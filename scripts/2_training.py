"""
Step 2: Fine-tuning of the Large Language Models

This script is used to fine-tune CodeT5 or CodeT5+ using
the dataset created by 1_dataset.py.

To use this script the following requirements have to be installed on the machine:

    * PyTorch, accelerate,  rouge_score, sacrebleu

A GPU compatible with CUDA is highly recommended to speed up this script.

If the dataset was created with 1_dataset.py and the default arguments then
this script can be used without any arguments to fine-tune CodeT5+ (220m version).
"""

import argparse
import gc
import os
import pprint
import warnings

import evaluate
import numpy as np
import torch
from datasets import load_dataset, load_from_disk
from transformers import (
    AutoModelForSeq2SeqLM,
    AutoTokenizer,
    Seq2SeqTrainer,
    Seq2SeqTrainingArguments,
)


# Training loop
def run_training(args, model, train_data):
    print("  ==> Starting main loop")

    # Setup evaluation
    tokenizer = AutoTokenizer.from_pretrained(args.load)
    if not args.no_eval:
        dataset = train_data.train_test_split(test_size=args.test_size)
        train_data = dataset["train"]
        eval_data = dataset["test"]

    # Evaluation function
    def compute_metrics(eval_preds):
        preds, labels = eval_preds

        # Decode preds and labels
        labels = np.where(labels != -100, labels, tokenizer.pad_token_id)
        decoded_preds = tokenizer.batch_decode(preds, skip_special_tokens=True)
        decoded_labels = tokenizer.batch_decode(labels, skip_special_tokens=True)

        # Compute metrics
        metric_bleu = evaluate.load("bleu")
        metric_exact_match = evaluate.load("exact_match")
        metric_rouge = evaluate.load("rouge")
        metric_ter = evaluate.load("ter")

        bleu = metric_bleu.compute(predictions=decoded_preds, references=decoded_labels)
        rouge = metric_rouge.compute(
            predictions=decoded_preds, references=decoded_labels
        )
        ter = metric_ter.compute(predictions=decoded_preds, references=decoded_labels)
        exact_match = metric_exact_match.compute(
            predictions=decoded_preds, references=decoded_labels
        )
        return {
            "bleu": bleu["bleu"],
            "rouge": rouge["rougeLsum"],
            "ter": ter["score"],
            "exact_match": exact_match["exact_match"],
        }

    training_args = Seq2SeqTrainingArguments(
        output_dir=args.save_dir,
        overwrite_output_dir=False,
        do_train=True,
        save_strategy="epoch",
        predict_with_generate=True,
        num_train_epochs=args.epochs,
        per_device_train_batch_size=args.batch_size_per_replica,
        gradient_accumulation_steps=args.grad_acc_steps,
        eval_accumulation_steps=args.eval_acc_steps,
        optim="adamw_torch",
        learning_rate=args.lr,
        weight_decay=0.05,
        warmup_steps=args.lr_warmup_steps,
        logging_dir=args.save_dir,
        logging_first_step=True,
        logging_steps=args.log_freq,
        save_total_limit=1,
        dataloader_drop_last=True,
        dataloader_num_workers=4,
        local_rank=args.local_rank,
        deepspeed=args.deepspeed,
        fp16=args.fp16,
    )

    trainer = Seq2SeqTrainer(
        model=model,
        args=training_args,
        train_dataset=train_data,
        eval_dataset=eval_data,
        compute_metrics=compute_metrics,
    )

    # Run training
    trainer.train()
    print("  ==> Completed training")

    # Run evaluation
    if not args.no_eval:
        print("  ==> Starting evaluation")
        print(pprint.pformat(trainer.evaluate()))
        print("  ==> Completed evaluation")


# Load and tokenize data
def load_tokenize_data(args):
    if os.path.exists(args.cache_data):
        train_data = load_from_disk(args.cache_data)
        print(f"  ==> Loaded {len(train_data)} samples")
        return train_data
    else:
        datasets = load_dataset("json", data_files=args.data_file, split="train")
        tokenizer = AutoTokenizer.from_pretrained(args.load)

        def preprocess_function(examples):
            source = [" ".join(["generate contracts:", ex]) for ex in examples["code"]]
            target = [ex for ex in examples["jml"]]

            model_inputs = tokenizer(
                source,
                max_length=args.max_source_len,
                padding="max_length",
                truncation=True,
            )
            labels = tokenizer(
                target,
                max_length=args.max_target_len,
                padding="max_length",
                truncation=True,
            )

            model_inputs["labels"] = labels["input_ids"].copy()
            model_inputs["labels"] = [
                [(L if L != tokenizer.pad_token_id else -100) for L in label]
                for label in model_inputs["labels"]
            ]
            return model_inputs

        train_data = datasets.map(
            preprocess_function,
            batched=True,
            remove_columns=datasets.column_names,
            num_proc=64,
            load_from_cache_file=False,
        )

        print(f"  ==> Loaded {len(train_data)} samples")
        train_data.save_to_disk(args.cache_data)
        print(f"  ==> Saved to {args.cache_data}")
        return train_data


def main(args):
    argsdict = vars(args)
    print(pprint.pformat(argsdict))

    # Save command to file
    with open("2_command.txt", "w") as f:
        f.write(pprint.pformat(argsdict))

    # Activate Cuda (GPU) if available
    device = torch.device("cuda") if torch.cuda.is_available() else torch.device("cpu")
    print(f"  ==> Using {device} for computation")

    # Empty the cache of the GPU and perform garbage collection
    torch.cuda.empty_cache()
    gc.collect()

    # Ignore UserWarnings about Scalars
    warnings.filterwarnings(action="ignore", category=UserWarning)

    # Load and tokenize data using the tokenizer from `args.load`.
    # If the data is already cached, load it from there.
    train_data = load_tokenize_data(args)

    # Load model from `args.load`
    model = AutoModelForSeq2SeqLM.from_pretrained(args.load)
    print(f"  ==> Loaded model from {args.load}, model size {model.num_parameters()}")

    run_training(args, model, train_data)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        "--max-source-len",
        default=512,
        type=int,
        help="maximum input length of the model",
    )
    parser.add_argument(
        "--max-target-len",
        default=256,
        type=int,
        help="maximum output length of the model",
    )
    parser.add_argument(
        "--cache-data",
        default="cache_data/codet5p-contracts",
        type=str,
        help="path to cache directory",
    )
    parser.add_argument(
        "--data-file",
        default="dataset.json",
        type=str,
        help="path to the dataset file that shall be used",
    )
    parser.add_argument(
        "--load",
        default="Salesforce/codet5p-220m",
        type=str,
        help="name of the model that shall be fine-tuned; "
        "this can be a local path or a HuggingFace model name",
    )

    # Training
    parser.add_argument(
        "--epochs",
        default=10,
        type=int,
        help="training hyperparameter: number of epochs",
    )
    parser.add_argument(
        "--lr", default=5e-5, type=float, help="training hyperparameter: learning rate"
    )
    parser.add_argument(
        "--lr-warmup-steps",
        default=200,
        type=int,
        help="training hyperparameter: warmup steps",
    )
    parser.add_argument(
        "--batch-size-per-replica",
        default=8,
        type=int,
        help="training hyperparameter: batch size",
    )
    parser.add_argument(
        "--grad-acc-steps",
        default=4,
        type=int,
        help="training hyperparameter: gradient accumulation steps",
    )
    parser.add_argument("--local-rank", default=-1, type=int)
    parser.add_argument(
        "--deepspeed",
        default=None,
        type=str,
        help="optional path to deepspeed config file",
    )
    parser.add_argument(
        "--fp16",
        default=False,
        action="store_true",
        help="use half-precision 16bit floating point to speed up",
    )

    # Evaluation
    parser.add_argument(
        "--no-eval",
        default=False,
        action="store_true",
        help="flag to disable the evaluation step",
    )
    parser.add_argument(
        "--test-size", default=0.2, type=float, help="test size to seperate for testing"
    )
    parser.add_argument(
        "--eval-acc-steps", default=4, type=int, help="evaluation accumulation steps"
    )

    # Logging and stuff
    parser.add_argument(
        "--save-dir",
        default="saved_models/codet5p-contracts",
        type=str,
        help="path to directory where fine-tuned model shall be saved",
    )
    parser.add_argument(
        "--log-freq", default=10, type=int, help="logging frequency (steps)"
    )
    parser.add_argument(
        "--save-freq", default=250, type=int, help="saving frequency (steps)"
    )

    args = parser.parse_args()

    os.makedirs(args.save_dir, exist_ok=True)

    main(args)
