"""
Step 3: Application to Java projects

This script is used to apply the fine-tuned model to a Java project.
The script will create a copy of the project with JML annotated copies
of the Java source files.

To use this script the following requirements have to be installed on the machine:

    * PyTorch
    * srcML tool (https://www.srcml.org/#download)

A GPU compatible with CUDA is highly recommended to speed up this script.

If 1_dataset.py and 2_training.py were used with the default arguments then
this script can be used with just the following two mandatory arguments:

    * --source-dir
    * --target-dir
"""

import argparse
import gc
import glob
import os
import pprint
import shutil
import subprocess
import sys
from builtins import print

import torch
from lxml import etree
from transformers import AutoModelForSeq2SeqLM, AutoTokenizer

# XML Namespaces
SRCML_NAMESPACE = "http://www.srcML.org/srcML/src"
SRCML_POS_NAMESPACE = "http://www.srcML.org/srcML/position"
NSMAP = {"src": SRCML_NAMESPACE, "pos": SRCML_POS_NAMESPACE}


def progressbar(it, prefix="", size=60, out=sys.stdout):
    count = len(it)
    print("Count: " + str(count))
    def show(j):
        x = int(size * j / count)
        print(
            "{}[{}{}] {}/{}".format(prefix, "#" * x, "." * (size - x), j, count),
            end="\r",
            file=out,
            flush=True,
        )

    show(0)
    for i, item in enumerate(it):
        yield item
        show(i + 1)
    print("\n", flush=True, file=out)


def save_file_at_dir(dir_path, filename, file_content, mode="w"):
    os.makedirs(dir_path, exist_ok=True)
    with open(os.path.join(dir_path, filename), mode, encoding="utf-8") as f:
        f.write(file_content)


def generateContractsFromModel(input, modelName, tokenizerModelName):
    text = input
    mname = modelName
    tokenizer = AutoTokenizer.from_pretrained(tokenizerModelName)
    model = AutoModelForSeq2SeqLM.from_pretrained(mname)
    input_ids = tokenizer.encode(text=text, return_tensors="pt")
    outputs = model.generate(input_ids, max_length=256)
    decoded = tokenizer.decode(outputs[0], skip_special_tokens=True)
    return decoded


def getLineRangeFromSRCMLElement(element):
    start = int(element.get("{" + NSMAP["pos"] + "}start").split(":")[0])
    end = int(element.get("{" + NSMAP["pos"] + "}end").split(":")[0])
    return start, end


def getJavaMethodsFromSourceFile(filepath):
    with open("Tmp.xml", "w", encoding="utf-8") as f:
        command = ["srcml", "--position", filepath]
        subprocess.run(command, shell=True, stdout=f)

    tree = etree.parse("Tmp.xml")
    functionXpath = etree.XPath("//src:class//src:function", namespaces=NSMAP)

    # Check if file has any functions at all
    if len(functionXpath(tree)) != 0:
        functions = []
        for element in functionXpath(tree):
            startline, endline = getLineRangeFromSRCMLElement(element)
            with open(filepath, encoding="utf-8") as f:
                functionCode = "".join(f.readlines()[startline - 1 : endline])
            currentFunctionElement = {
                "file": filepath,
                "functioncode": functionCode,
                "startline": startline,
                "endline": endline,
            }
            functions.append(currentFunctionElement)
        return functions
    else:
        print(f"{' '*6}File {filepath} does not have any functions.")
        return []


def getListOfAllJavaFilesInDirectory(directory):
    dirpath = os.path.join(directory, "**", "*.java")
    files = glob.glob(dirpath, recursive=True)
    return files


def annotateJavaFile(filepath, destination, listOfAnnotatedFunctions):
    os.makedirs(os.path.dirname(destination), exist_ok=True)
    shutil.copy(filepath, destination)
    numberOfInsertedLines = 0
    for function in listOfAnnotatedFunctions:
        with open(destination, "r", encoding="utf-8") as f:
            contents = f.readlines()
        contents.insert(
            function["startline"] - 1 + numberOfInsertedLines,
            function["openjml"] + "\n",
        )
        with open(destination, "w", encoding="utf-8") as f:
            contents = "".join(contents)
            f.write(contents)
        numberOfInsertedLines += function["openjmllength"]


def getStartLine(elem):
    return elem["startline"]


def main(args):
    argsdict = vars(args)
    print(pprint.pformat(argsdict))

    # Save command to file
    with open("3_command.txt", "w") as f:
        f.write(pprint.pformat(argsdict))

    # Activate Cuda (GPU) if available
    device = torch.device("cuda") if torch.cuda.is_available() else torch.device("cpu")
    print(f"  ==> Using {device} for computation")

    # Empty the cache of the GPU and perform garbage collection
    torch.cuda.empty_cache()
    gc.collect()

    projectPath = args.source_dir
    destinationPath = args.target_dir

    javaFiles = getListOfAllJavaFilesInDirectory(projectPath)
    functions = []
    annotatedFunctions = []
    hashTable = {}
    print("  ==> Extracting Java methods from files")
    for file in javaFiles:
        print("Processing file: " + file)
        newFunctions = getJavaMethodsFromSourceFile(file)
        print("Extracted Methods from file: " + file)
        if len(newFunctions) > 0:
            functions.extend(newFunctions)
        hashTable[file] = []
    print("  ==> Generating contracts for Java methods")
    for function in progressbar(functions, "      Computing: ", 40):
        function["openjml"] = generateContractsFromModel(
            input=("generate contracts: " + function["functioncode"]),
            modelName=args.model,
            tokenizerModelName=args.tokenizer,
        )
        annotatedFunctions.append(function)

    # Clean up
    os.remove("Tmp.xml")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )

    # Directories
    parser.add_argument(
        "--source-dir",
        required=True,
        type=str,
        help="path to directory of input java project",
    )
    parser.add_argument(
        "--target-dir",
        required=True,
        type=str,
        help="path to output directory for annotaed copy of project",
    )

    # Model
    parser.add_argument(
        "--model",
        default="saved_models/codet5p-contracts/checkpoint-1890",
        type=str,
        help="path to fine-tuned local model to use (checkpoint!)",
    )
    parser.add_argument(
        "--tokenizer",
        default="Salesforce/codet5p-220m",
        type=str,
        help="path or Huggingface name of tokenizer to use",
    )

    args = parser.parse_args()

    os.makedirs(args.target_dir, exist_ok=True)

    main(args)
