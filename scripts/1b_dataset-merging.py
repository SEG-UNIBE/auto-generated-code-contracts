"""
Step 1b: Preproccesing of the dataset

This script merges the collected Java methods stored injson files into a single dataset.
The merged dataset can be readily used for the fine-tuning with 2_training.py.

"""

import argparse
import glob
import json
import os

def main(args):
    # Merge all JSON files
    print("  ==> Merging everything into singular dataset file")
    data = []
    for f in glob.glob(os.path.join(args.data_dir, "dataset_*.json")):
        with open(f) as infile:
            data.extend(json.load(infile))

    with open(args.data_file, "w") as outfile:
        json.dump(data, outfile)



if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )

    # Sourcegraph API
    parser.add_argument(
        "--src-endpoint",
        default="https://sourcegraph.com",
        type=str,
        help="url for the sourcegraph search api endpoint",
    )

    # Data
    parser.add_argument(
        "--data-dir",
        default="dataset",
        type=str,
        help="path to the directory where the " "dataset files should be stored",
    )
    parser.add_argument(
        "--data-file",
        default="dataset_withoutWeka0107.json",
        type=str,
        help="path to the file where the final dataset " "json file should be stored",
    )

    # Logging
    parser.add_argument(
        "--verbose",
        default=False,
        action="store_true",
        help="flag to enable verbose output mode",
    )

    args = parser.parse_args()

    os.makedirs(args.data_dir, exist_ok=True)
    os.makedirs(os.path.join(args.data_dir, "raw_repositories"), exist_ok=True)

    main(args)
