"""
Step 1: Collection and preproccesing of the dataset

This script collects the Java methods with JML annotations
from the Sourcegraph code search engine.
It takes care of all the necessary preprocessing that is
needed to use the collected dataset for the fine-tuning with 2_training.py.

To use this script the following requirements have to be installed on the machine:

    * Sourcegraph CLI (https://docs.sourcegraph.com/cli)
    * srcML tool (https://www.srcml.org/#download)

The only mandatory parameter is:

    * --src-access-token - Access Token for the Sourcegraph CLI / API
"""

import argparse
import csv
import glob
import json
import os
import pprint
import re
import subprocess

import numpy as np
import pandas as pd
from lxml import etree


def checkInterface(xmlElement):
    currentElement = xmlElement
    while currentElement.getparent():
        if (
            currentElement.getparent().tag
            == r"{http://www.srcML.org/srcML/src}interface"
        ):
            return True
        currentElement = currentElement.getparent()
    return False


def checkFollowingSiblingFunctions(xmlElement, namespacemap):
    if (
        len(
            xmlElement.xpath(
                "following-sibling::src:function/@pos:start", namespaces=namespacemap
            )
        )
        == 0
    ):
        return False
    return True


def extract_contracts_and_methods(
    sourcegraph_file: str, dataset_file: str, verbose: bool
):
    SRCML_NAMESPACE = "http://www.srcML.org/srcML/src"
    SRCML_POS_NAMESPACE = "http://www.srcML.org/srcML/position"
    NSMAP = {"src": SRCML_NAMESPACE, "pos": SRCML_POS_NAMESPACE}
    regex = re.compile("(//@ requires)|(//@ ensures).*")

    with open(sourcegraph_file, "r", encoding="UTF-8") as f:
        sourcegraph = json.load(f)

    dataElements = []
    skippedFiles = 0
    JMLComments = 0
    nonJMLComments = 0
    interfaceComments = 0
    noFollowingFunctionComments = 0
    for result in sourcegraph["Results"]:
        file_contents = result["file"]["content"]
        file_name = result["file"]["path"]
        file_repository = result["repository"]["name"]
        with open("Tmp.java", "w", encoding="UTF-8", newline="") as f:
            f.write(file_contents)

        with open("Tmp.xml", "w", encoding="UTF-8") as f:
            command = ["srcml", "--position", "Tmp.java"]
            result = subprocess.run(command, shell=True, stdout=f)

        tree = etree.parse("Tmp.xml")
        functionXpath = etree.XPath("//src:function", namespaces=NSMAP)
        myxpath = etree.XPath("//src:comment[@type='line']", namespaces=NSMAP)

        # Check if file has any functions at all
        if len(functionXpath(tree)) == 0:
            if verbose:
                print(
                    f"{' '*6}File {file_name} does not have any functions. Skipping..."
                )
            skippedFiles += 1
            continue

        # Loop over all LINE COMMENTS in the java file
        idx = 0
        for comment in myxpath(tree):
            if checkInterface(comment):
                if verbose:
                    print(
                        f"{' '*6}File {file_name} We are inside an interface "
                        "and will skip to the next comment."
                    )
                interfaceComments += 1
                continue

            # If the line comment is an JML pre-/postcondition
            if re.match(regex, comment.text):
                if verbose:
                    print(f"{' '*6}Comment: {comment.text}")
                JMLComments += 1

                # Check if comment is already inside a function
                commentIsInsideFunction = (
                    True
                    if (
                        comment.getparent().tag
                        == r"{http://www.srcML.org/srcML/src}function"
                    )
                    else False
                )
                if not commentIsInsideFunction:
                    if not checkFollowingSiblingFunctions(comment, NSMAP):
                        if verbose:
                            print(
                                f"{' '*6}Comment is not inside a function "
                                "and there are no following functions. "
                                "Skipping to next comment."
                            )
                        noFollowingFunctionComments += 1
                        continue
                    if verbose:
                        print(
                            f"{' '*6}Comment is not inside a function "
                            "but there are follwing functions."
                        )
                else:
                    if verbose:
                        print(f"{' '*6}Comment is inside a function")

                if idx == 0:
                    if verbose:
                        print(f"{' '*6}First processed comment in this file.")

                    if commentIsInsideFunction:
                        startingLine = int(
                            comment.xpath(
                                "parent::src:function/@pos:start", namespaces=NSMAP
                            )[0].split(":")[0]
                        )
                        endingLine = int(
                            comment.xpath(
                                "parent::src:function/@pos:end", namespaces=NSMAP
                            )[0].split(":")[0]
                        )
                    else:
                        startingLine = int(
                            comment.xpath(
                                "following-sibling::src:function/@pos:start",
                                namespaces=NSMAP,
                            )[0].split(":")[0]
                        )
                        endingLine = int(
                            comment.xpath(
                                "following-sibling::src:function/@pos:end",
                                namespaces=NSMAP,
                            )[0].split(":")[0]
                        )
                    with open("Tmp.java", encoding="UTF-8") as myFile:
                        myLines = "".join(
                            myFile.readlines()[startingLine - 1 : endingLine]
                        )
                    currentDataElement = {
                        "repository": file_repository,
                        "file": file_name,
                        "code": myLines.replace(comment.text, ""),
                        "methodStartingLine": startingLine,
                        "methodEndingLine": endingLine,
                        "jml": comment.text,
                    }
                    idx += 1
                    continue

                if commentIsInsideFunction:
                    startingLine = int(
                        comment.xpath(
                            "parent::src:function/@pos:start", namespaces=NSMAP
                        )[0].split(":")[0]
                    )
                else:
                    startingLine = int(
                        comment.xpath(
                            "following-sibling::src:function/@pos:start",
                            namespaces=NSMAP,
                        )[0].split(":")[0]
                    )
                if startingLine == currentDataElement["methodStartingLine"]:
                    currentDataElement["jml"] = "\n".join(
                        [currentDataElement["jml"], comment.text]
                    )
                    currentDataElement["code"] = currentDataElement["code"].replace(
                        comment.text, ""
                    )
                else:
                    dataElements.append(currentDataElement)
                    if commentIsInsideFunction:
                        endingLine = int(
                            comment.xpath(
                                "parent::src:function/@pos:end", namespaces=NSMAP
                            )[0].split(":")[0]
                        )
                    else:
                        endingLine = int(
                            comment.xpath(
                                "following-sibling::src:function/@pos:end",
                                namespaces=NSMAP,
                            )[0].split(":")[0]
                        )
                    with open("Tmp.java", encoding="UTF-8") as myFile:
                        myLines = "".join(
                            myFile.readlines()[startingLine - 1 : endingLine]
                        )
                    currentDataElement = {
                        "repository": file_repository,
                        "file": file_name,
                        "code": myLines.replace(comment.text, ""),
                        "methodStartingLine": startingLine,
                        "methodEndingLine": endingLine,
                        "jml": comment.text,
                    }
            else:
                nonJMLComments += 1
        if idx > 0:
            dataElements.append(currentDataElement)
    if len(dataElements) > 0:
        with open(dataset_file, "w", encoding="UTF-8") as json_file:
            json_file.write(json.dumps(dataElements, ensure_ascii=False, indent=4))

    filestats = {
        "fileName": sourcegraph_file,
        "files": len(sourcegraph["Results"]),
        "skippedFiles": skippedFiles,
        "nonJMLComments": nonJMLComments,
        "JMLComments": JMLComments,
        "interfaceComments": interfaceComments,
        "noFollowingFunctionComments": noFollowingFunctionComments,
    }
    if verbose:
        statString = (
            "      File: {fileName}\n"
            + "      # files to start: {files}\n"
            + "      # skipped files: {skippedFiles}\n"
            + "      # non-JML comments: {nonJMLComments}\n"
            + "      # JML comments: {JMLComments}\n"
            + "      # interface comments: {interfaceComments}\n"
            + "      # comments after last function: {noFollowingFunctionComments}"
        )
        print(statString.format_map(filestats))
    return filestats


def extract_files_from_repos(
    repo_name: str, outfile_name: str, search_keyword: str, patterntype: str
) -> None:
    assert repo_name != ""
    assert outfile_name != ""
    assert search_keyword != ""

    lang_arg: str = "lang:java"
    repo_arg: str = "repo:" + repo_name
    count_arg: str = "count:all"
    case_arg: str = "case:yes"
    type_arg: str = "type:file"
    patterntype_arg: str = "patterntype:" + patterntype
    arg_string: str = (
        search_keyword
        + " "
        + repo_arg
        + " "
        + lang_arg
        + " "
        + count_arg
        + " "
        + case_arg
        + " "
        + type_arg
        + " "
        + patterntype_arg
    )

    print(f"  ==> Querying Sourcegraph for Repository: {repo_name}")
    command = ["src", "search", "-json", arg_string]
    print(f"{' '*6}" + " ".join(command))

    with open(outfile_name, "w") as f:
        result = subprocess.run(command, stdout=f)
        print(f"{' '*6}RESULT:" + str(result))


def main(args):
    argsdict = vars(args)
    print(pprint.pformat(argsdict))

    # Save command to file
    with open("1_command.txt", "w") as f:
        f.write(pprint.pformat(argsdict))

    # Set environment variables for Sourcegraph API
    os.environ["SRC_ENDPOINT"] = args.src_endpoint
    os.environ["SRC_ACCESS_TOKEN"] = args.src_access_token

    # Query Sourcegraph for Pre- and Postconditions
    print("  ==> Querying Sourcegraph for Preconditions")
    command = ["src", "search", "-json", "lang:java type:file count:all //@ requires"]
    print(f"{' '*6}" + " ".join(command))

    with open("requires.json", "w") as f:
        result = subprocess.run(command, stdout=f)
        print(f"{' '*6}RESULT: " + str(result))

    print("  ==> Querying Sourcegraph for Postconditions")
    command = ["src", "search", "-json", "lang:java type:file count:all //@ ensures"]
    print(f"{' '*6}" + " ".join(command))

    with open("ensures.json", "w") as f:
        result = subprocess.run(command, stdout=f)
        print(f"{' '*6}RESULT: " + str(result))

    my_df = []

    # Determine unique repositories
    print("  ==> Extracting repositories from precondition results")
    with open(file="requires.json", encoding="UTF-8", mode="r") as f:
        data = json.load(f)
        for i in range(0, len(data["Results"])):
            repo_name: str = data["Results"][i]["repository"]["name"]
            file_url: str = data["Results"][i]["file"]["url"]
            line_matches = []
            for j in range(0, len(data["Results"][i]["lineMatches"])):
                line_matches.append(data["Results"][i]["lineMatches"][j]["lineNumber"])
            number_of_line_matches = len(line_matches)
            dictEntry = {
                "repo_name": repo_name,
                "file_url": file_url,
                "number_of_line_matches": number_of_line_matches,
                "line_matches": np.array(line_matches),
            }
            my_df.append(dictEntry)

    print("  ==> Extracting repositories from postcondition results")
    with open(file="ensures.json", encoding="UTF-8", mode="r") as f:
        data = json.load(f)
        for i in range(0, len(data["Results"])):
            repo_name: str = data["Results"][i]["repository"]["name"]
            file_url: str = data["Results"][i]["file"]["url"]
            line_matches = []
            for j in range(0, len(data["Results"][i]["lineMatches"])):
                line_matches.append(data["Results"][i]["lineMatches"][j]["lineNumber"])
            number_of_line_matches = len(line_matches)
            dictEntry = {
                "repo_name": repo_name,
                "file_url": file_url,
                "number_of_line_matches": number_of_line_matches,
                "line_matches": line_matches,
            }
            my_df.append(dictEntry)

    my_df = pd.DataFrame(my_df)

    # Query Sourcegraph for every single repository individually
    repos = my_df["repo_name"].unique()
    for i in range(0, len(repos)):
        repo = repos[i]
        outfile_name = repo.replace("/", "_")
        extract_files_from_repos(
            repo,
            os.path.join(args.data_dir, "raw_repositories", outfile_name + ".json"),
            "(//@ requires )|(//@ ensures )",
            "regexp",
        )

    # Extract all contracts and methods from individual repository JSON files
    exclusionList = ["github.com_Flunzmas_gym-autokey.json"]

    statlist = []
    for path, subdirs, files in os.walk(
        os.path.join(args.data_dir, "raw_repositories")
    ):
        for name in files:
            if name not in exclusionList:
                print(f"  ==> Extracting contrats and methods for repository: {name}")
                filestats = extract_contracts_and_methods(
                    os.path.join(args.data_dir, "raw_repositories", name),
                    os.path.join(
                        args.data_dir, "dataset_" + os.path.splitext(name)[0] + ".json"
                    ),
                    args.verbose,
                )
                statlist.append(filestats)

    with open("stats.csv", "w", newline="") as f:
        fields = [
            "fileName",
            "files",
            "skippedFiles",
            "nonJMLComments",
            "JMLComments",
            "interfaceComments",
            "noFollowingFunctionComments",
        ]
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(statlist)

    # Merge all JSON files
    print("  ==> Merging everything into singular dataset file")
    data = []
    for f in glob.glob(os.path.join(args.data_dir, "dataset_*.json")):
        with open(f) as infile:
            data.extend(json.load(infile))

    with open(args.data_file, "w") as outfile:
        json.dump(data, outfile)

    # Clean up
    os.remove("Tmp.java")
    os.remove("Tmp.xml")


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
    parser.add_argument(
        "--src-access-token",
        required=True,
        type=str,
        help="sourcegraph api access token",
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
        default="dataset_withoutWeka.json",
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
