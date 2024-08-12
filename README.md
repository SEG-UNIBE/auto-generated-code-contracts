# AI-Generated Code Contracts

This repository provides the setup and results to generate OpenJML code contracts for Java source code by fine-tuning and employing the resulting CodeT5 and CodeT5+ transformer models.


# Contents of this repository

This repository contains all artifacts that we used to generate code contracts with CodeT5 models and evaluate their capabilities.
Our code contract generation setup involved the training of the AI models and application which we conducted with Python scripts.
Furthermore, we analyzed the Java source code we used in the experiment and the type of OpenJML compilation errors.
Both methods, together with the results are similarly provided. In concrete, this repository contains:

- **Scripts**
  We include the following Python scripts, which we used for training and adding the OpenJML code contracts to the Java methods.

  - [1_dataset.py](scripts/1_dataset.py)		collects the dataset from [Sourcegraph](https://sourcegraph.com/search)
  - [2_training.py](scripts/2_training.py)		performs the fine-tuning ont the CodeT5 and CodeT5+ model (as specified)
  - [3_application.py](scripts/3_application.py)	applies the fine-tuned models to the methods in a given Java project, to generate code-contracts
  - [4_quick-gen.py](scripts/4_quick-gen.py)	serves as quick validation, where you can put in a method body and let generate the corresponding contract by the fine-tuned model
  - [requirements.txt](scripts/requirements.txt) for executing above Python scripts

Furthermore, we performed automated analyses of the studied source code classes and the type of compilation errors, which involved the following Java classes
  - [JavaStatisticsScanner](scripts/JavaStatisticsScanner.java)  computes the number of contained annotations, LOC, ... of Java files in a given directory
  - [CompilationAnalysisScanner.java](scripts/CompilationAnalysisScanner.java) 	counts the number of OpenJML compilation errors in a given file

Finally, we add and link the results of our experiment:

- **Results** from our study including

	- the gathered dataset, the fine-tuned models with and without the weka-project
	- the results of compiling the generated contracts with OpenJML
	- the results of analyzing the logic validity


# Getting started
## Prerequisites

To use the Python scripts you need to have installed:

- a recent version of [Python 3](https://www.python.org/downloads)
- [srcML](https://www.srcml.org/#download)
- [Sourcegraph CLI](https://docs.sourcegraph.com/cli/quickstart)

To use Sourcegraph, you need to create an access token by following the instructions here: https://docs.sourcegraph.com/cli/how-tos/creating_an_access_token

## Setup

1. Clone the contents of this package to your local machine
2. Create a Python Virtual Environment inside the package directory. This is usually done as follows, but might be slightly different depending on your OS or Python distribution:
`$ python -m venv .venv`
3. Activate your new virtual environment by excuting one of the activation scripts in the folder `/.venv/Scripts/` called activate, activate.bat and Activate.ps1
4. Use pip to install the required Python packages for the scripts like this:
`pip install -r requirements.txt`

You are now ready to use our scripts.

## Scripts

All scripts are well documented to explain their purpose and usage. The Pyhton scripts encompass a "man page" that can be display using the `-h` argument;
e.g. `python 1_dataset.py -h` will print the description of the the script including all the possible or required arguments.

For this reason we only provide a short summary of the main scripts' functionality here.

### 1_dataset.py
This script collects the Java methods with JML annotations from the Sourcegraph code search engine.
It takes care of all the necessary preprocessing that is needed to use the collected dataset for the fine-tuning with 2_training.py.
### 2_training.py
This script is used to fine-tune CodeT5 or CodeT5+ using the dataset created by 1_dataset.py.
A GPU compatible with CUDA is highly recommended to speed up this script.
### 3_application.py
This script is used to apply the fine-tuned model to a Java project.
The script will create a copy of the project with JML annotated copies of the Java source files.
A GPU compatible with CUDA is highly recommended to speed up this script.

## Results

The results folder contains the

- two datasets:
	- one including the [weka-project](https://github.com/svn2github/weka) which contributes two-thirds of the contracts
	- one without weka, which is significantly smaller and was used to examine the performance bias when training and testing without weka

- two CodeT5 models
	+ the best performing CodeT5+ model which was fine-tuned to create OpenJML annotations for methods
	+ the CodeT5+ model which was trained without weka on the same task

- in application_tests
	- the subjects to which we applied the best performing CodeT5+
	- the compilation results and their analysis

- the analysis of logic validity of SimpleStack and SimpleTicTacToe

