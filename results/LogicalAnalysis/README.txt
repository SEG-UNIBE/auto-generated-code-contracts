To analyze the logical validity of generated contracts, we performed an in-depth manual analysis, comparing generated contracts with a reference implementation/specification of contracts for the academic projects Simple-Stack and Simple-TicTacToe.

We classify the pre- and postconditions of the generated contracts wrt. to the respective reference contract's pre- and postconditions using the following categories:
- E: Equivalent 
- W: Weaker 
- S_V: Stronger (valid) 
- S_I: Stronger (invalid) 
- U_I: Unrelated (invalid)

The classifiers E through U_I are provided as additional comment for each generated JML annotation directly in the Java source code files.
The reference contracts are specified/implemented using Java assertions.
