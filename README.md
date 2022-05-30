
# Verification examples

This repository contains examples of smart contracts specified and verified with [Dafny](https://github.com/dafny-lang/dafny).

# How to check the proofs?

We have checked the proofs with Dafny 3.5.0.
To mechanically check the proofs, it suffices to run the Dafny verifier on the contracts.
We explain in this section how to do so.

Pre-requisites:

* install Dafny, see [Dafny](https://github.com/dafny-lang/dafny)
* or alternatively install VsCode and the [Dafny VsCode plugin](https://marketplace.visualstudio.com/items?itemName=dafny-lang.ide-vscode) 
* clone or fork this repository.

If you use the VsCode plugin, opening the `*.dfy` file should autoamtically start the verification process.

Assuming you have a running Dafny compiler, you may use the following command line to check a `*.dfy` file:
```
> dafny /dafnyVerify:1 /compile:0  filename.dfy
...

Dafny program verifier finished with 10 verified, 0 errors
```

For some examples, it is also possible to run a program (or test) and the command is:
```
> dafny /noVerify /compile:4 filename.dfy
...

```
This will compile (in memory) and run the `Main` method in `filename.dfy`.