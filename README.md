
# Verification examples

This repository contains examples of smart contracts specified and verified with [Dafny](https://github.com/dafny-lang/dafny).

# How to check the proofs?

We have checked the proofs with Dafny 4.3.0.
To mechanically check the proofs, it suffices to run the Dafny verifier on the contracts.
We explain in this section how to do so.

Pre-requisites:

* install Dafny, see [Dafny](https://github.com/dafny-lang/dafny)
* or alternatively install VsCode and the [Dafny VsCode plugin](https://marketplace.visualstudio.com/items?itemName=dafny-lang.ide-vscode) 
* clone or fork this repository.

If you use the VsCode plugin, opening the `*.dfy` file should automatically start the verification process.

Assuming you have a running Dafny compiler, called `dafny`, you may use the following command line to check a `*.dfy` file:
```
> dafny verify  filename.dfy
...

Dafny program verifier finished with 10 verified, 0 errors
```

For some examples, it is also possible to run a program (or test) and the command is:
```
> dafny run filename.dfy
...

```
This will compile (in memory) and run the `Main` method in `filename.dfy`.

# Example: the Token contract.
To verify and run the `Token` contract versions in the terminal use the following commands:
```
> dafny verify token/token.dfy
...
> dafny verify token/token-with-revert.dfy
...
Dafny program verifier finished with 9 verified, 0 errors
> dafny verify token/token-with-revert-external.dfy
...
> dafny run token/token-with-callback-example.dfy
Dafny program verifier did not attempt verification
Running...

This is an example of exploit of re-entrancy
Token K : TokenK created
Token K : TokenK mints 200
Contract TokenK total amount:200
c2.bal initially: 200
TokenK.transfer#1 from BadGuy2 for 200 to BadGuy1
TokenK notifies BadGuy1
BadGuy1 calls BadGuy2.help  gas left:7
BadGuy2 calls TokenK.transfer for 200 to BadGuy1 gas left:6
TokenK.transfer#2 from BadGuy2 for 200 to BadGuy1
TokenK notifies BadGuy1
BadGuy1 calls BadGuy2.help  gas left:4
BadGuy2 calls TokenK.transfer for 200 to BadGuy1 gas left:3
TokenK.transfer#3 from BadGuy2 for 200 to BadGuy1
TokenK notifies BadGuy1
BadGuy1 calls BadGuy2.help  gas left:1
BadGuy2 calls TokenK.transfer for 200 to BadGuy1 gas left:0
TokenK.transfer#4 reverting gas: 0
TokenK.transfer#3 completed
TokenK.transfer#2 completed
TokenK.transfer#1 completed
Contract TokenK total amount:200
c1.bal final: 600
c2.bal final: 0
c1.bal + c2.bal: 600
>
```