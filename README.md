# nil

Zero-knowledge proof framework, written from field arithmetic up.

`nil` compiles a small language into an arithmetic circuit, converts it to a QAP,
and generates and verifies zk-SNARK proofs over BN-254. The curve, the field
tower and the pairing live in this repository rather than in a dependency.

## A proof, end to end

This is a complete program in the `nil` language. It proves that someone is over
19 from a credential signed by an issuer.

```
language (priv e, priv r, priv s, \
          priv dateOfBirth, priv legalName, priv address, \
          priv credHash, pub regID)

    # the credential matches the one registered on chain
    let checkpoint1 = if !(credHash * dateOfBirth * legalName * address) == regID then 1 else 0

    # the claim meets the age criteria
    let settlementTime = 1601478000
    let checkpoint2 = if (settlementTime - dateOfBirth) > (19 * 365 * 86400) then 1 else 0

    # the prover owns the signing key behind (r, s)
    let k = (credHash + r * e) / s
    let P = [e]
    let R = [k]
    let checkpoint3 = if r == :R then 1 else 0

    let passed = checkpoint1 * checkpoint2 * checkpoint3

    return if passed == 1 then :P else regID
```

The verifier learns one thing: whether the returned value is the registered
public key. The date of birth, the name, the address, the credential hash and
the private key are all `priv` and never leave the prover.

Note that `checkpoint3` verifies an ECDSA signature inside the circuit. The
signature check is part of what is proven, not something done beforehand.

## The language

Three kinds of statement. `language` declares the inputs, `let` binds an
expression, `return` states what is proven. Everything is an expression over the
prime field `Fr` or the curve `BN-254`.

| Operator          | Meaning                                    |
|-------------------|--------------------------------------------|
| `+ - * / ^ %`     | field arithmetic over `Fr`                 |
| `> >= < <= == /=` | relational, valid only inside `if`         |
| `!e`              | Blake2b hash of `e`, mapped back into `Fr` |
| `[k]`             | `k * G`, a point from the base point       |
| `[x,y]`           | a point from its coordinates               |
| `:P` `;P`         | the x- and y-coordinate of a point         |

There is no boolean primitive. A relational operator is always converted into an
if-expression, and an if-expression compiles to `a*b + (1-a)*c`. So a guard is
written as a product of checkpoints, as above: if any one of them is zero, the
whole thing is zero.

## Pipeline

```
language → tokens → AST → arithmetic circuit → R1CS → QAP → proof
```

The circuit can be exported as a graph at any stage with `-g`, which writes a
DAG through Graphviz.

## Usage

```bash
# trusted setup: writes a circuit, an evaluation key and a verification key
nil setup age-over-19.lang

# prove, with a JSON file of witnesses
nil prove -c CIRCUIT -k EKEY prover.json

# verify, with a JSON file of public instances
nil verify -p PROOF -k VKEY verifier.json
```

## What is implemented

Everything under the proof system is in this repository.

- `Fr`, `Fq`, `Fq2`, `Fq12` as a field tower, with Frobenius and inversion
- BN-254 in Jacobian coordinates, with the 2007 Bernstein–Lange formulas
- Square roots over `Fp` by Tonelli–Shanks, for point decompression
- The optimal Ate pairing: Miller loop over `6t+2`, the sextic twist, and final exponentiation
- Polynomials with Lagrange interpolation and an extended Euclidean algorithm
- Pinocchio (PGHR13), the setup, prover and verifier
- Shamir's secret sharing over a prime field
- ECDSA over BN-254 and secp256k1
- A lexer, a recursive-descent parser with operator precedence, and a circuit compiler

## nil-sign

`nil` also carries a multi-party scheme built on the same machinery.

One circuit is evaluated by several parties in turn. Each party partially
evaluates the gates that belong to it, using a secret the others never see, and
the intermediate values are randomized as they propagate. When every party has
signed, anyone can check the result with a single pairing equation. Nothing in
the final object reveals which secret produced it.

```bash
nil init  age-over-19.lang     # build the signature object from a circuit
nil sign  -s SIG secrets.json  # partially evaluate with your own secrets
nil check -s SIG return.json   # verify the accumulated result
```

## Build

```bash
git clone https://github.com/thyeem/nil.git
cd nil
stack build
```

Graph export needs Graphviz (`brew install graphviz`).

## Status

This is a correctness-first implementation, and there are places where that
shows.

- QAP construction interpolates in `O(d²)`. With an NTT over a power-of-two subgroup of `Fr` it would be `O(d log d)`, and `t(x)` would collapse to `x^n - 1`. BN-254 has 2-adicity 28, so there is room for it; the evaluation domain would have to move from `[1..d]` to the roots of unity.
- Field elements are `Integer` reduced by `mod`. No Montgomery form.
- The trusted setup samples its randomness in one process. It is not a ceremony.
- `nil-sign` has no written security proof.

Together these put a ceiling on circuit size. The framework is meant for reading
and for small circuits, not for production proving.

