# Contract Compositionality

A HOL4 formalization of a theory of specifications, components, contracts, and compositionality.

## Building

Requirements:
- [Poly/ML 5.7.1](https://github.com/polyml/polyml) (or later)
- [HOL4 trindemossen-1](https://github.com/HOL-Theorem-Prover/HOL/releases/tag/trindemossen-1)

The default Makefile task, which assumes `Holmake` is available on the system, builds all core HOL4 theories:

```shell
make
```

## Files

- [`folStringScript.sml`](fol/folStringScript.sml): first-order logic with string identifiers
- [`folStringInterpScript.sml`](fol/folStringInterpScript.sml): some simple first-order theories using string identifiers
- [`compSpecUtilityScript.sml`](semantics/compSpecUtilityScript.sml): some utility definitions and results
- [`compSpecScript.sml`](semantics/compSpecScript.sml): definition of abstract syntax for specifications, components, and predicates, and definition of proof systems
- [`compSpecMetaScript.sml`](semantics/compSpecMetaScript.sml): semantics and metatheory of specifications and components, including proof system soundness
- [`compSpecFolScript.sml`](semantics/compSpecFolScript.sml): interpretation as first-order theory
- [`compSpecFolScript.sml`](semantics/compSpecFolScript.sml): interpretation as first-order theory
- [`compSpecExampleScript.sml`](semantics/compSpecExampleScript.sml): examples of proof system use
- [`mitlScript.sml`](semantics/mitlScript.sml): MITL formal semantics
- [`compSpecMitlScript.sml`](semantics/compSpecMitlScript.sml): instantiation of specifications for MITL
- [`compSpecMitlFLDScript.sml`](semantics/compSpecMitlFLDScript.sml): instantiation for a fuel level display (FLD) system
