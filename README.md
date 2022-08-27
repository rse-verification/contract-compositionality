# Contract Compositionality

A HOL4 formalization of a theory of specifications, components, contracts, and compositionality. The formalization largely follows a [paper](https://doi.org/10.1007/978-3-030-61467-6_22) by Nyberg, Westman, and Gurov. Some parts build on an [earlier formalization](https://github.com/hedengran/compositionality) by Hedengran.

## Building

Requirements:
- [Poly/ML 5.8.1](https://github.com/polyml/polyml/releases/tag/v5.8.1) (or later)
- [HOL4 kananaskis-14](https://github.com/HOL-Theorem-Prover/HOL/releases/tag/kananaskis-14)

The default Makefile task, which assumes `Holmake` is available on the system, builds all core HOL4 theories:

```shell
make
```

## Files

- [`folStringScript.sml`](fol/folStringScript.sml): first-order logic with string identifiers
- [`folStringInterpScript.sml`](fol/folStringInterpScript.sml): some simple first-order theories using string identifiers
- [`compSpecUtilityScript.sml`](semantics/compSpecUtilityScript.sml): some utility definitions and results
- [`compSpecScript.sml`](semantics/compSpecScript.sml): definition of abstract syntax for specifications, components, and predicates, and definition of proof system
- [`compSpecMetaScript.sml`](semantics/compSpecMetaScript.sml): semantics and metatheory of specifications and components, including proof system soundness
- [`compSpecFolScript.sml`](semantics/compSpecFolScript.sml): interpretation as first-order theory
