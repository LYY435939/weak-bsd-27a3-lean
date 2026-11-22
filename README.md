# Weak BSD for the Fermat cubic in Lean

This project formalizes the rank part of the Birch–Swinnerton-Dyer conjecture for the elliptic curve `y² = x³ − 432` over `ℚ` (LMFDB 27.a3). The result is a previously known individual case.

The theorem is `BSD.FermatCubic.weakBSD` in `BSD/FermatCubicBSD.lean`. It states that this curve's Hasse–Weil L-series has a meromorphic continuation whose order at `s = 1` equals the Mordell–Weil rank. The proof gives an entire continuation, proves its value at 1 is nonzero, and proves the rank is zero.

It uses Lean 4.33.1 and mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. Run `lake exe cache get`, `lake build BSD`, and `lake env lean Verify.lean` to build and inspect the axioms. A fresh build and Lean kernel replay on CPU succeeded. The final theorem depends on `propext`, `Classical.choice`, and `Quot.sound`.

`BSD/JacobiTripleProduct.lean` contains an adapted MIT-licensed proof by Axiom Math with attribution and license in the file.
