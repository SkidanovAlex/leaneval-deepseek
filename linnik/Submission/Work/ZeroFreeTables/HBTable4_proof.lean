/-
# ZeroFreeTables — HBTable4_proof

**HB Table 4** (Heath-Brown, *Zero-free regions for Dirichlet L-functions, and the
least prime in an arithmetic progression*, PLMS **64** (1992) 265–338, p. 43): for a
real character `χ₁` with real exceptional zero `ρ₁`, the second zero `ρ₀` of the
working region satisfies `λ₀ ≥ v` for each of the 24 tabulated pairs
`(λ₁, v) ∈ hbTable4`, and `λ₀ ≥ ρ₁`'s own `λ₁` when `ρ₁` is a repeated zero.

The proof is the finite assembly of the two analytic inputs of `Table4Defs`:

* `HBLemma8_3` (HB Lemma 8.3, the `P₃` method of §8.2) — the case in which the
  second zero `ρ₀` is not real.  Its left hand side (8.7) is a *rational* function
  of the ratios `(a+λ₁)/a`, `(a+λ₁)/(a+λ₀)` and of the parameters `a`, `K`, so the
  Table-4 witnesses `a`, `K` (HB's own printed ones for the rows at
  `λ₁ = 0.4, …, 1.294`, and two rational witnesses covering `[0, 0.3]`) are certified
  by kernel arithmetic (`Table4Cert`);
* `HBLemma8_2` (HB Lemma 8.2, the `µ⁰ = 0` case of the `F`-method) — the case in
  which `ρ₀` is real, and the repeated-zero case `ρ₀ = ρ₁`: the optimal test function
  of HB §7 at `k = 2` gives `λ₀ ≥ 2.427…`, of which the rational constant `2.293`
  needed by the table is used here.

`Table4Derive.hbTable4_of_engines` performs the finite assembly: the thresholds of
the two inputs are merged, `λ₀ ≥ v` is proved for every zero of the working region
(other than `ρ₁` and, in the real case, its conjugate) by locating the certificate
row covering `λ₁`, and the repeated-zero conjuncts are discharged by `HBLemma8_2`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.Table4Defs
import Submission.Work.ZeroFreeTables.Table4Derive
import Submission.Work.ZeroFreeTables.Table4.HB82
import Submission.Work.ZeroFreeTables.Table4.HB83

namespace Work.ZeroFreeTables

theorem HBTable4_proof : Work.ZeroFreeTables.HBTable4 :=
  hbTable4_of_engines Table4.HB83 Table4.HB82

end Work.ZeroFreeTables
