import Mathlib
import Submission.Work.SeedCertNum.A1Defs
import Submission.Work.SeedCertNum.multiplier2_eq_prod_of_fixed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `multiplier2` of a period-`5` orbit of `T_c` equals the product `Π` of the seed certificate

The interval-certificate layer `Submission/Work/SeedCertNum/A1Defs.lean` writes the third
component `P₃` of the `(P₁,P₂,P₃)` system as `Π - 1`, where

  `Π(u) = ∏_{k<5} (2‖Z_k(u)‖)²`,  in the *nested* form `Nk 0 * (Nk 1 * (Nk 2 * (Nk 3 * Nk 4)))`,
  `Z_k(u) = (T_{c(u)})^[k] (z(u))`,  `Nk k = 4‖Z_k‖²`.

Here we identify this interval-bookkeeping object with the genuine dynamical quantity: for any
`u` whose orbit closes up, `(T_{c(u)})^[5] (z(u)) = z(u)`, the multiplier of the second return
map `(T_c)^[10] = (Tsq c)^[5]` is exactly `Π(u)` (a non-negative real number, coerced to `ℂ`).

The proof is the composition of the two halves:

* `multiplier2_eq_prod_of_fixed` (`Submission/Work/SeedCertNum/multiplier2_eq_prod_of_fixed.lean`)
  rewrites the multiplier as `∏_{k<5} (2‖(T_c)^[k] z‖)²`;
* `Z_eq_iterate` identifies the certificate's iterate `Z x₀ k u` with the honest orbit
  `(T_{cOf x₀ u})^[k] (zOf u)`;
* and the `Finset` range product is rearranged into the nested form `Π`.
-/

namespace Work.SeedCertNum

open LeanEval.ComplexAnalysis (Tantibar)

/-- The certificate's iterate `Z x₀ k u` is the honest `k`-th iterate of the antiholomorphic
quadratic `T_{cOf x₀ u}` at `zOf u`. -/
theorem Z_eq_iterate (x₀ : ℝ) (u : Work.SeedCert.E3) (k : ℕ) :
    Work.SeedCert.Z x₀ k u = (Tantibar (Work.SeedCert.cOf x₀ u))^[k] (Work.SeedCert.zOf u) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Work.SeedCert.Z_succ, ih, Function.iterate_succ_apply']
    rfl

theorem multiplier2_eq_Pi {x₀ : ℝ} {u : Work.SeedCert.E3}
    (hfix : (LeanEval.ComplexAnalysis.Tantibar (Work.SeedCert.cOf x₀ u))^[5] (Work.SeedCert.zOf u)
      = Work.SeedCert.zOf u) :
    Work.Landing.multiplier2 (Work.SeedCert.cOf x₀ u) 5 (Work.SeedCert.zOf u)
      = ((Work.SeedCert.Pi x₀ u : ℝ) : ℂ) := by
  rw [multiplier2_eq_prod_of_fixed hfix]
  congr 1
  have hg : ∀ k, (2 * ‖(Tantibar (Work.SeedCert.cOf x₀ u))^[k] (Work.SeedCert.zOf u)‖)^2
      = Work.SeedCert.Nk x₀ k u := by
    intro k
    rw [← Z_eq_iterate x₀ u k, Work.SeedCert.Nk]
    ring
  rw [Finset.prod_congr rfl (fun k _ => hg k)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, Work.SeedCert.Pi]
  ring

end Work.SeedCertNum
