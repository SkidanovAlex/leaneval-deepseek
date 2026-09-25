/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The one-sided `C^{k,α}` extension from `pd n ρ 1` to `pd n ρ c`

A function which is `C^∞` on the polydisc `pd n ρ 1` and has finite `C^{k,α}` norm there extends
to a `C^k` function on the larger polydisc `pd n ρ c` (`c > 1`), agreeing with the original on
`pd n ρ 1`, with a `C^{k,α}` norm bound uniform in the function.

The proof is assembled from two pieces:

* `Work.NN.Final.one_sided_disc_extension` — the one-variable input: a `C^k` function with finite
  `C^{k,α}` norm on `U × ball(0,1)` (with `U` an open region in an arbitrary real normed space)
  extends to `U × ball(0,c)` (this is proved by a Seeley reflection in the last coordinate, whose
  evaluation points stay strictly inside the unit disc);
* `Work.NN.Final.one_sided_extension_le_of_discExt` — the coordinate-by-coordinate assembly: the
  one-variable extension is applied once per coordinate of `ℂⁿ`, with the parameter region the
  already-extended region in the other coordinates; the `C^{k,α}` estimates multiply and the
  extensions agree with the original function on `pd n ρ 1` at every step.
-/
import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.DiscExtDefs
import Submission.Work.NN.Final.one_sided_disc_extension
import Submission.Work.NN.Final.one_sided_extension_le_of_discExt

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set Metric

namespace Work.NN.Final

open Work.CR.Flat

/-- The one-variable disc extension implies the predicate `DiscExt α c`. -/
theorem discExt_of_disc_extension {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {c : ℝ} (hc : 1 < c) :
    DiscExt.{0} α c := fun X _ _ => one_sided_disc_extension (X := X) hα0 hα1 hc

theorem one_sided_extension_le {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hα0 : 0 < α) (hα1 : α < 1) {c : ℝ} (hc : 1 < c) : ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ (k : ℕ) (v : (Fin n → ℂ) → ℂ), (∀ m : ℕ, ContDiffOn ℝ m v (Work.NN.Final.pd n ρ 1)) → Work.CR.Flat.holderNorm k α v (Work.NN.Final.pd n ρ 1) ≠ ⊤ → ∃ vtilde : (Fin n → ℂ) → ℂ, ContDiffOn ℝ (k : WithTop ENat) vtilde (Work.NN.Final.pd n ρ c) ∧ (∀ z ∈ Work.NN.Final.pd n ρ 1, vtilde z = v z) ∧ Work.CR.Flat.holderNorm k α vtilde (Work.NN.Final.pd n ρ c) ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α v (Work.NN.Final.pd n ρ 1) := by
  exact one_sided_extension_le_of_discExt hα0 hα1 hc
    (discExt_of_disc_extension hα0 hα1 hc) n ρ hρ

end Work.NN.Final
