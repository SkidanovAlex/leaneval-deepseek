import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.Coherent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.PhiProps` — the elementary properties of the coherent-state transform

Companion to `Submission/Work/BoseB4/Coherent.lean`: the level API of the Fock
space and the two structural facts `Phi_apply` (component form) and `Phi_lift`
(spectator operators act levelwise).

The non-elementary facts (`Phi_a0d`, the Bargmann isometry, the anti-Wick
substitution) are separate modules because their proofs are analytic:
`Submission.Work.BoseB4.Phi_a0d`, `Submission.Work.BoseB4.Bargmann_isometry`,
`Submission.Work.BoseB4.Kafz_monomial`.
-/

noncomputable section

open scoped lp NNReal ENNReal
open MeasureTheory

namespace Work.BoseB4

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Level API -/

lemma level_eq_single (n : ℕ) (v : E) : level E n v = lp.single 2 n v := by
  simp [level]

lemma Embed_level (n : ℕ) (v : E) :
    (Embed E (Finsupp.single n v) : Fock E) = lp.single 2 n v := by
  rw [Embed_single, level_eq_single]

/-- Distinct condensate levels are orthogonal; on a level the inner product is
the spectators' one. -/
@[simp]
lemma inner_level (n m : ℕ) (v w : E) :
    inner ℂ (level E n v) (level E m w) = if n = m then inner ℂ v w else 0 := by
  rw [level_eq_single, level_eq_single, lp.inner_single_left, lp.single_apply, Pi.single_apply]
  by_cases h : n = m
  · subst h; simp
  · simp [h]

lemma Embed_eq_sum_level (Ψ : FockCore E) :
    (Embed E Ψ : Fock E) = ∑ n ∈ Ψ.support, level E n (Ψ n) := by
  rw [Embed_eq_sum]
  exact Finset.sum_congr rfl fun n _ => (level_eq_single n (Ψ n)).symm

@[simp]
lemma norm_level (n : ℕ) (v : E) : ‖level E n v‖ = ‖v‖ := by
  rw [level_eq_single, lp.norm_single (by norm_num)]

/-- Distinct condensate levels span orthogonal subspaces. -/
@[simp]
lemma level_orthogonal (n m : ℕ) (v w : E) (h : n ≠ m) :
    inner ℂ (level E n v) (level E m w) = 0 := by
  rw [inner_level, if_neg h]

/-! ## The coherent-state transform, componentwise -/

@[simp]
lemma Phi_zero (z : ℂ) : Phi (0 : FockCore E) z = 0 := map_zero (PhiLin (E := E) z)

lemma Phi_apply (Ψ : FockCore E) (z : ℂ) :
    Phi Ψ z = ∑ n ∈ Ψ.support, cohWeight n z • Ψ n := by
  simp only [Phi, PhiLin, Finsupp.lsum, Finsupp.sum]
  rfl

lemma Phi_lift (B : E →ₗ[ℂ] E) (Ψ : FockCore E) (z : ℂ) :
    Phi (lift B Ψ) z = B (Phi Ψ z) := by
  induction Ψ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Phi_add, hf, hg]
  | single n v => simp [lift_single, Phi_single]

end Work.BoseB4
