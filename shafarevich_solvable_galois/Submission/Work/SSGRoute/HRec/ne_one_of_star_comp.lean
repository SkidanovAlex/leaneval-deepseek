import Mathlib.RingTheory.Henselian
import Mathlib.Basic.Complex.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SSGRoute.HRec.exists_sq_eq_of_ne_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The conjugation attached to a real place is nontrivial

If `Ψ (c x) = star (Ψ x)` for all `x : Ω`, then `c ≠ 1`: were `c = 1`, `star` would fix `Ψ x` for
every `x`, hence `Ψ (Ω) ⊆ ℝ`; but `Ψ` carries a square root `i` of `-1` to an element of `ℂ` whose
square is `-1`, which cannot be real (`r * r = -1` is impossible in `ℝ`).

Naming note (this cost two red drafts): in this pin the conjugation on `ℂ` is `Star.star` /
`starRingEnd ℂ`; `Complex.conj` does **not** resolve as a term (`Complex.conj_im`,
`Complex.star_def` do — `Data/Complex/Basic.lean:471`, `:501`).  So never write `Complex.conj x` in
a goal or term; instead rewrite the *function* `Star.star` to `conj` inside an equation with
`rw [Complex.star_def]`, e.g. `congrArg Complex.im hcp` followed by `rw [Complex.star_def] at h`.
-/

noncomputable section

namespace Work.SSGRoute.HRec

theorem ne_one_of_star_comp {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    {Ψ : Ω →+* ℂ} {c : Ω ≃ₐ[k] Ω}
    (hc : ∀ x : Ω, Ψ (c x) = starRingEnd ℂ (Ψ x)) : c ≠ 1 := by
  intro h
  have hfix : ∀ x : Ω, starRingEnd ℂ (Ψ x) = Ψ x := by
    intro x
    rw [← hc x, h, AlgEquiv.one_apply]
  obtain ⟨i, hi⟩ := exists_sq_eq_of_ne_zero (Ω := Ω) (a := (-1 : Ω)) (by norm_num)
  have hsq : Ψ i * Ψ i = -1 := by
    rw [← map_mul, hi]
    simp
  have him : (Ψ i).im = 0 := by
    have hcp : Star.star (Ψ i) = Ψ i := hfix i
    have h' := congrArg Complex.im hcp
    rw [Complex.star_def] at h'
    rw [Complex.conj_im] at h'
    linarith
  have hre := congrArg Complex.re hsq
  simp only [Complex.mul_re, Complex.neg_re, Complex.one_re] at hre
  rw [him] at hre
  nlinarith [mul_self_nonneg (Ψ i).re]

end Work.SSGRoute.HRec
