import Mathlib
import Submission.Work.Induction.Defs
import Submission.Work.Induction.indFun_TI_apply

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

/-- In the self-normalizing case `N_G(H) = H`, the sum `∑_{x ∈ N_G(H)} φ (x h x⁻¹)` of the
conjugated values of a class function `φ` on `H` collapses: every summand is `φ h`, so the sum
is `|H| * φ h`.  (For `x ∈ N_G(H) = H` the conjugate `x h x⁻¹` is the conjugate of `h` by the
element `⟨x, _⟩` of `H`, and `φ` is a class function on `H`.) -/
theorem sum_conjMem_normalizer_eq_self_normalizing {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) (φ : H → ℂ) (hN : Work.Induction.normalizer H = H)
    (hφ : Work.CharCore.IsClassFun φ) (h : H) :
    (∑ x : Work.Induction.normalizer H, φ (Work.Induction.conjMem H x h))
      = (Nat.card H : ℂ) * φ h := by
  have hterm : ∀ x : normalizer H, φ (conjMem H x h) = φ h := by
    intro x
    have : conjMem H x h
        = (⟨(x : G), le_of_eq hN x.2⟩ : H) * h * (⟨(x : G), le_of_eq hN x.2⟩ : H)⁻¹ := by
      apply Subtype.ext
      simp [conjMem_val]
    rw [this]
    exact hφ h ⟨(x : G), le_of_eq hN x.2⟩
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card]
  rw [hN]

-- Self-normalizing TI case (the form used for Frobenius complements): for `h ∈ H`, `h ≠ 1`,
-- `Res_H^G (Ind_H^G φ) h = φ h`.  From the general TI formula
-- `Work.Induction.indFun_TI_apply` (with `N_G(H) = H`) the left side is
-- `|H|⁻¹ ∑_{x : H} φ (x*h*x⁻¹) = |H|⁻¹ * |H| * φ h` because `φ` is a class function.
theorem indFun_TI_apply_self_normalizing {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    (φ : H → ℂ) (hTI : Work.Induction.IsTI H) (hN : Work.Induction.normalizer H = H)
    (hφ : Work.CharCore.IsClassFun φ) (h : H) (hh : h ≠ 1) :
    Work.Induction.resFun H (Work.Induction.indFun H φ) h = φ h := by
  -- General TI formula: `|H| * Res_H^G (Ind_H^G φ) h = ∑_{x ∈ N_G(H)} φ (x h x⁻¹)`.
  have hkey := indFun_TI_apply H φ hTI h hh
  -- Self-normalizing case: the sum over `N_G(H) = H` is `|H| * φ h`.
  have hsum := sum_conjMem_normalizer_eq_self_normalizing H φ hN hφ h
  rw [hsum] at hkey
  -- Cancel the nonzero factor `|H|`.
  have hcard : (Nat.card H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  exact mul_left_cancel₀ hcard hkey

end Work.Induction
