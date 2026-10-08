import Mathlib
import Submission.Work.Induction.Defs
import Submission.Work.Induction.indFun_TI_apply
import Submission.Work.Induction.isClassFun_indFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

/-- `indFun H φ` is constant on conjugacy classes: if `g₁` is conjugate to `g₂` (Mathlib's
`IsConj`), then `Ind_H^G φ g₁ = Ind_H^G φ g₂`. -/
theorem indFun_eq_of_isConj {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (φ : H → ℂ)
    {g₁ g₂ : G} (hg : IsConj g₁ g₂) : indFun H φ g₁ = indFun H φ g₂ := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hg
  rw [← indFun_conj_apply H φ g₁ c, hc]

/-- Self-normalizing TI case: for `h ∈ H` with `h ≠ 1`, the induced function
`Ind_H^G φ` takes the value `φ h` at `h`.  Multiplying the TI formula
`Work.Induction.indFun_TI_apply` by `|H|` and using `N_G(H) = H`, the left-hand side becomes
`|H| · Ind_H^G φ h` while the sum has `|H|` summands, each equal to `φ h` because `φ` is a
class function. -/
theorem indFun_apply_self_normalizing {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    (φ : H → ℂ) (hTI : IsTI H) (hN : normalizer H = H) (hφ : CharCore.IsClassFun φ)
    (h : H) (hh : h ≠ 1) : indFun H φ (h : G) = φ h := by
  have hcard : (Nat.card H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  -- `N_G(H) = H`, so an element `x` of the normalizer may be viewed as an element of `H`,
  -- and then `conjMem H x h` is a conjugate of `h` in `H`.
  have hconst : ∀ x : normalizer H, φ (conjMem H x h) = φ h := by
    intro x
    have hx : conjMem H x h = (⟨x.1, hN.le x.2⟩ : H) * h * (⟨x.1, hN.le x.2⟩ : H)⁻¹ := by
      apply Subtype.ext
      simp [conjMem]
    rw [hx]
    exact hφ h ⟨x.1, hN.le x.2⟩
  have hsum : (∑ x : normalizer H, φ (conjMem H x h)) = (Nat.card H : ℂ) * φ h := by
    have hcongr : (∑ x : normalizer H, φ (conjMem H x h)) = ∑ x : normalizer H, φ h :=
      Finset.sum_congr rfl fun x _ => hconst x
    have hcardN : Nat.card (normalizer H) = Nat.card H := by rw [hN]
    rw [hcongr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      hcardN]
  have hmain : (Nat.card H : ℂ) * resFun H (indFun H φ) h = (Nat.card H : ℂ) * φ h := by
    rw [indFun_TI_apply H φ hTI h hh, hsum]
  have hcancel : resFun H (indFun H φ) h = φ h := by
    have h := congrArg (fun z : ℂ => (Nat.card H : ℂ)⁻¹ * z) hmain
    rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul, ← mul_assoc, inv_mul_cancel₀ hcard,
      one_mul] at h
    exact h
  simpa using hcancel

-- Brauer–Suzuki normalisation: for `H` a self-normalizing TI subgroup and `φ` a class function
-- on `H`, the induced function `Ind_H^G φ` takes the value `φ h` at every `g` conjugate to a
-- non-identity `h ∈ H` (no matter whether `g` lies in `H`).  Reindex `x ↦ x * c` for `c` with
-- `c * g * c⁻¹ = h` to reduce to the case `g = h ∈ H` (then use `indFun_TI_apply` and
-- `IsClassFun φ` to rewrite every summand `φ (y * h * y⁻¹)` to `φ h`).
theorem indFun_apply_of_isConj {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    (hTI : Work.Induction.IsTI H) (hN : Work.Induction.normalizer H = H) (φ : H → ℂ)
    (hφ : Work.CharCore.IsClassFun φ) (g : G) (h : H) (hh : h ≠ 1) (hg : IsConj g (h : G)) :
    Work.Induction.indFun H φ g = φ h := by
  rw [indFun_eq_of_isConj H φ hg]
  exact indFun_apply_self_normalizing H φ hTI hN hφ h hh

end Work.Induction
