import Mathlib
import Submission.Work.Induction.Defs
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.isClassFun_indFun
import Submission.Work.Induction.indFun_TI_apply
import Submission.Work.Induction.indFun_apply_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

/-- **Restriction of an induced class function, self-normalizing TI case.**  If `H` is a TI
subgroup with `N_G(H) = H` and `ψ : H → ℂ` is a class function with `ψ 1 = 0`, then
`Res_H^G (Ind_H^G ψ) = ψ`.

At `h = 1` both sides are `0`, since `Ind_H^G ψ 1 = [G:H] * ψ 1 = 0`
(`Work.Induction.indFun_apply_one`).  For `h ≠ 1`, the TI restriction formula
`Work.Induction.indFun_TI_apply` expresses `|H| * Ind_H^G ψ h` as `∑_{x ∈ N_G(H)} ψ (x h x⁻¹)`;
with `N_G(H) = H` each summand is the conjugate of `h` by an element of `H`
(`MulEquiv.subgroupCongr hN`), hence equal to `ψ h` because `ψ` is a class function, and the
sum is `|H| * ψ h`.  Cancelling `|H| ≠ 0` gives the claim. -/
theorem resFun_indFun_eq_self_of_isTI_selfNormalizing {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) (hTI : IsTI H) (hN : normalizer H = H) (ψ : H → ℂ)
    (hψ : CharCore.IsClassFun ψ) (hψ1 : ψ 1 = 0) :
    resFun H (indFun H ψ) = ψ := by
  funext h
  by_cases hh : h = 1
  · -- `h = 1`: `Ind_H^G ψ 1 = [G:H] * ψ 1 = 0 = ψ 1`.
    subst hh
    simp only [resFun_apply, Subgroup.coe_one, indFun_apply_one, hψ1, mul_zero]
  · -- `h ≠ 1`: use the TI restriction formula and `N_G(H) = H`.
    have hkey := indFun_TI_apply H ψ hTI h hh
    -- Each summand `ψ (conjMem H x h)` is `ψ` at a conjugate of `h` by an element of `H`.
    have hterm : ∀ x : normalizer H, ψ (conjMem H x h) = ψ h := by
      intro x
      have he : conjMem H x h =
          MulEquiv.subgroupCongr hN x * h * (MulEquiv.subgroupCongr hN x)⁻¹ := by
        apply Subtype.ext
        simp [conjMem_val]
      rw [he]
      exact hψ h (MulEquiv.subgroupCongr hN x)
    -- `N_G(H)` and `H` have the same cardinality.
    have hcard : Fintype.card ↥(normalizer H) = Fintype.card ↥H :=
      Fintype.card_congr (MulEquiv.subgroupCongr hN).toEquiv
    have hsum : (∑ x : normalizer H, ψ (conjMem H x h)) = (Nat.card H : ℂ) * ψ h := by
      rw [Finset.sum_congr rfl (fun x _ => hterm x)]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      rw [hcard, Nat.card_eq_fintype_card]
    rw [hsum] at hkey
    have hne : (Nat.card ↥H : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
    exact mul_left_cancel₀ hne hkey

-- Brauer–Suzuki isometry: for a self-normalizing TI subgroup `H` and class functions
-- `φ, ψ : H → ℂ` vanishing at `1`, the induction map `f ↦ Ind_H^G f` preserves the inner
-- product.  Combining the restriction formula `Res_H^G (Ind_H^G ψ) = ψ` (which holds when
-- `ψ 1 = 0` and `N_G(H) = H`) with Frobenius reciprocity gives
-- `⟨Ind φ, Ind ψ⟩_G = ⟨φ, Res_H^G (Ind ψ)⟩_H = ⟨φ, ψ⟩_H`.
-- (`Ind_H^G ψ` is a class function by `Work.Induction.isClassFun_indFun`, and at `1` it takes
-- the value `[G:H] * ψ 1 = 0` by `Work.Induction.indFun_apply_one`.)
theorem cfInner_indFun_eq_of_TI {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    (hTI : Work.Induction.IsTI H) (hN : Work.Induction.normalizer H = H) (φ ψ : H → ℂ)
    (hφ : Work.CharCore.IsClassFun φ) (hψ : Work.CharCore.IsClassFun ψ)
    (hφ1 : φ 1 = 0) (hψ1 : ψ 1 = 0) :
    Work.CharCore.cfInner (Work.Induction.indFun H φ) (Work.Induction.indFun H ψ)
      = Work.CharCore.cfInner φ ψ := by
  -- Frobenius reciprocity, then `Res_H^G (Ind_H^G ψ) = ψ`.
  rw [frobenius_reciprocity H φ (indFun H ψ) (isClassFun_indFun H ψ),
    resFun_indFun_eq_self_of_isTI_selfNormalizing H hTI hN ψ hψ hψ1]

end Work.Induction
