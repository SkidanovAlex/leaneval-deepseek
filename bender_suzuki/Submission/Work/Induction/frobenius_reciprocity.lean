import Mathlib
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

-- Frobenius reciprocity `⟨Ind_H^G φ, ψ⟩_G = ⟨φ, Res_H^G ψ⟩_H` for `ψ` a class function on `G`
-- (and `φ : H → ℂ` arbitrary).  Expand the left side as a double sum over `g` and `x`; the
-- substitution `y = x * g * x⁻¹` (a bijection on each fibre) makes the inner sum
-- `∑_{y ∈ H} φ y * conj (ψ (x⁻¹ * y * x))`, and class-function-ness of `ψ` gives
-- `ψ (x⁻¹ * y * x) = ψ y`.  Then `|G| * |H|⁻¹ * |G|⁻¹ = |H|⁻¹`.
-- `Work.CharCore.cfInner f g = |G|⁻¹ * ∑_x f x * conj (g x)`.
theorem frobenius_reciprocity {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (φ : H → ℂ)
    (ψ : G → ℂ) (hψ : Work.CharCore.IsClassFun ψ) :
    Work.CharCore.cfInner (Work.Induction.indFun H φ) ψ
      = Work.CharCore.cfInner φ (Work.Induction.resFun H ψ) := by
  -- `F` is `φ` extended by zero off `H`; the defining summand of `indFun` at `x` is
  -- `F (x * g * x⁻¹)`.
  let F : G → ℂ := fun y => dite (y ∈ H) (fun hy => φ ⟨y, hy⟩) (fun _ => 0)
  -- Reindexing the inner sum: for fixed `x` the substitution `g ↦ x * g * x⁻¹` is a
  -- bijection of `G`, and `ψ` is a class function, so the summand becomes independent of `x`.
  have hper : ∀ x : G, (∑ g : G, F (x * g * x⁻¹) * star (ψ g))
      = ∑ y : G, F y * star (ψ y) := by
    intro x
    have hbij : Function.Bijective (fun g : G => x * g * x⁻¹) :=
      Function.bijective_iff_has_inverse.mpr
        ⟨fun y => x⁻¹ * y * x, fun y => by group, fun y => by group⟩
    have h1 : (∑ g : G, F (x * g * x⁻¹) * star (ψ g))
        = ∑ y : G, F y * star (ψ (x⁻¹ * y * x)) := by
      refine Finset.sum_bijective (fun g : G => x * g * x⁻¹) hbij (fun i => by simp) ?_
      intro i _
      show F (x * i * x⁻¹) * star (ψ i)
          = F (x * i * x⁻¹) * star (ψ (x⁻¹ * (x * i * x⁻¹) * x))
      rw [show x⁻¹ * (x * i * x⁻¹) * x = i from by group]
    have h2 : (∑ y : G, F y * star (ψ (x⁻¹ * y * x))) = ∑ y : G, F y * star (ψ y) := by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [show x⁻¹ * y * x = x⁻¹ * y * (x⁻¹)⁻¹ from by group, hψ y x⁻¹]
    rw [h1, h2]
  -- Converting the sum over `G` of `F` into the sum over the subgroup `H`.
  have hFsum : (∑ y : G, F y * star (ψ y)) = ∑ h : H, φ h * star (ψ (h : G)) := by
    have h1 : (∑ y : G, F y * star (ψ y))
        = ∑ y ∈ Finset.univ.filter (fun y : G => y ∈ H), F y * star (ψ y) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases hy : y ∈ H <;> simp [F, hy]
    have h2 : (∑ y ∈ Finset.univ.filter (fun y : G => y ∈ H), F y * star (ψ y))
        = ∑ h : H, φ h * star (ψ (h : G)) := by
      rw [show (∑ y ∈ Finset.univ.filter (fun y : G => y ∈ H), F y * star (ψ y))
            = ∑ a : Subtype (fun y : G => y ∈ H), F (a : G) * star (ψ (a : G)) from
          Finset.sum_subtype (Finset.univ.filter (fun y : G => y ∈ H)) (fun y => by simp)
            (fun y : G => F y * star (ψ y))]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      simp [F, h.2]
    rw [h1, h2]
  have hdef : ∀ g : G, indFun H φ g = (Nat.card H : ℂ)⁻¹ * ∑ x : G, F (x * g * x⁻¹) := by
    intro g; rw [indFun_apply_def]
  -- The double-sum computation of the left-hand side.
  have key : (∑ g : G, indFun H φ g * star (ψ g))
      = (Nat.card H : ℂ)⁻¹ * (Fintype.card G : ℂ) * (∑ h : H, φ h * star (ψ (h : G))) := by
    calc (∑ g : G, indFun H φ g * star (ψ g))
        = (Nat.card H : ℂ)⁻¹ * ∑ g : G, (∑ x : G, F (x * g * x⁻¹)) * star (ψ g) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun g _ => ?_)
            rw [hdef g, mul_assoc]
        _ = (Nat.card H : ℂ)⁻¹ * ∑ g : G, ∑ x : G, F (x * g * x⁻¹) * star (ψ g) := by
            congr 1
            refine Finset.sum_congr rfl (fun g _ => ?_)
            rw [Finset.sum_mul]
        _ = (Nat.card H : ℂ)⁻¹ * ∑ x : G, ∑ g : G, F (x * g * x⁻¹) * star (ψ g) := by
            congr 1
            exact Finset.sum_comm
        _ = (Nat.card H : ℂ)⁻¹ * ∑ x : G, ∑ y : G, F y * star (ψ y) := by
            congr 1
            refine Finset.sum_congr rfl (fun x _ => hper x)
        _ = (Nat.card H : ℂ)⁻¹ * (Fintype.card G : ℂ) * (∑ y : G, F y * star (ψ y)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
        _ = (Nat.card H : ℂ)⁻¹ * (Fintype.card G : ℂ)
              * (∑ h : H, φ h * star (ψ (h : G))) := by
            rw [hFsum]
  rw [CharCore.cfInner_apply, CharCore.cfInner_apply]
  simp only [starRingEnd_apply, resFun_apply]
  rw [key]
  rw [show (Nat.card H : ℂ) = (Fintype.card H : ℂ) from by rw [Nat.card_eq_fintype_card]]
  have hG : (Fintype.card G : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero
  have hH : (Fintype.card H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero
  field_simp

end Work.Induction
