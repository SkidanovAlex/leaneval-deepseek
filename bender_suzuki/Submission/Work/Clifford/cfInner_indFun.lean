import Mathlib
import Submission.Work.Clifford.CFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Clifford

open Classical Finset

/-- Sum over `G` of a function supported on a subgroup `H`, written in "extension by zero"
form, equals the sum over `H`. -/
private lemma sum_ite_mem_eq_sum_subtype {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] (f : H → ℂ) :
    (∑ y : G, (if hy : y ∈ H then f ⟨y, hy⟩ else 0)) = ∑ h : H, f h := by
  have h1 : (∑ y : G, (if hy : y ∈ H then f ⟨y, hy⟩ else 0))
      = ∑ y ∈ Finset.univ.filter (fun y : G => y ∈ H),
          (fun y => if hy : y ∈ H then f ⟨y, hy⟩ else 0) y := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ H <;> simp [ha]
  rw [h1]
  rw [Finset.sum_subtype (p := fun y : G => y ∈ H) (s := Finset.univ.filter (fun y : G => y ∈ H))
        (fun x => by simp) (fun y => if hy : y ∈ H then f ⟨y, hy⟩ else 0)]
  apply Finset.sum_congr rfl
  intro a _
  simp

/-- **Frobenius reciprocity** for `Work.Clifford.cfInner` and `Work.Clifford.indFun`: for a
function `φ` on a subgroup `H ≤ G` and a **class function** `ψ` on `G`,
`⟪Ind_H^G φ, ψ⟫_G = ⟪φ, Res_H^G ψ⟫_H`. -/
theorem cfInner_indFun {G : Type*} [Group G] [Fintype G] {H : Subgroup G} [Fintype H] (φ : H → ℂ)
    {ψ : G → ℂ} (hψ : Work.Clifford.IsClassFun ψ) :
    Work.Clifford.cfInner (Work.Clifford.indFun H φ) ψ =
      Work.Clifford.cfInner φ (Work.Clifford.resFun H ψ) := by
  set S : ℂ := ∑ h : H, φ h * starRingEnd ℂ (ψ h) with hS
  have hA : ∀ x : G, (∑ g : G, (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0) * starRingEnd ℂ (ψ g)) = S := by
    intro x
    rw [hS]
    have hsum : (∑ g : G, (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0) * starRingEnd ℂ (ψ g))
        = ∑ g : G, (fun y : G => (if hy : y ∈ H then φ ⟨y, hy⟩ else 0) * starRingEnd ℂ (ψ y))
            (((MulAut.conj x : G ≃* G) : G ≃ G) g) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [show ((MulAut.conj x : G ≃* G) : G ≃ G) g = x * g * x⁻¹ from by simp [MulAut.conj_apply]]
      simp only []
      rw [hψ g x]
    rw [hsum]
    rw [Equiv.sum_comp (((MulAut.conj x : G ≃* G) : G ≃ G))
          (fun y : G => (if hy : y ∈ H then φ ⟨y, hy⟩ else 0) * starRingEnd ℂ (ψ y))]
    have hB : (∑ y : G, (if hy : y ∈ H then φ ⟨y, hy⟩ else 0) * starRingEnd ℂ (ψ y))
        = ∑ y : G, (if hy : y ∈ H then φ ⟨y, hy⟩ * starRingEnd ℂ (ψ y) else 0) := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y ∈ H <;> simp [hy]
    rw [hB]
    exact sum_ite_mem_eq_sum_subtype H (fun h : H => φ h * starRingEnd ℂ (ψ (h : G)))
  have hmain : cfInner (indFun H φ) ψ = (Fintype.card H : ℂ)⁻¹ * S := by
    have hfac : (∑ g : G, ((Nat.card H : ℂ)⁻¹ * ∑ x : G,
          (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0)) * starRingEnd ℂ (ψ g))
        = (Nat.card H : ℂ)⁻¹ * ∑ g : G, (∑ x : G,
          (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0)) * starRingEnd ℂ (ψ g) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    have hbig : (∑ g : G, (∑ x : G,
          (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0)) * starRingEnd ℂ (ψ g))
        = (Fintype.card G : ℂ) * S := by
      calc (∑ g : G, (∑ x : G, (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0)) * starRingEnd ℂ (ψ g))
          = ∑ g : G, ∑ x : G, (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0) * starRingEnd ℂ (ψ g) :=
            Finset.sum_congr rfl (fun g _ => Finset.sum_mul _ _ _)
        _ = ∑ x : G, ∑ g : G, (if hx : x * g * x⁻¹ ∈ H then φ ⟨x * g * x⁻¹, hx⟩ else 0) * starRingEnd ℂ (ψ g) :=
            Finset.sum_comm
        _ = ∑ x : G, S := Finset.sum_congr rfl (fun x _ => hA x)
        _ = (Fintype.card G : ℂ) * S := by rw [Finset.sum_const, nsmul_eq_mul]; simp
    simp only [cfInner, indFun]
    rw [hfac, hbig]
    rw [show (Nat.card H : ℂ) = (Fintype.card H : ℂ) from by rw [Nat.card_eq_fintype_card]]
    have hcard : (Fintype.card G : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero
    have hcancel : (Fintype.card G : ℂ)⁻¹ * ((Fintype.card G : ℂ) * S) = S := by
      rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
    calc (Fintype.card G : ℂ)⁻¹ * ((Fintype.card H : ℂ)⁻¹ * ((Fintype.card G : ℂ) * S))
        = (Fintype.card H : ℂ)⁻¹ * ((Fintype.card G : ℂ)⁻¹ * ((Fintype.card G : ℂ) * S)) := by ring
      _ = (Fintype.card H : ℂ)⁻¹ * S := by rw [hcancel]
  have hR : cfInner φ (resFun H ψ) = (Fintype.card H : ℂ)⁻¹ * S := by
    simp only [cfInner, resFun]
    rw [hS]
  rw [hmain, hR]

end Work.Clifford
