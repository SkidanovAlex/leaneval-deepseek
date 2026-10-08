import Mathlib
import Submission.Work.BSW.Cases.Order.Setup

namespace Work.BSW.Char

theorem induceApplyCoeSupportSubset {G : Type} [Group G] [Fintype G]
    {K H : Subgroup G} [Invertible (Nat.card ↥H : ℂ)]
    (hKH : K ≤ H) (hTI : OddOrder.GroupTheory.IsTISubset ((K : Set G) \ {1}) H)
    (ψ : OddOrder.RepresentationTheory.ClassFunction ↥H ℂ)
    (hψ : ∀ x : ↥H, (x : G) ∉ K → ψ x = 0)
    {a : ↥K} (ha : (a : G) ≠ 1) :
    OddOrder.RepresentationTheory.ClassFunction.induce H ψ (a : G) = ψ ⟨(a : G), hKH a.2⟩ := by
  classical
  -- `K ∖ {1}` is a TI subset of `H`: any `x` with `x⁻¹ * a * x ∈ K` already lies in `H`.
  have ha_set : (a : G) ∈ ((K : Set G) \ {1}) := ⟨a.2, by simpa using ha⟩
  have hmemH : ∀ x : G, x⁻¹ * (a : G) * x ∈ K → x ∈ H := by
    intro x hx
    have hne : x⁻¹ * (a : G) * x ≠ 1 := by
      intro h
      have h2 : x * (x⁻¹ * (a : G) * x) * x⁻¹ = (a : G) := by group
      exact ha (by rw [← h2, h]; group)
    refine hTI x ⟨x⁻¹ * (a : G) * x, ⟨hx, by simpa using hne⟩, ?_⟩
    have key : x * (x⁻¹ * (a : G) * x) * x⁻¹ = (a : G) := by group
    rw [key]
    exact ha_set
  -- Each induction summand is `ψ a` when `x⁻¹ * a * x ∈ K`, and `0` otherwise.
  have hterm : ∀ x : G, OddOrder.RepresentationTheory.ClassFunction.induceTerm H ψ x (a : G) =
      if x⁻¹ * (a : G) * x ∈ K then ψ ⟨(a : G), hKH a.2⟩ else 0 := by
    intro x
    by_cases hx : x⁻¹ * (a : G) * x ∈ K
    · rw [ite_eq_left hx]
      have hxH : x⁻¹ * (a : G) * x ∈ H := hKH hx
      rw [OddOrder.RepresentationTheory.ClassFunction.induceTerm_of_mem ψ hxH]
      have hxmemH : x ∈ H := hmemH x hx
      have hconj : (⟨x⁻¹ * (a : G) * x, hxH⟩ : ↥H)
          = (⟨x, hxmemH⟩ : ↥H)⁻¹ * ⟨(a : G), hKH a.2⟩ * ((⟨x, hxmemH⟩ : ↥H)⁻¹)⁻¹ := by
        apply Subtype.ext
        simp
      rw [hconj]
      exact ψ.conj_eq ⟨(a : G), hKH a.2⟩ (⟨x, hxmemH⟩ : ↥H)⁻¹
    · rw [ite_eq_right hx]
      by_cases hxH : x⁻¹ * (a : G) * x ∈ H
      · rw [OddOrder.RepresentationTheory.ClassFunction.induceTerm_of_mem ψ hxH]
        exact hψ ⟨_, hxH⟩ hx
      · rw [OddOrder.RepresentationTheory.ClassFunction.induceTerm_of_not_mem ψ hxH]
  -- Hence the induction sum equals `|H| * ψ a` (each summand is either `0` or `ψ a`, and
  -- either all of `H` contributes or else `ψ a = 0`).
  have hsum : (∑ x : G, OddOrder.RepresentationTheory.ClassFunction.induceTerm H ψ x (a : G))
      = (Nat.card ↥H : ℂ) * ψ ⟨(a : G), hKH a.2⟩ := by
    rw [Finset.sum_congr rfl (fun x _ => hterm x)]
    by_cases hc : ψ ⟨(a : G), hKH a.2⟩ = 0
    · rw [show (∑ x : G, (if x⁻¹ * (a : G) * x ∈ K then ψ ⟨(a : G), hKH a.2⟩ else 0)) = 0 by
          apply Finset.sum_eq_zero
          intro x _
          split
          · exact hc
          · rfl,
        hc, mul_zero]
    · -- `ψ a ≠ 0` forces `x ∈ H → x⁻¹ * a * x ∈ K`, so the contributing set is all of `H`.
      have hxH' : ∀ x : G, x ∈ H → x⁻¹ * (a : G) * x ∈ H := fun x hxH =>
        H.mul_mem (H.mul_mem (H.inv_mem hxH) (hKH a.2)) hxH
      have hiff : ∀ x : G, x⁻¹ * (a : G) * x ∈ K ↔ x ∈ H := by
        intro x
        refine ⟨hmemH x, fun hxH => ?_⟩
        by_contra hxK
        have h1 : ψ ⟨x⁻¹ * (a : G) * x, hxH' x hxH⟩ = 0 := hψ ⟨_, hxH' x hxH⟩ hxK
        have hconj : (⟨x⁻¹ * (a : G) * x, hxH' x hxH⟩ : ↥H)
            = (⟨x, hxH⟩ : ↥H)⁻¹ * ⟨(a : G), hKH a.2⟩ * ((⟨x, hxH⟩ : ↥H)⁻¹)⁻¹ := by
          apply Subtype.ext
          simp
        have h2 : ψ ⟨x⁻¹ * (a : G) * x, hxH' x hxH⟩ = ψ ⟨(a : G), hKH a.2⟩ := by
          rw [hconj]
          exact ψ.conj_eq ⟨(a : G), hKH a.2⟩ (⟨x, hxH⟩ : ↥H)⁻¹
        exact hc (by rw [← h2]; exact h1)
      have hcard : (Finset.univ.filter (fun x : G => x⁻¹ * (a : G) * x ∈ K)).card
          = Nat.card ↥H := by
        have h1 : (Finset.univ.filter (fun x : G => x⁻¹ * (a : G) * x ∈ K)).card
            = (Finset.univ.filter (fun x : G => x ∈ H)).card := by
          congr 1
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hiff x
        rw [h1, Nat.card_eq_fintype_card]
        exact (Fintype.card_ofFinset (Finset.univ.filter (fun x : G => x ∈ H))
          (by intro x; simp)).symm
      rw [← Finset.sum_filter, Finset.sum_const, hcard, nsmul_eq_mul]
  rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply, hsum, ← mul_assoc,
    invOf_mul_self, one_mul]

end Work.BSW.Char
