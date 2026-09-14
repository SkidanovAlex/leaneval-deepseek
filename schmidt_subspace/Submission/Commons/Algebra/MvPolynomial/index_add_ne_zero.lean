import Mathlib
import Submission.Commons.Algebra.MvPolynomial.index_properties_pos_vanishing

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators

/-- The index of any polynomial is nonnegative, for arbitrary weights `r`. -/
lemma indexSet_sInf_nonneg {K : Type*} [CommSemiring K] {σ : Type*} [Fintype σ]
    (α : σ → K) (r : σ → ℕ) (P : MvPolynomial σ K) :
    0 ≤ sInf (indexSet α r P) := by
  rw [indexSet_eq_image]
  rcases ((indexTay α P).support.image (indexWt r)).eq_empty_or_nonempty with h | h
  · rw [h, Finset.coe_empty, Real.sInf_empty]
  · exact le_csInf h.to_set (fun x hx => by
      rcases Finset.mem_image.mp hx with ⟨m, _, rfl⟩
      exact indexWt_nonneg m)

/-- Subadditivity of the index in the correct form: the hypothesis `P + Q ≠ 0` is necessary
(otherwise `ind (P + Q) = ind 0 = sInf ∅ = 0` while `min (ind P) (ind Q) = ind P` can be `> 0`). -/
theorem index_add_ne_zero {K : Type*} [Field K] [CharZero K] {σ : Type*} [Fintype σ]
    (α : σ → K) (r : σ → ℕ) :
    let taylor := fun (P : MvPolynomial σ K) =>
      MvPolynomial.aeval (fun i => MvPolynomial.C (α i) + MvPolynomial.X i) P
    let ind := fun (P : MvPolynomial σ K) =>
      sInf {t : ℝ | ∃ m ∈ (taylor P).support, t = ∑ i, (m i : ℝ) / (r i : ℝ)}
    (∀ P Q : MvPolynomial σ K, P + Q ≠ 0 → min (ind P) (ind Q) ≤ ind (P + Q)) := by
  classical
  dsimp only
  intro P Q hPQ
  change min (sInf (indexSet α r P)) (sInf (indexSet α r Q))
      ≤ sInf (indexSet α r (P + Q))
  -- the support of `taylor (P+Q)` is nonempty
  have hne : (indexTay α (P + Q)).support.Nonempty :=
    MvPolynomial.support_nonempty.mpr ((indexTay_injective α).ne hPQ)
  -- pick a minimizing monomial
  obtain ⟨mstar, hmstar, hmin⟩ :=
    (indexTay α (P + Q)).support.exists_min_image (indexWt r) hne
  -- hence the index of `P + Q` is the weight of `mstar`
  have hIndC : sInf (indexSet α r (P + Q)) = indexWt r mstar := by
    rw [indexSet_eq_image]
    refine le_antisymm ?_ ?_
    · refine csInf_le ?_ ?_
      · exact ⟨0, fun x hx => by
          rcases Finset.mem_image.mp hx with ⟨m, _, rfl⟩
          exact indexWt_nonneg m⟩
      · exact Finset.mem_image.mpr ⟨mstar, hmstar, rfl⟩
    · refine le_csInf ?_ ?_
      · exact ⟨indexWt r mstar, Finset.mem_image.mpr ⟨mstar, hmstar, rfl⟩⟩
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨m, hm, rfl⟩
        exact hmin m hm
  -- the support of `taylor (P+Q)` sits inside the union of the two supports
  have hsub : (indexTay α (P + Q)).support ⊆
      (indexTay α P).support ∪ (indexTay α Q).support := by
    have hC : indexTay α (P + Q) = indexTay α P + indexTay α Q := by
      simp only [indexTay, map_add]
    rw [hC]
    exact MvPolynomial.support_add
  have hmstar' : mstar ∈ (indexTay α P).support ∪ (indexTay α Q).support :=
    hsub hmstar
  rcases Finset.mem_union.mp hmstar' with hmA | hmB
  · have hle : sInf (indexSet α r P) ≤ indexWt r mstar := by
      rw [indexSet_eq_image]
      refine csInf_le ?_ ?_
      · exact ⟨0, fun x hx => by
          rcases Finset.mem_image.mp hx with ⟨m, _, rfl⟩
          exact indexWt_nonneg m⟩
      · exact Finset.mem_image.mpr ⟨mstar, hmA, rfl⟩
    calc min (sInf (indexSet α r P)) (sInf (indexSet α r Q))
        ≤ sInf (indexSet α r P) := min_le_left _ _
      _ ≤ indexWt r mstar := hle
      _ = sInf (indexSet α r (P + Q)) := hIndC.symm
  · have hle : sInf (indexSet α r Q) ≤ indexWt r mstar := by
      rw [indexSet_eq_image]
      refine csInf_le ?_ ?_
      · exact ⟨0, fun x hx => by
          rcases Finset.mem_image.mp hx with ⟨m, _, rfl⟩
          exact indexWt_nonneg m⟩
      · exact Finset.mem_image.mpr ⟨mstar, hmB, rfl⟩
    calc min (sInf (indexSet α r P)) (sInf (indexSet α r Q))
        ≤ sInf (indexSet α r Q) := min_le_right _ _
      _ ≤ indexWt r mstar := hle
      _ = sInf (indexSet α r (P + Q)) := hIndC.symm

end Commons.Algebra.MvPolynomial
