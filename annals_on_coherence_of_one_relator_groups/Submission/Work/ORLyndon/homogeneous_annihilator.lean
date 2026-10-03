import Mathlib
import Submission.Work.ORLyndon.Fox

namespace Work.ORLyndon

universe u v

theorem homogeneous_annihilator {G : Type u} [Group G] {K : Type v} [Field K]
    {H : Type v} [Group H] (χ : G →* H) (s : H) (b : MonoidAlgebra K G)
    (hb : ∀ g : G, b.coeff g ≠ 0 → χ g = s)
    {ι : Type u} [Fintype ι] [Nonempty ι] (t : ι → G) (c : ι → K) (hc : ∀ i, c i ≠ 0)
    (ht : ∀ i j : ι, χ (t i) = χ (t j) → i = j) :
    b * (∑ i, c i • MonoidAlgebra.of K G (t i)) = 0 → b = 0 := by
  intro hba
  -- Distribute `b` over the sum: `b * a = ∑ i, c i • (b * of (t i))`.
  have hsplit : b * (∑ i, c i • MonoidAlgebra.of K G (t i))
      = ∑ i, c i • (b * MonoidAlgebra.of K G (t i)) := by
    rw [Finset.mul_sum]
    simp only [mul_smul_comm]
  have hzero : ∑ i, c i • (b * MonoidAlgebra.of K G (t i)) = 0 := by
    rw [← hsplit]; exact hba
  -- Support of `b * of (t i)` lies in the coset `χ = s * χ (t i)`.
  have hcoset : ∀ (i : ι) (x : G), (b * MonoidAlgebra.of K G (t i)).coeff x ≠ 0 →
      χ x = s * χ (t i) := by
    intro i x hx
    have h1 : b.coeff (x * (t i)⁻¹) ≠ 0 := by
      rwa [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_mul_single_apply, mul_one] at hx
    have h2 : χ (x * (t i)⁻¹) = s := hb _ h1
    rw [map_mul, map_inv] at h2
    exact mul_inv_eq_iff_eq_mul.mp h2
  -- Since the cosets `s * χ (t i)` are pairwise distinct, each summand vanishes.
  have hFi : ∀ i, b * MonoidAlgebra.of K G (t i) = 0 := by
    intro i
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro x
    by_cases hx : (b * MonoidAlgebra.of K G (t i)).coeff x = 0
    · simpa using hx
    · exfalso
      have hxcoset : χ x = s * χ (t i) := hcoset i x hx
      have hsum0 : (∑ j, c j • (b * MonoidAlgebra.of K G (t j))).coeff x = 0 := by
        rw [hzero]; simp
      rw [show (∑ j, c j • (b * MonoidAlgebra.of K G (t j))).coeff x
            = ∑ j, c j * (b * MonoidAlgebra.of K G (t j)).coeff x from by
          simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul,
            Finsupp.smul_apply, smul_eq_mul]] at hsum0
      have hsingle : (∑ j, c j * (b * MonoidAlgebra.of K G (t j)).coeff x)
          = c i * (b * MonoidAlgebra.of K G (t i)).coeff x := by
        refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
        by_contra hne
        have hjc : (b * MonoidAlgebra.of K G (t j)).coeff x ≠ 0 := fun h => hne (by rw [h, mul_zero])
        have hjcoset : χ x = s * χ (t j) := hcoset j x hjc
        have hχ : χ (t i) = χ (t j) := by
          rw [hxcoset] at hjcoset
          exact mul_left_cancel hjcoset
        exact hj (ht i j hχ).symm
      rw [hsingle] at hsum0
      exact hx ((mul_eq_zero.mp hsum0).resolve_left (hc i))
  -- `of (t i)` is a unit, so right-multiplying by it is injective.
  have key := hFi (Classical.arbitrary ι)
  have hof : MonoidAlgebra.of K G (t (Classical.arbitrary ι)) *
      MonoidAlgebra.of K G ((t (Classical.arbitrary ι))⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  calc b = (b * MonoidAlgebra.of K G (t (Classical.arbitrary ι))) *
        MonoidAlgebra.of K G ((t (Classical.arbitrary ι))⁻¹) := by
        rw [mul_assoc, hof, mul_one]
    _ = 0 := by rw [key, zero_mul]

end Work.ORLyndon
