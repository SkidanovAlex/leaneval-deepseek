import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

open MvPolynomial UpperHalfPlane

namespace Commons.Analysis.MvPolynomial

theorem isStable_of_degree_le_one (n d : ℕ) (hd : d ≤ 1)
  (f : homogeneousSubmodule (Fin n) ℝ d)
  (hnn : ∀ m, 0 ≤ MvPolynomial.coeff m f.1) :
  f.1 = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
    MvPolynomial.aeval ((fun h : UpperHalfPlane => (h : ℂ)) ∘ z) f.1 ≠ 0 := by
  classical
  by_cases hf0 : f.1 = 0
  · left
    exact hf0
  · right
    intro z
    have hd_cases : d = 0 ∨ d = 1 := by omega
    rcases hd_cases with rfl | rfl
    · -- d = 0
      have hmem : f.1 ∈ homogeneousSubmodule (Fin n) ℝ 0 := f.2
      have hmem_one : f.1 ∈ (1 : Submodule ℝ (MvPolynomial (Fin n) ℝ)) := by
        simpa [homogeneousSubmodule_zero] using hmem
      rcases (Submodule.mem_one.mp hmem_one) with ⟨c, hc⟩
      have hCf : MvPolynomial.C c = f.1 := by
        simpa [MvPolynomial.algebraMap_eq] using hc
      have hc_nonneg : 0 ≤ c := by
        have h := hnn 0
        rw [← hCf, MvPolynomial.coeff_C] at h
        simpa using h
      have hc_ne : c ≠ 0 := by
        intro hc0
        apply hf0
        rw [← hCf, hc0]
        simp
      have hc_pos : 0 < c := lt_of_le_of_ne hc_nonneg (Ne.symm hc_ne)
      have heval :
          MvPolynomial.aeval ((fun h : UpperHalfPlane => (h : ℂ)) ∘ z) f.1 = (c : ℂ) := by
        rw [← hCf, MvPolynomial.aeval_C]
        rfl
      rw [heval]
      exact (Complex.ofReal_ne_zero).2 (ne_of_gt hc_pos)
    · -- d = 1
      have hmem : f.1 ∈ homogeneousSubmodule (Fin n) ℝ 1 := f.2
      have hmem_span :
          f.1 ∈ Submodule.span ℝ (Set.range (X : Fin n → MvPolynomial (Fin n) ℝ)) := by
        simpa [homogeneousSubmodule_one_eq_span_X] using hmem
      rcases (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem_span with ⟨c, hc⟩
      have hsum : f.1 = ∑ i, c i • (X i : MvPolynomial (Fin n) ℝ) := hc.symm
      have hc_nonneg : ∀ i, 0 ≤ c i := by
        intro i
        have hcoeff_i :
            MvPolynomial.coeff (Finsupp.single i 1) f.1 = c i := by
          rw [hsum]
          simp [MvPolynomial.coeff_sum, MvPolynomial.smul_eq_C_mul,
            MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, Finsupp.single_eq_single_iff]
        have h := hnn (Finsupp.single i 1)
        simpa [hcoeff_i] using h
      have hexists_pos : ∃ i, 0 < c i := by
        by_contra h
        have hc0 : ∀ i, c i = 0 := by
          intro i
          have hle : c i ≤ 0 := le_of_not_gt (by
            intro hi
            exact h ⟨i, hi⟩)
          exact le_antisymm hle (hc_nonneg i)
        apply hf0
        rw [hsum]
        simp [hc0]
      have heval :
          MvPolynomial.aeval ((fun h : UpperHalfPlane => (h : ℂ)) ∘ z) f.1 =
            ∑ i, c i • ((z i : UpperHalfPlane) : ℂ) := by
        rw [hsum, map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul, MvPolynomial.aeval_X]
        rfl
      have him_pos : 0 < (∑ i, c i • ((z i : UpperHalfPlane) : ℂ)).im := by
        rw [Complex.im_sum]
        have hcongr :
            (∑ i, (c i • ((z i : UpperHalfPlane) : ℂ)).im) =
              ∑ i, c i * (z i).im := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Complex.real_smul, Complex.im_ofReal_mul, UpperHalfPlane.coe_im]
        rw [hcongr]
        refine Finset.sum_pos' (s := Finset.univ) ?_ ?_
        · intro i hi
          exact mul_nonneg (hc_nonneg i) (le_of_lt (UpperHalfPlane.im_pos (z i)))
        · rcases hexists_pos with ⟨i, hi⟩
          exact ⟨i, by simp, mul_pos hi (UpperHalfPlane.im_pos (z i))⟩
      have hne : (∑ i, c i • ((z i : UpperHalfPlane) : ℂ)) ≠ 0 := by
        intro hzero
        have himzero : (∑ i, c i • ((z i : UpperHalfPlane) : ℂ)).im = 0 := by
          rw [hzero, Complex.zero_im]
        linarith
      rw [heval]
      exact hne

end Commons.Analysis.MvPolynomial