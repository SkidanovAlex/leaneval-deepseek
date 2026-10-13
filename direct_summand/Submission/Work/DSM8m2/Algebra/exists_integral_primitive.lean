import Mathlib
import Submission.Work.DSM8m.Presentation.isFractionRing_adjoin_singleton

set_option linter.unusedVariables false

namespace Work.DSM8m2.Algebra

/-!
# An integral primitive element with minimal-polynomial compatibility

Let `A` be a domain with fraction field `K = Frac A`, and let `L/K` be a finite separable field
extension, with the `A`-algebra structure on `L` compatible with `A → K → L`.  We prove that `L`
has an integral primitive element `η` over `A` whose minimal polynomial over `A` reduces, under
`A → K`, to the minimal polynomial of `η` over `K`.

The construction: choose a primitive element `α` of `L/K` (primitive element theorem, using
separability); let `f = minpoly K α`.  Clearing denominators of the coefficients of `f` gives
`d ∈ A \ {0}` with `d·f.coeff i ∈ A` (the workspace lemma `exists_polynomial_clear_denom`).
Then `η := d·α` is a root of the monic `g ∈ A[X]` whose `i`-th coefficient is
`d^(n-i)·f.coeff i` (so `g` has degree `n = [L:K]` and is monic), hence `η` is integral over `A`;
`K(η) = K(α) = L`; and `natDegree (minpoly A η) ≤ n = natDegree (minpoly K η)` together with
`minpoly K η ∣ (minpoly A η).map (algebraMap A K)` forces `(minpoly A η).map = minpoly K η`.
-/

/-- A polynomial of the shape `X ^ n + Σ_{i<n} C (c i) * X ^ i` is monic of degree `n`. -/
theorem monic_X_pow_add_sum {A : Type*} [CommRing A] [Nontrivial A] (n : ℕ) (c : ℕ → A) :
    (Polynomial.X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (c i) * Polynomial.X ^ i).Monic ∧
    (Polynomial.X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (c i) * Polynomial.X ^ i).natDegree
      = n := by
  have hSu : ∀ N, (∑ i ∈ Finset.range n, Polynomial.C (c i) * Polynomial.X ^ i).coeff N
      = ∑ i ∈ Finset.range n, (Polynomial.C (c i) * Polynomial.X ^ i).coeff N := by
    intro N; simp
  have hS : (∑ i ∈ Finset.range n, Polynomial.C (c i) * Polynomial.X ^ i).coeff n = 0 := by
    rw [hSu]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Polynomial.coeff_C_mul_X_pow]
    exact ite_eq_right (fun h => (Finset.mem_range.mp hi).ne h.symm)
  have hSn : (Polynomial.X ^ n + ∑ i ∈ Finset.range n,
      Polynomial.C (c i) * Polynomial.X ^ i).coeff n = 1 := by
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, ite_eq_left rfl, hS, add_zero]
  have hSgt : ∀ N, n < N → (Polynomial.X ^ n + ∑ i ∈ Finset.range n,
      Polynomial.C (c i) * Polynomial.X ^ i).coeff N = 0 := by
    intro N hN
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, ite_eq_right (ne_of_lt hN).symm, zero_add,
      hSu]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Polynomial.coeff_C_mul_X_pow]
    exact ite_eq_right (ne_of_gt (lt_of_lt_of_le (Finset.mem_range.mp hi) (le_of_lt hN)))
  have hnd : (Polynomial.X ^ n + ∑ i ∈ Finset.range n,
      Polynomial.C (c i) * Polynomial.X ^ i).natDegree = n := by
    apply le_antisymm
    · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hSgt
    · exact Polynomial.le_natDegree_of_ne_zero (by rw [hSn]; exact one_ne_zero)
  refine ⟨?_, hnd⟩
  show Polynomial.leadingCoeff _ = 1
  rw [Polynomial.leadingCoeff, hnd, hSn]

/-- Given a monic `f ∈ K[X]` with root `x ∈ L`, and `d ∈ A` clearing the denominators of the
coefficients of `f` (`d * f.coeff i ∈ A`), the element `d · x` is a root of a monic polynomial
`g ∈ A[X]` with `natDegree g = natDegree f`.  In particular `d · x` is integral over `A`. -/
theorem exists_cleared_poly {A K L : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L]
    (x : L) (f : Polynomial K) (hf : f.Monic) (hfroot : Polynomial.aeval x f = 0) (d : A)
    (hclear : ∀ i, algebraMap A K d * f.coeff i ∈ (algebraMap A K).range) :
    ∃ g : Polynomial A, g.Monic ∧ g.natDegree = f.natDegree ∧
      Polynomial.aeval (algebraMap A L d * x) g = 0 := by
  classical
  choose b hb using fun i => Set.mem_range.mp (hclear i)
  set n := f.natDegree with hn
  have hfne1 : f ≠ 1 := by
    intro h1; rw [h1] at hfroot; simp at hfroot
  have hfc : f.coeff n = 1 := by rw [hn]; simpa using hf.leadingCoeff
  refine ⟨Polynomial.X ^ n + ∑ i ∈ Finset.range n,
      Polynomial.C (d ^ (n - 1 - i) * b i) * Polynomial.X ^ i, ?_, ?_, ?_⟩
  · exact (monic_X_pow_add_sum n (fun i => d ^ (n - 1 - i) * b i)).1
  · exact ((monic_X_pow_add_sum n (fun i => d ^ (n - 1 - i) * b i)).2).trans hn
  · have hterm : ∀ i ∈ Finset.range n,
        (Polynomial.aeval (algebraMap A L d * x))
          (Polynomial.C (d ^ (n - 1 - i) * b i) * Polynomial.X ^ i)
        = (algebraMap A L d) ^ n * (algebraMap K L (f.coeff i) * x ^ i) := by
      intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      have hni : n - 1 - i + 1 = n - i := by omega
      have hnn : n - i + i = n := by omega
      have hbi : algebraMap A L (b i) = algebraMap A L d * algebraMap K L (f.coeff i) := by
        rw [IsScalarTower.algebraMap_apply A K L (b i), hb i, map_mul,
          IsScalarTower.algebraMap_apply A K L d]
      simp only [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_pow]
      rw [map_mul, map_pow, hbi, mul_pow]
      rw [show (algebraMap A L) d ^ (n - 1 - i) *
            ((algebraMap A L) d * (algebraMap K L) (f.coeff i)) *
            ((algebraMap A L) d ^ i * x ^ i)
          = ((algebraMap A L) d ^ (n - 1 - i) * (algebraMap A L) d *
              (algebraMap A L) d ^ i) * ((algebraMap K L) (f.coeff i) * x ^ i) from by ring]
      rw [← pow_succ, hni, ← pow_add, hnn]
    have haeval_top : (Polynomial.aeval (algebraMap A L d * x)) (Polynomial.X ^ n : Polynomial A)
        = (algebraMap A L d) ^ n * x ^ n := by
      rw [map_pow, Polynomial.aeval_X, mul_pow]
    have hsum : (Polynomial.aeval (algebraMap A L d * x))
          (∑ i ∈ Finset.range n, Polynomial.C (d ^ (n - 1 - i) * b i) * Polynomial.X ^ i)
        = (algebraMap A L d) ^ n *
          ∑ i ∈ Finset.range n, algebraMap K L (f.coeff i) * x ^ i := by
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact hterm i hi
    have hsplit : Polynomial.aeval x f
        = x ^ n + ∑ i ∈ Finset.range n, algebraMap K L (f.coeff i) * x ^ i := by
      rw [Polynomial.aeval_eq_sum_range]
      simp only [Algebra.smul_def]
      rw [← hn, Finset.sum_range_succ]
      rw [show algebraMap K L (f.coeff n) * x ^ n = x ^ n from by rw [hfc, map_one, one_mul]]
      rw [add_comm]
    have key : (algebraMap A L d) ^ n * x ^ n + (algebraMap A L d) ^ n *
        (∑ i ∈ Finset.range n, algebraMap K L (f.coeff i) * x ^ i) = 0 := by
      rw [← mul_add ((algebraMap A L d) ^ n), ← hsplit, hfroot, mul_zero]
    rw [map_add, haeval_top, hsum]
    exact key

theorem exists_integral_primitive {A K L : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] (hAL : Function.Injective (algebraMap A L))
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    ∃ η : L, IsIntegral A η ∧ Algebra.adjoin K ({η} : Set L) = ⊤ ∧
      (minpoly A η).map (algebraMap A K) = minpoly K η := by
  classical
  -- a primitive element `α` of `L/K`
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  have hα_alg : IsAlgebraic K α := IsAlgebraic.of_finite K α
  have hα' : Algebra.adjoin K ({α} : Set L) = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hα_alg hα
  -- clear the denominators of the coefficients of `minpoly K α`
  obtain ⟨s, hs, q, hq⟩ :=
    _root_.Work.DSM8m.Presentation.exists_polynomial_clear_denom (A := A) (K := K)
      (minpoly K α)
  have hsne : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
  have hKne : algebraMap A K s ≠ 0 :=
    fun h => hsne (IsFractionRing.injective A K (by rw [h, map_zero]))
  have hclear : ∀ i, algebraMap A K s * (minpoly K α).coeff i ∈ (algebraMap A K).range := by
    intro i
    exact ⟨q.coeff i, by rw [← Polynomial.coeff_C_mul, ← hq, Polynomial.coeff_map]⟩
  -- the monic polynomial `g` over `A` vanishing at `s · α`
  obtain ⟨g, hgmonic, hgdeg, hgroot⟩ :=
    exists_cleared_poly α (minpoly K α) (minpoly.monic (IsIntegral.of_finite K α))
      (minpoly.aeval K α) s hclear
  -- `K(s·α) = K(α) = L`
  have hadjoin : Algebra.adjoin K ({algebraMap A L s * α} : Set L) = ⊤ := by
    have hmem : α ∈ Algebra.adjoin K ({algebraMap A L s * α} : Set L) := by
      have hU : algebraMap K L ((algebraMap A K s)⁻¹) * (algebraMap A L s * α) = α := by
        rw [IsScalarTower.algebraMap_apply A K L s, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hKne,
          map_one, one_mul]
      have hmem2 : algebraMap K L ((algebraMap A K s)⁻¹) * (algebraMap A L s * α) ∈
          Algebra.adjoin K ({algebraMap A L s * α} : Set L) :=
        mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin (Set.mem_singleton _))
      rw [hU] at hmem2
      exact hmem2
    have hle : Algebra.adjoin K ({α} : Set L) ≤
        Algebra.adjoin K ({algebraMap A L s * α} : Set L) :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hmem)
    exact top_le_iff.mp (by rw [← hα']; exact hle)
  refine ⟨algebraMap A L s * α, ⟨g, hgmonic, hgroot⟩, hadjoin, ?_⟩
  -- the minimal-polynomial compatibility
  set η := algebraMap A L s * α with hη
  have hint : IsIntegral A η := ⟨g, hgmonic, hgroot⟩
  have hηalg : IsAlgebraic K η := IsAlgebraic.of_finite K η
  have hKη : IntermediateField.adjoin K ({η} : Set L) = ⊤ :=
    (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic hηalg).mpr hadjoin
  have hdegA : (minpoly K α).natDegree = Module.finrank K L :=
    (Field.primitive_element_iff_minpoly_natDegree_eq K α).mp hα
  have hdegB : (minpoly K η).natDegree = Module.finrank K L :=
    (Field.primitive_element_iff_minpoly_natDegree_eq K η).mp hKη
  have hle_g : (minpoly A η).natDegree ≤ g.natDegree :=
    Polynomial.natDegree_le_natDegree (minpoly.min A η hgmonic hgroot)
  have hmonK : (minpoly K η).Monic := minpoly.monic (IsIntegral.of_finite K η)
  have hmonA : ((minpoly A η).map (algebraMap A K)).Monic :=
    (minpoly.monic hint).map (algebraMap A K)
  have hdiv : minpoly K η ∣ (minpoly A η).map (algebraMap A K) :=
    minpoly.dvd_map_of_isScalarTower A K η
  have hndmap : ((minpoly A η).map (algebraMap A K)).natDegree = (minpoly A η).natDegree :=
    (minpoly.monic hint).natDegree_map (algebraMap A K)
  have hdeg_le : ((minpoly A η).map (algebraMap A K)).natDegree ≤ (minpoly K η).natDegree := by
    rw [hndmap, hdegB, ← hdegA, ← hgdeg]
    exact hle_g
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonK hmonA hdiv hdeg_le

end Work.DSM8m2.Algebra
