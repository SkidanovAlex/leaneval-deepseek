import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Descent of `K`-linear span along a field extension

Let `K ⊆ L` be a field extension (`K`, `L` fields with `[Algebra K L]`), `σ` any type,
`S : Set (MvPolynomial σ K)` and `x : MvPolynomial σ K`.  If the base change of `x` to `L`
lies in the `L`-linear span of the base changes of `S`, then `x` already lies in the
`K`-linear span of `S`:

`MvPolynomial.map (algebraMap K L) x ∈ span_L (map (algebraMap K L) '' S) → x ∈ span_K S`.

This is the "faithful flatness of a field extension" statement for the free `K`-module
`MvPolynomial σ K`.  The proof given here is the elementary coefficient argument: choose a
`K`-linear retraction `ρ : L →ₗ[K] K` of `algebraMap K L` (it exists because `K` is a field,
so `K` is a direct summand of the `K`-vector space `L`).  Writing the hypothesis as a finite
`L`-linear combination `∑ lᵢ • (map sᵢ)`, the element `∑ ρ lᵢ • sᵢ` is a `K`-linear combination
of elements of `S` having the same coefficients as `x` after base change; comparing
coefficients gives `x = ∑ ρ lᵢ • sᵢ ∈ span_K S`.
-/

namespace Work.MotV5.ASLocal

theorem mem_span_of_map_mem_span {K L : Type*} [Field K] [Field L] [Algebra K L]
    {σ : Type*} {S : Set (MvPolynomial σ K)} {x : MvPolynomial σ K}
    (h : MvPolynomial.map (algebraMap K L) x ∈
        Submodule.span L (MvPolynomial.map (algebraMap K L) '' S)) :
    x ∈ Submodule.span K S := by
  classical
  -- ### Step 0: a `K`-linear retraction `ρ` of `algebraMap K L`.
  have hker : (LinearMap.toSpanSingleton K L (1 : L)).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro a b hab
    have hab' : a • (1 : L) = b • (1 : L) := hab
    have h0 : algebraMap K L (a - b) = 0 := by
      have h1 : (a - b) • (1 : L) = 0 := by rw [sub_smul, hab', sub_self]
      rwa [Algebra.smul_def, mul_one] at h1
    by_contra hne
    have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
    have h1 : algebraMap K L (a - b) * (algebraMap K L (a - b))⁻¹ = 1 := by
      rw [← map_inv₀, ← map_mul, mul_inv_cancel₀ hne', map_one]
    rw [h0, zero_mul] at h1
    exact one_ne_zero h1.symm
  obtain ⟨ρ, hρ⟩ :=
    LinearMap.exists_leftInverse_of_injective (LinearMap.toSpanSingleton K L (1 : L)) hker
  have hρ1 : ρ 1 = 1 := by
    have := DFunLike.congr_fun hρ (1 : K)
    simpa using this
  have hρ_alg : ∀ a : K, ρ (algebraMap K L a) = a := by
    intro a
    have hsm : algebraMap K L a = a • (1 : L) := by rw [Algebra.smul_def, mul_one]
    rw [hsm, map_smul, hρ1, smul_eq_mul, mul_one]
  -- ### Step 1: write the hypothesis as a finite `L`-linear combination.
  obtain ⟨c, hsupp, hc⟩ := (Submodule.mem_span_set).mp h
  -- ### Step 2: choose preimages in `S` of the elements of the support.
  let b : MvPolynomial σ L → MvPolynomial σ K :=
    fun y => if hy : y ∈ MvPolynomial.map (algebraMap K L) '' S then Classical.choose hy else 0
  have hbspec : ∀ y (hy : y ∈ MvPolynomial.map (algebraMap K L) '' S),
      b y ∈ S ∧ MvPolynomial.map (algebraMap K L) (b y) = y := by
    intro y hy
    simp only [b, dite_eq_left hy]
    exact Classical.choose_spec hy
  -- ### Step 3: the candidate `K`-linear combination of elements of `S`.
  set z : MvPolynomial σ K := c.sum (fun y l => (ρ l) • b y) with hz
  have hzmem : z ∈ Submodule.span K S := by
    rw [hz, Finsupp.sum_of_support_subset c (Finset.Subset.refl _) (fun y l => (ρ l) • b y)
      (fun i _ => by simp)]
    refine Submodule.sum_mem _ (fun y hy => ?_)
    exact Submodule.smul_mem _ _ (Submodule.subset_span ((hbspec y (hsupp hy)).1))
  have hxz : x = z := by
    apply MvPolynomial.ext
    intro m
    have hA : x.coeff m = ρ ((MvPolynomial.map (algebraMap K L) x).coeff m) := by
      rw [MvPolynomial.coeff_map, hρ_alg]
    have hB : (MvPolynomial.map (algebraMap K L) x).coeff m
        = c.sum (fun y l => l * algebraMap K L ((b y).coeff m)) := by
      rw [← hc, ← MvPolynomial.lcoeff_apply L m, map_finsuppSum]
      apply Finsupp.sum_congr
      intro y hy
      have hy' : y ∈ MvPolynomial.map (algebraMap K L) '' S := hsupp hy
      have hcoeff : y.coeff m = (MvPolynomial.map (algebraMap K L) (b y)).coeff m := by
        rw [(hbspec y hy').2]
      rw [map_smul, MvPolynomial.lcoeff_apply, hcoeff, MvPolynomial.coeff_map, smul_eq_mul]
    have hC : ρ (c.sum (fun y l => l * algebraMap K L ((b y).coeff m)))
        = c.sum (fun y l => ((b y).coeff m) * ρ l) := by
      rw [map_finsuppSum]
      apply Finsupp.sum_congr
      intro y hy
      have hsm : (c y) * algebraMap K L ((b y).coeff m) = ((b y).coeff m) • (c y) := by
        rw [Algebra.smul_def, mul_comm]
      rw [hsm, map_smul, smul_eq_mul]
    have hD : z.coeff m = c.sum (fun y l => ((b y).coeff m) * ρ l) := by
      rw [hz, ← MvPolynomial.lcoeff_apply K m, map_finsuppSum]
      apply Finsupp.sum_congr
      intro y hy
      rw [map_smul, MvPolynomial.lcoeff_apply, smul_eq_mul, mul_comm]
    rw [hA, hB, hC, hD]
  rw [hxz]
  exact hzmem

end Work.MotV5.ASLocal
