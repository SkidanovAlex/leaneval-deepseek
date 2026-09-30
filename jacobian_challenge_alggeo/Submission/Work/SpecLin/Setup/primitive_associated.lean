import Mathlib
import Submission.Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

namespace Work.SpecLin.Setup

theorem primitive_associated {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (p : Polynomial K) (hp : p ≠ 0) :
    ∃ q : Polynomial R, q.IsPrimitive ∧ ∃ μ : K, μ ≠ 0 ∧
      Polynomial.map (algebraMap R K) q = Polynomial.C μ * p := by
  classical
  -- The algebra structure `R[X] → K[X]` given by `Polynomial.map` makes `K[X]` the
  -- localisation of `R[X]` at the non-zero constants.
  letI : Algebra (Polynomial R) (Polynomial K) := Polynomial.algebra R K
  haveI hloc : IsLocalization ((nonZeroDivisors R).map Polynomial.C) (Polynomial K) :=
    Polynomial.isLocalization (nonZeroDivisors R) K
  have hcoe : ∀ q : Polynomial R,
      (algebraMap (Polynomial R) (Polynomial K)) q = Polynomial.map (algebraMap R K) q := by
    intro q
    rw [Polynomial.algebraMap_def]
    rfl
  -- Clear denominators: `C s * p` is the image of an integral polynomial `x.1`.
  obtain ⟨x, hx⟩ := IsLocalization.surj ((nonZeroDivisors R).map Polynomial.C) p
  obtain ⟨s, hs_mem, hs_eq⟩ := Submonoid.mem_map.mp (x.2).property
  have hs_ne : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs_mem
  have hsK : algebraMap R K s ≠ 0 :=
    fun h => hs_ne (IsFractionRing.injective R K (by simpa using h))
  have hC_ne : Polynomial.C (algebraMap R K s) ≠ 0 := by simpa using hsK
  have hCp_ne : Polynomial.C (algebraMap R K s) * p ≠ 0 := mul_ne_zero hC_ne hp
  -- Reduce `x.1` by a common divisor of its coefficients to a primitive polynomial `q'`.
  obtain ⟨c, q', hcq, hq'mem⟩ :=
    Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map (R := R) (B := Polynomial R) x.1
  have hx' : Polynomial.map (algebraMap R K) x.1 =
      Polynomial.C (algebraMap R K s) * p := by
    simp only [hcoe, ← hs_eq, Polynomial.map_C] at hx
    rw [mul_comm] at hx
    exact hx.symm
  have hmain : Polynomial.C (algebraMap R K s) * p =
      Polynomial.C (algebraMap R K c) * Polynomial.map (algebraMap R K) q' := by
    rw [← hx', hcq, Polynomial.map_smul, Polynomial.smul_eq_C_mul]
  have hcK : algebraMap R K c ≠ 0 := by
    intro hc0
    have hz : Polynomial.C (algebraMap R K c) * Polynomial.map (algebraMap R K) q' = 0 := by
      rw [hc0, Polynomial.C_0, zero_mul]
    exact hCp_ne (hmain.trans hz)
  -- `q'` is primitive: otherwise a non-unit constant would divide all of its coefficients.
  have hqprim : q'.IsPrimitive := by
    intro r hr
    by_contra hru
    have hrmem : r ∈ IsLocalRing.maximalIdeal R := by
      by_contra hmem
      exact hru (IsLocalRing.notMem_maximalIdeal.mp hmem)
    have hCr : Polynomial.C r ∈
        (IsLocalRing.maximalIdeal R).map (algebraMap R (Polynomial R)) := by
      have h := Ideal.mem_map_of_mem (f := algebraMap R (Polynomial R)) hrmem
      rwa [Polynomial.C_eq_algebraMap]
    obtain ⟨q'', hq''⟩ := hr
    exact hq'mem (hq'' ▸ Ideal.mul_mem_right q'' _ hCr)
  refine ⟨q', hqprim, (algebraMap R K c)⁻¹ * algebraMap R K s,
    mul_ne_zero (inv_ne_zero hcK) hsK, ?_⟩
  have h1 : Polynomial.C ((algebraMap R K c)⁻¹) *
      (Polynomial.C (algebraMap R K c) * Polynomial.map (algebraMap R K) q') =
      Polynomial.C ((algebraMap R K c)⁻¹) *
      (Polynomial.C (algebraMap R K s) * p) := by rw [hmain.symm]
  have hlhs : Polynomial.C ((algebraMap R K c)⁻¹) *
      (Polynomial.C (algebraMap R K c) * Polynomial.map (algebraMap R K) q') =
      Polynomial.map (algebraMap R K) q' := by
    rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hcK, Polynomial.C_1, one_mul]
  have hrhs : Polynomial.C ((algebraMap R K c)⁻¹) *
      (Polynomial.C (algebraMap R K s) * p) =
      Polynomial.C ((algebraMap R K c)⁻¹ * algebraMap R K s) * p := by
    rw [← mul_assoc, ← Polynomial.C_mul]
  exact hlhs.symm.trans (h1.trans hrhs)

end Work.SpecLin.Setup
