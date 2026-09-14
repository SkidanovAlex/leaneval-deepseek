import Mathlib
import Submission.Commons.Geometry.Convex.John.john_sandwich_symmetric

namespace Commons.GeometryOfNumbers.Lattice

open Module Filter

/-- For a symmetric convex body `K` with nonempty interior in `ℝⁿ`, the Minkowski functional
`gauge K` is equivalent, up to the factor `√n`, to a Euclidean norm:
there is a linear equivalence `T` with `‖T x‖ ≤ gauge K x ≤ √n ‖T x‖` for all `x`.

This is the "linear isomorphism to `ℓ₂ⁿ`" form of Fritz John's theorem for symmetric bodies; here
it is derived from `Commons.Geometry.Convex.John.john_sandwich_symmetric`. -/
theorem exists_gauge_euclidean_comparison {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hcvx : Convex ℝ K) (hcpt : IsCompact K) (hsymm : (∀ x, x ∈ K ↔ -x ∈ K))
    (hint : (interior K).Nonempty) :
    ∃ T : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ x, ‖T x‖ ≤ gauge K x) ∧ (∀ x, gauge K x ≤ Real.sqrt n * ‖T x‖) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    refine ⟨LinearEquiv.refl ℝ _, ?_, ?_⟩
    · intro x
      have hx : x = 0 := Subsingleton.elim x 0
      rw [hx, LinearEquiv.refl_apply, norm_zero, gauge_zero]
    · intro x
      have hx : x = 0 := Subsingleton.elim x 0
      simp [hx]
  · obtain ⟨T, hT1, hT2⟩ :=
      Commons.Geometry.Convex.John.john_sandwich_symmetric K hcpt hcvx hsymm hint
    obtain ⟨x₀, hx₀⟩ := hint
    have h0int : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K := by
      have hneg : -x₀ ∈ K := (hsymm x₀).mp (interior_subset hx₀)
      have h := hcvx.combo_interior_self_mem_interior hx₀ hneg
        (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) + 1/2 = 1)
      simpa using h
    have hKnhds : K ∈ nhds (0 : EuclideanSpace ℝ (Fin n)) :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds h0int) interior_subset
    have habs : Absorbent ℝ K := absorbent_nhds_zero hKnhds
    have hbdd : Bornology.IsVonNBounded ℝ K :=
      NormedSpace.isVonNBounded_of_isBounded ℝ hcpt.isBounded
    have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
    set c : ℝ := (Real.sqrt n)⁻¹ with hc
    have hcpos : 0 < c := by rw [hc]; positivity
    have hcne : c ≠ 0 := ne_of_gt hcpos
    let S : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin n)) c hcne).trans T.symm.toLinearEquiv
    have hSapp : ∀ y, S y = c • T.symm y := by
      intro y
      simp only [S, LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply,
        ContinuousLinearEquiv.coe_toLinearEquiv, map_smul]
    have hS_on_K : ∀ z ∈ K, ‖S z‖ ≤ 1 := by
      intro z hz
      obtain ⟨w, hw1, hwz⟩ := hT2 z hz
      have hzw : S z = w := by
        rw [hSapp, hwz, map_smul, ContinuousLinearEquiv.symm_apply_apply, smul_smul,
          show c * Real.sqrt n = 1 by rw [hc, inv_mul_cancel₀ (ne_of_gt hsqrtpos)], one_smul]
      rw [hzw]
      exact hw1
    refine ⟨S, ?_, ?_⟩
    · intro x
      rcases eq_or_ne x 0 with rfl | hx
      · rw [map_zero, norm_zero, gauge_zero]
      · have hgpos : 0 < gauge K x := (gauge_pos habs hbdd).mpr hx
        have hgne : gauge K x ≠ 0 := ne_of_gt hgpos
        have hmem : (gauge K x)⁻¹ • x ∈ K := by
          have hg : gauge K ((gauge K x)⁻¹ • x) ≤ 1 := by
            rw [gauge_smul_of_nonneg (inv_nonneg.mpr hgpos.le), smul_eq_mul,
              inv_mul_cancel₀ hgne]
          have hcl : (gauge K x)⁻¹ • x ∈ closure K :=
            (gauge_le_one_iff_mem_closure hcvx hKnhds).mp hg
          rwa [hcpt.isClosed.closure_eq] at hcl
        have h1 : ‖S ((gauge K x)⁻¹ • x)‖ ≤ 1 := hS_on_K _ hmem
        have h2 : S ((gauge K x)⁻¹ • x) = (gauge K x)⁻¹ • S x := by rw [map_smul]
        rw [h2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hgpos.le)] at h1
        rw [inv_mul_le_iff₀ hgpos, mul_one] at h1
        exact h1
    · intro x
      set z : EuclideanSpace ℝ (Fin n) := T.symm x with hz
      have hxT : x = T z := by rw [hz, ContinuousLinearEquiv.apply_symm_apply]
      have hSz : ‖S x‖ = c * ‖z‖ := by
        rw [hSapp, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
      have hbound : gauge K (T z) ≤ ‖z‖ := by
        rcases eq_or_ne z 0 with hz0 | hz0
        · rw [hz0, map_zero, gauge_zero, norm_zero]
        · have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
          have hnorm1 : ‖(‖z‖⁻¹ : ℝ) • z‖ = 1 := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)),
              inv_mul_cancel₀ hzn]
          have hu : T ((‖z‖⁻¹ : ℝ) • z) ∈ K := hT1 _ (le_of_eq hnorm1)
          have hTz : ‖z‖ • T ((‖z‖⁻¹ : ℝ) • z) = T z := by
            rw [← map_smul]
            congr 1
            rw [smul_smul, mul_inv_cancel₀ hzn, one_smul]
          exact gauge_le_of_mem (norm_nonneg z) ⟨T ((‖z‖⁻¹ : ℝ) • z), hu, hTz⟩
      have hgx : gauge K x = gauge K (T z) := by rw [hxT]
      rw [hgx]
      calc gauge K (T z) ≤ ‖z‖ := hbound
        _ = Real.sqrt n * ‖S x‖ := by
            rw [hSz, hc, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hsqrtpos), one_mul]

end Commons.GeometryOfNumbers.Lattice
