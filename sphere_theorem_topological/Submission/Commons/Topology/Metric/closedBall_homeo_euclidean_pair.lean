import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Topology.Metric

theorem closedBall_homeo_euclidean_pair {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (hn : Module.finrank ℝ V = n) {r : ℝ} (hr : 0 < r) :
    ∃ e : Metric.closedBall (0 : V) r ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      ∀ v : Metric.closedBall (0 : V) r, ‖(v : V)‖ = r ↔
        ‖((e v : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
          EuclideanSpace ℝ (Fin n))‖ = 1 := by
  -- A linear isometric equivalence `V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)`, from an orthonormal basis
  -- of `V` reindexed along `hn`.
  let idx : Fin (Module.finrank ℝ V) ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hn)
  let b : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex idx
  let φ : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) := b.repr
  -- Radial scaling `r⁻¹` sends the ball of radius `r` into the unit ball.
  have hmemF : ∀ v : V, ‖v‖ ≤ r → ‖r⁻¹ • φ v‖ ≤ 1 := by
    intro v hv
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), φ.norm_map]
    have h1 : r⁻¹ * ‖v‖ ≤ r⁻¹ * r :=
      mul_le_mul_of_nonneg_left hv (le_of_lt (inv_pos.mpr hr))
    rwa [inv_mul_cancel₀ (ne_of_gt hr)] at h1
  -- Radial scaling by `r` sends the unit ball into the ball of radius `r`.
  have hmemG : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ 1 → ‖φ.symm (r • w)‖ ≤ r := by
    intro w hw
    rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    calc r * ‖w‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hw (le_of_lt hr)
      _ = r := mul_one r
  let F : Metric.closedBall (0 : V) r → Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    fun v => ⟨r⁻¹ • φ (v : V), by
      have hv : ‖(v : V)‖ ≤ r := mem_closedBall_zero_iff.mp v.2
      exact mem_closedBall_zero_iff.mpr (hmemF (v : V) hv)⟩
  let G : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 → Metric.closedBall (0 : V) r :=
    fun w => ⟨φ.symm (r • (w : EuclideanSpace ℝ (Fin n))), by
      have hw : ‖(w : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := mem_closedBall_zero_iff.mp w.2
      exact mem_closedBall_zero_iff.mpr (hmemG (w : EuclideanSpace ℝ (Fin n)) hw)⟩
  have hFc : Continuous F := by
    apply Continuous.subtype_mk
    exact ((φ.continuous.comp continuous_subtype_val).const_smul r⁻¹)
  have hGc : Continuous G := by
    apply Continuous.subtype_mk
    exact (φ.symm.continuous.comp ((continuous_subtype_val).const_smul r))
  have hFG : Function.LeftInverse G F := by
    intro v
    apply Subtype.ext
    simp only [F, G, smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul,
      LinearIsometryEquiv.symm_apply_apply]
  have hGF : Function.RightInverse G F := by
    intro w
    apply Subtype.ext
    simp only [F, G, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul,
      LinearIsometryEquiv.apply_symm_apply]
  let e : Metric.closedBall (0 : V) r ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    Homeomorph.mk ⟨F, G, hFG, hGF⟩ hFc hGc
  refine ⟨e, ?_⟩
  intro v
  change ‖(v : V)‖ = r ↔ ‖(F v : EuclideanSpace ℝ (Fin n))‖ = 1
  constructor
  · -- sphere of radius `r` maps into the unit sphere
    intro hv
    simp only [F]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), φ.norm_map, hv,
      inv_mul_cancel₀ (ne_of_gt hr)]
  · -- unit sphere maps back into the sphere of radius `r`
    intro hv
    simp only [F] at hv
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), φ.norm_map] at hv
    have hmul : r * (r⁻¹ * ‖(v : V)‖) = r * 1 := by rw [hv]
    rwa [mul_one, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hr), one_mul] at hmul

end Commons.Topology.Metric