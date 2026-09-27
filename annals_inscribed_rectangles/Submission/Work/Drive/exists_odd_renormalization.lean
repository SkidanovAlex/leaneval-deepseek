import Mathlib

namespace Work.Drive

open scoped RealInnerProductSpace

/-- **Renormalising a lift to be odd on the boundary circle.**

If a smooth nonvanishing lift `V` of a class map that is *seam invariant* (so that `V (-z)` is parallel
to `V z` on the unit circle, the hypothesis `hpar`) has a **negative** parallelism factor at one point
of the circle, then `V` can be rescaled by a positive smooth weight `μ` to a lift `W = μ • V` that is
exactly **odd** on the circle: `W (-z) = - W z`.

This is the bridge from the checkable input "the factor is negative at one point" to the oddness
hypothesis used by `Work.Drive.exists_diskClassHomotopy`; the missing ingredient of the proof (the sign
is in fact negative *everywhere* on the circle) is the connectedness of the circle, and the weight is
built explicitly as `μ z = exp (ψ z * log (-c z))` where `c z = ⟪V (-z), V z⟫ / ‖V z‖²` and
`ψ z = (1 - z.re) / 2` satisfies `ψ (-z) + ψ z = 1`, so that
`log μ (-z) - log μ z = log (-1 / c z)` on the circle. -/
theorem exists_odd_renormalization (V : ℂ → EuclideanSpace ℝ (Fin 4))
    (hVsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hVne : ∀ z, V z ≠ 0)
    (hpar : ∀ z : ℂ, ‖z‖ = 1 → ∃ c : ℝ, V (-z) = c • V z)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1)
    (hneg : ∃ c : ℝ, V (-z₀) = c • V z₀ ∧ c < 0) :
    ∃ (W : ℂ → EuclideanSpace ℝ (Fin 4)) (μ : ℂ → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W ∧ (∀ z, W z ≠ 0) ∧
      (∀ z, 0 < μ z) ∧ (∀ z, W z = μ z • V z) ∧
      (∀ z : ℂ, ‖z‖ = 1 → W (-z) = - W z) := by
  -- **Step 1.**  The parallelism factor is negative at *every* point of the circle.
  --
  -- The scalar product `F w = ⟪V (-w), V w⟫` is continuous and, on the circle where `V (-w)` is
  -- parallel to `V w`, it is `c · ‖V w‖²`, so it has the sign of the parallelism factor `c` and
  -- never vanishes there.  The circle is preconnected, so its image under `F` is an interval; since
  -- it contains the strictly negative value `F z₀` and does not contain `0`, it is contained in
  -- `(-∞, 0)`.
  have key : ∀ z : ℂ, ‖z‖ = 1 → ∀ c : ℝ, V (-z) = c • V z → c < 0 := by
    have hFneg : ∀ z : ℂ, ‖z‖ = 1 → inner ℝ (V (-z)) (V z) < 0 := by
      intro z hz
      set F : ℂ → ℝ := fun w => inner ℝ (V (-w)) (V w) with hFdef
      have hFcont : Continuous F := by
        rw [hFdef]
        exact (hVsmooth.continuous.comp continuous_neg).inner hVsmooth.continuous
      have hsphere : IsPreconnected (Metric.sphere (0 : ℂ) 1) :=
        isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 1
      have himg : IsPreconnected (F '' Metric.sphere (0 : ℂ) 1) :=
        hsphere.image F hFcont.continuousOn
      have hord : (F '' Metric.sphere (0 : ℂ) 1).OrdConnected := himg.ordConnected
      have hmemz0 : F z₀ ∈ F '' Metric.sphere (0 : ℂ) 1 :=
        ⟨z₀, by rw [mem_sphere_iff_norm]; simpa using hz₀, rfl⟩
      have hmemz : F z ∈ F '' Metric.sphere (0 : ℂ) 1 :=
        ⟨z, by rw [mem_sphere_iff_norm]; simpa using hz, rfl⟩
      have hz0neg : F z₀ < 0 := by
        obtain ⟨c, hc, hcneg⟩ := hneg
        have hEq : F z₀ = c * ‖V z₀‖ ^ 2 := by
          simp only [hFdef]
          rw [hc, real_inner_smul_left, real_inner_self_eq_norm_sq]
        rw [hEq]
        exact mul_neg_of_neg_of_pos hcneg (pow_pos (norm_pos_iff.mpr (hVne z₀)) 2)
      have hne : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → F w ≠ 0 := by
        intro w hw hw0
        have hw1 : ‖w‖ = 1 := by rw [mem_sphere_iff_norm] at hw; simpa using hw
        obtain ⟨c, hc⟩ := hpar w hw1
        have hEq : F w = c * ‖V w‖ ^ 2 := by
          simp only [hFdef]
          rw [hc, real_inner_smul_left, real_inner_self_eq_norm_sq]
        rw [hEq] at hw0
        have hwn : ‖V w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (hVne w))
        have hc0 : c = 0 := by
          rcases mul_eq_zero.mp hw0 with h | h
          · exact h
          · exact absurd h hwn
        rw [hc0, zero_smul] at hc
        exact hVne (-w) hc
      by_contra hcon
      rw [not_lt] at hcon
      have hmem0 : (0 : ℝ) ∈ Set.Icc (F z₀) (F z) := Set.mem_Icc.mpr ⟨le_of_lt hz0neg, hcon⟩
      obtain ⟨w, hw, hw0⟩ := hord.out hmemz0 hmemz hmem0
      exact hne w hw hw0
    intro z hz c hc
    have h1 := hFneg z hz
    have hEq : inner ℝ (V (-z)) (V z) = c * ‖V z‖ ^ 2 := by
      rw [hc, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [hEq] at h1
    rcases mul_neg_iff.mp h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · exact absurd h3 (not_lt.mpr (by positivity))
    · exact h2
  -- **Step 2.**  The normalisation `W z = (‖V z‖)⁻¹ • V z`, `μ z = (‖V z‖)⁻¹` is smooth, positive
  -- and odd on the circle:  on the circle `V (-z) = c • V z` with `c < 0`, hence
  -- `‖V (-z)‖ = |c| ‖V z‖ = -c ‖V z‖` and `W (-z) = ((−c)‖V z‖)⁻¹ · c • V z = - (‖V z‖)⁻¹ • V z`.
  refine ⟨fun z => (‖V z‖)⁻¹ • V z, fun z => (‖V z‖)⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((ContDiff.norm ℝ hVsmooth hVne).inv
      (fun z => norm_ne_zero_iff.mpr (hVne z))).smul hVsmooth
  · intro z
    exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr (hVne z))) (hVne z)
  · intro z
    exact inv_pos.mpr (norm_pos_iff.mpr (hVne z))
  · intro z
    rfl
  · intro z hz
    obtain ⟨c, hc⟩ := hpar z hz
    have hcneg : c < 0 := key z hz c hc
    change (‖V (-z)‖)⁻¹ • V (-z) = - ((‖V z‖)⁻¹ • V z)
    rw [hc, norm_smul, Real.norm_eq_abs, abs_of_neg hcneg, smul_smul, ← neg_smul]
    congr 1
    have hc0 : c ≠ 0 := ne_of_lt hcneg
    field_simp

end Work.Drive
