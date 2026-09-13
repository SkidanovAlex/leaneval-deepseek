import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere

namespace Commons.Analysis.Measure.Integral

open MeasureTheory Metric Set Filter Function
open scoped Topology RealInnerProductSpace InnerProductSpace BigOperators ENNReal

/-! ## Geometric estimates on the ball and sphere -/

section Geometric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Points of the unit sphere have norm one. -/
lemma norm_coe_unitSphere (u : sphere (0 : E) 1) : ‖(u : E)‖ = 1 := by
  have h := u.2
  rwa [mem_sphere_zero_iff_norm] at h

/-- `c + R • u` lies on `sphere c R` for `R ≥ 0` and `u` on the unit sphere. -/
lemma add_smul_mem_sphere {c : E} {R : ℝ} (hR : 0 ≤ R) (u : sphere (0 : E) 1) :
    c + R • (u : E) ∈ sphere c R := by
  rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_coe_unitSphere, mul_one,
    Real.norm_of_nonneg hR]

/-- The denominator of the Poisson kernel is bounded below by `R - ‖x - c‖`. -/
lemma le_norm_sub_smul (x c : E) {R : ℝ} (hR : 0 ≤ R) (u : sphere (0 : E) 1) :
    R - ‖x - c‖ ≤ ‖x - c - R • (u : E)‖ := by
  have h1 : ‖R • (u : E)‖ = R := by
    rw [norm_smul, norm_coe_unitSphere, mul_one, Real.norm_of_nonneg hR]
  have hv : R • (u : E) - (x - c) = -(x - c - R • (u : E)) := by abel
  have h2 := norm_sub_norm_le (R • (u : E)) (x - c)
  rw [h1, hv, norm_neg] at h2
  exact h2

/-- The denominator of the Poisson kernel is positive strictly inside the ball. -/
lemma norm_sub_smul_pos (x c : E) {R : ℝ} (hR : 0 < R) (hx : ‖x - c‖ < R)
    (u : sphere (0 : E) 1) : 0 < ‖x - c - R • (u : E)‖ := by
  have := le_norm_sub_smul x c hR.le u
  linarith

/-- The numerator estimate `R ^ 2 - ‖x - c‖ ^ 2 ≤ 2 R ‖x - y‖` inside the ball. -/
lemma sq_sub_sq_le_two_mul (x y c : E) {R : ℝ} (hR : 0 ≤ R) (hx : ‖x - c‖ ≤ R)
    (hy : y ∈ sphere c R) : R ^ 2 - ‖x - c‖ ^ 2 ≤ 2 * R * ‖x - y‖ := by
  have hyc : ‖y - c‖ = R := by
    rw [← dist_eq_norm]; exact mem_sphere.mp hy
  have h1 : R - ‖x - c‖ ≤ ‖x - y‖ := by
    have h := abs_norm_sub_norm_le (y - c) (x - c)
    rw [hyc] at h
    have hv : (y - c) - (x - c) = y - x := by abel
    rw [hv] at h
    have h4 : ‖y - x‖ = ‖x - y‖ := norm_sub_rev y x
    rw [h4] at h
    exact (le_abs_self _).trans h
  have h2 : R + ‖x - c‖ ≤ 2 * R := by linarith
  have hfac : R ^ 2 - ‖x - c‖ ^ 2 = (R - ‖x - c‖) * (R + ‖x - c‖) := by ring
  rw [hfac]
  calc (R - ‖x - c‖) * (R + ‖x - c‖)
      ≤ ‖x - y‖ * (2 * R) := mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
    _ = 2 * R * ‖x - y‖ := by ring

/-- Away from the boundary point the denominator stays bounded below. -/
lemma le_norm_sub_smul_of_far (x y c : E) {R η : ℝ} (u : sphere (0 : E) 1)
    (h1 : η ≤ ‖c + R • (u : E) - y‖) (h2 : ‖x - y‖ ≤ η / 2) :
    η / 2 ≤ ‖x - c - R • (u : E)‖ := by
  have hv : x - c - R • (u : E) = -((c + R • (u : E) - y) - (x - y)) := by abel
  rw [hv, norm_neg]
  have h3 := norm_sub_norm_le (c + R • (u : E) - y) (x - y)
  linarith

end Geometric

/-! ## An abstract approximate-identity integral bound -/

/-- If `k ≥ 0` has total mass `1`, `F` is bounded by `M` everywhere and by `ε / 2` on a
measurable set `A`, then the integral of `k * F` is controlled by `ε / 2` plus the mass of `k`
outside `A`. -/
theorem abs_integral_mul_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {k F : α → ℝ} (hkint : Integrable k μ) (hk0 : ∀ a, 0 ≤ k a) (hk1 : ∫ a, k a ∂μ = 1)
    (hFint : Integrable F μ) {A : Set α} (hA : MeasurableSet A)
    {ε M : ℝ} (hε : 0 ≤ ε) (hFbdd : ∀ a, |F a| ≤ M)
    (hAclose : ∀ a ∈ A, |F a| ≤ ε / 2) :
    |∫ a, k a * F a ∂μ| ≤ ε / 2 + M * ∫ a in Aᶜ, k a ∂μ := by
  have hFabs_meas : AEStronglyMeasurable (fun a => |F a|) μ := by
    simpa only [Real.norm_eq_abs] using hFint.aestronglyMeasurable.norm
  have hkabs_meas : AEStronglyMeasurable (fun a => k a * |F a|) μ :=
    hkint.aestronglyMeasurable.mul hFabs_meas
  have hkabs_int : Integrable (fun a => k a * |F a|) μ := by
    refine Integrable.mono' (hkint.const_mul M) hkabs_meas ?_
    filter_upwards with a
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 a), abs_of_nonneg (abs_nonneg _)]
    calc k a * |F a| ≤ k a * M := mul_le_mul_of_nonneg_left (hFbdd a) (hk0 a)
      _ = M * k a := by ring
  have hnear : ∫ a in A, k a * |F a| ∂μ ≤ ε / 2 := by
    have h1 : ∫ a in A, k a * |F a| ∂μ ≤ ∫ a in A, (ε / 2) * k a ∂μ := by
      refine setIntegral_mono_of_nonneg (fun a _ => mul_nonneg (hk0 a) (abs_nonneg _)) ?_ ?_
      · intro a ha
        calc k a * |F a| ≤ k a * (ε / 2) := mul_le_mul_of_nonneg_left (hAclose a ha) (hk0 a)
          _ = (ε / 2) * k a := by ring
      · exact (hkint.const_mul (ε / 2)).integrableOn
    rw [integral_const_mul] at h1
    have h2 : ∫ a in A, k a ∂μ ≤ 1 := by
      have h3 := setIntegral_le_integral (f := k) hkint (Eventually.of_forall hk0) (s := A)
      rwa [hk1] at h3
    calc ∫ a in A, k a * |F a| ∂μ ≤ (ε / 2) * ∫ a in A, k a ∂μ := h1
      _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = ε / 2 := by ring
  have hfar : ∫ a in Aᶜ, k a * |F a| ∂μ ≤ M * ∫ a in Aᶜ, k a ∂μ := by
    have h1 : ∫ a in Aᶜ, k a * |F a| ∂μ ≤ ∫ a in Aᶜ, M * k a ∂μ := by
      refine setIntegral_mono_of_nonneg (fun a _ => mul_nonneg (hk0 a) (abs_nonneg _)) ?_ ?_
      · intro a _
        calc k a * |F a| ≤ k a * M := mul_le_mul_of_nonneg_left (hFbdd a) (hk0 a)
          _ = M * k a := by ring
      · exact (hkint.const_mul M).integrableOn
    rwa [integral_const_mul] at h1
  have hmain : |∫ a, k a * F a ∂μ| ≤ ∫ a, k a * |F a| ∂μ := by
    have h := norm_integral_le_integral_norm (fun a => k a * F a) (μ := μ)
    rw [Real.norm_eq_abs] at h
    refine h.trans_eq ?_
    apply integral_congr_ae
    filter_upwards with a
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 a)]
  calc |∫ a, k a * F a ∂μ| ≤ ∫ a, k a * |F a| ∂μ := hmain
    _ = ∫ a in A, k a * |F a| ∂μ + ∫ a in Aᶜ, k a * |F a| ∂μ :=
        (integral_add_compl hA hkabs_int).symm
    _ ≤ ε / 2 + M * ∫ a in Aᶜ, k a ∂μ := add_le_add hnear hfar

/-- **Boundary continuity of the Poisson integral.**
Assuming the mass identity (the Poisson integral of the constant function `1` equals `1` on the
ball), the Poisson integral of continuous boundary data `g` on `sphere c R` converges to `g y`
as `x → y` from inside the ball, for every `y ∈ sphere c R`. -/
theorem poissonIntegral_tendsto_boundary {n : ℕ} (hn : 0 < n)
    {c : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContinuousOn g (sphere c R))
    (hmass : ∀ x ∈ ball c R,
      (∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          ((R^n / ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere.real
              Set.univ * R^2))
            * ((R^2 - ‖x - c‖^2) * (‖x - c - R • (u : EuclideanSpace ℝ (Fin n))‖^n)⁻¹))
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) = 1) :
    ∀ y ∈ sphere c R, ∀ ε > 0, ∃ δ > 0, ∀ x : EuclideanSpace ℝ (Fin n),
      ‖x - c‖ < R → ‖x - y‖ < δ →
      |(∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          (R^n / ((MeasureTheory.volume : Measure
              (EuclideanSpace ℝ (Fin n))).toSphere.real Set.univ * R^2))
            * ((R^2 - ‖x - c‖^2) * (‖x - c - R • (u : EuclideanSpace ℝ (Fin n))‖^n)⁻¹)
            * g (c + R • (u : EuclideanSpace ℝ (Fin n)))
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) - g y| < ε := by
  classical
  intro y hy ε hε
  haveI hnt : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    infer_instance
  haveI hNeZero :
      NeZero ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) :=
    ⟨Measure.toSphere_ne_zero (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n)))⟩
  set σ : ℝ :=
    ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).real Set.univ with hσ
  have hσpos : 0 < σ := by rw [hσ]; exact measureReal_univ_pos
  set a : ℝ := R ^ n / (σ * R ^ 2) with ha
  have ha_pos : 0 < a := by
    rw [ha]; exact div_pos (pow_pos hR n) (mul_pos hσpos (pow_pos hR 2))
  -- continuity of `g` at the boundary point `y`
  have hcont : ContinuousWithinAt g (sphere c R) y := hg.continuousWithinAt hy
  rw [continuousWithinAt_iff] at hcont
  obtain ⟨η, hηpos, hη⟩ := hcont (ε / 2) (by linarith)
  -- boundedness of `g - g y` on the sphere
  obtain ⟨C, hC⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn
    (hg.sub continuousOn_const)
  set M : ℝ := max C 0 with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hgbdd : ∀ z ∈ sphere c R, |g z - g y| ≤ M := by
    intro z hz
    have h1 := hC z hz
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (by rw [hMdef]; exact le_max_left _ _)
  -- the constants and the radius
  set Ctot : ℝ := a * (2 * R) * ((η / 2) ^ n)⁻¹ with hCtotdef
  have hCtot0 : 0 ≤ Ctot := by
    rw [hCtotdef]
    exact mul_nonneg (mul_nonneg ha_pos.le (by linarith))
      (inv_nonneg.mpr (pow_nonneg (by linarith) n))
  set K : ℝ := M * Ctot * σ with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]; exact mul_nonneg (mul_nonneg hM0 hCtot0) hσpos.le
  refine ⟨min (η / 2) (ε / (4 * (K + 1))), ?_, ?_⟩
  · exact lt_min (by linarith) (div_pos hε (by linarith))
  · intro x hxnorm hxδ
    have hxη : ‖x - y‖ < η / 2 := lt_of_lt_of_le hxδ (min_le_left _ _)
    have hxε : ‖x - y‖ < ε / (4 * (K + 1)) := lt_of_lt_of_le hxδ (min_le_right _ _)
    have hxmem : x ∈ ball c R := by rw [mem_ball, dist_eq_norm]; exact hxnorm
    have hnum : 0 ≤ R ^ 2 - ‖x - c‖ ^ 2 := by
      have h2 : ‖x - c‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxnorm.le 2
      linarith
    have hRd : 0 < R - ‖x - c‖ := by linarith
    -- the kernel and the boundary-data error
    set k : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ :=
      fun u => a * ((R ^ 2 - ‖x - c‖ ^ 2) *
        (‖x - c - R • (u : EuclideanSpace ℝ (Fin n))‖ ^ n)⁻¹) with hkdef
    set F : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ :=
      fun u => g (c + R • (u : EuclideanSpace ℝ (Fin n))) - g y with hFdef
    set A : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
      {u | ‖c + R • (u : EuclideanSpace ℝ (Fin n)) - y‖ < η} with hAdef
    have hφcont : Continuous (fun u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        c + R • (u : EuclideanSpace ℝ (Fin n))) :=
      continuous_const.add (continuous_subtype_val.const_smul R)
    -- basic properties of the kernel
    have hk0 : ∀ u, 0 ≤ k u := by
      intro u; rw [hkdef]
      exact mul_nonneg ha_pos.le
        (mul_nonneg hnum (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _)))
    have hkcont : Continuous k := by
      rw [hkdef]
      apply Continuous.const_mul
      apply Continuous.mul continuous_const
      apply Continuous.inv₀
      · exact ((continuous_const.sub (continuous_subtype_val.const_smul R)).norm).pow n
      · intro u
        exact pow_ne_zero n (norm_sub_smul_pos x c hR hxnorm u).ne'
    have hkint : Integrable k
        ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
      refine Integrable.of_bound hkcont.aestronglyMeasurable
        (a * (R ^ 2 - ‖x - c‖ ^ 2) * ((R - ‖x - c‖) ^ n)⁻¹) ?_
      filter_upwards with u
      rw [hkdef, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg ha_pos.le
          (mul_nonneg hnum (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _))))]
      have hlb := le_norm_sub_smul x c hR.le u
      have hpow : (R - ‖x - c‖) ^ n ≤ ‖x - c - R • (u : EuclideanSpace ℝ (Fin n))‖ ^ n :=
        pow_le_pow_left₀ hRd.le hlb n
      have hinv : (‖x - c - R • (u : EuclideanSpace ℝ (Fin n))‖ ^ n)⁻¹
          ≤ ((R - ‖x - c‖) ^ n)⁻¹ := by
        rw [inv_le_inv₀ (pow_pos (lt_of_lt_of_le hRd hlb) n) (pow_pos hRd n)]
        exact hpow
      calc a * ((R ^ 2 - ‖x - c‖ ^ 2)
              * (‖x - c - R • (u : EuclideanSpace ℝ (Fin n))‖ ^ n)⁻¹)
          ≤ a * ((R ^ 2 - ‖x - c‖ ^ 2) * ((R - ‖x - c‖) ^ n)⁻¹) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv hnum) ha_pos.le
        _ = a * (R ^ 2 - ‖x - c‖ ^ 2) * ((R - ‖x - c‖) ^ n)⁻¹ := by ring
    have hk1 : ∫ u, k u
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere = 1 := by
      simpa only [hkdef] using hmass x hxmem
    -- the boundary-data error is bounded and small near the boundary point
    have hFbdd : ∀ u, |F u| ≤ M := by
      intro u
      have h1 := hgbdd (c + R • (u : EuclideanSpace ℝ (Fin n)))
        (add_smul_mem_sphere hR.le u)
      simpa only [hFdef] using h1
    have hFint : Integrable F
        ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
      refine Integrable.of_bound ?_ M (Eventually.of_forall hFbdd)
      rw [hFdef]
      exact ((hg.comp_continuous hφcont (fun u => add_smul_mem_sphere hR.le u)).sub
        continuous_const).aestronglyMeasurable
    have hAmeas : MeasurableSet A := by
      have hAeq : A = (fun u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          c + R • (u : EuclideanSpace ℝ (Fin n))) ⁻¹' ball y η := by
        ext u
        simp only [hAdef, Set.mem_setOf_eq, Set.mem_preimage, mem_ball, dist_eq_norm]
      rw [hAeq]
      exact (isOpen_ball.preimage hφcont).measurableSet
    have hAclose : ∀ u ∈ A, |F u| ≤ ε / 2 := by
      intro u hu
      have hmem : c + R • (u : EuclideanSpace ℝ (Fin n)) ∈ sphere c R :=
        add_smul_mem_sphere hR.le u
      have hlt : dist (c + R • (u : EuclideanSpace ℝ (Fin n))) y < η := by
        rw [dist_eq_norm]
        rw [hAdef] at hu
        simpa only [Set.mem_setOf_eq] using hu
      have h1 := hη hmem hlt
      rw [Real.dist_eq] at h1
      simpa only [hFdef] using h1.le
    -- the abstract approximate-identity bound
    have hbound := abs_integral_mul_le
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
      hkint hk0 hk1 hFint hAmeas hε.le hFbdd hAclose
    -- the mass of the kernel off the small set is small
    have hAk : ∀ u ∈ Aᶜ, k u ≤ Ctot * ‖x - y‖ := by
      intro u hu
      rw [hAdef] at hu
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hu
      have hfar := le_norm_sub_smul_of_far x y c u hu (le_of_lt hxη)
      have hη2pos : 0 < η / 2 := by linarith
      have hpow : (η / 2) ^ n ≤ ‖x - c - R • (u : EuclideanSpace ℝ (Fin n))‖ ^ n :=
        pow_le_pow_left₀ hη2pos.le hfar n
      have hinv : (‖x - c - R • (u : EuclideanSpace ℝ (Fin n))‖ ^ n)⁻¹ ≤ ((η / 2) ^ n)⁻¹ := by
        rw [inv_le_inv₀ (pow_pos (lt_of_lt_of_le hη2pos hfar) n) (pow_pos hη2pos n)]
        exact hpow
      have hnum2 := sq_sub_sq_le_two_mul x y c hR.le hxnorm.le hy
      rw [hkdef, hCtotdef]
      calc a * ((R ^ 2 - ‖x - c‖ ^ 2)
              * (‖x - c - R • (u : EuclideanSpace ℝ (Fin n))‖ ^ n)⁻¹)
          ≤ a * ((2 * R * ‖x - y‖) * ((η / 2) ^ n)⁻¹) := by
            apply mul_le_mul_of_nonneg_left _ ha_pos.le
            exact mul_le_mul hnum2 hinv (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) n))
              (by positivity)
        _ = (a * (2 * R) * ((η / 2) ^ n)⁻¹) * ‖x - y‖ := by ring
    have hfar_int : ∫ u in Aᶜ, k u
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
        ≤ Ctot * ‖x - y‖ * σ := by
      set cst : ℝ := Ctot * ‖x - y‖ with hcstdef
      have hcst0 : 0 ≤ cst := by
        rw [hcstdef]; exact mul_nonneg hCtot0 (norm_nonneg _)
      have h1 : ∫ u in Aᶜ, k u
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
          ≤ ∫ u in Aᶜ, cst
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
        refine setIntegral_mono_of_nonneg (fun u _ => hk0 u) (fun u hu => ?_)
          ((integrable_const cst).integrableOn)
        have := hAk u hu
        rwa [hcstdef]
      rw [setIntegral_const, smul_eq_mul] at h1
      have hle : (((MeasureTheory.volume :
          Measure (EuclideanSpace ℝ (Fin n))).toSphere).real Aᶜ) ≤ σ := by
        rw [hσ]
        exact measureReal_mono (subset_univ _) (measure_lt_top _ _).ne
      calc ∫ u in Aᶜ, k u
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
          ≤ (((MeasureTheory.volume :
              Measure (EuclideanSpace ℝ (Fin n))).toSphere).real Aᶜ) * cst := h1
        _ ≤ σ * cst := mul_le_mul_of_nonneg_right hle hcst0
        _ = Ctot * ‖x - y‖ * σ := by rw [hcstdef]; ring
    have hfar_lt : M * ∫ u in Aᶜ, k u
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere < ε / 2 := by
      have h2 : M * ∫ u in Aᶜ, k u
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
          ≤ K * ‖x - y‖ := by
        calc M * ∫ u in Aᶜ, k u
              ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
            ≤ M * (Ctot * ‖x - y‖ * σ) := mul_le_mul_of_nonneg_left hfar_int hM0
          _ = K * ‖x - y‖ := by rw [hKdef]; ring
      have h5 : K * (ε / (4 * (K + 1))) ≤ ε / 4 := by
        have h1 : K * (ε / (4 * (K + 1))) = K * ε / (4 * (K + 1)) := by rw [mul_div_assoc]
        rw [h1, div_le_iff₀ (by linarith : (0:ℝ) < 4 * (K + 1))]
        nlinarith [hε.le]
      have h3 : K * ‖x - y‖ ≤ ε / 4 :=
        (mul_le_mul_of_nonneg_left hxε.le hK0).trans h5
      linarith
    -- convert the goal to the approximation error
    have hkey : (∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            k u * g (c + R • (u : EuclideanSpace ℝ (Fin n)))
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) - g y
        = ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, k u * F u
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
      have hkg : Integrable (fun u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          k u * g (c + R • (u : EuclideanSpace ℝ (Fin n))))
          ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
        refine Integrable.mono' (hkint.const_mul (M + |g y|)) ?_ ?_
        · exact (hkcont.mul (hg.comp_continuous hφcont
            (fun u => add_smul_mem_sphere hR.le u))).aestronglyMeasurable
        · filter_upwards with u
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 u)]
          calc k u * |g (c + R • (u : EuclideanSpace ℝ (Fin n)))|
              ≤ k u * (M + |g y|) := by
                apply mul_le_mul_of_nonneg_left _ (hk0 u)
                calc |g (c + R • (u : EuclideanSpace ℝ (Fin n)))|
                    = |(g (c + R • (u : EuclideanSpace ℝ (Fin n))) - g y) + g y| := by
                      rw [sub_add_cancel]
                  _ ≤ |g (c + R • (u : EuclideanSpace ℝ (Fin n))) - g y| + |g y| :=
                      abs_add_le _ _
                  _ ≤ M + |g y| := by linarith [hFbdd u]
            _ = (M + |g y|) * k u := by ring
      have hkgy : Integrable (fun u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => k u * g y)
          ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) :=
        hkint.mul_const _
      calc (∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              k u * g (c + R • (u : EuclideanSpace ℝ (Fin n)))
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) - g y
          = (∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              k u * g (c + R • (u : EuclideanSpace ℝ (Fin n)))
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
            - (∫ u, k u
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) * g y := by
              rw [hk1, one_mul]
        _ = (∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              k u * g (c + R • (u : EuclideanSpace ℝ (Fin n)))
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
            - ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, k u * g y
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
              rw [integral_mul_const]
        _ = ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              (k u * g (c + R • (u : EuclideanSpace ℝ (Fin n))) - k u * g y)
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere :=
              (integral_sub hkg hkgy).symm
        _ = ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, k u * F u
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
              apply integral_congr_ae
              filter_upwards with u
              rw [hFdef]; ring
    have hgoal_int : (∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          (a * ((R ^ 2 - ‖x - c‖ ^ 2)
              * (‖x - c - R • (u : EuclideanSpace ℝ (Fin n))‖ ^ n)⁻¹))
            * g (c + R • (u : EuclideanSpace ℝ (Fin n)))
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
        = ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            k u * g (c + R • (u : EuclideanSpace ℝ (Fin n)))
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
      apply integral_congr_ae
      filter_upwards with u
      simp only [hkdef]
    have hgoal := congrArg (fun z : ℝ => z - g y) hgoal_int
    rw [hgoal, hkey]
    linarith [hbound, hfar_lt]


end Commons.Analysis.Measure.Integral