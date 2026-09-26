import Mathlib
import Submission.Work.Smooth.Morse.MorseModel.norm_sub_linear_le
import Submission.Work.Smooth.Morse.MorseModel.mul_norm_le_norm_sub
import Submission.Work.Smooth.Morse.MorseModel.strictMonoOn_norm_sq_smul_sub
import Submission.Work.Smooth.Morse.MorseModel.continuous_of_strictMonoOn_solution

namespace Work.Smooth.Morse.MorseModel

open Set Metric
open scoped RealInnerProductSpace

/-- Two-point mean value estimate: if the derivative of `u` stays within `ε` of the fixed
continuous linear map `A` on the closed unit ball, then for any two points `y, z` of that ball
`u y - u z` is `ε‖y - z‖`-close to `A (y - z)`. -/
theorem norm_deriv_pair_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℂ → F} {A : ℂ →L[ℝ] F} {ε : ℝ}
    (hdiff : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, HasFDerivAt u (fderiv ℝ u z) z)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ u z - A‖ ≤ ε) :
    ∀ y ∈ Metric.closedBall (0 : ℂ) 1, ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ‖u y - u z - A (y - z)‖ ≤ ε * ‖y - z‖ := by
  intro y hy z hz
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (𝕜 := ℝ)
    (f := u) (f' := fun w => fderiv ℝ u w) (φ := A) (C := ε)
    (s := Metric.closedBall (0 : ℂ) 1) (x := z) (y := y)
    (fun w hw => (hdiff w hw).hasFDerivWithinAt)
    (fun w hw => hbound w hw)
    (convex_closedBall 0 1) hz hy

/-- The "direction" of a complex number: `z / ‖z‖` for `z ≠ 0`, with an arbitrary value `1`
at `0`. -/
noncomputable def dirV (z : ℂ) : ℂ := if z = 0 then 1 else z / ((‖z‖ : ℝ) : ℂ)

theorem dirV_zero : dirV 0 = 1 := by rw [dirV, if_pos rfl]

theorem dirV_ne {z : ℂ} (hz : z ≠ 0) : dirV z = z / ((‖z‖ : ℝ) : ℂ) := by
  rw [dirV, if_neg hz]

theorem dirV_smul {a : ℝ} {z : ℂ} (ha : 0 < a) (hz : z ≠ 0) : dirV (a • z) = dirV z := by
  have haz : a • z ≠ 0 := smul_ne_zero ha.ne' hz
  rw [dirV_ne haz, dirV_ne hz]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, Complex.real_smul]
  rw [Complex.ofReal_mul]
  rw [mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr ha.ne')]

theorem dirV_unit {a : ℝ} {θ : ℂ} (ha : 0 < a) (hθ : ‖θ‖ = 1) : dirV (a • θ) = θ := by
  have hne : a • θ ≠ 0 := smul_ne_zero ha.ne' (by intro h; rw [h] at hθ; simp at hθ)
  rw [dirV_ne hne]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, hθ, mul_one, Complex.real_smul]
  rw [mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr ha.ne')]

theorem dirV_repr {z : ℂ} (hz : z ≠ 0) : ‖z‖ • dirV z = z := by
  rw [dirV_ne hz, Complex.real_smul]
  rw [mul_div_assoc', mul_div_cancel_left₀ _
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))]

theorem dirV_norm (z : ℂ) : ‖dirV z‖ = 1 := by
  by_cases hz : z = 0
  · rw [hz, dirV_zero]; simp
  · rw [dirV_ne hz, norm_div]; simp [hz]

/-- The unit sphere of `ℂ`. -/
abbrev Sph : Type := {v : ℂ // ‖v‖ = 1}

/-- The unit direction of a complex number, as a point of the unit sphere. -/
noncomputable def dirOf (z : ℂ) : Sph := ⟨dirV z, dirV_norm z⟩

theorem dirOf_coe (z : ℂ) : ((dirOf z : Sph) : ℂ) = dirV z := rfl

set_option maxHeartbeats 4000000 in
theorem exists_disc_param_of_chart {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u : ℂ → F} {x : F} {A : ℂ →L[ℝ] F} {c ε δ : ℝ}
    (hu : Continuous u) (hc : 0 < c) (hε : 0 ≤ ε) (hεc : 4 * ε ≤ c) (hδ : 0 < δ)
    (hδc : δ < c - ε) (hAc : ∀ v : ℂ, c * ‖v‖ ≤ ‖A v‖) (h0 : u 0 = x)
    (hdiff : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, HasFDerivAt u (fderiv ℝ u z) z)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ u z - A‖ ≤ ε) :
    ∃ e : C(Metric.closedBall (0 : ℂ) 1, F), Function.Injective e ∧
      Set.range e = {y : F | (∃ z ∈ Metric.closedBall (0 : ℂ) 1, u z = y) ∧ ‖y - x‖ ≤ δ} ∧
      (e '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1} =
        {y : F | (∃ z ∈ Metric.closedBall (0 : ℂ) 1, u z = y) ∧ ‖y - x‖ < δ}) ∧
      e 0 = x := by
  classical
  let D : Set ℂ := Metric.closedBall (0 : ℂ) 1
  have hDmem : ∀ z : ℂ, z ∈ D ↔ ‖z‖ ≤ 1 := by
    intro z; simp only [D, Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have hD0 : (0 : ℂ) ∈ D := by rw [hDmem]; simp
  have hceps : 0 < c - ε := by nlinarith [hεc, hc]
  -- ============ Part 1: basic mean value estimates ============
  have hLower : ∀ z ∈ D, (c - ε) * ‖z‖ ≤ ‖u z - x‖ :=
    fun z hz => mul_norm_le_norm_sub hc hε hAc h0 hdiff hbound z hz
  have hPair : ∀ y ∈ D, ∀ z ∈ D, ‖u y - u z - A (y - z)‖ ≤ ε * ‖y - z‖ :=
    fun y hy z hz => norm_deriv_pair_le hdiff hbound y hy z hz
  have hpair_lb : ∀ y ∈ D, ∀ z ∈ D, (c - ε) * ‖y - z‖ ≤ ‖u y - u z‖ := by
    intro y hy z hz
    have hb := hPair y hy z hz
    have h1 : ‖A (y - z)‖ ≤ ‖u y - u z‖ + ε * ‖y - z‖ := by
      have h2 := norm_add_le (A (y - z) - (u y - u z)) (u y - u z)
      have he : A (y - z) - (u y - u z) + (u y - u z) = A (y - z) := by abel
      rw [he] at h2
      have h3 : ‖A (y - z) - (u y - u z)‖ = ‖u y - u z - A (y - z)‖ := norm_sub_rev _ _
      rw [h3] at h2
      linarith [h2, hb]
    have h4 := hAc (y - z)
    nlinarith [h4, h1, norm_nonneg (y - z)]
  have hu_inj : Set.InjOn u D := by
    intro y hy z hz heq
    have hb := hpair_lb y hy z hz
    rw [heq, sub_self, norm_zero] at hb
    have hzy : y - z = 0 := norm_eq_zero.mp (by nlinarith [hb, hceps, norm_nonneg (y - z)])
    exact sub_eq_zero.mp hzy
  -- ============ Part 2: monotonicity along rays ============
  have hmono : ∀ v : ℂ, ‖v‖ = 1 →
      StrictMonoOn (fun t : ℝ => ‖u (t • v) - x‖ ^ 2) (Icc 0 1) :=
    fun v hv => strictMonoOn_norm_sq_smul_sub hc hε hεc hAc h0 hdiff hbound v hv
  -- ============ Part 3: the auxiliary function and tau ============
  let G : Sph → ℝ → ℝ := fun θ t => ‖u (t • (θ : ℂ)) - x‖ ^ 2
  have hGapply : ∀ (θ : Sph) (t : ℝ), G θ t = ‖u (t • (θ : ℂ)) - x‖ ^ 2 := fun _ _ => rfl
  have hGcont : Continuous (Function.uncurry G) := by
    have h1 : Continuous (fun p : Sph × ℝ => p.2 • ((p.1 : Sph) : ℂ)) :=
      continuous_snd.smul (continuous_subtype_val.comp continuous_fst)
    have h2 : Continuous (fun p : Sph × ℝ => u (p.2 • ((p.1 : Sph) : ℂ)) - x) :=
      (hu.comp h1).sub continuous_const
    exact h2.norm.pow 2
  have hGmono : ∀ θ : Sph, StrictMonoOn (G θ) (Icc 0 1) :=
    fun θ => hmono (θ : ℂ) θ.2
  have hexists : ∀ θ : Sph, ∃ t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧ G θ t = δ ^ 2 := by
    intro θ
    have hv : ‖(θ : ℂ)‖ = 1 := θ.2
    have hmemθ : (θ : ℂ) ∈ D := by rw [hDmem, hv]
    have h0g : G θ 0 = 0 := by rw [hGapply]; simp [h0]
    have h1g : δ ^ 2 < G θ 1 := by
      have hlow := hLower (θ : ℂ) hmemθ
      rw [hv, mul_one] at hlow
      have hlt : δ < ‖u (θ : ℂ) - x‖ := lt_of_lt_of_le hδc hlow
      have hsq : δ ^ 2 < ‖u (θ : ℂ) - x‖ ^ 2 := by
        nlinarith [norm_nonneg (u (θ : ℂ) - x)]
      simpa [hGapply] using hsq
    have hcontθ : ContinuousOn (G θ) (Icc (0 : ℝ) 1) :=
      (hGcont.comp (continuous_const.prodMk continuous_id)).continuousOn
    have hmem2 : δ ^ 2 ∈ Icc (G θ 0) (G θ 1) := by
      rw [h0g]; exact ⟨le_of_lt (pow_pos hδ 2), le_of_lt h1g⟩
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcontθ hmem2
    exact ⟨t, ht, hgt⟩
  let τ : Sph → ℝ := fun θ => Classical.choose (hexists θ)
  have hτmem : ∀ θ : Sph, τ θ ∈ Icc (0 : ℝ) 1 := fun θ => (Classical.choose_spec (hexists θ)).1
  have hτeq : ∀ θ : Sph, G θ (τ θ) = δ ^ 2 := fun θ => (Classical.choose_spec (hexists θ)).2
  have hτcont : Continuous τ := continuous_of_strictMonoOn_solution hGcont hGmono hτmem hτeq
  have hτpos : ∀ θ : Sph, 0 < τ θ := by
    intro θ
    have hne : τ θ ≠ 0 := by
      intro hzero
      have hg : G θ (τ θ) = 0 := by rw [hzero, hGapply]; simp [h0]
      linarith [hτeq θ, hg, pow_pos hδ 2]
    exact lt_of_le_of_ne (hτmem θ).1 (Ne.symm hne)
  -- ============ Part 4: sigma ============
  let σ : ℂ → ℂ := fun z => τ (dirOf z) • z
  have hτdir_pos : ∀ z : ℂ, 0 < τ (dirOf z) := fun z => hτpos (dirOf z)
  have hz_repr : ∀ z : ℂ, z = ‖z‖ • ((dirOf z : Sph) : ℂ) := by
    intro z
    by_cases hz : z = 0
    · rw [hz]; simp
    · rw [dirOf_coe]; exact (dirV_repr hz).symm
  have hσ_smul : ∀ z : ℂ, σ z = (τ (dirOf z) * ‖z‖) • ((dirOf z : Sph) : ℂ) := by
    intro z
    have hrepr : z = ‖z‖ • ((dirOf z : Sph) : ℂ) := hz_repr z
    calc σ z = τ (dirOf z) • z := rfl
      _ = τ (dirOf z) • (‖z‖ • ((dirOf z : Sph) : ℂ)) :=
            congrArg (fun w => τ (dirOf z) • w) hrepr
      _ = (τ (dirOf z) * ‖z‖) • ((dirOf z : Sph) : ℂ) := by rw [smul_smul]
  have hσ_G : ∀ z : ℂ, ‖u (σ z) - x‖ ^ 2 = G (dirOf z) (τ (dirOf z) * ‖z‖) := by
    intro z
    rw [hσ_smul z, hGapply]
  -- ============ Part 5: continuity of sigma ============
  have hσcont : Continuous σ := by
    rw [continuous_iff_continuousAt]
    intro z₀
    by_cases hz₀ : z₀ = 0
    · subst hz₀
      rw [ContinuousAt, Metric.tendsto_nhds_nhds]
      intro ε₀ hε₀
      refine ⟨ε₀, hε₀, ?_⟩
      intro z hz
      have hσ0 : σ 0 = 0 := by
        change τ (dirOf 0) • (0 : ℂ) = 0; simp
      have hnorm : ‖σ z‖ ≤ ‖z‖ := by
        rw [hσ_smul z, norm_smul, Real.norm_eq_abs, (dirOf z).2, mul_one,
            abs_of_nonneg (mul_nonneg (le_of_lt (hτdir_pos z)) (norm_nonneg z))]
        nlinarith [hτdir_pos z, norm_nonneg z, (hτmem (dirOf z)).2]
      rw [hσ0, dist_eq_norm, sub_zero]
      have hz' : ‖z‖ < ε₀ := by rw [dist_eq_norm, sub_zero] at hz; exact hz
      linarith
    · have hdirV_at : ContinuousAt dirV z₀ := by
        have hg : ContinuousAt (fun z : ℂ => z / ((‖z‖ : ℝ) : ℂ)) z₀ := by
          apply ContinuousAt.div continuousAt_id _ _
          · exact (Complex.continuous_ofReal.comp continuous_norm).continuousAt
          · exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz₀)
        refine hg.congr ?_
        filter_upwards [(isOpen_ne (x := (0 : ℂ))).mem_nhds hz₀] with z hz
        exact (dirV_ne hz).symm
      have hdirOf_at : ContinuousAt dirOf z₀ := by
        rw [(Topology.IsInducing.subtypeVal (t := {v : ℂ | ‖v‖ = 1})).continuousAt_iff
          (f := dirOf) (x := z₀)]
        exact hdirV_at
      have hTat : ContinuousAt (fun z => τ (dirOf z)) z₀ := hτcont.continuousAt.comp hdirOf_at
      exact hTat.smul continuousAt_id
  -- ============ Part 6: sigma maps into the ball and shrinks distances ============
  have hσ_mem : ∀ z ∈ D, σ z ∈ D := by
    intro z hz
    rw [hDmem] at hz ⊢
    rw [hσ_smul z, norm_smul, Real.norm_eq_abs, (dirOf z).2, mul_one,
        abs_of_nonneg (mul_nonneg (le_of_lt (hτdir_pos z)) (norm_nonneg z))]
    nlinarith [hτdir_pos z, norm_nonneg z, (hτmem (dirOf z)).2, hz]
  have hσ_le : ∀ z ∈ D, ‖u (σ z) - x‖ ≤ δ := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := (hDmem z).mp hz
    have hp := hτdir_pos z
    have hrle : τ (dirOf z) * ‖z‖ ≤ τ (dirOf z) := by nlinarith [hp, norm_nonneg z, hz1]
    have hr0 : 0 ≤ τ (dirOf z) * ‖z‖ := mul_nonneg (le_of_lt hp) (norm_nonneg z)
    have hr1 : τ (dirOf z) * ‖z‖ ≤ 1 := le_trans hrle (hτmem (dirOf z)).2
    have hle : G (dirOf z) (τ (dirOf z) * ‖z‖) ≤ G (dirOf z) (τ (dirOf z)) :=
      ((hGmono (dirOf z)).le_iff_le ⟨hr0, hr1⟩ (hτmem (dirOf z))).mpr hrle
    rw [hτeq (dirOf z)] at hle
    have hsq : ‖u (σ z) - x‖ ^ 2 ≤ δ ^ 2 := by rw [hσ_G z]; exact hle
    nlinarith [norm_nonneg (u (σ z) - x), hδ]
  have hσ_lt : ∀ z ∈ D, ‖z‖ < 1 → ‖u (σ z) - x‖ < δ := by
    intro z hz hzlt
    have hp := hτdir_pos z
    have hrlt : τ (dirOf z) * ‖z‖ < τ (dirOf z) := by nlinarith [hp, hzlt]
    have hr0 : 0 ≤ τ (dirOf z) * ‖z‖ := mul_nonneg (le_of_lt hp) (norm_nonneg z)
    have hr1 : τ (dirOf z) * ‖z‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hrlt (hτmem (dirOf z)).2)
    have hlt' : G (dirOf z) (τ (dirOf z) * ‖z‖) < G (dirOf z) (τ (dirOf z)) :=
      ((hGmono (dirOf z)).lt_iff_lt ⟨hr0, hr1⟩ (hτmem (dirOf z))).mpr hrlt
    rw [hτeq (dirOf z)] at hlt'
    have hsq : ‖u (σ z) - x‖ ^ 2 < δ ^ 2 := by rw [hσ_G z]; exact hlt'
    nlinarith [norm_nonneg (u (σ z) - x), hδ]
  -- ============ Part 7: converse monotonicity ============
  have hz_le_tau : ∀ z ∈ D, ‖u z - x‖ ≤ δ → ‖z‖ ≤ τ (dirOf z) := by
    intro z hzD hzδ
    have hz1 : ‖z‖ ≤ 1 := (hDmem z).mp hzD
    have hGle : G (dirOf z) ‖z‖ ≤ G (dirOf z) (τ (dirOf z)) := by
      have h1 : G (dirOf z) ‖z‖ = ‖u z - x‖ ^ 2 := by rw [hGapply, ← hz_repr z]
      have h2 : G (dirOf z) (τ (dirOf z)) = δ ^ 2 := hτeq (dirOf z)
      rw [h1, h2]; nlinarith [norm_nonneg (u z - x)]
    exact ((hGmono (dirOf z)).le_iff_le ⟨norm_nonneg z, hz1⟩ (hτmem (dirOf z))).mp hGle
  have hz_lt_tau : ∀ z ∈ D, ‖u z - x‖ < δ → ‖z‖ < τ (dirOf z) := by
    intro z hzD hzδ
    have hz1 : ‖z‖ ≤ 1 := (hDmem z).mp hzD
    have hGlt : G (dirOf z) ‖z‖ < G (dirOf z) (τ (dirOf z)) := by
      have h1 : G (dirOf z) ‖z‖ = ‖u z - x‖ ^ 2 := by rw [hGapply, ← hz_repr z]
      have h2 : G (dirOf z) (τ (dirOf z)) = δ ^ 2 := hτeq (dirOf z)
      rw [h1, h2]; nlinarith [norm_nonneg (u z - x)]
    exact ((hGmono (dirOf z)).lt_iff_lt ⟨norm_nonneg z, hz1⟩ (hτmem (dirOf z))).mp hGlt
  -- ============ Part 8: preimages under sigma ============
  have hpreimage : ∀ z ∈ D, ‖z‖ ≤ τ (dirOf z) → ∃ w ∈ D, σ w = z := by
    intro z hzD hle
    by_cases hz0 : z = 0
    · subst hz0
      refine ⟨0, hD0, ?_⟩
      change τ (dirOf 0) • (0 : ℂ) = 0; simp
    · have hp := hτdir_pos z
      have hnormθ : ‖((dirOf z : Sph) : ℂ)‖ = 1 := (dirOf z).2
      refine ⟨(‖z‖ / τ (dirOf z)) • ((dirOf z : Sph) : ℂ), ?_, ?_⟩
      · rw [hDmem, norm_smul, hnormθ, mul_one, Real.norm_eq_abs,
            abs_of_nonneg (div_nonneg (norm_nonneg z) (le_of_lt hp))]
        rw [div_le_one hp]
        exact hle
      · have ha : 0 < ‖z‖ / τ (dirOf z) := div_pos (norm_pos_iff.mpr hz0) hp
        have hdirw : dirOf ((‖z‖ / τ (dirOf z)) • ((dirOf z : Sph) : ℂ)) = dirOf z := by
          apply Subtype.ext
          rw [dirOf_coe, dirOf_coe]
          exact dirV_unit ha hnormθ
        change τ (dirOf ((‖z‖ / τ (dirOf z)) • ((dirOf z : Sph) : ℂ)))
            • ((‖z‖ / τ (dirOf z)) • ((dirOf z : Sph) : ℂ)) = z
        rw [hdirw, smul_smul]
        rw [show τ (dirOf z) * (‖z‖ / τ (dirOf z)) = ‖z‖ from
              mul_div_cancel₀ _ hp.ne']
        exact (hz_repr z).symm
  have hpreimage_lt : ∀ z ∈ D, ‖z‖ < τ (dirOf z) → ∃ w ∈ D, ‖w‖ < 1 ∧ σ w = z := by
    intro z hzD hlt
    by_cases hz0 : z = 0
    · subst hz0
      refine ⟨0, hD0, by simp, ?_⟩
      change τ (dirOf 0) • (0 : ℂ) = 0; simp
    · have hp := hτdir_pos z
      have hnormθ : ‖((dirOf z : Sph) : ℂ)‖ = 1 := (dirOf z).2
      have hwd : ‖z‖ / τ (dirOf z) < 1 := by rw [div_lt_one hp]; exact hlt
      refine ⟨(‖z‖ / τ (dirOf z)) • ((dirOf z : Sph) : ℂ), ?_, ?_, ?_⟩
      · rw [hDmem, norm_smul, hnormθ, mul_one, Real.norm_eq_abs,
            abs_of_nonneg (div_nonneg (norm_nonneg z) (le_of_lt hp))]
        exact le_of_lt hwd
      · rw [norm_smul, hnormθ, mul_one, Real.norm_eq_abs,
            abs_of_nonneg (div_nonneg (norm_nonneg z) (le_of_lt hp))]
        exact hwd
      · have ha : 0 < ‖z‖ / τ (dirOf z) := div_pos (norm_pos_iff.mpr hz0) hp
        have hdirw : dirOf ((‖z‖ / τ (dirOf z)) • ((dirOf z : Sph) : ℂ)) = dirOf z := by
          apply Subtype.ext
          rw [dirOf_coe, dirOf_coe]
          exact dirV_unit ha hnormθ
        change τ (dirOf ((‖z‖ / τ (dirOf z)) • ((dirOf z : Sph) : ℂ)))
            • ((‖z‖ / τ (dirOf z)) • ((dirOf z : Sph) : ℂ)) = z
        rw [hdirw, smul_smul]
        rw [show τ (dirOf z) * (‖z‖ / τ (dirOf z)) = ‖z‖ from
              mul_div_cancel₀ _ hp.ne']
        exact (hz_repr z).symm
  -- ============ Part 9: injectivity of sigma on the ball ============
  have hσ_inj : Set.InjOn σ D := by
    intro a ha b hb hab
    by_cases ha0 : a = 0
    · subst ha0
      have hb0 : b = 0 := by
        by_contra hbne
        have hzero : σ b = 0 := by
          rw [← hab]; change τ (dirOf 0) • (0 : ℂ) = 0; simp
        change τ (dirOf b) • b = 0 at hzero
        exact smul_ne_zero (hτdir_pos b).ne' hbne hzero
      exact hb0.symm
    · have hbne : b ≠ 0 := by
        intro hb0; subst hb0
        have hzero : σ a = 0 := by
          rw [hab]; change τ (dirOf 0) • (0 : ℂ) = 0; simp
        change τ (dirOf a) • a = 0 at hzero
        exact smul_ne_zero (hτdir_pos a).ne' ha0 hzero
      have hdir : dirOf a = dirOf b := by
        have h1 : dirOf (σ a) = dirOf a := by
          apply Subtype.ext
          rw [dirOf_coe, dirOf_coe]
          change dirV (τ (dirOf a) • a) = dirV a
          exact dirV_smul (hτdir_pos a) ha0
        have h2 : dirOf (σ b) = dirOf b := by
          apply Subtype.ext
          rw [dirOf_coe, dirOf_coe]
          change dirV (τ (dirOf b) • b) = dirV b
          exact dirV_smul (hτdir_pos b) hbne
        rw [← h1, ← h2, hab]
      have hτab : τ (dirOf a) = τ (dirOf b) := by rw [hdir]
      have heq' : τ (dirOf a) • a = τ (dirOf a) • b := by
        have h := hab
        change τ (dirOf a) • a = τ (dirOf b) • b at h
        rw [← hτab] at h
        exact h
      exact smul_right_injective ℂ (hτdir_pos a).ne' heq'
  -- ============ Part 10: assemble e and the geometric descriptions ============
  let efun : D → F := fun z => u (σ (z : ℂ))
  have hefun_cont : Continuous efun := hu.comp (hσcont.comp continuous_subtype_val)
  let e : C(D, F) := ⟨efun, hefun_cont⟩
  have he_apply : ∀ z : D, e z = u (σ (z : ℂ)) := fun z => rfl
  have hinj : Function.Injective e := by
    intro a b hab
    have h1 : σ (a : ℂ) ∈ D := hσ_mem _ a.2
    have h2 : σ (b : ℂ) ∈ D := hσ_mem _ b.2
    have heq : σ (a : ℂ) = σ (b : ℂ) := hu_inj h1 h2 hab
    exact Subtype.ext (hσ_inj a.2 b.2 heq)
  have hrange : Set.range e = {y : F | (∃ z ∈ D, u z = y) ∧ ‖y - x‖ ≤ δ} := by
    ext y; constructor
    · rintro ⟨z, rfl⟩
      exact ⟨⟨σ (z : ℂ), hσ_mem _ z.2, rfl⟩, hσ_le _ z.2⟩
    · rintro ⟨⟨z, hzD, hzy⟩, hyx⟩
      obtain ⟨w, hwD, hσw⟩ := hpreimage z hzD (hz_le_tau z hzD (by rw [hzy]; exact hyx))
      refine ⟨⟨w, hwD⟩, ?_⟩
      show u (σ w) = y
      rw [hσw, hzy]
  have hopen : e '' {z : D | ‖(z : ℂ)‖ < 1}
      = {y : F | (∃ z ∈ D, u z = y) ∧ ‖y - x‖ < δ} := by
    ext y; constructor
    · rintro ⟨z, hzlt, rfl⟩
      exact ⟨⟨σ (z : ℂ), hσ_mem _ z.2, rfl⟩, hσ_lt _ z.2 hzlt⟩
    · rintro ⟨⟨z, hzD, hzy⟩, hyx⟩
      obtain ⟨w, hwD, hwlt, hσw⟩ :=
        hpreimage_lt z hzD (hz_lt_tau z hzD (by rw [hzy]; exact hyx))
      refine ⟨⟨w, hwD⟩, hwlt, ?_⟩
      show u (σ w) = y
      rw [hσw, hzy]
  have h0e : e 0 = x := by
    have hco : ((0 : D) : ℂ) = 0 := by simp
    show u (σ ((0 : D) : ℂ)) = x
    rw [hco]
    change u (τ (dirOf 0) • (0 : ℂ)) = x
    rw [smul_zero, h0]
  exact ⟨e, hinj, hrange, hopen, h0e⟩

end Work.Smooth.Morse.MorseModel
