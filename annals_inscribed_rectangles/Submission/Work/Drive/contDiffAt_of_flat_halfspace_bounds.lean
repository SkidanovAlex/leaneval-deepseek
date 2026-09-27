import Mathlib

universe u v

namespace Work.Drive

open Set Filter Metric
open scoped ContDiff Topology

/-- Points of the segment `[y, y+h]` are at distance at most `‖h‖` from `y`. -/
private lemma smul_segment_sub {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {y h z : X} (hz : z ∈ segment ℝ y (y + h)) : ‖z - y‖ ≤ ‖h‖ := by
  rw [segment_eq_image₂] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  obtain ⟨hp1, hp2, hpsum⟩ := hp
  have hkey : p.1 • y + p.2 • (y + h) - y = p.2 • h := by
    have h1 : p.1 = 1 - p.2 := by linarith
    rw [h1, sub_smul, one_smul, smul_add]
    abel
  rw [hkey, norm_smul, Real.norm_eq_abs, abs_of_nonneg hp2]
  exact mul_le_of_le_one_left (norm_nonneg h) (by linarith)

/-- A function vanishing on the lower half-plane near `(x₀,0)` is eventually `0` at any point of
the open lower half-plane. -/
private lemma eventuallyEq_zero_of_lt {X E : Type*} [NormedAddCommGroup X] [NormedAddCommGroup E]
    {f : X × ℝ → E} {x₀ : X} {ρ : ℝ}
    (hz : ∀ z : X × ℝ, ‖z - (x₀, 0)‖ < ρ → z.2 ≤ 0 → f z = 0)
    {z : X × ℝ} (hzρ : ‖z - (x₀, 0)‖ < ρ) (hz2 : z.2 < 0) :
    f =ᶠ[𝓝 z] (fun _ => (0 : E)) := by
  have h1 : 0 < ρ - ‖z - (x₀, 0)‖ := sub_pos.mpr hzρ
  refine Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨Metric.ball z (min ((ρ - ‖z - (x₀, 0)‖) / 2) (-z.2 / 2)),
      Metric.ball_mem_nhds _ (lt_min (by linarith) (by linarith)), ?_⟩
  intro w hw
  have hdist : ‖w - z‖ < min ((ρ - ‖z - (x₀, 0)‖) / 2) (-z.2 / 2) := by
    simpa [dist_eq_norm] using Metric.mem_ball.mp hw
  have h1' : ‖w - z‖ < (ρ - ‖z - (x₀, 0)‖) / 2 := lt_of_lt_of_le hdist (min_le_left _ _)
  have h2' : ‖w - z‖ < -z.2 / 2 := lt_of_lt_of_le hdist (min_le_right _ _)
  have hwρ : ‖w - (x₀, 0)‖ < ρ := by
    calc ‖w - (x₀, 0)‖ ≤ ‖w - z‖ + ‖z - (x₀, 0)‖ := by
          rw [show w - (x₀, 0) = (w - z) + (z - (x₀, 0)) by abel]
          exact norm_add_le _ _
      _ < (ρ - ‖z - (x₀, 0)‖) / 2 + ‖z - (x₀, 0)‖ := by linarith
      _ < ρ := by linarith
  have hw2 : w.2 ≤ 0 := by
    have h3 : |w.2 - z.2| ≤ ‖w - z‖ := by
      have h := norm_snd_le (w - z)
      rwa [Real.norm_eq_abs] at h
    have h4 : w.2 - z.2 ≤ |w.2 - z.2| := le_abs_self _
    have : w.2 - z.2 < -z.2 / 2 := lt_of_le_of_lt (le_trans h4 h3) h2'
    linarith
  exact hz w hwρ hw2

/-- Differentiability at a point of the hyperplane, from the flat bounds. -/
private lemma hasFDerivAt_bdry {X : Type u} {E' : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] {g : X × ℝ → E'} {x₀ : X} {M : ℕ} {ρ : ℝ}
    (hM : 1 ≤ M) (hρ : 0 < ρ)
    (hz : ∀ z : X × ℝ, ‖z - (x₀, 0)‖ < ρ → z.2 ≤ 0 → g z = 0)
    (hC : ContDiffOn ℝ ((M : ℕ) : WithTop ℕ∞) g
      (Metric.ball (x₀, 0) ρ ∩ {z : X × ℝ | 0 < z.2}))
    (hb0 : ∃ C : ℝ, ∀ z : X × ℝ, ‖z - (x₀, 0)‖ < ρ → 0 < z.2 →
      ‖g z‖ ≤ C * (z.2) ^ (M + 1))
    (hb1 : ∃ C : ℝ, ∀ z : X × ℝ, ‖z - (x₀, 0)‖ < ρ → 0 < z.2 →
      ‖fderiv ℝ g z‖ ≤ C * (z.2) ^ M)
    {z : X × ℝ} (hzρ : ‖z - (x₀, 0)‖ < ρ) (hz2 : z.2 = 0) :
    HasFDerivAt g (0 : (X × ℝ) →L[ℝ] E') z := by
  classical
  obtain ⟨C0, hC0⟩ := hb0
  obtain ⟨C1, hC1⟩ := hb1
  have hz0 : g z = 0 := hz z hzρ hz2.le
  have hεpos : 0 < min (1:ℝ) ((ρ - ‖z - (x₀, 0)‖) / 3) :=
    lt_min one_pos (by linarith)
  have hερ : min (1:ℝ) ((ρ - ‖z - (x₀, 0)‖) / 3) ≤ (ρ - ‖z - (x₀, 0)‖) / 3 :=
    min_le_right _ _
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hbig : (fun h : X × ℝ => g (z + h) - g z - (0 : (X × ℝ) →L[ℝ] E') h) =O[𝓝 0]
      (fun h : X × ℝ => ‖h‖ ^ (M + 1)) := by
    refine Asymptotics.IsBigO.of_bound (max C0 0 + max C1 0) ?_
    have hsmall : ∀ᶠ h : X × ℝ in 𝓝 (0 : X × ℝ),
        ‖h‖ < min (1:ℝ) ((ρ - ‖z - (x₀, 0)‖) / 3) :=
      Metric.eventually_nhds_iff.mpr ⟨_, hεpos, fun h hh => by simpa using hh⟩
    filter_upwards [hsmall] with h hh
    have hhδ : ‖h‖ < (ρ - ‖z - (x₀, 0)‖) / 3 := lt_of_lt_of_le hh hερ
    have hh1 : ‖h‖ < 1 := lt_of_lt_of_le hh (min_le_left _ _)
    have hzρ' : ‖z + h - (x₀, 0)‖ < ρ := by
      calc ‖z + h - (x₀, 0)‖ = ‖(z - (x₀, 0)) + h‖ := by congr 1; abel
        _ ≤ ‖z - (x₀, 0)‖ + ‖h‖ := norm_add_le _ _
        _ < ‖z - (x₀, 0)‖ + (ρ - ‖z - (x₀, 0)‖) / 3 := by linarith
        _ < ρ := by linarith
    simp only [ContinuousLinearMap.zero_apply, sub_zero,
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ‖h‖ ^ (M + 1))]
    rcases lt_trichotomy h.2 0 with hu | hu | hu
    · have hcase : (z + h).2 ≤ 0 := by
        have h2 : (z + h).2 = h.2 := by
          show z.2 + h.2 = h.2; rw [hz2, zero_add]
        rw [h2]; exact hu.le
      rw [hz (z + h) hzρ' hcase, hz0, sub_zero, norm_zero]
      positivity
    · have hcase : (z + h).2 ≤ 0 := by
        have h2 : (z + h).2 = h.2 := by
          show z.2 + h.2 = h.2; rw [hz2, zero_add]
        rw [h2, hu]
      rw [hz (z + h) hzρ' hcase, hz0, sub_zero, norm_zero]
      positivity
    · have hu0 : 0 < h.2 := hu
      have hzplus : z + h = (z.1 + h.1, h.2) := by ext <;> simp [hz2, hu]
      have hhρ : ‖h‖ < ρ := by linarith [norm_nonneg (z - (x₀,0)), hρ]
      have hyu : ‖(z.1, h.2) - (x₀, 0)‖ < ρ := by
        rw [Prod.norm_def]
        simp only [Prod.fst_sub, Prod.snd_sub, sub_zero]
        exact max_lt (lt_of_le_of_lt (norm_fst_le (z - (x₀,0))) hzρ)
          (lt_of_le_of_lt (norm_snd_le h) hhρ)
      have hval : ‖g (z.1, h.2)‖ ≤ C0 * (h.2) ^ (M + 1) := by
        have h2' := hC0 _ hyu hu0
        simpa using h2'
      have hmotion : ‖g (z + h) - g (z.1, h.2)‖
          ≤ max C1 0 * (h.2) ^ M * ‖h.1‖ := by
        have hseg : ∀ y' ∈ segment ℝ z.1 (z.1 + h.1), ‖(y', h.2) - (x₀, 0)‖ < ρ := by
          intro y' hy'
          have hy'dist : ‖y' - z.1‖ ≤ ‖h.1‖ := smul_segment_sub hy'
          have h1 : ‖(y', h.2) - (z.1, h.2)‖ = ‖y' - z.1‖ := by
            rw [show (y', h.2) - (z.1, h.2) = (y' - z.1, (0:ℝ)) by ext <;> simp]
            rw [Prod.norm_def]; simp
          have h2 : ‖(z.1, h.2) - (x₀, 0)‖ ≤ ‖h‖ + ‖z.1 - x₀‖ := by
            rw [show (z.1, h.2) - (x₀, 0) = (z.1 - x₀, h.2) by ext <;> simp]
            rw [Prod.norm_def]
            simp only [Prod.snd_sub, sub_zero]
            exact max_le (le_add_of_nonneg_left (norm_nonneg h))
              (le_trans (norm_snd_le h) (le_add_of_nonneg_right (norm_nonneg (z.1 - x₀))))
          have h3 : ‖z.1 - x₀‖ ≤ ‖z - (x₀, 0)‖ := norm_fst_le (z - (x₀,0))
          calc ‖(y', h.2) - (x₀, 0)‖
              ≤ ‖(y', h.2) - (z.1, h.2)‖ + ‖(z.1, h.2) - (x₀, 0)‖ := by
                rw [show (y', h.2) - (x₀, 0)
                    = ((y', h.2) - (z.1, h.2)) + ((z.1, h.2) - (x₀, 0)) by abel]
                exact norm_add_le _ _
            _ ≤ ‖h‖ + (‖h‖ + ‖z.1 - x₀‖) := by
                have h1' := le_trans hy'dist (norm_fst_le h)
                rw [h1]; linarith [h2]
            _ < ρ := by linarith
        have hmain := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
          (s := segment ℝ z.1 (z.1 + h.1)) (f := fun y'' : X => g (y'', h.2))
          (f' := fun y' => (fderiv ℝ g (y', h.2)).comp (ContinuousLinearMap.inl ℝ X ℝ))
          (C := max C1 0 * (h.2) ^ M)
          (fun y' hy' => by
            have hmem : ‖(y', h.2) - (x₀, 0)‖ < ρ := hseg y' hy'
            have hmemS : (y', h.2) ∈ Metric.ball (x₀, 0) ρ ∩ {z : X × ℝ | 0 < z.2} :=
              ⟨Metric.mem_ball.mpr (by simpa [dist_eq_norm] using hmem), hu0⟩
            have hdiff : DifferentiableAt ℝ g (y', h.2) :=
              (hC.contDiffAt (x := (y', h.2))
                ((isOpen_ball.inter (isOpen_Ioi.preimage continuous_snd)).mem_nhds
                  hmemS)).differentiableAt (by exact_mod_cast (show M ≠ 0 by omega))
            have hg_at : HasFDerivAt (fun y'' : X => g (y'', h.2))
                ((fderiv ℝ g (y', h.2)).comp (ContinuousLinearMap.inl ℝ X ℝ)) y' :=
              (hdiff.hasFDerivAt).comp y' (hasFDerivAt_prodMk_left y' h.2)
            exact hg_at.hasFDerivWithinAt)
          (fun y' hy' => by
            have hmem : ‖(y', h.2) - (x₀, 0)‖ < ρ := hseg y' hy'
            have hle : ‖fderiv ℝ g (y', h.2)‖ ≤ C1 * (h.2) ^ M := by
              simpa using hC1 (y', h.2) hmem hu0
            calc ‖(fderiv ℝ g (y', h.2)).comp (ContinuousLinearMap.inl ℝ X ℝ)‖
                ≤ ‖fderiv ℝ g (y', h.2)‖ * ‖ContinuousLinearMap.inl ℝ X ℝ‖ :=
                  ContinuousLinearMap.opNorm_comp_le _ _
              _ ≤ ‖fderiv ℝ g (y', h.2)‖ * 1 := by
                  gcongr; exact ContinuousLinearMap.norm_inl_le_one ℝ X ℝ
              _ = ‖fderiv ℝ g (y', h.2)‖ := mul_one _
              _ ≤ C1 * (h.2) ^ M := hle
              _ ≤ max C1 0 * (h.2) ^ M :=
                  mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
          (convex_segment _ _) (left_mem_segment ℝ z.1 (z.1 + h.1))
          (right_mem_segment ℝ z.1 (z.1 + h.1))
        rw [← hzplus] at hmain
        simpa using hmain
      have hC0nn : C0 ≤ max C0 0 := le_max_left _ _
      have hh2 : h.2 ≤ ‖h‖ := by
        have hh2' := norm_snd_le h
        rw [Real.norm_eq_abs] at hh2'
        exact le_trans (le_abs_self h.2) hh2'
      have hh1' : ‖h.1‖ ≤ ‖h‖ := norm_fst_le h
      have hstep : g (z + h) = (g (z + h) - g (z.1, h.2)) + g (z.1, h.2) := by abel
      rw [hz0, sub_zero, hstep]
      calc ‖(g (z + h) - g (z.1, h.2)) + g (z.1, h.2)‖
          ≤ ‖g (z + h) - g (z.1, h.2)‖ + ‖g (z.1, h.2)‖ := norm_add_le _ _
        _ ≤ max C1 0 * (h.2) ^ M * ‖h.1‖ + C0 * (h.2) ^ (M + 1) :=
            add_le_add hmotion hval
        _ ≤ max C1 0 * ‖h‖ ^ (M + 1) + max C0 0 * ‖h‖ ^ (M + 1) := by
            refine add_le_add ?_ (mul_le_mul hC0nn
              (pow_le_pow_left₀ (le_of_lt hu0) hh2 _) (by positivity) (by positivity))
            have hpow : (h.2) ^ M * ‖h.1‖ ≤ ‖h‖ ^ M * ‖h‖ :=
              mul_le_mul (pow_le_pow_left₀ (le_of_lt hu0) hh2 _) hh1' (norm_nonneg _)
                (by positivity)
            calc max C1 0 * (h.2) ^ M * ‖h.1‖
                = max C1 0 * ((h.2) ^ M * ‖h.1‖) := by ring
              _ ≤ max C1 0 * (‖h‖ ^ M * ‖h‖) :=
                  mul_le_mul_of_nonneg_left hpow (by positivity)
              _ = max C1 0 * ‖h‖ ^ (M + 1) := by rw [pow_succ]
        _ = (max C0 0 + max C1 0) * ‖h‖ ^ (M + 1) := by ring
  have hpow : (fun h : X × ℝ => ‖h‖ ^ (M + 1)) =o[𝓝 0] (fun h : X × ℝ => h) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    refine Metric.eventually_nhds_iff.mpr ⟨min 1 c / 2, by positivity, ?_⟩
    intro h hh
    simp only [dist_eq_norm, sub_zero] at hh
    have h1 : ‖h‖ < 1 := lt_of_lt_of_le hh (by have := min_le_left (1:ℝ) c; linarith)
    have h2 : ‖h‖ < c / 2 := lt_of_lt_of_le hh (by have := min_le_right (1:ℝ) c; linarith)
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖h‖ ^ (M + 1) ≤ ‖h‖ ^ 2 := pow_le_pow_of_le_one (norm_nonneg h) h1.le (by omega : 2 ≤ M + 1)
      _ = ‖h‖ * ‖h‖ := by ring
      _ ≤ c * ‖h‖ := by nlinarith [norm_nonneg h]
  simpa using hbig.trans_isLittleO hpow



/-- The main extension lemma: a function vanishing on the closed lower half-plane and bounded by
`z.2 ^ (m+1-k)` on its `k`-th derivatives on the upper half-plane is `C^m` at `(x₀,0)`. -/
theorem contDiffAt_of_flat_halfspace_bounds {X : Type u} {E : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : X × ℝ → E} {x₀ : X} {m : ℕ} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hz : ∀ z : X × ℝ, ‖z - (x₀, 0)‖ < ρ → z.2 ≤ 0 → f z = 0)
    (hC : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) f
        ((Metric.ball (x₀, 0) ρ) ∩ {z : X × ℝ | 0 < z.2}))
    (hb : ∀ k ≤ m, ∃ C : ℝ, ∀ z : X × ℝ, ‖z - (x₀, 0)‖ < ρ → 0 < z.2 →
        ‖iteratedFDeriv ℝ k f z‖ ≤ C * (z.2) ^ (m + 1 - k)) :
    ContDiffAt ℝ ((m : ℕ) : WithTop ℕ∞) f (x₀, 0) := by
  classical
  have key : ∀ (n : ℕ) (E' : Type (max u (v+1))) [NormedAddCommGroup E'] [NormedSpace ℝ E']
      (g : X × ℝ → E'),
      (∀ z : X × ℝ, ‖z - (x₀, 0)‖ < ρ → z.2 ≤ 0 → g z = 0) →
      ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) g
        ((Metric.ball (x₀, 0) ρ) ∩ {z : X × ℝ | 0 < z.2}) →
      (∀ k ≤ n, ∃ C : ℝ, ∀ z : X × ℝ, ‖z - (x₀, 0)‖ < ρ → 0 < z.2 →
        ‖iteratedFDeriv ℝ k g z‖ ≤ C * (z.2) ^ (n + 1 - k)) →
      ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) g (x₀, 0) := by
    intro n
    induction n with
    | zero =>
      intro E' _ _ g hgz hgC hgb
      have hcontAt : ∀ b : X × ℝ, ‖b - (x₀, 0)‖ < ρ / 2 → ContinuousAt g b := by
        intro b hbhalf
        have hbρ : ‖b - (x₀, 0)‖ < ρ := by linarith
        rcases lt_trichotomy b.2 0 with hb2 | hb2 | hb2
        · exact (continuousAt_const (x := b) (y := (0 : E'))).congr
            (eventuallyEq_zero_of_lt hgz hbρ hb2).symm
        · have hgb0 : g b = 0 := hgz b hbρ hb2.le
          obtain ⟨C, hCb⟩ := hgb 0 (Nat.zero_le _)
          have hCb' : ∀ z : X × ℝ, ‖z - (x₀, 0)‖ < ρ → 0 < z.2 → ‖g z‖ ≤ C * z.2 := by
            intro z h1 h2; simpa using hCb z h1 h2
          rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
          rw [NormedAddGroup.tendsto_nhds_zero]
          intro ε hε
          refine Metric.eventually_nhds_iff.mpr
            ⟨min (ε / max C 1) (ρ / 2), lt_min (by positivity) (by linarith), ?_⟩
          intro z hz
          rw [dist_eq_norm] at hz
          have h1 : ‖z - b‖ < ε / max C 1 := lt_of_lt_of_le hz (min_le_left _ _)
          have h2 : ‖z - b‖ < ρ / 2 := lt_of_lt_of_le hz (min_le_right _ _)
          have hzρ : ‖z - (x₀, 0)‖ < ρ := by
            calc ‖z - (x₀, 0)‖ ≤ ‖z - b‖ + ‖b - (x₀, 0)‖ := by
                  rw [show z - (x₀, 0) = (z - b) + (b - (x₀, 0)) by abel]
                  exact norm_add_le _ _
              _ < ρ / 2 + ρ / 2 := by linarith
              _ = ρ := by ring
          have hC1 : (0:ℝ) < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
          rw [hgb0, sub_zero, norm_norm]
          by_cases hzz : 0 < z.2
          · have h3 : ‖g z‖ ≤ C * z.2 := hCb' z hzρ hzz
            have hz2 : z.2 ≤ ‖z - b‖ := by
              have h := norm_snd_le (z - b)
              rw [Real.norm_eq_abs] at h
              simpa [hb2, abs_of_pos hzz] using h
            have h4 : C * z.2 ≤ max C 1 * ‖z - b‖ := by
              rcases le_total C 0 with hC0 | hC0
              · have h5 : C * z.2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC0 (by linarith)
                have h6 : (0:ℝ) ≤ max C 1 * ‖z - b‖ := by positivity
                linarith
              · exact mul_le_mul (le_max_left _ _) hz2 (by linarith) (le_trans hC0 (le_max_left C 1))
            calc ‖g z‖ ≤ max C 1 * ‖z - b‖ := le_trans h3 h4
              _ < max C 1 * (ε / max C 1) := mul_lt_mul_of_pos_left h1 hC1
              _ = ε := by field_simp
          · push_neg at hzz
            simpa [hgz z hzρ hzz] using hε
        · exact hgC.continuousOn.continuousAt
            ((isOpen_ball.inter (isOpen_Ioi.preimage continuous_snd)).mem_nhds
              ⟨Metric.mem_ball.mpr (by simpa [dist_eq_norm] using hbρ), hb2⟩)
      have hContOn : ContinuousOn g (Metric.ball (x₀, 0) (ρ / 2)) := fun b hb =>
        (hcontAt b (by simpa [dist_eq_norm] using Metric.mem_ball.mp hb)).continuousWithinAt
      exact contDiffAt_zero.mpr ⟨_, Metric.ball_mem_nhds _ (by linarith), hContOn⟩
    | succ n ih =>
      intro E' _ _ g hgz hgC hgb
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (((n : ℕ) : WithTop ℕ∞) + 1) by push_cast; rfl]
      rw [contDiffAt_succ_iff_hasFDerivAt]
      obtain ⟨C0, hC0⟩ := hgb 0 (Nat.zero_le _)
      obtain ⟨C1, hC1⟩ := hgb 1 (by omega)
      have hb0' : ∃ C : ℝ, ∀ z : X × ℝ, ‖z - (x₀, 0)‖ < ρ → 0 < z.2 →
          ‖g z‖ ≤ C * (z.2) ^ ((n+1) + 1) := ⟨C0, fun z h1 h2 => by
            have := hC0 z h1 h2; simpa using this⟩
      have hb1' : ∃ C : ℝ, ∀ z : X × ℝ, ‖z - (x₀, 0)‖ < ρ → 0 < z.2 →
          ‖fderiv ℝ g z‖ ≤ C * (z.2) ^ (n+1) := ⟨C1, fun z h1 h2 => by
            have := hC1 z h1 h2
            rw [norm_iteratedFDeriv_one] at this
            simpa [Nat.add_sub_cancel] using this⟩
      have hbdry : ∀ z : X × ℝ, ‖z - (x₀, 0)‖ < ρ → z.2 = 0 →
          HasFDerivAt g (0 : (X × ℝ) →L[ℝ] E') z :=
        fun z h1 h2 => hasFDerivAt_bdry (M := n+1) (by omega) hρ hgz hgC hb0' hb1' h1 h2
      have hderiv0 : ∀ z : X × ℝ, ‖z - (x₀, 0)‖ < ρ → z.2 ≤ 0 → fderiv ℝ g z = 0 := by
        intro z hzρ hz2
        rcases lt_or_eq_of_le hz2 with h | h
        · rw [(eventuallyEq_zero_of_lt hgz hzρ h).fderiv_eq]; simp
        · rw [(hbdry z hzρ h).fderiv]
      have hC' : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fderiv ℝ g)
          ((Metric.ball (x₀, 0) ρ) ∩ {z : X × ℝ | 0 < z.2}) := by
        have h := ContDiffOn.fderiv_of_isOpen (𝕜 := ℝ) (m := (n : WithTop ℕ∞)) hgC
          (isOpen_ball.inter (isOpen_Ioi.preimage continuous_snd))
          (show (n : WithTop ℕ∞) + 1 ≤ ((n + 1 : ℕ) : WithTop ℕ∞) by push_cast; rfl)
        simpa using h
      have hb' : ∀ k ≤ n, ∃ C : ℝ, ∀ z : X × ℝ, ‖z - (x₀, 0)‖ < ρ → 0 < z.2 →
          ‖iteratedFDeriv ℝ k (fderiv ℝ g) z‖ ≤ C * (z.2) ^ (n + 1 - k) := by
        intro k hk
        obtain ⟨C, hCk⟩ := hgb (k + 1) (by omega)
        refine ⟨max C 0, fun z h1 h2 => ?_⟩
        rw [norm_iteratedFDeriv_fderiv]
        have h := hCk z h1 h2
        have hexp : (n + 1) + 1 - (k + 1) = n + 1 - k := by omega
        rw [hexp] at h
        calc ‖iteratedFDeriv ℝ (k + 1) g z‖ ≤ C * (z.2) ^ (n + 1 - k) := h
          _ ≤ max C 0 * (z.2) ^ (n + 1 - k) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      refine ⟨fderiv ℝ g, ?_, ih (X × ℝ →L[ℝ] E') (fderiv ℝ g) hderiv0 hC' hb'⟩
      refine ⟨Metric.ball (x₀, 0) (ρ / 2), Metric.ball_mem_nhds _ (by linarith), ?_⟩
      intro z hz
      have hzρ : ‖z - (x₀, 0)‖ < ρ := by
        have := Metric.mem_ball.mp hz; rw [dist_eq_norm] at this; linarith
      rcases lt_trichotomy z.2 0 with h2 | h2 | h2
      · rw [hderiv0 z hzρ h2.le]
        have hconst : HasFDerivAt (fun _ : X × ℝ => (0 : E')) (0 : (X × ℝ) →L[ℝ] E') z :=
          hasFDerivAt_const (0 : E') z
        exact hconst.congr_of_eventuallyEq (eventuallyEq_zero_of_lt hgz hzρ h2)
      · rw [(hbdry z hzρ h2).fderiv]
        exact hbdry z hzρ h2
      · have hdiff : DifferentiableAt ℝ g z :=
          (hgC.contDiffAt (x := z) ((isOpen_ball.inter
            (isOpen_Ioi.preimage continuous_snd)).mem_nhds
            ⟨Metric.mem_ball.mpr (by simpa [dist_eq_norm] using hzρ), h2⟩)).differentiableAt
            (by exact_mod_cast (show n+1 ≠ 0 by omega))
        exact hdiff.hasFDerivAt
  -- lift the codomain to a universe closed under `X × ℝ →L ·`
  have hlift : ContDiffAt ℝ ((m : ℕ) : WithTop ℕ∞)
      (fun p : X × ℝ => (LinearIsometryEquiv.ulift (R := ℝ) (E := E)).symm (f p)) (x₀, 0) := by
    refine key m (ULift.{max u (v+1), v} E)
      (fun p : X × ℝ => (LinearIsometryEquiv.ulift (R := ℝ) (E := E)).symm (f p)) ?_ ?_ ?_
    · intro z h1 h2
      rw [hz z h1 h2]; rfl
    · have h := (ContinuousLinearEquiv.comp_contDiffOn_iff (𝕜 := ℝ)
        (e := (LinearIsometryEquiv.ulift (R := ℝ) (E := E)).symm.toContinuousLinearEquiv)).mpr hC
      simpa [Function.comp_def, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        ContinuousLinearEquiv.coe_toLinearEquiv] using h
    · intro k hk
      obtain ⟨C, hCk⟩ := hb k hk
      refine ⟨C, fun z h1 h2 => ?_⟩
      have hnorm : ‖iteratedFDeriv ℝ k
            (fun p : X × ℝ => (LinearIsometryEquiv.ulift (R := ℝ) (E := E)).symm (f p)) z‖
          = ‖iteratedFDeriv ℝ k f z‖ := by
        have h := LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left (𝕜 := ℝ)
          (g := (LinearIsometryEquiv.ulift (R := ℝ) (E := E)).symm) (f := f) uniqueDiffOn_univ
          (mem_univ z) k
        simpa [Function.comp_def, iteratedFDerivWithin_univ] using h
      rw [hnorm]
      exact hCk z h1 h2
  have htransport := (ContinuousLinearEquiv.comp_contDiffAt_iff (𝕜 := ℝ)
    (f := f) (x := (x₀, 0)) (n := ((m : ℕ) : WithTop ℕ∞))
    (e := (LinearIsometryEquiv.ulift (R := ℝ) (E := E)).symm.toContinuousLinearEquiv)).mp
  exact htransport (by simpa [Function.comp_def] using hlift)

end Work.Drive
