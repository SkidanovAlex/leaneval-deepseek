import Mathlib
import Submission.Work.Drive.oFatDefs
import Submission.Work.Drive.chordFrame
import Submission.Work.Drive.nmf_deriv_deriv_nonpos_of_globalMax
import Submission.Work.Drive.nmf_uniform_modulus_periodic
import Submission.Work.Drive.nmf_norm_sub_ge_of_speed_ge
import Submission.Work.Drive.nmf_pos_of_secondDeriv_neg

noncomputable section



namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-! ## Auxiliary calculus lemmas -/

/-- The derivative of a `T`-periodic function is `T`-periodic. -/
lemma nmf_periodic_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    {T : ℝ} (hf : Function.Periodic f T) : Function.Periodic (deriv f) T := by
  intro t
  have h1 : (fun y : ℝ => f (y + T)) = f := funext fun y => hf y
  have h2 : deriv (fun y : ℝ => f (y + T)) t = deriv f (t + T) := deriv_comp_add_const f T t
  rw [h1] at h2
  exact h2.symm

/-- The elementary triangle-inequality corollary `‖x‖ ≤ ‖y‖ + ‖x - y‖`. -/
lemma nmf_abs_norm_sub_le {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
  have h := abs_norm_sub_norm_le x y
  rw [abs_le] at h
  linarith [h.2]

/-- **The second-derivative bound at a global maximiser of `‖f‖`.**  If `‖f‖` is maximal at `t₀`
and `f` is twice differentiable there, then the second derivative of `f` in the radial direction is
strictly negative: `⟪r''(t₀), e⟫ ≤ -‖v(t₀)‖²/‖r(t₀)‖`, where `e` is the unit vector along `r(t₀)`. -/
lemma nmf_secondDeriv_le_at_globalMax {f : ℝ → Space} {t₀ : ℝ}
    (hmax : ∀ t, ‖f t‖ ≤ ‖f t₀‖)
    (hd : ∀ t, DifferentiableAt ℝ f t) (hd2 : ∀ t, DifferentiableAt ℝ (deriv f) t)
    (hpos : 0 < ‖f t₀‖) :
    inner ℝ (deriv (deriv f) t₀) ((‖f t₀‖)⁻¹ • f t₀) ≤ -(‖deriv f t₀‖ ^ 2) / ‖f t₀‖ := by
  set g : ℝ → ℝ := fun t => inner ℝ (f t) (f t) with hgdef
  have hgmax : ∀ t, g t ≤ g t₀ := by
    intro t
    simp only [hgdef]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    nlinarith [hmax t, norm_nonneg (f t), norm_nonneg (f t₀)]
  have hgc : ContinuousAt g t₀ := by
    rw [hgdef]
    exact (hd t₀).continuousAt.inner (hd t₀).continuousAt
  have hkey : deriv (deriv g) t₀ ≤ 0 := nmf_deriv_deriv_nonpos_of_globalMax hgmax hgc
  have hg_eq : deriv g = fun t => 2 * inner ℝ (deriv f t) (f t) := by
    funext t
    rw [hgdef, deriv_inner_apply ℝ (hd t) (hd t), real_inner_comm (f t) (deriv f t)]
    ring
  have hg2 : deriv (deriv g) t₀
      = 2 * (inner ℝ (deriv f t₀) (deriv f t₀) + inner ℝ (deriv (deriv f) t₀) (f t₀)) := by
    rw [hg_eq]
    have hinner : HasDerivAt (fun t : ℝ => inner ℝ (deriv f t) (f t))
        (inner ℝ (deriv f t₀) (deriv f t₀) + inner ℝ (deriv (deriv f) t₀) (f t₀)) t₀ :=
      HasDerivAt.inner ℝ ((hd2 t₀).hasDerivAt) ((hd t₀).hasDerivAt)
    have := hinner.const_mul 2
    rw [this.deriv]
  have hmain : inner ℝ (deriv (deriv f) t₀) (f t₀) ≤ -(‖deriv f t₀‖ ^ 2) := by
    have h' : 2 * (inner ℝ (deriv f t₀) (deriv f t₀) + inner ℝ (deriv (deriv f) t₀) (f t₀)) ≤ 0 := by
      rw [← hg2]; exact hkey
    rw [real_inner_self_eq_norm_sq] at h'
    linarith
  rw [inner_smul_right]
  have h2 : 0 < ‖f t₀‖⁻¹ := inv_pos.mpr hpos
  calc ‖f t₀‖⁻¹ * inner ℝ (deriv (deriv f) t₀) (f t₀)
      ≤ ‖f t₀‖⁻¹ * (-(‖deriv f t₀‖ ^ 2)) := mul_le_mul_of_nonneg_left hmain (le_of_lt h2)
    _ = -(‖deriv f t₀‖ ^ 2) / ‖f t₀‖ := by rw [div_eq_mul_inv]; exact mul_comm _ _

/-- **Reference data of a smooth knot**: a positive lower bound for the speed, a positive upper
bound for the norm, an upper bound for the acceleration on the whole line (via periodicity), and a
uniform continuity modulus for the acceleration. -/
lemma nmf_reference_data {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ mm R₀ CM : ℝ, 0 < mm ∧ 0 < R₀ ∧ 0 < CM ∧
      (∀ t : ℝ, mm ≤ ‖velocity r t‖) ∧
      (∀ t : ℝ, ‖r t‖ ≤ R₀) ∧ (∃ t : ℝ, ‖r t‖ = R₀) ∧
      (∀ t : ℝ, ‖deriv (deriv r) t‖ ≤ CM) ∧
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ,
        |x - y| ≤ δ → ‖deriv (deriv r) x - deriv (deriv r) y‖ ≤ ε) := by
  obtain ⟨m, M, C, hm, hM, hC, hminvel, hmaxvel, hlipvel⟩ := exists_knot_c2_bounds hr
  -- the farthest point
  obtain ⟨tR, htR, hmaxR⟩ := isCompact_Icc.exists_isMaxOn
    (s := Set.Icc (0 : ℝ) period) ⟨0, le_rfl, period_pos.le⟩ hr.continuous.norm.continuousOn
  have hRbound : ∀ t : ℝ, ‖r t‖ ≤ ‖r tR‖ := by
    intro t
    obtain ⟨y, hy, hty⟩ := hr.periodic.exists_mem_Ico period_pos t 0
    have hy' : y ∈ Set.Icc (0 : ℝ) period := ⟨hy.1, by linarith [hy.2]⟩
    rw [hty]
    exact hmaxR hy'
  have hRpos : 0 < ‖r tR‖ := by
    by_contra hcon
    have h0 : ‖r tR‖ = 0 := le_antisymm (le_of_not_gt hcon) (norm_nonneg _)
    have hzero : ∀ t : ℝ, r t = 0 := by
      intro t
      have h := hRbound t
      rw [h0] at h
      exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
    have hmem0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) period := ⟨le_rfl, period_pos⟩
    have hmemh : period / 2 ∈ Set.Ico (0 : ℝ) period :=
      ⟨by linarith [period_pos], by linarith [period_pos]⟩
    have hinj := hr.injective_on_period hmem0 hmemh
    have hcontra : (0 : ℝ) = period / 2 := by
      apply hinj
      rw [hzero 0, hzero (period / 2)]
    linarith [period_pos]
  -- periodicity and bounds for the second derivative
  have hd1per : Function.Periodic (deriv r) period := nmf_periodic_deriv hr.periodic
  have hd1cont : Continuous (deriv r) := by
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le le_top
    exact ((contDiff_infty_iff_deriv (𝕜 := ℝ) (f := r)).mp hs).2.continuous
  have hd2per : Function.Periodic (deriv (deriv r)) period := nmf_periodic_deriv hd1per
  have hd2cont : Continuous (deriv (deriv r)) := by
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le le_top
    have h1 := ((contDiff_infty_iff_deriv (𝕜 := ℝ) (f := r)).mp hs).2
    exact (((contDiff_infty_iff_deriv (𝕜 := ℝ) (f := deriv r)).mp h1).2).continuous
  obtain ⟨C₂, hC₂⟩ := (hd2per.isBounded_of_continuous period_pos.ne' hd2cont).exists_norm_le
  refine ⟨m, ‖r tR‖, max C₂ 1, hm, hRpos, lt_max_of_lt_right zero_lt_one, hminvel, hRbound,
    ⟨tR, rfl⟩, ?_, ?_⟩
  · intro t
    exact le_trans (hC₂ _ ⟨t, rfl⟩) (le_max_left _ _)
  · intro ε hε
    exact nmf_uniform_modulus_periodic period_pos hd2per hd2cont hε


/-- **No middle on a chord with both ends near a maximiser of `‖r‖`.**

There are a `C²`-radius `ε₃ > 0` and a window radius `ηc > 0`, both *uniform over the `C²`-ball*
around the reference knot `r` and over the choice of maximiser, such that: for every knot `r'` that
is `C²`-`ε₃`-close to `r`, for every `t₀` with `‖r' t₀‖` maximal, and for every *non-degenerate*
chord `(a, a+y)` of `r'` (`0 < y < period`) whose two ends lie in `[t₀ - ηc, t₀ + ηc]`, no point
`r' u` with `u ∈ [a, a+y]` lies in the open segment of the two chord ends. -/
theorem noMiddle_near_farthest {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ ε₃ : ℝ, 0 < ε₃ ∧ ∃ ηc : ℝ, 0 < ηc ∧
      ∀ r' : ℝ → Space, IsSmoothKnot r' →
        (∀ t : ℝ, ‖r' t - r t‖ < ε₃ ∧ ‖velocity r' t - velocity r t‖ < ε₃ ∧
          ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε₃) →
        ∀ t₀ : ℝ, (∀ t : ℝ, ‖r' t‖ ≤ ‖r' t₀‖) →
          ∀ a y u : ℝ, 0 < y → y < period →
            t₀ - ηc ≤ a → a ≤ t₀ + ηc → t₀ - ηc ≤ a + y → a + y ≤ t₀ + ηc →
            a ≤ u → u ≤ a + y → r' u ∉ openSegment ℝ (r' a) (r' (a + y)) := by
  obtain ⟨mm, R₀, CM, hmm, hR₀, hCM, hspeed, hRb, ⟨tstar, htstar⟩, hCMb, hmod⟩ :=
    nmf_reference_data hr
  set K2 : ℝ := CM + 1 with hK2def
  have hK2pos : 0 < K2 := by rw [hK2def]; linarith
  set c1 : ℝ := (mm / 2) ^ 2 / (R₀ + 1) with hc1def
  have hc1pos : 0 < c1 := by
    rw [hc1def]
    exact div_pos (pow_pos (by linarith) 2) (by linarith)
  obtain ⟨δω, hδωpos, hδω⟩ := hmod (c1 / 4) (by positivity)
  set ε₃ : ℝ := min 1 (min (mm / 2) (min (R₀ / 2) (c1 / 8))) with hε₃def
  have hε₃pos : 0 < ε₃ := by
    rw [hε₃def]
    exact lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hε₃1 : ε₃ ≤ 1 := by rw [hε₃def]; exact min_le_left _ _
  have hε₃mm : ε₃ ≤ mm / 2 := by
    rw [hε₃def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hε₃R : ε₃ ≤ R₀ / 2 := by
    rw [hε₃def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε₃c : ε₃ ≤ c1 / 8 := by
    rw [hε₃def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  set ηc : ℝ := min δω (min (mm / (8 * K2)) (min (c1 * mm / (16 * K2 ^ 2)) 1)) with hηcdef
  have hηcpos : 0 < ηc := by
    rw [hηcdef]
    exact lt_min hδωpos (lt_min (by positivity) (lt_min (by positivity) one_pos))
  have hηcω : ηc ≤ δω := by rw [hηcdef]; exact min_le_left _ _
  have hηcm : ηc ≤ mm / (8 * K2) := by
    rw [hηcdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hηcc : ηc ≤ c1 * mm / (16 * K2 ^ 2) := by
    rw [hηcdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  refine ⟨ε₃, hε₃pos, ηc, hηcpos, ?_⟩
  intro r' hr' hclose t₀ hmax a y u hy0 hylt ha1 ha2 hay1 hay2 hau hua
  have hcl1 : ∀ t : ℝ, ‖r' t - r t‖ < ε₃ := fun t => (hclose t).1
  have hcl2 : ∀ t : ℝ, ‖deriv r' t - deriv r t‖ < ε₃ := fun t => (hclose t).2.1
  have hcl3 : ∀ t : ℝ, ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε₃ := fun t => (hclose t).2.2
  -- smoothness of `r'`
  have hdr : ∀ t : ℝ, HasDerivAt r' (deriv r' t) t := fun t =>
    ((hr'.smooth.differentiable (by simp)) t).hasDerivAt
  have hdr2 : ∀ t : ℝ, HasDerivAt (deriv r') (deriv (deriv r') t) t := by
    intro t
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r' := hr'.smooth.of_le le_top
    have hd1r : Differentiable ℝ (deriv r') :=
      ((contDiff_infty_iff_deriv (𝕜 := ℝ) (f := r')).mp hs).2.differentiable (by simp)
    exact (hd1r t).hasDerivAt
  have hc1r : Continuous (deriv r') := by
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r' := hr'.smooth.of_le le_top
    exact ((contDiff_infty_iff_deriv (𝕜 := ℝ) (f := r')).mp hs).2.continuous
  have hr'cont : Continuous r' := hr'.continuous
  -- the farthest distance
  set R : ℝ := ‖r' t₀‖ with hRdef
  have hRge : R₀ / 2 ≤ R := by
    have h1 : ‖r' tstar‖ ≤ R := by rw [hRdef]; exact hmax tstar
    have h2 : ‖r tstar‖ ≤ ‖r' tstar‖ + ‖r tstar - r' tstar‖ := nmf_abs_norm_sub_le _ _
    have h3 : ‖r tstar - r' tstar‖ < ε₃ := by simpa [norm_sub_rev] using hcl1 tstar
    rw [htstar] at h2
    linarith
  have hRpos : 0 < R := lt_of_lt_of_le (by linarith) hRge
  have hRle : R ≤ R₀ + 1 := by
    have h1 : ‖r' t₀‖ ≤ ‖r t₀‖ + ‖r' t₀ - r t₀‖ := nmf_abs_norm_sub_le _ _
    have h2 : ‖r t₀‖ ≤ R₀ := hRb t₀
    have h3 : ‖r' t₀ - r t₀‖ < ε₃ := hcl1 t₀
    rw [hRdef]
    linarith
  have hspeed' : ∀ t : ℝ, mm / 2 ≤ ‖deriv r' t‖ := by
    intro t
    have h1 : ‖deriv r t‖ ≤ ‖deriv r' t‖ + ‖deriv r t - deriv r' t‖ := nmf_abs_norm_sub_le _ _
    have h2 : mm ≤ ‖deriv r t‖ := hspeed t
    have h3 : ‖deriv r t - deriv r' t‖ < ε₃ := by simpa [norm_sub_rev] using hcl2 t
    linarith
  have hK2b : ∀ t : ℝ, ‖deriv (deriv r') t‖ ≤ K2 := by
    intro t
    have h1 : ‖deriv (deriv r') t‖
        ≤ ‖deriv (deriv r) t‖ + ‖deriv (deriv r') t - deriv (deriv r) t‖ :=
      nmf_abs_norm_sub_le _ _
    have h2 : ‖deriv (deriv r) t‖ ≤ CM := hCMb t
    have h3 : ‖deriv (deriv r') t - deriv (deriv r) t‖ < ε₃ := hcl3 t
    rw [hK2def]
    linarith
  -- the radial direction at the maximiser
  set e : Space := R⁻¹ • r' t₀ with hedef
  have henorm : ‖e‖ = 1 := by
    rw [hedef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos),
      inv_mul_cancel₀ (ne_of_gt hRpos)]
  have hFt₀ : inner ℝ (r' t₀) e = R := by
    rw [hedef, inner_smul_right, real_inner_self_eq_norm_sq, ← hRdef]
    field_simp
  have hFmax : ∀ t : ℝ, inner ℝ (r' t) e ≤ inner ℝ (r' t₀) e := by
    intro t
    rw [hFt₀]
    have h := abs_real_inner_le_norm (r' t) e
    have h2 : inner ℝ (r' t) e ≤ ‖r' t‖ * ‖e‖ := le_trans (le_abs_self _) h
    rw [henorm, mul_one] at h2
    refine le_trans h2 ?_
    rw [hRdef]
    exact hmax t
  have hsec : inner ℝ (deriv (deriv r') t₀) e ≤ -(‖deriv r' t₀‖ ^ 2) / R := by
    have h := nmf_secondDeriv_le_at_globalMax (f := r') (t₀ := t₀) hmax
      (fun t => (hdr t).differentiableAt) (fun t => (hdr2 t).differentiableAt) hRpos
    simpa [hRdef, hedef] using h
  have hc1le : c1 ≤ (‖deriv r' t₀‖ ^ 2) / R := by
    have h1 : mm / 2 ≤ ‖deriv r' t₀‖ := hspeed' t₀
    have h2 : (mm / 2) ^ 2 ≤ ‖deriv r' t₀‖ ^ 2 := by nlinarith
    rw [hc1def]
    exact div_le_div₀ (by positivity) h2 hRpos hRle
  -- propagation of the second-derivative bound to the window
  have hprop : ∀ θ : ℝ, |θ - t₀| ≤ ηc → inner ℝ (deriv (deriv r') θ) e ≤ -(c1 / 2) := by
    intro θ hθ
    have hsplit : inner ℝ (deriv (deriv r') θ) e
        = inner ℝ (deriv (deriv r') t₀) e
          + inner ℝ (deriv (deriv r') θ - deriv (deriv r') t₀) e := by
      rw [← inner_add_left]
      congr 1
      abel
    have hb2 : ‖deriv (deriv r) θ - deriv (deriv r) t₀‖ ≤ c1 / 4 :=
      hδω θ t₀ (le_trans hθ hηcω)
    have hbd : ‖deriv (deriv r') θ - deriv (deriv r') t₀‖ ≤ c1 / 2 := by
      have e1 : ‖deriv (deriv r') θ - deriv (deriv r) θ‖ < ε₃ := hcl3 θ
      have e3 : ‖deriv (deriv r') t₀ - deriv (deriv r) t₀‖ < ε₃ := hcl3 t₀
      have e3' : ‖deriv (deriv r) t₀ - deriv (deriv r') t₀‖ < ε₃ := by
        rwa [norm_sub_rev] at e3
      have h2 := norm_add_le (deriv (deriv r) θ - deriv (deriv r) t₀)
        (deriv (deriv r) t₀ - deriv (deriv r') t₀)
      calc ‖deriv (deriv r') θ - deriv (deriv r') t₀‖
          = ‖(deriv (deriv r') θ - deriv (deriv r) θ)
              + ((deriv (deriv r) θ - deriv (deriv r) t₀)
                + (deriv (deriv r) t₀ - deriv (deriv r') t₀))‖ := by
            congr 1
            abel
        _ ≤ ‖deriv (deriv r') θ - deriv (deriv r) θ‖
              + ‖(deriv (deriv r) θ - deriv (deriv r) t₀)
                + (deriv (deriv r) t₀ - deriv (deriv r') t₀)‖ := norm_add_le _ _
        _ ≤ c1 / 2 := by linarith
    have hbn : inner ℝ (deriv (deriv r') θ - deriv (deriv r') t₀) e
        ≤ ‖deriv (deriv r') θ - deriv (deriv r') t₀‖ := by
      calc inner ℝ (deriv (deriv r') θ - deriv (deriv r') t₀) e
          ≤ |inner ℝ (deriv (deriv r') θ - deriv (deriv r') t₀) e| := le_abs_self _
        _ ≤ ‖deriv (deriv r') θ - deriv (deriv r') t₀‖ * ‖e‖ := abs_real_inner_le_norm _ _
        _ = ‖deriv (deriv r') θ - deriv (deriv r') t₀‖ := by rw [henorm, mul_one]
    have hsec' : inner ℝ (deriv (deriv r') t₀) e ≤ -(c1) := by
      refine le_trans hsec ?_
      rw [neg_div]
      exact neg_le_neg hc1le
    rw [hsplit]
    linarith
  -- the first-derivative bound for the radial profile
  have hFderiv : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => inner ℝ (r' t) e) (inner ℝ (deriv r' θ) e) θ := by
    intro θ
    have h := HasDerivAt.inner ℝ (hdr θ) (hasDerivAt_const θ e)
    simpa [inner_zero_right, zero_add] using h
  have hFderiv_eq : deriv (fun t : ℝ => inner ℝ (r' t) e) = fun θ => inner ℝ (deriv r' θ) e :=
    funext fun θ => (hFderiv θ).deriv
  have hFderiv2 : ∀ θ : ℝ, HasDerivAt (deriv (fun t : ℝ => inner ℝ (r' t) e))
      (inner ℝ (deriv (deriv r') θ) e) θ := by
    intro θ
    have h := HasDerivAt.inner ℝ (hdr2 θ) (hasDerivAt_const θ e)
    rw [hFderiv_eq]
    simpa [inner_zero_right, zero_add] using h
  have hFderiv0 : deriv (fun t : ℝ => inner ℝ (r' t) e) t₀ = 0 := by
    have hloc : IsLocalMax (fun t : ℝ => inner ℝ (r' t) e) t₀ := Filter.Eventually.of_forall hFmax
    exact hloc.deriv_eq_zero
  have hF'le : ∀ θ : ℝ, |θ - t₀| ≤ ηc →
      |deriv (fun t : ℝ => inner ℝ (r' t) e) θ| ≤ K2 * ηc := by
    intro θ hθ
    have hbd : ∀ x : ℝ, ‖inner ℝ (deriv (deriv r') x) e‖ ≤ K2 := by
      intro x
      calc ‖inner ℝ (deriv (deriv r') x) e‖ ≤ ‖deriv (deriv r') x‖ * ‖e‖ := norm_inner_le_norm _ _
        _ = ‖deriv (deriv r') x‖ := by rw [henorm, mul_one]
        _ ≤ K2 := hK2b x
    rcases le_total t₀ θ with hle | hle
    · have h := norm_image_sub_le_of_norm_deriv_le_segment'
        (f := deriv (fun t : ℝ => inner ℝ (r' t) e))
        (f' := fun x => inner ℝ (deriv (deriv r') x) e) (C := K2) (a := t₀) (b := θ)
        (fun x hx => (hFderiv2 x).hasDerivWithinAt) (fun x hx => hbd x) θ ⟨hle, le_rfl⟩
      rw [Real.norm_eq_abs] at h
      have hθle : θ - t₀ ≤ ηc := by have := abs_le.mp hθ; linarith
      calc |deriv (fun t : ℝ => inner ℝ (r' t) e) θ|
          = |deriv (fun t : ℝ => inner ℝ (r' t) e) θ
              - deriv (fun t : ℝ => inner ℝ (r' t) e) t₀| := by rw [hFderiv0, sub_zero]
        _ ≤ K2 * (θ - t₀) := h
        _ ≤ K2 * ηc := mul_le_mul_of_nonneg_left hθle (le_of_lt hK2pos)
    · have h := norm_image_sub_le_of_norm_deriv_le_segment'
        (f := deriv (fun t : ℝ => inner ℝ (r' t) e))
        (f' := fun x => inner ℝ (deriv (deriv r') x) e) (C := K2) (a := θ) (b := t₀)
        (fun x hx => (hFderiv2 x).hasDerivWithinAt) (fun x hx => hbd x) t₀ ⟨hle, le_rfl⟩
      rw [Real.norm_eq_abs] at h
      have hθle : t₀ - θ ≤ ηc := by have := abs_le.mp hθ; linarith
      calc |deriv (fun t : ℝ => inner ℝ (r' t) e) θ|
          = |deriv (fun t : ℝ => inner ℝ (r' t) e) t₀
              - deriv (fun t : ℝ => inner ℝ (r' t) e) θ| := by rw [hFderiv0, zero_sub, abs_neg]
        _ ≤ K2 * (t₀ - θ) := h
        _ ≤ K2 * ηc := mul_le_mul_of_nonneg_left hθle (le_of_lt hK2pos)
  -- the chord
  set w : Space := r' (a + y) - r' a with hwdef
  have hwbound : |inner ℝ w e| ≤ K2 * ηc * y := by
    have hFdiff : ∀ x ∈ Set.Icc a (a + y),
        |deriv (fun t : ℝ => inner ℝ (r' t) e) x| ≤ K2 * ηc := by
      intro x hx
      refine hF'le x ?_
      rw [abs_le]
      exact ⟨by linarith [hx.1, ha1], by linarith [hx.2, hay2]⟩
    have hderivw : ∀ x ∈ Set.Icc a (a + y),
        HasDerivWithinAt (fun t : ℝ => inner ℝ (r' t) e)
          (deriv (fun t : ℝ => inner ℝ (r' t) e) x) (Set.Icc a (a + y)) x := by
      intro x hx
      rw [hFderiv_eq]
      exact (hFderiv x).hasDerivWithinAt
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun t : ℝ => inner ℝ (r' t) e)
      (f' := fun x => deriv (fun t : ℝ => inner ℝ (r' t) e) x) (C := K2 * ηc)
      (a := a) (b := a + y) hderivw (fun x hx => hFdiff x ⟨hx.1, hx.2.le⟩) (a + y)
      ⟨by linarith, le_rfl⟩
    rw [Real.norm_eq_abs, show a + y - a = y by ring] at hmvt
    have h1 : inner ℝ (r' (a + y)) e - inner ℝ (r' a) e = inner ℝ w e := by
      rw [← inner_sub_left, ← hwdef]
    rwa [h1] at hmvt
  have hwlen : (mm / 4) * y ≤ ‖w‖ := by
    have hy2η : y ≤ 2 * ηc := by linarith
    have hsmall : K2 * ((a + y) - a) ≤ (mm / 2) / 2 := by
      have h1 : K2 * y ≤ K2 * (2 * ηc) := mul_le_mul_of_nonneg_left hy2η (le_of_lt hK2pos)
      have h2 : K2 * (2 * ηc) ≤ K2 * (2 * (mm / (8 * K2))) :=
        mul_le_mul_of_nonneg_left (by linarith [hηcm]) (le_of_lt hK2pos)
      have h3 : K2 * (2 * (mm / (8 * K2))) = mm / 4 := by
        field_simp
        ring
      linarith
    have h := nmf_norm_sub_ge_of_speed_ge (f := r') (f' := deriv r') (f'' := deriv (deriv r'))
      (mm := mm / 2) (K := K2) (a := a) (b := a + y) (by linarith) (by linarith)
      (fun x => hdr x) (fun x => hdr2 x) hspeed' hK2b hsmall
    have hrew : ((mm / 2) / 2) * ((a + y) - a) = (mm / 4) * y := by ring
    rw [hrew] at h
    rw [hwdef]
    exact h
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le (by positivity) hwlen
  have hwne : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hwpos)
  set ŵ : Space := ‖w‖⁻¹ • w with hŵdef
  have hŵnorm : ‖ŵ‖ = 1 := by
    rw [hŵdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwpos),
      inv_mul_cancel₀ (ne_of_gt hwpos)]
  set α : ℝ := inner ℝ w e / ‖w‖ with hαdef
  set n : Space := e - α • ŵ with hndef
  have hwn : inner ℝ w n = 0 := by
    have h1 : inner ℝ w ŵ = ‖w‖ := by
      rw [hŵdef, inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have h3 : inner ℝ w (α • ŵ) = inner ℝ w e := by
      rw [inner_smul_right, h1, hαdef, div_mul_cancel₀ _ (ne_of_gt hwpos)]
    rw [hndef, inner_sub_right, h3, sub_self]
  have hnsube : n - e = -(α • ŵ) := by rw [hndef]; abel
  have hnedist : ‖n - e‖ = |α| := by
    rw [hnsube, norm_neg, norm_smul, Real.norm_eq_abs, hŵnorm, mul_one]
  have hαbound : |α| ≤ 4 * K2 * ηc / mm := by
    rw [hαdef, abs_div, abs_of_nonneg (norm_nonneg w)]
    calc |inner ℝ w e| / ‖w‖ ≤ (K2 * ηc * y) / ((mm / 4) * y) :=
          div_le_div₀ (by positivity) hwbound (by positivity) hwlen
      _ = 4 * K2 * ηc / mm := by
          field_simp
  -- the concave functional
  have hHderiv : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => inner ℝ (r' t - r' a) n)
      (inner ℝ (deriv r' θ) n) θ := by
    intro θ
    have h := HasDerivAt.inner ℝ ((hdr θ).sub_const (r' a)) (hasDerivAt_const θ n)
    simpa [inner_zero_right, zero_add] using h
  have hHderiv_eq : deriv (fun t : ℝ => inner ℝ (r' t - r' a) n)
      = fun θ => inner ℝ (deriv r' θ) n := funext fun θ => (hHderiv θ).deriv
  have hHderiv2 : ∀ θ : ℝ, HasDerivAt (deriv (fun t : ℝ => inner ℝ (r' t - r' a) n))
      (inner ℝ (deriv (deriv r') θ) n) θ := by
    intro θ
    have h := HasDerivAt.inner ℝ (hdr2 θ) (hasDerivAt_const θ n)
    rw [hHderiv_eq]
    simpa [inner_zero_right, zero_add] using h
  have hHHa : (fun t : ℝ => inner ℝ (r' t - r' a) n) a = 0 := by
    simp [inner_zero_left]
  have hH2 : ∀ θ : ℝ, |θ - t₀| ≤ ηc →
      deriv (deriv (fun t : ℝ => inner ℝ (r' t - r' a) n)) θ ≤ -(c1 / 4) := by
    intro θ hθ
    have h1 : deriv (deriv (fun t : ℝ => inner ℝ (r' t - r' a) n)) θ
        = inner ℝ (deriv (deriv r') θ) n := (hHderiv2 θ).deriv
    rw [h1]
    have h2 : inner ℝ (deriv (deriv r') θ) n
        ≤ inner ℝ (deriv (deriv r') θ) e + ‖deriv (deriv r') θ‖ * ‖n - e‖ := by
      have hsplit : inner ℝ (deriv (deriv r') θ) n
          = inner ℝ (deriv (deriv r') θ) e + inner ℝ (deriv (deriv r') θ) (n - e) := by
        rw [← inner_add_right]
        congr 1
        abel
      rw [hsplit]
      have h3 : inner ℝ (deriv (deriv r') θ) (n - e) ≤ ‖deriv (deriv r') θ‖ * ‖n - e‖ :=
        le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
      linarith
    have h6 : ‖deriv (deriv r') θ‖ * ‖n - e‖ ≤ K2 * (4 * K2 * ηc / mm) := by
      rw [hnedist]
      exact mul_le_mul (hK2b θ) hαbound (abs_nonneg _) (le_of_lt hK2pos)
    have h7 : K2 * (4 * K2 * ηc / mm) ≤ c1 / 4 := by
      have key : 16 * K2 ^ 2 * ηc ≤ c1 * mm := by
        have h8 : K2 ^ 2 * ηc ≤ K2 ^ 2 * (c1 * mm / (16 * K2 ^ 2)) :=
          mul_le_mul_of_nonneg_left hηcc (by positivity)
        have h9 : K2 ^ 2 * (c1 * mm / (16 * K2 ^ 2)) = c1 * mm / 16 := by
          field_simp
        rw [h9] at h8
        linarith
      have hgoal : K2 * (4 * K2 * ηc / mm) = 4 * K2 ^ 2 * ηc / mm := by ring
      rw [hgoal, div_le_iff₀ hmm]
      rw [show c1 / 4 * mm = c1 * mm / 4 by ring]
      linarith
    linarith [hprop θ hθ, h2, h6]
  have hHpos : ∀ x ∈ Set.Ioo a (a + y), 0 < (fun t : ℝ => inner ℝ (r' t - r' a) n) x :=
    nmf_pos_of_secondDeriv_neg (by linarith) (by linarith)
      ((hr'cont.sub continuous_const).continuousOn.inner continuousOn_const)
      (DifferentiableOn.inner ℝ
        (fun t ht => ((hdr t).sub_const (r' a)).differentiableAt.differentiableWithinAt)
        (differentiableOn_const n))
      (by
        rw [hHderiv_eq]
        exact (hc1r.inner continuous_const).continuousOn)
      (by
        rw [hHderiv_eq]
        exact DifferentiableOn.inner ℝ
          (fun t ht => (hdr2 t).differentiableAt.differentiableWithinAt)
          (differentiableOn_const n))
      (fun x hx => hH2 x (by
        rw [abs_le]
        exact ⟨by linarith [hx.1, ha1], by linarith [hx.2.le, hay2]⟩))
      hHHa
      (by rw [← hwdef]; exact hwn)
  -- no middle
  intro hmem
  rw [openSegment_eq_image'] at hmem
  obtain ⟨θ, hθ, hθeq⟩ := hmem
  have hθw : r' u - r' a = θ • w := by
    have h : r' a + θ • w = r' u := by
      rw [hwdef]
      exact hθeq
    rw [← h]
    abel
  have hHu : (fun t : ℝ => inner ℝ (r' t - r' a) n) u = 0 := by
    show inner ℝ (r' u - r' a) n = 0
    rw [hθw, inner_smul_left, hwn, mul_zero]
  have hθ0 : θ ≠ 0 := ne_of_gt hθ.1
  have hθ1 : θ - 1 ≠ 0 := by linarith [hθ.2]
  have hult : a < u := by
    rcases lt_or_eq_of_le hau with h | h
    · exact h
    · exfalso
      have h0 : r' u - r' a = 0 := by rw [h]; abel
      rw [hθw] at h0
      rcases smul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 hθ0
      · exact hwne h1
  have hugt : u < a + y := by
    rcases lt_or_eq_of_le hua with h | h
    · exact h
    · exfalso
      have h0 : r' u - r' (a + y) = (θ - 1) • w := by
        rw [show r' u - r' (a + y) = (r' u - r' a) - (r' (a + y) - r' a) by abel, hθw, ← hwdef]
        module
      rw [h] at h0
      rw [sub_self, eq_comm] at h0
      rcases smul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 hθ1
      · exact hwne h1
  exact absurd (hHpos u ⟨hult, hugt⟩) (by rw [hHu]; exact lt_irrefl 0)

end Work.Drive
