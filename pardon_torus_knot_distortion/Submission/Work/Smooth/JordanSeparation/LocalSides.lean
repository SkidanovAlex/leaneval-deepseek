import Submission.Work.Smooth.JordanSeparation.LocalFrame

/-!
# The two local sides of a simple closed curve at a regular point

At a point `γ 0` where the curve is regular (`deriv c.γ 0 ≠ 0`) the curve is locally a graph over
its tangent line, so a small neighbourhood of `γ 0` is split by the curve into exactly two pieces.
This file proves the form of that statement used by the separation theorem:

* `exists_locS_strictMono` — the tangential coordinate `locS` is strictly increasing near `0`;
* `exists_no_reentry` — away from a fixed local radius, curve points at distance `≤ ε₁` from the
  local arc have parameters close to it again (a compactness statement);
* `locPhi_injOn` — the local parametrisation `(t,u) ↦ γ t + u·locN` is injective on a rectangle;
* `local_sides` — the local two-sidedness: an open neighbourhood `U` of `γ 0` and two non-empty
  preconnected sets `P`, `M` off the trace with `U \ trace ⊆ P ∪ M`.
-/

open Set Metric Filter
open scoped Topology
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- The tangential coordinate of the curve is **strictly increasing** near a regular parameter. -/
theorem exists_locS_strictMono (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ StrictMonoOn (locS c) (Icc (-r) r) := by
  have ha : 0 < deriv (locS c) 0 := by
    rw [deriv_locS_zero c hreg]
    exact norm_pos_iff.mpr hreg
  have hcont : Continuous (deriv (locS c)) := continuous_deriv_locS c
  obtain ⟨r, hr, hpos⟩ : ∃ r > 0, ∀ t, |t| < r → 0 < deriv (locS c) t := by
    have hopen : IsOpen {t : ℝ | 0 < deriv (locS c) t} := isOpen_lt continuous_const hcont
    obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp hopen 0 ha
    exact ⟨e, he, fun t ht => hball (by rwa [Metric.mem_ball, Real.dist_eq, sub_zero])⟩
  refine ⟨r, hr, strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_locS c).continuousOn ?_⟩
  intro z hz
  rw [interior_Icc, Set.mem_Ioo] at hz
  exact hpos z (abs_lt.mpr ⟨hz.1, hz.2⟩)

/-- **No re-entry, uniformly.**  For a simple closed curve there is `ε₁ > 0` such that a curve
point whose parameter stays a fixed distance `r₁` away from `t` modulo the period is at distance at
least `ε₁` from `γ t`, uniformly for `t` in a compact range. -/
theorem exists_no_reentry (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    {δ r₁ : ℝ} (hr₁ : 0 < r₁) (hr₁π : r₁ + δ < 2 * Real.pi) :
    ∃ ε₁ > 0, ∀ t : ℝ, |t| ≤ δ → ∀ t₁ : ℝ,
      (∀ k : ℤ, r₁ ≤ |t₁ - t - (k : ℝ) * (2 * Real.pi)|) → ε₁ ≤ ‖c.γ t₁ - c.γ t‖ := by
  classical
  have hbox : IsCompact (Icc (-δ) δ ×ˢ Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  have hcl₁ : IsClosed {p : ℝ × ℝ | r₁ ≤ |p.2 - p.1|} :=
    isClosed_le continuous_const (continuous_snd.sub continuous_fst).abs
  have hcl₂ : IsClosed {p : ℝ × ℝ | r₁ ≤ |p.2 - p.1 - 2 * Real.pi|} :=
    isClosed_le continuous_const (((continuous_snd.sub continuous_fst).sub continuous_const).abs)
  have hcl₃ : IsClosed {p : ℝ × ℝ | r₁ ≤ |p.2 - p.1 + 2 * Real.pi|} :=
    isClosed_le continuous_const (((continuous_snd.sub continuous_fst).add continuous_const).abs)
  set E : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ∈ Icc (-δ) δ ∧ p.2 ∈ Icc (0:ℝ) (2 * Real.pi) ∧
      r₁ ≤ |p.2 - p.1| ∧ r₁ ≤ |p.2 - p.1 - 2 * Real.pi| ∧
      r₁ ≤ |p.2 - p.1 + 2 * Real.pi|} with hEdef
  have hEeq : E = ((Icc (-δ) δ ×ˢ Icc (0:ℝ) (2 * Real.pi))
      ∩ {p : ℝ × ℝ | r₁ ≤ |p.2 - p.1|}) ∩ {p : ℝ × ℝ | r₁ ≤ |p.2 - p.1 - 2 * Real.pi|}
      ∩ {p : ℝ × ℝ | r₁ ≤ |p.2 - p.1 + 2 * Real.pi|} := by
    ext p; simp only [hEdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc]
    tauto
  have hEcomp : IsCompact E := by
    rw [hEeq]
    exact ((hbox.inter_right hcl₁).inter_right hcl₂).inter_right hcl₃
  have hpos : ∀ p ∈ E, 0 < ‖c.γ p.2 - c.γ p.1‖ := by
    intro p hp
    obtain ⟨hp1, hp2, h₁, h₂, h₃⟩ : p.1 ∈ Icc (-δ) δ ∧ p.2 ∈ Icc (0:ℝ) (2 * Real.pi) ∧
        r₁ ≤ |p.2 - p.1| ∧ r₁ ≤ |p.2 - p.1 - 2 * Real.pi| ∧
        r₁ ≤ |p.2 - p.1 + 2 * Real.pi| := hp
    rw [norm_pos_iff, sub_ne_zero]
    intro hγ
    obtain ⟨k, hk⟩ := PlaneCurve.IsSimple.eq_mod_period hs hγ
    have h_abs : |(k : ℝ) * (2 * Real.pi)| = |p.2 - p.1| := by
      rw [show (k:ℝ) * (2*Real.pi) = -(p.2 - p.1) from by linarith [hk], abs_neg]
    have hle : |(k : ℝ)| * (2 * Real.pi) ≤ 2 * Real.pi + δ := by
      calc |(k : ℝ)| * (2 * Real.pi) = |(k : ℝ) * (2 * Real.pi)| := by
            rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
        _ = |p.2 - p.1| := h_abs
        _ ≤ |p.2| + |p.1| := abs_sub _ _
        _ ≤ 2 * Real.pi + δ := by
            rw [abs_of_nonneg hp2.1]
            linarith [hp2.2, abs_le.mpr ⟨hp1.1, hp1.2⟩]
    have hk2 : |(k : ℝ)| < 2 := by nlinarith [Real.pi_pos, hle, hr₁π]
    have hkR : -(2:ℝ) < (k:ℝ) ∧ (k:ℝ) < 2 := abs_lt.mp hk2
    have hkZ : k = -1 ∨ k = 0 ∨ k = 1 := by
      have h1 : (-(2:ℤ) : ℤ) < k := by exact_mod_cast hkR.1
      have h2 : k < (2:ℤ) := by exact_mod_cast hkR.2
      omega
    rcases hkZ with h | h | h
    · rw [h] at hk
      simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] at hk
      rw [hk] at h₂
      rw [show p.2 - (p.2 + -(2 * Real.pi)) - 2 * Real.pi = 0 from by ring, abs_zero] at h₂
      linarith
    · rw [h] at hk
      simp only [Int.cast_zero, zero_mul, add_zero] at hk
      rw [hk] at h₁
      rw [show p.2 - p.2 = 0 from by ring, abs_zero] at h₁
      linarith
    · rw [h] at hk
      simp only [Int.cast_one, one_mul] at hk
      rw [hk] at h₃
      rw [show p.2 - (p.2 + 2 * Real.pi) + 2 * Real.pi = 0 from by ring, abs_zero] at h₃
      linarith
  have hred : ∀ t t₁ : ℝ, |t| ≤ δ →
      (∀ k : ℤ, r₁ ≤ |t₁ - t - (k : ℝ) * (2 * Real.pi)|) →
      ((t, t₁ - ((⌊t₁ / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi)) ∈ E) := by
    intro t t₁ ht hfar
    set m : ℤ := ⌊t₁ / (2 * Real.pi)⌋ with hm
    have hpos2 : (0 : ℝ) < 2 * Real.pi := by positivity
    have hm₁ : 0 ≤ t₁ - (m : ℝ) * (2 * Real.pi) := by
      have := (le_div_iff₀ hpos2).mp (Int.floor_le (t₁ / (2 * Real.pi))); linarith
    have hm₂ : t₁ - (m : ℝ) * (2 * Real.pi) < 2 * Real.pi := by
      have := (div_lt_iff₀ hpos2).mp (Int.lt_floor_add_one (t₁ / (2 * Real.pi))); linarith
    have h₁ : r₁ ≤ |t₁ - (m : ℝ) * (2 * Real.pi) - t| := by
      have := hfar m
      rwa [show t₁ - t - (m : ℝ) * (2 * Real.pi) = t₁ - (m : ℝ) * (2 * Real.pi) - t
        from by ring] at this
    have h₂ : r₁ ≤ |t₁ - (m : ℝ) * (2 * Real.pi) - t - 2 * Real.pi| := by
      have := hfar (m + 1)
      rwa [show t₁ - t - (↑(m + 1) : ℝ) * (2 * Real.pi)
        = t₁ - (m : ℝ) * (2 * Real.pi) - t - 2 * Real.pi from by push_cast; ring] at this
    have h₃ : r₁ ≤ |t₁ - (m : ℝ) * (2 * Real.pi) - t + 2 * Real.pi| := by
      have := hfar (m - 1)
      rwa [show t₁ - t - (↑(m - 1) : ℝ) * (2 * Real.pi)
        = t₁ - (m : ℝ) * (2 * Real.pi) - t + 2 * Real.pi from by push_cast; ring] at this
    exact ⟨abs_le.mp ht, ⟨hm₁, le_of_lt hm₂⟩, h₁, h₂, h₃⟩
  rcases E.eq_empty_or_nonempty with hE | hE
  · refine ⟨1, one_pos, fun t ht t₁ hfar => ?_⟩
    have h' := hred t t₁ ht hfar
    rw [hE] at h'
    exact absurd h' (Set.notMem_empty _)
  · obtain ⟨p₀, hp₀, hmin⟩ := hEcomp.exists_isMinOn hE
      ((continuous_norm.comp (c.cont.comp continuous_snd |>.sub
        (c.cont.comp continuous_fst))).continuousOn)
    refine ⟨‖c.γ p₀.2 - c.γ p₀.1‖, hpos p₀ hp₀, fun t ht t₁ hfar => ?_⟩
    have hmem := hred t t₁ ht hfar
    have hper : c.γ (t₁ - ((⌊t₁ / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi)) = c.γ t₁ := by
      have := c.apply_add_int_mul (t₁ - ((⌊t₁ / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi))
        ⌊t₁ / (2 * Real.pi)⌋
      rw [show t₁ - ((⌊t₁ / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi)
          + ((⌊t₁ / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) = t₁ from by ring] at this
      exact this.symm
    rw [← hper]
    exact hmin hmem

/-- The local parametrisation is **injective** on a rectangle on which the tangential coordinate is
strictly monotone. -/
theorem locPhi_injOn (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0) {r ε : ℝ}
    (hmono : StrictMonoOn (locS c) (Icc (-r) r)) :
    Set.InjOn (locPhi c) (Ioo (-r) r ×ˢ Ioo (-ε) ε) := by
  rintro ⟨t, u⟩ hp ⟨t', u'⟩ hq hpq
  have hsub : Ioo (-r) r ⊆ Icc (-r) r := Ioo_subset_Icc_self
  have h₁ : locS c t = locS c t' := by
    have h := congrArg (locX c) hpq
    rwa [locX_phi c hreg (t, u), locX_phi c hreg (t', u')] at h
  have htt : t = t' := by
    rcases lt_trichotomy t t' with hlt | heq | hgt
    · exact absurd h₁ (ne_of_lt (hmono (hsub hp.1) (hsub hq.1) hlt))
    · exact heq
    · exact absurd h₁.symm (ne_of_lt (hmono (hsub hq.1) (hsub hp.1) hgt))
  subst htt
  have h₂ : locR c t + u = locR c t + u' := by
    have h := congrArg (locY c) hpq
    rw [locY_phi c hreg (t, u), locY_phi c hreg (t, u')] at h
    linarith
  exact Prod.ext rfl (by linarith)

/-- **The two local sides of the curve at a regular point.**

For a simple `C¹` closed curve regular at the parameter `0` there is an open neighbourhood `U` of
`γ 0` and two non-empty preconnected sets `P`, `M` off the trace such that every point of `U` off
the trace lies in `P` or in `M`.  In the separation theorem `P` and `M` are the two local sides of
the curve at `γ 0`, and they lie in two *different* components of the complement because the index
jumps by one across the curve there. -/
theorem local_sides (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    (hreg : deriv c.γ 0 ≠ 0) :
    ∃ U P M : Set ℂ, IsOpen U ∧ c.γ 0 ∈ U ∧ IsPreconnected P ∧ IsPreconnected M ∧
      P.Nonempty ∧ M.Nonempty ∧ P ⊆ c.traceᶜ ∧ M ⊆ c.traceᶜ ∧ (U \ c.trace) ⊆ P ∪ M := by
  obtain ⟨r, hr, hmono⟩ := exists_locS_strictMono c hreg
  -- shrink the monotonicity radius so that it is small compared with `π`
  set R : ℝ := min r (Real.pi / 4) with hRdef
  have hRpos : 0 < R := lt_min hr (by positivity)
  have hRle : R ≤ r := min_le_left _ _
  have hRπ : R < Real.pi := lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
  have hR4 : 4 * R ≤ Real.pi := by
    have h := min_le_right r (Real.pi / 4); rw [← hRdef] at h; linarith
  have hmonoR : StrictMonoOn (locS c) (Icc (-R) R) :=
    hmono.mono (fun x hx => ⟨by linarith [hRle, hx.1], by linarith [hRle, hx.2]⟩)
  -- the rectangle half-width and the no-reentry radius
  set δ : ℝ := R / 4 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδR : δ ≤ R := by rw [hδdef]; linarith
  obtain ⟨ε₁, hε₁pos, hnoReentry⟩ := exists_no_reentry c hs (δ := δ) (r₁ := δ)
    hδpos (by linarith [hδpos, hR4])
  -- a bound for the normal coordinate of the curve on the rectangle
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ t : ℝ, |t| ≤ δ₁ → |locR c t| ≤ ε₁ / 8 := by
    have hcont : ContinuousAt (locR c) 0 := (continuous_locR c).continuousAt
    have h0 : locR c 0 = 0 := locR_zero c
    have hev : ∀ᶠ t in 𝓝 (0:ℝ), |locR c t| < ε₁ / 8 := by
      have hball := hcont.eventually
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by positivity : (0:ℝ) < ε₁ / 8)))
      filter_upwards [hball] with t ht
      rwa [h0, Real.dist_eq, sub_zero] at ht
    obtain ⟨δ₁, hδ₁pos, hsub⟩ := Metric.mem_nhds_iff.mp hev
    exact ⟨δ₁ / 2, by linarith, fun t ht => le_of_lt (hsub (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith [ht]))⟩
  set μ : ℝ := min δ δ₁ with hμdef
  have hμpos : 0 < μ := lt_min hδpos hδ₁pos
  have hμδ : μ ≤ δ := min_le_left _ _
  have hμδ₁ : μ ≤ δ₁ := min_le_right _ _
  set ε : ℝ := ε₁ / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεlt : ε < ε₁ := by rw [hεdef]; linarith
  set ρ' : ℝ := ε₁ / 8 with hρ'def
  have hρ'pos : 0 < ρ' := by rw [hρ'def]; linarith
  -- the two local sides
  set P : Set ℂ := locPhi c '' (Ioo (-μ) μ ×ˢ Ioo (0:ℝ) ε) with hPdef
  set M : Set ℂ := locPhi c '' (Ioo (-μ) μ ×ˢ Ioo (-ε) (0:ℝ)) with hMdef
  have hcontPhi : Continuous (locPhi c) := continuous_locPhi c
  have hprec : ∀ s : Set (ℝ × ℝ), IsPreconnected s → IsPreconnected (locPhi c '' s) :=
    fun s hs' => hs'.image _ hcontPhi.continuousOn
  have hPpre : IsPreconnected P := by
    rw [hPdef]; exact hprec _ (isPreconnected_Ioo.prod isPreconnected_Ioo)
  have hMpre : IsPreconnected M := by
    rw [hMdef]; exact hprec _ (isPreconnected_Ioo.prod isPreconnected_Ioo)
  have hPne : P.Nonempty := by
    refine ⟨locPhi c (0, ε / 2), ?_⟩
    rw [hPdef]
    exact ⟨(0, ε / 2), ⟨⟨by linarith [hμpos], by linarith [hμpos]⟩,
      ⟨by linarith [hεpos], by linarith [hεpos]⟩⟩, rfl⟩
  have hMne : M.Nonempty := by
    refine ⟨locPhi c (0, -(ε / 2)), ?_⟩
    rw [hMdef]
    exact ⟨(0, -(ε / 2)), ⟨⟨by linarith [hμpos], by linarith [hμpos]⟩,
      ⟨by linarith [hεpos], by linarith [hεpos]⟩⟩, rfl⟩
  have hinj : Set.InjOn (locPhi c) (Ioo (-R) R ×ˢ Ioo (-ε) ε) := locPhi_injOn c hreg hmonoR
  have hN : ‖locN c‖ = 1 := by
    rw [locN, norm_mul, Complex.norm_I, one_mul]; exact norm_locE c hreg
  -- the two sides miss the trace: a curve point at distance `< ε₁` from `γ t` has its parameter
  -- within `δ` of `t` modulo the period, and then injectivity of the local parametrisation applies
  have key : ∀ (t u t₁ : ℝ), |t| < μ → |u| < ε → u ≠ 0 →
      c.γ t₁ = c.γ t + (u : ℂ) * locN c → False := by
    intro t u t₁ htμ hu hu0 hγ
    have hnorm : ‖c.γ t₁ - c.γ t‖ = |u| := by
      rw [hγ]
      have : c.γ t + (u : ℂ) * locN c - c.γ t = (u : ℂ) * locN c := by ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, hN, mul_one]
    have hex : ∃ k : ℤ, |t₁ - t - (k : ℝ) * (2 * Real.pi)| < δ := by
      by_contra hcon
      have hfar : ∀ k : ℤ, δ ≤ |t₁ - t - (k : ℝ) * (2 * Real.pi)| := fun k =>
        not_lt.mp (fun hlt => hcon ⟨k, hlt⟩)
      have htabs : |t| ≤ δ := by
        rw [abs_le]
        exact ⟨by linarith [(abs_lt.mp htμ).1, hμδ], by linarith [(abs_lt.mp htμ).2, hμδ]⟩
      have h := hnoReentry t htabs t₁ hfar
      rw [hnorm] at h
      linarith
    obtain ⟨k, hk⟩ := hex
    set t₁' : ℝ := t₁ - (k : ℝ) * (2 * Real.pi) with ht₁'def
    have hsum : t₁' + (k : ℝ) * (2 * Real.pi) = t₁ := by linarith [ht₁'def]
    have hper : c.γ t₁' = c.γ t₁ := by
      have h := c.apply_add_int_mul t₁' k
      rw [hsum] at h
      exact h.symm
    have hmain : |t₁ - (k : ℝ) * (2 * Real.pi)| < R := by
      have h1 : t₁ - (k : ℝ) * (2 * Real.pi) = (t₁ - t - (k : ℝ) * (2 * Real.pi)) + t := by ring
      calc |t₁ - (k : ℝ) * (2 * Real.pi)|
          = |(t₁ - t - (k : ℝ) * (2 * Real.pi)) + t| := congrArg abs h1
        _ ≤ |t₁ - t - (k : ℝ) * (2 * Real.pi)| + |t| := abs_add_le _ _
        _ < δ + μ := by linarith [hk, htμ]
        _ ≤ R := by rw [hδdef]; linarith
    have ht₁'R : |t₁'| < R := by rw [ht₁'def]; exact hmain
    have hphi : locPhi c (t₁', 0) = locPhi c (t, u) := by
      show c.γ t₁' + ((0:ℝ) : ℂ) * locN c = c.γ t + (u : ℂ) * locN c
      rw [hper, hγ]
      simp
    have hmem1 : (t, u) ∈ Ioo (-R) R ×ˢ Ioo (-ε) ε :=
      ⟨abs_lt.mp (lt_of_lt_of_le htμ (by linarith [hμδ, hδR])), abs_lt.mp hu⟩
    have hmem2 : (t₁', 0) ∈ Ioo (-R) R ×ˢ Ioo (-ε) ε :=
      ⟨abs_lt.mp ht₁'R, ⟨by linarith [hεpos], by linarith [hεpos]⟩⟩
    have hEq := hinj hmem1 hmem2 hphi.symm
    exact hu0 (by simpa using congrArg Prod.snd hEq)
  have hPoff : P ⊆ c.traceᶜ := by
    rintro z hz
    obtain ⟨⟨t, u⟩, ⟨⟨ht1, ht2⟩, hu1, hu2⟩, heq⟩ := hz
    rw [← heq]
    simp only [Set.mem_compl_iff]
    intro hmem
    obtain ⟨t₁, ht₁⟩ := (PlaneCurve.mem_trace_iff c.toPlaneCurve
      (c.γ t + (u : ℂ) * locN c)).mpr hmem
    exact key t u t₁ (abs_lt.mpr ⟨ht1, ht2⟩) (abs_lt.mpr ⟨by linarith [hu1], hu2⟩)
      (ne_of_gt hu1) ht₁
  have hMoff : M ⊆ c.traceᶜ := by
    rintro z hz
    obtain ⟨⟨t, u⟩, ⟨⟨ht1, ht2⟩, hu1, hu2⟩, heq⟩ := hz
    rw [← heq]
    simp only [Set.mem_compl_iff]
    intro hmem
    obtain ⟨t₁, ht₁⟩ := (PlaneCurve.mem_trace_iff c.toPlaneCurve
      (c.γ t + (u : ℂ) * locN c)).mpr hmem
    exact key t u t₁ (abs_lt.mpr ⟨ht1, ht2⟩) (abs_lt.mpr ⟨hu1, by linarith [hu2, hεpos]⟩)
      (ne_of_lt hu2) ht₁
  -- the neighbourhood
  set ρ : ℝ := min (locS c μ) (-(locS c (-μ))) with hρdef
  have hρpos : 0 < ρ := by
    have h1 : locS c 0 < locS c μ :=
      hmonoR ⟨by linarith [hRpos], le_of_lt hRpos⟩ ⟨by linarith [hμpos, hμδ, hδR, hRpos], by linarith [hμpos, hμδ, hδR, hRpos]⟩ (by linarith [hμpos])
    have h2 : locS c (-μ) < locS c 0 :=
      hmonoR ⟨by linarith [hμpos, hμδ, hδR, hRpos], by linarith [hμpos, hμδ, hδR, hRpos]⟩ ⟨by linarith [hRpos], le_of_lt hRpos⟩ (by linarith [hμpos])
    rw [hρdef]
    simp only [locS_zero] at h1 h2
    exact lt_min h1 (by linarith)
  set U : Set ℂ := {z : ℂ | |locX c z| < ρ ∧ |locY c z| < ρ'} with hUdef
  have hUopen : IsOpen U := by
    have h1 : IsOpen {z : ℂ | |locX c z| < ρ} := by
      rw [show {z : ℂ | |locX c z| < ρ} = locX c ⁻¹' Ioo (-ρ) ρ by
        ext z; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioo, abs_lt]]
      exact isOpen_Ioo.preimage (continuous_locX c)
    have h2 : IsOpen {z : ℂ | |locY c z| < ρ'} := by
      rw [show {z : ℂ | |locY c z| < ρ'} = locY c ⁻¹' Ioo (-ρ') ρ' by
        ext z; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioo, abs_lt]]
      exact isOpen_Ioo.preimage (continuous_locY c)
    rw [hUdef]
    exact h1.inter h2
  have hpU : c.γ 0 ∈ U := by
    rw [hUdef]
    simp only [Set.mem_setOf_eq, locX_self, locY_self, abs_zero]
    exact ⟨hρpos, hρ'pos⟩
  -- the covering of `U` off the trace by the two sides
  have hcover : (U \ c.trace) ⊆ P ∪ M := by
    rintro z ⟨hzU, hzK⟩
    rw [hUdef] at hzU
    obtain ⟨hx, hy⟩ := hzU
    have hxle : ρ ≤ locS c μ := by rw [hρdef]; exact min_le_left _ _
    have hxle' : ρ ≤ -(locS c (-μ)) := by rw [hρdef]; exact min_le_right _ _
    have hxmem : locX c z ∈ Icc (locS c (-μ)) (locS c μ) :=
      ⟨by linarith [(abs_lt.mp hx).1, hxle'], by linarith [(abs_lt.mp hx).2, hxle]⟩
    have hIVT := intermediate_value_Icc (show -μ ≤ μ by linarith [hμpos])
      (continuous_locS c).continuousOn hxmem
    obtain ⟨t, ht, htval⟩ := hIVT
    have htne : t ≠ μ := by
      intro h
      have h1 : locS c μ = locX c z := by rw [← h]; exact htval
      rw [← h1] at hx
      linarith [(abs_lt.mp hx).2, hxle]
    have htne' : t ≠ -μ := by
      intro h
      have h1 : locS c (-μ) = locX c z := by rw [← h]; exact htval
      rw [← h1] at hx
      linarith [(abs_lt.mp hx).1, hxle']
    have htIoo : t ∈ Ioo (-μ) μ := ⟨lt_of_le_of_ne ht.1 (Ne.symm htne'), lt_of_le_of_ne ht.2 htne⟩
    have hrt : |locR c t| ≤ ε₁ / 8 := hδ₁ t (by
      rw [abs_le]; exact ⟨by linarith [ht.1, hμδ₁], by linarith [ht.2, hμδ₁]⟩)
    set u : ℝ := locY c z - locR c t with hudef
    have hull : |u| < ε := by
      have h1 : |u| ≤ |locY c z| + |locR c t| := by
        rw [hudef]; exact abs_sub _ _
      rw [hεdef]
      linarith [h1, hy, hrt]
    have hrec1 : z = c.γ 0 + (locX c z : ℂ) * locE c + (locY c z : ℂ) * locN c :=
      loc_reconstruction c hreg z
    have hrec2 : c.γ t = c.γ 0 + (locS c t : ℂ) * locE c + (locR c t : ℂ) * locN c := by
      have h := loc_reconstruction c hreg (c.γ t)
      simpa only [locS, locR] using h
    have hPhi : z = locPhi c (t, u) := by
      rw [hrec1, ← htval, hudef, locPhi, hrec2]
      push_cast
      ring
    have hune : u ≠ 0 := by
      intro h0
      apply hzK
      rw [hPhi]
      have h1 : locPhi c (t, 0) = c.γ t := by rw [locPhi]; simp
      rw [h0, h1]
      exact PlaneCurve.mem_trace c.toPlaneCurve t
    have huIoo : u ∈ Ioo (-ε) ε := abs_lt.mp hull
    rcases lt_or_gt_of_ne hune with hneg | hpos
    · right
      rw [hMdef]
      exact ⟨(t, u), ⟨htIoo, ⟨huIoo.1, by rw [hudef]; exact hneg⟩⟩, hPhi.symm⟩
    · left
      rw [hPdef]
      exact ⟨(t, u), ⟨htIoo, ⟨hpos, huIoo.2⟩⟩, hPhi.symm⟩
  exact ⟨U, P, M, hUopen, hpU, hPpre, hMpre, hPne, hMne, hPoff, hMoff, hcover⟩

end

end Work.Smooth.JordanSeparation
