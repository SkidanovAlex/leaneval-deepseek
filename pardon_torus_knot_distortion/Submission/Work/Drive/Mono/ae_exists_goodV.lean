import Mathlib
import Submission.Work.Drive.Mono.ae_noCritValue_near

/-!
# Good tilt directions exist for almost every cut level

`Work.Drive.Mono.ae_exists_goodV` is the "no grazing for a.e. level" input of the a.e. form of the
crux: for almost every level `u` of the cutting plane `⟪v, ·⟫ = ⟪v, c⟫ + u` there is a tilt
direction `v` (as close as we like to the standard direction `shiftVσ σ 1 = e_{σ 2}`) whose critical
values, over the part of the knot inside the box `PBox s c σ`, stay a positive distance `δ` away from
the level.

The statement as requested only asks for the *existence* of such a `v`, and `v = shiftVσ σ 1` itself
is a witness: the swept height is then the `σ 2`-coordinate of the curve, and the flat statement
`Work.Drive.Mono.ae_noCritValue_near` (positive distance of a.e. level from the flat critical values,
built from Sard in dimension one) applies verbatim.  That is `ae_exists_goodV` below.

The genuinely useful form -- and the one a proof that has *already committed* to a specific tilt
direction (e.g. the Morse-generic slab direction of the sweep, chosen close to `shiftVσ σ 1`) needs --
is `ae_exists_goodV_near`: for a.e. `u` there is `δ > 0` such that *every* unit `v` with
`‖v - shiftVσ σ 1‖ < δ` has all its critical values over the box at distance `≥ δ` from the level
(and `δ ≤ θ`).  It is proved here by a uniform transversality argument:

* `ae_noCritValue_near` gives `d > 0` with `d ≤ |f|` at every critical point of the flat height
  `f = (curve ·).(σ 2) - (c (σ 2) + u)`;
* `exists_deriv_lower_bound_of_periodic` (below, a one-dimensional compactness + periodicity lemma)
  upgrades this to `c > 0` with `c ≤ |deriv f|` on the whole set `{|f| ≤ d/2}`;
* a tilted critical point of a nearby direction `v` has `|deriv f| ≤ ‖v - e‖ · ‖K'‖ ≤ ‖v - e‖ M`,
  so it cannot be *near* the level; being *exactly* at the level it would be strictly nearer than
  `d/2`, hence is excluded for `‖v - e‖ M < c`.  This is the quantitative "no grazing" statement.

In particular the requested `ae_exists_goodV` follows from `ae_exists_goodV_near` by taking the witness
`v = shiftVσ σ 1` (`ae_exists_goodV_of_near`); the direct proof is also included, since it is the
statement that was asked for.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
/-- The unit vector `shiftVσ σ 1` evaluates test vectors at the coordinate `σ 2`: the functional
`⟪shiftVσ σ 1, ·⟫` is the `σ 2`-coordinate. -/
theorem inner_shiftVσ_one (σ : Equiv.Perm (Fin 3)) (x : R3) :
    inner ℝ (Work.BoxShrink.shiftVσ σ 1) x = x (σ 2) := by
  rw [PiLp.inner_apply]
  simp [Work.BoxShrink.shiftVσ_apply]

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology RealInnerProductSpace in
/-- **The derivative of the height in a fixed direction along a knot.**  For a smooth knot `K` and a
direction `v` this is `⟪v, K'(t)⟫`. -/
theorem deriv_inner_curve_const (K : Knot) (v : R3) (t : ℝ) :
    deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = inner ℝ v (deriv K.curve t) := by
  have h1 : (fun r : ℝ => inner ℝ v (K.curve r)) = fun r : ℝ => inner ℝ (K.curve r) v := by
    funext r; exact (real_inner_comm v (K.curve r)).symm
  rw [h1]
  rw [deriv_inner_apply ℝ (K.smooth.differentiable (by simp)).differentiableAt
    (differentiableAt_const v)]
  simp [real_inner_comm]

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology RealInnerProductSpace in
/-- The derivative of the knot is `2π`-periodic, like the knot itself. -/
theorem periodic_deriv_curve (K : Knot) : Function.Periodic (deriv K.curve) (2 * Real.pi) := by
  intro x
  rw [(deriv_comp_add_const K.curve (2 * Real.pi) x).symm]
  rw [funext K.periodic]

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology RealInnerProductSpace in
/-- **The speed of a knot is bounded.** -/
theorem exists_bound_deriv_curve (K : Knot) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, ‖deriv K.curve t‖ ≤ M := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hper : Function.Periodic (deriv K.curve) (2 * Real.pi) := periodic_deriv_curve K
  have hcont : Continuous (deriv K.curve) := K.smooth.continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max 1 C, le_trans zero_le_one (le_max_left _ _), fun t => ?_⟩
  obtain ⟨s, hs, hds⟩ := hper.exists_mem_Ico₀ hpi t
  rw [hds]
  exact le_trans (hC s (Ico_subset_Icc_self hs)) (le_max_right _ _)

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology RealInnerProductSpace in
/-- If a `C¹`, `2π`-periodic function `f : ℝ → ℝ` has all its critical values at distance at least
`d > 0` from `0`, then `|deriv f|` is bounded below by a positive constant on the set where
`|f| ≤ d/2`.  (Compactness on one period: the set `{|f| ≤ d/2}` contains no critical point.) -/
theorem exists_deriv_lower_bound_of_periodic {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : Function.Periodic f (2 * Real.pi)) {d : ℝ} (hd : 0 < d)
    (hcrit : ∀ t : ℝ, deriv f t = 0 → d ≤ |f t|) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, |f t| ≤ d / 2 → c ≤ |deriv f t| := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hperd : Function.Periodic (deriv f) (2 * Real.pi) := by
    intro x
    rw [(deriv_comp_add_const f (2 * Real.pi) x).symm]
    rw [funext hper]
  have hdcont : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hfc : Continuous f := hf.continuous
  -- reduce an arbitrary parameter to one period, keeping both `f` and `deriv f`
  have hred : ∀ t : ℝ, ∃ s ∈ Set.Ico (0 : ℝ) (2 * Real.pi),
      f t = f s ∧ deriv f t = deriv f s := by
    intro t
    set k : ℤ := ⌊t / (2 * Real.pi)⌋ with hk
    refine ⟨t - k • (2 * Real.pi), ?_, (hper.sub_zsmul_eq k).symm, (hperd.sub_zsmul_eq k).symm⟩
    constructor
    · rw [sub_nonneg, zsmul_eq_mul]
      rw [← le_div_iff₀ hpi]
      rw [hk]
      exact Int.floor_le _
    · rw [sub_lt_iff_lt_add, zsmul_eq_mul]
      have hh : t / (2 * Real.pi) < (k : ℝ) + 1 := by
        have h3 := Int.lt_floor_add_one (t / (2 * Real.pi))
        rwa [← hk] at h3
      rw [div_lt_iff₀ hpi] at hh
      linarith
  set A : Set ℝ := {t | |f t| ≤ d / 2} ∩ Set.Icc 0 (2 * Real.pi) with hA
  have hAc : IsCompact A :=
    IsCompact.of_isClosed_subset isCompact_Icc
      ((isClosed_le (continuous_abs.comp hfc) continuous_const).inter isClosed_Icc)
      Set.inter_subset_right
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · -- nothing is near the level: any positive constant works vacuously
    refine ⟨1, one_pos, fun t ht => ?_⟩
    obtain ⟨s, hs, hfs, _⟩ := hred t
    have hsA : s ∈ A := ⟨by show |f s| ≤ d / 2; rw [← hfs]; exact ht, Ico_subset_Icc_self hs⟩
    rw [hAe] at hsA
    exact absurd hsA (by simp)
  · obtain ⟨t₀, ht₀, hmin⟩ :=
      hAc.exists_isMinOn hAne ((continuous_abs.comp hdcont).continuousOn)
    have hd0 : deriv f t₀ ≠ 0 := by
      intro h0
      have h1 := hcrit t₀ h0
      have h2 : |f t₀| ≤ d / 2 := ht₀.1
      linarith
    refine ⟨|deriv f t₀|, abs_pos.mpr hd0, fun t ht => ?_⟩
    obtain ⟨s, hs, hfs, hds⟩ := hred t
    have hsA : s ∈ A := ⟨by show |f s| ≤ d / 2; rw [← hfs]; exact ht, Ico_subset_Icc_self hs⟩
    have h1 : |deriv f t₀| ≤ |deriv f s| := hmin hsA
    rw [← hds] at h1
    exact h1

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
theorem ae_exists_goodV (K : Knot) {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    {θ : ℝ} (hθ : 0 < θ) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∃ (v : R3) (δ : ℝ), ‖v‖ = 1 ∧ ‖v - Work.BoxShrink.shiftVσ σ 1‖ < θ ∧ 0 < δ ∧
        ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
          deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
          δ ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)| := by
  -- The fixed direction `shiftVσ σ 1` (the `σ 2`-coordinate axis) is itself an admissible tilt:
  -- its distance from itself is `0 < θ`.  For it the swept height is the `σ 2`-coordinate of the
  -- curve, whose critical values are a.e. bounded away from the level by
  -- `Work.Drive.Mono.ae_noCritValue_near`.
  filter_upwards [ae_noCritValue_near K c σ] with u hu
  obtain ⟨δ, hδ, hcrit⟩ := hu
  refine ⟨Work.BoxShrink.shiftVσ σ 1, δ, Work.Drive.EpsForm.norm_shiftVσ_one σ, ?_, hδ, ?_⟩
  · simpa using hθ
  · intro t _ hderiv
    have hflat : deriv (fun r : ℝ => (K.curve r) (σ 2)) t = 0 := by
      have hfun : (fun r : ℝ => inner ℝ (Work.BoxShrink.shiftVσ σ 1) (K.curve r))
          = fun r : ℝ => (K.curve r) (σ 2) := by
        funext r
        exact inner_shiftVσ_one σ (K.curve r)
      rw [← hfun]
      exact hderiv
    rw [inner_shiftVσ_one σ (K.curve t), inner_shiftVσ_one σ c]
    exact hcrit t hflat

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology RealInnerProductSpace in
/-- **The uniform form: for almost every level, every direction close enough to `shiftVσ σ 1` has its
critical values over the box bounded away from the level.**  Both the threshold on `‖v - e‖` and the
margin are the same number `δ ≤ θ`; for `δ` also a bound on `‖deriv K.curve‖` this is exactly the
quantitative no-grazing statement. -/
theorem ae_exists_goodV_near (K : Knot) {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    {θ : ℝ} (hθ : 0 < θ) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∃ (ε δ : ℝ), 0 < ε ∧ 0 < δ ∧ ε ≤ θ ∧ δ ≤ θ ∧
        ∀ v : R3, ‖v‖ = 1 → ‖v - Work.BoxShrink.shiftVσ σ 1‖ < ε →
          ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
            deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
            δ ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)| := by
  obtain ⟨M, hM0, hMb⟩ := exists_bound_deriv_curve K
  obtain ⟨R, hR0, hRbox⟩ := Work.Drive.EpsForm.boxBound s c σ
  filter_upwards [ae_noCritValue_near K c σ] with u hu
  obtain ⟨d, hd, hcrit⟩ := hu
  -- the flat height, shifted by the level `c (σ 2) + u`
  set L : ℝ := c (σ 2) + u with hL
  set f : ℝ → ℝ := fun t => (K.curve t) (σ 2) - L with hf
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f := by
    rw [hf]
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (K.curve t) (σ 2)) := by
      have := ContDiff.continuousLinearMap_comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (σ 2)) K.smooth
      simpa using this
    exact h1.sub contDiff_const
  have hf_per : Function.Periodic f (2 * Real.pi) := by
    intro x
    rw [hf]
    simp only
    rw [K.periodic x]
  have hf_crit : ∀ t : ℝ, deriv f t = 0 → d ≤ |f t| := by
    intro t ht
    have ht' : deriv (fun r : ℝ => (K.curve r) (σ 2)) t = 0 := by
      rw [hf, deriv_sub_const] at ht
      exact ht
    have h1 := hcrit t ht'
    simpa [hf, hL] using h1
  obtain ⟨cmin, hcmin0, hcmin⟩ :=
    exists_deriv_lower_bound_of_periodic hf_smooth hf_per hd hf_crit
  -- the sizes: `ε` below both `θ` and the two critical ratios, `δ` below `θ` and `d/4`
  set ε : ℝ := min θ (min (d / 4 / (R + 1)) (cmin / 2 / (M + 1))) with hεdef
  set δ : ℝ := min (d / 4) θ with hδdef
  have hε0 : 0 < ε := by
    rw [hεdef]
    exact lt_min_iff.mpr ⟨hθ, lt_min_iff.mpr
      ⟨div_pos (div_pos (by linarith) (by norm_num)) (by linarith),
       div_pos (div_pos (by linarith) (by norm_num)) (by linarith)⟩⟩
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact lt_min_iff.mpr ⟨by linarith, hθ⟩
  have hεθ : ε ≤ θ := by rw [hεdef]; exact min_le_left _ _
  have hδθ : δ ≤ θ := by rw [hδdef]; exact min_le_right _ _
  have hεR : ε * R ≤ d / 4 := by
    have h1 : ε ≤ d / 4 / (R + 1) := le_trans (min_le_right _ _) (min_le_left _ _)
    calc ε * R ≤ (d / 4 / (R + 1)) * R := mul_le_mul_of_nonneg_right h1 hR0
      _ ≤ d / 4 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0 : ℝ) < R + 1)]
          nlinarith
  have hεM : ε * M ≤ cmin / 2 := by
    have h1 : ε ≤ cmin / 2 / (M + 1) := le_trans (min_le_right _ _) (min_le_right _ _)
    calc ε * M ≤ (cmin / 2 / (M + 1)) * M := mul_le_mul_of_nonneg_right h1 hM0
      _ ≤ cmin / 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0 : ℝ) < M + 1)]
          nlinarith
  refine ⟨ε, δ, hε0, hδ0, hεθ, hδθ, ?_⟩
  intro v hv1 hve t htbox hderiv
  set e : R3 := Work.BoxShrink.shiftVσ σ 1 with he
  have hne : ‖v - e‖ < ε := by rw [he]; exact hve
  -- the level difference is the flat one plus the tilt correction
  have hev : ∀ x : R3, inner ℝ e x = x (σ 2) := by
    intro x
    rw [he]
    exact inner_shiftVσ_one σ x
  have hval : inner ℝ v (K.curve t) - (inner ℝ v c + u)
      = f t + inner ℝ (v - e) (K.curve t - c) := by
    simp only [inner_sub_left, inner_sub_right, hev, hf, hL]
    ring
  have hb : |inner ℝ (v - e) (K.curve t - c)| ≤ ε * R := by
    calc |inner ℝ (v - e) (K.curve t - c)| ≤ ‖v - e‖ * ‖K.curve t - c‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ε * R := mul_le_mul (le_of_lt hne) (hRbox _ htbox) (norm_nonneg _) (le_of_lt hε0)
  -- a tilted critical point is an almost-critical point of the flat height
  have hdkey : deriv f t = - inner ℝ (v - e) (deriv K.curve t) := by
    have hyth : inner ℝ v (deriv K.curve t) = 0 := by
      rw [← deriv_inner_curve_const K v t]
      exact hderiv
    have hde : deriv f t = inner ℝ e (deriv K.curve t) := by
      have hfe : (fun r : ℝ => inner ℝ e (K.curve r)) = fun r : ℝ => (K.curve r) (σ 2) := by
        funext r
        rw [he]
        exact inner_shiftVσ_one σ (K.curve r)
      rw [hf, deriv_sub_const, ← hfe, deriv_inner_curve_const K e t]
    rw [hde, inner_sub_left, hyth]
    ring
  rcases le_or_gt (|f t|) (d / 2) with hle | hgt
  · -- the tilted critical point is near the flat level: `|deriv f|` is bounded below there
    exfalso
    have h1 : cmin ≤ |deriv f t| := hcmin t hle
    have h2 : |deriv f t| ≤ ε * M := by
      rw [hdkey, abs_neg]
      calc |inner ℝ (v - e) (deriv K.curve t)| ≤ ‖v - e‖ * ‖deriv K.curve t‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ ε * M := mul_le_mul (le_of_lt hne) (hMb t) (norm_nonneg _) (le_of_lt hε0)
    linarith
  · -- the tilted critical point is far from the flat level, and the tilt moves the value little
    have hmargin : δ ≤ |f t + inner ℝ (v - e) (K.curve t - c)| := by
      have h1 : |f t| ≤ |f t + inner ℝ (v - e) (K.curve t - c)|
          + |inner ℝ (v - e) (K.curve t - c)| := by
        have := abs_add_le (f t + inner ℝ (v - e) (K.curve t - c))
          (-(inner ℝ (v - e) (K.curve t - c)))
        simpa using this
      have h2 : δ ≤ d / 4 := by rw [hδdef]; exact min_le_left _ _
      linarith
    rwa [hval]

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology RealInnerProductSpace in
/-- The uniform form `ae_exists_goodV_near` implies the requested `ae_exists_goodV`, with the witness
`v = shiftVσ σ 1` (any unit direction at distance `< ε` of it would do, in particular the fixed
direction itself). -/
theorem ae_exists_goodV_of_near (K : Knot) {s : ℝ} (hs : 0 < s) (c : R3)
    (σ : Equiv.Perm (Fin 3)) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∃ (v : R3) (δ : ℝ), ‖v‖ = 1 ∧ ‖v - Work.BoxShrink.shiftVσ σ 1‖ < θ ∧ 0 < δ ∧
        ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
          deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
          δ ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)| := by
  filter_upwards [ae_exists_goodV_near K hs c σ hθ] with u hu
  obtain ⟨ε, δ, hε0, hδ0, hεθ, hδθ, h⟩ := hu
  refine ⟨Work.BoxShrink.shiftVσ σ 1, δ, Work.Drive.EpsForm.norm_shiftVσ_one σ, ?_, hδ0, ?_⟩
  · simpa using hθ
  · intro t ht hderiv
    exact h (Work.BoxShrink.shiftVσ σ 1) (Work.Drive.EpsForm.norm_shiftVσ_one σ)
      (by simpa using hε0) t ht hderiv

end Work.Drive.Mono
