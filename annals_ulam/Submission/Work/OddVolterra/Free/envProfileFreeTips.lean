import Mathlib
import Submission.Work.OddVolterra.Free.envProfileFreeConcave

/-!
# The tip of a free-tip envelope curve

For a free-tip envelope curve `Work.OddCurve.Free.IsEnvelopeCurveFree h x y` the two tips are
`bY = lim_{s→0⁺} y s` and `bX = lim_{s→0⁺} x s`; they are *not* normalised to `1`.  The main
result of this file is that the radial parametrisation `u ↦ ρ u · u` of the body described by
`hgraph` stays inside the profile's support:

  `ρ u * u < bY`  (and dually `-bX < ρ (-u) * (-u)`)  for every `u ∈ (0,1)`.

Consequently the chord equality `ρ c · c = y s` (the identity
`Work.OddCurve.LowSlope.envelope_chord_eq_radial` in the tip-normalised setting) holds here too
(`envProfileFree_chord_eq_radial`), which is what lets the spherical-Radon identity be applied
with the untruncated profile.

The argument for `ρ u * u < bY`: the map `T u = ρ u · u` is continuous and strictly increasing
with `T 0 = 0`, and the profile's right branch is `F z = slopeRight y z · z + h (slopeRight y z)`,
so for `T u < bY` one has `T u / √(T u² + F (T u)²) = u` (`hgraph`).  If `T` crossed `bY` at some
`u* ∈ (0,1)`, then on the one hand `T u < bY` for `u < u*` forces `u* = 1` (because
`z / √(z² + F z²) → 1` as `z → bY` from below, the branch vanishing at the tip), while on the
other hand `hgraph` gives `F (T u) = ρ u √(1-u²) → ρ u* √(1-u*²) > 0` — and the branch vanishes at
the tip.  The two are incompatible.
-/

namespace Work.OddVolterra.Free

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

variable {h x y : ℝ → ℝ}

/-- Below the perturbation window the bump vanishes (from `H.h_support`). -/
theorem h_eq_zero_below (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {s : ℝ}
    (hs : s < 1 - 2 * Work.OddCurve.tau) : h s = 0 := by
  by_contra hne
  have hmem := H.h_support (Function.mem_support.mpr hne)
  linarith [hmem.1, hs]

/-! ## The branch vanishes at the tip -/

/-- **A right branch vanishes at the tip.**  Generic form: `c` is continuous and strictly
decreasing on `(0,∞)` with limit `b > 0` at `0⁺` and realises every point of `(0,b)`, `p σ → 0` at
`0⁺`, and `F z = slopeRight c z * z + p (slopeRight c z)`; then `F z → 0` as `z → b` from below
within `(0,b)`. -/
theorem tendsto_branch_at_tip {c p F : ℝ → ℝ} {b : ℝ}
    (hb : Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 b)) (hbpos : 0 < b)
    (hcanti : StrictAntiOn c (Set.Ioi 0))
    (hsurj : ∀ z ∈ Set.Ioo (0 : ℝ) b, ∃ σ : ℝ, 0 < σ ∧ c σ = z)
    (hpzero : Tendsto (fun σ : ℝ => σ * c σ + p σ) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hF : ∀ z ∈ Set.Ioo (0 : ℝ) b,
      F z = Work.OddEnvelope.slopeRight c z * z + p (Work.OddEnvelope.slopeRight c z)) :
    Tendsto F (𝓝[Set.Ioo (0 : ℝ) b] b) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hpzero) ε hε
  have hcδ : c δ < b := Work.OddEnvelope.lt_of_tendsto_of_strictAntiOn_Ioi hcanti hb δ hδpos
  refine ⟨b - c δ, by linarith, ?_⟩
  intro z hz hzdist
  rw [Real.dist_eq] at hzdist
  have hzgt : c δ < z := by
    have := (abs_lt.mp hzdist).1
    linarith
  have hzpos : 0 < z := hz.1
  obtain ⟨σ, hσpos, hσ⟩ := hsurj z hz
  have hσlt : σ < δ := by
    by_contra hle
    push_neg at hle
    have hmono : c σ ≤ c δ := (hcanti.le_iff_ge hσpos hδpos).mpr hle
    rw [hσ] at hmono
    linarith
  have hval := hδ hσpos (by rw [Real.dist_eq, sub_zero, abs_of_pos hσpos]; exact hσlt)
  have hsl : Work.OddEnvelope.slopeRight c z = σ := by
    rw [← hσ]
    exact hcanti.injOn.leftInvOn_invFunOn hσpos
  have hFz : F z = σ * z + p σ := by rw [hF z hz, hsl]
  rw [hσ] at hval
  rw [hFz]
  exact hval

/-! ## The radial parameter stays below the tip -/

/-- **The radial parametrisation of the body stays below the tip** (generic form). -/
theorem rho_mul_lt_tip_of_branch {c p F ρ : ℝ → ℝ} {b : ℝ}
    (hb : Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 b)) (hbpos : 0 < b)
    (hcanti : StrictAntiOn c (Set.Ioi 0))
    (hsurj : ∀ z ∈ Set.Ioo (0 : ℝ) b, ∃ σ : ℝ, 0 < σ ∧ c σ = z)
    (hpzero : Tendsto (fun σ : ℝ => σ * c σ + p σ) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hF : ∀ z ∈ Set.Ioo (0 : ℝ) b,
      F z = Work.OddEnvelope.slopeRight c z * z + p (Work.OddEnvelope.slopeRight c z))
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρcont : ContinuousOn ρ (Set.Ioo (-1 : ℝ) 1))
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * Real.sqrt (1 - u ^ 2) = F (ρ u * u)) :
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, ρ u * u < b := by
  set T : ℝ → ℝ := fun u => ρ u * u with hT
  intro u₀ hu₀
  by_contra hcon
  push_neg at hcon
  have hTcont : ContinuousOn T (Set.Ioo (-1 : ℝ) 1) := hρcont.mul continuousOn_id
  have hTmono : StrictMonoOn T (Set.Ioo (-1 : ℝ) 1) := hρmono
  have hT0 : T 0 = 0 := by simp [hT]
  have hu₀1 : (0 : ℝ) < u₀ := hu₀.1
  have hcontIcc : ContinuousOn T (Set.Icc 0 u₀) :=
    hTcont.mono (fun u hu => ⟨by linarith [hu.1], lt_of_le_of_lt hu.2 hu₀.2⟩)
  have hbT : b ∈ Set.Icc (T 0) (T u₀) := by
    rw [hT0]
    exact ⟨hbpos.le, hcon⟩
  obtain ⟨ustar, husmem, huseq⟩ := (intermediate_value_Icc hu₀1.le hcontIcc hbT)
  have huspos : 0 < ustar := by
    rcases lt_or_eq_of_le husmem.1 with hlt | heq
    · exact hlt
    · exfalso
      have hz : T ustar = 0 := by rw [← heq, hT0]
      rw [hz] at huseq
      linarith [hbpos]
  have huslt1 : ustar < 1 := lt_of_le_of_lt husmem.2 hu₀.2
  have husIoo : ustar ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, huslt1⟩
  have hltb : ∀ v ∈ Set.Ioo (0 : ℝ) ustar, T v < b := by
    intro v hv
    have hvIoo : v ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hv.1], by linarith [huslt1, hv.2]⟩
    have h := hTmono hvIoo husIoo hv.2
    rwa [huseq] at h
  -- the branch limit along `T`
  have hcomp : Tendsto (fun v : ℝ => F (T v)) (𝓝[Set.Ioo (0 : ℝ) ustar] ustar) (𝓝 0) := by
    have hTat : ContinuousAt T ustar := hTcont.continuousAt (isOpen_Ioo.mem_nhds husIoo)
    have hmaps : Tendsto T (𝓝[Set.Ioo (0 : ℝ) ustar] ustar) (𝓝[Set.Ioo (0 : ℝ) b] b) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · rw [← huseq]
        exact hTat.tendsto.mono_left nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin] with v hv
      have hv1 : v ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hv.1], by linarith [huslt1, hv.2]⟩
      exact ⟨by rw [hT]; exact mul_pos (hρpos v hv1) hv.1, hltb v hv⟩
    exact (tendsto_branch_at_tip hb hbpos hcanti hsurj hpzero hF).comp hmaps
  -- the `hgraph` limit along `T`
  have hρlim : Tendsto (fun v : ℝ => ρ v * Real.sqrt (1 - v ^ 2))
      (𝓝[Set.Ioo (0 : ℝ) ustar] ustar) (𝓝 (ρ ustar * Real.sqrt (1 - ustar ^ 2))) := by
    have hρc : ContinuousAt ρ ustar := hρcont.continuousAt (isOpen_Ioo.mem_nhds husIoo)
    have hs : ContinuousAt (fun v : ℝ => Real.sqrt (1 - v ^ 2)) ustar := by fun_prop
    exact (hρc.mul hs).tendsto.mono_left nhdsWithin_le_nhds
  haveI : NeBot (𝓝[Set.Ioo (0 : ℝ) ustar] ustar) := by
    rw [nhdsWithin_Ioo_eq_nhdsLT huspos]
    infer_instance
  have heq : ∀ᶠ v in 𝓝[Set.Ioo (0 : ℝ) ustar] ustar, F (T v) = ρ v * Real.sqrt (1 - v ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact (hgraph v ⟨by linarith [hv.1], by linarith [huslt1, hv.2]⟩).symm
  have hzero : ρ ustar * Real.sqrt (1 - ustar ^ 2) = 0 :=
    tendsto_nhds_unique hρlim (hcomp.congr' heq)
  have hpos : 0 < ρ ustar * Real.sqrt (1 - ustar ^ 2) :=
    mul_pos (hρpos ustar husIoo) (Real.sqrt_pos.mpr (by nlinarith [huspos, huslt1]))
  linarith [hzero, hpos]

/-! ## The two instantiations -/

/-- The `y`-branch of a free-tip envelope curve vanishes at its tip. -/
theorem tendsto_envProfileFree_at_tip (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {b : ℝ}
    (hb : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 b)) (hbpos : 0 < b) :
    Tendsto (envProfileFree h x y) (𝓝[Set.Ioo (0 : ℝ) b] b) (𝓝 0) := by
  refine tendsto_branch_at_tip (c := y) (p := h) (F := envProfileFree h x y) hb hbpos
    H.strictAntiOn_y ?_ ?_ ?_
  · intro z hz
    exact H.toChordCurveFree_y.exists_slope_of_mem_Ioo hb hz
  · have h1 : Tendsto (fun σ : ℝ => σ * y σ) (𝓝[>] (0 : ℝ)) (𝓝 (0 * b)) :=
      ((tendsto_id : Tendsto (fun σ : ℝ => σ) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left
        nhdsWithin_le_nhds).mul hb
    have h2 : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_lt_of_pos (show (0 : ℝ) < 1 - 2 * Work.OddCurve.tau by
        rw [Work.OddCurve.one_sub_two_tau_eq]; norm_num)] with σ hσ
      exact (h_eq_zero_below H hσ).symm
    simpa using h1.add h2
  · intro z hz
    rw [envProfileFree_of_pos hz.1, Work.OddEnvelope.envelopeRight]

/-- The `x`-branch of a free-tip envelope curve vanishes at its tip. -/
theorem tendsto_envProfileFreeLeft_at_tip (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    {b : ℝ} (hb : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 b)) (hbpos : 0 < b) :
    Tendsto (fun z : ℝ => envProfileFree h x y (-z)) (𝓝[Set.Ioo (0 : ℝ) b] b) (𝓝 0) := by
  refine tendsto_branch_at_tip (c := x) (p := Work.OddEnvelope.negH h)
    (F := fun z : ℝ => envProfileFree h x y (-z)) hb hbpos H.strictAntiOn_x ?_ ?_ ?_
  · intro z hz
    exact H.toChordCurveFree_x.exists_slope_of_mem_Ioo hb hz
  · have h1 : Tendsto (fun σ : ℝ => σ * x σ) (𝓝[>] (0 : ℝ)) (𝓝 (0 * b)) :=
      ((tendsto_id : Tendsto (fun σ : ℝ => σ) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left
        nhdsWithin_le_nhds).mul hb
    have h2 : Tendsto (Work.OddEnvelope.negH h) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_lt_of_pos (show (0 : ℝ) < 1 - 2 * Work.OddCurve.tau by
        rw [Work.OddCurve.one_sub_two_tau_eq]; norm_num)] with σ hσ
      simp only [Work.OddEnvelope.negH]
      rw [h_eq_zero_below H hσ, neg_zero]
    simpa using h1.add h2
  · intro z hz
    rw [envProfileFree_of_neg (by linarith [hz.1] : -z < 0),
      Work.OddEnvelope.envelopeLeft_eq_negH, neg_neg]
    rfl

/-- **The radial image of the body stays below the right tip.** -/
theorem rho_mul_lt_tip (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {ρ : ℝ → ℝ} {b : ℝ}
    (hb : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 b)) (hbpos : 0 < b)
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρcont : ContinuousOn ρ (Set.Ioo (-1 : ℝ) 1))
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = envProfileFree h x y (ρ u * u)) :
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, ρ u * u < b := by
  refine rho_mul_lt_tip_of_branch (c := y) (p := h) (F := envProfileFree h x y)
    hb hbpos H.strictAntiOn_y ?_ ?_ ?_ hρpos hρcont hρmono hgraph
  · intro z hz
    exact H.toChordCurveFree_y.exists_slope_of_mem_Ioo hb hz
  · have h1 : Tendsto (fun σ : ℝ => σ * y σ) (𝓝[>] (0 : ℝ)) (𝓝 (0 * b)) :=
      ((tendsto_id : Tendsto (fun σ : ℝ => σ) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left
        nhdsWithin_le_nhds).mul hb
    have h2 : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_lt_of_pos (show (0 : ℝ) < 1 - 2 * Work.OddCurve.tau by
        rw [Work.OddCurve.one_sub_two_tau_eq]; norm_num)] with σ hσ
      exact (h_eq_zero_below H hσ).symm
    simpa using h1.add h2
  · intro z hz
    rw [envProfileFree_of_pos hz.1, Work.OddEnvelope.envelopeRight]

/-- **The radial image of the body stays above the left tip.** -/
theorem rho_neg_mul_lt_tip (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {ρ : ℝ → ℝ}
    {b : ℝ} (hb : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 b)) (hbpos : 0 < b)
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρcont : ContinuousOn ρ (Set.Ioo (-1 : ℝ) 1))
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = envProfileFree h x y (ρ u * u)) :
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, -b < ρ (-u) * (-u) := by
  have hmain := rho_mul_lt_tip_of_branch (c := x) (p := Work.OddEnvelope.negH h)
    (F := fun z : ℝ => envProfileFree h x y (-z)) (ρ := fun u : ℝ => ρ (-u))
    hb hbpos H.strictAntiOn_x ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro u hu
    have h := hmain u hu
    linarith [neg_neg (ρ (-u) * (-u))]
  · intro z hz
    exact H.toChordCurveFree_x.exists_slope_of_mem_Ioo hb hz
  · have h1 : Tendsto (fun σ : ℝ => σ * x σ) (𝓝[>] (0 : ℝ)) (𝓝 (0 * b)) :=
      ((tendsto_id : Tendsto (fun σ : ℝ => σ) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left
        nhdsWithin_le_nhds).mul hb
    have h2 : Tendsto (Work.OddEnvelope.negH h) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_lt_of_pos (show (0 : ℝ) < 1 - 2 * Work.OddCurve.tau by
        rw [Work.OddCurve.one_sub_two_tau_eq]; norm_num)] with σ hσ
      simp only [Work.OddEnvelope.negH]
      rw [h_eq_zero_below H hσ, neg_zero]
    simpa using h1.add h2
  · intro z hz
    rw [envProfileFree_of_neg (by linarith [hz.1] : -z < 0),
      Work.OddEnvelope.envelopeLeft_eq_negH, neg_neg]
    rfl
  · intro u hu
    exact hρpos (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
  · have hcomp : ContinuousOn (fun u : ℝ => -u) (Set.Ioo (-1 : ℝ) 1) := continuous_neg.continuousOn
    exact hρcont.comp hcomp (fun u hu => ⟨by linarith [hu.2], by linarith [hu.1]⟩)
  · intro u₁ hu₁ u₂ hu₂ hlt
    have h1 : -u₂ ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hu₂.2], by linarith [hu₂.1]⟩
    have h2 : -u₁ ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hu₁.2], by linarith [hu₁.1]⟩
    have hlt' : -u₂ < -u₁ := by linarith
    have h := hρmono h1 h2 hlt'
    simp only
    linarith
  · intro u hu
    have hg := hgraph (-u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
    rw [show (-u) ^ 2 = u ^ 2 by ring] at hg
    rw [show ρ (-u) * (-u) = -(ρ (-u) * u) by ring] at hg
    exact hg

/-! ## Uniqueness of the root on a section -/

/-- Free-tip version of `Work.OddCurve.LowSlope.eq_linear_unique_pos`. -/
theorem eq_linear_unique_pos_Icc {f : ℝ → ℝ} {Y : ℝ} (hY : 0 < Y)
    (hconc : StrictConcaveOn ℝ (Set.Icc 0 Y) f) (h0 : f 0 = 1) {s a : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) Y) (hfa : f a = s * a) :
    ∀ b ∈ Set.Ioo (0 : ℝ) Y, f b = s * b → b = a := by
  intro b hb hfb
  rcases lt_trichotomy a b with hab | heq | hba
  · have hb0 : (0 : ℝ) < b := hb.1
    have hca : (0 : ℝ) < 1 - a / b := by
      rw [sub_pos, div_lt_one hb0]; exact hab
    have hcb : (0 : ℝ) < a / b := div_pos ha.1 hb0
    have hsum : (1 - a / b) + a / b = 1 := by ring
    have hx : (0 : ℝ) ∈ Set.Icc 0 Y := ⟨le_refl 0, hY.le⟩
    have hy : b ∈ Set.Icc 0 Y := ⟨hb0.le, hb.2.le⟩
    have hne : (0 : ℝ) ≠ b := ne_of_lt hb0
    have hkey := hconc.2 hx hy hne hca hcb hsum
    have hpt : (1 - a / b) • (0 : ℝ) + (a / b) • b = a := by
      rw [smul_eq_mul, smul_eq_mul, mul_zero, zero_add]
      field_simp
    rw [hpt] at hkey
    simp only [smul_eq_mul, h0, hfb, hfa, mul_one] at hkey
    have hsab : a / b * (s * b) = s * a := by field_simp
    rw [hsab] at hkey
    linarith [hkey, hca]
  · exact heq.symm
  · have ha0 : (0 : ℝ) < a := ha.1
    have hca : (0 : ℝ) < 1 - b / a := by
      rw [sub_pos, div_lt_one ha0]; exact hba
    have hcb : (0 : ℝ) < b / a := div_pos hb.1 ha0
    have hsum : (1 - b / a) + b / a = 1 := by ring
    have hx : (0 : ℝ) ∈ Set.Icc 0 Y := ⟨le_refl 0, hY.le⟩
    have hy : a ∈ Set.Icc 0 Y := ⟨ha0.le, ha.2.le⟩
    have hne : (0 : ℝ) ≠ a := ne_of_lt ha0
    have hkey := hconc.2 hx hy hne hca hcb hsum
    have hpt : (1 - b / a) • (0 : ℝ) + (b / a) • a = b := by
      rw [smul_eq_mul, smul_eq_mul, mul_zero, zero_add]
      field_simp
    rw [hpt] at hkey
    simp only [smul_eq_mul, h0, hfa, hfb, mul_one] at hkey
    have hsab : b / a * (s * a) = s * b := by field_simp
    rw [hsab] at hkey
    linarith [hkey, hca]

/-- Free-tip version of `Work.OddCurve.LowSlope.eq_linear_unique_neg`. -/
theorem eq_linear_unique_neg_Icc {f : ℝ → ℝ} {Y : ℝ} (hY : 0 < Y)
    (hconc : StrictConcaveOn ℝ (Set.Icc (-Y) 0) f) (h0 : f 0 = 1) {s a : ℝ}
    (ha : a ∈ Set.Ioo (-Y) 0) (hfa : f a = -(s * a)) :
    ∀ b ∈ Set.Ioo (-Y) 0, f b = -(s * b) → b = a := by
  intro b hb hfb
  rcases lt_trichotomy a b with hab | heq | hba
  · have ha0 : a < 0 := ha.2
    have ha1 : -Y < a := ha.1
    have hb0 : b < 0 := hb.2
    have hcb : (0 : ℝ) < b / a := div_pos_of_neg_of_neg hb0 ha0
    have hca : (0 : ℝ) < 1 - b / a := by
      rw [sub_pos]
      rw [div_lt_one_of_neg ha0]
      exact hab
    have hsum : (b / a) + (1 - b / a) = 1 := by ring
    have hx : a ∈ Set.Icc (-Y) 0 := ⟨ha1.le, ha0.le⟩
    have hy : (0 : ℝ) ∈ Set.Icc (-Y) 0 := ⟨by linarith, le_refl 0⟩
    have hne : a ≠ (0 : ℝ) := ne_of_lt ha0
    have hkey := hconc.2 hx hy hne hcb hca hsum
    have hpt : (b / a) • a + (1 - b / a) • (0 : ℝ) = b := by
      rw [smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
      field_simp
    rw [hpt] at hkey
    simp only [smul_eq_mul, h0, hfa, hfb, mul_one] at hkey
    have hsab : b / a * (s * a) = s * b := by field_simp
    rw [mul_neg, hsab] at hkey
    linarith [hkey, hca]
  · exact heq.symm
  · have hb0 : b < 0 := hb.2
    have hb1 : -Y < b := hb.1
    have hcb : (0 : ℝ) < a / b := div_pos_of_neg_of_neg ha.2 hb0
    have hca : (0 : ℝ) < 1 - a / b := by
      rw [sub_pos]
      rw [div_lt_one_of_neg hb0]
      exact hba
    have hsum : (a / b) + (1 - a / b) = 1 := by ring
    have hx : b ∈ Set.Icc (-Y) 0 := ⟨hb1.le, hb0.le⟩
    have hy : (0 : ℝ) ∈ Set.Icc (-Y) 0 := ⟨by linarith, le_refl 0⟩
    have hne : b ≠ (0 : ℝ) := ne_of_lt hb0
    have hkey := hconc.2 hx hy hne hcb hca hsum
    have hpt : (a / b) • b + (1 - a / b) • (0 : ℝ) = a := by
      rw [smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
      field_simp
    rw [hpt] at hkey
    simp only [smul_eq_mul, h0, hfb, hfa, mul_one] at hkey
    have hsab : a / b * (s * b) = s * a := by field_simp
    rw [mul_neg, hsab] at hkey
    linarith [hkey, hca]

/-! ## The chord of a vanishing crop is the radial chord -/

/-- The two chord identities for the untruncated profile. -/
theorem envProfileFree_chord_roots (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {s : ℝ}
    (hs : 0 < s) (hz : h s = 0) :
    envProfileFree h x y (y s) = s * y s ∧
      envProfileFree h x y (-(x s)) = -(s * (-(x s))) := by
  have hsmx : ContDiffOn ℝ ∞ x (Set.Ioi 0) := H.smooth_x
  have hsmy : ContDiffOn ℝ ∞ y (Set.Ioi 0) := H.smooth_y
  obtain ⟨h1, h2⟩ := envProfileFree_chord h x y hsmx hsmy
    (fun u hu => H.x_deriv_neg u hu) (fun u hu => H.y_deriv_neg u hu)
    (fun u hu => H.pos_x hu) (fun u hu => H.pos_y hu)
  refine ⟨?_, ?_⟩
  · rw [h1 s hs, hz, add_zero]
  · rw [h2 s hs, hz, add_zero]

/-- **The chord of a vanishing crop is the radial chord**, for the untruncated (free-tip)
profile.  Free-tip analogue of `Work.OddCurve.LowSlope.envelope_chord_eq_radial`. -/
theorem envProfileFree_chord_eq_radial (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    {ρ : ℝ → ℝ} {bY bX : ℝ}
    (hY : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 bY)) (hYpos : 0 < bY)
    (hX : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 bX)) (hXpos : 0 < bX)
    {s : ℝ} (hs : 0 < s) (hz : h s = 0)
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρcont : ContinuousOn ρ (Set.Ioo (-1 : ℝ) 1))
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = envProfileFree h x y (ρ u * u)) :
    y s = ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * ((Real.sqrt (1 + s ^ 2))⁻¹) ∧
      x s = ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * ((Real.sqrt (1 + s ^ 2))⁻¹) := by
  set c : ℝ := (Real.sqrt (1 + s ^ 2))⁻¹ with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hclt : c < 1 := by
    rw [hc]
    refine inv_lt_one_of_one_lt₀ ?_
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (1 + s ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by nlinarith [sq_nonneg s])
  have hcmem : c ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hclt⟩
  have hnmcmem : -c ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hcsq : c ^ 2 = (1 + s ^ 2)⁻¹ := by
    rw [hc, inv_pow, Real.sq_sqrt (by positivity)]
  have h1mc : 1 - c ^ 2 = (s * c) ^ 2 := by
    have h1 : c ^ 2 * (1 + s ^ 2) = 1 := by rw [hcsq]; field_simp
    nlinarith [h1]
  have hsqrt : Real.sqrt (1 - c ^ 2) = s * c := by
    rw [h1mc, Real.sqrt_sq (by positivity)]
  have hroots := envProfileFree_chord_roots H hs hz
  -- the right branch
  have ht1pos : 0 < ρ c * c := mul_pos (hρpos c hcmem) hcpos
  have ht1lt : ρ c * c < bY :=
    rho_mul_lt_tip H hY hYpos hρpos hρcont hρmono hgraph c ⟨hcpos, hclt⟩
  have hft1 : envProfileFree h x y (ρ c * c) = s * (ρ c * c) := by
    rw [← hgraph c hcmem, hsqrt]
    ring
  have hyspos : 0 < y s := H.pos_y hs
  have hyslt : y s < bY := H.toChordCurveFree_y.lt_tip hY hs
  obtain ⟨c₀, hc₀, hc₀pos⟩ :
      ∃ c₀ : ℝ, max (ρ c * c) (y s) < y c₀ ∧ 0 < c₀ := by
    have hbmax : max (ρ c * c) (y s) < bY := max_lt ht1lt hyslt
    exact ((hY.eventually (Ioi_mem_nhds hbmax)).and self_mem_nhdsWithin).exists
  have hmaxpos : 0 < max (ρ c * c) (y s) := lt_of_lt_of_le ht1pos (le_max_left _ _)
  have hYmem : max (ρ c * c) (y s) < y c₀ := hc₀
  have hconc : StrictConcaveOn ℝ (Set.Icc 0 (y c₀)) (envProfileFree h x y) :=
    (strictConcaveOn_envProfileFree_Icc H hc₀pos).subset
      (fun t ht => ⟨by linarith [H.pos_x hc₀pos, ht.1], ht.2⟩) (convex_Icc _ _)
  have huniq := eq_linear_unique_pos_Icc (lt_of_lt_of_le hmaxpos hYmem.le) hconc
    (envProfileFree_zero) ⟨ht1pos, lt_of_le_of_lt (le_max_left _ _) hYmem⟩ hft1
  have hright : ρ c * c = y s :=
    (huniq (y s) ⟨hyspos, lt_of_le_of_lt (le_max_right _ _) hYmem⟩ hroots.1).symm
  -- the left branch
  have ht2neg : ρ (-c) * (-c) < 0 := by
    have h := hρpos (-c) hnmcmem
    nlinarith
  have ht2gt : -bX < ρ (-c) * (-c) :=
    rho_neg_mul_lt_tip H hX hXpos hρpos hρcont hρmono hgraph c ⟨hcpos, hclt⟩
  have hft2 : envProfileFree h x y (ρ (-c) * (-c)) = -(s * (ρ (-c) * (-c))) := by
    have hg := hgraph (-c) hnmcmem
    rw [show (-c) ^ 2 = c ^ 2 by ring, hsqrt] at hg
    rw [← hg]
    ring
  have hxspos : 0 < x s := H.pos_x hs
  have hxslt : x s < bX := H.toChordCurveFree_x.lt_tip hX hs
  obtain ⟨c₁, hc₁, hc₁pos⟩ :
      ∃ c₁ : ℝ, max (-(ρ (-c) * (-c))) (x s) < x c₁ ∧ 0 < c₁ := by
    have hbmax : max (-(ρ (-c) * (-c))) (x s) < bX := max_lt (by linarith [ht2gt]) hxslt
    exact ((hX.eventually (Ioi_mem_nhds hbmax)).and self_mem_nhdsWithin).exists
  have hmaxpos₁ : 0 < max (-(ρ (-c) * (-c))) (x s) :=
    lt_of_lt_of_le hxspos (le_max_right _ _)
  have hconc₁ : StrictConcaveOn ℝ (Set.Icc (-(x c₁)) 0) (envProfileFree h x y) :=
    (strictConcaveOn_envProfileFree_Icc H hc₁pos).subset
      (fun t ht => ⟨ht.1, by linarith [H.pos_y hc₁pos, ht.2]⟩) (convex_Icc _ _)
  have huniq₁ := eq_linear_unique_neg_Icc (lt_of_lt_of_le hmaxpos₁ hc₁.le) hconc₁
    (envProfileFree_zero) ⟨by linarith [le_max_left (-(ρ (-c) * (-c))) (x s), hc₁],
      ht2neg⟩ hft2
  have hleft : ρ (-c) * (-c) = -(x s) :=
    (huniq₁ (-(x s)) ⟨by linarith [le_max_right (-(ρ (-c) * (-c))) (x s), hc₁],
      by linarith⟩ hroots.2).symm
  refine ⟨by rw [← hright], ?_⟩
  have : x s = -(ρ (-c) * (-c)) := by linarith [hleft]
  rw [this]
  ring

end

end Work.OddVolterra.Free
