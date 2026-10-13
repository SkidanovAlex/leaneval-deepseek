import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25Aux.abs_le_chord_left
import Submission.Work.FTS_StreamBdry.SB25Aux.eventually_uniform_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB5Aux.unif_decay_ratio_proved` — leaf E5 (`UnifDecayRatio`)

Pointwise decay in `z` together with *uniform* `∂_θ`- and `∂_θ²`-bounds `K` and vanishing at
the two ends `θ = 0`, `θ = π/2` imply *uniform* decay relative to `s2 θ = sin 2θ`:

`∀ ε > 0, ∃ R, ∀ z ≥ R, ∀ θ ∈ (0,π/2), |P z θ| ≤ ε · sin 2θ`.

## Proof scheme

Fix `ε > 0` and `δ > 0` small (`δ := min (π/8) (ε / (K+1))`), and put `th := 2εδ/π`.

* On the *middle* interval `[δ, π/2 - δ]` the pointwise convergence in `z` upgrades to uniform
  convergence (`SB25Aux.eventually_uniform_abs_le`, using only the `θ`-Lipschitz bound `K`);
  there `sin 2θ ≥ sin 2δ`, so the uniform bound `|P z θ| ≤ ε·sin 2δ` suffices.
* On `[0, δ]` (resp. `[π/2 - δ, π/2]`) the two-sided chord bound
  `SB25Aux.abs_le_chord_left` (resp. its mirror `chord_right`, proved here by reflecting the
  interval) applied with the *reference value* at `δ` (resp. at `π/2 - δ`) gives
  `|P z θ| ≤ (θ/δ)|P z δ| + (K/2)θ(δ-θ)`, and `|P z δ| ≤ th` for `z` large; the result is
  `|P z θ| ≤ θ·(2ε/π + Kδ/2) ≤ θ·(4ε/π) ≤ ε sin 2θ` since `sin 2θ ≥ (4/π)θ` on `[0,π/8]`.

The right-endpoint mirror `chord_right` is proved in this file by applying
`abs_le_chord_left` to the reflected function `θ ↦ F (b - θ)`.  This file deliberately does
**not** import `SB25Aux.abs_le_chord_right`: that module is derived from the still-open
`SB25Aux.chord_bound` and would therefore taint this theorem with `sorryAx`.  The whole proof
below rests only on the `sorry`-free modules `SB25Aux.abs_le_chord_left` and
`SB25Aux.eventually_uniform_abs_le`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB5Aux

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP psiHatP SB5Barrier oddPerS)
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## §1 The one-dimensional ingredients -/

/-- `∂_θ` of a fixed `z`-slice is the slice of `pth`. -/
private lemma pth_eq_deriv (P : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.pth P z = deriv (fun θ' => P z θ') := by
  funext θ
  simp only [Work.Spaces.pth]

/-- `∂_θ²` of a fixed `z`-slice is the slice of `pthIter 2`. -/
private lemma pthIter_two_eq (P : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.pthIter 2 P z = deriv (deriv (fun θ' => P z θ')) := by
  funext θ
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]

/-- Jordan's inequality in the form `(4/π) x ≤ sin 2x` for `x ∈ (0, π/8]`. -/
private lemma sin_two_ge_of_le_pi_div_eight {x : ℝ} (hx : 0 < x) (hx' : x ≤ π / 8) :
    (4 / π) * x ≤ Real.sin (2 * x) := by
  have h := Real.mul_le_sin (x := 2 * x) (by linarith) (by linarith [Real.pi_pos])
  calc (4 / π) * x = (2 / π) * (2 * x) := by ring
    _ ≤ Real.sin (2 * x) := h

/-- **Chord bound at the right endpoint.**  A `C²` function on `(a,b)` with `|F'| ≤ K`,
`|F''| ≤ K`, whose one-sided limit at `b` is `0` and which is continuous at `a` (with value
`F a`), satisfies

`|F θ| ≤ ((b - θ)/(b - a)) |F a| + (K/2) (θ - a) (b - θ)`.

This is the mirror image of `SB25Aux.abs_le_chord_left`, obtained by applying the latter to the
reflected function `x ↦ F (b - x)` on `(0, b - a)`.  Kept public so that other leaves of the
SB2/SB5 plan can reuse it instead of the copy in `SB25Aux.abs_le_chord_right`, which in this
workspace still depends on the open `SB25Aux.chord_bound`.
-/

theorem chord_right {F : ℝ → ℝ} {K a b : ℝ} (hab : a < b)
    (hlim : Filter.Tendsto F (nhdsWithin b (Set.Iio b)) (nhds 0))
    (hcont : Filter.Tendsto F (nhdsWithin a (Set.Ioi a)) (nhds (F a)))
    (hd1 : ∀ θ ∈ Set.Ioo a b, DifferentiableAt ℝ F θ)
    (hd2 : ∀ θ ∈ Set.Ioo a b, DifferentiableAt ℝ (deriv F) θ)
    (hb1 : ∀ θ ∈ Set.Ioo a b, |deriv F θ| ≤ K)
    (hb2 : ∀ θ ∈ Set.Ioo a b, |deriv (deriv F) θ| ≤ K) :
    ∀ θ ∈ Set.Ioo a b, |F θ| ≤ ((b - θ) / (b - a)) * |F a| + (K / 2) * (θ - a) * (b - θ) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hmem : ∀ x ∈ Set.Ioo (0:ℝ) (b - a), b - x ∈ Set.Ioo a b :=
    fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hC : Continuous (fun x : ℝ => b - x) := continuous_const.sub continuous_id
  -- the reflected variable maps `0⁺` to `b⁻`
  have hsub_lim : Filter.Tendsto (fun x : ℝ => b - x) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin b (Set.Iio b)) := by
    have hmap : Set.MapsTo (fun x : ℝ => b - x) (Set.Ioi (0:ℝ)) (Set.Iio b) := fun x hx => by
      have hx' : (0:ℝ) < x := hx
      show b - x < b
      linarith
    have ht := (hC.continuousAt (x := (0:ℝ))).continuousWithinAt
      (s := Set.Ioi (0:ℝ)) |>.tendsto_nhdsWithin hmap
    simpa only [sub_zero] using ht
  have hGlim : Filter.Tendsto (fun x : ℝ => F (b - x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [Function.comp_def] using hlim.comp hsub_lim
  -- and `(b-a)⁻` to `a⁺`
  have hsub_lim2 : Filter.Tendsto (fun x : ℝ => b - x) (nhdsWithin (b - a) (Set.Iio (b - a)))
      (nhdsWithin a (Set.Ioi a)) := by
    have hmap : Set.MapsTo (fun x : ℝ => b - x) (Set.Iio (b - a)) (Set.Ioi a) := fun x hx => by
      have hx' : x < b - a := hx
      show a < b - x
      linarith
    have ht := (hC.continuousAt (x := b - a)).continuousWithinAt
      (s := Set.Iio (b - a)) |>.tendsto_nhdsWithin hmap
    simpa only [sub_sub_cancel] using ht
  have hGcont : Filter.Tendsto (fun x : ℝ => F (b - x)) (nhdsWithin (b - a) (Set.Iio (b - a)))
      (nhds (F a)) := by
    simpa only [Function.comp_def, sub_sub_cancel] using hcont.comp hsub_lim2
  have hGcont' : Filter.Tendsto (fun x : ℝ => F (b - x)) (nhdsWithin (b - a) (Set.Iio (b - a)))
      (nhds (F (b - (b - a)))) := by
    simpa only [sub_sub_cancel] using hGcont
  have hGd1 : ∀ x ∈ Set.Ioo (0:ℝ) (b - a), DifferentiableAt ℝ (fun y : ℝ => F (b - y)) x := by
    intro x hx
    exact (hd1 (b - x) (hmem x hx)).comp x
      ((differentiableAt_const (c := b)).sub differentiableAt_id)
  have hGderiv : ∀ x ∈ Set.Ioo (0:ℝ) (b - a),
      deriv (fun y : ℝ => F (b - y)) x = -deriv F (b - x) := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => b - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub b
    have h2 := (hd1 (b - x) (hmem x hx)).hasDerivAt.comp x h1
    have hd := h2.deriv
    simp only [Function.comp_def] at hd
    rw [hd]; ring
  have hGderiv_ev : ∀ x ∈ Set.Ioo (0:ℝ) (b - a),
      (deriv (fun y : ℝ => F (b - y))) =ᶠ[nhds x] (fun y => -deriv F (b - y)) := by
    intro x hx
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact hGderiv y hy
  have hGd2 : ∀ x ∈ Set.Ioo (0:ℝ) (b - a),
      DifferentiableAt ℝ (deriv (fun y : ℝ => F (b - y))) x := by
    intro x hx
    exact (Filter.EventuallyEq.differentiableAt_iff (hGderiv_ev x hx)).mpr
      (((hd2 (b - x) (hmem x hx)).comp x
        ((differentiableAt_const (c := b)).sub differentiableAt_id)).neg)
  have hneg : ∀ x ∈ Set.Ioo (0:ℝ) (b - a),
      HasDerivAt (fun y : ℝ => -deriv F (b - y)) (-(deriv (deriv F) (b - x) * -1)) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => b - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub b
    have h2 : HasDerivAt (deriv F ∘ fun y : ℝ => b - y) (deriv (deriv F) (b - x) * -1) x :=
      (hd2 (b - x) (hmem x hx)).hasDerivAt.comp x h1
    exact h2.neg
  have hGderiv2 : ∀ x ∈ Set.Ioo (0:ℝ) (b - a),
      deriv (deriv (fun y : ℝ => F (b - y))) x = deriv (deriv F) (b - x) := by
    intro x hx
    rw [Filter.EventuallyEq.deriv_eq (hGderiv_ev x hx)]
    have hd := (hneg x hx).deriv
    rw [hd]; ring
  have hGb1 : ∀ x ∈ Set.Ioo (0:ℝ) (b - a), |deriv (fun y : ℝ => F (b - y)) x| ≤ K := by
    intro x hx
    rw [hGderiv x hx, abs_neg]
    exact hb1 (b - x) (hmem x hx)
  have hGb2 : ∀ x ∈ Set.Ioo (0:ℝ) (b - a),
      |deriv (deriv (fun y : ℝ => F (b - y))) x| ≤ K := by
    intro x hx
    rw [hGderiv2 x hx]
    exact hb2 (b - x) (hmem x hx)
  intro θ hθ
  have hkey := Work.FTS_StreamBdry.SB25Aux.abs_le_chord_left
    (F := fun y : ℝ => F (b - y)) (K := K) (a := 0) (b := b - a) hba
    hGlim hGcont' hGd1 hGd2 hGb1 hGb2 (b - θ) ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  simp only [sub_sub_cancel, sub_zero] at hkey
  calc |F θ| ≤ ((b - θ) / (b - a)) * |F a| + K / 2 * (b - θ) * (b - a - (b - θ)) := hkey
    _ = ((b - θ) / (b - a)) * |F a| + K / 2 * (θ - a) * (b - θ) := by ring

/-! ## §2 The leaf -/

/-- **`UnifDecayRatio`** (leaf E5 of the SB5 plan): pointwise decay in `z`, a uniform
`∂_θ`-bound `K`, a uniform `∂_θ²`-bound `K` and vanishing at the two ends `θ = 0`, `θ = π/2`
give uniform decay relative to `s2 θ = sin 2θ`. -/
theorem unif_decay_ratio_proved (P : ℝ → ℝ → ℝ) (K : ℝ) :
    Work.FTS_StreamBdry.SB25.UnifDecayRatio P K := by
  intro hdiff hb1 hb2 hlim hdecay
  have hQd1 : ((1 : ℝ), (π / 4 : ℝ)) ∈ Work.Construction.Qd := by
    rw [Work.FTS_StreamBdry.mem_Qd]
    exact ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hK : 0 ≤ K := le_trans (abs_nonneg (Work.Spaces.pth P 1 (π / 4))) (hb1 1 (π / 4) hQd1)
  intro ε hε
  set δ : ℝ := min (π / 8) (ε / (K + 1)) with hδdef
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  have hδpos : 0 < δ := lt_min (by linarith [Real.pi_pos]) (by positivity)
  have hδle_eps : δ ≤ ε / (K + 1) := min_le_right _ _
  have hδle8 : δ ≤ π / 8 := min_le_left _ _
  have hδlt : δ < π / 2 := by linarith [Real.pi_pos]
  have hKδ : K * δ ≤ 4 * ε / π := by
    have h1 : K * δ ≤ ε := by
      calc K * δ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hδle_eps hK
        _ = K * ε / (K + 1) := by rw [mul_div_assoc]
        _ ≤ ε := by rw [div_le_iff₀ hK1]; nlinarith [hK, hε.le]
    have h2 : ε ≤ 4 * ε / π := by
      rw [le_div_iff₀ Real.pi_pos]
      nlinarith [Real.pi_lt_four, hε.le]
    linarith
  set th : ℝ := 2 * ε * δ / π with hthdef
  have hthpos : 0 < th := by rw [hthdef]; positivity
  have hthδ : th / δ = 2 * ε / π := by
    rw [hthdef]
    field_simp
  have hA : th / δ + K * δ / 2 ≤ 4 * ε / π := by
    have h2 : K * δ / 2 ≤ 2 * ε / π := by
      have h3 := div_le_div_of_nonneg_right hKδ (by norm_num : (0 : ℝ) ≤ 2)
      have h4 : (4 : ℝ) * ε / π / 2 = 2 * ε / π := by ring
      rwa [h4] at h3
    rw [hthδ]
    calc 2 * ε / π + K * δ / 2 = K * δ / 2 + 2 * ε / π := by ring
      _ ≤ 2 * ε / π + 2 * ε / π := add_le_add_left h2 _
      _ = 4 * ε / π := by ring
  -- eventual smallness at the two reference points
  have hsmallδ : ∀ᶠ z in atTop, |P z δ| ≤ th := by
    filter_upwards [(Metric.tendsto_nhds.1 (hdecay δ ⟨hδpos, hδlt⟩)) th hthpos] with z hz
    rw [Real.dist_eq, sub_zero] at hz
    exact le_of_lt hz
  have hsmallr : ∀ᶠ z in atTop, |P z (π / 2 - δ)| ≤ th := by
    filter_upwards
      [(Metric.tendsto_nhds.1 (hdecay (π / 2 - δ) ⟨by linarith, by linarith⟩)) th hthpos]
      with z hz
    rw [Real.dist_eq, sub_zero] at hz
    exact le_of_lt hz
  have hεs : 0 < ε * Real.sin (2 * δ) :=
    mul_pos hε (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have hmiddle : ∀ᶠ z in atTop, ∀ θ ∈ Icc δ (π / 2 - δ), |P z θ| ≤ ε * Real.sin (2 * δ) := by
    have hG : ∀ᶠ z in atTop, ∀ θ ∈ Icc δ (π / 2 - δ),
        |P (max z 1) θ| ≤ ε * Real.sin (2 * δ) := by
      refine Work.FTS_StreamBdry.SB25Aux.eventually_uniform_abs_le (F := fun z θ => P (max z 1) θ)
        (K := K) (a := δ) (b := π / 2 - δ) (ε := ε * Real.sin (2 * δ)) (by linarith) hK ?_ ?_ hεs
      · intro z θ hθ θ' hθ'
        have hxQd : ∀ x ∈ Icc δ (π / 2 - δ), (max z 1, x) ∈ Work.Construction.Qd := by
          intro x hx
          rw [Work.FTS_StreamBdry.mem_Qd]
          exact ⟨lt_of_lt_of_le one_pos (le_max_right _ _), by linarith [hδpos, hx.1],
            by linarith [hδpos, hx.2]⟩
        have hFdiff : ∀ x ∈ Icc δ (π / 2 - δ),
            DifferentiableAt ℝ (fun θ' => P (max z 1) θ') x :=
          fun x hx => (hdiff _ x (hxQd x hx)).1
        have hFbnd : ∀ x ∈ Icc δ (π / 2 - δ), ‖deriv (fun θ' => P (max z 1) θ') x‖ ≤ K := by
          intro x hx
          have h := hb1 _ x (hxQd x hx)
          rw [pth_eq_deriv] at h
          rwa [Real.norm_eq_abs]
        have hL := (convex_Icc δ (π / 2 - δ)).norm_image_sub_le_of_norm_deriv_le hFdiff hFbnd hθ' hθ
        rwa [Real.norm_eq_abs, Real.norm_eq_abs] at hL
      · intro θ hθ
        refine (hdecay θ ⟨by linarith [hδpos, hθ.1], by linarith [hδpos, hθ.2]⟩).congr' ?_
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
        simp only [max_eq_left hz]
    filter_upwards [hG, eventually_ge_atTop (1 : ℝ)] with z hz hz1
    simp only [max_eq_left hz1] at hz
    exact hz
  have hall : ∀ᶠ z in atTop, |P z δ| ≤ th ∧ |P z (π / 2 - δ)| ≤ th ∧
      (∀ θ ∈ Icc δ (π / 2 - δ), |P z θ| ≤ ε * Real.sin (2 * δ)) := by
    filter_upwards [hsmallδ, hsmallr, hmiddle] with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  rw [Filter.eventually_atTop] at hall
  obtain ⟨R, hR⟩ := hall
  refine ⟨max R 1, ?_⟩
  intro z θ hz hθ
  have hzR : R ≤ z := le_trans (le_max_left _ _) hz
  have hzpos : 0 < z := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hz)
  obtain ⟨hrefδ, hrefr, hmid⟩ := hR z hzR
  have hzQd : ∀ x ∈ Ioo (0 : ℝ) (π / 2), (z, x) ∈ Work.Construction.Qd := by
    intro x hx
    rw [Work.FTS_StreamBdry.mem_Qd]
    exact ⟨hzpos, hx.1, hx.2⟩
  rcases lt_or_ge θ δ with hlt | hge
  · -- near θ = 0
    have hFlim : Tendsto (fun θ' => P z θ') (nhdsWithin 0 (Ioi 0)) (nhds 0) := (hlim z hzpos).1
    have hFcont : Tendsto (fun θ' => P z θ') (nhdsWithin δ (Iio δ)) (nhds (P z δ)) :=
      ((hdiff z δ (hzQd δ ⟨hδpos, hδlt⟩)).1.continuousAt).tendsto.mono_left inf_le_left
    have hmain := Work.FTS_StreamBdry.SB25Aux.abs_le_chord_left (F := fun θ' => P z θ') (K := K)
      (a := 0) (b := δ) hδpos hFlim hFcont
      (fun x hx => (hdiff z x (hzQd x ⟨hx.1, lt_trans hx.2 hδlt⟩)).1)
      (fun x hx => by
        have h := (hdiff z x (hzQd x ⟨hx.1, lt_trans hx.2 hδlt⟩)).2
        rwa [pth_eq_deriv] at h)
      (fun x hx => by
        have h := hb1 z x (hzQd x ⟨hx.1, lt_trans hx.2 hδlt⟩)
        rwa [pth_eq_deriv] at h)
      (fun x hx => by
        have h := hb2 z x (hzQd x ⟨hx.1, lt_trans hx.2 hδlt⟩)
        rwa [pthIter_two_eq] at h)
      θ ⟨hθ.1, hlt⟩
    have hsin := sin_two_ge_of_le_pi_div_eight (x := θ) (by linarith [hθ.1]) (by linarith)
    calc |P z θ| ≤ (θ / δ) * |P z δ| + K / 2 * θ * (δ - θ) := by simpa using hmain
      _ ≤ (θ / δ) * th + K / 2 * θ * δ := by
          have h1 : (θ / δ) * |P z δ| ≤ (θ / δ) * th :=
            mul_le_mul_of_nonneg_left hrefδ (le_of_lt (div_pos hθ.1 hδpos))
          have h2 : K / 2 * θ * (δ - θ) ≤ K / 2 * θ * δ := by
            have hXY : δ - θ ≤ δ := by linarith [hθ.1]
            have hX : 0 ≤ K / 2 * θ := mul_nonneg (by linarith) (le_of_lt hθ.1)
            exact mul_le_mul_of_nonneg_left hXY hX
          linarith
      _ = θ * (th / δ + K * δ / 2) := by ring_nf
      _ ≤ θ * (4 * ε / π) := mul_le_mul_of_nonneg_left hA (by linarith [hθ.1])
      _ = ε * ((4 / π) * θ) := by ring
      _ ≤ ε * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hsin hε.le
      _ = ε * Work.Construction.s2 θ := by rw [Work.Construction.s2_eq]
  · rcases le_or_gt θ (π / 2 - δ) with hmidθ | hgt
    · -- middle region
      have hθmem : θ ∈ Icc δ (π / 2 - δ) := ⟨hge, hmidθ⟩
      have hsinmono : Real.sin (2 * δ) ≤ Real.sin (2 * θ) := by
        rcases le_or_gt θ (π / 4) with h4 | h4
        · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
            (by linarith) (by linarith)
        · rw [← Real.sin_pi_sub (2 * θ)]
          exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
            (by linarith) (by linarith)
      calc |P z θ| ≤ ε * Real.sin (2 * δ) := hmid θ hθmem
        _ ≤ ε * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hsinmono hε.le
        _ = ε * Work.Construction.s2 θ := by rw [Work.Construction.s2_eq]
    · -- near θ = π/2
      have hFlim : Tendsto (fun θ' => P z θ') (nhdsWithin (π / 2) (Iio (π / 2))) (nhds 0) :=
        (hlim z hzpos).2
      have hFcont : Tendsto (fun θ' => P z θ') (nhdsWithin (π / 2 - δ) (Ioi (π / 2 - δ)))
          (nhds (P z (π / 2 - δ))) :=
        ((hdiff z (π / 2 - δ) (hzQd _ ⟨by linarith, by linarith⟩)).1.continuousAt).tendsto.mono_left
          inf_le_left
      have hmain := chord_right (F := fun θ' => P z θ') (K := K)
        (a := π / 2 - δ) (b := π / 2) (by linarith) hFlim hFcont
        (fun x hx => (hdiff z x (hzQd x ⟨by linarith [hx.1], by linarith [hx.2]⟩)).1)
        (fun x hx => by
          have h := (hdiff z x (hzQd x ⟨by linarith [hx.1], by linarith [hx.2]⟩)).2
          rwa [pth_eq_deriv] at h)
        (fun x hx => by
          have h := hb1 z x (hzQd x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
          rwa [pth_eq_deriv] at h)
        (fun x hx => by
          have h := hb2 z x (hzQd x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
          rwa [pthIter_two_eq] at h)
        θ ⟨hgt, hθ.2⟩
      have hmain' : |P z θ| ≤ ((π / 2 - θ) / δ) * |P z (π / 2 - δ)|
          + K / 2 * (θ - (π / 2 - δ)) * (π / 2 - θ) := by
        have h := hmain
        rw [show (π / 2 : ℝ) - (π / 2 - δ) = δ by ring] at h
        exact h
      have hsin := sin_two_ge_of_le_pi_div_eight (x := π / 2 - θ)
        (by linarith [hθ.2]) (by linarith [hδle8, hgt])
      have hsin2 : Real.sin (2 * θ) = Real.sin (2 * (π / 2 - θ)) := by
        rw [show 2 * θ = π - 2 * (π / 2 - θ) by ring, Real.sin_pi_sub]
      calc |P z θ| ≤ ((π / 2 - θ) / δ) * |P z (π / 2 - δ)|
            + K / 2 * (θ - (π / 2 - δ)) * (π / 2 - θ) := hmain'
        _ ≤ ((π / 2 - θ) / δ) * th + K / 2 * δ * (π / 2 - θ) := by
            have h1 : ((π / 2 - θ) / δ) * |P z (π / 2 - δ)| ≤ ((π / 2 - θ) / δ) * th :=
              mul_le_mul_of_nonneg_left hrefr (div_nonneg (by linarith [hθ.2]) (le_of_lt hδpos))
            have hXY : θ - (π / 2 - δ) ≤ δ := by linarith [hθ.2]
            have hX : 0 ≤ K / 2 * (π / 2 - θ) := mul_nonneg (by linarith) (by linarith [hθ.2])
            have h2 : K / 2 * (θ - (π / 2 - δ)) * (π / 2 - θ) ≤ K / 2 * δ * (π / 2 - θ) := by
              calc K / 2 * (θ - (π / 2 - δ)) * (π / 2 - θ)
                  = K / 2 * (π / 2 - θ) * (θ - (π / 2 - δ)) := by ring
                _ ≤ K / 2 * (π / 2 - θ) * δ := mul_le_mul_of_nonneg_left hXY hX
                _ = K / 2 * δ * (π / 2 - θ) := by ring
            linarith
        _ = (π / 2 - θ) * (th / δ + K * δ / 2) := by ring_nf
        _ ≤ (π / 2 - θ) * (4 * ε / π) := mul_le_mul_of_nonneg_left hA (by linarith [hθ.2])
        _ = ε * ((4 / π) * (π / 2 - θ)) := by ring
        _ ≤ ε * Real.sin (2 * θ) := by
            rw [hsin2]
            exact mul_le_mul_of_nonneg_left hsin hε.le
        _ = ε * Work.Construction.s2 θ := by rw [Work.Construction.s2_eq]

end Work.FTS_StreamBdry.SB5Aux
