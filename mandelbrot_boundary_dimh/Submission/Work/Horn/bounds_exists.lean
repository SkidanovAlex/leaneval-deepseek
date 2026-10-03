import Mathlib
import Submission.Work.Horn.flower_defs

/-!
# Existence of the quantitative local bounds for a parabolic germ

Given the hypotheses `Work.Horn.Flower.Setup f D q a` of the local Leau–Fatou flower
(`f z = z + a z ^ (q+1) + o (z ^ (q+1))`, `q ≥ 1`, `a ≠ 0`, `f` holomorphic on the open
`D ∋ 0`), this file produces a radius `ρ > 0` with `Work.Horn.Flower.Bounds f D q a ρ`, i.e.

* `B(0,ρ) ⊆ D`;
* `f z = z (1 + z^q H z)` with `H = Hfun f q a` (true by definition);
* `‖f' - 1‖ ≤ 1/2` on `B(0,ρ)`;
* the chart `w = c/z^q` (`c = cc q a = -1/(q a)`) satisfies
  `‖c/(f z)^q - c/z^q - 1‖ ≤ 1/4` on the punctured disc;
* the unit factor `1 + z^q H z` is non-zero on `B(0,ρ)`, its `q`-th power has positive real
  part there, and `|arg (1 + z^q H z)| * q < π`.

Each of these is a *limit statement* at `0`, so all of them follow from the germ hypothesis:
`Hfun f q a → a` at `0` (the germ hypothesis verbatim), from which `1 + z^q H → 1`; and the
chart identity `c/(f z)^q - c/z^q = -c H z · ψ (z^q H z)/(1 + z^q H z)^q`, where
`ψ u = ((1+u)^q - 1)/u` (`= q` at `u = 0`) is the difference quotient of `x ↦ x^q` at `1`,
whose limit is `q`; the limit of the right-hand side is `-c·a·q = 1`.
-/

namespace Work.Horn

open Filter Topology Complex
open Work.Horn.Flower

noncomputable section

namespace BoundsAux

/-- `u ↦ ((1+u)^q - 1)/u`, extended at `u = 0` by `q` (its limit: the derivative of `x ↦ x^q`
at `x = 1`). -/
def psi (q : ℕ) (u : ℂ) : ℂ := if u = 0 then (q : ℂ) else ((1 + u) ^ q - 1) / u

theorem psi_tendsto (q : ℕ) : Tendsto (psi q) (𝓝 (0 : ℂ)) (𝓝 (q : ℂ)) := by
  have hd : HasDerivAt (fun x : ℂ => (1 + x) ^ q) ((q : ℂ)) 0 := by
    have h2 := ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).add (hasDerivAt_id (0 : ℂ))).pow q
    convert h2 using 1
    · ext x; simp
    · simp
  have h3 : Tendsto (fun u : ℂ => ((1 + u) ^ q - 1) / u) (𝓝[≠] (0 : ℂ)) (𝓝 (q : ℂ)) := by
    refine hd.tendsto_slope.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu
    rw [slope_def_field]
    simp
  have hp : Tendsto (psi q) (𝓝[≠] (0 : ℂ)) (𝓝 (q : ℂ)) := by
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu
    simp [psi, hu]
  have hcont : ContinuousAt (psi q) 0 := by
    rw [continuousAt_iff_punctured_nhds]
    simpa [psi] using hp
  have hh := hcont
  rw [ContinuousAt] at hh
  rwa [show psi q 0 = (q : ℂ) by simp [psi]] at hh

/-- `f z = z (1 + z^q Hfun f q a z)`: the defining property of `Hfun`. -/
theorem setup_f_eq {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} (h : Setup f D q a) :
    ∀ z : ℂ, f z = z * (1 + z ^ q * Hfun f q a z) := by
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · rw [Hfun]
    simp [h.hfix]
  · rw [Hfun]
    simp only [hz, ↓reduceIte]
    field_simp
    ring

/-- The germ hypothesis, read as `Hfun f q a → a`. -/
theorem setup_hfun_tendsto {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ}
    (h : Setup f D q a) : Tendsto (Hfun f q a) (𝓝[≠] (0 : ℂ)) (𝓝 a) := by
  have hEq : (fun z : ℂ => (f z - z - a * z ^ (q + 1)) / z ^ (q + 1))
      =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => Hfun f q a z - a) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    rw [Hfun]
    simp only [hz, ↓reduceIte]
    field_simp
  exact tendsto_sub_nhds_zero_iff.mp (h.hgerm.congr' hEq)

/-- `Hfun f q a` is continuous at `0` (with value `a`). -/
theorem setup_hfun_continuousAt {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ}
    (h : Setup f D q a) : ContinuousAt (Hfun f q a) 0 := by
  rw [continuousAt_iff_punctured_nhds]
  simpa [Hfun] using setup_hfun_tendsto h

/-- `1 + z^q Hfun f q a z` is continuous at `0` with value `1`. -/
theorem setup_unit_tendsto {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ}
    (h : Setup f D q a) :
    Tendsto (fun z : ℂ => 1 + z ^ q * Hfun f q a z) (𝓝 (0 : ℂ)) (𝓝 1) := by
  have hWc : ContinuousAt (fun z : ℂ => 1 + z ^ q * Hfun f q a z) 0 :=
    continuousAt_const.add ((continuousAt_id (x := (0 : ℂ))).pow q |>.mul
      (setup_hfun_continuousAt h))
  have h0 : 1 + (0 : ℂ) ^ q * Hfun f q a 0 = 1 := by
    rw [zero_pow (Nat.one_le_iff_ne_zero.mp h.hq), zero_mul, add_zero]
  rw [ContinuousAt] at hWc
  rwa [h0] at hWc

/-- The three unit conditions hold near `0`. -/
theorem setup_unit_eventually {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ}
    (h : Setup f D q a) :
    ∀ᶠ z in 𝓝 (0 : ℂ), (1 + z ^ q * Hfun f q a z ≠ 0) ∧
      (0 < ((1 + z ^ q * Hfun f q a z) ^ q).re) ∧
      |(1 + z ^ q * Hfun f q a z).arg| * (q : ℝ) < Real.pi := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h.hq
    linarith
  have hW : Tendsto (fun z : ℂ => 1 + z ^ q * Hfun f q a z) (𝓝 (0 : ℂ)) (𝓝 1) :=
    setup_unit_tendsto h
  have he1 : ∀ᶠ z in 𝓝 (0 : ℂ), 1 + z ^ q * Hfun f q a z ≠ 0 :=
    hW.eventually (isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0))
  have he2 : ∀ᶠ z in 𝓝 (0 : ℂ), 0 < ((1 + z ^ q * Hfun f q a z) ^ q).re := by
    have hWq : Tendsto (fun z : ℂ => (1 + z ^ q * Hfun f q a z) ^ q) (𝓝 (0 : ℂ)) (𝓝 (1 : ℂ)) :=
      by simpa using hW.pow q
    have hWqr : Tendsto (fun z : ℂ => ((1 + z ^ q * Hfun f q a z) ^ q).re)
        (𝓝 (0 : ℂ)) (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_def, Complex.one_re] using
        (Complex.continuous_re.tendsto (x := (1 : ℂ))).comp hWq
    exact hWqr.eventually ((isOpen_lt continuous_const continuous_id).mem_nhds (by norm_num))
  have he3 : ∀ᶠ z in 𝓝 (0 : ℂ),
      |(1 + z ^ q * Hfun f q a z).arg| * (q : ℝ) < Real.pi := by
    have harg : Tendsto (fun z : ℂ => (1 + z ^ q * Hfun f q a z).arg)
        (𝓝 (0 : ℂ)) (𝓝 (0 : ℝ)) := by
      have h1 : Tendsto Complex.arg (𝓝 (1 : ℂ)) (𝓝 (Complex.arg 1)) :=
        (Complex.continuousAt_arg Complex.one_mem_slitPlane).tendsto
      simpa only [Function.comp_def, Complex.arg_one] using h1.comp hW
    have hε : (0 : ℝ) < Real.pi / (2 * (q : ℝ)) := by positivity
    have h2 := (Metric.tendsto_nhds.mp harg) (Real.pi / (2 * (q : ℝ))) hε
    filter_upwards [h2] with z hz
    rw [Real.dist_eq, sub_zero] at hz
    have h3 : |(1 + z ^ q * Hfun f q a z).arg| * (q : ℝ)
        < Real.pi / (2 * (q : ℝ)) * q := mul_lt_mul_of_pos_right hz hqpos
    have h4 : Real.pi / (2 * (q : ℝ)) * (q : ℝ) = Real.pi / 2 := by field_simp
    rw [h4] at h3
    linarith [Real.pi_pos]
  exact he1.and (he2.and he3)

/-- The germ hypothesis gives `f' 0 = 1`. -/
theorem setup_hasDerivAt {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} (h : Setup f D q a) :
    HasDerivAt f 1 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hzq : Tendsto (fun z : ℂ => z ^ q) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have h' : Tendsto (fun z : ℂ => z ^ q) (𝓝 (0 : ℂ)) (𝓝 ((0 : ℂ) ^ q)) :=
      (tendsto_id (x := 𝓝 (0 : ℂ))).pow q
    rw [zero_pow (Nat.one_le_iff_ne_zero.mp h.hq)] at h'
    exact h'.mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun z : ℂ => z ^ q * ((f z - z - a * z ^ (q + 1)) / z ^ (q + 1)))
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have := hzq.mul h.hgerm
    simpa using this
  have hsum : Tendsto (fun z : ℂ =>
      1 + a * z ^ q + z ^ q * ((f z - z - a * z ^ (q + 1)) / z ^ (q + 1)))
      (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have h1 : Tendsto (fun z : ℂ => 1 + a * z ^ q) (𝓝[≠] (0 : ℂ)) (𝓝 (1 + a * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul hzq)
    have := h1.add hprod
    simpa using this
  have hEq : (fun z : ℂ =>
      1 + a * z ^ q + z ^ q * ((f z - z - a * z ^ (q + 1)) / z ^ (q + 1)))
      =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => f z / z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    field_simp
    ring
  have hslope : Tendsto (fun z : ℂ => f z / z) (𝓝[≠] (0 : ℂ)) (𝓝 1) := hsum.congr' hEq
  refine hslope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
  rw [slope_def_field]
  simp only [sub_zero]
  rw [h.hfix, sub_zero, div_eq_mul_inv, mul_comm]

/-- `deriv f → 1` at `0` (holomorphy upgrades the pointwise derivative `f' 0 = 1`). -/
theorem setup_deriv_eventually {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ}
    (h : Setup f D q a) : ∀ᶠ z in 𝓝 (0 : ℂ), ‖deriv f z - 1‖ ≤ 1 / 2 := by
  have hderiv0 : deriv f 0 = 1 := (setup_hasDerivAt h).deriv
  have hAn : AnalyticAt ℂ (deriv f) 0 := (h.hf.analyticAt (h.hD.mem_nhds h.h0)).deriv
  have hcont : Tendsto (deriv f) (𝓝 (0 : ℂ)) (𝓝 1) := by
    have := hAn.continuousAt
    rwa [ContinuousAt, hderiv0] at this
  have h2 := (Metric.tendsto_nhds.mp hcont) (1 / 2) (by norm_num)
  filter_upwards [h2] with z hz
  rw [dist_eq_norm] at hz
  linarith

/-- The chart limit: `c/(f z)^q - c/z^q → 1`, the "translation in the `w = c/z^q` chart". -/
theorem setup_chartQ_tendsto {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ}
    (h : Setup f D q a) :
    Tendsto (fun z : ℂ => chartQ q a (f z) - chartQ q a z) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
  have hq0 : ((q : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp h.hq)
  have hfe := setup_f_eq h
  have hH : Tendsto (Hfun f q a) (𝓝[≠] (0 : ℂ)) (𝓝 a) := setup_hfun_tendsto h
  have hzq : Tendsto (fun z : ℂ => z ^ q) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have h' : Tendsto (fun z : ℂ => z ^ q) (𝓝 (0 : ℂ)) (𝓝 ((0 : ℂ) ^ q)) :=
      (tendsto_id (x := 𝓝 (0 : ℂ))).pow q
    rw [zero_pow (Nat.one_le_iff_ne_zero.mp h.hq)] at h'
    exact h'.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun z : ℂ => z ^ q * Hfun f q a z) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have := hzq.mul hH
    simpa using this
  have hpsi : Tendsto (fun z : ℂ => psi q (z ^ q * Hfun f q a z))
      (𝓝[≠] (0 : ℂ)) (𝓝 ((q : ℂ))) := by
    have := (psi_tendsto q).comp hu
    simpa only [Function.comp_def] using this
  have hW : Tendsto (fun z : ℂ => 1 + z ^ q * Hfun f q a z) (𝓝[≠] (0 : ℂ)) (𝓝 1) :=
    (setup_unit_tendsto h).mono_left nhdsWithin_le_nhds
  have he1 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), 1 + z ^ q * Hfun f q a z ≠ 0 :=
    ((setup_unit_tendsto h).eventually
      (isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0))).filter_mono nhdsWithin_le_nhds
  have hWq : Tendsto (fun z : ℂ => (1 + z ^ q * Hfun f q a z) ^ q)
      (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have := hW.pow q
    simpa using this
  have hlim : Tendsto (fun z : ℂ => -cc q a * Hfun f q a z * psi q (z ^ q * Hfun f q a z)
      / (1 + z ^ q * Hfun f q a z) ^ q) (𝓝[≠] (0 : ℂ)) (𝓝 (-cc q a * a * (q : ℂ) / 1)) :=
    (((tendsto_const_nhds.mul hH).mul hpsi).div hWq (by norm_num))
  have hval : -cc q a * a * (q : ℂ) / 1 = 1 := by
    rw [div_one, cc]
    field_simp
    exact mul_inv_cancel₀ h.ha
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, he1] with z hz hWne
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
  have hWne2 : 1 + Hfun f q a z * z ^ q ≠ 0 := by
    rw [mul_comm]; exact hWne
  rcases eq_or_ne (z ^ q * Hfun f q a z) 0 with hu0 | hu0
  · have hH0 : Hfun f q a z = 0 := by
      rcases mul_eq_zero.mp hu0 with hh | hh
      · exact absurd hh (pow_ne_zero _ hz)
      · exact hh
    have hfz : f z = z := by rw [hfe z, hH0, mul_zero, add_zero, mul_one]
    have hps0 : psi q (z ^ q * Hfun f q a z) = (q : ℂ) := by simp [psi, hu0]
    rw [hps0, hfz, hH0]
    simp [chartQ]
  · have hH0 : Hfun f q a z ≠ 0 := fun h0 => hu0 (by rw [h0, mul_zero])
    have hψ : psi q (z ^ q * Hfun f q a z)
        = ((1 + z ^ q * Hfun f q a z) ^ q - 1) / (z ^ q * Hfun f q a z) := by
      simp [psi, hu0]
    have hzq' : z ^ q ≠ 0 := pow_ne_zero _ hz
    rw [hψ, hfe z, chartQ, chartQ, mul_pow]
    field_simp
    ring

end BoundsAux

open BoundsAux

theorem bounds_exists {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ}
    (h : Work.Horn.Flower.Setup f D q a) :
    ∃ ρ : ℝ, 0 < ρ ∧ Work.Horn.Flower.Bounds f D q a ρ := by
  obtain ⟨ε, hε, hεD⟩ := Metric.mem_nhds_iff.mp (h.hD.mem_nhds h.h0)
  obtain ⟨ρ₁, hρ₁, hρ₁'⟩ := Metric.eventually_nhds_iff.mp (setup_unit_eventually h)
  obtain ⟨ρ₂, hρ₂, hρ₂'⟩ := Metric.eventually_nhds_iff.mp (setup_deriv_eventually h)
  have hchart : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖chartQ q a (f z) - chartQ q a z - 1‖ ≤ 1 / 4 := by
    have h1 := (Metric.tendsto_nhds.mp (setup_chartQ_tendsto h)) (1 / 4) (by norm_num)
    filter_upwards [h1] with z hz
    rw [dist_eq_norm] at hz
    linarith
  obtain ⟨ρ₃, hρ₃, hρ₃'⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hchart)
  have hρpos : (0 : ℝ) < min (min ρ₁ ρ₂) (min ρ₃ ε) := lt_min (lt_min hρ₁ hρ₂) (lt_min hρ₃ hε)
  refine ⟨min (min ρ₁ ρ₂) (min ρ₃ ε), hρpos, ?_⟩
  have hle₁ : min (min ρ₁ ρ₂) (min ρ₃ ε) ≤ ρ₁ :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hle₂ : min (min ρ₁ ρ₂) (min ρ₃ ε) ≤ ρ₂ :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hle₃ : min (min ρ₁ ρ₂) (min ρ₃ ε) ≤ ρ₃ :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hleε : min (min ρ₁ ρ₂) (min ρ₃ ε) ≤ ε :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨hρpos, fun z hz => hεD (Metric.ball_subset_ball hleε hz), h.hq, h.ha, h.hfix,
    setup_f_eq h, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact hρ₂' (lt_of_lt_of_le (by simpa [Metric.mem_ball, dist_eq_norm] using hz) hle₂)
  · intro z hzpos hzlt
    refine hρ₃' (lt_of_lt_of_le (by simpa using hzlt) hle₃) ?_
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact norm_pos_iff.mp hzpos
  · intro z hz
    exact (hρ₁' (lt_of_lt_of_le (by simpa [Metric.mem_ball, dist_eq_norm] using hz) hle₁)).1
  · intro z hz
    exact (hρ₁' (lt_of_lt_of_le (by simpa [Metric.mem_ball, dist_eq_norm] using hz) hle₁)).2.1
  · intro z hz
    exact (hρ₁' (lt_of_lt_of_le (by simpa [Metric.mem_ball, dist_eq_norm] using hz) hle₁)).2.2

end

end Work.Horn
