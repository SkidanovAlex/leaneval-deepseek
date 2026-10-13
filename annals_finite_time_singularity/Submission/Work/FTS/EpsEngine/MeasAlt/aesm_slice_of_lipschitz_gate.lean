import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EpsEngine.EpsClass
import Submission.Work.FTS.EpsEngine.MeasAlt.EpsLDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.MeasAlt

open MeasureTheory Set Filter

open scoped Topology

set_option maxHeartbeats 1000000

/-! ## The dyadic approximation

For `τ_k s := min δ (⌊2 ^ k * s⌋₊ / 2 ^ k)` we need three things:

* `measurable_dyadicApprox` — for *arbitrary* `F`, `V`, `z`, `θ` the function
  `s ↦ F (V (τ_k s)) z θ` is measurable.  It is the composition of the measurable map
  `⌊2 ^ k ·⌋₊ : ℝ → ℕ` with an arbitrary function on the natural numbers (which are discrete), so
  no measurability of `s ↦ V s` is needed;
* `tau_mem` — `τ_k s ∈ [0,δ]` for `s ∈ [0,δ]` (so that `V (τ_k s) ∈ P`);
* `tau_sub_bounds` — `0 ≤ s - τ_k s ≤ 2^{-k}` on `[0,δ]`.
-/

/-- **The dyadic approximant of the curve is measurable.**  The composition of the measurable map
`⌊2 ^ k ·⌋₊ : ℝ → ℕ` with the arbitrary function `m ↦ F (V (min δ (m / 2 ^ k))) z θ` on the
discrete space `ℕ`. -/
private lemma measurable_dyadicApprox {F : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)} {V : ℝ → ℝ → ℝ → ℝ}
    {δ z θ : ℝ} (k : ℕ) :
    Measurable (fun s : ℝ =>
      F (V (min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k))) z θ) := by
  have h : Measurable ((fun m : ℕ => F (V (min δ ((m : ℝ) / (2 : ℝ) ^ k))) z θ) ∘
      fun s : ℝ => Nat.floor ((2 : ℝ) ^ k * s)) :=
    (measurable_of_countable (fun m : ℕ => F (V (min δ ((m : ℝ) / (2 : ℝ) ^ k))) z θ)).comp
      (Nat.floor_mono.measurable.comp (measurable_const.mul measurable_id))
  simpa only [Function.comp_def] using h

/-- **The dyadic point stays in the horizon**: `min δ (⌊2 ^ k s⌋₊ / 2 ^ k) ∈ [0,δ]` when `δ ≥ 0`. -/
private lemma tau_mem {δ s : ℝ} (hδ : 0 ≤ δ) (k : ℕ) :
    min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k) ∈ Set.Icc (0 : ℝ) δ := by
  have hq : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hfl : (0 : ℝ) ≤ (Nat.floor ((2 : ℝ) ^ k * s) : ℝ) := Nat.cast_nonneg _
  have hx : 0 ≤ (Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k := div_nonneg hfl hq.le
  exact ⟨le_min hδ hx, min_le_left _ _⟩

/-- **The dyadic point does not overshoot**: for `s ∈ [0,δ]` one has `τ_k s ≤ s` and
`s - τ_k s ≤ 2^{-k}`. -/
private lemma tau_sub_bounds {δ s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) δ) (k : ℕ) :
    min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k) ≤ s ∧
    s - min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k) ≤ ((2 : ℝ) ^ k)⁻¹ := by
  have hq : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hs0 : 0 ≤ s := hs.1
  have hfls : (Nat.floor ((2 : ℝ) ^ k * s) : ℝ) ≤ s * (2 : ℝ) ^ k := by
    rw [mul_comm s]; exact Nat.floor_le (mul_nonneg hq.le hs0)
  have hle : (Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k ≤ s := by
    rw [div_le_iff₀ hq]; exact hfls
  have hmin : min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k)
      = (Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k := min_eq_right (hle.trans hs.2)
  constructor
  · rw [hmin]; exact hle
  · rw [hmin]
    have hcast : s * (2 : ℝ) ^ k < (Nat.floor ((2 : ℝ) ^ k * s) : ℝ) + 1 := by
      rw [mul_comm s ((2 : ℝ) ^ k)]; exact Nat.lt_floor_add_one _
    have hone : ((2 : ℝ) ^ k)⁻¹ * (2 : ℝ) ^ k = 1 := inv_mul_cancel₀ (ne_of_gt hq)
    have key : s - ((2 : ℝ) ^ k)⁻¹ ≤ (Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k := by
      rw [le_div_iff₀ hq]
      have hexp : (s - ((2 : ℝ) ^ k)⁻¹) * (2 : ℝ) ^ k = s * (2 : ℝ) ^ k - 1 := by
        rw [sub_mul, hone]
      rw [hexp]
      linarith [hcast]
    linarith [key]

/-- **The Lipschitz gate against the curve itself**: on `[0,δ]` the dyadic approximant differs
from `F (V s) z θ` by at most `Cpt · √Lb · 2^{-k}`, at a point of the open quadrant. -/
private lemma lip_bound {F : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)} {V : ℝ → ℝ → ℝ → ℝ}
    {P : (ℝ → ℝ → ℝ) → Prop} {α δ Cpt Lb z θ : ℝ}
    (hδ : 0 ≤ δ) (hLb : 0 ≤ Lb) (hCpt : 0 ≤ Cpt)
    (hV : ∀ s ∈ Set.Icc 0 δ, P (V s))
    (hpt : ∀ u v : ℝ → ℝ → ℝ, P u → P v → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F u z θ - F v z θ|
        ≤ Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)))
    (hdc : ∀ s t : ℝ, s ∈ Set.Icc 0 δ → t ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsSq α (fun z θ => V s z θ - V t z θ) ≤ Lb * (s - t) ^ 2)
    (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2)
    {s : ℝ} (hs : s ∈ Set.Icc 0 δ) (k : ℕ) :
    |F (V (min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k))) z θ - F (V s) z θ|
      ≤ Cpt * Real.sqrt Lb * ((2 : ℝ) ^ k)⁻¹ := by
  set τ := min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k) with hτdef
  have hτmem : τ ∈ Set.Icc (0 : ℝ) δ := by simpa only [hτdef] using tau_mem (δ := δ) hδ k
  have htb := tau_sub_bounds (δ := δ) hs k
  rw [← hτdef] at htb
  have hEps : Work.FTS.StrongEps.EpsSq α (fun z θ => V τ z θ - V s z θ) ≤ Lb * (s - τ) ^ 2 := by
    have h := hdc τ s hτmem hs
    rwa [show (τ - s) ^ 2 = (s - τ) ^ 2 from by ring] at h
  have hsqrt : Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => V τ z θ - V s z θ))
      ≤ Real.sqrt (Lb * (s - τ) ^ 2) := Real.sqrt_le_sqrt hEps
  have hbound : Real.sqrt (Lb * (s - τ) ^ 2) = Real.sqrt Lb * |s - τ| := by
    rw [Real.sqrt_mul hLb, Real.sqrt_sq_eq_abs]
  have hdiff : |s - τ| ≤ ((2 : ℝ) ^ k)⁻¹ := by
    rw [abs_of_nonneg (sub_nonneg.mpr htb.1)]
    exact htb.2
  calc |F (V τ) z θ - F (V s) z θ|
      ≤ Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => V τ z θ - V s z θ)) :=
        hpt (V τ) (V s) (hV τ hτmem) (hV s hs) z θ hz hθ1 hθ2
    _ ≤ Cpt * Real.sqrt (Lb * (s - τ) ^ 2) := mul_le_mul_of_nonneg_left hsqrt hCpt
    _ = Cpt * (Real.sqrt Lb * |s - τ|) := by rw [hbound]
    _ ≤ Cpt * (Real.sqrt Lb * ((2 : ℝ) ^ k)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ hCpt
        exact mul_le_mul_of_nonneg_left hdiff (Real.sqrt_nonneg _)
    _ = Cpt * Real.sqrt Lb * ((2 : ℝ) ^ k)⁻¹ := by ring

/-- **Measurability in the time variable, from the Lipschitz gate alone** (the
rational-approximation step of the fallback for `EpsEngine.hmeasIter_of_epsClass`).

`V : ℝ → Fn` is a curve of profiles whose values on `[0,δ]` lie in a class `P` on which `F` is
continuous on the open quadrant, vanishes off it, and is pointwise Lipschitz w.r.t. the `EpsSq`
metric (`hpt`).  If moreover `V` is `EpsSq`-Lipschitz in the time variable on `[0,δ]` (`hdc`), then
for every fixed `(z,θ)` the function `s ↦ F (V s) z θ` is a.e. strongly measurable on `[0,δ]`.

Proof (dyadic approximation *against the curve itself*, so no convexity/density/separability is
involved): let `τ_k s := min δ (Nat.floor (2 ^ k * s) / 2 ^ k)`, which on `[0,δ]` takes values in
the *finite* set `{min δ (m / 2 ^ k) : m ≤ Nat.floor (2 ^ k * δ)}` and satisfies
`0 ≤ s - τ_k s ≤ 2^{-k}`; hence
`g_k s := if s ∈ Set.Icc 0 δ then F (V (τ_k s)) z θ else 0` is measurable (a finite sum of
indicators of the measurable level sets `{s ∈ Icc 0 δ : Nat.floor (2 ^ k * s) = m}` times the
constants `F (V (min δ (m / 2 ^ k))) z θ`), and it converges pointwise on `Icc 0 δ` to
`s ↦ F (V s) z θ` by `hpt` + `hdc`; conclude with `aestronglyMeasurable_of_tendsto_ae`. -/
theorem aesm_slice_of_lipschitz_gate {F : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)} {V : ℝ → ℝ → ℝ → ℝ}
    {P : (ℝ → ℝ → ℝ) → Prop} {α δ Cpt Lb : ℝ}
    (hδ : 0 ≤ δ) (hLb : 0 ≤ Lb) (hCpt : 0 ≤ Cpt)
    (hV : ∀ s ∈ Set.Icc 0 δ, P (V s))
    (hcont : ∀ w : ℝ → ℝ → ℝ, P w → ContinuousOn (fun q : ℝ × ℝ => F w q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hzero : ∀ (w : ℝ → ℝ → ℝ) (q : ℝ × ℝ),
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → F w q.1 q.2 = 0)
    (hpt : ∀ u v : ℝ → ℝ → ℝ, P u → P v → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F u z θ - F v z θ|
        ≤ Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)))
    (hdc : ∀ s t : ℝ, s ∈ Set.Icc 0 δ → t ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsSq α (fun z θ => V s z θ - V t z θ) ≤ Lb * (s - t) ^ 2) :
    ∀ z θ : ℝ, MeasureTheory.AEStronglyMeasurable (fun s : ℝ => F (V s) z θ)
      (MeasureTheory.volume.restrict (Set.Icc 0 δ)) := by
  classical
  intro z θ
  by_cases hq : 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2
  · -- on the open quadrant: dyadic approximation against the curve itself
    obtain ⟨hz, hθ1, hθ2⟩ := hq
    have hmeas : ∀ k : ℕ, Measurable (fun s : ℝ =>
        F (V (min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k))) z θ) :=
      fun k => measurable_dyadicApprox k
    have hlim : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc 0 δ)),
        Tendsto (fun k : ℕ =>
            F (V (min δ ((Nat.floor ((2 : ℝ) ^ k * s) : ℝ) / (2 : ℝ) ^ k))) z θ)
          atTop (nhds (F (V s) z θ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have ht : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (nhds 0) :=
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).inv_tendsto_atTop
      have ht2 : Tendsto (fun k : ℕ => (Cpt * Real.sqrt Lb) * ((2 : ℝ) ^ k)⁻¹)
          atTop (nhds 0) := by
        have h2 := ht.const_mul (Cpt * Real.sqrt Lb)
        simpa only [mul_zero] using h2
      refine squeeze_zero (g := fun k : ℕ => (Cpt * Real.sqrt Lb) * ((2 : ℝ) ^ k)⁻¹)
        (fun k => norm_nonneg _) (fun k => ?_) ht2
      rw [Real.norm_eq_abs]
      exact lip_bound hδ hLb hCpt hV hpt hdc hz hθ1 hθ2 hs k
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (hmeas k).aestronglyMeasurable) hlim
  · -- off the open quadrant `F (V s) z θ` vanishes identically
    have hzall : ∀ s : ℝ, F (V s) z θ = 0 := by
      intro s
      have hmem : (z, θ) ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
        intro hmem
        exact hq (by simpa only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] using hmem)
      exact hzero (V s) (z, θ) hmem
    rw [show (fun s : ℝ => F (V s) z θ) = fun _ => (0 : ℝ) from funext hzall]
    exact aestronglyMeasurable_const

end Work.FTS.EpsEngine.MeasAlt
