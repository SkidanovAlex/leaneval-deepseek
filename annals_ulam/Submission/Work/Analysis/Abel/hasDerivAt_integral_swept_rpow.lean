import Mathlib
import Submission.Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuousOn_of_le
import Submission.Work.Analysis.Abel.continuousOn_deriv_slice_fst
import Submission.Work.Analysis.Abel.continuousOn_deriv_slice_snd
import Submission.Work.Analysis.Abel.hasDerivAt_diag_of_contDiffOn
import Submission.Work.Analysis.Abel.hasFDerivAt_integral_upper_of_continuousOn
import Submission.Work.Analysis.Abel.integral_rpow_mul_deriv_slice_eq

namespace Work.Analysis.Abel

open MeasureTheory Set Filter
open scoped Topology Interval

/-- **Differentiation of a swept integral with a fractional-power kernel (one step).**

Let `q > 0`, `x₀ < b` (in the sharpened form `x₀ + R < b` with `R > 0`), and let
`B : ℝ → ℝ → ℝ` be jointly `C¹` near the region swept by `{(x,σ) : x ≈ x₀, σ ∈ [x, b]}`, as
made precise by the hypothesis that the uncurried `(x,σ) ↦ B x σ` is `C¹` on the open box
`(x₀-R, x₀+R) × (x₀-2R, b+R)`. Then

`x ↦ ∫_x^b (σ - x)^q B(x,σ) dσ`

is differentiable at `x₀` with derivative

`∫_{x₀}^b ((σ - x₀)^q ∂_1 B(x₀,σ) - q (σ - x₀)^{q-1} B(x₀,σ)) dσ`,

where `∂_1 B(x₀,σ) = deriv (fun x' => B x' σ) x₀` is the derivative of the slice. (Note
`q - 1 ∈ (-1, 0)` is allowed, so the second summand has an integrable `(σ-x₀)^{q-1}`
singularity — this is the case where the moving-limit boundary term vanishes and one cannot
apply the standard continuous-parametric lemmas directly.)

Proof sketch: substitute `σ = x + y` with `y ∈ [0, b-x]`. Then the integral is `Φ(x, b-x)`
where `Φ(x,L) = ∫_0^L y^q B(x, x+y) dy`. Show `Φ` has Fréchet derivative
`(h₁,h₂) ↦ h₁ ∫_0^{L₀} y^q (∂_1B + ∂_2B)(x₀, x₀+y) dy + h₂ L₀^q B(x₀, b)` at `(x₀, L₀)`,
`L₀ = b - x₀`: split `Φ = Ψ + Θ` with `Ψ(x) = ∫_0^{L₀} y^q B(x,x+y) dy` (fixed interval —
differentiate under the integral sign with `Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuousOn_of_le`
(import `Submission.Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuousOn_of_le`),
valid because `y^q (∂_1B+∂_2B)(x,x+y)` is continuous on the compact box for `q > 0`) and
`Θ(x,L) = ∫_{L₀}^{L} y^q B(x,x+y) dy` (a corner at `(x₀,L₀)` with `L₀ > 0`; the little-`o`
estimate only uses joint continuity there, cf.
`Commons.Analysis.Calculus.intervalIntegral_hasFDerivAt_upper_continuous` in
`Submission/Commons/Analysis/Calculus/intervalIntegral_hasDerivAt_upper_piece_of_continuous.lean`).
Then differentiate the curve `x ↦ (x, b-x)` and use the integration by parts in `y`
(`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto` on `[0,L₀]`)
`∫_0^{L₀} y^q ∂_2B(x₀,x₀+y) dy = L₀^q B(x₀,b) - ∫_0^{L₀} q y^{q-1} B(x₀,x₀+y) dy`,
in which `[y^q B(x₀,x₀+y)]_0^{L₀} = L₀^q B(x₀,b)` (`0^q = 0` for `q ≠ 0`) cancels the endpoint
term `-L₀^q B(x₀,b)` of `∂_L Φ`. Finally substitute back `σ = x₀ + y`.-/
theorem hasDerivAt_integral_swept_rpow
    {q : ℝ} (hq : 0 < q) {b x₀ R : ℝ} (hR : 0 < R) (hRb : x₀ + R < b)
    {B : ℝ → ℝ → ℝ}
    (hB : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => B p.1 p.2)
      (Set.Ioo (x₀ - R) (x₀ + R) ×ˢ Set.Ioo (x₀ - 2 * R) (b + R))) :
    HasDerivAt (fun x : ℝ => ∫ σ in x..b, (σ - x) ^ q * B x σ)
      (∫ σ in x₀..b, ((σ - x₀) ^ q * deriv (fun x' : ℝ => B x' σ) x₀
        - q * (σ - x₀) ^ (q - 1) * B x₀ σ)) x₀ := by
  set L₀ : ℝ := b - x₀ with hL₀def
  set δ : ℝ := R / 4 with hδdef
  set U : Set (ℝ × ℝ) := Set.Ioo (x₀ - R) (x₀ + R) ×ˢ Set.Ioo (x₀ - 2 * R) (b + R) with hUdef
  set Gd : ℝ → ℝ → ℝ := fun x y => y ^ q * B x (x + y) with hGddef
  set Gp : ℝ → ℝ → ℝ := fun x y =>
    y ^ q * (deriv (fun u : ℝ => B u (x + y)) x + deriv (fun v : ℝ => B x v) (x + y)) with hGpdef
  have hL₀ : 0 < L₀ := by rw [hL₀def]; linarith
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδR : δ < R := by rw [hδdef]; linarith
  have h2δR : 2 * δ < R := by rw [hδdef]; linarith
  have hδ2R : δ < 2 * R := by rw [hδdef]; linarith
  have hbL₀ : x₀ + L₀ = b := by rw [hL₀def]; ring
  have hU : IsOpen U := by rw [hUdef]; exact isOpen_Ioo.prod isOpen_Ioo
  have hBU : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => B p.1 p.2) U := by rw [hUdef]; exact hB
  -- ## Continuity of the partial derivatives of `B`
  have hP₁ : ContinuousOn (fun r : ℝ × ℝ => deriv (fun u : ℝ => B u r.2) r.1) U :=
    continuousOn_deriv_slice_fst hU hBU
  have hP₂ : ContinuousOn (fun r : ℝ × ℝ => deriv (fun v : ℝ => B r.1 v) r.2) U :=
    continuousOn_deriv_slice_snd hU hBU
  have hdiag : Continuous (fun p : ℝ × ℝ => (p.1, p.1 + p.2)) :=
    continuous_fst.prodMk (continuous_fst.add continuous_snd)
  -- ## Containment facts
  have hbox : ∀ x ∈ Set.Icc (x₀ - δ) (x₀ + δ), ∀ y ∈ Set.Icc (0 : ℝ) (max L₀ (b - x)),
      (x, x + y) ∈ U := by
    intro x hx y hy
    rw [hUdef]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · linarith [hx.1, hδR]
    · linarith [hx.2, hδR]
    · have h1 : x₀ - δ ≤ x + y := by linarith [hx.1, hy.1]
      linarith [hδ2R]
    · have h2 : x + y ≤ b + δ := by
        rcases max_cases L₀ (b - x) with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he] at hy
          have : x + L₀ ≤ b + δ := by linarith [hx.2, hbL₀]
          linarith [hy.2]
        · rw [he] at hy
          linarith [hy.2, hδ]
      linarith [h2, hδR]
  have hboxIcc : ∀ x ∈ Set.Icc (x₀ - δ) (x₀ + δ), ∀ y ∈ Set.Icc (0 : ℝ) L₀, (x, x + y) ∈ U :=
    fun x hx y hy => hbox x hx y ⟨hy.1, le_trans hy.2 (le_max_left _ _)⟩
  have huIccIcc : ∀ y ∈ Set.uIcc (0 : ℝ) L₀, y ∈ Set.Icc (0 : ℝ) L₀ := by
    intro y hy
    rcases mem_uIcc.mp hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
    · exact ⟨le_trans hL₀.le h1, le_trans h2 hL₀.le⟩
  have hvert : ∀ y ∈ Set.Icc (0 : ℝ) L₀, (x₀, x₀ + y) ∈ U := by
    intro y hy
    rw [hUdef]
    exact ⟨⟨by linarith [hR], by linarith [hR]⟩,
      ⟨by linarith [hy.1, hR], by linarith [hy.2, hR]⟩⟩
  -- ## Step 1: substitution `σ = x + y`
  have hsubst : ∀ x : ℝ, (∫ σ in x..b, (σ - x) ^ q * B x σ)
      = ∫ y in (0 : ℝ)..(b - x), Gd x y := by
    intro x
    have h := intervalIntegral.integral_comp_add_right
      (f := fun σ : ℝ => (σ - x) ^ q * B x σ) (a := (0 : ℝ)) (b := b - x) (d := x)
    have h' : (∫ y in (0 : ℝ)..(b - x), (y + x - x) ^ q * B x (y + x))
        = ∫ σ in x..b, (σ - x) ^ q * B x σ := by
      simpa using h
    rw [hGddef, ← h']
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    simp only [add_comm y x, add_sub_cancel_left]
  -- ## Step 2: differentiate `Ψ`
  have hboxdiag : MapsTo (fun p : ℝ × ℝ => (p.1, p.1 + p.2))
      (Set.Icc (x₀ - δ) (x₀ + δ) ×ˢ Set.Icc (0 : ℝ) L₀) U :=
    fun p hp => hboxIcc p.1 hp.1 p.2 hp.2
  have hFcont : ContinuousOn (fun p : ℝ × ℝ => Gd p.1 p.2)
      (Set.Icc (x₀ - δ) (x₀ + δ) ×ˢ Set.Icc (0 : ℝ) L₀) := by
    rw [hGddef]
    have hpow : ContinuousOn (fun p : ℝ × ℝ => p.2 ^ q)
        (Set.Icc (x₀ - δ) (x₀ + δ) ×ˢ Set.Icc (0 : ℝ) L₀) :=
      (Real.continuous_rpow_const hq.le).comp_continuousOn continuous_snd.continuousOn
    have hBc : ContinuousOn (fun p : ℝ × ℝ => B p.1 (p.1 + p.2))
        (Set.Icc (x₀ - δ) (x₀ + δ) ×ˢ Set.Icc (0 : ℝ) L₀) :=
      hBU.continuousOn.comp hdiag.continuousOn hboxdiag
    exact (hpow.mul hBc).congr (fun p _ => by simp [Pi.mul_apply])
  have hF'cont : ContinuousOn (fun p : ℝ × ℝ => Gp p.1 p.2)
      (Set.Icc (x₀ - δ) (x₀ + δ) ×ˢ Set.Icc (0 : ℝ) L₀) := by
    rw [hGpdef]
    have hpow : ContinuousOn (fun p : ℝ × ℝ => p.2 ^ q)
        (Set.Icc (x₀ - δ) (x₀ + δ) ×ˢ Set.Icc (0 : ℝ) L₀) :=
      (Real.continuous_rpow_const hq.le).comp_continuousOn continuous_snd.continuousOn
    have h1 : ContinuousOn (fun p : ℝ × ℝ => deriv (fun u : ℝ => B u (p.1 + p.2)) p.1)
        (Set.Icc (x₀ - δ) (x₀ + δ) ×ˢ Set.Icc (0 : ℝ) L₀) :=
      hP₁.comp hdiag.continuousOn hboxdiag
    have h2 : ContinuousOn (fun p : ℝ × ℝ => deriv (fun v : ℝ => B p.1 v) (p.1 + p.2))
        (Set.Icc (x₀ - δ) (x₀ + δ) ×ˢ Set.Icc (0 : ℝ) L₀) :=
      hP₂.comp hdiag.continuousOn hboxdiag
    exact (hpow.mul (h1.add h2)).congr (fun p _ => by simp [Pi.mul_apply, Pi.add_apply])
  have hd : ∀ s ∈ Set.Icc (x₀ - δ) (x₀ + δ), ∀ t ∈ Set.Icc (0 : ℝ) L₀,
      HasDerivAt (fun u : ℝ => Gd u t) (Gp s t) s := by
    intro s hs t ht
    have hpt : (s, s + t) ∈ U := hboxIcc s hs t ht
    have h := hasDerivAt_diag_of_contDiffOn hU hBU hpt
    rw [hGddef, hGpdef]
    exact h.const_mul (t ^ q)
  have hΨ : HasDerivAt (fun s : ℝ => ∫ y in (0 : ℝ)..L₀, Gd s y)
      (∫ y in (0 : ℝ)..L₀, Gp x₀ y) x₀ :=
    Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuousOn_of_le
      (F := Gd) (F' := Gp) (s₀ := x₀) (a := (0 : ℝ)) (b := L₀) (s₁ := x₀ - δ) (s₂ := x₀ + δ)
      (by linarith [hδ]) (by linarith [hδ]) hL₀.le hFcont hF'cont hd
  -- ## Step 3: differentiate `Θ` (moving upper endpoint), boundary term
  have hboxΘdiag : MapsTo (fun p : ℝ × ℝ => (p.1, p.1 + p.2))
      (Set.Icc (x₀ - δ) (x₀ + δ) ×ˢ Set.Icc (L₀ - δ) (L₀ + δ)) U := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    rw [hUdef]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · linarith [hx.1, hδR]
    · linarith [hx.2, hδR]
    · have h1 : L₀ - δ ≤ y := hy.1
      have h2 : x₀ - δ ≤ x := hx.1
      have h3 : b - 2 * δ ≤ x + y := by linarith [hbL₀]
      linarith [h2δR, hL₀]
    · have h1 : y ≤ L₀ + δ := hy.2
      have h2 : x ≤ x₀ + δ := hx.2
      have h3 : x + y ≤ b + 2 * δ := by linarith [hbL₀]
      linarith [h2δR]
  have hΘboxcont : ContinuousOn (fun p : ℝ × ℝ => Gd p.1 p.2)
      (Set.Icc (x₀ - δ) (x₀ + δ) ×ˢ Set.Icc (L₀ - δ) (L₀ + δ)) := by
    rw [hGddef]
    have hpow : ContinuousOn (fun p : ℝ × ℝ => p.2 ^ q)
        (Set.Icc (x₀ - δ) (x₀ + δ) ×ˢ Set.Icc (L₀ - δ) (L₀ + δ)) :=
      (Real.continuous_rpow_const hq.le).comp_continuousOn continuous_snd.continuousOn
    have hBc : ContinuousOn (fun p : ℝ × ℝ => B p.1 (p.1 + p.2))
        (Set.Icc (x₀ - δ) (x₀ + δ) ×ˢ Set.Icc (L₀ - δ) (L₀ + δ)) :=
      hBU.continuousOn.comp hdiag.continuousOn hboxΘdiag
    exact (hpow.mul hBc).congr (fun p _ => by simp [Pi.mul_apply])
  have hΘfd : HasFDerivAt (fun p : ℝ × ℝ => ∫ t in L₀..p.2, Gd p.1 t)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Gd x₀ L₀)) (x₀, L₀) :=
    hasFDerivAt_integral_upper_of_continuousOn (F := Gd) (x₀ := x₀) (b₀ := L₀)
      (x₁ := x₀ - δ) (x₂ := x₀ + δ) (c := L₀ - δ) (d := L₀ + δ)
      (by linarith [hδ]) (by linarith [hδ]) (by linarith [hδ]) (by linarith [hδ]) hΘboxcont
  have hcurve2 : HasDerivAt (fun x : ℝ => (x, b - x)) (1, -1) x₀ := by
    have h1 : HasDerivAt (fun x : ℝ => b - x) (-1) x₀ := by
      simpa using (hasDerivAt_id x₀).const_sub b
    exact (hasDerivAt_id x₀).prodMk h1
  have hΘcomp := hΘfd.comp_hasDerivAt x₀ hcurve2
  have hvalΘ : ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Gd x₀ L₀)) (1, -1)
      = -(L₀ ^ q * B x₀ b) := by
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd', smul_eq_mul,
      hGddef, hbL₀]
    ring
  have hΘ : HasDerivAt (fun x : ℝ => ∫ y in L₀..(b - x), Gd x y) (-(L₀ ^ q * B x₀ b)) x₀ :=
    (hΘcomp.congr_deriv hvalΘ).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun x => by simp [Function.comp_apply]))
  -- ## Step 4: assemble `Ψ + Θ`, splitting at `L₀`
  have hev : (fun x : ℝ => ∫ y in (0 : ℝ)..(b - x), Gd x y) =ᶠ[𝓝 x₀]
      (fun x : ℝ => (∫ y in (0 : ℝ)..L₀, Gd x y) + ∫ y in L₀..(b - x), Gd x y) := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show x₀ ∈ Set.Ioo (x₀ - δ) (x₀ + δ) from ⟨by linarith [hδ], by linarith [hδ]⟩)] with x hx
    have hxc : x ∈ Set.Icc (x₀ - δ) (x₀ + δ) := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hcurve : Continuous (fun y : ℝ => (x, x + y)) :=
      continuous_const.prodMk (continuous_const.add continuous_id)
    have h1 : IntervalIntegrable (Gd x) volume (0 : ℝ) L₀ := by
      rw [hGddef]
      have hmaps : MapsTo (fun y : ℝ => (x, x + y)) (Set.uIcc (0 : ℝ) L₀) U :=
        fun y hy => hbox x hxc y
          ⟨(huIccIcc y hy).1, le_trans (huIccIcc y hy).2 (le_max_left _ _)⟩
      have hb : ContinuousOn (fun y : ℝ => B x (x + y)) (Set.uIcc (0 : ℝ) L₀) :=
        hBU.continuousOn.comp hcurve.continuousOn hmaps
      have hp : ContinuousOn (fun y : ℝ => y ^ q) (Set.uIcc (0 : ℝ) L₀) :=
        (Real.continuous_rpow_const hq.le).comp_continuousOn continuousOn_id
      exact ((hp.mul hb).congr (fun y _ => by simp [Pi.mul_apply])).intervalIntegrable
    have h2 : IntervalIntegrable (Gd x) volume L₀ (b - x) := by
      rw [hGddef]
      have hbx : 0 < b - x := by linarith [hx.2, hδR, hRb]
      have hmaps : MapsTo (fun y : ℝ => (x, x + y)) (Set.uIcc L₀ (b - x)) U := by
        intro y hy
        rcases mem_uIcc.mp hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hbox x hxc y ⟨le_trans hL₀.le h1, le_trans h2 (le_max_right _ _)⟩
        · exact hbox x hxc y ⟨le_trans hbx.le h1, le_trans h2 (le_max_left _ _)⟩
      have hb : ContinuousOn (fun y : ℝ => B x (x + y)) (Set.uIcc L₀ (b - x)) :=
        hBU.continuousOn.comp hcurve.continuousOn hmaps
      have hp : ContinuousOn (fun y : ℝ => y ^ q) (Set.uIcc L₀ (b - x)) :=
        (Real.continuous_rpow_const hq.le).comp_continuousOn continuousOn_id
      exact ((hp.mul hb).congr (fun y _ => by simp [Pi.mul_apply])).intervalIntegrable
    exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
  -- ## Step 5: identify the derivative value
  set D₁ : ℝ := ∫ y in (0 : ℝ)..L₀, y ^ q * deriv (fun u : ℝ => B u (x₀ + y)) x₀ with hD₁def
  set D₂ : ℝ := ∫ y in (0 : ℝ)..L₀, y ^ q * deriv (fun v : ℝ => B x₀ v) (x₀ + y) with hD₂def
  set B₂ : ℝ := ∫ y in (0 : ℝ)..L₀, q * y ^ (q - 1) * B x₀ (x₀ + y) with hB₂def
  have hIntf : IntervalIntegrable
      (fun y : ℝ => y ^ q * deriv (fun u : ℝ => B u (x₀ + y)) x₀) volume (0 : ℝ) L₀ := by
    have hp : ContinuousOn (fun y : ℝ => y ^ q) (Set.uIcc (0 : ℝ) L₀) :=
      (Real.continuous_rpow_const hq.le).comp_continuousOn continuousOn_id
    have hd1 : ContinuousOn (fun y : ℝ => deriv (fun u : ℝ => B u (x₀ + y)) x₀)
        (Set.uIcc (0 : ℝ) L₀) :=
      hP₁.comp ((continuous_const.prodMk (continuous_const.add continuous_id)).continuousOn)
        (fun y hy => hvert y (huIccIcc y hy))
    exact (hp.mul hd1).intervalIntegrable
  have hIntg' : IntervalIntegrable
      (fun y : ℝ => y ^ q * deriv (fun v : ℝ => B x₀ v) (x₀ + y)) volume (0 : ℝ) L₀ := by
    have hp : ContinuousOn (fun y : ℝ => y ^ q) (Set.uIcc (0 : ℝ) L₀) :=
      (Real.continuous_rpow_const hq.le).comp_continuousOn continuousOn_id
    have hd2 : ContinuousOn (fun y : ℝ => deriv (fun v : ℝ => B x₀ v) (x₀ + y))
        (Set.uIcc (0 : ℝ) L₀) :=
      hP₂.comp ((continuous_const.prodMk (continuous_const.add continuous_id)).continuousOn)
        (fun y hy => hvert y (huIccIcc y hy))
    exact (hp.mul hd2).intervalIntegrable
  have hIntg : IntervalIntegrable
      (fun y : ℝ => q * y ^ (q - 1) * B x₀ (x₀ + y)) volume (0 : ℝ) L₀ := by
    have hbase : IntervalIntegrable (fun y : ℝ => y ^ (q - 1)) volume (0 : ℝ) L₀ :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < q - 1)
    have hBc : ContinuousOn (fun y : ℝ => B x₀ (x₀ + y)) (Set.uIcc (0 : ℝ) L₀) :=
      hBU.continuousOn.comp ((continuous_const.prodMk (continuous_const.add continuous_id)).continuousOn)
        (fun y hy => hvert y (huIccIcc y hy))
    simpa only [mul_assoc] using (hbase.mul_continuousOn hBc).const_mul q
  have hsplit : (∫ y in (0 : ℝ)..L₀, Gp x₀ y) = D₁ + D₂ := by
    have heq : (fun y : ℝ => Gp x₀ y) = fun y : ℝ =>
        (y ^ q * deriv (fun u : ℝ => B u (x₀ + y)) x₀)
          + (y ^ q * deriv (fun v : ℝ => B x₀ v) (x₀ + y)) := by
      funext y
      rw [hGpdef]
      simp only [mul_add]
    rw [heq, intervalIntegral.integral_add hIntf hIntg', hD₁def, hD₂def]
  have hIBP : D₂ = L₀ ^ q * B x₀ b - B₂ := by
    rw [hD₂def, hB₂def]
    have h := integral_rpow_mul_deriv_slice_eq (q := q) hq (B := B) (x₀ := x₀) (L₀ := L₀)
      (x₁ := x₀ - R) (x₂ := x₀ + R) (c := x₀ - 2 * R) (d := b + R)
      (by linarith [hR]) (by linarith [hR]) (by linarith [hR]) (by linarith [hR]) hL₀ hB
    rw [h, hbL₀]
  have hsubAll : (∫ σ in x₀..b, ((σ - x₀) ^ q * deriv (fun x' : ℝ => B x' σ) x₀
        - q * (σ - x₀) ^ (q - 1) * B x₀ σ))
      = ∫ y in (0 : ℝ)..L₀, (y ^ q * deriv (fun u : ℝ => B u (x₀ + y)) x₀
        - q * y ^ (q - 1) * B x₀ (x₀ + y)) := by
    have h := intervalIntegral.integral_comp_add_right
      (f := fun σ : ℝ => (σ - x₀) ^ q * deriv (fun x' : ℝ => B x' σ) x₀
        - q * (σ - x₀) ^ (q - 1) * B x₀ σ) (a := (0 : ℝ)) (b := L₀) (d := x₀)
    have h' : (∫ y in (0 : ℝ)..L₀, ((y + x₀ - x₀) ^ q * deriv (fun x' : ℝ => B x' (y + x₀)) x₀
          - q * (y + x₀ - x₀) ^ (q - 1) * B x₀ (y + x₀)))
        = ∫ σ in x₀..b, ((σ - x₀) ^ q * deriv (fun x' : ℝ => B x' σ) x₀
          - q * (σ - x₀) ^ (q - 1) * B x₀ σ) := by
      simpa [hL₀def] using h
    rw [← h']
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    simp only [add_comm y x₀, add_sub_cancel_left]
  have hsplitY : (∫ y in (0 : ℝ)..L₀, (y ^ q * deriv (fun u : ℝ => B u (x₀ + y)) x₀
        - q * y ^ (q - 1) * B x₀ (x₀ + y))) = D₁ - B₂ := by
    rw [intervalIntegral.integral_sub hIntf hIntg, hD₁def, hB₂def]
  have hfinal : D₁ + D₂ - L₀ ^ q * B x₀ b
      = ∫ σ in x₀..b, ((σ - x₀) ^ q * deriv (fun x' : ℝ => B x' σ) x₀
        - q * (σ - x₀) ^ (q - 1) * B x₀ σ) := by
    rw [hsubAll, hsplitY, hIBP]
    ring
  have hder : (∫ y in (0 : ℝ)..L₀, Gp x₀ y) + (-(L₀ ^ q * B x₀ b))
      = D₁ + D₂ - L₀ ^ q * B x₀ b := by
    rw [hsplit]; ring
  have hΦ : HasDerivAt (fun x : ℝ => ∫ y in (0 : ℝ)..(b - x), Gd x y)
      (D₁ + D₂ - L₀ ^ q * B x₀ b) x₀ :=
    (hΨ.add hΘ).congr_deriv hder |>.congr_of_eventuallyEq hev
  have hmain : HasDerivAt (fun x : ℝ => ∫ σ in x..b, (σ - x) ^ q * B x σ)
      (D₁ + D₂ - L₀ ^ q * B x₀ b) x₀ :=
    hΦ.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => hsubst x))
  exact hmain.congr_deriv hfinal

end Work.Analysis.Abel
