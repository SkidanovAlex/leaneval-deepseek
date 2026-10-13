import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.sliceInterp
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.remov.pth_zero_of_HkMem
import Submission.Work.FTS.EllipticEst.Honest.derivDeriv_divCos

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The three ingredients

The proof of `psiDerivSq_lower` below is assembled from the three lemmas of this section:

* `integrableOn_sq_mul_sig_of_hkMem` extracts, from the `H^0`-honesty `HkMem α 0 g` and for
  `z > 0`, the `θ`-integrability of the single weighted square `g z θ² · σ θ` (the constant
  factor `w z² ≠ 0` of the level-`0` `HkIntegrand` is divided out);
* `deriv_divCos_eq` is the quotient rule for the slice variable `θ ↦ u θ / cos θ`;
* `div_cos_sq_le` is the numerical core `((a + t b)/c)² ≤ 4 (a² + b²)` valid when
  `0 < c`, `c² ≥ 1/2` and `t² ≤ 1` — precisely the regime `θ ∈ (0, π/4)` with
  `c = cos θ`, `t = tan θ`.

Their combination (`psi_deriv_sq_le`) is the pointwise bound `(ψ')² ≤ 4 f'² + 4 f²` on
`(0, π/4)`, which together with `Honest.sliceInterp` (giving `f'²σ ∈ L¹` from `f²σ`, `f''²σ`)
and `Integrable.mono'` yields the target. -/

/-- **Slice honesty of the level-`0` `HkMem`.**  For `z > 0` the single weighted square
`g z θ² · σ θ` (`σ = sin(2θ)^{-η}`) is integrable on `Iθ`.

At level `0` the `HkIntegrand` is `(g z θ · w z / sin(2θ)^{η/2})²`, i.e. `w z²` times the
present integrand (`remov.HkIntegrand_zero_eq`); since `w z ≠ 0` for `z > 0`, the constant
`w z²` can be divided out. -/
lemma integrableOn_sq_mul_sig_of_hkMem {α z : ℝ} {g : ℝ → ℝ → ℝ} (hz : 0 < z)
    (hmem : Work.Spaces.HkMem α 0 g) :
    MeasureTheory.IntegrableOn
      (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    have h1 : Work.Spaces.w z ≠ 0 := by
      rw [Work.Spaces.w]
      exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
    exact pow_ne_zero 2 h1
  have hbase : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 0 g z θ * ((Work.Spaces.w z) ^ 2)⁻¹)
      Work.Spaces.Iθ :=
    (hmem.1 z hzI).mul_const _
  refine hbase.congr_fun (fun θ hθ => ?_) measurableSet_Icc
  show Work.Spaces.HkIntegrand α 0 g z θ * ((Work.Spaces.w z) ^ 2)⁻¹
    = (g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
  rw [Work.FTS.EllipticEst.remov.HkIntegrand_zero_eq α g z hθ,
    Work.FTS.EllipticEst.AngSecond.sig]
  calc (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
        * ((Work.Spaces.w z) ^ 2)⁻¹
      = (g z θ) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
          * ((Work.Spaces.w z) ^ 2 * ((Work.Spaces.w z) ^ 2)⁻¹) := by ring
    _ = (g z θ) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta) := by
        rw [mul_inv_cancel₀ hw, mul_one]

/-- **The quotient rule for the slice variable.**  If the slice `u` is differentiable at `θ` and
`cos θ ≠ 0`, then `∂_θ(u/cos θ) = (u' + tan θ · u)/cos θ` at `θ`. -/
lemma deriv_divCos_eq (u : ℝ → ℝ) {θ : ℝ} (hu : DifferentiableAt ℝ u θ)
    (hcos : Real.cos θ ≠ 0) :
    deriv (fun t => u t / Real.cos t) θ
      = (deriv u θ + Real.tan θ * u θ) / Real.cos θ := by
  change deriv (u / Real.cos) θ = (deriv u θ + Real.tan θ * u θ) / Real.cos θ
  rw [deriv_div hu Real.differentiableAt_cos hcos, Real.deriv_cos, Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- **Numerical core.**  If `0 < c`, `c² ≥ 1/2` and `t² ≤ 1` then `((a + t b)/c)² ≤ 4(a² + b²)`.
On `(0, π/4)` the hypotheses hold with `c = cos θ`, `t = tan θ`. -/
lemma div_cos_sq_le (a b t c : ℝ) (hc : 0 < c) (hc2 : (1 : ℝ) / 2 ≤ c ^ 2)
    (ht : t ^ 2 ≤ 1) : ((a + t * b) / c) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  have hc2pos : (0 : ℝ) < c ^ 2 := pow_pos hc 2
  have hsqab : (0 : ℝ) ≤ a ^ 2 + b ^ 2 := by positivity
  have hAB : (a + t * b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (a - t * b)]
  have hfac : (2 : ℝ) * (a ^ 2 + b ^ 2) ≤ 4 * (a ^ 2 + b ^ 2) * c ^ 2 := by
    have h1 : ((1 : ℝ) / 2) * (a ^ 2 + b ^ 2) ≤ c ^ 2 * (a ^ 2 + b ^ 2) :=
      mul_le_mul_of_nonneg_right hc2 hsqab
    linarith
  rw [div_pow, div_le_iff₀ hc2pos]
  linarith

/-- **The pointwise bound on the derivative of the slice variable** on the lower half
`(0, π/4)`.  For a slice `θ ↦ Ψ z θ` that is `C²` on `(0, π/2)`:

  `(∂_θ(Ψ z ·/cos))² ≤ 4 (∂_θΨ z ·)² + 4 (Ψ z ·)²`. -/
lemma psi_deriv_sq_le {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hslice : ContDiffOn ℝ 2 (fun t => Ψ z t) (Set.Ioo 0 (Real.pi / 2)))
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    (deriv (fun t => Ψ z t / Real.cos t) θ) ^ 2
      ≤ 4 * (deriv (fun t => Ψ z t) θ) ^ 2 + 4 * (Ψ z θ) ^ 2 := by
  obtain ⟨hθ0, hθ4⟩ := hθ
  have hθmid : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hθ0, by linarith [hθ4, Real.pi_pos]⟩
  have hcosp : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [hθmid.2, Real.pi_pos]⟩
  have hcosne : Real.cos θ ≠ 0 := ne_of_gt hcosp
  have hd : DifferentiableAt ℝ (fun t => Ψ z t) θ :=
    (hslice.contDiffAt (isOpen_Ioo.mem_nhds hθmid)).differentiableAt (by simp)
  have hcos2 : (1 : ℝ) / 2 ≤ Real.cos θ ^ 2 := by
    rw [Real.cos_sq]
    have h2 : 0 ≤ Real.cos (2 * θ) :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [Real.pi_pos], by linarith [hθmid.2, Real.pi_pos]⟩
    linarith
  have htan2 : (Real.tan θ) ^ 2 ≤ 1 := by
    have hmono : Real.tan θ < Real.tan (Real.pi / 4) :=
      Real.strictMonoOn_tan
        ⟨by linarith [Real.pi_pos], by linarith [hθmid.2, Real.pi_pos]⟩
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hθ4
    rw [Real.tan_pi_div_four] at hmono
    have hnn : 0 ≤ Real.tan θ :=
      Real.tan_nonneg_of_nonneg_of_le_pi_div_two hθ0.le (by linarith [hθmid.2])
    nlinarith
  rw [deriv_divCos_eq (fun t => Ψ z t) hd hcosne]
  have hkey := div_cos_sq_le (deriv (fun t => Ψ z t) θ) (Ψ z θ) (Real.tan θ) (Real.cos θ)
    hcosp hcos2 htan2
  nlinarith [hkey]

/-- The slice `θ ↦ Ψ z θ` of a function that is smooth on the open strip `(0,∞) × (0,π/2)` is
`Cⁿ` on the open interval `(0, π/2)`. -/
lemma contDiffOn_slice_of_strip {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) {z : ℝ} (hz : 0 < z) (n : ℕ) :
    ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
  have hp : ContDiffOn ℝ n (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_const.prodMk contDiffOn_id
  have h := (hsm n).comp hp hmap
  simpa [Function.comp_def, Function.uncurry] using h

/-- The slice variable `θ ↦ Ψ z θ / cos θ` is `C²` on `(0, π/2)` whenever the slice itself
is. -/
lemma contDiffOn_divCos {Ψ : ℝ → ℝ → ℝ} {z : ℝ}
    (hslice : ContDiffOn ℝ 2 (fun t => Ψ z t) (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 2 (fun t => Ψ z t / Real.cos t) (Set.Ioo 0 (Real.pi / 2)) :=
  hslice.div Real.contDiff_cos.contDiffOn (fun t ht =>
    ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩))

/-- `σ = sin(2θ)^{-η}` is (Borel) measurable. -/
lemma measurable_sigEta : Measurable Work.FTS.EllipticEst.AngSecond.sig := by
  change Measurable (fun θ : ℝ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
  exact Measurable.pow_const (Real.measurable_sin.comp (measurable_const.mul measurable_id)) _

/-- In the weak class `EllWeakPos α 0 F Ψ` (plus `HkMem α 0 Ψ`), the square of the `θ`-derivative
of the slice variable `θ ↦ Ψ z θ / cos θ`, against `σ θ = sin(2θ)^{-η}` (`η = 99/100`), is
integrable on the **lower half** `(0, π/4)` for every `z > 0`.

Route.  Let `f := fun θ => Ψ z θ`, so `ψ = f / cos`.  On `(0, π/4)` one has `cos θ ≥ 1/√2`, and
the chain rule gives `ψ' = (f' + sin θ · ψ) / cos θ`, hence
`(ψ')² σ ≤ 4 (f'² + ψ²) σ ≤ 4 f'² σ + 8 f² σ` (using `ψ² ≤ 2 f²` there).

* `IntegrableOn (fun θ => f θ² σ θ) Iθ` comes from `HkMem α 0 Ψ`: the level-`0` `HkIntegrand` is
  `(g · w/s^{η/2})²` (`Submission.Work.FTS.EllipticEst.remov.pth_zero_of_HkMem.HkIntegrand_zero_eq`),
  and for `z > 0` the constant factor `w z² ≠ 0` can be divided out.
* `IntegrableOn (fun θ => (f'' θ)² σ θ) Iθ` is the same statement with
  `g := pthIter 2 Ψ = fun z θ => deriv (deriv (fun θ' => Ψ z θ')) θ`, which is `HkMem α 0` by
  `EllWeakPos.memB`.
* `IntegrableOn (fun θ => (f' θ)² σ θ) Iθ` is the **second-order weighted interpolation**
  `Work.FTS.EllipticEst.Honest.sliceInterp` (`u` is only `C²` on the *open* interval `(0,π/2)`,
  which is exactly what `EllWeakPos.smooth` supplies for the slice, and no endpoint condition is
  required), applied to `u := f`.

The conclusion then follows by `Integrable.mono'` on `Ioo 0 (π/4)` with the a.e. strong
measurability of `(ψ')²σ` (`ψ'` is continuous on `(0, π/2)` because the slice is `C^∞` there and
`cos > 0`). -/
theorem psiDerivSq_lower : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
    Work.Spaces.HkMem α 0 Ψ →
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 4)) := by
  intro α F Ψ _hα _hα4 h hm z hz
  -- the slice of `Ψ` at `z` is `C²` on `(0, π/2)`
  have hslice : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_slice_of_strip h.smooth hz 2
  -- `f = Ψ z ·`: the two weighted energies `f²σ` and `f''²σ` are integrable on `Iθ`
  have h0 : MeasureTheory.IntegrableOn
      (fun θ => (fun θ' => Ψ z θ') θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      Work.Spaces.Iθ :=
    integrableOn_sq_mul_sig_of_hkMem hz hm
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
    have hbase : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ :=
      integrableOn_sq_mul_sig_of_hkMem (α := α) (z := z) (g := Work.Spaces.pthIter 2 Ψ)
        hz h.memB
    have hpt : ∀ θ : ℝ, Work.Spaces.pthIter 2 Ψ z θ
        = deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ := fun θ => rfl
    refine hbase.congr_fun (fun θ _ => ?_) measurableSet_Icc
    show (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
      = (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ
    rw [hpt θ]
  -- the weighted interpolation gives `f'²σ ∈ L¹`
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => Ψ z θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ :=
    (Work.FTS.EllipticEst.Honest.sliceInterp (fun θ' => Ψ z θ') hslice h0 h2).1
  -- restrict to the lower half and add the two pieces
  have hsub : Set.Ioo 0 (Real.pi / 4) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hbig : MeasureTheory.IntegrableOn
      (fun θ => 4 * ((deriv (fun t => Ψ z t) θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ)
        + 4 * ((Ψ z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))
      (Set.Ioo 0 (Real.pi / 4)) :=
    MeasureTheory.Integrable.add
      (MeasureTheory.Integrable.const_mul (MeasureTheory.IntegrableOn.mono_set h1 hsub) 4)
      (MeasureTheory.Integrable.const_mul (MeasureTheory.IntegrableOn.mono_set h0 hsub) 4)
  -- a.e. strong measurability of the target integrand
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun θ => (deriv (fun θ' => Ψ z θ' / Real.cos θ') θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 4))) := by
    have hcont : ContinuousOn (deriv (fun t => Ψ z t / Real.cos t)) (Set.Ioo 0 (Real.pi / 2)) :=
      (contDiffOn_divCos hslice).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
    have h1' : MeasureTheory.AEStronglyMeasurable
        (deriv (fun t => Ψ z t / Real.cos t))
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 4))) :=
      (hcont.aestronglyMeasurable measurableSet_Ioo).mono_set
        (Set.Ioo_subset_Ioo_right (by linarith [Real.pi_pos]))
    exact (h1'.pow 2).mul (measurable_sigEta.aestronglyMeasurable)
  -- the pointwise domination and `Integrable.mono'`
  refine hbig.mono' hmeas ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
  have hσθ : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig θ :=
    Work.FTS.EllipticEst.AngSecond.sig_nonneg ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hpt := psi_deriv_sq_le hslice hθ
  have hmul : (deriv (fun t => Ψ z t / Real.cos t) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ
      ≤ (4 * (deriv (fun t => Ψ z t) θ) ^ 2 + 4 * (Ψ z θ) ^ 2)
        * Work.FTS.EllipticEst.AngSecond.sig θ :=
    mul_le_mul_of_nonneg_right hpt hσθ
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hσθ)]
  nlinarith [hmul]

end Work.FTS.EllipticEst.TT
