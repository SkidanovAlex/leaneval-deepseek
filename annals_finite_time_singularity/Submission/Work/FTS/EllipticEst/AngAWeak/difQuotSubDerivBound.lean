/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `z`-difference quotient of the angular moment `F_*`

`Work.FTS.EllipticEst.AngAWeak.difQuotSubDerivBound` bounds the backward `z`-difference
quotient of the angular moment `F_*u(z) = ∫_θ u(z,θ) sinθcos²θ dθ` by the integral of
`|∂_z²u|`:

  `|(F_*u(z) - F_*u(z-hh))/hh - F_*(∂_zu)(z)| ≤ ∫_θ (∫_{z-hh}^{z}|∂_z²u(x,θ)|dx)·|sinθcos²θ|`.

## Proof

* First the linearity identity `fstar_sub_difQuot_eq_integral'`: since `u(z,·) sinθcos²θ`,
  `u(z-hh,·) sinθcos²θ` and `∂_zu(z,·) sinθcos²θ` are integrable on `Iθ`, the difference
  `(F_*u(z) - F_*u(z-hh))/hh - F_*(∂_zu)(z)` is the integral of the pointwise
  difference quotient `((u z θ - u (z-hh) θ)/hh - ∂_zu(z,θ)) sinθcos²θ`.
* The pointwise mean-value bound `sliceDifQuotBound'` (second-order Taylor/Lagrange on the
  `z`-slice, valid for `θ ∈ (0,π/2)`, where the open quadrant smoothness hypothesis
  applies) gives
  `|(u z θ - u (z-hh) θ)/hh - ∂_zu(z,θ)| ≤ ∫_{z-hh}^{z} |∂_z²u(x,θ)| dx`
  for every interior angle; multiplying by `|sinθcos²θ|` (nonnegative) and extending the
  pointwise estimate to `Iθ` almost everywhere (the two endpoints `θ = 0, π/2` are null)
  gives the a.e. domination.
* `integrableOn_integral_abs_pzIter2'` is the Fubini step that upgrades the joint
  integrability hypothesis `hbox` on the box `[z-hh,z] × Iθ` into integrability of the
  angular function `θ ↦ (∫_{z-hh}^{z}|∂_z²u|)·|sinθcos²θ|` — needed to apply
  `integral_mono_ae`.
* `|∫| ≤ ∫|·|` (`abs_integral_le_integral_abs`) and `integral_mono_ae` finish the job.

The auxiliary lemmas are self-contained copies (of `Honest.abs_difquot_sub_deriv_le`,
`Honest.contDiffOn_slice_Icc`, `Honest.hasDerivAt_slice_of_contDiffOn`) restricted to what
this argument uses, so that the file does not depend on the (actively edited) `Honest`
chapter.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Blocks.PzIterTwoContinuousOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## The open quadrant and slice facts for `C^n`-functions -/

/-- The open quadrant, on which the smoothness hypothesis is assumed. -/
private def AngQd : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)

private theorem isOpen_AngQd : IsOpen AngQd := isOpen_Ioi.prod isOpen_Ioo

/-- `z`-slices of a `C^n`-function on an open subset of `ℝ × ℝ`, restricted to a subset of
that open set. -/
private theorem contDiffOn_slice_Icc' {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} {n : WithTop ℕ∞}
    (hG : ContDiffOn ℝ n (Function.uncurry G) U) {a b θ : ℝ}
    (hmaps : ∀ s ∈ Set.Icc a b, (s, θ) ∈ U) :
    ContDiffOn ℝ n (fun s => G s θ) (Set.Icc a b) :=
  hG.comp (by fun_prop) hmaps

/-- A `C¹`-function on an open subset of `ℝ × ℝ` has differentiable `z`-slices on that set,
with derivative the `z`-partial `pz`. -/
private theorem hasDerivAt_slice_of_contDiffOn' {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hG : ContDiffOn ℝ 1 (Function.uncurry G) U) {u θ : ℝ}
    (hmem : (u, θ) ∈ U) :
    HasDerivAt (fun u' => G u' θ) (Work.Spaces.pz G u θ) u := by
  have hd : DifferentiableAt ℝ (Function.uncurry G) (u, θ) :=
    (hG.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hmem)
  have hcur : DifferentiableAt ℝ (fun u' => G u' θ) u :=
    Work.Spaces.differentiableAt_curry_left hd
  simpa [Work.Spaces.pz] using hcur.hasDerivAt

/-- **Second-order Taylor bound for a backward difference quotient.**  If `g` is the
derivative of `f` on `[a,b]`, `g'` the derivative of `g` there, and `a ≤ b - hh` with
`hh > 0`, then the backward difference quotient of `f` at `b` approximates `g b` up to the
integral of `|g'|` over the whole interval `[a,b]`. -/
private theorem abs_difquot_sub_deriv_le' {f g g' : ℝ → ℝ} {a b hh : ℝ}
    (hh_pos : 0 < hh) (ha : a ≤ b - hh)
    (hfcont : ContinuousOn f (Set.Icc (b - hh) b))
    (hfdiff : DifferentiableOn ℝ f (Set.Ioo (b - hh) b))
    (hfderiv : ∀ x ∈ Set.Icc a b, HasDerivAt f (g x) x)
    (hgderiv : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hgi : IntervalIntegrable g' volume a b) :
    |(f b - f (b - hh)) / hh - g b| ≤ ∫ x in a..b, |g' x| := by
  have hbhh : b - hh < b := by linarith
  have hab : a ≤ b := le_trans ha (le_of_lt hbhh)
  -- Lagrange's mean value theorem on the slice
  obtain ⟨ξ, hξ, hξderiv⟩ := exists_deriv_eq_slope f hbhh hfcont hfdiff
  have hξle : ξ ≤ b := le_of_lt hξ.2
  have haξ : a ≤ ξ := le_trans ha (le_of_lt hξ.1)
  have hξmem : ξ ∈ Set.Icc a b := ⟨haξ, hξle⟩
  -- the slope is the derivative of `f`, which is `g`
  have hgξ : deriv f ξ = g ξ := (hfderiv ξ hξmem).deriv
  have hslope : (f b - f (b - hh)) / hh = g ξ := by
    have h1 : b - (b - hh) = hh := by ring
    have h2 : (f b - f (b - hh)) / (b - (b - hh)) = g ξ := hξderiv.symm.trans hgξ
    rwa [h1] at h2
  -- the fundamental theorem of calculus for `g` on `[ξ,b]`
  have hftc : ∫ x in ξ..b, g' x = g b - g ξ := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := g) (f' := g') ?_ ?_
    · intro x hx
      rw [Set.uIcc_of_le hξle] at hx
      exact hgderiv x ⟨le_trans haξ hx.1, hx.2⟩
    · refine hgi.mono_set ?_
      rw [Set.uIcc_of_le hξle, Set.uIcc_of_le hab]
      exact Set.Icc_subset_Icc_left haξ
  rw [hslope]
  calc |g ξ - g b| = |∫ x in ξ..b, g' x| := by rw [hftc]; exact abs_sub_comm _ _
    _ ≤ ∫ x in ξ..b, |g' x| := intervalIntegral.abs_integral_le_integral_abs hξle
    _ ≤ ∫ x in a..b, |g' x| :=
        intervalIntegral.integral_mono_interval haξ hξle le_rfl
          (Eventually.of_forall fun x => abs_nonneg _) hgi.abs

/-! ## The pointwise mean-value bound on a slice -/

private theorem sliceDifQuotBound' {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z hh : ℝ} (hh0 : 0 < hh) (hhz : hh < z / 2)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |(u z θ - u (z - hh) θ) / hh - Work.Spaces.pz u z θ|
      ≤ ∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ| := by
  have hz : 0 < z := by linarith
  have hz2 : 0 < z - hh := by linarith
  have hle : z - hh ≤ z := by linarith
  have hmem : ∀ s ∈ Set.Icc (z - hh) z, (s, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) :=
    fun s hs => ⟨Set.mem_Ioi.mpr (by linarith [hs.1]), hθ.1, hθ.2⟩
  have hslice2 : ContDiffOn ℝ 2 (fun s : ℝ => u s θ) (Set.Icc (z - hh) z) :=
    contDiffOn_slice_Icc' (hsm 2) hmem
  have hfcont : ContinuousOn (fun s : ℝ => u s θ) (Set.Icc (z - hh) z) := hslice2.continuousOn
  have hfdiff : DifferentiableOn ℝ (fun s : ℝ => u s θ) (Set.Ioo (z - hh) z) :=
    (hslice2.differentiableOn (by norm_num)).mono Set.Ioo_subset_Icc_self
  have hfderiv : ∀ x ∈ Set.Icc (z - hh) z,
      HasDerivAt (fun s : ℝ => u s θ) (Work.Spaces.pz u x θ) x := fun x hx =>
    hasDerivAt_slice_of_contDiffOn' (isOpen_Ioi.prod isOpen_Ioo) (hsm 1) (hmem x hx)
  have hpz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz u))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ
      (isOpen_Ioi.prod isOpen_Ioo) (n := 1) (hsm 2)
  have hgderiv : ∀ x ∈ Set.Icc (z - hh) z,
      HasDerivAt (fun s : ℝ => Work.Spaces.pz u s θ) (Work.Spaces.pzIter 2 u x θ) x := by
    intro x hx
    have h' := hasDerivAt_slice_of_contDiffOn' (isOpen_Ioi.prod isOpen_Ioo) hpz1 (hmem x hx)
    simpa [Work.Spaces.pzIter_succ] using h'
  have hcs : ContinuousOn (fun s : ℝ => Work.Spaces.pzIter 2 u s θ) (Set.Icc (z - hh) z) :=
    (Work.FTS.EllipticEst.Blocks.PzIterTwoContinuousOn
      (isOpen_Ioi.prod isOpen_Ioo) (hsm 2)).comp (by fun_prop) hmem
  have hgi : IntervalIntegrable (fun s : ℝ => Work.Spaces.pzIter 2 u s θ) volume (z - hh) z := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hle]
    exact hcs
  exact abs_difquot_sub_deriv_le' (f := fun s : ℝ => u s θ)
    (g := fun s : ℝ => Work.Spaces.pz u s θ) (g' := fun s : ℝ => Work.Spaces.pzIter 2 u s θ)
    (a := z - hh) (b := z) (hh := hh) hh0 le_rfl hfcont hfdiff hfderiv hgderiv hgi

/-! ## The Fubini step: integrability of the angular function -/

private theorem integrableOn_integral_abs_pzIter2' {u : ℝ → ℝ → ℝ} {z hh : ℝ} (hh0 : 0 < hh)
    (hbox : MeasureTheory.IntegrableOn
      (Function.uncurry (fun x θ : ℝ =>
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
      (Set.Icc (z - hh) z ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ =>
        (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|) * |Work.Elliptic.sinCos2 θ|)
      Work.Spaces.Iθ := by
  have hle : z - hh ≤ z := by linarith
  have hprod : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => |Work.Spaces.pzIter 2 u p.1 p.2| * |Work.Elliptic.sinCos2 p.2|)
      ((MeasureTheory.volume.restrict (Set.Icc (z - hh) z)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have h := hbox
    rw [MeasureTheory.IntegrableOn, MeasureTheory.Measure.volume_eq_prod,
      ← MeasureTheory.Measure.prod_restrict] at h
    exact h
  have hout := hprod.integral_prod_right
  refine hout.congr ?_
  filter_upwards with θ
  rw [MeasureTheory.integral_mul_const]
  rw [intervalIntegral.integral_of_le hle]
  rw [MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc]

/-! ## The linearity identity for the difference quotient of `F_*` -/

private theorem fstar_sub_difQuot_eq_integral' {u : ℝ → ℝ → ℝ}
    (hψ : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => u z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hp1 : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    {z hh : ℝ} (hz : 0 < z) (hh0 : 0 < hh) (hhz : hh < z / 2) :
    (Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh
        - Work.Elliptic.Fstar (Work.Spaces.pz u) z
      = ∫ θ in Work.Spaces.Iθ,
          ((u z θ - u (z - hh) θ) / hh - Work.Spaces.pz u z θ)
            * Work.Elliptic.sinCos2 θ := by
  have hzhh : 0 < z - hh := by linarith
  have hI1 := hψ z hz
  have hI2 := hψ (z - hh) hzhh
  have hI3 := hp1 z hz
  have hdiv : MeasureTheory.IntegrableOn
      (fun θ => ((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun ((hI1.sub hI2).div_const hh)
      (fun θ _ => by simp only [Pi.sub_apply]; ring) measurableSet_Icc
  have h1 : Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)
      = ∫ θ in Work.Spaces.Iθ, (u z θ - u (z - hh) θ) * Work.Elliptic.sinCos2 θ := by
    rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, ← MeasureTheory.integral_sub hI1 hI2]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  have h2 : (∫ θ in Work.Spaces.Iθ,
        (u z θ - u (z - hh) θ) * Work.Elliptic.sinCos2 θ) / hh
      = ∫ θ in Work.Spaces.Iθ, ((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ := by
    rw [← MeasureTheory.integral_div]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  rw [h1, h2, Work.Elliptic.Fstar, ← MeasureTheory.integral_sub hdiv hI3]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

/-! ## The target -/

theorem difQuotSubDerivBound {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hψ : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => u z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hp1 : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pz u z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    {z hh : ℝ} (hz : 0 < z) (hh0 : 0 < hh) (hhz : hh < z / 2)
    (hbox : MeasureTheory.IntegrableOn
      (Function.uncurry (fun x θ : ℝ =>
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
      (Set.Icc (z - hh) z ×ˢ Work.Spaces.Iθ)) :
    |(Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh
        - Work.Elliptic.Fstar (Work.Spaces.pz u) z|
      ≤ ∫ θ in Work.Spaces.Iθ,
          (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|)
            * |Work.Elliptic.sinCos2 θ| := by
  have hzhh : 0 < z - hh := by linarith
  have hI3 := hp1 z hz
  -- the pointwise integrand and its two dominating functions
  have hdiv : MeasureTheory.IntegrableOn
      (fun θ => ((u z θ - u (z - hh) θ) / hh) * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun (((hψ z hz).sub (hψ (z - hh) hzhh)).div_const hh)
      (fun θ _ => by simp only [Pi.sub_apply]; ring) measurableSet_Icc
  have hφ : MeasureTheory.IntegrableOn
      (fun θ => ((u z θ - u (z - hh) θ) / hh - Work.Spaces.pz u z θ)
        * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun (hdiv.sub hI3)
      (fun θ _ => by simp only [Pi.sub_apply]; ring) measurableSet_Icc
  have hTint : MeasureTheory.IntegrableOn
      (fun θ : ℝ =>
        (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|) * |Work.Elliptic.sinCos2 θ|)
      Work.Spaces.Iθ :=
    integrableOn_integral_abs_pzIter2' hh0 hbox
  -- almost-everywhere pointwise domination
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |((u z θ - u (z - hh) θ) / hh - Work.Spaces.pz u z θ) * Work.Elliptic.sinCos2 θ|
        ≤ (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|)
            * |Work.Elliptic.sinCos2 θ| := by
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
        |((u z θ - u (z - hh) θ) / hh - Work.Spaces.pz u z θ) * Work.Elliptic.sinCos2 θ|
          ≤ (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|)
              * |Work.Elliptic.sinCos2 θ| :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (sliceDifQuotBound' hsm hh0 hhz hθ) (abs_nonneg _))
    exact (MeasureTheory.ae_restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))).1 h1
  rw [fstar_sub_difQuot_eq_integral' hψ hp1 hz hh0 hhz]
  refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
  exact MeasureTheory.integral_mono_ae hφ.abs hTint hae

end Work.FTS.EllipticEst.AngAWeak
