/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular-moment chain for the radial derivatives of `Ψ`

`Work.Elliptic.Fstar F z = ∫_θ F z θ · sinθcos²θ dθ` is the angular moment appearing in the
solvability condition of the elliptic estimates, and `Work.Elliptic.OrthCond Ψ` says that the
moment of the datum `Ψ` vanishes identically.  The present module propagates that condition to
the two radial derivatives:

* `F_*(∂_zΨ) ≡ 0` **everywhere** on `(0,∞)`,
* `F_*(∂_z²Ψ) = 0` **almost everywhere** on `(0,∞)`.

The mechanism is the differentiated moment relation of `moment_relation`: for a function `u`
smooth on the open quadrant with the relevant integrability,

  `F_* u (b) - F_* u (a) = ∫_a^b F_*(∂_z u)`

for all `0 < a < b` (`moment_relation u …`).  Applied to `u = Ψ` it says that the primitive of
`z ↦ F_*(∂_zΨ)(z)` is the constant `F_*Ψ = 0`, so the interval integrals of `F_*(∂_zΨ)`
vanish; applied to `u = ∂_zΨ` it exhibits `z ↦ F_*(∂_zΨ)(z)` as (a constant plus) the
primitive of `z ↦ F_*(∂_z²Ψ)(z)`, whence it is **continuous**.  This is exactly the two
ingredients of `eq_zero_of_forall_intervalIntegral_eq_zero_of_continuousOn` below, which upgrades "all interval
integrals vanish" to "the function vanishes" for a continuous function; the second moment then
vanishes a.e. by Lebesgue differentiation
(`Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_forall_intervalIntegral_eq_zero`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.moment_relation
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.AeBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Endpt

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## A continuous function all of whose interval integrals vanish is zero -/

/-- If `V` is continuous on `(0,∞)` and `∫_s^w V = 0` for all `0 < s ≤ w`, then `V ≡ 0` on
`(0,∞)`: the primitive of `V` starting at `z/2` has both derivative `V z` and derivative `0`
at `z`. -/
theorem eq_zero_of_forall_intervalIntegral_eq_zero_of_continuousOn {V : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hint : ∀ s w : ℝ, 0 < s → s ≤ w → ∫ r in s..w, V r = 0)
    (hcont : ContinuousOn V (Set.Ioi 0)) : V z = 0 := by
  set a : ℝ := z / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have haz : a < z := by rw [ha]; linarith
  have hsub : Set.uIcc a z ⊆ Set.Ioi 0 := by
    rw [Set.uIcc_of_le haz.le]
    exact fun x hx => lt_of_lt_of_le ha0 hx.1
  have hInt : IntervalIntegrable V volume a z := (hcont.mono hsub).intervalIntegrable
  have hsm : StronglyMeasurableAtFilter V (𝓝 z) volume :=
    hcont.stronglyMeasurableAtFilter isOpen_Ioi z hz
  have hderiv : HasDerivAt (fun w => ∫ r in a..w, V r) (V z) z :=
    intervalIntegral.integral_hasDerivAt_right hInt hsm
      (hcont.continuousAt (isOpen_Ioi.mem_nhds hz))
  have hev : (fun w => ∫ r in a..w, V r) =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds haz] with w hw
    exact hint a w ha0 (le_of_lt hw)
  have hderiv0 : HasDerivAt (fun w => ∫ r in a..w, V r) 0 z :=
    hev.hasDerivAt_iff.mpr (hasDerivAt_const z 0)
  exact hderiv.unique hderiv0

/-! ## The moment chain -/

theorem moment_chain_pz {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hOP : Work.Elliptic.OrthCond Ψ)
    (hU : ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz Ψ s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    (hZ : ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pzIter 2 Ψ s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    (hψ : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hp1 : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hT2 : ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
      (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ)) (Set.Icc a b)) :
    (∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z = 0) ∧
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z = 0) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  -- ## the differentiated moment relation for `∂_zΨ`
  have hmr1 : ∀ a b : ℝ, 0 < a → a < b →
      Work.Elliptic.Fstar (Work.Spaces.pz Ψ) b - Work.Elliptic.Fstar (Work.Spaces.pz Ψ) a
        = ∫ r in a..b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) r := by
    intro a b ha hab
    have h := Work.FTS.EllipticEst.moment_relation (Work.Spaces.pz Ψ) hΨ.pz hZ hp1 ha hab
    have hIcc : (∫ s in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz (Work.Spaces.pz Ψ) s θ * Work.Elliptic.sinCos2 θ)
        = ∫ s in Set.Icc a b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) s := rfl
    have hconv : (∫ s in Set.Icc a b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) s)
        = ∫ r in a..b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) r := by
      rw [intervalIntegral.integral_of_le hab.le]
      exact (setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume))).symm
    rw [hIcc, hconv] at h
    linarith
  -- ## the differentiated moment relation for `Ψ`
  have hzero1 : ∀ a b : ℝ, 0 < a → a < b →
      ∫ r in a..b, Work.Elliptic.Fstar (Work.Spaces.pz Ψ) r = 0 := by
    intro a b ha hab
    have h := Work.FTS.EllipticEst.moment_relation Ψ hΨ hU hψ ha hab
    have hIcc : (∫ s in Set.Icc a b, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz Ψ s θ * Work.Elliptic.sinCos2 θ)
        = ∫ s in Set.Icc a b, Work.Elliptic.Fstar (Work.Spaces.pz Ψ) s := rfl
    rw [hIcc, hOP b, hOP a, zero_add] at h
    have hconv : (∫ s in Set.Icc a b, Work.Elliptic.Fstar (Work.Spaces.pz Ψ) s)
        = ∫ r in a..b, Work.Elliptic.Fstar (Work.Spaces.pz Ψ) r := by
      rw [intervalIntegral.integral_of_le hab.le]
      exact (setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume))).symm
    rw [hconv] at h
    exact h.symm
  -- ## continuity of `z ↦ F_*(∂_zΨ)(z)` from the second moment relation
  have hcont1 : ContinuousOn (fun z => Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z)
      (Set.Ioi 0) := by
    intro z hz
    have hz0 : 0 < z := hz
    set a : ℝ := z / 2 with ha
    have ha0 : 0 < a := by rw [ha]; linarith
    have haz : a < z := by rw [ha]; linarith
    have haz2 : z < z + 1 := by linarith
    have hIntM2 : IntegrableOn
        (fun r => Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) r) (Set.uIcc a (z + 1)) := by
      rw [Set.uIcc_of_le (by linarith : a ≤ z + 1)]
      exact hT2 a (z + 1) ha0 (by linarith)
    have hcontprim : ContinuousOn
        (fun x => ∫ r in a..x, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) r)
        (Set.uIcc a (z + 1)) :=
      intervalIntegral.continuousOn_primitive_interval hIntM2
    have hmem : Set.uIcc a (z + 1) ∈ 𝓝 z := by
      rw [Set.uIcc_of_le (by linarith : a ≤ z + 1)]
      exact Icc_mem_nhds haz haz2
    have hcontR : ContinuousWithinAt (fun x => Work.Elliptic.Fstar (Work.Spaces.pz Ψ) a
        + ∫ r in a..x, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) r)
        (Set.Ioi 0) z :=
      continuousWithinAt_const.add (hcontprim.continuousAt hmem).continuousWithinAt
    have hrepr : ∀ x ∈ Set.Ioi 0, Work.Elliptic.Fstar (Work.Spaces.pz Ψ) x
        = Work.Elliptic.Fstar (Work.Spaces.pz Ψ) a
          + ∫ r in a..x, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) r := by
      intro x hx
      rcases lt_trichotomy a x with h | h | h
      · linarith [hmr1 a x ha0 h]
      · subst h; simp
      · have hh := hmr1 x a hx h
        rw [intervalIntegral.integral_symm] at hh
        linarith
    exact hcontR.congr_of_eventuallyEq
      (Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => hrepr x hx) (hrepr z hz)
  -- ## the first moment vanishes everywhere
  have hpoint1 : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z = 0 := by
    intro z hz
    refine eq_zero_of_forall_intervalIntegral_eq_zero_of_continuousOn hz (fun s w hs hsw => ?_) hcont1
    rcases lt_or_eq_of_le hsw with h | h
    · exact hzero1 s w hs h
    · subst h; simp
  -- ## hence the second moment vanishes a.e.
  have hzero2 : ∀ s t : ℝ, 0 < s → 0 < t →
      ∫ r in s..t, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) r = 0 := by
    intro s t hs ht
    rcases le_total s t with h | h
    · rcases lt_or_eq_of_le h with hlt | heq
      · have hh := hmr1 s t hs hlt
        rw [hpoint1 t (lt_trans hs hlt), hpoint1 s hs, sub_zero] at hh
        exact hh.symm
      · subst heq; simp
    · rcases lt_or_eq_of_le h with hlt | heq
      · have hh := hmr1 t s ht hlt
        rw [hpoint1 s (lt_trans ht hlt), hpoint1 t ht, sub_zero] at hh
        rw [intervalIntegral.integral_symm, ← hh, neg_zero]
      · subst heq; simp
  have hInt2 : ∀ a b : ℝ, 0 < a → a < b →
      IntervalIntegrable (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ)) volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact hT2 a b ha hab
  have hae2 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z = 0 :=
    Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_forall_intervalIntegral_eq_zero
      hzero2 hInt2
  exact ⟨hpoint1, hae2⟩

end Work.FTS.EllipticEst.Endpt
