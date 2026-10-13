import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

open MeasureTheory Filter
open scoped Topology

/-- **Fubini identity for the sliding window.**

For `0 < hh ≤ z/2` the angular integral of the sliding window equals the sliding-window
integral of the angular slice:

  `∫_θ (∫_{z-hh}^{z} |∂_z²u(x,θ)|) |sinθcos²θ| = ∫_{z-hh}^{z} ∫_θ |∂_z²u(x,θ)|·|sinθcos²θ|`.

The inner product is pulled out of the `x`-integral with the (hypothesis-free)
`intervalIntegral.integral_mul_const`, and the two iterated interval integrals are exchanged with
`MeasureTheory.intervalIntegral_integral_swap`, whose integrability hypothesis comes from `hbox`
on the larger box `[z/2,z] × Iθ` (legitimate because `0 < hh ≤ z/2` puts `[z-hh,z] ⊆ [z/2,z]`). -/
private lemma slidingWindow_swap {u : ℝ → ℝ → ℝ}
    (hbox : ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
      (Function.uncurry (fun x θ : ℝ =>
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    {z hh : ℝ} (hhpos : 0 < hh) (hhz : hh ≤ z / 2) :
    (∫ θ in Work.Spaces.Iθ,
        (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|) * |Work.Elliptic.sinCos2 θ|)
      = ∫ x in (z - hh)..z, ∫ θ in Work.Spaces.Iθ,
          |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ| := by
  have hz2 : 0 < z / 2 := by linarith
  have hz2z : z / 2 < z := by linarith
  have hbox' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun x θ : ℝ =>
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
      (Set.Icc (z / 2) z ×ˢ Work.Spaces.Iθ) := hbox (z / 2) z hz2 hz2z
  have hsub : Set.Ioc (z - hh) z ×ˢ Work.Spaces.Iθ ⊆ Set.Icc (z / 2) z ×ˢ Work.Spaces.Iθ :=
    Set.prod_mono (fun y hy => ⟨by linarith [hy.1], hy.2⟩) (fun _ h => h)
  have hint0 : MeasureTheory.Integrable
      (Function.uncurry (fun x θ : ℝ =>
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Set.Ioc (z - hh) z ×ˢ Work.Spaces.Iθ)) :=
    MeasureTheory.Integrable.mono_measure hbox'
      (MeasureTheory.Measure.restrict_mono hsub le_rfl)
  have hint : MeasureTheory.Integrable
      (Function.uncurry (fun x θ : ℝ =>
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.uIoc (z - hh) z)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) := by
    rw [Set.uIoc_of_le (by linarith : z - hh ≤ z)]
    rw [MeasureTheory.Measure.prod_restrict]
    exact hint0
  have hswap := MeasureTheory.intervalIntegral_integral_swap (a := z - hh) (b := z)
    (f := fun x θ : ℝ => |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|)
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) hint
  calc (∫ θ in Work.Spaces.Iθ,
        (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|) * |Work.Elliptic.sinCos2 θ|)
      = (∫ θ in Work.Spaces.Iθ,
          (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|)) := by
          simp only [intervalIntegral.integral_mul_const]
    _ = ∫ x in (z - hh)..z, ∫ θ in Work.Spaces.Iθ,
          |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ| := hswap.symm

/-- **The sliding-window integral of the angular slice tends to `0`.**

This is absolute continuity of the Lebesgue integral: the slice function
`x ↦ ∫_θ |∂_z²u(x,θ)|·|sinθcos²θ|` is integrable on `[z/2,z]` by `hsec`, so its primitive is
continuous on `[z/2,z]` (`intervalIntegral.continuousOn_primitive_interval_left`); evaluating at the
right endpoint `z` gives `0`, and `hh ↦ z - hh` lands in `[z/2,z]` for `hh ∈ (0,z/2)`. -/
private lemma slidingWindow_tendsto {u : ℝ → ℝ → ℝ}
    (hsec : ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
      (fun x : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|)
      (Set.Icc a b))
    {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun hh : ℝ => ∫ x in (z - hh)..z, ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hz2 : 0 < z / 2 := by linarith
  have hz2z : z / 2 < z := by linarith
  have hFint : MeasureTheory.IntegrableOn
      (fun x : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|) (Set.Icc (z / 2) z) :=
    hsec (z / 2) z hz2 hz2z
  have hcont' : ContinuousOn (fun t : ℝ => ∫ x in t..z, ∫ θ in Work.Spaces.Iθ,
      |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|) (Set.uIcc (z / 2) z) := by
    refine intervalIntegral.continuousOn_primitive_interval_left (a := z / 2) (b := z) ?_
    rwa [Set.uIcc_of_le hz2z.le]
  have hcont : ContinuousOn (fun t : ℝ => ∫ x in t..z, ∫ θ in Work.Spaces.Iθ,
      |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|) (Set.Icc (z / 2) z) := by
    rwa [Set.uIcc_of_le hz2z.le] at hcont'
  have hz_mem : z ∈ Set.Icc (z / 2) z := ⟨hz2z.le, le_refl z⟩
  have hcw : ContinuousWithinAt (fun t : ℝ => ∫ x in t..z, ∫ θ in Work.Spaces.Iθ,
      |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|) (Set.Icc (z / 2) z) z :=
    hcont z hz_mem
  have hzn : (fun t : ℝ => ∫ x in t..z, ∫ θ in Work.Spaces.Iθ,
      |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|) z = 0 := by
    simp [intervalIntegral.integral_same]
  have hmem : ∀ᶠ hh in nhdsWithin (0 : ℝ) (Set.Ioi 0), z - hh ∈ Set.Icc (z / 2) z := by
    have hI : Set.Ioo (0 : ℝ) (z / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      mem_nhdsWithin.mpr ⟨Set.Iio (z / 2), isOpen_Iio, hz2, fun x hx => ⟨hx.2, hx.1⟩⟩
    filter_upwards [hI] with hh hhh using ⟨by linarith [hhh.2], by linarith [hhh.1]⟩
  have htend : Filter.Tendsto (fun hh : ℝ => z - hh) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhdsWithin z (Set.Icc (z / 2) z)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hmem⟩
    have h1 : Filter.Tendsto (fun hh : ℝ => z - hh) (𝓝 (0 : ℝ)) (𝓝 (z - 0)) :=
      tendsto_const_nhds.sub tendsto_id
    have h2 : Filter.Tendsto (fun hh : ℝ => z - hh) (𝓝 (0 : ℝ)) (𝓝 z) := by
      simpa using h1
    exact Filter.Tendsto.mono_left h2 inf_le_left
  have hfin := Filter.Tendsto.comp hcw htend
  rw [hzn] at hfin
  simpa [Function.comp_def] using hfin

theorem tendstoThetaIntervalAbsPzIter2 {u : ℝ → ℝ → ℝ}
    (hbox : ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
      (Function.uncurry (fun x θ : ℝ =>
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|))
      (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    (hsec : ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
      (fun x : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|)
      (Set.Icc a b))
    {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun hh : ℝ => ∫ θ in Work.Spaces.Iθ,
        (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|) * |Work.Elliptic.sinCos2 θ|)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hkey := slidingWindow_tendsto hsec hz
  have heq : (fun hh : ℝ => ∫ x in (z - hh)..z, ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 u x θ| * |Work.Elliptic.sinCos2 θ|)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun hh : ℝ => ∫ θ in Work.Spaces.Iθ,
        (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|) * |Work.Elliptic.sinCos2 θ|) := by
    have hz2 : 0 < z / 2 := by linarith
    have hI : Set.Ioo (0 : ℝ) (z / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      mem_nhdsWithin.mpr ⟨Set.Iio (z / 2), isOpen_Iio, hz2, fun x hx => ⟨hx.2, hx.1⟩⟩
    filter_upwards [hI] with hh hhh
    exact (slidingWindow_swap hbox hhh.1 hhh.2.le).symm
  exact Filter.Tendsto.congr' heq hkey

end Work.FTS.EllipticEst.AngAWeak
