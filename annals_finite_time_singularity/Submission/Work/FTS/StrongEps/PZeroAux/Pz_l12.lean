import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.EllSol.EllAux1
import Submission.Work.FTS.EllSol.EllAux2
import Submission.Work.FTS.StrongEps.PZeroAux.integrableOn_L12dens_bump

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.PZeroAux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The two facts used by `Pz_l12`

`Pz f = f − (L₁₂ f 0 / pzNorm) • bump`, and `L₁₂` is an integral, hence additive.  The
correction profile `bump` is supported in `[1/2,1] × [π/4,3π/8] ⊂ (0,∞) × (0,π/2)`, so its
`L₁₂`-density is a bounded compactly supported function: `integrableOn_L12dens_bump`.  With
that, the density of the projected profile is the difference of the two densities a.e., and
the set integral splits.

The point of stating the linearity with *a.e.* hypotheses rather than for every `s > 0` is
that this is all the caller has (`hae` of `Pz_l12` is an a.e. statement: the slice of a
`ClassC`/`ℋ⁴` profile is integrable for every `s > 0` only because of the honest-`ℋ⁴`
hypotheses, which `Pz_l12` does not assume). -/

/-- **A.e. additivity-and-homogeneity of `L₁₂` at `z = 0`.** If the `θ`-slices of `f` and of
`h` are integrable on `Iθ` for a.e. `s > 0`, and the densities of `f` and `h` are integrable
on `(0,∞)`, then `L₁₂(f + c·h)(0) = L₁₂ f(0) + c·L₁₂ h(0)`. -/
theorem L12_add_mul_ae {f h : ℝ → ℝ → ℝ} {c : ℝ}
    (hf : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ)
    (hh : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * h s θ / s) Work.Spaces.Iθ)
    (hF : MeasureTheory.IntegrableOn
      (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ / s) (Set.Ioi 0))
    (hH : MeasureTheory.IntegrableOn
      (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h s θ / s) (Set.Ioi 0)) :
    Work.Construction.L12 (fun z θ => f z θ + c * h z θ) 0
      = Work.Construction.L12 f 0 + c * Work.Construction.L12 h 0 := by
  have hfm : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.Ioi 0 →
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mp hf
  have hhm : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.Ioi 0 →
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * h s θ / s) Work.Spaces.Iθ :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mp hh
  have hden : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.Ioi 0 →
      Work.FM.L12dens Work.Spaces.K (fun z θ => f z θ + c * h z θ) s
        = Work.FM.L12dens Work.Spaces.K f s + c * Work.FM.L12dens Work.Spaces.K h s := by
    filter_upwards [hfm, hhm] with s hs1 hs2 hs
    exact Work.FTS.EllSol.L12dens_add_mul (hs1 hs) (hs2 hs)
  have hF' : MeasureTheory.Integrable (Work.FM.L12dens Work.Spaces.K f)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hF
  have hH' : MeasureTheory.Integrable (Work.FM.L12dens Work.Spaces.K h)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hH
  simp only [Work.Construction.L12, Work.FM.L12]
  rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioi hden]
  rw [MeasureTheory.integral_add hF' (hH'.const_mul c), MeasureTheory.integral_const_mul]

/-- The `θ`-slice of the `L₁₂`-density of `bump` is integrable on `Iθ` for every `s > 0`. -/
theorem integrableOn_slice_bump {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s) Work.Spaces.Iθ := by
  have hK : Continuous Work.Spaces.K := by
    show Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
    fun_prop
  have hb : Continuous (fun θ : ℝ => Work.FTS.StrongEps.bump s θ) := by
    show Continuous fun θ : ℝ => Work.FTS.StrongEps.zCut s * Work.FTS.StrongEps.thCut θ
    exact continuous_const.mul (Work.FTS.StrongEps.contDiff_thCut 0).continuous
  exact ((hK.mul hb).div_const s).continuousOn.integrableOn_compact isCompact_Icc

theorem Pz_l12 {f : ℝ → ℝ → ℝ} (hpz : Work.FTS.StrongEps.pzNorm ≠ 0)
    (hint : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f r θ / r) (Set.Ioi 0))
    (hae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f r θ / r) Work.Spaces.Iθ) :
    Work.Construction.L12 (Work.FTS.StrongEps.Pz f) 0 = 0 := by
  set c : ℝ := Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm with hc
  have hPz : Work.FTS.StrongEps.Pz f = fun z θ => f z θ + (-c) * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply, hc]
    ring
  rw [hPz]
  have hB : MeasureTheory.IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s) (Set.Ioi 0) :=
    integrableOn_L12dens_bump
  have hbump_slice : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s) Work.Spaces.Iθ :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun s hs => integrableOn_slice_bump hs)
  have hlin := L12_add_mul_ae (f := f) (h := Work.FTS.StrongEps.bump) (c := -c)
    hae hbump_slice hint hB
  rw [hlin]
  have hpz' : Work.Construction.L12 Work.FTS.StrongEps.bump 0 ≠ 0 := hpz
  simp only [hc, Work.FTS.StrongEps.pzNorm]
  rw [neg_mul, div_mul_cancel₀ _ hpz']
  ring

end Work.FTS.StrongEps.PZeroAux
