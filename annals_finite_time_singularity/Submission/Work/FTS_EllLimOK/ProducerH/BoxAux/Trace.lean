import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.ClassC.VopAux.vopTracesPointwise_classC
import Submission.Work.FTS.ClassC.RopGen.Transfer
import Submission.Work.FTS.EllSol.ellPkgConj_of_classOk

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS_EllLimOK/ProducerH/BoxAux/Trace` — the two angular traces of `E g`

The pointwise (in `z`) vanishing of `E g` at both angular endpoints, for a stream function
carrying the level-`8` existence class.  This is the `(T)` of `ProducerH/NOTES_pkgBoxH.md` §4,
at the *value* level: the junk values `E g z 0 = E g z (π/2) = 0` prescribed by `IsBslSol`
are the one-sided limits.

The proof reuses the tree's `ClassC.VopAux.vopTracesPointwise_classC` (traces of the radial
iterates `D_z^j Ξ` of the residual `Ξ = PhiTil α g (E g)` at both endpoints, `j ≤ 6`), by
writing `E g = Ξ + Θ` with `Θ = (1/(4α)) sin 2θ · L₁₂ g` an explicit `θ`-continuous function
vanishing at both endpoints.

Everything is `sorry`-free.
-/
noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The residual `Φ̃ = PhiTil α g (E g)` is the elliptic residual `EllResid α g (E g)`. -/
theorem phiTil_eq (α : ℝ) (g Ψ : Fn) :
    Work.Construction.PhiTil α g Ψ = Work.Elliptic.EllResid α g Ψ :=
  Work.FTS.ClassC.phiTil_eq_EllResid_gen α g Ψ

/-- The shifted decomposition `E g = Φ̃ + Θ`, with `Θ α g z θ = (1/(4α)) sin 2θ · L₁₂ g z`. -/
theorem Eg_eq_phiTil_add (α : ℝ) (g Ψ : Fn) :
    Ψ = fun z θ => Work.Construction.PhiTil α g Ψ z θ + Work.Construction.Theta α g z θ := by
  funext z θ
  simp only [Work.Construction.PhiTil]
  ring

/-- The pointwise decomposition `E g = Φ̃ + Θ`, in the `θ`-slice form used below. -/
theorem slice_eq_phiTil_add (α : ℝ) (g Ψ : Fn) (z : ℝ) :
    (fun θ => Ψ z θ)
      = fun θ => Work.Construction.PhiTil α g Ψ z θ + Work.Construction.Theta α g z θ := by
  funext θ
  have h := congrFun (congrFun (Eg_eq_phiTil_add α g Ψ) z) θ
  simpa only [Pi.add_apply] using h

/-- `Θ α g z ·` tends to `0` at both angular endpoints (the `z`-factor `L₁₂ g z` is fixed). -/
theorem tendsto_Theta (α : ℝ) (g : Fn) (z : ℝ) :
    (Filter.Tendsto (fun θ => Work.Construction.Theta α g z θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
      (Filter.Tendsto (fun θ => Work.Construction.Theta α g z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
  have hfun : Work.Construction.Theta α g z
      = fun θ => (1 / (4 * α)) * Work.Construction.L12 g z * Real.sin (2 * θ) := by
    funext θ
    simp only [Work.Construction.Theta, Work.Construction.s2_eq]
    ring
  rw [hfun]
  constructor
  · have h2 : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hc : ContinuousAt (fun θ : ℝ => Real.sin (2 * θ)) 0 :=
        Real.continuous_sin.continuousAt.comp (continuousAt_const.mul continuousAt_id)
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h2.const_mul ((1 / (4 * α)) * Work.Construction.L12 g z)
  · have h2 : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have hc : ContinuousAt (fun θ : ℝ => Real.sin (2 * θ)) (Real.pi / 2) :=
        Real.continuous_sin.continuousAt.comp (continuousAt_const.mul continuousAt_id)
      have h3 := hc.tendsto.mono_left (nhdsWithin_le_nhds :
        nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤ nhds (Real.pi / 2))
      rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi] at h3
      simpa using h3
    simpa using h2.const_mul ((1 / (4 * α)) * Work.Construction.L12 g z)

/-- **The `θ = 0⁺` trace of `E g`.** -/
theorem tendsto_Eg_at_zero {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
        Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
        Work.FTS.ClassC.EllPkgK α 6 Ce g (E g))
    {g : Work.FTS.Galerkin.Fn} (hg : Work.FTS.ClassC.ClassC α g) {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun θ => (E g) z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hO7 : Work.FTS.EllExist.EllClassOk 7 α g (E g) :=
    Work.FTS.EllSol.ellClassOk_eight_seven (hE g hg).1
  have htr := (Work.FTS.ClassC.VopAux.vopTracesPointwise_classC 0 (by norm_num) α g (E g)
    hα hα4 hg hO7 z hz).1
  have htr' : Filter.Tendsto (fun θ => Work.Construction.PhiTil α g (E g) z θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [Work.Spaces.DzIter_zero, phiTil_eq] using htr
  rw [slice_eq_phiTil_add α g (E g) z]
  simpa using htr'.add (tendsto_Theta α g z).1

/-- **The `θ = π/2⁻` trace of `E g`.** -/
theorem tendsto_Eg_at_pi_half {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
        Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
        Work.FTS.ClassC.EllPkgK α 6 Ce g (E g))
    {g : Work.FTS.Galerkin.Fn} (hg : Work.FTS.ClassC.ClassC α g) {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun θ => (E g) z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hO7 : Work.FTS.EllExist.EllClassOk 7 α g (E g) :=
    Work.FTS.EllSol.ellClassOk_eight_seven (hE g hg).1
  have htr := (Work.FTS.ClassC.VopAux.vopTracesPointwise_classC 0 (by norm_num) α g (E g)
    hα hα4 hg hO7 z hz).2
  have htr' : Filter.Tendsto (fun θ => Work.Construction.PhiTil α g (E g) z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    simpa only [Work.Spaces.DzIter_zero, phiTil_eq] using htr
  rw [slice_eq_phiTil_add α g (E g) z]
  simpa using htr'.add (tendsto_Theta α g z).2

end Work.FTS_EllLimOK.ProducerH.BoxAux
