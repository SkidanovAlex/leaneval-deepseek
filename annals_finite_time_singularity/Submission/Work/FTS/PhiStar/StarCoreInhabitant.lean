import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Assemble
import Submission.Work.FTS.PhiStar.Model
import Submission.Work.FTS.PhiStar.Decomp
import Submission.Work.FTS.PhiStar.GzProfile_tendsto
import Submission.Work.FTS.PhiStar.ZeroOffWitness
import Submission.Work.FTS.PhiStar.StarCoreAux
import Submission.Work.FTS.PhiStar.FlatW_psiSeries
import Submission.Work.FTS.PhiStar.FlatWApi.FlatW_congr
import Submission.Work.FTS.PhiStar.FlatWApi.FlatW_ycheckSmooth
import Submission.Work.FTS.PhiStar.Series.psiSeries_solves_rem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.StarCoreInhabitant` — the analysis node `StarCore`

For every `0 < α ≤ 1/5` there is a stream function `Φ_* = Model α (GzProfile α) ψ + R` with

* `R = psiSeries α (RemSource α ψ)` the mode series solving the `O(α²)` remainder equation
  (`Series.psiSeries_solves_rem`),
* `Φ_*` presented in the zero-extension normal form (`ZeroOffWitness`) so that `PhiTs α Φ_*`
  vanishes off the open quadrant,
* and the flat bound `FlatW 7 (Ycheck α Φ_*) (Cs·α)` assembled from

  `Ycheck α Φ_* = ((z+1)/z)·Aprof α + α·(2/(1+z))·(ψ/sin 2θ) + ((z+1)/z)·R/sin 2θ`

  whose three pieces are bounded by `FlatW_aprof` (`O(α)`), `FlatW_psiDiv` transported along the
  radial factor `2/(1+z)` (`O(α)`), and `FlatW_psiSeries` (`O(α²)`) respectively
  (`FlatW_YcheckExpansion`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Classical

namespace Work.FTS.PhiStar

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The analysis node `StarCore`.** -/
theorem StarCore_inhabitant : ∃ Cs : ℝ, 0 < Cs ∧ ∀ α : ℝ, 0 < α → α ≤ 1 / 5 →
    ∃ Φs : Fn, Work.FTS.VocabO2.StarCore α Cs Φs := by
  obtain ⟨Ce, hCe, hE⟩ := FlatWApi.FlatW_ycheckSmooth
  obtain ⟨Cy, hCy, hY⟩ := FlatW_psiSeries
  obtain ⟨Cg, hCg, hG⟩ := FlatWApi.FlatW_congr
  obtain ⟨hSsmooth, hSeq, hSdir, hSdec⟩ := Series.psiSeries_solves_rem
  refine ⟨Cg * Ce * (1 + Cg * Cy / 5), by positivity, fun α hα hα5 => ?_⟩
  have hα4 : α ≤ 1 / 4 := by linarith
  have hα1 : α ≤ 1 := by linarith
  -- the angular model
  obtain ⟨Cψ, ψ, hCψpos, hψang, hψbd⟩ := Psi0AngModel hα hα4
  -- the remainder and the witness
  set R : Fn := fun z θ => Series.psiSeries α (RemSource α ψ) z θ with hR
  set Ψ : Fn := fun z θ => Model α (GzProfile α) ψ z θ + R z θ with hΨ
  set Φs : Fn := ZeroOffW α Ψ with hΦs
  -- the four series facts
  have hRsmooth : Work.FTS.EllipticEst.SmoothOpen R := hSsmooth α ψ hα hα5 hψang
  have hReq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α R z θ = RemSource α ψ z θ := hSeq α ψ hα hα5 hψang
  have hRdir : ∀ z, R z 0 = 0 ∧ R z (π / 2) = 0 := hSdir α ψ hα hα5 hψang
  have hRdec : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => R z θ) atTop (𝓝 0) :=
    hSdec α ψ hα hα5 hψang
  have hGzdec : Tendsto (GzProfile α) atTop (𝓝 0) := GzProfile_tendsto hα hα4
  -- `sol`
  have hsolΨ : Work.Elliptic.IsBslSol α (Work.Construction.Fstar α) Ψ := by
    rw [hΨ]
    exact isBslSol_of_rem' hα hα4 hψang hGzdec hψbd hRsmooth hReq
      (fun z => (hRdir z).1) (fun z => (hRdir z).2) hRdec
  -- `smooth`
  have hmodsmooth : Work.FTS.EllipticEst.SmoothOpen (Model α (GzProfile α) ψ) :=
    smoothOpen_model hα hα4 hψang
  have hsumsmooth : Work.FTS.EllipticEst.SmoothOpen Ψ := by
    rw [hΨ]
    refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
    refine ((hmodsmooth.forall n).add (hRsmooth.forall n)).congr (fun p _ => ?_)
    simp only [Function.uncurry, Pi.add_apply]
  -- `core`
  have hRflat0 : Work.FTS.VocabO2.FlatW 7
      (fun z θ => (z + 1) / z * (R z θ / Work.Construction.s2 θ)) (Cy * α ^ 2) :=
    hY α ψ hα hα5 hψang
  have hRflat : Work.FTS.VocabO2.FlatW 7
      (fun z θ => (z + 1) / z * R z θ / Work.Construction.s2 θ) (Cg * (Cy * α ^ 2)) :=
    hG 7 (fun z θ => (z + 1) / z * (R z θ / Work.Construction.s2 θ))
      (fun z θ => (z + 1) / z * R z θ / Work.Construction.s2 θ) (Cy * α ^ 2)
      (fun z θ _ _ _ => by ring) hRflat0
  have hFflat : Work.FTS.VocabO2.FlatW 7 (YcheckExpand α ψ R)
      (Ce * (α + Cg * (Cy * α ^ 2))) := by
    have h0 := hE α ψ R (Cg * (Cy * α ^ 2)) hα hα5 hψang (by positivity) hRsmooth hRflat
    unfold YcheckExpand
    exact h0
  have heqfun : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      YcheckExpand α ψ R z θ = Work.FTS.VocabO2.Ycheck α Φs z θ := by
    intro z θ hz hθ hθ2
    have hzp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.mem_Q0).mpr ⟨hz, hθ, hθ2⟩
    have h1 : YcheckExpand α ψ R z θ = Work.FTS.VocabO2.Ycheck α Ψ z θ :=
      Ycheck_eq_expand (α := α) (ψ := ψ) (R := R) (Φs := Ψ) hα hα1
        (fun z θ _ => by rw [hΨ]) z θ hz hθ hθ2
    have h2 : Work.FTS.VocabO2.Ycheck α Ψ z θ = Work.FTS.VocabO2.Ycheck α Φs z θ := by
      unfold Work.FTS.VocabO2.Ycheck
      rw [show Work.FTS.VocabO2.PhiTs α Φs z θ = Work.FTS.VocabO2.PhiTs α Ψ z θ from
        PhiTs_zeroOffW_eqOn α Ψ z θ hzp]
    exact h1.trans h2
  have hYc : Work.FTS.VocabO2.FlatW 7 (Work.FTS.VocabO2.Ycheck α Φs)
      (Cg * (Ce * (α + Cg * (Cy * α ^ 2)))) :=
    hG 7 (YcheckExpand α ψ R) (Work.FTS.VocabO2.Ycheck α Φs) (Ce * (α + Cg * (Cy * α ^ 2)))
      heqfun hFflat
  have hle : Cg * (Ce * (α + Cg * (Cy * α ^ 2)))
      ≤ (Cg * Ce * (1 + Cg * Cy / 5)) * α := by
    have hCy' : 0 < Cg * Cy := mul_pos hCg hCy
    have hs : α ^ 2 ≤ α * (1 / 5) := by nlinarith [hα, hα5]
    have hc : Cg * Cy * α ^ 2 ≤ Cg * Cy * (α * (1 / 5)) :=
      mul_le_mul_of_nonneg_left hs (le_of_lt hCy')
    have h1 : α + Cg * (Cy * α ^ 2) ≤ α * (1 + Cg * Cy / 5) := by nlinarith [hc]
    have h2 : Ce * (α + Cg * (Cy * α ^ 2)) ≤ Ce * (α * (1 + Cg * Cy / 5)) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hCe)
    have h3 : Cg * (Ce * (α + Cg * (Cy * α ^ 2))) ≤ Cg * (Ce * (α * (1 + Cg * Cy / 5))) :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt hCg)
    calc Cg * (Ce * (α + Cg * (Cy * α ^ 2))) ≤ Cg * (Ce * (α * (1 + Cg * Cy / 5))) := h3
      _ = (Cg * Ce * (1 + Cg * Cy / 5)) * α := by ring
  have hcore : Work.FTS.VocabO2.FlatW 7 (Work.FTS.VocabO2.Ycheck α Φs)
      ((Cg * Ce * (1 + Cg * Cy / 5)) * α) := FlatW_mono hYc hle
  refine ⟨Φs, ?_, ?_, ?_, hcore⟩
  · rw [hΦs]
    exact isBslSol_zeroOffW hsolΨ
  · rw [hΦs]
    exact smoothOpen_zeroOffW hsumsmooth
  · intro z θ h
    rw [hΦs]
    exact PhiTs_zeroOffW_off α Ψ z θ h

end Work.FTS.PhiStar
