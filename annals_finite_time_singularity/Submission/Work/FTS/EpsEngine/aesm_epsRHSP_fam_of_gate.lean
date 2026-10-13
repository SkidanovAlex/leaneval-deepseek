/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/aesm_epsRHSP_fam_of_gate.lean`

**The measurability gate of the projected `ε`-scheme**: a family `g` whose slices lie in the
`X`-ball `XBall α ρ ε R C₀` and are `EpsSq`-Lipschitz in the fake time has an a.e. strongly
measurable right-hand side `(τ,z,θ) ↦ epsRHSP α ρ ε Φs E g τ z θ` for the horizon-restricted
product measure `(volume.restrict (Icc 0 δ)) ⊗ volume`.

The route is the one designed in the audit of the statement (`.fm3_reviews.json`, entry
`FTS/EpsEngine/aesm_epsRHSP_fam_of_gate`):

* `epsRHSP_eq_Feps_slice` rewrites the right-hand side as `Feps (slice g τ)`, with `Feps` the
  `τ`-free map `u ↦ Pz (J_ε (profRHS α Φs E (Pz (J_ε u))))` on profiles (`EpsEngine.EpsClass`);
* the *pointwise Lipschitz gate* `pt_of_XBall` below is `profRHS_sub_sup_le_Sq` unpacked at the
  `XBall` data of `u` and `v` (its hypotheses are literally the five `XBall` fields);
* per slice, `Feps ·` is continuous on the open quadrant and vanishes off it
  (`continuousOn_Feps_of_XBall` / `Feps_eq_zero_off_Q0`, from `LocalStepXBall`), so the abstract
  dyadic lemma `MeasAlt.aesm_slice_of_lipschitz_gate` turns the two gates into a.e. strong
  measurability of `τ ↦ Feps (slice g τ) z θ` on `[0,δ]` for every `(z,θ)`;
* the Carathéodory assembly `MeasAlt.aesm_of_slice_aesm` combines the slicewise measurability with
  per-slice continuity on the quadrant into the joint measurability for the product measure.

The statement does not assume `0 ≤ δ`; for `δ < 0` the horizon `Icc 0 δ` is empty and the measure
vanishes, which is handled by the second branch below.
-/
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.SmoothOpenIter
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.EpsEngine.EpsClass
import Submission.Work.FTS.EpsEngine.MeasAlt.aesm_slice_of_lipschitz_gate
import Submission.Work.FTS.EpsEngine.MeasAlt.IterMeas
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le_Sq
import Submission.Work.FTS.EpsEngine.aesm_uncurry_of_continuousOn_of_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open MeasureTheory Set Filter
open scoped Real Topology
open Work.FTS.Galerkin (Fn)

/-- **The pointwise Lipschitz gate of `Feps` on the `X`-ball**: there is `C > 0` with
`|Feps u z θ − Feps v z θ| ≤ C √(EpsSq (u−v))` on the open quadrant, for all `u, v ∈ XBall`.

This is `profRHS_sub_sup_le_Sq` with its hypotheses read off the `XBall` structure (and the
`τ`-free form `Feps u = epsRHPSlice … 0 u`, `Feps_eq_epsRHPSlice`). -/
theorem pt_of_XBall {α C₀ R Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : Fn, XBall α ρ ε R C₀ u → XBall α ρ ε R C₀ v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ|
        ≤ C * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
  obtain ⟨C, hCpos, hC⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le_Sq (α := α) (C₀ := C₀) (Ce := Ce)
      (Cs := Cs) (R := R) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε)
      hα hρ hε hε1 hEll hstar hml hR
  refine ⟨C, hCpos, fun u v hu hv z θ hz hθ1 hθ2 => ?_⟩
  have h1 := hC hu.smoothOpen hv.smoothOpen hu.mem hu.sq_le hv.mem hv.sq_le
    hu.classC hv.classC hu.ball hv.ball z θ hz hθ1 hθ2
  rwa [← Feps_eq_epsRHPSlice α ρ ε Φs E 0 u, ← Feps_eq_epsRHPSlice α ρ ε Φs E 0 v] at h1

theorem aesm_epsRHSP_fam_of_gate {α C₀ R Ce Cs Lw δ : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {ε : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (hP : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₀ (Work.FTS.Galerkin.slice g s))
    (hEq : ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ, Work.FTS.StrongEps.EpsSq α (fun z θ =>
      Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g t z θ) ≤ Lw * (s - t) ^ 2) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g p.1 p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod MeasureTheory.volume) := by
  classical
  by_cases hδ : 0 ≤ δ
  · -- main case: `δ ≥ 0`, the horizon is non-degenerate
    obtain ⟨C, hCpos, hpt⟩ := pt_of_XBall (α := α) (C₀ := C₀) (R := R) (Ce := Ce) (Cs := Cs)
      (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml hR
    -- the per-slice data of `Feps` at `XBall`-profiles
    have hcont : ∀ w : Fn, XBall α ρ ε R C₀ w →
        ContinuousOn (fun q : ℝ × ℝ => Feps α ρ ε Φs E w q.1 q.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      fun w hw => (continuousOn_Feps_of_XBall (α := α) (Ce := Ce) (Cs := Cs) (R := R)
        (C₀ := C₀) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (u := w)
        hα hρ hε hEll hstar hw).1
    have hzero : ∀ (w : Fn) (q : ℝ × ℝ),
        q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → Feps α ρ ε Φs E w q.1 q.2 = 0 :=
      fun w q hq => Feps_eq_zero_off_Q0 α ρ ε Φs E w q hq
    -- the slicewise measurability in the fake time (dyadic approximation against the curve)
    have hmeas : ∀ z θ : ℝ, MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc 0 δ)) :=
      MeasAlt.aesm_slice_of_lipschitz_gate (F := fun u : Fn => Feps α ρ ε Φs E u)
        (V := fun s : ℝ => Work.FTS.Galerkin.slice g s)
        (P := fun u : Fn => XBall α ρ ε R C₀ u)
        (α := α) (δ := δ) (Cpt := C) (Lb := Lw) hδ hLw hCpos.le hP hcont hzero hpt
        (fun s t hs ht => hEq s hs t ht)
    -- the Carathéodory assembly
    have hmain : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ × ℝ => Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g p.1) p.2.1 p.2.2)
        ((MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod MeasureTheory.volume) :=
      MeasAlt.aesm_of_slice_aesm (F := fun u : Fn => Feps α ρ ε Φs E u)
        (V := fun s : ℝ => Work.FTS.Galerkin.slice g s)
        (P := fun u : Fn => XBall α ρ ε R C₀ u) (δ := δ) hP hcont hzero hmeas
    refine hmain.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [epsRHSP_eq_Feps_slice]
  · -- degenerate case: `δ < 0`, the horizon `Icc 0 δ` is empty, so the measure vanishes
    have hIcc : Set.Icc (0 : ℝ) δ = ∅ := Set.Icc_eq_empty_of_lt (lt_of_not_ge hδ)
    have hzero : (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) δ)).prod MeasureTheory.volume
        = (0 : Measure (ℝ × ℝ × ℝ)) := by
      rw [hIcc, MeasureTheory.Measure.restrict_empty, MeasureTheory.Measure.zero_prod]
    rw [hzero]
    exact MeasureTheory.aestronglyMeasurable_zero_measure _

end Work.FTS.EpsEngine
