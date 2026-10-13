/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/LocalStepEngine.lean` — the local step of the projected
# `ε`-scheme, reduced to the engine's *concrete* obligations

`Work.FTS.StrongEps.EpsLocalPStar` (`= Work.FTS.StrongEps.EpsE4Thr.LocalStepP`) asks: for every
datum `h₀` with `EpsDatumP α ρ ε h₀`, `Xn α (Pz (J_ε h₀)) ≤ C₀ α²` and `Xn6 α h₀ ≤ M'` there are
`δ > 0` and a family `h` with `IsEpsSolP α ρ ε δ Φs E h₀ h ∧ EpsRegP α ρ ε δ h`.

This module isolates the *only* remaining inputs of that statement, by composing the applicable
engine `exists_volterra_v4` (with `F := Feps`, `P := EpsClass α ρ ε C₁ B`, whose solution is the
explicit limit family `limFam (Feps …) h₀` of the Picard iteration) with the conversions of
`EpsClass.lean`:

* **profile-level** (provable from the gates, see `EpsClass.lean` and `hpt_of_epsClass`):
  `hP₀`, `hbd`, `hlip`, `hpt`;
* **iterate-level** (about the explicit Picard iterates of `VolterraAux/Iter.lean`):
  `hcontIter`, `hmeasIter` (both *derivable* — see `hcontIter_of_le`; the measurability one is the
  concrete parametric-integral induction) and
  `hkeepIter` — "the Picard iterates stay in the class", the class-invariance obligation;
* **limit-level**: `hlimP` (the limit family's slices are in the class, at the ball radius `C₁`)
  and `hreg` (the joint `C¹` regularity of the limit family, which is `EpsRegP`'s first conjunct).

Everything else — the contraction, the convergence, the Volterra identity, the fake-time
derivative, the identification of the scheme's right-hand side, and the passage to `EpsDatumP` of
each slice — is discharged here.

**Radius.**  The engine runs at the ball radius `C₁` of `EpsClass α ρ ε C₁ B`; the gates
(`EpsRHSPBdd`, `EpsRHSPLipX`) and `MuLamOK` are only available at that radius, so the instantiation
must supply `MuLamOK α C₁ Φs E` with `C₁ > C₀` (*room*) — the blocker documented in
`NOTES_VolterraV4.md` §3.  This module deliberately takes `C₁` as a parameter: the room problem is
statement-level and does not affect the *content* proved here.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EpsEngine.EpsClass
import Submission.Work.FTS.EpsEngine.VolterraV4Main
import Submission.Work.FTS.StrongEps.EpsStructP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps

set_option autoImplicit false

/-- **The local step at a fixed datum and a fixed horizon**, reduced to the engine's concrete
obligations (see the module docstring).  The conclusion is exactly the pair
`IsEpsSolP ∧ EpsRegP` required by `LocalStepP`. -/
theorem exists_sol_of_engine {α C₁ Cpt L δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {ε : ℝ} {h₀ : Fn} {B : ℝ}
    (hδ : 0 < δ) (hL : 0 < L) (hδL : δ * Real.sqrt L < 1) (hCpt : 0 ≤ Cpt)
    (hP₀ : EpsClass α ρ ε C₁ B h₀)
    (hbd : ∀ u : Fn, EpsClass α ρ ε C₁ B u →
      EpsMem α (Feps α ρ ε Φs E u) ∧ EpsSq α (Feps α ρ ε Φs E u) ≤ L)
    (hlip : ∀ u v : Fn, EpsClass α ρ ε C₁ B u → EpsClass α ρ ε C₁ B v →
      EpsMem α (fun z θ => u z θ - v z θ) →
      EpsSq α (fun z θ => Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ)
        ≤ L * EpsSq α (fun z θ => u z θ - v z θ))
    (hpt : ∀ u v : Fn, EpsClass α ρ ε C₁ B u → EpsClass α ρ ε C₁ B v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ|
          ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ)))
    (hcontP : ∀ u : Fn, EpsClass α ρ ε C₁ B u → ContinuousOn (fun q : ℝ × ℝ =>
      Feps α ρ ε Φs E u q.1 q.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hzeroP : ∀ u : Fn, EpsClass α ρ ε C₁ B u → ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → Feps α ρ ε Φs E u q.1 q.2 = 0)
    (hkeepIter : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      EpsClass α ρ ε C₁ B (slice (Work.FTS.StrongEps.EpsLocalPStar.iter (Feps α ρ ε Φs E) h₀
        (n + 1)) τ))
    (hlimP : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      EpsClass α ρ ε C₁ B (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Feps α ρ ε Φs E)
        h₀) τ))
    (hreg : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ × ℝ => Work.FTS.StrongEps.EpsLocalPStar.limFam (Feps α ρ ε Φs E) h₀
        p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 δ)) :
    ∃ h : Fam, IsEpsSolP α ρ ε δ Φs E h₀ h ∧ EpsRegP α ρ ε δ h := by
  obtain ⟨h0, hder⟩ :=
    exists_volterra_v4 (α := α) (F := Feps α ρ ε Φs E) (h₀ := h₀)
      (P := fun u => EpsClass α ρ ε C₁ B u) (Cpt := Cpt) (L := L) (δ := δ)
      hδ hL hδL hCpt hP₀ hbd hlip hpt hcontP hzeroP hkeepIter hlimP
  refine ⟨Work.FTS.StrongEps.EpsLocalPStar.limFam (Feps α ρ ε Φs E) h₀,
    IsEpsSolP_of_v4 (α := α) (ε := ε) (δ := δ) (ρ := ρ) (Φs := Φs) (E := E)
      (g₀ := h₀) (h := Work.FTS.StrongEps.EpsLocalPStar.limFam (Feps α ρ ε Φs E) h₀) h0 hder,
    hreg, ?_⟩
  intro τ hτ
  have hP := hlimP τ hτ
  -- the three conjuncts of `EpsDatumP` are the first, second and fourth of `EpsClass`
  -- (`slice (JfamP ρ ε g) τ = Pz (Jeps ρ ε (slice g τ))` is `rfl`)
  exact ⟨hP.1, hP.2.1, by
    show Work.FTS.ClassC.ClassC α (Pz (Jeps ρ ε (slice
      (Work.FTS.StrongEps.EpsLocalPStar.limFam (Feps α ρ ε Φs E) h₀) τ)))
    exact hP.2.2.2.1⟩

end Work.FTS.EpsEngine
