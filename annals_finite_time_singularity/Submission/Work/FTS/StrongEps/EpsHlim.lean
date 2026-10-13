/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsHlim.lean` — the slot-level identification `epsRHSP → rhsFun`

This module performs the last *formal* step of the identification `hlim` of `E5-3`: from the
convergence package of the *pre-mollified* right-hand sides

  `ConvLocUnifH6 α B (fun n => epsWP α ρ (ε n) Φs E (G n) s) (rhsFun α Φs E g s)`

(which is what `epsWP_tendsto` supplies pointwise, upgraded to locally uniform by the extraction's
slot convergence) together with the `h0`-clause `L₁₂(epsWP …)(0) = 0` (the proved `EpsZeroMode` for
the projected family) and the `ℋ⁵`-data of `epsWP`, the slots of the scheme's right-hand side

  `epsRHSP … = Pz (J_ε (epsWP …)) = J_ε (epsWP …) − (L₁₂(J_ε(epsWP …))(0)/pzNorm)·bump`

converge to the slots of `rhsFun`.  The two ingredients are the proved `mixed_Jeps_tendsto`
(the mollification converges) and `EpsCorr_tendsto_zero` (the rank-one correction vanishes).

Nothing here is analytic beyond what is already proved; the module is the `pointwise` analogue of
`ConvLocUnifH6_JfamP`'s argument.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz
import Submission.Work.FTS.StrongEps.JepsSmoothOpen
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup
import Submission.Work.FTS.StrongEps.mixed_Jeps_tendsto
import Submission.Work.FTS.StrongEps.EpsCorrTendsto
import Submission.Work.FTS.StrongEps.EpsLimitDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **The slot-level identification.**  If the pre-mollified right-hand sides converge to `rhsFun`
in the `ConvLocUnifH6`-sense, if their `L₁₂`-zero modes vanish and if they are honestly `ℋ⁵` with a
uniform bound, then every slot of order `≤ 4` of the scheme's right-hand side converges to the
corresponding slot of `rhsFun`. -/
theorem epsRHSP_slot_tendsto {α B B5 Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g : Fam} {ε : ℕ → ℝ} {G : ℕ → Fam} {s : ℝ}
    (hρ : IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (epsWP α ρ (ε n) Φs E (G n) s)) Quad)
    (hconv : ConvLocUnifH6 α B (fun n => epsWP α ρ (ε n) Φs E (G n) s)
      (rhsFun α Φs E g s))
    (hεpos : ∀ n : ℕ, 0 < ε n) (hε1 : ∀ n : ℕ, ε n ≤ 1)
    (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsm5 : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ (ε n) Φs E (G n) s))
    (h5 : ∀ n : ℕ, Work.Spaces.HkMem α 5 (epsWP α ρ (ε n) Φs E (G n) s))
    (hb5 : ∀ n : ℕ, Work.Spaces.HkNorm α 5 (epsWP α ρ (ε n) Φs E (G n) s) ≤ B5)
    (h0 : ∀ n : ℕ, Work.Construction.L12 (epsWP α ρ (ε n) Φs E (G n) s) 0 = 0)
    {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) {j i : ℕ} (hji : j + i ≤ 4) :
    Filter.Tendsto
      (fun n : ℕ => Work.Spaces.mixed j i (epsRHSP α ρ (ε n) Φs E (G n) s) p.1 p.2)
      Filter.atTop (nhds (Work.Spaces.mixed j i (rhsFun α Φs E g s) p.1 p.2)) := by
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hθ : p.2 ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ1⟩
  -- the mollified slots converge
  have hJ : Filter.Tendsto
      (fun n : ℕ => Work.Spaces.mixed j i
        (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) p.1 p.2)
      Filter.atTop (nhds (Work.Spaces.mixed j i (rhsFun α Φs E g s) p.1 p.2)) :=
    mixed_Jeps_tendsto hρ.moll hsm hconv hεpos hε0 hp hji
  -- the correction scalar vanishes
  have hc : Filter.Tendsto
      (fun n : ℕ => Work.Construction.L12
        (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
      Filter.atTop (nhds 0) := by
    exact EpsCorr_tendsto_zero (α := α) (C₀ := 0) (Cs := Cs) (B := B5) hρ hα hstar hεpos hε1
      hε0 hsm5 h5 hb5 h0
  -- the correction term vanishes (the correction profile is bounded on the compact)
  obtain ⟨Cb, hCb0, hbump⟩ := exists_bound_mixed_bump ({p} : Set (ℝ × ℝ)) isCompact_singleton
  have hbump' : ∀ n : ℕ, |Work.Spaces.mixed j i bump p.1 p.2| ≤ Cb :=
    fun _ => hbump j i hji p (Set.mem_singleton p)
  have hcorr : Filter.Tendsto
      (fun n : ℕ => (Work.Construction.L12
          (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
        * Work.Spaces.mixed j i bump p.1 p.2)
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto
        (fun n : ℕ => |Work.Construction.L12
            (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm| * Cb)
        Filter.atTop (nhds 0) := by
      have := hc.abs.mul_const Cb
      simpa using this
    have h2 : Filter.Tendsto
        (fun n : ℕ => |Work.Construction.L12
            (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm|
          * |Work.Spaces.mixed j i bump p.1 p.2|) Filter.atTop (nhds 0) :=
      squeeze_zero (fun n => mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (fun n => mul_le_mul_of_nonneg_left (hbump' n) (abs_nonneg _)) h1
    have h3 : Filter.Tendsto
        (fun n : ℕ => (Work.Construction.L12
            (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
          * Work.Spaces.mixed j i bump p.1 p.2) Filter.atTop (nhds 0) := by
      have h4 : Filter.Tendsto (fun n : ℕ => |(Work.Construction.L12
            (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
          * Work.Spaces.mixed j i bump p.1 p.2|) Filter.atTop (nhds 0) := by
        simpa only [abs_mul] using h2
      exact (tendsto_zero_iff_abs_tendsto_zero _).mpr h4
    exact h3
  -- the pointwise split of the projection
  have hsplit : (fun n : ℕ => Work.Spaces.mixed j i (epsRHSP α ρ (ε n) Φs E (G n) s) p.1 p.2)
      = fun n : ℕ => Work.Spaces.mixed j i
            (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) p.1 p.2
          - (Work.Construction.L12
              (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
            * Work.Spaces.mixed j i bump p.1 p.2 := by
    funext n
    rw [epsRHSP_eq_Pz_Jeps_epsWP,
      PZeroAux.mixed_Pz (smoothOpen_Jeps ρ hρ (hεpos n) (hsm n)) hz hθ j i]
  rw [hsplit]
  simpa using hJ.sub hcorr

end Work.FTS.StrongEps
