/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsHlim4.lean` — the slot identification of `epsRHSP` at level 4

`EpsHlim.epsRHSP_slot_tendsto` proves the slotwise convergence of the scheme's right-hand side
`epsRHSP = Pz (J_ε (epsWP))` to `rhsFun`, using the `ℋ⁵`-data of `epsWP` (Gap 2 of the E5 chapter).

The C3 ruling (`sources/ftsV2/fts_strongeps_c1c5_ruling.md` §3) removes the `ℋ⁵` input: the
`P₀`-correction scalar `L₁₂(J_ε (epsWP))(0)/pzNorm` vanishes at level **4** as well
(`EpsCorrTendsto4.EpsCorr_tendsto_zero4`, proved from the new leaf `L12_Jeps_sub_le4`), because the
functional `L₁₂(·)(0)` only sees the *angular* marginal of the convolution.  This module is the
mechanical switch: the same proof as `EpsHlim`, with `h5`/`hb5` replaced by
`h4`/`hb4` and `EpsCorr_tendsto_zero` replaced by `EpsCorr_tendsto_zero4`.

Everything here is `sorry`-free (modulo the leaf `L12_Jeps_sub_le4`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz
import Submission.Work.FTS.StrongEps.JepsSmoothOpen
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup
import Submission.Work.FTS.StrongEps.mixed_Jeps_tendsto
import Submission.Work.FTS.StrongEps.EpsCorrTendsto4
import Submission.Work.FTS.StrongEps.EpsHlim

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

/-- **The slot-level identification at level 4** (C3 ruling): the same convergence as
`epsRHSP_slot_tendsto`, with the `ℋ⁵`-data of `epsWP` replaced by `ℋ⁴`-data (which
`epsWP_hkMem4_bnd_unif` provides). -/
theorem epsRHSP_slot_tendsto4 {α B B4 Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g : Fam} {ε : ℕ → ℝ} {G : ℕ → Fam} {s : ℝ}
    (hρ : IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (epsWP α ρ (ε n) Φs E (G n) s)) Quad)
    (hconv : ConvLocUnifH6 α B (fun n => epsWP α ρ (ε n) Φs E (G n) s)
      (rhsFun α Φs E g s))
    (hεpos : ∀ n : ℕ, 0 < ε n) (hε1 : ∀ n : ℕ, ε n ≤ 1)
    (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsm4 : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ (ε n) Φs E (G n) s))
    (h4 : ∀ n : ℕ, Work.Spaces.HkMem α 4 (epsWP α ρ (ε n) Φs E (G n) s))
    (hb4 : ∀ n : ℕ, Work.Spaces.HkNorm α 4 (epsWP α ρ (ε n) Φs E (G n) s) ≤ B4)
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
  -- the correction scalar vanishes (level-4 route)
  have hc : Filter.Tendsto
      (fun n : ℕ => Work.Construction.L12
        (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
      Filter.atTop (nhds 0) :=
    EpsCorr_tendsto_zero4 (α := α) (Cs := Cs) (B := B4) hρ hα hstar hεpos hε1 hε0 hsm4 h4 hb4 h0
  -- the correction term vanishes (the correction profile is bounded on the compact)
  obtain ⟨Cb, _hCb0, hbump⟩ := exists_bound_mixed_bump ({p} : Set (ℝ × ℝ)) isCompact_singleton
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
      have h5 : Filter.Tendsto (fun n : ℕ => |(Work.Construction.L12
            (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0 / pzNorm)
          * Work.Spaces.mixed j i bump p.1 p.2|) Filter.atTop (nhds 0) := by
        simpa only [abs_mul] using h2
      exact (tendsto_zero_iff_abs_tendsto_zero _).mpr h5
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
