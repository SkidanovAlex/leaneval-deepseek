/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5ExtractHbdd.lean` — the extraction with the *value* bound

`E5Extract` (`E5Extract.lean`) produces the subsequence and the limit curve from a sequence of
`P₀`-solutions plus the four inputs of `E5Equi` (`hcont`, `hwin`, `hcorr`, `hreg`), where `hwin`
is the **slot-wise** sup bound on `epsWP` (slots `≤ 4`) — the level-six chapter of the area.

The extraction only needs the *level-`0`* τ-Lipschitz property `hequi`, and the proved
`EpsProfileLip` produces it from the **value** bounds alone (`hcont` + a compact bound on
`epsRHSP`).  This module records that route: `E5Extract_of_hbdd` is `E5Extract` with
`hwin`/`hcorr`/`hreg` replaced by the compact value bound `hbdd`, which the session-14 bricks
produce from the interface data (`EpsHbdd.hbdd_of_mem_compact`, via `epsWP_sup_le_fam` +
`epsWP_hkMem4_bnd_fam` + `smoothOpen_epsWP` + `exists_shift_window_compact`).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E5Extract
import Submission.Work.FTS.StrongEps.EpsProfileLip

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

/-- **The extraction, from the value bound of `epsRHSP`.**  Same conclusion as `E5Extract`, with
`hequi` produced by `EpsProfileLip` instead of `E5Equi`. -/
theorem E5Extract_of_hbdd {α B T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {ε : ℕ → ℝ} {G : ℕ → Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ)
    (hε : ∀ k : ℕ, ε k ∈ Set.Ioc 0 1)
    (hsol : ∀ k : ℕ, IsEpsSolP α ρ (ε k) T Φs E g₀ (G k))
    (hsm : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (slice (G k) τ))
    (hmem6 : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 6 (slice (G k) τ))
    (hb6 : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.StrongGlobal.Xn6 α (slice (G k) τ) ≤ B)
    (hcont : ∀ k : ℕ, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => epsRHSP α ρ (ε k) Φs E (G k) s p.1 p.2) (Set.Icc 0 T))
    (hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ p ∈ K,
        |epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C) :
    ∃ (φ : ℕ → ℕ) (F : ℝ → Fn), StrictMono φ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) T,
        ConvLocUnifH6 α B (fun n => slice (G (φ n)) τ) (F τ) := by
  -- the raw `ContDiffOn` form of the smoothness clause, as `EpsConvRat` asks for it
  have hsm' : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (slice (G n) τ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n τ hτ k => (hsm n τ hτ).forall k
  -- **Step 1.** the diagonal extraction over the rational times
  obtain ⟨φ, F, hφ, hconvR⟩ := EpsConvRat (α := α) (B := B) (T := T) hα.1
    (G := G) hsm' hmem6 hb6
  -- the level-`0` Lipschitz property of the profiles, from the *value* bound only
  have hequi := EpsProfileLip (α := α) (T := T) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀)
    (ε := ε) (G := G) hsol hcont hbdd
  -- **Step 2.** the limit at the given `τ` (a fresh extraction, coherent via Cauchy)
  have hAll : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ∃ f : Fn, ConvLocUnifH6 α B (fun n => slice (G (φ n)) τ) f :=
    fun τ hτ => EpsConvAllTau (α := α) (B := B) (T := T) hα.1 (G := G) (F := F) (φ := φ) hφ
      hsm' hmem6 hb6 (fun σ hσ => (hconvR σ hσ).toLev0) hequi τ hτ
  -- **Step 3.** the two pieces, as a total function of `τ`
  have htot : ∀ τ : ℝ, ∃ f : Fn,
      τ ∈ Set.Icc (0 : ℝ) T → ConvLocUnifH6 α B (fun n => slice (G (φ n)) τ) f := by
    intro τ
    by_cases hT : τ ∈ Set.Icc (0 : ℝ) T
    · by_cases hq : τ ∈ Set.range (fun q : ℚ => (q : ℝ))
      · exact ⟨F τ, fun _ => hconvR τ ⟨hT, hq⟩⟩
      · obtain ⟨f, hf⟩ := hAll τ hT
        exact ⟨f, fun _ => hf⟩
    · exact ⟨F τ, fun h => absurd h hT⟩
  refine ⟨φ, fun τ => Classical.choose (htot τ), hφ, fun τ hτ => ?_⟩
  exact Classical.choose_spec (htot τ) hτ

end Work.FTS.StrongEps
