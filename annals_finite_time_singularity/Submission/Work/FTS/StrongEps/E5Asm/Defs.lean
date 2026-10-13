/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5Asm/Defs.lean` — the vocabulary of the E5 **assembly**

The E5 chapter (`EpsLimit.lean`, `exists_limH`) has to turn the extraction of the `ε`-scheme
(`E5Extract_of_mem`: for every horizon `T` a sequence `G`, a strictly increasing `φ` and a limit
curve `F` with `ConvLocUnifH6 α B (slice (G (φ n)) τ) (F τ)` at every `τ ∈ [0,T]`) into the
package `EpsLimPkg` for the **quadrant clamp** `clampQ F g₀` of the limit.

Everything that the *extraction* alone produces is bundled here as `EpsAsmData`, together with the
**supply clauses** — the clauses that the frozen hypotheses of `exists_limH` do *not* determine,
each of which is a named obligation of another chapter (see `NOTES_session18.md`):

| clause | what it is | producer |
|---|---|---|
| `hE2` | `ContDiffOn ℝ 2 (E (slice g τ))` at limit slices (**Gap 1**) | elliptic area (`PkgCos`) via `E5Aux3.contDiffOn_two_E_of_pin` |
| `hl12` | `L₁₂ (J_ε (slice (G (φ n)) τ)) 0 → 0` along the extraction | `E5Aux3.hl12_of_supply` (needs the `L₁₂`-density majorant) |
| `hlim` | pointwise identification `epsRHSP … → rhsFun …` (**Gap 2**) | `EpsHlim.epsRHSP_slot_tendsto` (needs the `ℋ⁵`-data of `epsWP`) |
| `hWc` | joint continuity of `rhsFun α Φs E (clampQ F g₀)` | joint regularity of the limit family's slots |
| `hdbd` | the `ℋ³`-bound on `∂_τ` at the limit (`dbd`) | `EpsGdotThirdHP` / the level-3 Fatou route (needs `L3Data` + level-4 sup bounds) |
| `hapx` | the G2 approximation clause `LimApproxOn` | the `LimApproxOn` producer (mollified approximants) |

Everything *else* (`init`, `vanish`, `c4`, `bd6`, `cont`, `bd4`, `mem4`, `law`, `eqT`, `c1`) is
**proved** from these in `E5Asm/LimPkg.lean`.

The module also carries the clamp-congruence of the convergence package, which is what lets the
clauses be stated for the clamped family.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.E5Clamp
import Submission.Work.FTS.StrongEps.E5Clauses
import Submission.Work.FTS.StrongEps.E5Law
import Submission.Work.FTS.StrongEps.EpsSlotAux
import Submission.Work.FTS.StrongEps.ConvLocUnifH6_JfamP
import Submission.Work.FTS.StrongEps.RhsCont
import Submission.Work.FTS.StrongEps.E5ExtractMem
import Submission.Work.FTS.StrongEps.EpsMemRegP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Asm

open Work.FTS.Galerkin (Fn Fam slice gdot)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The clamp congruence of the convergence package -/

/-- **The quadrant clamp does not change the convergence package.**  `clampQ F g₀` agrees with `F`
on the open quadrant — and `Q0` is open, so every `mixed`-slot of the two agrees at every point of
`Q0` (locality of `deriv`), while the slot-convergence clause of `ConvLocUnifH6` is uniform on
compacts of `Q0` and the `ℋᵏ`-integrals only see the quadrant (`clampQ_hkNorm`). -/
theorem ConvLocUnifH6.clampQ_congr {α B : ℝ} {G : ℕ → Fn} {F : ℝ → Fn} {g₀ : Fn} {τ : ℝ}
    (h : ConvLocUnifH6 α B G (F τ)) :
    ConvLocUnifH6 α B G (slice (clampQ F g₀) τ) := by
  refine ⟨?_, clampQ_contDiffOn h.2.1, ?_⟩
  · intro K hK hKQ j i hji
    refine (h.1 K hK hKQ j i hji).congr_right ?_
    intro p hp
    exact (Work.FTS.StrongEps.mixed_congr_of_isOpen (V := Work.FTS.EllipticEst.Q0)
      Work.FTS.EllipticEst.isOpen_Q0
      (f := F τ) (g := slice (clampQ F g₀) τ)
      (fun q hq => (clampQ_of_mem hq.1 ⟨hq.2.1, hq.2.2⟩).symm) j i) (hKQ hp)
  · rw [clampQ_hkNorm]
    exact h.2.2

/-! ## The assembly data -/

/-- **The data of the E5 assembly**: the extraction output at the horizon `T`, its interface
properties (the extraction's own clauses, all read off `EpsUniformMem`), and the six supply
clauses of the module header. -/
structure EpsAsmData (α C₀ K B Cd T : ℝ) (ρ : ℝ × ℝ → ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (ε : ℕ → ℝ) (G : ℕ → Fam) (φ : ℕ → ℕ) (F : ℝ → Fn) : Prop where
  /-- the horizon is positive. -/
  hT : 0 < T
  /-- the exponent range of the interface's energy estimates. -/
  hα : α ∈ Set.Ioc 0 1
  /-- the mollifier is admissible. -/
  hρ : IsSmoothKernel ρ
  /-- the datum vanishes on the two angular boundary lines (a *necessary* interface clause). -/
  hvan : ∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0
  /-- the `ℋ⁶`-bound is non-negative. -/
  hB0 : 0 ≤ B
  /-- the mollification parameters are positive. -/
  hεpos : ∀ k : ℕ, 0 < ε k
  /-- and bounded by `1`. -/
  hε : ∀ k : ℕ, ε k ∈ Set.Ioc 0 1
  /-- and tend to `0`. -/
  hε0 : Tendsto ε atTop (nhds 0)
  /-- the sub-sequence index is strictly increasing. -/
  hφ : StrictMono φ
  /-- the `ε`-solutions of the projected scheme. -/
  hsol : ∀ k : ℕ, IsEpsSolP α ρ (ε k) T Φs E g₀ (G k)
  /-- their τ-regularity. -/
  hreg : ∀ k : ℕ, EpsRegP α ρ (ε k) T (G k)
  /-- all-order smoothness of the slices. -/
  hsmcd : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T, ∀ n : ℕ,
    ContDiffOn ℝ n (Function.uncurry (slice (G k) τ)) Quad
  /-- honest `ℋ⁶`-membership of the slices. -/
  hmem6 : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 6 (slice (G k) τ)
  /-- the uniform `ℋ⁶`-bound of the slices. -/
  hb6 : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice (G k) τ) ≤ B
  /-- the *projected* slices are class `C`. -/
  hC : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T,
    Work.FTS.ClassC.ClassC α (slice (JfamP ρ (ε k) (G k)) τ)
  /-- the uniform `ℋ⁴`-bound of the *projected* slices. -/
  hb4 : ∀ k : ℕ, ∀ τ ∈ Set.Icc 0 T,
    Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε k) (G k)) τ) ≤ C₀ * α ^ 2
  /-- the convergence package of the extraction. -/
  hconv : ∀ τ ∈ Set.Icc 0 T, ConvLocUnifH6 α B (fun n : ℕ => slice (G (φ n)) τ) (F τ)
  /-- the level-`1` τ-Lipschitz property of the approximants (from `EpsSlotLipP`). -/
  hlip : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Quad → ∃ C : ℝ, 0 ≤ C ∧
    ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 1 → ∀ p ∈ K,
      ∀ τ ∈ Set.Icc 0 T, ∀ τ' ∈ Set.Icc 0 T,
        |Work.Spaces.mixed j i (slice (G (φ n)) τ) p.1 p.2
          - Work.Spaces.mixed j i (slice (G (φ n)) τ') p.1 p.2| ≤ C * |τ - τ'|
  /-- **(supply, Gap 1)** the elliptic image of the limit slice is `C²` on the open quadrant. -/
  hE2 : ∀ τ ∈ Set.Icc 0 T,
    ContDiffOn ℝ 2 (Function.uncurry (E (slice (clampQ F g₀) τ))) Quad
  /-- **(supply)** the `L₁₂`-zero mode of the mollified slice vanishes in the limit. -/
  hl12 : ∀ τ ∈ Set.Icc 0 T, Tendsto (fun n : ℕ => Work.Construction.L12
      (Jeps ρ (ε (φ n)) (slice (G (φ n)) τ)) 0) atTop (nhds 0)
  /-- **(supply, Gap 2)** the pointwise identification of the scheme's right-hand side. -/
  hlim : ∀ p : ℝ × ℝ, p ∈ Quad → ∀ s ∈ Set.Icc 0 T, Tendsto
    (fun n : ℕ => epsRHSP α ρ (ε (φ n)) Φs E (G (φ n)) s p.1 p.2) atTop
      (nhds (rhsFun α Φs E (clampQ F g₀) s p.1 p.2))
  /-- **(supply)** joint continuity of the limiting right-hand side on the interior, up to the
  horizon (`Icc 0 T` in the fake time, so that the `eqT` row can restrict it to a fixed point). -/
  hWc : ContinuousOn (fun p : ℝ × ℝ × ℝ => rhsFun α Φs E (clampQ F g₀) p.2.2 p.1 p.2.1)
    (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T)
  /-- **(supply)** the `ℋ³`-bound of the fake-time derivative at the limit. -/
  hdbd : ∀ τ : ℝ, 0 < τ → τ < T →
    Work.Spaces.HkMem α 3 (gdot (clampQ F g₀) τ) ∧
      Work.Spaces.HkNorm α 3 (gdot (clampQ F g₀) τ) ≤ Cd
  /-- **(supply)** the G2 approximation clause at the clamped family. -/
  hapx : ∀ T' : ℝ, 0 < T' → T' ≤ T → LimApproxOn α C₀ T' Φs E (clampQ F g₀)

end Work.FTS.StrongEps.E5Asm
