/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsUniformMem_seq.lean` — the entry point of E5

`EpsUniformMem` (`EpsMem.lean`) is a *uniform-in-`ε`* statement: for every horizon `T` there is a
threshold `ε₁ > 0` and a constant `K' ≥ K` such that for every `ε ∈ (0,ε₁]` the **`P₀`-corrected**
scheme has a solution on `[0,T]` whose projected slices are honestly in `ℋ⁴` with `Xn ≤ C₀α²` and
whose slices are honestly in `ℋ⁶` with `Xn6 ≤ K'`.

The E5 chapter (`exists_limH`) works with a *sequence*: it needs `ε k ↓ 0` and a fixed family
sequence with the uniform bounds, so that the extraction bricks (`EpsConvAllH`, `EpsConvLev0`,
`EpsConvSubseq`) and the τ-modulus `EpsSlotLipP` apply.  This module performs that trivial but
load-bearing step (the `P`-analogue of `EpsUniform_exists_seq.lean`): the sequence
`ε k = ε₁/(k+1)` lies in `(0,ε₁]` and tends to `0`.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsMem

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

/-- **The E5 entry point**: a uniform `ε`-bound produces a positive sequence `ε k → 0` and a
sequence of `P₀`-scheme solutions on `[0,T]` with all the membership and bound clauses carried
along.  The horizon constant `K' ≥ K` is *also* returned (it is existential in `EpsUniformMem`). -/
theorem EpsUniformMem.exists_seq {α C₀ K : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g₀ : Fn} (hU : EpsUniformMem α ρ Φs E g₀ C₀ K) {T : ℝ} (hT : 0 < T) :
    (∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) ∧ Work.Construction.L12 g₀ 0 = 0 ∧
    ∃ K' : ℝ, K ≤ K' ∧ ∃ ε : ℕ → ℝ, (∀ k : ℕ, 0 < ε k) ∧
      Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∃ Maj : ℝ → ℝ, MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0) ∧
      ∃ g : ℕ → Fam, ∀ k : ℕ, IsEpsSolP α ρ (ε k) T Φs E g₀ (g k) ∧
        ∀ τ ∈ Set.Icc 0 T,
          Work.FTS.EllipticEst.SmoothOpen (slice (g k) τ) ∧
            Work.Spaces.HkMem α 4 (slice (JfamP ρ (ε k) (g k)) τ) ∧
            Work.Spaces.HkMem α 6 (slice (g k) τ) ∧
            Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε k) (g k)) τ) ≤ C₀ * α ^ 2 ∧
            Work.FTS.StrongGlobal.Xn6 α (slice (g k) τ) ≤ K' ∧
            Work.FTS.ClassC.ClassC α (slice (JfamP ρ (ε k) (g k)) τ) ∧
            ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g k p.1 p.2.1 p.2.2)
              (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T) ∧
            EpsDecay α ρ Φs E (ε k) τ (g k) Maj := by
  obtain ⟨K', hKK', ε₁, hε₁pos, Maj, hMajint, hε₁⟩ := hU.2.2 T hT
  have hpos : ∀ k : ℕ, 0 < ε₁ / (k + 1 : ℝ) := fun k =>
    div_pos hε₁pos (by positivity)
  have hle : ∀ k : ℕ, ε₁ / (k + 1 : ℝ) ≤ ε₁ := by
    intro k
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
    calc ε₁ = ε₁ * 1 := (mul_one ε₁).symm
      _ ≤ ε₁ * ((k : ℝ) + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hε₁pos.le
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have htend : Filter.Tendsto (fun k : ℕ => ε₁ / (k + 1 : ℝ)) Filter.atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε₁
    simpa [div_eq_mul_inv] using h
  have hex : ∀ k : ℕ, ∃ g : Fam,
      IsEpsSolP α ρ (ε₁ / (k + 1 : ℝ)) T Φs E g₀ g ∧
        ∀ τ ∈ Set.Icc 0 T,
          Work.FTS.EllipticEst.SmoothOpen (slice g τ) ∧
            Work.Spaces.HkMem α 4 (slice (JfamP ρ (ε₁ / (k + 1 : ℝ)) g) τ) ∧
            Work.Spaces.HkMem α 6 (slice g τ) ∧
            Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε₁ / (k + 1 : ℝ)) g) τ) ≤ C₀ * α ^ 2 ∧
            Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ K' ∧
            Work.FTS.ClassC.ClassC α (slice (JfamP ρ (ε₁ / (k + 1 : ℝ)) g) τ) ∧
            ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
              (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T) ∧
            EpsDecay α ρ Φs E (ε₁ / (k + 1 : ℝ)) τ g Maj :=
    fun k => hε₁ _ ⟨hpos k, hle k⟩
  choose g hg using hex
  exact ⟨hU.1, hU.2.1, K', hKK', fun k => ε₁ / (k + 1 : ℝ), hpos, htend, Maj, hMajint, g, hg⟩

end Work.FTS.StrongEps
