/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsMemRegP.lean` — the regularity package carried by the
# interface `EpsUniformMem`

`EpsUniformMem` (`EpsMem.lean`) is the interface of the strong route: for every horizon `T` and
every small `ε` the `P₀`-corrected scheme has a solution whose projected slices are in class `C`
with `Xn ≤ C₀α²`, whose slices are honest `ℋ⁶` with `Xn6 ≤ K'`, and which is **jointly `C¹` in
`(z,θ,τ)`** on `Ioi 0 ×ˢ Ioo 0 (π/2) ×ˢ Icc 0 T` (the fourth conjunct of the per-`τ` clause: the
τ-regularity of the solution, which is what the fundamental-theorem-of-calculus steps of `E5`
consume).

This module reads the package off the interface in the vocabulary of the E4/E5 chapters:

* `EpsUniformMem.exists_seq_regP` — the sequence `ε k ↓ 0`, the families `g k`, and for every `k`
  the triple `IsEpsSolP … ∧ EpsRegP α ρ (ε k) T (g k) ∧ (the two bounds)`;
* `EpsUniformMem.exists_seq_regP_cont` — the same, together with the **fake-time continuity of the
  scheme's right-hand side** `s ↦ epsRHSP α ρ (ε k) Φs E (g k) s p`, which is the `hcont`
  hypothesis of `EpsLimVolterraP` and of `EpsProfileLip_of_epsWP_corr`; it is produced from the
  joint `C¹` and the equation by `RhsCont.continuousOn_epsRHSP_of_regP`.

The identification `EpsDatumP α ρ ε (slice g τ) = SmoothOpen ∧ HkMem α 6 ∧ ClassC α (Pz (J_ε ·))`
is `rfl`-level: the third conjunct uses `slice_JfamP`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsStructP
import Submission.Work.FTS.StrongEps.EpsUniformMem_seq
import Submission.Work.FTS.StrongEps.RhsCont

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

/-- **The interface, in the vocabulary of the E4/E5 chapters.**  From
`EpsUniformMem α ρ Φs E g₀ C₀ K` and a horizon `T > 0`: a sequence `ε k > 0` with `ε k → 0`, a
sequence of families `g k`, a constant `K' ≥ K`, and for every `k` a *regular* `P₀`-solution
(`IsEpsSolP` together with `EpsRegP`, i.e. joint `C¹` in `(z,θ,τ)` and every slice in `EpsDatumP`)
carrying both a-priori bounds. -/
theorem EpsUniformMem.exists_seq_regP {α C₀ K : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g₀ : Fn} (hU : EpsUniformMem α ρ Φs E g₀ C₀ K) {T : ℝ} (hT : 0 < T) :
    ∃ K' : ℝ, K ≤ K' ∧ ∃ ε : ℕ → ℝ, (∀ k : ℕ, 0 < ε k) ∧
      Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∃ g : ℕ → Fam, ∀ k : ℕ, IsEpsSolP α ρ (ε k) T Φs E g₀ (g k) ∧
        EpsRegP α ρ (ε k) T (g k) ∧
        (∀ τ ∈ Set.Icc 0 T,
          Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε k) (g k)) τ) ≤ C₀ * α ^ 2) ∧
        (∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice (g k) τ) ≤ K') := by
  obtain ⟨hvan, hl12, K', hKK', ε, hεpos, hε0, Maj, _hMaj, g, hg⟩ := hU.exists_seq hT
  refine ⟨K', hKK', ε, hεpos, hε0, g, fun k => ?_⟩
  obtain ⟨hsol, hb⟩ := hg k
  refine ⟨hsol, ⟨(hb 0 ⟨le_rfl, hT.le⟩).2.2.2.2.2.2.1, fun τ hτ => ?_⟩,
    fun τ hτ => (hb τ hτ).2.2.2.1, fun τ hτ => (hb τ hτ).2.2.2.2.1⟩
  exact ⟨(hb τ hτ).1, (hb τ hτ).2.2.1, by rw [← slice_JfamP]; exact (hb τ hτ).2.2.2.2.2.1⟩

/-- **The interface plus the fake-time continuity of the right-hand side.**  The extra clause
supplied here is exactly the `hcont` hypothesis of `EpsLimVolterraP` (and of
`EpsProfileLip_of_epsWP_corr`): the continuity of `s ↦ epsRHSP α ρ (ε k) Φs E (g k) s p` on
`Icc 0 T`, at every point `p` of the open quadrant.  It is *derived*, not assumed: the joint `C¹`
of `EpsRegP` and the scheme's equation give it (`RhsCont.continuousOn_epsRHSP_of_regP`). -/
theorem EpsUniformMem.exists_seq_regP_cont {α C₀ K : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g₀ : Fn} (hU : EpsUniformMem α ρ Φs E g₀ C₀ K) {T : ℝ} (hT : 0 < T) :
    ∃ K' : ℝ, K ≤ K' ∧ ∃ ε : ℕ → ℝ, (∀ k : ℕ, 0 < ε k) ∧
      Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∃ g : ℕ → Fam, ∀ k : ℕ, IsEpsSolP α ρ (ε k) T Φs E g₀ (g k) ∧
        EpsRegP α ρ (ε k) T (g k) ∧
        (∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
          ContinuousOn (fun s : ℝ => epsRHSP α ρ (ε k) Φs E (g k) s p.1 p.2)
            (Set.Icc 0 T)) ∧
        (∀ τ ∈ Set.Icc 0 T,
          Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε k) (g k)) τ) ≤ C₀ * α ^ 2) ∧
        (∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice (g k) τ) ≤ K') := by
  obtain ⟨K', hKK', ε, hεpos, hε0, g, hg⟩ := hU.exists_seq_regP hT
  refine ⟨K', hKK', ε, hεpos, hε0, g, fun k => ?_⟩
  obtain ⟨hsol, hreg, h4, h6⟩ := hg k
  exact ⟨hsol, hreg, continuousOn_epsRHSP_of_regP hT hsol hreg, h4, h6⟩

end Work.FTS.StrongEps
