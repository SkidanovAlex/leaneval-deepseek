/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5G/TowerDecay.lean` — the tower *with* the decay majorant

`E5G/Tower.lean`'s `tower_exists` extracts from `EpsUniformMem` the datum sequence `e ↓ 0`, the
horizon constants `K' n` and the two-index family of solutions `G n k` (for `n ≤ k`).  It drops
one conjunct of the interface: the **radial decay majorant** `Maj` of the clause
`Work.FTS.StrongEps.EpsDecay` (`EpsMem.lean`), which `EpsUniformMem` quantifies *before* `∀ ε`, so
that one and the same `Maj` serves the whole horizon-`h` sequence.

That majorant is not cosmetic: it is exactly what the pointwise identification of the scheme's
right-hand side with the limiting one (`hlim` of E5) consumes.  The modulation constants
`muDyn`/`lamDyn` are built from the *radial* zero modes `L₁₂(·)(0) = ∫_0^∞ (1/s)∫_θ K(θ)·(s,θ) ds`,
which are bounded but **not continuous** along a locally uniformly convergent sequence with
uniform `ℋ⁴`/`ℋ⁶`-bounds; their convergence needs dominated convergence in the radial variable,
i.e. a majorant `Maj` with `∫_0^∞ Maj(s)/s ds < ∞`, uniform in `ε`.  The child that reviewed
`E5G.EpsLimPkg_of_horizon` returned it FALSE as stated for exactly this reason (see
`NOTES_session19.md` §7 and `E5G/PkgOfHlim.lean`'s header), and its repair is either to add the
pointwise identification as a hypothesis or to make the majorant available along the tower — which
is what this module does, **without changing any statement of `TowerAt`** (the extra data lives
beside it).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.E5G.Tower
import Submission.Work.FTS.StrongEps.EpsUniformMem_seq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The tower together with the radial decay majorant.**  Same conclusion as `tower_exists`,
plus a per-horizon majorant `Maj n` which is `1/z`-integrable and whose `EpsDecay` clause holds for
the whole horizon-`n` sequence at every fake time of `[0, Tn n]`. -/
theorem tower_exists_decay {α C₀ K : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    (hU : EpsUniformMem α ρ Φs E g₀ C₀ K) :
    ∃ (e : ℕ → ℝ) (G : ℕ → ℕ → Fam) (K' : ℕ → ℝ) (Maj : ℕ → ℝ → ℝ),
      (∀ k : ℕ, e k ∈ Set.Ioc 0 1) ∧ Tendsto e atTop (nhds 0) ∧
      (∀ n : ℕ, MeasureTheory.IntegrableOn (fun z => Maj n z / z) (Set.Ioi 0)) ∧
      (∀ n k : ℕ, n ≤ k → TowerAt α C₀ ρ Φs E g₀ n (e k) (K' n) (G n k) ∧
        ∀ τ ∈ Set.Icc 0 (Tn n), EpsDecay α ρ Φs E (e k) τ (G n k) (Maj n)) := by
  classical
  -- ## the per-horizon interface data, *keeping* the majorant
  have hper : ∀ n : ℕ, ∃ K' ε₁ : ℝ, ∃ Maj : ℝ → ℝ, K ≤ K' ∧ 0 < ε₁ ∧
      MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0) ∧
      ∀ ε ∈ Set.Ioc 0 ε₁, ∃ g : Fam, TowerAt α C₀ ρ Φs E g₀ n ε K' g ∧
        ∀ τ ∈ Set.Icc 0 (Tn n), EpsDecay α ρ Φs E ε τ g Maj := by
    intro n
    obtain ⟨K', hK', ε₁, hε₁, Maj, hMaj, hg⟩ := hU.2.2 (Tn n) (Tn_pos n)
    refine ⟨K', ε₁, Maj, hK', hε₁, hMaj, fun ε hε => ?_⟩
    obtain ⟨g, hsol, hcl⟩ := hg ε hε
    have h0 := hcl 0 ⟨le_rfl, (Tn_pos n).le⟩
    exact ⟨g, ⟨hsol, fun τ hτ => (hcl τ hτ).1, fun τ hτ => (hcl τ hτ).2.1,
      fun τ hτ => (hcl τ hτ).2.2.1, fun τ hτ => (hcl τ hτ).2.2.2.1,
      fun τ hτ => (hcl τ hτ).2.2.2.2.1, fun τ hτ => (hcl τ hτ).2.2.2.2.2.1,
      h0.2.2.2.2.2.2.1⟩,
      fun τ hτ => (hcl τ hτ).2.2.2.2.2.2.2⟩
  let K' : ℕ → ℝ := fun n => Classical.choose (hper n)
  let ε₁ : ℕ → ℝ := fun n => Classical.choose (Classical.choose_spec (hper n))
  let Maj : ℕ → ℝ → ℝ := fun n =>
    Classical.choose (Classical.choose_spec (Classical.choose_spec (hper n)))
  have hspec : ∀ n : ℕ, K ≤ K' n ∧ 0 < ε₁ n ∧
      MeasureTheory.IntegrableOn (fun z => Maj n z / z) (Set.Ioi 0) ∧
      ∀ ε ∈ Set.Ioc 0 (ε₁ n), ∃ g : Fam, TowerAt α C₀ ρ Φs E g₀ n ε (K' n) g ∧
        ∀ τ ∈ Set.Icc 0 (Tn n), EpsDecay α ρ Φs E ε τ g (Maj n) := fun n =>
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hper n)))
  have hε₁pos : ∀ n : ℕ, 0 < ε₁ n := fun n => (hspec n).2.1
  have hMajint : ∀ n : ℕ,
      MeasureTheory.IntegrableOn (fun z => Maj n z / z) (Set.Ioi 0) :=
    fun n => (hspec n).2.2.1
  have hg : ∀ n : ℕ, ∀ ε ∈ Set.Ioc 0 (ε₁ n), ∃ g : Fam,
      TowerAt α C₀ ρ Φs E g₀ n ε (K' n) g ∧
        ∀ τ ∈ Set.Icc 0 (Tn n), EpsDecay α ρ Φs E ε τ g (Maj n) :=
    fun n => (hspec n).2.2.2
  -- ## the global datum sequence
  refine ⟨dataSeq ε₁, fun n k => if h : n ≤ k then
      Classical.choose (hg n (dataSeq ε₁ k)
        ⟨dataSeq_pos hε₁pos k, dataSeq_le (fun k => (hε₁pos k).le) h⟩)
      else fun z θ _ => g₀ z θ,
    K', Maj, ⟨fun k => ⟨dataSeq_pos hε₁pos k, dataSeq_le_one ε₁⟩,
      dataSeq_tendsto (fun k => (hε₁pos k).le), hMajint, ?_⟩⟩
  intro n k hnk
  have h := Classical.choose_spec (hg n (dataSeq ε₁ k)
    ⟨dataSeq_pos hε₁pos k, dataSeq_le (fun k => (hε₁pos k).le) hnk⟩)
  simpa only [dif_pos hnk] using h

end Work.FTS.StrongEps.E5G
