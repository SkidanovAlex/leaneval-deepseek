import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.RingTheory.Finiteness.Prod
import Submission.Work.FTS.StrongEps.E4R3.Chapters
import Submission.Work.FTS.StrongEps.EpsE4Thr.AprioriHalves
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.IP6_cs_coeffs
import Submission.Work.FTS.StrongPersist.StarPkg6OfCore
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_FinalLeaves.kernel_exists_proved

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `StrongEps/E4R3/Apriori4Defs.lean` — vocabulary of the corrected a-priori chapter (v4)

curric-46 install (2026-10-12) of `cbc/fts_apriori6_ruling.md` §3 + `cbc/fts_apriori6_ruling_REVIEW.md`
(fixes F1–F3).  Replaces `AprioriChapter3` (unprovable as stated: the `ℋ⁶`-half has no ε-uniform
producer, see the ruling §Verdict) by `AprioriChapter4` = `AprioriChapter3` + `StarPkg6`, with the
`ℋ⁶`-half run on the **raw** slice energy `rawE6` and a **symmetric** kernel.

PROVED here: `kernel_exists_symm` (L0, review F2), `starPkg6_of_starCore` (L1, review F2, from
`StrongPersist.StarPkg6OfCore`), `AprioriPFourth.toB`.  Leaves: `E4R3/Apriori4Leaves/*`,
`E4R3/Sixth4.lean`, `E4R3/Fourth4.lean`; assembly: `E4R3/Apriori4.lean`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6)
open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option linter.unusedVariables false

/-- shorthand: the all-ones level-six inner product of the energy route. -/
abbrev IP6o (α : ℝ) : Fn → Fn → ℝ := Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α

/-- The level-six energy of the **raw** slice (not of the mollified one). -/
def rawE6 (α : ℝ) (g : Fam) (τ : ℝ) : ℝ := IP6o α (slice g τ) (slice g τ)

/-- (L0, PROVED — review F2) a SYMMETRIC smooth kernel exists: the wire's `kerBump.normed` is a
`ContDiffBump` centred at `0`, hence even (`ContDiffBump.normed_neg`). -/
theorem kernel_exists_symm :
    ∃ ρ : ℝ × ℝ → ℝ, IsSmoothKernel ρ ∧ ∀ p : ℝ × ℝ, ρ (-p) = ρ p := by
  refine ⟨Work.FTS_FinalLeaves.kerBump.normed MeasureTheory.volume,
    ⟨fun n => Work.FTS_FinalLeaves.kerBump.contDiff_normed (μ := MeasureTheory.volume),
      Work.FTS_FinalLeaves.kerBump.continuous_normed,
      fun p hp => Work.FTS_FinalLeaves.kerBump_support_pointwise p hp,
      fun p => Work.FTS_FinalLeaves.kerBump.nonneg_normed p,
      by simpa using Work.FTS_FinalLeaves.kerBump.integral_normed (μ := MeasureTheory.volume)⟩,
    fun p => Work.FTS_FinalLeaves.kerBump.normed_neg p⟩

/-- (L1, PROVED — review F2) the order-six star package from `StarCore`, via the proved
`StrongPersist.StarPkg6OfCore` (which needs `α ≤ 1/4`; here `α ≤ 1/5`). -/
theorem starPkg6_of_starCore : ∃ C : ℝ, 0 < C ∧ ∀ (α Cs : ℝ) (Φs : Fn),
    0 < α → α ≤ 1 / 5 → 0 < Cs → Work.FTS.VocabO2.StarCore α Cs Φs →
    Work.FTS.StrongPersist.StarPkg6 α (C * Cs) Φs := by
  obtain ⟨C, hC, h⟩ := Work.FTS.StrongPersist.StarPkg6OfCore
  exact ⟨C, hC, fun α Cs Φs hα hα5 hCs hcore => h α Cs Φs hα (hα5.trans (by norm_num)) hCs hcore⟩

/-! ## The two halves, ball- and bound-carrying -/

/-- The `ℋ⁶`-half, **ball-carrying** (the ball along the flow is an input; time-localised by the
`∀ T' ≤ T`). Conclusion in the continuous raw energy. -/
def AprioriPSixthB (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (C₀ E₁ : ℝ) : Prop :=
  ∀ T' : ℝ, 0 < T' → T' ≤ T → ∀ g : Fam, IsEpsSolP α ρ ε T' Φs E g₀ g → EpsRegP α ρ ε T' g →
    (∀ τ ∈ Icc 0 T', Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2) →
    ∀ τ ∈ Icc 0 T', rawE6 α g τ ≤ E₁

/-- The small-ball half, **`ℋ⁶`-bound-carrying** (the barrier's `ε`-perturbation is priced by the
raw `ℋ⁶` bound `M`; weaker than `AprioriPFourth`, so `AprioriPFourth ⟹` it). -/
def AprioriPFourthB (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε T : ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn)
    (C₀ M : ℝ) : Prop :=
  Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε g₀)) ≤ C₀ * α ^ 2 →
    ∀ T' : ℝ, 0 < T' → T' ≤ T → ∀ g : Fam, IsEpsSolP α ρ ε T' Φs E g₀ g →
      EpsRegP α ρ ε T' g → (∀ τ ∈ Icc 0 T', Xn6 α (slice g τ) ≤ M) →
      ∀ τ ∈ Icc 0 T', Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2

/-- `AprioriPFourth ⟹ AprioriPFourthB` (PROVED). -/
theorem AprioriPFourth.toB {α ε T C₀ M : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    (h : AprioriPFourth α ρ ε T Φs E g₀ C₀) : AprioriPFourthB α ρ ε T Φs E g₀ C₀ M :=
  fun h0 T' hT' hle g hsol hreg _ => h h0 T' hT' hle g hsol hreg

/-! ## The corrected chapter and its halves -/

/-- **A-priori chapter, corrected (v4)**: `AprioriChapter3` plus the order-six star package.
(The kernel symmetry enters through the leaf's hypothesis `hρs`.) -/
def AprioriChapter4 (Ce Cs C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ α' ∈ Ioc 0 α, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    E4Data α' C₀ K Ce Cs ρ Φs E g₀ → Work.FTS.StrongPersist.StarPkg6 α' Cs Φs →
    ∀ T : ℝ, 0 < T → ∃ M : ℝ, K ≤ M ∧ ∃ ε₂ : ℝ, 0 < ε₂ ∧ ε₂ ≤ 1 ∧
      ∀ ε ∈ Ioc 0 ε₂, AprioriP α' ρ ε T Φs E g₀ C₀ M

/-- The level-four chapter, `ℋ⁶`-bound-carrying: `ε₂` may depend on `T` and on the `ℋ⁶` bound. -/
def FourthChapterB (Ce Cs C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ α' ∈ Ioc 0 α, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    E4Data α' C₀ K Ce Cs ρ Φs E g₀ →
    ∀ T M : ℝ, 0 < T → ∃ ε₄ : ℝ, 0 < ε₄ ∧ ε₄ ≤ 1 ∧
      ∀ ε ∈ Ioc 0 ε₄, AprioriPFourthB α' ρ ε T Φs E g₀ C₀ M

/-- The level-six chapter, ball-carrying: `E₁(T)` before `ε₆(T)`. -/
def SixthChapterB (Ce Cs C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ α' ∈ Ioc 0 α, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    E4Data α' C₀ K Ce Cs ρ Φs E g₀ → Work.FTS.StrongPersist.StarPkg6 α' Cs Φs →
    ∀ T : ℝ, 0 < T → ∃ E₁ : ℝ, 0 ≤ E₁ ∧ K ^ 2 ≤ E₁ ∧ ∃ ε₆ : ℝ, 0 < ε₆ ∧ ε₆ ≤ 1 ∧
      ∀ ε ∈ Ioc 0 ε₆, AprioriPSixthB α' ρ ε T Φs E g₀ C₀ E₁

/-- `EpsE4R` with two added hypotheses: kernel symmetry (carried by the theorem) and the
order-six star package.  This is the statement body of the restated `StrongEps.EpsE4R`. -/
def EpsE4R4Stmt (Ce Cs : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C₀ : ℝ, Cstar ≤ C₀ → ∃ α₄ : ℝ, 0 < α₄ ∧
    ∀ α ∈ Set.Ioc 0 α₄, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}, 0 ≤ K →
    (∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) →
    (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    MuLamOK α C₀ Φs E →
    (∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀) →
    Work.FTS.Nonlin.Xn α g₀ ≤ α ^ 2 →
    Work.FTS.StrongGlobal.Xn6 α g₀ ≤ K * α ^ 2 →
    EpsUniformMem α ρ Φs E g₀ C₀ K

end Work.FTS.StrongEps.EpsE4Thr.E4R4
