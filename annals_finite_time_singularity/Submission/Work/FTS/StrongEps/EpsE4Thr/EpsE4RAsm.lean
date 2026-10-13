/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/EpsE4RAsm.lean` — the assembly of the **restated** `EpsE4Thr`

The lead's ruling (`cbc/fts_strongeps_c1c5_ruling*.md` §6, installed as `StrongEps/EpsE4R.lean`)
replaces the target's statement by

    ∀ {Ce Cs} {ρ}, IsSmoothKernel ρ → ∃ Cstar ≥ 1, ∀ C₀ ≥ Cstar, ∃ α₄ > 0,
      ∀ α ∈ (0, α₄], <datum and package hypotheses> → EpsUniformMem α ρ Φs E g₀ C₀ K,

i.e. the constant `C★` and the threshold `α₄` are now chosen **by the prover** (`C★` before `C₀`,
`α₄` after `C₀`).  This resolves the two statement-level blockers of the old form:

* **the `C₀ = 1` saturation** (`TauZero.certificate_datum_one_needs_monotone`): the datum clause is
  now the *absolute* `Xn α g₀ ≤ α²`, while the conclusion's ball is at `C₀ α²`; the fake-time-`0`
  obligation `∃ ε₁, ∀ ε ∈ (0,ε₁], Xn α (J_ε g₀) ≤ C₀ α²` needs only `1 < C₀`, which we get from
  `C★ ≥ 2` (`TauZero.Jeps_smallBall_one_lt`);
* **the level-four constant bookkeeping** (`√(Cup/clo)`): the same separation of the datum's
  `α²`-ball from the level `(C₀ α²)²` makes the barrier's start condition
  `IP4 α x₀ x₀ < clo (C₀α²)²` hold for `C₀` large (`C★` absorbs `√(Cup/clo)` and every other
  chapter threshold that depends on `C₀` but not on `α`);
* **the class-ball *room***: the local step may internally run the Picard engine at the class ball
  `2C₀`, since `MuLamOK α (2C₀)` follows from `hEll` + `hstar` for `α ≤ α₄`
  (`AprioriFourthLevel.MuLamOK_of_hEll_hstar`) — the threshold `α₄` is chosen after `C₀`.

This module performs the *assembly*: it turns the three analytic chapters of the route

* `LocalStepChapter`  — E2a for the projected scheme,
* `AprioriChapter`    — the level-four/level-six sub-horizon a-priori bound `AprioriP`,
* `DecayChapter`      — the `Maj` clause `AprioriDecayB`,

each holding for `α` below a `C₀`-dependent threshold, into the restated target, by taking
`Cstar := 2` and `α₄` the minimum of the three thresholds (and `1`).  The parameters
`K, Φs, E, g₀` are universally quantified *after* `α₄`, exactly as in the target; the chapters are
uniform in them.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.DecayMaj
import Submission.Work.FTS.StrongEps.EpsE4Thr.TauZero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The bundle of the target's inner hypotheses -/

/-- **The hypotheses of the restated target *after* `α₄`**: the datum's angular vanishing and
regularity, the two elliptic/star packages, the modulation clause, and the two datum bounds. -/
def E4Data (α C₀ K Ce Cs : ℝ) (ρ : ℝ × ℝ → ℝ) (Φs : Fn) (E : Fn → Fn) (g₀ : Fn) : Prop :=
  0 ≤ K ∧
  (∀ z : ℝ, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) ∧
  (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
    Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) ∧
  Work.FTS.VocabO2.StarPkgo2 α Cs Φs ∧
  MuLamOK α C₀ Φs E ∧
  (∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀) ∧
  Work.FTS.Nonlin.Xn α g₀ ≤ α ^ 2 ∧
  Xn6 α g₀ ≤ K * α ^ 2

/-! ## The three analytic chapters -/

/-- **The local-step chapter** (E2a): for every `C₀` there is a threshold `α ≤ 1` below which the
projected scheme has a regular solution on a small time interval for every datum of the class. -/
def LocalStepChapter (Ce Cs C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ α' ∈ Set.Ioc 0 α, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    E4Data α' C₀ K Ce Cs ρ Φs E g₀ → ∀ ε : ℝ, 0 < ε → LocalStepP α' ρ ε Φs E C₀

/-- **The a-priori chapter**: the two-clause sub-horizon bound `AprioriP` at the constant `M = K`
of the datum. -/
def AprioriChapter (Ce Cs C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ α' ∈ Set.Ioc 0 α, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    E4Data α' C₀ K Ce Cs ρ Φs E g₀ →
    ∀ ε : ℝ, 0 < ε → ∀ T : ℝ, 0 < T → AprioriP α' ρ ε T Φs E g₀ C₀ K

/-- **The decay (`Maj`) chapter**: the ball-carrying a-priori decay bound. -/
def DecayChapter (Ce Cs C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ α' ∈ Set.Ioc 0 α, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    E4Data α' C₀ K Ce Cs ρ Φs E g₀ →
    ∀ T : ℝ, 0 < T → ∃ Maj : ℝ → ℝ, AprioriDecayB α' ρ T Φs E g₀ C₀ Maj

/-! ## The assembly -/

/-- **The restated `EpsE4Thr`, from its three analytic chapters.** -/
theorem EpsE4Thr_of_chapters {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ)
    (hL : ∀ C₀ : ℝ, LocalStepChapter Ce Cs C₀ ρ)
    (hP : ∀ C₀ : ℝ, AprioriChapter Ce Cs C₀ ρ)
    (hD : ∀ C₀ : ℝ, DecayChapter Ce Cs C₀ ρ) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C₀ : ℝ, Cstar ≤ C₀ → ∃ α₄ : ℝ, 0 < α₄ ∧
      ∀ α ∈ Set.Ioc 0 α₄, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}, 0 ≤ K →
      (∀ z : ℝ, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) →
      (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → MuLamOK α C₀ Φs E →
      (∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀) →
      Work.FTS.Nonlin.Xn α g₀ ≤ α ^ 2 → Xn6 α g₀ ≤ K * α ^ 2 →
      EpsUniformMem α ρ Φs E g₀ C₀ K := by
  refine ⟨2, by norm_num, ?_⟩
  intro C₀ hC₀
  have hC₀' : 1 < C₀ := lt_of_lt_of_le (by norm_num) hC₀
  obtain ⟨αL, hαL0, hαL1, hL'⟩ := hL C₀
  obtain ⟨αP, hαP0, hαP1, hP'⟩ := hP C₀
  obtain ⟨αD, hαD0, hαD1, hD'⟩ := hD C₀
  refine ⟨min (min αL αP) (min αD 1), lt_min (lt_min hαL0 hαP0) (lt_min hαD0 one_pos), ?_⟩
  intro α hα
  have hα1 : α ≤ 1 := le_trans hα.2 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hαL : α ∈ Set.Ioc 0 αL :=
    ⟨hα.1, le_trans hα.2 (le_trans (min_le_left _ _) (min_le_left _ _))⟩
  have hαP : α ∈ Set.Ioc 0 αP :=
    ⟨hα.1, le_trans hα.2 (le_trans (min_le_left _ _) (min_le_right _ _))⟩
  have hαD : α ∈ Set.Ioc 0 αD :=
    ⟨hα.1, le_trans hα.2 (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  intro K Φs E g₀ hK hvan hEll hstar hml hd h4 h6
  have hdata : E4Data α C₀ K Ce Cs ρ Φs E g₀ :=
    ⟨hK, hvan, hEll, hstar, hml, hd, h4, h6⟩
  exact EpsUniformMem_of_localStep_aprioriB (α := α) (C₀ := C₀) (K := K) (M := K)
    (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀)
    hvan hρ hα.1 hα1 hK h6 le_rfl
    (Jeps_smallBall_one_lt hρ hα.1 hα1 hC₀' hd h4) hd
    (fun ε hε => hL' α hαL hdata ε hε)
    (fun ε hε T hT => hP' α hαP hdata ε hε T hT)
    (fun T hT => hD' α hαD hdata T hT)

end Work.FTS.StrongEps.EpsE4Thr
