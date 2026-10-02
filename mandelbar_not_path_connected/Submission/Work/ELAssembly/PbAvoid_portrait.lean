import Mathlib
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELAssembly.Instantiate
import Submission.Work.ELAssembly.coLand_Q
import Submission.Work.ELAssembly.rayPt_eq_of_eqOn_compl
import Submission.Work.ELPull.portrait_step
import Submission.Work.ELPull.portrait_five
import Submission.Work.ELPull.landsN_image
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Set Filter
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ}

/-- **The portrait of the first five levels, for the canonical `ELPull` datum of `d`.**

This is `Work.ELPull.portrait_five` with the root-parabolic bundle replaced by the single
point `z₁`, the periodicity `d.per_half` (`(Tantibar c)^[5] z₁ = z₁`) and the canonical
`ELPull.DynB c` datum `hNcanOf d`.  Its input `hzero` is the two-ray portrait at `z₁` in the
`Work.EL` flavour, transported to `hNcanOf d` by `Work.PortraitCount.landsN_elDynB`; the image
rule `himg` of `portrait_five` is `Work.ELPull.landsN_image (hNcanOf d) (hφcanOf d)`, and the
orbit-portrait count `hcount` is taken as given.  The known landings
`T^[j] αᵢ ↦ (Tantibar c)^[j] z₁` are built inside, by induction on `j`, from `hzero` and
`himg`. -/
theorem portraitFive_can (d : Work.EL.RootParabolic c)
    (hzero : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.EL.LandsN d.hN θ d.z₁ ↔ θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2))
    (hcount : Work.ELPull.PortraitCount (hNcanOf d)) :
    ∀ j : ℕ, j < 5 → ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.ELPull.LandsN (hNcanOf d) θ ((Tantibar c)^[j] d.z₁) ↔
        θ = Work.ELPull.T^[j] Work.ELPull.alpha1 ∨
          θ = Work.ELPull.T^[j] Work.ELPull.alpha2) := by
  -- the two ray-landing relations agree (`Work.PortraitCount.landsN_elDynB`)
  have hcan : ∀ (θ : ℝ) (y : ℂ),
      Work.ELPull.LandsN (hNcanOf d) θ y ↔ Work.EL.LandsN d.hN θ y :=
    fun θ y => Work.PortraitCount.landsN_elDynB d θ y
  -- the portrait at `z₁`, in the `ELPull` flavour
  have hzero' : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.ELPull.LandsN (hNcanOf d) θ d.z₁ ↔
        θ = Work.ELPull.alpha1 ∨ θ = Work.ELPull.alpha2) := by
    intro θ hθ
    rw [hcan θ d.z₁]
    simpa only [Work.ELPull.alpha1, Work.EL.alpha1, Work.ELPull.alpha2, Work.EL.alpha2]
      using hzero θ hθ
  -- the image rule (the Böttcher functional equation for the canonical coordinate)
  have himg : ∀ {θ' : ℝ} {y : ℂ}, Work.ELPull.LandsN (hNcanOf d) θ' y →
      Work.ELPull.LandsN (hNcanOf d) (Work.ELPull.T θ') (Tantibar c y) :=
    fun h => Work.ELPull.landsN_image (hNcanOf d) (hφcanOf d) h
  -- the arithmetic of the two root angles
  obtain ⟨harith, hT5a, hT5b⟩ := Work.ELPull.alpha_iter_arith
  -- the iterated image rule: `T^[j] αᵢ` lands at the `j`-th iterate of `z₁`
  have hLand : ∀ j : ℕ,
      Work.ELPull.LandsN (hNcanOf d) (Work.ELPull.T^[j] Work.ELPull.alpha1)
          ((Tantibar c)^[j] d.z₁) ∧
      Work.ELPull.LandsN (hNcanOf d) (Work.ELPull.T^[j] Work.ELPull.alpha2)
          ((Tantibar c)^[j] d.z₁) := by
    intro j
    induction j with
    | zero =>
        exact ⟨(hzero' Work.ELPull.alpha1 (harith 0 (by norm_num)).1).mpr (Or.inl rfl),
               (hzero' Work.ELPull.alpha2 (harith 0 (by norm_num)).2.1).mpr (Or.inr rfl)⟩
    | succ k ih =>
        refine ⟨?_, ?_⟩
        · rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
          exact himg ih.1
        · rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
          exact himg ih.2
  -- the portrait at `(Tantibar c)^[5] z₁ = z₁`, with the angles of level `5`
  have hP5 : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.ELPull.LandsN (hNcanOf d) θ ((Tantibar c)^[5] d.z₁) ↔
        θ = Work.ELPull.T^[5] Work.ELPull.alpha1 ∨
          θ = Work.ELPull.T^[5] Work.ELPull.alpha2) := by
    intro θ hθ
    have h := hzero' θ hθ
    rw [d.per_half, hT5a, hT5b]
    constructor
    · intro hl
      rcases h.mp hl with h1 | h1
      · exact Or.inr h1
      · exact Or.inl h1
    · rintro (h1 | h1)
      · exact h.mpr (Or.inr h1)
      · exact h.mpr (Or.inl h1)
  -- one step of the descent, from the `(j+1)`-st level to the `j`-th
  have hstep : ∀ j : ℕ, j ≤ 4 →
      (∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
        (Work.ELPull.LandsN (hNcanOf d) θ ((Tantibar c)^[j+1] d.z₁) ↔
          θ = Work.ELPull.T^[j+1] Work.ELPull.alpha1 ∨
            θ = Work.ELPull.T^[j+1] Work.ELPull.alpha2)) →
      (∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
        (Work.ELPull.LandsN (hNcanOf d) θ ((Tantibar c)^[j] d.z₁) ↔
          θ = Work.ELPull.T^[j] Work.ELPull.alpha1 ∨
            θ = Work.ELPull.T^[j] Work.ELPull.alpha2)) := by
    intro j hj hnext
    have hAj := harith j (by omega)
    have hAj1 := harith (j+1) (by omega)
    have hL := hLand j
    refine Work.ELPull.portrait_step (hN := hNcanOf d)
      (u := Work.ELPull.T^[j+1] Work.ELPull.alpha1)
      (v := Work.ELPull.T^[j+1] Work.ELPull.alpha2)
      (u' := Work.ELPull.T^[j] Work.ELPull.alpha1)
      (v' := Work.ELPull.T^[j] Work.ELPull.alpha2)
      himg hcount ?_ hAj1.1 hAj1.2.1 hAj1.2.2 hnext hAj.1 hAj.2.1 ?_ ?_ hL.1 hL.2
    · rw [Function.iterate_succ_apply']
    · rw [Function.iterate_succ_apply']
    · rw [Function.iterate_succ_apply']
  -- the five levels, by four descents `z₁ → z₄ → z₃ → z₂ → z₁`
  intro j hj θ hθ
  have hP4 := hstep 4 (by norm_num) hP5
  have hP3 := hstep 3 (by norm_num) hP4
  have hP2 := hstep 2 (by norm_num) hP3
  have hP1 := hstep 1 (by norm_num) hP2
  interval_cases j
  · exact hzero' θ hθ
  · exact hP1 θ hθ
  · exact hP2 θ hθ
  · exact hP3 θ hθ
  · exact hP4 θ hθ

-- Shell: `namespace Work.ELAssembly` (area `Submission/Work/ELAssembly/`).
/-- **(PJ) the two-ray portrait at every point of the parabolic cycle**
(`NOTES_LEAD_mandelbar_pbavoid.md` §3.2).  From the portrait at `z₁` (`hzero`), the orbit-portrait
count (`hcount`, available as `Work.ELAssembly.portraitCount_of_crit d fl`) and the cycle landings
(`hlands`, the `(C1)` half of `PbAvoid_cycle`), the only rays of angles in `Ico 0 1` landing at
`(Tantibar c)^[j] z₁`, `j < 5`, are the two portrait rays `T^[j] α₁`, `T^[j] α₂`.  The proof is
`Work.ELPull.portrait_five`'s four descents `z₁ → z₄ → z₃ → z₂ → z₁`
(`Work.ELPull.portrait_step`) carried out for the canonical data `Work.ELAssembly.hNcanOf d`
transported to `Work.EL.LandsN d.hN` (as in `coLand_Q`, via `Work.ELAssembly.hψOf` and
`Work.ELAssembly.rayPt_eq_of_eqOn_compl` — add that import), using `Work.ELPull.landsN_image`,
`Work.ELPull.T = Work.EL.T`, `d.per_half` (`T^5 z₁ = z₁`) and `T^[j] αᵢ ∈ Ico 0 1`. -/
theorem PbAvoid_portrait {c : ℂ} (d : Work.EL.RootParabolic c)
    (hzero : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.EL.LandsN d.hN θ d.z₁ ↔ θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2))
    (hcount : Work.ELPull.PortraitCount (hNcanOf d))
    (hlands : ∀ j : ℕ, Work.EL.LandsN d.hN (Work.EL.T^[j] Work.EL.alpha1)
        ((LeanEval.ComplexAnalysis.Tantibar c)^[j] d.z₁) ∧
      Work.EL.LandsN d.hN (Work.EL.T^[j] Work.EL.alpha2)
        ((LeanEval.ComplexAnalysis.Tantibar c)^[j] d.z₁))
    (j : ℕ) (hj : j < 5) :
    ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.EL.LandsN d.hN θ ((LeanEval.ComplexAnalysis.Tantibar c)^[j] d.z₁) ↔
        θ = Work.EL.T^[j] Work.EL.alpha1 ∨ θ = Work.EL.T^[j] Work.EL.alpha2) := by
  intro θ hθ
  -- the vocabulary bridge: `hzero` and `portraitFive_can` are transported across it
  have hcan : ∀ (θ : ℝ) (y : ℂ),
      Work.ELPull.LandsN (hNcanOf d) θ y ↔ Work.EL.LandsN d.hN θ y :=
    fun θ y => Work.PortraitCount.landsN_elDynB d θ y
  exact ((hcan θ ((LeanEval.ComplexAnalysis.Tantibar c)^[j] d.z₁)).symm).trans
    (portraitFive_can d hzero hcount j hj θ hθ)

end Work.ELAssembly
