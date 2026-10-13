import Mathlib
import Submission.Work.WilVP.Defs
import Submission.Work.WilVP.IsoBallSyntax
import Submission.Work.WilVP.isoSentRealize
import Submission.Work.WilVP.realIsoBallGood
import Submission.Work.WilC4.ULPMSyntax
import Submission.Work.WilC4.ULPMRealize
import Submission.Work.WilC4.realULPMGood
import Submission.Work.WilC2.Square

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilVP

open Work.WilC4
open Work.WilC2 (model_exists_sq real_exists_sq)

/-- **Transfer of iso-balls from `ℝ` to every model of `TR`.**  `Work.WilVP.IsoBallProp` is a
first-order schema: for a fixed parameter-free `LRc`-formula `φ` (defining the family `Y`) one
exhibits `N` and a parameter-free formula `ψ` (defining `P`) such that the statement of
`IsoBallProp` (with the functionality and bounded-fibre hypotheses as an implication) becomes a
single `LRc`-**sentence** — clone the construction of `Work.WilC4.ULPMSyntax` /
`Work.WilC4.ULPMRealize` (`ulpmSent`, `ULPMGood`, `ulpmSent_realize`, and the helper lemmas
`leTerm`, `ltNMul`, `approxAtom`, `graphPart`, `ucard`) with the body of `IsoBallProp` (the
cardinality clause is the same; the new atoms are `y₀ ≠ 0`, `(N|y−x|)² < (x−b)²`,
`y₁² ≤ (N y₀)²`, `(N y₀)² ≤ y₁²`, and the bounded-fibre hypothesis
`∃R, ∀x y, φ(x,y,c) → x² ≤ R²`).  Extract `N, ψ` on the `ℝ`-side from the hypothesis
`h : IsoBallProp ℝ` applied to `{v | φ.Realize v}` (analogue of `Work.WilC4.realULPMGood`), then
transfer the sentence with
`FirstOrder.Language.Theory.Model.realize_iff_of_model_completeTheory` (using
`M ⊨ LRc.completeTheory ℝ`, which is `hM`; see `Work.WilC4/transferOfULPM.lean` for the exact
5-line pattern).  Do NOT import `Submission.Work.WilC5.stdPart` or
`Submission.Work.WilC5.LRcReduct` (review fix F1: they bring the `lrcConstReduct` instance that
makes later `ℝ`-side statements fail to elaborate). -/
theorem transferOfIsoBall (h : Work.WilVP.IsoBallProp ℝ) :
    ∀ (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M]
      [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
      [(FirstOrder.Language.constantsOn ℝ).Structure M],
      FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR → Work.WilVP.IsoBallProp M := by
  intro M _ _ _ _ _ _ hM k Y hYd hgraph hbnd
  -- `Y` is the set defined by a parameter-free formula `φ`
  obtain ⟨φ, hYeq⟩ := Set.empty_definable_iff.mp hYd
  -- the `ℝ`-side data: `N`, `ψ` and the syntactic content `IsoBallGood`
  obtain ⟨N, ψ, hN, hgoodℝ⟩ := realIsoBallGood h φ
  have hsqM : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z := model_exists_sq hM
  have hsqℝ : ∀ x : ℝ, 0 ≤ x → ∃ z : ℝ, x = z * z := real_exists_sq
  haveI : M ⊨ LRc.completeTheory ℝ := hM
  -- the sentence holds over `ℝ` and hence, by completeness of `TR`, in `M`
  have hSentℝ : ℝ ⊨ isoSent k N φ ψ := (isoSentRealize hsqℝ k N φ ψ).mpr hgoodℝ
  have hSentM : M ⊨ isoSent k N φ ψ :=
    (realize_iff_of_model_completeTheory (L := LRc) (M := ℝ) (N := M)
      (isoSent k N φ ψ)).mpr hSentℝ
  have hgoodM : IsoBallGood k N φ ψ M := (isoSentRealize hsqM k N φ ψ).mp hSentM
  -- the two hypotheses of `IsoBallGood` in `M`, transported along `Y = {v | φ.Realize v}`
  have hgraphM : ∀ (c : Fin k → M) (x y y' : M), uphiVal k φ M c x y →
      uphiVal k φ M c x y' → y = y' := by
    intro c x y y' h1 h2
    refine hgraph c x y y' ?_ ?_
    · rw [hYeq]; exact (uphiVal_eq k φ c x y).mp h1
    · rw [hYeq]; exact (uphiVal_eq k φ c x y').mp h2
  have hbndM : ∀ c : Fin k → M, ∃ R : M, ∀ x y : M, uphiVal k φ M c x y → |x| ≤ R := by
    intro c
    obtain ⟨R, hR⟩ := hbnd c
    exact ⟨R, fun x y hxy => hR x y (by rw [hYeq]; exact (uphiVal_eq k φ c x y).mp hxy)⟩
  -- the conclusion, with `P` defined by `ψ`
  refine ⟨N, hN, {z : Fin (k + 1) → M | ψ.Realize z}, ?_, ?_⟩
  · exact Set.empty_definable_iff.mpr ⟨ψ, rfl⟩
  · intro c
    obtain ⟨hcard, hiso⟩ := hgoodM hgraphM hbndM c
    refine ⟨?_, ?_⟩
    · have hset : {x : M | Fin.cons x c ∈ ({z : Fin (k + 1) → M | ψ.Realize z} :
          Set (Fin (k + 1) → M))} = {x : M | upsiVal k ψ M c x} := by
        ext x
        exact (upsiVal_eq k ψ c x).symm
      rw [hset]
      exact hcard
    · intro x y₀ y hy₀ hne hball
      have hy₀' : uphiVal k φ M c x y₀ :=
        (uphiVal_eq k φ c x y₀).mp (by rw [hYeq] at hy₀; exact hy₀)
      have hball' : ∀ p : M, upsiVal k ψ M c p → (N : M) * |y - x| < |x - p| := by
        intro p hp
        exact hball p ((upsiVal_eq k ψ c p).mp hp)
      obtain ⟨y₁, hwit, h1, h2⟩ := hiso x y₀ y hy₀' hne hball'
      exact ⟨y₁, by rw [hYeq]; exact (uphiVal_eq k φ c y y₁).mp hwit, h1, h2⟩

end Work.WilVP
