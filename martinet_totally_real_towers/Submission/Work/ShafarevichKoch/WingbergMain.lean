import Mathlib
import Submission.Work.ShafarevichKoch.CountZ
import Submission.Work.ShafarevichKoch.KcArithmetic
import Submission.Work.ShafarevichKoch.card_twoMulH2_le_of_wingbergDuality
import Submission.Work.ShafarevichKoch.card_twoTorsionH3_le_of_wingbergDuality
import Submission.Work.ShafarevichKoch.KcCohomology
import Submission.Work.ShafarevichKoch.Kc
import Submission.Work.ShafarevichKoch.KcRealization
import Submission.Work.ShafarevichKoch.KcKochInjection
import Submission.Work.ShafarevichKoch.kochInjection_of_contH2DimLe

/-!
# `Work.ShafarevichKoch.WingbergMain` -- the relation count from Wingberg's duality

This module assembles the reduction of the chapter's crux to the single named classical input
`Work.ShafarevichKoch.WingbergDuality` (Wingberg's duality, Neukirch--Schmidt--Wingberg Ch. VIII
§8 Theorem 8.8.1, together with NSW Ch. VIII §8 Lemma 8.8.4):

* `natCard_H2_zmodTwo_eq` (`CountZ.lean`) : the `ℤ`-power sequence gives
  `#H²(G_∅,ℤ/2) = #(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) · #(H³(G_∅,ℤ)[2])`;
* `card_twoMulH2_le_of_wingbergDuality` : the first factor is at most `2^5` (Wingberg's duality
  `i = 1` + NSW Lemma 8.8.4 + `rank₂ Cl(Kc) = 5`);
* `card_twoTorsionH3_le_of_wingbergDuality` : the second factor is at most `2` (Wingberg's duality
  `i = 0` + `(𝓞 Kc)ˣ = {±1}`);

hence `#H²(G_∅,𝔽₂) ≤ 2^6`, i.e. `Work.RelatorRank.ContH2DimLe (G_∅) 6`, and from there the
chapter's crux `KcProTwoPresentationInput`, the walls, and (with the realization clause) the
caller's `ProTwoShafarevichKochInput Kc`.

## Main declarations

* `Work.ShafarevichKoch.finite_H2_zmodTwo_of_wingbergDuality`,
  `Work.ShafarevichKoch.natCard_contH2_le_six_of_wingbergDuality`,
  `Work.ShafarevichKoch.contH2DimLe_six_of_wingbergDuality`;
* `Work.ShafarevichKoch.kcProTwoPresentationInput_of_wingbergDuality`,
  `Work.ShafarevichKoch.infiniteProTwoExtension_Kc_of_wingbergDuality`,
  `Work.ShafarevichKoch.unramifiedPro2TowerWall_of_wingbergDuality`,
  `Work.ShafarevichKoch.boundedRdTowerWall_of_wingbergDuality`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

open scoped Classical
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower
open Work.ConCohomology

section Main

variable (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2)

local instance instTwoActionMain :
    DistribMulAction (Work.ClassFieldTower.galoisGroup M) (ZMod 2) :=
  Work.RelatorRank.f2TrivialAction _
local instance instTwoDiscreteMain :
    IsDiscreteGModule (Work.ClassFieldTower.galoisGroup M) (ZMod 2) :=
  Work.RelatorRank.f2Discrete _

/-- **`H²(G_∅,𝔽₂)` is finite**, from Wingberg's duality: its kernel under the connecting map of
the `ℤ`-power sequence is a quotient of the finite `H²(G_∅,ℤ)` and its range lies in the finite
`H³(G_∅,ℤ)`. -/
theorem finite_H2_zmodTwo_of_wingbergDuality (h : WingbergDuality M) :
    Finite (H2 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) := by
  haveI hfin : Finite (H2 (Work.ClassFieldTower.galoisGroup M) ℤ) := h.1
  haveI hfin3 : Finite (H3 (Work.ClassFieldTower.galoisGroup M) ℤ) := h.2.1
  have hcard := natCard_H2_zmodTwo_eq (G := Work.ClassFieldTower.galoisGroup M)
  have hne1 : Nat.card (H2 (Work.ClassFieldTower.galoisGroup M) ℤ ⧸
      twoMulH2 (Work.ClassFieldTower.galoisGroup M)) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  haveI : Finite (twoTorsionH3 (Work.ClassFieldTower.galoisGroup M)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hne2 : Nat.card (twoTorsionH3 (Work.ClassFieldTower.galoisGroup M)) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨0, by simp⟩, inferInstance⟩
  exact Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.mul_ne_zero hne1 hne2)

/-- **The relation count `#H²(G_∅,𝔽₂) ≤ 2^6` from Wingberg's duality.** -/
theorem natCard_contH2_le_six_of_wingbergDuality (h : WingbergDuality M) :
    Nat.card (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) ≤ 2 ^ 6 := by
  have hA := card_twoMulH2_le_of_wingbergDuality M h
  have hB := card_twoTorsionH3_le_of_wingbergDuality M h
  have hmain := natCard_H2_zmodTwo_le (G := Work.ClassFieldTower.galoisGroup M) hA hB
  show Nat.card (H2 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) ≤ 2 ^ 6
  exact hmain

/-- **`dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ 6` from Wingberg's duality.** -/
theorem contH2DimLe_six_of_wingbergDuality (h : WingbergDuality M) :
    Work.RelatorRank.ContH2DimLe (Work.ClassFieldTower.galoisGroup M) 6 := by
  have hcard := natCard_contH2_le_six_of_wingbergDuality M h
  haveI : Finite (H2 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) :=
    finite_H2_zmodTwo_of_wingbergDuality M h
  have hexp : ∀ x : Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M),
      (2 : ℕ) • x = 0 := by
    intro x
    letI := Work.RelatorRank.f2TrivialAction (Work.ClassFieldTower.galoisGroup M)
    letI : Work.ConCohomology.IsDiscreteGModule
        (Work.ClassFieldTower.galoisGroup M) (ZMod 2) :=
      Work.RelatorRank.f2Discrete (Work.ClassFieldTower.galoisGroup M)
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective
      (Work.ConCohomology.B2' (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) x
    rw [← map_nsmul]
    rw [show (2 : ℕ) • z = 0 from by
          refine Subtype.ext ?_
          ext p
          show (2 : ℕ) • (z.1 p) = 0
          exact CharTwo.two_nsmul _,
      map_zero]
  letI : Module (ZMod 2) (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) :=
    AddCommGroup.zmodModule (n := 2) hexp
  haveI : Module.Finite (ZMod 2)
      (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) := Module.Finite.of_finite
  have hcardfin : Nat.card (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) =
      2 ^ Module.finrank (ZMod 2)
        (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  refine ⟨Module.finrank (ZMod 2)
    (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)), ?_, hcardfin⟩
  have : 2 ^ Module.finrank (ZMod 2)
      (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) ≤ 2 ^ 6 := by
    rw [← hcardfin]
    exact hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

/-- **The new input implies the chapter's earlier named form.**  `WingbergDuality` determines
`dim H²(G_∅,𝔽₂) ≤ 6`, and the counting route of `KochInjectionEquiv`/`KochInjection` (proved in
sessions 10--11) turns that into the classical Koch injection
`H²(G_∅,𝔽₂) ↪ (V_∅/Kc^{×2})^∨`. -/
theorem kochInjection_of_wingbergDuality (h : WingbergDuality M) :
    KochInjection M :=
  kochInjection_of_contH2DimLe M (contH2DimLe_six_of_wingbergDuality M h)

end Main


/-! ## The chapter's crux and the walls -/

/-- **The chapter's crux from Wingberg's duality** (and the shared group-theoretic input
`Work.RelatorRank.GaschutzCohomologicalValue`). -/
theorem kcProTwoPresentationInput_of_wingbergDuality
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2,
      WingbergDuality M) :
    KcProTwoPresentationInput := by
  obtain ⟨M, hM⟩ := h
  exact kcProTwoPresentationInput_of_contH2DimLe M (hdict M)
    (contH2DimLe_six_of_wingbergDuality M hM)

/-- **`Kc` has an infinite Hilbert `2`-class field tower**, from Wingberg's duality. -/
theorem infiniteProTwoExtension_Kc_of_wingbergDuality
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2,
      WingbergDuality M) :
    Work.ClassFieldTower.InfiniteProTwoExtension Work.ClassFieldTower.Kc :=
  infiniteProTwoExtension_Kc_of_input (kcProTwoPresentationInput_of_wingbergDuality hdict h)

/-- **The caller's wall `Submission.NumberField.UnramifiedPro2TowerWall`**, from Wingberg's
duality. -/
theorem unramifiedPro2TowerWall_of_wingbergDuality
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2,
      WingbergDuality M) :
    Submission.NumberField.UnramifiedPro2TowerWall :=
  unramifiedPro2TowerWall_of_input (kcProTwoPresentationInput_of_wingbergDuality hdict h)

/-- **The benchmark's wall `Submission.NumberField.BoundedRdTowerWall`**, from Wingberg's
duality. -/
theorem boundedRdTowerWall_of_wingbergDuality
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2,
      WingbergDuality M) :
    Submission.NumberField.BoundedRdTowerWall :=
  boundedRdTowerWall_of_input (kcProTwoPresentationInput_of_wingbergDuality hdict h)


/-- **Item (3) of the deliverable from Wingberg's duality**: the caller's sound interface
`Work.ClassFieldTower.ProTwoShafarevichKochInput Kc`, from Wingberg's duality, the shared
group-theoretic input and the realization clause `RealizationClauseKc`. -/
theorem proTwoShafarevichKochInput_Kc_of_wingbergDuality
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : ∃ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2,
      WingbergDuality M)
    (hreal : RealizationClauseKc) :
    Work.ClassFieldTower.ProTwoShafarevichKochInput Work.ClassFieldTower.Kc :=
  proTwoShafarevichKochInput_Kc_of_input_and_realization
    (kcProTwoPresentationInput_of_wingbergDuality hdict h) hreal

end Work.ShafarevichKoch
