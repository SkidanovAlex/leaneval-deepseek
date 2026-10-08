/-
Higman's Lemma 8, first reduction: `P` acts trivially on `C / A`.

If `C > A` is a minimal normal `ξ`-section and `⁅C,C⁆ = A`, then `⁅⊤,C⁆ = A`: the subgroup
`⁅⊤,C⁆` is normal, `ξ`-invariant and lies between `A` and `C`, so `hcover` makes it `A` or `C`;
the second case forces `C = 1` (a finite `2`-group has no proper subgroup equal to its commutator
with the whole group), contradicting `A ≠ ⊥`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.MSA.l8_local

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.MSA.L8

variable {P : Type} [Group P] [Finite P]

/-- A finite `2`-group has no normal subgroup `C` equal to its own commutator with the whole
group: `⁅⊤,C⁆ = C` forces `C = ⊥`. -/
theorem eq_bot_of_commutator_top_eq_self (hP : IsPGroup 2 P) {C : Subgroup P} [hCn : C.Normal]
    (h : ⁅(⊤ : Subgroup P), C⁆ = C) : C = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨n, hn⟩ := (Subgroup.nilpotent_iff_lowerCentralSeries).mp
    (inferInstance : Group.IsNilpotent P)
  have hle : ∀ k, C ≤ (⊤ : Subgroup P).lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih =>
        calc C = ⁅(⊤ : Subgroup P), C⁆ := h.symm
          _ ≤ ⁅(⊤ : Subgroup P), (⊤ : Subgroup P).lowerCentralSeries k⁆ :=
              Subgroup.commutator_mono le_rfl ih
          _ = ⁅(⊤ : Subgroup P).lowerCentralSeries k, ⊤⁆ := Subgroup.commutator_comm _ _
          _ = (⊤ : Subgroup P).lowerCentralSeries (k + 1) :=
              (Subgroup.lowerCentralSeries_succ ⊤ k).symm
  exact le_bot_iff.mp (hn ▸ hle n)

/-- **`P` acts trivially on `C / A`.**  In the situation of Higman's Lemma 8 with `A ≠ ⊥`,
`⁅⊤, C⁆ = A`. -/
theorem commutator_top_C_le (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : IsXiAbelNormal h A) (hCn : C.Normal)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : powSub C 2 ≤ A) (hCd : ⁅C, C⁆ = A) (hAne : A ≠ ⊥) :
    ⁅(⊤ : Subgroup P), C⁆ ≤ A := by
  have hDnorm : (⁅(⊤ : Subgroup P), C⁆ : Subgroup P).Normal := Subgroup.commutator_normal _ _
  have hDinv : (⁅(⊤ : Subgroup P), C⁆).map (h.xi : MulAut P).toMonoidHom = ⁅(⊤ : Subgroup P), C⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective,
      hCinv]
  have hAD : A ≤ ⁅(⊤ : Subgroup P), C⁆ := by
    rw [← hCd]
    exact Subgroup.commutator_mono le_top le_rfl
  have hDC : ⁅(⊤ : Subgroup P), C⁆ ≤ C := Subgroup.commutator_le_right _ _
  rcases hcover _ hDnorm hDinv hAD hDC with h1 | h1
  · exact le_of_eq h1
  · exfalso
    haveI : C.Normal := hCn
    have hCbot : C = ⊥ := eq_bot_of_commutator_top_eq_self h.isPGroup h1
    exact hAne (le_bot_iff.mp (hAC.trans (le_of_eq hCbot)))

/-- Any subgroup between `A` and `C` is normal in `P` (since `P` acts trivially on `C/A`). -/
theorem normal_of_le_of_contains {A C D : Subgroup P}
    (hPC : ⁅(⊤ : Subgroup P), C⁆ ≤ A) (hAD : A ≤ D) (hDC : D ≤ C) : D.Normal := by
  have h1 : ⁅(⊤ : Subgroup P), D⁆ ≤ D :=
    le_trans (Subgroup.commutator_mono le_rfl hDC) (le_trans hPC hAD)
  have h2 : (⊤ : Subgroup P) ≤ Subgroup.normalizer (D : Set P) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr h1
  exact Subgroup.normalizer_eq_top_iff.mp (le_antisymm le_top h2)

end Work.Higman.MSA.L8
