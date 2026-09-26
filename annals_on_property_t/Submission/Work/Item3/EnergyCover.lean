import Submission.Work.Item3.EnergyStepGeneralMinus
import Submission.Work.Item3.EnergyInvert

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# EnergyCover: the complete four-way cut-slide case analysis at a balanced factor

At a balanced factor (`coordWord α p = A ++ B` or `invRev B ++ invRev A`,
`|A| = |B|`) in a residual state, with the left neighbour `v` and right
neighbour `u` covering the two halves
(`coordWord α v = X ++ invRev A` or `A ++ invRev X`;
 `coordWord α u = invRev B ++ Z` or `invRev Z ++ B`), there are exactly eight
sign combinations and the available `N`-preserving energy moves are:

| sign of | move | energy condition |
|---|---|---|
| `v` plus | `rho` / `rhoNeg v p` | `E B < E (invRev A)` |
| `v` minus | `lam` / `lamNeg v p` | `E (invRev B) < E A` |
| `u` plus | `lam` / `lamNeg u p` | `E A < E (invRev B)` |
| `u` minus | `rho` / `rhoNeg u p` | `E (invRev A) < E B` |

(the exact transvection depending on the balanced row's own sign).  The four
"general" cut-slide lemmas of `EnergyStepGeneral`/`EnergyStepGeneralMinus`
prove each row of the table.  This module collects them into the two uniform
statements used by the assembly:

* `energy_general_cover4` — the four classical cut-slides, with the
  disjunction of the four energy conditions as hypothesis;
* `energy_general_cover5` — the same together with the two *inversion*
  fallbacks of `Item3/EnergyInvert.lean` (invert the balanced coordinate when
  both classical comparisons fail in the appropriate direction).

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- **Plus-orientation left-neighbour energy step (sign-parametrized).** -/
theorem energy_general_Lplus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p v : Fin n} (hvp : v ≠ p)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length) (s : Bool)
    (hE : wordEnergy (ebase n) (lweight) B <
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev A))
    (hp : coordWord α p = if s then A ++ B else FreeGroup.invRev B ++ FreeGroup.invRev A)
    (hv : coordWord α v = X ++ FreeGroup.invRev A) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) ≤ N α ∧ eEnergy (α * γ) < eEnergy α := by
  cases s
  · simp only [Bool.false_eq_true, if_false] at hp
    rcases energy_step_general_rhoNeg_bal α hres hvp A B X hAB hE hp hv with ⟨hEn, hN⟩
    exact ⟨rhoNeg v p hvp, Subgroup.subset_closure (rhoNeg_mem_AutGen n hvp), le_of_eq hN, hEn⟩
  · simp only [if_true] at hp
    rcases energy_step_general_rho α hres hvp A B X hAB hE hp hv with ⟨hEn, hN⟩
    exact ⟨rho v p hvp, Subgroup.subset_closure (rho_mem_AutGen n hvp), le_of_eq hN, hEn⟩

/-- **Plus-orientation right-neighbour energy step (sign-parametrized).** -/
theorem energy_general_Rplus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p u : Fin n} (hup : u ≠ p)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length) (s : Bool)
    (hE : wordEnergy (ebase n) (lweight) A <
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev B))
    (hp : coordWord α p = if s then A ++ B else FreeGroup.invRev B ++ FreeGroup.invRev A)
    (hu : coordWord α u = FreeGroup.invRev B ++ Z) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) ≤ N α ∧ eEnergy (α * γ) < eEnergy α := by
  cases s
  · simp only [Bool.false_eq_true, if_false] at hp
    rcases energy_step_general_lamNeg_bal α hres hup A B Z hAB hE hp hu with ⟨hEn, hN⟩
    exact ⟨lamNeg u p hup,
      (AutClosure n).inv_mem (Subgroup.subset_closure (lam_mem_AutGen n hup)), le_of_eq hN, hEn⟩
  · simp only [if_true] at hp
    rcases energy_step_general_lam α hres hup A B Z hAB hE hp hu with ⟨hEn, hN⟩
    exact ⟨lam u p hup, Subgroup.subset_closure (lam_mem_AutGen n hup), le_of_eq hN, hEn⟩

/-- **The four classical cut-slides at a balanced factor.** -/
theorem energy_general_cover4 {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p v u : Fin n} (hvp : v ≠ p) (hup : u ≠ p)
    (A B X Z : List (Fin n × Bool)) (hAB : A.length = B.length) (sp sv su : Bool)
    (hp : coordWord α p = if sp then A ++ B else FreeGroup.invRev B ++ FreeGroup.invRev A)
    (hv : coordWord α v = if sv then X ++ FreeGroup.invRev A else A ++ FreeGroup.invRev X)
    (hu : coordWord α u = if su then FreeGroup.invRev B ++ Z else FreeGroup.invRev Z ++ B)
    (h : (sv = true ∧ wordEnergy (ebase n) (lweight) B <
            wordEnergy (ebase n) (lweight) (FreeGroup.invRev A)) ∨
         (sv = false ∧ wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) <
            wordEnergy (ebase n) (lweight) A) ∨
         (su = true ∧ wordEnergy (ebase n) (lweight) A <
            wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)) ∨
         (su = false ∧ wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) <
            wordEnergy (ebase n) (lweight) B)) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) ≤ N α ∧ eEnergy (α * γ) < eEnergy α := by
  rcases h with ⟨hsv, hE⟩ | ⟨hsv, hE⟩ | ⟨hsu, hE⟩ | ⟨hsu, hE⟩
  · have hv' : coordWord α v = X ++ FreeGroup.invRev A := by simpa [hsv] using hv
    exact energy_general_Lplus α hres hvp A B X hAB sp hE hp hv'
  · have hv' : coordWord α v = A ++ FreeGroup.invRev X := by simpa [hsv] using hv
    exact energy_general_Lminus α hres hvp A B X hAB sp hE hp hv'
  · have hu' : coordWord α u = FreeGroup.invRev B ++ Z := by simpa [hsu] using hu
    exact energy_general_Rplus α hres hup A B Z hAB sp hE hp hu'
  · have hu' : coordWord α u = FreeGroup.invRev Z ++ B := by simpa [hsu] using hu
    exact energy_general_Rminus α hres hup A B Z hAB sp hE hp hu' 

/-- **The four classical cut-slides together with the two inversion
fallbacks.** -/
theorem energy_general_cover5 {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p v u : Fin n} (hvp : v ≠ p) (hup : u ≠ p)
    (A B X Z : List (Fin n × Bool)) (hAB : A.length = B.length) (sp sv su : Bool)
    (hp : coordWord α p = if sp then A ++ B else FreeGroup.invRev B ++ FreeGroup.invRev A)
    (hv : coordWord α v = if sv then X ++ FreeGroup.invRev A else A ++ FreeGroup.invRev X)
    (hu : coordWord α u = if su then FreeGroup.invRev B ++ Z else FreeGroup.invRev Z ++ B)
    (h : (sv = true ∧ wordEnergy (ebase n) (lweight) B <
            wordEnergy (ebase n) (lweight) (FreeGroup.invRev A)) ∨
         (sv = false ∧ wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) <
            wordEnergy (ebase n) (lweight) A) ∨
         (su = true ∧ wordEnergy (ebase n) (lweight) A <
            wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)) ∨
         (su = false ∧ wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) <
            wordEnergy (ebase n) (lweight) B) ∨
         (sp = true ∧ wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) ≤
              wordEnergy (ebase n) (lweight) B ∧
            wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) ≤
              wordEnergy (ebase n) (lweight) A ∧
            (wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) <
                wordEnergy (ebase n) (lweight) B ∨
              wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) <
                wordEnergy (ebase n) (lweight) A)) ∨
         (sp = false ∧ wordEnergy (ebase n) (lweight) B ≤
              wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) ∧
            wordEnergy (ebase n) (lweight) A ≤
              wordEnergy (ebase n) (lweight) (FreeGroup.invRev B) ∧
            (wordEnergy (ebase n) (lweight) B <
                wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) ∨
              wordEnergy (ebase n) (lweight) A <
                wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)))) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) ≤ N α ∧ eEnergy (α * γ) < eEnergy α := by
  rcases h with ⟨hsv, hE⟩ | ⟨hsv, hE⟩ | ⟨hsu, hE⟩ | ⟨hsu, hE⟩
      | ⟨hsp, h1, h2, h3⟩ | ⟨hsp, h1, h2, h3⟩
  · have hv' : coordWord α v = X ++ FreeGroup.invRev A := by simpa [hsv] using hv
    exact energy_general_Lplus α hres hvp A B X hAB sp hE hp hv'
  · have hv' : coordWord α v = A ++ FreeGroup.invRev X := by simpa [hsv] using hv
    exact energy_general_Lminus α hres hvp A B X hAB sp hE hp hv'
  · have hu' : coordWord α u = FreeGroup.invRev B ++ Z := by simpa [hsu] using hu
    exact energy_general_Rplus α hres hup A B Z hAB sp hE hp hu'
  · have hu' : coordWord α u = FreeGroup.invRev Z ++ B := by simpa [hsu] using hu
    exact energy_general_Rminus α hres hup A B Z hAB sp hE hp hu'
  · have hp' : coordWord α p = A ++ B := by simpa [hsp] using hp
    rcases energy_invert_pos_strict α hAB hp' h1 h2 h3 with ⟨hγ, hN, hE⟩
    exact ⟨sigma p, hγ, le_of_eq hN, hE⟩
  · have hp' : coordWord α p = FreeGroup.invRev B ++ FreeGroup.invRev A := by
      simpa [hsp] using hp
    rcases energy_invert_neg_strict α hAB hp' h1 h2 h3 with ⟨hγ, hN, hE⟩
    exact ⟨sigma p, hγ, le_of_eq hN, hE⟩

end Submission.Nielsen
