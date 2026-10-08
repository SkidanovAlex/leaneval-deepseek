import Mathlib
import Submission.Work.DSTR.D16Aux
import Submission.Work.DSTR.D16Basic
import Submission.Work.DSTR.D16.case1
import Submission.Work.DSTR.fittingSelfCentralizing
import Submission.Work.DSTR.M110.PiCoreFacts
import Submission.Work.ASM.oddCore_odd
import Submission.Work.CORE2A.thm26_aux
import Submission.Work.CORE2A.fstar_ne_bot

set_option linter.style.haveILetI false

namespace Work.DSTR.D16

open Subgroup

/-- If the centralizer of `F_{2'}(X)` is solvable and `O_2(X) = ⊥`, then `C_X(F_{2'}(X)) ≤ F_{2'}(X)`.

Mathematics.  `O_2(X) = ⊥` forces the Fitting subgroup `F(X)` to be of odd order: the `2`-part of
the nilpotent group `F(X)` is a normal `2`-subgroup of `X`, hence lies in `O_2(X) = ⊥`.  Therefore
`F_{2'}(X) = O_{2'}(F(X)) = F(X)` (the reverse inclusion `F_{2'}(X) ≤ F(X)` always holds), and the
statement becomes `C_X(F(X)) ≤ F(X)` under the sole hypothesis that `C_X(F(X))` is solvable.

Let `C = C_X(F(X))` and `K = F(C)` (viewed in `X`).  Since `F(C)` is characteristic in `C ⊴ X`,
`K` is normal in `X`, and it is nilpotent, so `K ≤ F(X)`.  Moreover every `c ∈ C` centralizes
`F(X) ⊇ K`, so `C` centralizes `K = F(C) ≥ C_C(F(C))`; Bender 1.2 (Fitting's theorem, valid for the
solvable group `C`) gives `C_C(F(C)) ≤ F(C)`, whence `c ∈ F(C)` and so `C ≤ K ≤ F(X)`. -/
theorem centralizer_le_fittingPi_of_solvable (X : Type) [Group X] [Finite X] (hA : Work.GW2.pCore 2 X = ⊥) (hsol : Group.IsSolvable ↥(Subgroup.centralizer ((Work.DSTR.F2p X : Subgroup X) : Set X))) : Subgroup.centralizer ((Work.DSTR.F2p X : Subgroup X) : Set X) ≤ Work.DSTR.F2p X := by
  -- `O_2(X) = ⊥` forces `F_{2'}(X) = F(X)`.
  have hF : Work.DSTR.F2p X = Work.GW2.fitting X :=
    le_antisymm (Work.DSTR.fittingPi_le' ({2}ᶜ : Set ℕ) X)
      (Work.DSTR.fitting_le_fittingPi_of_pCore_two_eq_bot X hA)
  rw [hF] at hsol ⊢
  classical
  set C : Subgroup X := Subgroup.centralizer ((Work.GW2.fitting X : Subgroup X) : Set X) with hC
  haveI hCnorm : C.Normal := by rw [hC]; exact inferInstance
  haveI hCsolv : Group.IsSolvable ↥C := hsol
  set K : Subgroup X := (Work.GW2.fitting ↥C).map C.subtype with hK
  haveI : (Work.GW2.fitting ↥C).Characteristic := by
    rw [Work.CORE2A.fitting_eq_isaacsFitting]; exact inferInstance
  haveI hKnorm : K.Normal := by rw [hK]; exact inferInstance
  haveI hKnil : Group.IsNilpotent ↥K := by
    rw [hK]
    have h1 : Group.IsNilpotent ↥(Work.GW2.fitting ↥C) := by
      rw [Work.CORE2A.fitting_eq_isaacsFitting]; exact inferInstance
    exact (Group.isNilpotent_congr (Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective)).mp h1
  have hKle : K ≤ Work.GW2.fitting X := by
    rw [hK]
    exact Work.CORE2A.le_fitting_of_normal_isNilpotent
  have hCK : C ≤ K := by
    intro c hc
    have hc' : c ∈ Subgroup.centralizer ((Work.GW2.fitting X : Subgroup X) : Set X) := by
      rw [← hC]; exact hc
    rw [Subgroup.mem_centralizer_iff] at hc'
    have hyK : ∀ y : ↥C, y ∈ Work.GW2.fitting ↥C → (y : X) ∈ K := by
      intro y hy
      rw [hK]
      exact ⟨y, hy, rfl⟩
    have hmem : (⟨c, hc⟩ : ↥C) ∈
        Subgroup.centralizer ((Work.GW2.fitting ↥C : Subgroup ↥C) : Set ↥C) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      exact hc' (y : X) (hKle (hyK y hy))
    have h2 : (⟨c, hc⟩ : ↥C) ∈ Work.GW2.fitting ↥C :=
      Work.DSTR.fittingSelfCentralizing ↥C hCsolv hmem
    exact ⟨⟨c, hc⟩, h2, rfl⟩
  calc C ≤ K := hCK
    _ ≤ Work.GW2.fitting X := hKle

end Work.DSTR.D16
