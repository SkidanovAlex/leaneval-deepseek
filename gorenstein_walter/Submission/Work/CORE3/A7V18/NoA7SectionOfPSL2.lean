import Mathlib
import Submission.Work.ASM.Defs
import Submission.Work.CORE3.MData.NoA7SectionPSL2
import Submission.Work.CORE2A.perfect_hom_odd_card
import Submission.Work.DSTR.fstar

/-!
# `CORE3` / `A7V18` / `NoA7SectionOfPSL2`

`Work.CORE3.MData.NoA7SectionPSL2` proves the "no `A₇`-section" statement for a normal subgroup
`L` of odd index with `L/Z(L) ≅ PSL(2, q)` containing a quasisimple `E` with `E/Z(E) ≅ A₇`,
`q = p^k ≥ 5` an odd prime power.  The present file removes the two hypotheses `E ≤ L` and
`L ⧸ Z(L) ≅ PSL(2, q)` from that statement, replacing them by the data that the intended
application actually supplies: an isomorphism `L ≃* PSL(2, q)` and the odd order theorem (in the
form of `Work.GW2.FeitThompsonProp`).

* `le_of_odd_index_of_perfect` : a perfect subgroup of a finite group lies in every normal
  subgroup of odd index.  Indeed `E/(E ∩ L) ≅ EL/L` is a quotient of the perfect group `E`
  (hence perfect) and a subgroup of `Q/L` of odd order (hence solvable, by the odd order
  theorem), so it is trivial and `E ≤ L`.
* `quotient_center_iso_of_center_bot` : if `L ≃* M` and `M` has trivial centre then
  `L ⧸ Z(L) ≃* M`.  (Here `M = PSL(2, q)` has trivial centre for `q ≥ 5` odd,
  `Work.DSTR.center_PSL`.)
-/

open scoped MatrixGroups

namespace Work.CORE3.A7V18

open Subgroup

/-- **A perfect subgroup lies in every normal subgroup of odd index.**
A homomorphism from a perfect group to a finite group of odd order is trivial (the odd order
theorem makes the target solvable, and a perfect solvable group is trivial), applied to the
composite `E ↪ Q ↠ Q/L`. -/
theorem le_of_odd_index_of_perfect {Q : Type} [Group Q] [Finite Q]
    (hFT : Work.GW2.FeitThompsonProp) (L : Subgroup Q) (hLn : L.Normal) (hLodd : Odd L.index)
    (E : Subgroup Q) (hE : ⁅E, E⁆ = E) : E ≤ L := by
  classical
  haveI : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hE
  have hoddQ : Odd (Nat.card (Q ⧸ L)) := by
    rw [← Subgroup.index_eq_card]
    exact hLodd
  have htriv : (QuotientGroup.mk' L).comp E.subtype = 1 :=
    Work.CORE2A.perfect_hom_odd_card hFT hoddQ _
  intro x hx
  have h2 := (MonoidHom.ext_iff.mp htriv) (⟨x, hx⟩ : ↥E)
  have h1 : (QuotientGroup.mk' L) x = 1 := by simpa using h2
  rw [QuotientGroup.mk'_apply] at h1
  exact (QuotientGroup.eq_one_iff x).mp h1

/-- **A central quotient of a centreless group.**  If `L ≃* M` and `M` has trivial centre, then
`L ⧸ Z(L) ≃* M`: the isomorphism carries `Z(L)` onto `Z(M) = ⊥`. -/
theorem quotient_center_iso_of_center_bot {L M : Type} [Group L] [Group M] (e : L ≃* M)
    (h : Subgroup.center M = ⊥) : Nonempty ((L ⧸ Subgroup.center L) ≃* M) := by
  have hc : Subgroup.center L = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    have hy2 : e y ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨w, rfl⟩ := e.surjective z
      have h3 := congrArg (⇑e) (Subgroup.mem_center_iff.mp hy w)
      simpa using h3
    rw [h] at hy2
    exact e.injective (by simpa using hy2)
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e⟩

theorem NoA7SectionOfPSL2 {Q : Type} [Group Q] [Finite Q] (hFT : Work.GW2.FeitThompsonProp) (L : Subgroup Q) (hLn : L.Normal) (hLodd : Odd L.index) (p k : ℕ) [Fact p.Prime] (hpodd : Odd p) (h5 : 5 ≤ p ^ k) (hLiso : Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) (E : Subgroup Q) (hEq : Work.GW2.IsQuasisimple E) (hA7 : Nonempty ((↥E ⧸ Subgroup.center ↥E) ≃* alternatingGroup (Fin 7))) : False := by
  classical
  -- The quasisimple `E` is perfect, so it lies in the odd-index normal subgroup `L`.
  have hEL : E ≤ L := le_of_odd_index_of_perfect hFT L hLn hLodd E hEq.1
  -- `PSL(2, q)` is centreless, so `L ⧸ Z(L) ≅* PSL(2, q)`.
  have hLq : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
    hLiso.elim fun eL => quotient_center_iso_of_center_bot eL
      (Work.DSTR.center_PSL p k hpodd h5)
  exact Work.CORE3.MData.NoA7SectionPSL2 p k hpodd h5 Q L hLn hLq E hEq hEL hA7

end Work.CORE3.A7V18
