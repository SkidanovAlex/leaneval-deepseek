import Mathlib
import Submission.Work.DSTR.D16.psl2_basic
import Submission.Work.CORE3.MData.A7QuotientSubgroupOf

open scoped MatrixGroups

namespace Work.CORE3.A7V18

/-- `PSL(2, q)` with `q = p ^ k ≥ 5` has trivial centre.  Indeed `PSL(2, q)` is simple
(`Work.DSTR.D16.psl2_basic`) and perfect; a simple group with non-trivial centre is
commutative, hence perfect-commutative, hence trivial — contradicting non-triviality. -/
theorem center_psl2_eq_bot (p k : ℕ) [Fact p.Prime] (hq : 5 ≤ p ^ k) :
    Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) = ⊥ := by
  obtain ⟨hsimple, hperfect, -⟩ := Work.DSTR.D16.psl2_basic p k hq
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
    hsimple
  haveI : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
    hperfect
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) with
    h | h
  · exact h
  · exfalso
    -- A simple group with whole centre is commutative, hence has trivial commutator;
    -- but `PSL(2, q)` is perfect so its commutator is everything.
    haveI : IsMulCommutative (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
      Subgroup.center_eq_top_iff.mp h
    have h1 : commutator (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) = ⊥ :=
      commutator_eq_bot _
    rw [Group.IsPerfect.commutator_eq_top] at h1
    have htriv : ∀ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k), x = 1 :=
      fun x => by
        have := (le_of_eq h1) (Subgroup.mem_top x)
        simpa using this
    exact not_subsingleton _ ⟨fun x y => by rw [htriv x, htriv y]⟩

theorem QuotientCenterIsoPSL2 {L : Type} [Group L] (p k : ℕ) [Fact p.Prime] (hq : 5 ≤ p ^ k)
    (h : Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) :
    Nonempty ((L ⧸ Subgroup.center L) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) := by
  obtain ⟨e⟩ := h
  -- Transport along `e = (L ≃* PSL(2, q))`: `Z L` maps onto `Z (PSL(2, q)) = ⊥`.
  have hc := center_psl2_eq_bot p k hq
  refine ⟨(QuotientGroup.congr (Subgroup.center L)
        (Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)))
        e (Subgroup.map_center_eq e)).trans
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)⟩

end Work.CORE3.A7V18
