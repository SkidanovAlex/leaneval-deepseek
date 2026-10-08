import Mathlib
import Submission.Work.ASM.Defs
import Submission.Work.CORE2A.c14_aux_index_Lsub
import Submission.Work.CORE2A.c14_aux_isPerfect_Lsub

/-!
# CORE3 / A7V18: elementary preliminaries for `NotA7QuotientPSL2PGL2`

Three elementary general facts used in the proof of
`Work.CORE3.A7V18.NotA7QuotientPSL2PGL2`:

* `le_ker_of_isSolvable_of_perfect` — a perfect subgroup has no nontrivial solvable image;
  equivalently every homomorphism from a perfect group to a solvable group is trivial
  (a perfect solvable group is trivial, `Group.IsPerfect.not_isSolvable`);
* `commutator_le_of_index_eq_two` — a subgroup of index two contains the commutator subgroup
  (an index-two subgroup is normal and its quotient has order two, hence is commutative);
* `commutator_top_eq_Lsub` — the commutator subgroup of `PGL₂(q) = PGL(2, GF(p,k))` is
  `L₂(q) = Lsub p k = toPGL.range`, the image of `PSL₂(q)` (for `p` an odd prime and `q ≥ 5`).
  Here `≤` follows from `[PGL₂(q) : L₂(q)] = 2` (`Work.CORE2A.c14_aux_index_Lsub`), and `≥`
  from the perfectness of `L₂(q)` (`Work.CORE2A.c14_aux_isPerfect_Lsub`).

These are the two ingredients of the reduction "a copy of `PGL₂(q)` containing a perfect
subgroup `E` has `E ≤ [L,L] ≅ L₂(q)`".
-/

open scoped MatrixGroups

namespace Work.CORE3.A7V18

/-- **A perfect subgroup has no nontrivial solvable image.**  If `⁅E,E⁆ = E` then any
homomorphism `f` from the ambient group to a solvable group annihilates `E`. -/
theorem le_ker_of_isSolvable_of_perfect {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hsol : Group.IsSolvable H) (E : Subgroup G) (hE : ⁅E, E⁆ = E) :
    E ≤ f.ker := by
  haveI : Group.IsSolvable H := hsol
  haveI : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hE
  have hperf : Group.IsPerfect ↥(E.map f) := Group.IsPerfect.map f (H := E)
  have hbot : E.map f = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥(E.map f) := (Subgroup.nontrivial_iff_ne_bot (E.map f)).mpr hne
    haveI : Group.IsSolvable ↥(E.map f) := inferInstance
    exact Group.IsPerfect.not_isSolvable ↥(E.map f) inferInstance
  rwa [Subgroup.map_eq_bot_iff] at hbot

/-- **A subgroup of index two contains the commutator subgroup.** -/
theorem commutator_le_of_index_eq_two {G : Type*} [Group G] {N : Subgroup G}
    (h : N.index = 2) : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro g _ h' _
  have e1 : g * h' ∈ N ↔ h' * g ∈ N := by
    rw [Subgroup.mul_mem_iff_of_index_two h, Subgroup.mul_mem_iff_of_index_two h]
    exact Iff.comm
  have key : (g * h') * (h' * g)⁻¹ ∈ N := by
    rw [Subgroup.mul_mem_iff_of_index_two h, Subgroup.inv_mem_iff N]
    exact e1
  simpa [commutatorElement_def, mul_inv_rev, mul_assoc] using key

/-- **The commutator subgroup of `PGL₂(q)` is `L₂(q)`.**  For `q = p ^ k` an odd prime power
with `q ≥ 5`, the commutator subgroup of `PGL(2, GF(p,k))` is the image `L₂(q)` of `PSL₂(q)`. -/
theorem commutator_top_eq_Lsub (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k) :
    ⁅(⊤ : Subgroup (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k))), ⊤⁆ =
      Work.GW2.Lsub p k := by
  apply le_antisymm
  · exact commutator_le_of_index_eq_two (Work.CORE2A.c14_aux_index_Lsub p k hp hq)
  · haveI : Group.IsPerfect ↥(Work.GW2.Lsub p k) :=
      Work.CORE2A.c14_aux_isPerfect_Lsub p k hp hq
    rw [← Subgroup.commutator_eq_self (H := Work.GW2.Lsub p k)]
    exact Subgroup.commutator_mono le_top le_top

end Work.CORE3.A7V18
