import Mathlib
import Submission.Work.CORE3.A7V18.Prelim
import Submission.Work.CORE2A.c14_aux_index_Lsub
import Submission.Work.CORE2A.c14_aux_isPerfect_Lsub

/-!
# CORE3 / A7V18: the commutator subgroup of a copy of `PGL₂(q)` is `PSL₂(q)`

Let `L ≤ Q` be a subgroup isomorphic to `PGL(2, q) = ProjGenLinGroup (Fin 2) (GF(p,k))` for an odd
prime `p` and `q = p ^ k ≥ 5`.  Then the commutator subgroup `⁅L, L⁆` (a subgroup of `Q`) is
isomorphic to `PSL(2, q)`.

This is an entirely formal consequence of two facts:

* `⁅L, L⁆` is the commutator subgroup of the group `↥L`
  (`Subgroup.map_subtype_commutator`);
* the commutator subgroup of `PGL₂(q)` is the image `L₂(q) = Lsub p k` of `PSL₂(q)`
  (`Work.CORE3.A7V18.commutator_top_eq_Lsub`), which is in turn isomorphic to `PSL₂(q)` since
  `ProjectiveSpecialLinearGroup.toPGL` is injective.
-/

namespace Work.CORE3.A7V18

open scoped MatrixGroups

/-- **An isomorphism of groups induces an isomorphism of their commutator subgroups.** -/
private theorem commutator_isNonempty_iso {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nonempty (↥(commutator G) ≃* ↥(commutator H)) := by
  have hrange : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
  have hmap : Subgroup.map e.toMonoidHom (commutator G) = commutator H := by
    rw [map_commutator_eq, hrange]
    exact (commutator_def H).symm
  exact ⟨(Subgroup.equivMapOfInjective (commutator G) e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hmap)⟩

/-- **The commutator subgroup of a subgroup.**  If `L ≤ Q`, then `⁅L,L⁆` (as a subgroup of `Q`)
is isomorphic to the commutator subgroup of the group `↥L`. -/
private theorem commutator_subgroup_isNonempty_iso {Q : Type} [Group Q] (L : Subgroup Q) :
    Nonempty (↥(commutator ↥L) ≃* ↥(⁅L, L⁆ : Subgroup Q)) :=
  ⟨(Subgroup.equivMapOfInjective (commutator ↥L) L.subtype L.subtype_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator L))⟩

/-- **The image `L₂(q) ≤ PGL₂(q)` of `PSL₂(q)` is isomorphic to `PSL₂(q)`.** -/
private theorem Lsub_isNonempty_iso (p k : ℕ) [Fact p.Prime] :
    Nonempty (↥(Work.GW2.Lsub p k) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
  ⟨(MonoidHom.ofInjective (f := Matrix.ProjectiveSpecialLinearGroup.toPGL)
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).symm⟩

theorem CommutatorIsoPSL2 {Q : Type} [Group Q] (L : Subgroup Q) (p k : ℕ) [Fact p.Prime]
    (hp : Odd p) (hq : 5 ≤ p ^ k)
    (h : Nonempty (L ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k))) :
    Nonempty (↥(⁅L, L⁆ : Subgroup Q) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) := by
  obtain ⟨e⟩ := h
  -- `⁅L,L⁆` is the commutator subgroup of the group `↥L`.
  obtain ⟨i₁⟩ := commutator_subgroup_isNonempty_iso L
  -- any isomorphism `↥L ≃* PGL₂(q)` maps the commutator subgroup onto `⁅PGL₂(q), PGL₂(q)⁆`.
  obtain ⟨i₂'⟩ := commutator_isNonempty_iso e
  -- `⁅PGL₂(q), PGL₂(q)⁆ = Lsub p k` (Bender's notation for the image of `PSL₂(q)`).
  obtain ⟨i₂⟩ : Nonempty (↥(commutator ↥L) ≃* ↥(Work.GW2.Lsub p k)) :=
    ⟨i₂'.trans (MulEquiv.subgroupCongr (commutator_top_eq_Lsub p k hp hq))⟩
  obtain ⟨i₃⟩ := Lsub_isNonempty_iso p k
  exact ⟨i₁.symm.trans (i₂.trans i₃)⟩

end Work.CORE3.A7V18
