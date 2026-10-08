/-
Area `CORE3`, `MData`: auxiliaries for `Work.CORE3.MData.NoA7SectionPSL2`.

The main theorem `NoA7SectionPSL2` shows that `A₇` is not a section of `PSL(2, q)` (`q = p ^ k`
odd, `q ≥ 5`).  Its proof proceeds by the local structure of the centralizer of an involution:
in `PSL(2, q)` the centralizer of an involution is dihedral (`Work.L2F.l2InvolutionCentralizer`),
hence every subgroup of it is cyclic or dihedral, whereas the centralizer of an involution of `A₇`
is neither (`Work.AUTA7.A7.CentralizerInvolution` plus the absence of elements of order `12`).

This file collects the small vocabulary used by both the main file and the delegated pieces:

* `CycOrDih G` — `G` is cyclic or isomorphic to a dihedral group;
* `CycOrDih.of_iso` — invariance under isomorphisms;
* `CycOrDih_of_le_dihedral` — subgroups of a dihedral group are cyclic or dihedral;
* `CycOrDih_of_le_of_mulEquiv` — the same in the form needed in the main proof, where the
  ambient centralizer is only *isomorphic* to a dihedral group.
-/
import Mathlib
import Submission.Work.ASM.Defs
import Submission.Work.L2F.Main
import Submission.Work.A7.Defs
import Submission.Work.AUTA7.A7.CentralizerInvolution
import Submission.Work.AUTA7.A7.A7KNoOrderFour
import Submission.Work.AUTA7.A7.SylowTwoSubgroup
import Submission.Work.AUTA7.A7.dihedral_subgroup_isCyclic_or_dihedral
import Submission.Work.DSTR.dihedralQuotient

namespace Work.CORE3.MData

open Subgroup

/-- `G` is cyclic or (isomorphic to) a dihedral group. -/
def CycOrDih (G : Type*) [Group G] : Prop :=
  IsCyclic G ∨ ∃ n : ℕ, Nonempty (G ≃* DihedralGroup n)

/-- `CycOrDih` is invariant under group isomorphisms. -/
theorem CycOrDih.of_iso {G H : Type*} [Group G] [Group H] (e : G ≃* H) (h : CycOrDih G) :
    CycOrDih H := by
  rcases h with h | ⟨n, ⟨en⟩⟩
  · exact Or.inl ((MulEquiv.isCyclic e).mp h)
  · exact Or.inr ⟨n, ⟨e.symm.trans en⟩⟩

/-- A cyclic group is cyclic-or-dihedral. -/
theorem CycOrDih_of_isCyclic {G : Type*} [Group G] (h : IsCyclic G) : CycOrDih G :=
  Or.inl h

/-- A group isomorphic to a dihedral group is cyclic-or-dihedral. -/
theorem CycOrDih_of_dihedral {G : Type*} [Group G] {n : ℕ}
    (h : Nonempty (G ≃* DihedralGroup n)) : CycOrDih G :=
  Or.inr ⟨n, h⟩

/-- Subgroups of a dihedral group are cyclic or dihedral. -/
theorem CycOrDih_of_le_dihedral {n : ℕ} [NeZero n] (H : Subgroup (DihedralGroup n)) :
    CycOrDih ↥H :=
  Work.AUTA7.A7.dihedral_subgroup_isCyclic_or_dihedral H

/-- **Transport form used in the main proof.**  If `A` is a subgroup of `C` and `C` is isomorphic
to a dihedral group, then `A` is cyclic or dihedral.

(`C` will be the centralizer of an involution in `PSL(2, q)`: it is *isomorphic to* a dihedral
group, not literally one, and `A` is the image of the layer in question.) -/
theorem CycOrDih_of_le_of_mulEquiv {P : Type*} [Group P] {A C : Subgroup P} (hAC : A ≤ C)
    {n : ℕ} [NeZero n] (e : ↥C ≃* DihedralGroup n) : CycOrDih ↥A := by
  have hH : CycOrDih ↥((A.subgroupOf C).map (e : ↥C →* DihedralGroup n)) :=
    Work.AUTA7.A7.dihedral_subgroup_isCyclic_or_dihedral _
  refine CycOrDih.of_iso ?_ hH
  exact (e.subgroupMap (A.subgroupOf C)).symm.trans (Subgroup.subgroupOfEquivOfLe hAC)

/-- **Quotients of cyclic-or-dihedral groups are cyclic-or-dihedral.** -/
theorem CycOrDih_quotient {G : Type*} [Group G] (h : CycOrDih G) (N : Subgroup G) [N.Normal] :
    CycOrDih (G ⧸ N) := by
  rcases h with hcyc | ⟨n, ⟨e⟩⟩
  · exact Or.inl (isCyclic_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N))
  · haveI : (N.map (e : G →* DihedralGroup n)).Normal :=
      (inferInstance : N.Normal).map _ e.surjective
    have hiso : G ⧸ N ≃* DihedralGroup n ⧸ N.map (e : G →* DihedralGroup n) :=
      QuotientGroup.congr N (N.map (e : G →* DihedralGroup n)) e rfl
    rcases Work.DSTR.dihedralQuotient n (N.map (e : G →* DihedralGroup n)) with h2 | h2
    · exact Or.inl ((MulEquiv.isCyclic hiso).mpr h2)
    · obtain ⟨m, ⟨e2⟩⟩ := h2
      exact Or.inr ⟨m, ⟨hiso.trans e2⟩⟩

/-! ## A subgroup of order `8` of `A₇` is dihedral of order `8`

`|A₇| = 2520 = 8 · 315`, so every subgroup of order `8` is a Sylow `2`-subgroup; all Sylow
`2`-subgroups are conjugate, and the explicit subgroup `dihToA7.range` of
`Submission.Work.AUTA7.A7.SylowTwoSubgroup` is one of them and is isomorphic to
`DihedralGroup 4`. -/

/-- **A subgroup of order `8` of `A₇` is isomorphic to `DihedralGroup 4`.** -/
theorem subgroup_card_eight_a7 (K : Subgroup (alternatingGroup (Fin 7))) (hK : Nat.card ↥K = 8) :
    Nonempty (↥K ≃* DihedralGroup 4) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKp : IsPGroup 2 K := IsPGroup.of_card (n := 3) (by rw [hK]; norm_num)
  have hKnotdvd : ¬ 2 ∣ K.index := by
    have h := Subgroup.card_mul_index K
    rw [hK, Work.A7.card_alternatingGroup_seven] at h
    rintro ⟨k, hk⟩
    rw [hk] at h
    omega
  let P : Sylow 2 (alternatingGroup (Fin 7)) := hKp.toSylow hKnotdvd
  have hP : (P : Subgroup (alternatingGroup (Fin 7))) = K := IsPGroup.toSylow_coe hKp hKnotdvd
  obtain ⟨K₀, ⟨e₀⟩⟩ := Work.AUTA7.A7.SylowTwoSubgroup
  have hK₀card : Nat.card ↥K₀ = 8 := by
    rw [Nat.card_congr e₀.toEquiv, DihedralGroup.nat_card]
  have hK₀p : IsPGroup 2 K₀ := IsPGroup.of_card (n := 3) (by rw [hK₀card]; norm_num)
  have hK₀notdvd : ¬ 2 ∣ K₀.index := by
    have h := Subgroup.card_mul_index K₀
    rw [hK₀card, Work.A7.card_alternatingGroup_seven] at h
    rintro ⟨k, hk⟩
    rw [hk] at h
    omega
  let P₀ : Sylow 2 (alternatingGroup (Fin 7)) := hK₀p.toSylow hK₀notdvd
  have hP₀ : (P₀ : Subgroup (alternatingGroup (Fin 7))) = K₀ := IsPGroup.toSylow_coe hK₀p hK₀notdvd
  exact ⟨(MulEquiv.subgroupCongr hP).symm.trans
    ((Sylow.equiv P P₀).trans ((MulEquiv.subgroupCongr hP₀).trans e₀))⟩

end Work.CORE3.MData
