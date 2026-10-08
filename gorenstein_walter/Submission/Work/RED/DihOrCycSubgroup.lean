import Mathlib
import Submission.Work.RED.Basic

/-!
# RED: `DihOrCycSylow` is inherited by subgroups

If every Sylow 2-subgroup of `G` is cyclic or dihedral, then the same holds for every
subgroup `K ≤ G`.  Indeed, a Sylow 2-subgroup `Q` of `K`, viewed inside `G`, is a 2-subgroup
of `G`, hence lies in some Sylow 2-subgroup `P` of `G`.  If `P` is cyclic then `Q`, being a
subgroup of a cyclic group, is cyclic.  If `P ≅ DihedralGroup n`, then the image of `Q` in
`DihedralGroup n` is cyclic or dihedral by the hypothesis `hsub` (which is
`Work.RED.DihedralSubgroup`), and `Q` is isomorphic to that image.
-/

namespace Work.RED

open Subgroup

/-- A finite dihedral group has nonzero parameter. -/
theorem neZero_of_finite_dihedral {n : ℕ} (h : Finite (DihedralGroup n)) : NeZero n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn] at h
    exact (not_finite_iff_infinite.mpr (inferInstance : Infinite (DihedralGroup 0)) h).elim
  · exact ⟨hn.ne'⟩

theorem DihOrCycSubgroup
    (hsub : ∀ (n : ℕ) [NeZero n] (H : Subgroup (DihedralGroup n)),
      IsCyclic ↥H ∨ ∃ m : ℕ, Nonempty (↥H ≃* DihedralGroup m))
    {G : Type*} [Group G] [Finite G] (K : Subgroup G) (h : Work.RED.GW2.DihOrCycSylow G) :
    Work.RED.GW2.DihOrCycSylow ↥K := by
  intro Q
  -- `Q`, viewed inside `G`, and the isomorphism `↥Q ≃* ↥QG`.
  let QG : Subgroup G := (Q : Subgroup ↥K).map K.subtype
  have heQ : ↥(Q : Subgroup ↥K) ≃* ↥QG :=
    Subgroup.equivMapOfInjective (Q : Subgroup ↥K) K.subtype K.subtype_injective
  have hQp : IsPGroup 2 ↥QG := (Q.isPGroup').of_equiv heQ
  obtain ⟨P, hPle⟩ := hQp.exists_le_sylow
  rcases h P with hcyc | ⟨n, ⟨e⟩⟩
  · -- `P` is cyclic, hence so are `QG` and `Q`.
    left
    haveI : IsCyclic ↥(P : Subgroup G) := hcyc
    exact (MulEquiv.isCyclic heQ).mpr (isCyclic_of_le hPle)
  · -- `P ≅ DihedralGroup n`; push `Q` into `DihedralGroup n` and use `hsub`.
    haveI : NeZero n :=
      neZero_of_finite_dihedral
        (Finite.of_injective (e.symm : DihedralGroup n → ↥(P : Subgroup G)) e.symm.injective)
    let Q'' : Subgroup ↥(P : Subgroup G) := QG.subgroupOf (P : Subgroup G)
    let H' : Subgroup (DihedralGroup n) := Q''.map e.toMonoidHom
    have h1 : ↥Q'' ≃* ↥QG := Subgroup.subgroupOfEquivOfLe hPle
    have h2 : ↥Q'' ≃* ↥H' := Subgroup.equivMapOfInjective Q'' e.toMonoidHom e.injective
    rcases hsub n H' with hcyc' | ⟨m, ⟨em⟩⟩
    · left
      haveI : IsCyclic ↥Q'' := (MulEquiv.isCyclic h2).mpr hcyc'
      haveI : IsCyclic ↥QG := (MulEquiv.isCyclic h1).mp inferInstance
      exact (MulEquiv.isCyclic heQ).mpr inferInstance
    · right
      exact ⟨m, ⟨heQ.trans (h1.symm.trans (h2.trans em))⟩⟩

end Work.RED
