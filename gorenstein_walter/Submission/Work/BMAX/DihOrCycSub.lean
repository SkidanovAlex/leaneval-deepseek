/-
# BMAX: Sylow-2 heredity (`DihOrCycSylow` passes to subgroups)

The deliverable of this file is `Work.BMAX.DihOrCycSub`, i.e. the Prop
`Work.GW2.DihOrCycSubgroupProp` of `Submission/Work/BMAX/Defs.lean`:

  *every subgroup of a group whose Sylow 2-subgroups are cyclic or dihedral again has
  cyclic or dihedral Sylow 2-subgroups.*

This is the `DS1` step of the blueprint (Bender 1981, §2, first line: all proper subgroups
of the minimal counterexample are `D`-groups).

## The argument

Let `K ≤ X` and let `Q` be a Sylow 2-subgroup of `K`.  Through the inclusion `K ↪ X`, `Q` is
a 2-subgroup of `X`, so `Q` is contained in a Sylow 2-subgroup `P` of `X`; equivalently
(`Sylow.exists_comap_subtype_eq`) there is `P : Sylow 2 X` whose preimage in `K` is `Q`, and
then the map

  `↥Q →* ↥P`, `q ↦ q`

is an *injective* homomorphism.  Now `hX P` says that `P` is cyclic or dihedral:

* if `P` is cyclic then `↥Q`, a subgroup of a cyclic group, is cyclic
  (`isCyclic_of_injective`);
* if `P ≃* DihedralGroup n` then `↥Q` embeds into `DihedralGroup n`, and every *finite*
  subgroup of a dihedral group is cyclic or dihedral
  (`dihedral_subgroup_cyclic_or_dihedral`), whence so is `↥Q`.

The non-trivial input is the last point.  Its classical proof: let `T ≤ DihedralGroup m`.
If `T` lies in the rotation subgroup `⟨r⟩` (cyclic) it is cyclic.  Otherwise `T` contains a
reflection `s = sr i`; the rotation part `C = T ⊓ ⟨r⟩`, viewed inside `↥T`, is cyclic, has
index two, and is inverted by the involution `s ∉ C`, so the index-two recognition criterion
`Work.L2F.Dihedral.dihedral_recognition` gives `↥T ≃* DihedralGroup (Nat.card C)`.
-/
import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.Dihedral.Defs
import Submission.Work.L2F.Dihedral.dihedral_recognition

set_option linter.style.haveILetI false

namespace Work.BMAX

open Subgroup

/-- Every finite subgroup of a dihedral group is cyclic or dihedral (i.e. isomorphic to
`DihedralGroup k` for some `k`).  This holds for `m = 0` as well, where `DihedralGroup 0` is
the infinite dihedral group: the finiteness hypothesis on `T` is what is used, not on `m`. -/
theorem dihedral_subgroup_cyclic_or_dihedral {m : ℕ} (T : Subgroup (DihedralGroup m))
    [Finite ↥T] : IsCyclic ↥T ∨ ∃ k : ℕ, Nonempty (↥T ≃* DihedralGroup k) := by
  classical
  by_cases hT : T ≤ Work.Dihedral.rot m
  · -- `T` lies in the cyclic rotation subgroup.
    exact Or.inl (Subgroup.isCyclic_of_le hT)
  · -- `T` contains a reflection.  Write it as a reflection `s` over the cyclic rotation part.
    refine Or.inr ?_
    obtain ⟨x0, hx0T, hx0R⟩ : ∃ x, x ∈ T ∧ x ∉ Work.Dihedral.rot m := by
      by_contra h
      apply hT
      intro x hx
      by_contra hxR
      exact h ⟨x, hx, hxR⟩
    obtain ⟨i, hi⟩ := Work.Dihedral.notMem_rot.mp hx0R
    -- the rotation part of `T`, viewed inside `↥T`
    let C : Subgroup ↥T := (Work.Dihedral.rot m).subgroupOf T
    have hCcyc : IsCyclic ↥C := by
      -- `C` embeds into the cyclic group `⟨r⟩`.
      let f : ↥C →* ↥(Work.Dihedral.rot m) :=
        { toFun := fun x => ⟨((x : ↥T) : DihedralGroup m), x.2⟩
          map_one' := Subtype.ext rfl
          map_mul' := fun a b => Subtype.ext rfl }
      refine isCyclic_of_injective f (fun a b h => ?_)
      have h1 : ((a : ↥T) : DihedralGroup m) = ((b : ↥T) : DihedralGroup m) :=
        congrArg (fun y : ↥(Work.Dihedral.rot m) => (y : DihedralGroup m)) h
      exact Subtype.ext (Subtype.ext h1)
    haveI : IsCyclic ↥C := hCcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥C)
    have hg' : Subgroup.zpowers g = ⊤ := (Subgroup.eq_top_iff' _).mpr hg
    -- the reflection `s = sr i` of `T`
    let s : ↥T := ⟨DihedralGroup.sr i, by rw [← hi]; exact hx0T⟩
    have hsG : (s : DihedralGroup m) = DihedralGroup.sr i := rfl
    have hs2 : s ^ 2 = 1 := by
      apply Subtype.ext
      simp [Subgroup.coe_mul, hsG, pow_two, DihedralGroup.sr_mul_sr]
    have hsK : s ∉ C := by
      intro h
      have h2 : (s : DihedralGroup m) ∈ Work.Dihedral.rot m := Subgroup.mem_subgroupOf.mp h
      rw [hsG] at h2
      exact Work.Dihedral.sr_notMem_rot i h2
    -- `s` inverts the generator of `C`
    have hgrot : ((g : ↥T) : DihedralGroup m) ∈ Work.Dihedral.rot m :=
      Subgroup.mem_subgroupOf.mp g.2
    obtain ⟨a, ha⟩ := Work.Dihedral.mem_rot.mp hgrot
    have hconjG :
        (s : DihedralGroup m) * ((g : ↥T) : DihedralGroup m) * (s : DihedralGroup m)⁻¹ =
          (((g : ↥T) : DihedralGroup m))⁻¹ := by
      rw [hsG, ha, DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
        DihedralGroup.inv_r]
      congr 1
      ring
    have hconj : s * (g : ↥T) * s⁻¹ = (g : ↥T)⁻¹ := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconjG
    -- every element of `T` is in `C` or in the second coset `C * s`
    have hcover : ∀ x : ↥T, x ∈ C ∨ x * s ∈ C := by
      intro x
      by_cases hx : (x : DihedralGroup m) ∈ Work.Dihedral.rot m
      · exact Or.inl (Subgroup.mem_subgroupOf.mpr hx)
      · refine Or.inr (Subgroup.mem_subgroupOf.mpr ?_)
        obtain ⟨j, hj⟩ := Work.Dihedral.notMem_rot.mp hx
        have hxs : ((x * s : ↥T) : DihedralGroup m) = DihedralGroup.r (i - j) := by
          rw [Subgroup.coe_mul, hj, hsG, DihedralGroup.sr_mul_sr]
        rw [hxs]
        exact Work.Dihedral.r_mem_rot _
    obtain ⟨e⟩ := Work.L2F.Dihedral.dihedral_recognition C g hg' s hs2 hsK hconj hcover
    exact ⟨Nat.card ↥C, ⟨e⟩⟩

/-- If a finite group embeds into a dihedral group, it is cyclic or dihedral. -/
theorem cyclic_or_dihedral_of_injective_into_dihedral {m : ℕ} {H : Type*} [Group H] [Finite H]
    (f : H →* DihedralGroup m) (hf : Function.Injective f) :
    IsCyclic H ∨ ∃ k : ℕ, Nonempty (H ≃* DihedralGroup k) := by
  classical
  let T : Subgroup (DihedralGroup m) := f.range
  haveI hfinT : Finite ↥T :=
    Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hinj : Function.Injective f.rangeRestrict := fun a b h =>
    hf (by simpa using congrArg Subtype.val h)
  have eH : H ≃* ↥T :=
    MulEquiv.ofBijective f.rangeRestrict ⟨hinj, f.rangeRestrict_surjective⟩
  rcases dihedral_subgroup_cyclic_or_dihedral T with hT | ⟨k, ⟨eT⟩⟩
  · left
    exact (MulEquiv.isCyclic eH).mpr hT
  · right
    exact ⟨k, ⟨eH.trans eT⟩⟩

theorem DihOrCycSub : Work.GW2.DihOrCycSubgroupProp := by
  intro X _ _ hX K Q
  -- `Q`, viewed inside `X`, is contained in a Sylow 2-subgroup `P` of `X`.
  obtain ⟨P, hP⟩ := Q.exists_comap_subtype_eq
  -- the inclusion `↥Q →* ↥P`
  let φ : ↥(Q : Subgroup ↥K) →* ↥(P : Subgroup X) :=
    { toFun := fun x => ⟨(x : ↥K), by
        have hx : (x : ↥K) ∈ (P : Subgroup X).comap K.subtype := by
          rw [hP]; exact x.2
        exact Subgroup.mem_comap.mp hx⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : ((a : ↥K) : X) = ((b : ↥K) : X) :=
      congrArg (fun z : ↥(P : Subgroup X) => (z : X)) hab
    exact Subtype.ext (Subtype.ext h1)
  rcases hX P with hcyc | ⟨n, ⟨e⟩⟩
  · -- `P` is cyclic, so `Q` is cyclic.
    left
    haveI : IsCyclic ↥(P : Subgroup X) := hcyc
    exact isCyclic_of_injective φ hφinj
  · -- `P` is dihedral, so `Q` embeds into it and is cyclic or dihedral.
    have hf : Function.Injective ((e.toMonoidHom).comp φ) :=
      fun a b hab => hφinj (e.injective hab)
    exact cyclic_or_dihedral_of_injective_into_dihedral ((e.toMonoidHom).comp φ) hf

end Work.BMAX
