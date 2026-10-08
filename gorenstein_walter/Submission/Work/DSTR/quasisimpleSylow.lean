import Mathlib
import Submission.Work.DSTR.Defs

namespace Work.DSTR

set_option linter.style.haveILetI false

open Subgroup

/-- **DS4** (`Work.GW2.QuasisimpleSylowProp`): a quasisimple subgroup has noncyclic Sylow 2-subgroups.  (Cyclic Sylow 2 gives a normal subgroup of index 2, so the group is not perfect; odd order is excluded by Feit--Thompson.) -/
theorem quasisimpleSylow : Work.GW2.QuasisimpleSylowProp := by
  intro X instG instF hFT E hQ P hcyc
  obtain ⟨hcomm, hsimple⟩ := hQ
  -- `E` is nontrivial, since its central quotient is simple.
  have hN : Nontrivial ↥E := by
    by_contra h
    haveI : Subsingleton ↥E := not_nontrivial_iff_subsingleton.mp h
    haveI : Nontrivial (↥E ⧸ Subgroup.center ↥E) := hsimple.toNontrivial
    exact (not_subsingleton (↥E ⧸ Subgroup.center ↥E)) inferInstance
  -- `E` is perfect.
  haveI hperf : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hcomm
  -- Feit–Thompson rules out the odd order case.
  have h2dvd : 2 ∣ Nat.card ↥E := by
    by_contra h
    have hodd : Odd (Nat.card ↥E) := Nat.not_even_iff_odd.mp (fun he => h (even_iff_two_dvd.mp he))
    haveI : Group.IsSolvable ↥E := hFT ↥E hodd
    exact Group.IsPerfect.not_isSolvable ↥E inferInstance
  have hp2 : (Nat.card ↥E).minFac = 2 := Nat.minFac_eq_two_iff _ |>.mpr h2dvd
  -- Burnside's normal `p`-complement theorem for the cyclic Sylow 2-subgroup.
  have hle : Subgroup.normalizer (P : Set ↥E) ≤ Subgroup.centralizer (P : Set ↥E) :=
    IsCyclic.normalizer_le_centralizer hp2 hcyc
  set K : Subgroup ↥E := (MonoidHom.transferSylow P hle).ker with hKdef
  haveI hKnorm : K.Normal := by rw [hKdef]; exact MonoidHom.normal_ker _
  have hcomp : K.IsComplement' (P : Subgroup ↥E) :=
    MonoidHom.ker_transferSylow_isComplement' P hle
  -- `E ⧸ K` is a 2-group (it is isomorphic to `P`).
  have hcard : Nat.card (↥E ⧸ K) = Nat.card (P : Subgroup ↥E) := by
    rw [← Subgroup.index_eq_card K, hcomp.symm.index_eq_card]
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  haveI hpg : IsPGroup 2 (↥E ⧸ K) := IsPGroup.of_card (by rw [hcard, hk])
  haveI : Group.IsNilpotent (↥E ⧸ K) := IsPGroup.isNilpotent (p := 2) hpg
  haveI : Group.IsSolvable (↥E ⧸ K) := IsNilpotent.to_isSolvable
  haveI : Group.IsPerfect (↥E ⧸ K) := inferInstance
  -- A perfect solvable group is trivial, hence `K = ⊤`.
  have htriv : Subsingleton (↥E ⧸ K) := by
    by_contra h
    haveI : Nontrivial (↥E ⧸ K) := not_subsingleton_iff_nontrivial.mp h
    exact Group.IsPerfect.not_isSolvable (↥E ⧸ K) inferInstance
  have hKtop : K = ⊤ := QuotientGroup.subgroup_eq_top_of_subsingleton K htriv
  -- But `K` (the kernel of the transfer) has odd order, a contradiction.
  have hoddK : ¬ 2 ∣ Nat.card ↥K := by
    rw [hKdef]
    exact MonoidHom.not_dvd_card_ker_transferSylow P hle
  rw [hKtop, Subgroup.card_top] at hoddK
  exact hoddK h2dvd

end Work.DSTR
