import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.DSTR.dihedralQuotient
import Submission.Work.DSTR.dihOrCycHered
import Submission.Work.DSTR.layerOneInvClass

namespace Work.DSTR

open Subgroup

/-- **DS6** (`Work.GW2.QuasisimpleCenterOddProp`): the centre of a quasisimple subgroup is odd.  A central involution of `E` would be conjugate to every other involution of `E` (`InvolutionFusionProp`, applicable because `E` is perfect, so has no subgroup of index `2`, and because `h4` gives `E` a noncyclic -- hence dihedral -- Sylow 2 of order at least `4`) but only to itself.  The `FeitThompsonProp` hypothesis is needed to instantiate `h4`. -/
theorem quasisimpleCenterOdd (hFT : Work.GW2.FeitThompsonProp)
    (hsub : Work.GW2.DihedralSubgroupProp) (hfus : Work.GW2.InvolutionFusionProp)
    (h4 : Work.GW2.QuasisimpleSylowProp) : Work.GW2.QuasisimpleCenterOddProp := by
  intro X _instG _instF hsyl E hQ
  -- `Z(E)` has odd order: suppose it has even order.
  apply Nat.not_even_iff_odd.mp
  intro heven
  -- Then, by Cauchy, it contains an involution `z`.
  have h2dvd : 2 ∣ Nat.card (Subgroup.center ↥E) := even_iff_two_dvd.mp heven
  obtain ⟨z, hz2⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  set zE : ↥E := (z : ↥E) with hzE
  have hzE2 : orderOf zE = 2 := by
    rw [hzE, Subgroup.orderOf_coe z, hz2]
  -- `z` is central in `E`.
  have hzcent : ∀ g : ↥E, g * zE = zE * g := by
    intro g
    have h := (Subgroup.mem_center_iff.mp z.2) g
    rw [hzE]; exact h
  -- `E` is perfect, so has no normal subgroup of index `2`.
  have hperf : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hQ.1
  have hnoN : ∀ N : Subgroup ↥E, N.Normal → N.index ≠ 2 := index_ne_two_of_isPerfect hperf
  -- Transfer the Sylow 2-shape of `X` to `E` (DS1); `h4` makes a Sylow 2 of `E` noncyclic,
  -- hence dihedral of order `≥ 4`.
  have hsyE : Work.GW2.DihOrCycSylow ↥E :=
    (dihOrCycHered hsub dihedralQuotient X hsyl).1 E
  obtain ⟨S, n, hn2, hee⟩ : ∃ (S : Sylow 2 ↥E) (n : ℕ), 2 ≤ n ∧
      Nonempty ((S : Subgroup ↥E) ≃* DihedralGroup n) := by
    let S : Sylow 2 ↥E := Classical.choice (inferInstance : Nonempty (Sylow 2 ↥E))
    have hnc : ¬ IsCyclic (S : Subgroup ↥E) := h4 X hFT E hQ S
    rcases hsyE S with hcyc | ⟨n, ⟨e⟩⟩
    · exact absurd hcyc hnc
    · exact ⟨S, n, two_le_of_noncyclic_dihedral_iso n e hnc, ⟨e⟩⟩
  obtain ⟨e⟩ := hee
  -- Every involution of `E` is conjugate to every other one (`hfus`).
  have hconj := (hfus ↥E S n hn2 ⟨e⟩ hnoN).1
  -- Since `zE` is central, it is conjugate only to itself, so `zE` is the *unique* involution.
  have key : ∀ w : ↥E, orderOf w = 2 → w = zE := by
    intro w hw
    obtain ⟨g, hg⟩ := isConj_iff.mp (hconj zE w hzE2 hw)
    rw [← hg, hzcent g]
    group
  -- On the other hand the dihedral Sylow contains two distinct involutions.
  have hu2 : orderOf (((e.symm (DihedralGroup.sr 0) : ↥S)) : ↥E) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact (MulEquiv.orderOf_eq e.symm (DihedralGroup.sr 0)).trans (DihedralGroup.orderOf_sr 0)
  have hv2 : orderOf (((e.symm (DihedralGroup.sr 1) : ↥S)) : ↥E) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact (MulEquiv.orderOf_eq e.symm (DihedralGroup.sr 1)).trans (DihedralGroup.orderOf_sr 1)
  have huv : (((e.symm (DihedralGroup.sr 0) : ↥S)) : ↥E) ≠
      (((e.symm (DihedralGroup.sr 1) : ↥S)) : ↥E) := by
    intro h
    have h' : e.symm (DihedralGroup.sr 0) = e.symm (DihedralGroup.sr 1) := Subtype.ext h
    have h'' : (DihedralGroup.sr 0 : DihedralGroup n) = DihedralGroup.sr 1 := e.symm.injective h'
    rw [DihedralGroup.sr.injEq] at h''
    have hv : (1 : ZMod n).val = 1 := ZMod.val_one'' (by omega)
    have hval := congrArg ZMod.val h''
    rw [ZMod.val_zero, hv] at hval
    exact Nat.zero_ne_one hval
  exact huv ((key _ hu2).trans (key _ hv2).symm)

end Work.DSTR
