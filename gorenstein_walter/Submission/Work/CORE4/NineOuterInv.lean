import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2K1_ne_bot
import Submission.Work.CORE4.A7Vsylow
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.NineOuterInvContra
import Submission.Work.CORE4.NineQuasisimpleSylowNotCyclic
import Submission.Work.AUTL2.A5.basic

namespace Work.CORE4

open Subgroup

set_option linter.style.haveILetI false

/-- **LEAF C10.N5a `NineOuterInv`** (Bender p. 226): "If `S ⊄ E`, then `S ∩ M ⊄ E` because
`N_S(S∩E)` normalizes `C_{F(U)}(S∩E) = F`", plus the choice of an involution `r ∈ (S∩M) ∖ E`.

`NineOuterInvProp I` gives, from `Hyp9 G B C` and `¬ B.S ≤ layerIn C.D.M`:
`∃ r ∈ (B.S : Subgroup G) ⊓ C.D.M, orderOf r = 2 ∧ r ∉ layerIn C.D.M`.

Route (design pass 10 §3.3, N5a, with the reviewer's addendum):
* `C_{F(U)}(S∩E) = F` uses `Case2PrePlus`'s `B₀` clause and `Case2Pre`'s `B₀ = C_U(s)`;
* if `S ∩ M ≤ E` then `S ∩ E = S ∩ M`; if moreover `S ≠ S ∩ E`, then `N_S(S∩E) > S ∩ E` normalizes
  `F`, hence lies in `N_G(F) = M`, hence in `S ∩ M = S ∩ E`, a contradiction;
* **new (reviewer 1):** `S ∩ M` must be shown non-cyclic.  `DihOrCycSylow` allows a cyclic Sylow;
  in that case Burnside transfer (`IsCyclic.isComplement'`) makes `M` 2-nilpotent, so `M'` is odd,
  while `E = E(M) ≤ M'` is even (it contains `s`) — contradiction;
* in the dihedral `S ∩ M`, involutions outside the cyclic maximal subgroup generate, so one of them
  lies outside the proper normal subgroup `S ∩ E`.

Formalisation.  Write `S := (B.S : Subgroup G)`, `M := C.D.M` and `E := layerIn C.D.M`.  We use
`Work.CORE4.NineOuterInvContra` (`S ∩ M ≤ E ⟹ S ≤ E`, i.e. `¬ S ≤ E` forces `S ∩ M ⊄ E`, so that
`X := S ∩ E` is a *proper* subgroup of `S ∩ M`), and `Work.CORE4.NineQuasisimpleSylowNotCyclic`
applied to the quasisimple `E` (`Work.CORE4.LayerCtx6`) to see that `S ∩ E` is *not* cyclic
(`S ∩ E` is a Sylow `2`-subgroup of `E` by `Work.CORE4.not_two_dvd_relIndex_inf_of_normal`).
Inside the group `↥S`, which is cyclic or dihedral (`BenderCtx.sylow`), the general group-theoretic
fact `Work.AUTL2.A5.exists_involution_outside_of_ne_of_not_cyclic` then produces an involution
`z ∈ (S ∩ M).subgroupOf S ∖ (S ∩ E).subgroupOf S`, whose underlying element of `G` is the required
`r`. -/
theorem NineOuterInv (I : Work.GW2.C4Inputs) : Work.GW2.NineOuterInvProp I := by
  intro G _ _ B C hH hSE
  obtain ⟨hbc, hc2, hplus, hseven, height⟩ := hH
  have hpre : Work.GW2.Case2Pre B C.D := C.pre
  set S : Subgroup G := (B.S : Subgroup G) with hSdef
  set M : Subgroup G := C.D.M with hMdef
  set E : Subgroup G := Work.GW2.layerIn C.D.M with hEdef
  have hEM : E ≤ M := by rw [hEdef, hMdef]; exact Work.CORE4.layerIn_le C.D.M
  have hEsub : M ≤ Subgroup.normalizer (E : Set G) := by
    rw [hEdef, hMdef]; exact Work.CORE4.layerIn_le_normalizer C.D.M
  have hoddPM : ¬ 2 ∣ (S ⊓ M).relIndex M := by rw [hSdef, hMdef]; exact hplus.1
  -- `S ∩ E` is a Sylow `2`-subgroup of `E`
  have hoddQE : ¬ 2 ∣ (S ⊓ E).relIndex E :=
    not_two_dvd_relIndex_inf_of_normal M E S hEM hEsub hoddPM
  -- `E` is quasisimple, hence has no cyclic Sylow `2`-subgroup; so `S ∩ E` is not cyclic
  have hqE : Work.GW2.IsQuasisimple E := by
    rw [hEdef]
    exact (LayerCtx6 I hbc C (DihOrCycSub hbc.sylow C.D.M)).1
  have hncyc : ¬ IsCyclic ↥(S ⊓ E) := by
    intro hcyc
    have hQE : S ⊓ E ≤ E := inf_le_right
    have hpg : IsPGroup 2 ↥(S ⊓ E) :=
      IsPGroup.to_le (B.S).isPGroup' (by rw [hSdef]; exact inf_le_left)
    have hpg' : IsPGroup 2 ↥((S ⊓ E).subgroupOf E) := IsPGroup.comap_subtype hpg
    have hodd : ¬ 2 ∣ ((S ⊓ E).subgroupOf E).index := hoddQE
    let P : Sylow 2 ↥E := hpg'.toSylow hodd
    have hPcoe : (P : Subgroup ↥E) = (S ⊓ E).subgroupOf E :=
      IsPGroup.toSylow_coe hpg' hodd
    have hcycP : IsCyclic ↥(P : Subgroup ↥E) := by
      rw [hPcoe]
      exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hQE)).mpr hcyc
    exact NineQuasisimpleSylowNotCyclic hqE P hcycP
  -- in the group `↥S`, the subgroup `S ∩ E` is a proper subgroup of `S ∩ M`
  have hle : (S ⊓ E).subgroupOf S ≤ (S ⊓ M).subgroupOf S :=
    Subgroup.subgroupOf_mono S (le_inf inf_le_left (le_trans inf_le_right hEM))
  have hne : (S ⊓ E).subgroupOf S ≠ (S ⊓ M).subgroupOf S := by
    intro h
    have h2 : (S ⊓ E) ⊓ S = (S ⊓ M) ⊓ S := Subgroup.subgroupOf_inj.mp h
    rw [inf_eq_left.mpr (inf_le_left : S ⊓ E ≤ S),
      inf_eq_left.mpr (inf_le_left : S ⊓ M ≤ S)] at h2
    apply hSE
    have hSM : S ⊓ M ≤ E := by rw [← h2]; exact inf_le_right
    exact NineOuterInvContra B C.D hpre hplus hSM
  have hT : ¬ IsCyclic ↥((S ⊓ E).subgroupOf S) := by
    intro hc
    exact hncyc ((MulEquiv.isCyclic
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : S ⊓ E ≤ S))).mp hc)
  obtain ⟨z, hzS', hzT, hz2⟩ := Work.AUTL2.A5.exists_involution_outside_of_ne_of_not_cyclic
    ((S ⊓ E).subgroupOf S) ((S ⊓ M).subgroupOf S) (hbc.sylow B.S) hle hT hne
  refine ⟨((z : ↥(B.S)) : G), Subgroup.mem_subgroupOf.mp hzS', ?_, ?_⟩
  · -- the underlying element of `G` has order `2`
    have hzz : ((z : ↥(B.S)) : G) * ((z : ↥(B.S)) : G) = 1 := by
      have h := congrArg (fun w : ↥(B.S) => (w : G)) hz2
      simpa using h
    have hz1 : z ≠ 1 := fun h => hzT (h ▸ Subgroup.one_mem _)
    have hr1 : ((z : ↥(B.S)) : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hdvd : orderOf (((z : ↥(B.S)) : G)) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hr1
    · exact h
  · -- and it does not lie in `E`
    intro hrE
    apply hzT
    rw [Subgroup.mem_subgroupOf]
    exact ⟨(Subgroup.mem_subgroupOf.mp hzS').1, hrE⟩

end Work.CORE4
