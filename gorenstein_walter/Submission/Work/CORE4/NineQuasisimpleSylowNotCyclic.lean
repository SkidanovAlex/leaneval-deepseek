import Mathlib
import Submission.Work.CORE4.Defs
import Submission.OddOrder.FeitThompson

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE4

/-- **A quasisimple subgroup has no cyclic Sylow `2`-subgroup.**

`E` is quasisimple, i.e. perfect (`⁅E,E⁆ = E`) with `E ⧸ Z(E)` simple; in particular `E` is
nontrivial and not solvable, so by the Feit–Thompson odd order result `OddOrder.feitThompson`
(import it in your file as `import Submission.OddOrder.FeitThompson`) `|E|` is even, and
`2 = (Nat.card ↥E).minFac`.  If a Sylow `2`-subgroup `P` of `↥E` were cyclic, Burnside's normal
`p`-complement result (Mathlib's `IsCyclic.isComplement'`) would give a normal complement `K` of
`P` in `↥E`: `K ⊔ P = ⊤`, `K ⊓ P = ⊥`, `Nat.card K = P.index` (odd, since `P` is Sylow), and
`↥E ⧸ K ≃* ↥P` (`Subgroup.IsComplement'.QuotientMulEquiv`) is cyclic, hence abelian, so
`⁅⊤,⊤⁆ ≤ K` (`Subgroup.commutator_le`); as `E` is perfect this gives `E ≤ K`, so `2 ∤ |E|` is
forced — contradicting `2 ∣ |E|`.

The same argument is carried out in `Submission/Work/CORE2B/isQuasisimple_four_dvd.lean`
(`Work.CORE2B.not_isCyclic_sylow_two_of_isQuasisimple`), but that module declares its own clashing
`Work.GW2.*` vocabulary and must NOT be imported here; read it for the transfer step
(`MonoidHom.transferSylow`, `IsCyclic.normalizer_le_centralizer`, `IsCyclic.isComplement'`,
`MonoidHom.not_dvd_card_ker_transferSylow`). -/
theorem NineQuasisimpleSylowNotCyclic {G : Type} [Group G] [Finite G]
    {E : Subgroup G} (hE : Work.GW2.IsQuasisimple E) (P : Sylow 2 ↥E) :
    ¬ IsCyclic ↥(P : Subgroup ↥E) := by
  intro hcyc
  obtain ⟨hcomm, hsimple⟩ := hE
  -- `↥E` is nontrivial: its central quotient is simple.
  have hN : Nontrivial ↥E := by
    by_contra hcon
    haveI : Subsingleton ↥E := not_nontrivial_iff_subsingleton.mp hcon
    haveI : Nontrivial (↥E ⧸ Subgroup.center ↥E) := hsimple.toNontrivial
    exact (not_subsingleton (↥E ⧸ Subgroup.center ↥E)) inferInstance
  -- `↥E` is perfect.
  haveI hperf : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hcomm
  -- Feit–Thompson rules out the odd order case.
  have h2dvd : 2 ∣ Nat.card ↥E := by
    by_contra h2
    have hodd : Odd (Nat.card ↥E) :=
      Nat.not_even_iff_odd.mp fun he => h2 (even_iff_two_dvd.mp he)
    haveI : Group.IsSolvable ↥E := OddOrder.feitThompson hodd
    exact Group.IsPerfect.not_isSolvable ↥E inferInstance
  have hp2 : (Nat.card ↥E).minFac = 2 := Nat.minFac_eq_two_iff _ |>.mpr h2dvd
  -- Burnside's transfer: `N(P) ≤ C(P)` for a cyclic Sylow at the smallest prime.
  have hle : Subgroup.normalizer (P : Set ↥E) ≤ Subgroup.centralizer (P : Set ↥E) :=
    IsCyclic.normalizer_le_centralizer hp2 hcyc
  set K : Subgroup ↥E := (MonoidHom.transferSylow P hle).ker with hKdef
  haveI hKnorm : K.Normal := by rw [hKdef]; exact MonoidHom.normal_ker _
  have hcomp : K.IsComplement' (P : Subgroup ↥E) :=
    MonoidHom.ker_transferSylow_isComplement' P hle
  -- `↥E ⧸ K` is a `2`-group (isomorphic to `P`).
  have hcard : Nat.card (↥E ⧸ K) = Nat.card ↥(P : Subgroup ↥E) := by
    rw [← Subgroup.index_eq_card K, hcomp.symm.index_eq_card]
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  haveI hpg : IsPGroup 2 (↥E ⧸ K) := IsPGroup.of_card (by rw [hcard, hk])
  haveI : Group.IsNilpotent (↥E ⧸ K) := IsPGroup.isNilpotent (p := 2) hpg
  haveI : Group.IsSolvable (↥E ⧸ K) := IsNilpotent.to_isSolvable
  haveI : Group.IsPerfect (↥E ⧸ K) := inferInstance
  -- A perfect solvable group is trivial, hence `K = ⊤`.
  have htriv : Subsingleton (↥E ⧸ K) := by
    by_contra hcon
    haveI : Nontrivial (↥E ⧸ K) := not_subsingleton_iff_nontrivial.mp hcon
    exact Group.IsPerfect.not_isSolvable (↥E ⧸ K) inferInstance
  have hKtop : K = ⊤ := QuotientGroup.subgroup_eq_top_of_subsingleton K htriv
  -- But `K` (the kernel of the transfer) has odd order.
  have hoddK : ¬ 2 ∣ Nat.card ↥K := by
    rw [hKdef]
    exact MonoidHom.not_dvd_card_ker_transferSylow P hle
  rw [hKtop, Subgroup.card_top] at hoddK
  exact hoddK h2dvd

end Work.CORE4
