import Mathlib
import Submission.Work.CORE2B.Defs
import Submission.OddOrder.FeitThompson

/-!
# CORE2B: `IsQuasisimple E` ⇒ `4 ∣ |E|`

A quasisimple subgroup `E` is **perfect** (`⁅E,E⁆ = E`) with **simple central quotient**
`E/Z(E)`.  We show that `4` divides its order:

* `E` is perfect, hence not solvable (a nontrivial perfect solvable group is trivial); by the
  Feit–Thompson theorem `|E|` is therefore even.
* If a Sylow `2`-subgroup `P` of `E` were **cyclic**, then `p = 2 = |E|.minFac` and
  `N(P) ≤ C(P)` for a cyclic Sylow at the smallest prime, so Burnside's normal `p`-complement
  theorem (`MonoidHom.ker_transferSylow_isComplement'`, available in Mathlib) exhibits a normal
  complement `K` of `P`.  Then `E ⧸ K` is a `2`-group, hence solvable, and it is perfect as a
  quotient of the perfect group `E`; so `E ⧸ K` is trivial, `K = ⊤`, and `K` has odd order —
  contradicting `2 ∣ |E|`.  Hence no Sylow `2`-subgroup of `E` is cyclic.
* A Sylow `2`-subgroup of a group whose order is divisible by `2` but not by `4` is cyclic (of
  order `2`), so the previous point gives `4 ∣ |E|`.

This is the fact used in Bender 1981 §2.7 step 1 (every normal subgroup of order divisible by
`4` contains `t`).
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

/-- **Feit–Thompson** in the `Work.GW2` vocabulary, discharged from the ported odd-order
library. -/
theorem feitThompsonProp_core2b : Work.GW2.FeitThompsonProp :=
  fun _ _ _ h => OddOrder.feitThompson h

/-- **A quasisimple subgroup has no cyclic Sylow `2`-subgroup.**
(`Work.GW2.QuasisimpleSylowProp`, proved here for the CORE2B copy of the vocabulary.)

`E` is perfect, so it is nontrivial and not solvable; Feit–Thompson makes `|E|` even.  If a
Sylow `2`-subgroup `P` of `E` were cyclic, then (as `2 = |E|.minFac`) Burnside's normal
`p`-complement theorem would produce a normal complement `K` of `P`; `E ⧸ K` would be a perfect
`2`-group, hence trivial, forcing `K = ⊤` of odd order — contradicting `2 ∣ |E|`. -/
theorem not_isCyclic_sylow_two_of_isQuasisimple {G : Type} [Group G] [Finite G]
    {E : Subgroup G} (h : Work.GW2.IsQuasisimple E) (P : Sylow 2 ↥E) :
    ¬ IsCyclic ↥(P : Subgroup ↥E) := by
  intro hcyc
  obtain ⟨hcomm, hsimple⟩ := h
  -- `E` is nontrivial: its central quotient is simple.
  have hN : Nontrivial ↥E := by
    by_contra hcon
    haveI : Subsingleton ↥E := not_nontrivial_iff_subsingleton.mp hcon
    haveI : Nontrivial (↥E ⧸ Subgroup.center ↥E) := hsimple.toNontrivial
    exact (not_subsingleton (↥E ⧸ Subgroup.center ↥E)) inferInstance
  -- `E` is perfect.
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
  -- `E ⧸ K` is a `2`-group (isomorphic to `P`).
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
  -- But `K` (kernel of the transfer) has odd order.
  have hoddK : ¬ 2 ∣ Nat.card ↥K := by
    rw [hKdef]
    exact MonoidHom.not_dvd_card_ker_transferSylow P hle
  rw [hKtop, Subgroup.card_top] at hoddK
  exact hoddK h2dvd

/-- A finite group with a non-cyclic Sylow `2`-subgroup has order divisible by `4`. -/
theorem four_dvd_card_of_not_isCyclic_sylow_two {G : Type} [Group G] [Finite G]
    (hnc : ∀ P : Sylow 2 G, ¬ IsCyclic ↥(P : Subgroup G)) : 4 ∣ Nat.card G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := G)
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  -- `2^k ∤ 2`, so `k ≥ 2`.
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hle : k ≤ 1 := by omega
    have hdvd : Nat.card ↥(P : Subgroup G) ∣ 2 := by
      rw [hk, show (2 : ℕ) = 2 ^ 1 from (pow_one 2).symm]
      exact Nat.pow_dvd_pow 2 hle
    exact hnc P (isCyclic_of_card_dvd_prime hdvd)
  have h4 : 4 ∣ Nat.card ↥(P : Subgroup G) := by
    have h4eq : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [hk, h4eq]
    exact ⟨2 ^ (k - 2), by rw [← pow_add]; congr 1; omega⟩
  exact h4.trans (Subgroup.card_subgroup_dvd_card _)

/-- **A quasisimple subgroup `E ≠ ⊥` has order divisible by `4`.** -/
theorem isQuasisimple_four_dvd {G : Type} [Group G] [Finite G] (E : Subgroup G)
    (h : Work.GW2.IsQuasisimple E) (hne : E ≠ ⊥) : 4 ∣ Nat.card E := by
  exact four_dvd_card_of_not_isCyclic_sylow_two
    (fun P => not_isCyclic_sylow_two_of_isQuasisimple h P)

end Work.CORE2B
