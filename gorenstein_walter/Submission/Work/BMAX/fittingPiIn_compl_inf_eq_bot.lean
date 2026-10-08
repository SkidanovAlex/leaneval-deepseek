/-
# Bender 1970, 1.7(i) ⟹ Bender 1981, Lemma 2.3(ii): `F_{π'}(B) ∩ A = 1`

The target of this file is the glue

`fittingPiIn (primesOf (fittingIn A))ᶜ B ⊓ A = ⊥`

from the prime-by-prime input

`∀ q prime, q ∉ π(F(A)) → O_q(B) ⊓ A = ⊥`  (`π(F(A)) = primesOf (fittingIn A)`),

which is exactly Bender 1970, 1.7(i) (`O_q(B) ∩ A = 1` for `q ∈ π(F(A))'`), the form in which
Bender 1981, Lemma 2.3(ii) quotes his 1970 paper.

The mathematics (Bender 1970, proof of 1.7): `F_{π'}(B) = O_{π'}(F(B))`, and `F(B)` is
nilpotent, hence the (internal, characteristic) direct product of its Sylow subgroups
`O_q(F(B)) = O_q(B)`.  So an element `x ∈ F_{π'}(B)` of prime order `q` has `q ∉ π(F(A))` and
lies in `O_q(B)`, hence — if in addition `x ∈ A` — in `O_q(B) ∩ A = 1`.

Formally the argument is Cauchy's theorem on the subgroup `M = F_{π'}(B) ∩ A`: if `M ≠ 1`, a
prime `q ∣ |M|` and an element `y ∈ M` of order `q` exist.  Then

* `q ∈ π'`:  `M ≤ F_{π'}(B)` and `F_π(K)` is a `π`-subgroup (`isPiSubgroup_fittingPiIn'`);
* `y ∈ O_q(B)`: `y ∈ F_{π'}(B) ≤ F(B)` and `y` generates a `q`-group
  (`pCoreIn_of_isPGroup_zpowers_of_mem_fittingIn`);
* `y ∈ A` by construction, so `y ∈ O_q(B) ∩ A = ⊥`, contradicting `orderOf y = q ≠ 1`.
-/
import Mathlib
import Submission.Work.BMAX.D17Defs
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.inf_fittingIn_le_pCoreIn_of_le_pCoreIn
import Submission.Work.DSTR.map_fittingPiIn_le

set_option linter.style.haveILetI false

namespace Work.BMAX

open Subgroup

/-! ## 1. `F_π(K)` is a `π`-subgroup

`F_π(K) = O_π(F(↥K))`, realized in the ambient group, is the image of a `π`-subgroup under the
two injective inclusions `↥(F(↥K)) → ↥K → G`, and injective maps preserve the order. -/

theorem isPiSubgroup_fittingPiIn' {G : Type} [Group G] [Finite G] (π : Set ℕ) (K : Subgroup G) :
    Subgroup.IsPiSubgroup π (Work.GW2.fittingPiIn π K) := by
  have h1 : Subgroup.IsPiSubgroup π (Work.GW2.piCore π ↥(Work.GW2.fitting ↥K)) :=
    Work.DSTR.FittingPiImg.isPiSubgroup_piCore π
  have h2 : Subgroup.IsPiSubgroup π
      ((Work.GW2.piCore π ↥(Work.GW2.fitting ↥K)).map (Work.GW2.fitting ↥K).subtype) :=
    Work.DSTR.FittingPiImg.isPiSubgroup_map (f := (Work.GW2.fitting ↥K).subtype) h1
  simpa only [Work.GW2.fittingPiIn, Work.GW2.fittingPi] using
    (Work.DSTR.FittingPiImg.isPiSubgroup_map (f := K.subtype) h2)

/-! ## 2. The glue -/

theorem fittingPiIn_compl_inf_eq_bot {G : Type} [Group G] [Finite G] (A B : Subgroup G)
    (hcore : ∀ q : ℕ, q.Prime → q ∉ Work.GW2.primesOf (Work.GW2.fittingIn A) →
      Work.GW2.pCoreIn q B ⊓ A = ⊥) :
    Work.GW2.fittingPiIn (Work.GW2.primesOf (Work.GW2.fittingIn A))ᶜ B ⊓ A = ⊥ := by
  classical
  set π : Set ℕ := Work.GW2.primesOf (Work.GW2.fittingIn A) with hπ
  set M : Subgroup G := Work.GW2.fittingPiIn πᶜ B ⊓ A with hM
  by_contra hne
  -- `M ≠ ⊥`, so some prime `q` divides `|M|`, and `M` has an element of order `q`
  have hcard : Nat.card ↥M ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hcard
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) q hqdvd
  have hyMem : ((y : ↥M) : G) ∈ Work.GW2.fittingPiIn πᶜ B ⊓ A := y.2
  obtain ⟨hyF, hyA⟩ := Subgroup.mem_inf.mp hyMem
  have hyordG : orderOf ((y : ↥M) : G) = q := (Subgroup.orderOf_coe y).trans hyord
  -- `q` lies in the complement of `π`: `F_{π'}(B)` is a `π'`-subgroup and `q ∣ |M| ∣ |F_{π'}(B)|`
  have hqdvd' : q ∣ Nat.card ↥(Work.GW2.fittingPiIn πᶜ B) :=
    hqdvd.trans (Subgroup.card_dvd_of_le (show M ≤ Work.GW2.fittingPiIn πᶜ B from inf_le_left))
  have hqmem : q ∈ (Nat.card ↥(Work.GW2.fittingPiIn πᶜ B)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, hqdvd', Nat.card_pos.ne'⟩
  have hqpiC : q ∈ πᶜ := isPiSubgroup_fittingPiIn' πᶜ B q hqmem
  have hqpi : q ∉ π := hqpiC
  -- `y` lies in `O_q(B)`: it is a `q`-element of the Fitting subgroup of `B`
  have hyFB : ((y : ↥M) : G) ∈ Work.GW2.fittingIn B :=
    Work.GW2.fittingPiIn_le_fittingIn πᶜ B hyF
  have hyq : IsPGroup q ↥(Subgroup.zpowers ((y : ↥M) : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyordG, pow_one])
  have hpc : ((y : ↥M) : G) ∈ Work.GW2.pCoreIn q B :=
    pCoreIn_of_isPGroup_zpowers_of_mem_fittingIn B q hyFB hyq
  -- hence `y ∈ O_q(B) ⊓ A = ⊥`, contradicting `orderOf y = q ≠ 1`
  have hbot : ((y : ↥M) : G) ∈ (⊥ : Subgroup G) := by
    rw [← hcore q hq hqpi]
    exact Subgroup.mem_inf.mpr ⟨hpc, hyA⟩
  rw [Subgroup.mem_bot] at hbot
  exact hq.ne_one (by rw [← hyordG, hbot, orderOf_one])

end Work.BMAX
