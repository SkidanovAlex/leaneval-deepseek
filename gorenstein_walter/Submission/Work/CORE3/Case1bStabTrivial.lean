import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.InvSetVUSingleton
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.Case1bFalse
import Submission.Work.CORE3.exists_mul_of_mem_sup_of_normal
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE3.J4.J4CosetStep
import Submission.Work.CORE3.BenderSevenU3
import Submission.Work.CORE3.CardInfConjSubOfThree
import Submission.Work.CORE3.CosetInvCountNeSixOf

/-!
# CORE3: the stabilizer of a `b₄`-coset in `KV = VU` is trivial (B81 §3, p. 224)

Bender 1981, *Finite groups with dihedral Sylow 2-subgroups*, §3, pp. 223–224, Case (1)
subcase (1b): with `V = O₂(Ĥ)` a four-group, `U = O(Ĥ) = O(H)`, `VU = V × U` and `|Ĥ : VU| = 6`,
Bender shows that `KV = V·K = VU` acts **fixed-point-freely** on the set of cosets `Ĥg` that
contribute to `b₄`; this is what forces `|KV| = 12 ∣ b₄`.

The elementary form of that statement, for a single coset `Ĥy` carrying exactly four involutions
(`y ∈ J₄`), is: for every `a ∈ VU`, `a ≠ 1`, the conjugate `y * a * y` is **not** in `Ĥ`.  Indeed
an `a ∈ VU ≤ Ĥ` fixes the right coset `Ĥy` under the conjugation action of `Ĥ` on its cosets
exactly when `y * a * y ∈ Ĥ`, so the statement says that the stabilizer of `Ĥy` in `VU` is
trivial — equivalently `VU ⊓ (Ĥ ⊓ Ĥ^y) = ⊥`.

This module contains the *assembly* of that statement from Bender's step (7) for the `J₄`-coset
(`Submission/Work/CORE3/J4Structure.lean`: `|U| = 3` and `|Ĥ ⊓ Ĥ^y| = 6`), the argument being
reproduced in `stabTrivial_of_card_data` below.  Write `V = O₂(Ĥ) = pCoreIn 2 B.Hhat`,
`U = O(Ĥ) = B.U` and `D = Ĥ ⊓ Ĥ^y`.

* if `a ∈ VU ⊓ D`, write `VU = V × U ∋ a = v·u`; then `a ^ 3 = v` (as `|U| = 3` and `v` has
  order `2`), so either `v ∈ V# ⊓ D`, or `v = 1` and `u ∈ U ⊓ D`;
* in the second case `U ⊓ D` has order `3` (it contains `⟨u⟩` of order `3` and divides `3`),
  so `U ≤ D`; then `U^y` is a second subgroup of order `3` of the group `D` of order `6`, hence
  `U^y = U` (a group of order `6` has a unique subgroup of order `3`), i.e. `y ∈ N_G(U)`; but
  `U = O(Ĥ) ⊴ Ĥ` has order `3`, so `Ĥ` is a maximal subgroup normalized by `U ≠ ⊥`, whence
  `N_G(U) = Ĥ`, so `y ∈ Ĥ`, contradiction;
* in the first case `N := V ⊓ D` is normal in `D` (as `V ⊴ Ĥ`) of index `3`, so the third power
  of every element of `D` lies in `N`; applied to `h := y*v*y ∈ D` (with `h² = 1`) this gives
  `h ∈ N ⊆ V`, so `h ∈ V#`.  As `N(V) = Ĥ` is transitive on `V#` (`I.T.fus`), there is `g ∈ Ĥ`
  with `g*v*g⁻¹ = h`; then `g⁻¹*y` centralizes the involution `v ∈ V#`, so (`Work.CORE3.claimA`)
  `g⁻¹*y ∈ Ĥ` and hence `y ∈ Ĥ`, contradiction.
-/

namespace Work.CORE3

open Subgroup
open Work.GW2

set_option linter.unusedVariables false

/-! ## Elementary facts about groups of order `6` -/

/-- The trivial subgroup is the only subgroup of order `1`. -/
theorem eq_bot_of_card_eq_one {G : Type*} [Group G] {H : Subgroup G} (h : Nat.card ↥H = 1) :
    H = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have hdvd : Nat.card ↥(Subgroup.zpowers x) ∣ Nat.card ↥H :=
    Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx)
  rw [h] at hdvd
  rw [Nat.card_zpowers] at hdvd
  have hone : orderOf x = 1 := Nat.dvd_one.mp hdvd
  simpa using (orderOf_eq_one_iff.mp hone)

/-- A group of order `6` has at most one subgroup of order `3`: if `A ⊓ B = ⊥` then the
multiplication map `A × B → Q` is injective and would give `9 ≤ 6`. -/
theorem eq_of_card_eq_three_of_card_six {Q : Type*} [Group Q] [Finite Q]
    (hQ : Nat.card Q = 6) {A B : Subgroup Q} (hA : Nat.card ↥A = 3) (hB : Nat.card ↥B = 3) :
    A = B := by
  by_contra hne
  have hdvd : Nat.card ↥(A ⊓ B) ∣ 3 := by
    have h := Subgroup.card_dvd_of_le (H := A ⊓ B) (K := A) inf_le_left
    rwa [hA] at h
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · -- the multiplication map `A × B → Q` is injective
    have hbot : A ⊓ B = ⊥ := eq_bot_of_card_eq_one h1
    have hinj : Function.Injective (fun p : ↥A × ↥B => (p.1 : Q) * (p.2 : Q)) := by
      rintro ⟨a1, b1⟩ ⟨a2, b2⟩ heq
      change (a1 : Q) * (b1 : Q) = (a2 : Q) * (b2 : Q) at heq
      have h0 : (a2 : Q)⁻¹ * (a1 : Q) * (b1 : Q) = (b2 : Q) := by
        calc (a2 : Q)⁻¹ * (a1 : Q) * (b1 : Q) = (a2 : Q)⁻¹ * ((a1 : Q) * (b1 : Q)) := by group
          _ = (a2 : Q)⁻¹ * ((a2 : Q) * (b2 : Q)) := by rw [heq]
          _ = (b2 : Q) := by group
      have h : (a2 : Q)⁻¹ * (a1 : Q) = (b2 : Q) * (b1 : Q)⁻¹ := by
        calc (a2 : Q)⁻¹ * (a1 : Q) = (a2 : Q)⁻¹ * (a1 : Q) * (b1 : Q) * (b1 : Q)⁻¹ := by group
          _ = (b2 : Q) * (b1 : Q)⁻¹ := by rw [h0]
      have hmem : (a2 : Q)⁻¹ * a1 ∈ A ⊓ B :=
        ⟨A.mul_mem (A.inv_mem a2.2) a1.2, h ▸ B.mul_mem b2.2 (B.inv_mem b1.2)⟩
      rw [hbot] at hmem
      have h1' : (a2 : Q)⁻¹ * a1 = 1 := by simpa using hmem
      have h2' : (b2 : Q) * (b1 : Q)⁻¹ = 1 := by rw [← h, h1']
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · exact (inv_mul_eq_one.mp h1').symm
      · exact (mul_inv_eq_one.mp h2').symm
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hA, hB, hQ] at hle
    omega
  · -- `A ⊓ B = A`, hence `A ≤ B` and `A = B`
    have hAeq : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hA])
    have hle : A ≤ B := by rw [← hAeq]; exact inf_le_right
    exact absurd (Subgroup.eq_of_le_of_card_ge hle (by rw [hA, hB])) hne

/-- If `N ≤ K` is a normal subgroup of the finite group `K` with `|K : N| = 3`, then `x ^ 3 ∈ N`
for every `x ∈ K`. -/
theorem pow_three_mem_of_relIndex_three {G : Type*} [Group G] [Finite G] {N K : Subgroup G}
    [hN : (N.subgroupOf K).Normal] (hidx : N.relIndex K = 3) {x : G} (hx : x ∈ K) :
    x ^ 3 ∈ N := by
  have hcard : Nat.card (↥K ⧸ N.subgroupOf K) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hdvd : orderOf (QuotientGroup.mk' (N.subgroupOf K) (⟨x, hx⟩ : ↥K)) ∣ 3 := by
    rw [← hcard]; exact orderOf_dvd_natCard _
  have h1 : (QuotientGroup.mk' (N.subgroupOf K) (⟨x, hx⟩ : ↥K)) ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp hdvd
  have h2 : QuotientGroup.mk' (N.subgroupOf K) ((⟨x, hx⟩ : ↥K) ^ 3) = 1 := by
    rw [map_pow]; exact h1
  have h3 : ((⟨x, hx⟩ : ↥K) ^ 3) ∈ N.subgroupOf K :=
    (QuotientGroup.eq_one_iff ((⟨x, hx⟩ : ↥K) ^ 3)).mp h2
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at h3
  simpa using h3

/-- For an involution `y` (with `y⁻¹ = y`): `y * (y * x * y) * y = x`. -/
theorem mul_conj_self {G : Type} [Group G] {y x : G} (hy : y * y = 1) :
    y * (y * x * y) * y = x := by
  rw [show y * (y * x * y) * y = (y * y) * x * (y * y) by group, hy, one_mul, mul_one]

/-- A group of order `6` has a unique subgroup of order `3`, in `D`-relative form. -/
theorem eq_of_card_eq_three_of_card_six_of_le {G : Type*} [Group G] [Finite G]
    {Dd : Subgroup G} (hD : Nat.card ↥Dd = 6) {A Bb : Subgroup G} (hA : A ≤ Dd)
    (hB : Bb ≤ Dd) (hcardA : Nat.card ↥A = 3) (hcardB : Nat.card ↥Bb = 3) : A = Bb := by
  have hEq : A.subgroupOf Dd = Bb.subgroupOf Dd :=
    eq_of_card_eq_three_of_card_six (Q := ↥Dd) hD
      (A := A.subgroupOf Dd) (B := Bb.subgroupOf Dd)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hcardA])
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv, hcardB])
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have hmem : (⟨x, hA hx⟩ : ↥Dd) ∈ A.subgroupOf Dd := Subgroup.mem_subgroupOf.mpr hx
    rw [hEq] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  · have hmem : (⟨x, hB hx⟩ : ↥Dd) ∈ Bb.subgroupOf Dd := Subgroup.mem_subgroupOf.mpr hx
    rw [← hEq] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem

/-! ## `conjSub` helpers -/

/-- For an involution `y`: `y * (y * x * y⁻¹) * y⁻¹ = x`. -/
theorem mul_conj_self' {G : Type} [Group G] {y x : G} (hy : y * y = 1) :
    y * (y * x * y⁻¹) * y⁻¹ = x := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  rw [hyinv, show y * (y * x * y) * y = (y * y) * x * (y * y) by group, hy, one_mul, mul_one]

/-- For an involution `y` and a subgroup `K`, membership in `conjSub y K = y K y⁻¹` is the
elementwise condition. -/
theorem mem_conjSub_iff {G : Type} [Group G] {y : G} (hy : y * y = 1) (K : Subgroup G) (x : G) :
    x ∈ Work.GW2.conjSub y K ↔ y * x * y⁻¹ ∈ K := by
  constructor
  · intro hx
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
    have hkx' : y * k * y⁻¹ = x := hkx
    rw [← hkx']
    exact mul_conj_self' hy ▸ hk
  · intro hx
    exact Subgroup.mem_map.mpr ⟨y * x * y⁻¹, hx, mul_conj_self' hy⟩

/-- `conjSub y (conjSub y K) = K` for an involution `y`. -/
theorem conjSub_conjSub_self_of_sq_one {G : Type} [Group G] {y : G} (hy : y * y = 1)
    (K : Subgroup G) : Work.GW2.conjSub y (Work.GW2.conjSub y K) = K := by
  show (K.map (MulAut.conj y).toMonoidHom).map (MulAut.conj y).toMonoidHom = K
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj y).toMonoidHom.comp (MulAut.conj y).toMonoidHom =
      MonoidHom.id G := by
    ext x
    change y * (y * x * y⁻¹) * y⁻¹ = x
    exact mul_conj_self' hy
  rw [hcomp]
  exact Subgroup.map_id K

/-! ## The assembly -/

/-- **Assembly.**  Suppose Bender's step (7) for the `J₄`-coset `Ĥy` holds, i.e. `|U| = 3` and
`|Ĥ ⊓ Ĥ^y| = 6`.  Then the stabilizer of `Ĥy` in `VU = O₂(Ĥ)·O(Ĥ)` is trivial: for every
`a ∈ VU`, `a ≠ 1`, one has `y * a * y ∉ Ĥ`. -/
theorem stabTrivial_of_card_data {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {y a : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (hU3 : Nat.card B.U = 3)
    (hD6 : Nat.card ↥(B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) = 6)
    (ha : a ∈ Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) (ha1 : a ≠ 1) :
    y * a * y ∉ B.Hhat := by
  classical
  intro hconj
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup G := hBc.simple
  have hy1 : y * y = 1 := by
    have h2 : y ^ 2 = 1 := by rw [← hy2]; exact pow_orderOf_eq_one y
    simpa [pow_two] using h2
  have h26 := I.h26 G I.T.ft hBc B
  -- ## structural facts about `V = O₂(Ĥ)`, `U = O(Ĥ)`
  have hV_le_S : Work.GW2.pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) := by
    rw [← h26.2.1]; exact inf_le_left
  have hV_le_Hhat : Work.GW2.pCoreIn 2 B.Hhat ≤ B.Hhat :=
    le_trans hV_le_S (le_trans (Work.CORE2A.bSetup_S_le_H B) B.H_le_Hhat)
  have hU_le_Hhat : B.U ≤ B.Hhat := Work.CORE2A.thm26Concl_U_le_Hhat h26
  have hV_cent : Work.GW2.pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← h26.2.1]; exact inf_le_right
  have hVnormal : B.Hhat ≤ Subgroup.normalizer (Work.GW2.pCoreIn 2 B.Hhat : Set G) :=
    le_of_eq (_root_.Work.CORE3.NormalizerPcoreEqHhat G hBc B D.four).symm
  have hVnorm : ∀ s ∈ B.Hhat, ∀ v ∈ Work.GW2.pCoreIn 2 B.Hhat, s * v * s⁻¹ ∈
      Work.GW2.pCoreIn 2 B.Hhat := by
    intro s hs v hv
    exact (Subgroup.mem_normalizer_iff.mp (hVnormal hs) v).mp hv
  have hUnormal : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
    rw [← h26.1]
    exact _root_.Work.CORE3.le_normalizer_map_subtype_of_normal' (K := B.Hhat)
      (N := Work.GW2.oddCore ↥B.Hhat) inferInstance
  have hUnorm : ∀ s ∈ B.Hhat, ∀ u ∈ B.U, s * u * s⁻¹ ∈ B.U := by
    intro s hs u hu
    exact (Subgroup.mem_normalizer_iff.mp (hUnormal hs) u).mp hu
  have hDs_le_Hhat : B.Hhat ⊓ Work.GW2.conjSub y B.Hhat ≤ B.Hhat := inf_le_left
  -- `D = Ĥ ⊓ Ĥ^y` is `y`-invariant
  have hconjDs : Work.GW2.conjSub y (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) =
      B.Hhat ⊓ Work.GW2.conjSub y B.Hhat := by
    show (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat).map (MulAut.conj y).toMonoidHom =
        B.Hhat ⊓ Work.GW2.conjSub y B.Hhat
    rw [Subgroup.map_inf B.Hhat (Work.GW2.conjSub y B.Hhat) (MulAut.conj y).toMonoidHom
      (MulAut.conj y).injective]
    have h2 : (Work.GW2.conjSub y B.Hhat).map (MulAut.conj y).toMonoidHom = B.Hhat :=
      conjSub_conjSub_self_of_sq_one hy1 B.Hhat
    rw [h2]
    exact inf_comm _ _
  -- `a ∈ D`
  have ha_Hhat : a ∈ B.Hhat := sup_le hV_le_Hhat hU_le_Hhat ha
  have ha_conj : y * a * y⁻¹ ∈ B.Hhat := by
    rw [show y⁻¹ = y from inv_eq_of_mul_eq_one_right hy1]; exact hconj
  have ha_Ds : a ∈ B.Hhat ⊓ Work.GW2.conjSub y B.Hhat :=
    ⟨ha_Hhat, (mem_conjSub_iff hy1 B.Hhat a).mpr ha_conj⟩
  -- ## decompose `a = v * u`
  obtain ⟨v, hv, u, hu, haeq⟩ :=
    _root_.Work.CORE3.exists_mul_of_mem_sup_of_normal (S := B.Hhat) hV_le_Hhat hU_le_Hhat
      hVnorm hUnorm a ha
  have hv_sq : v * v = 1 := by simpa [pow_two] using D.four.2 v hv
  have hu3 : u ^ 3 = 1 := by
    have hdvd : orderOf u ∣ Nat.card ↥B.U := Subgroup.orderOf_dvd_natCard B.U hu
    rw [hU3] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hcomm : Commute v u := ((Subgroup.mem_centralizer_iff.mp (hV_cent hv)) u hu).symm
  have hcube : a ^ 3 = v := by
    rw [haeq, hcomm.mul_pow]
    have hv3 : v ^ 3 = v := by rw [pow_succ, pow_two, hv_sq, one_mul]
    rw [hv3, hu3, mul_one]
  have hv_Ds : v ∈ B.Hhat ⊓ Work.GW2.conjSub y B.Hhat := by
    rw [← hcube]; exact (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat).pow_mem ha_Ds 3
  -- ## auxiliary facts
  have hUbot : B.U ≠ ⊥ := by
    intro h
    have h1c : Nat.card ↥B.U = 1 := by rw [h]; exact Subgroup.card_bot
    omega
  rcases eq_or_ne v 1 with hv1 | hv1
  · -- ## case `v = 1`: then `a = u ∈ U`
    have hua : u = a := by rw [haeq, hv1, one_mul]
    have hu_Ds : u ∈ B.Hhat ⊓ Work.GW2.conjSub y B.Hhat := hua ▸ ha_Ds
    have hu1 : u ≠ 1 := by intro h; exact ha1 (by rw [haeq, hv1, h, mul_one])
    have hu_mem : u ∈ B.U ⊓ (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) := ⟨hu, hu_Ds⟩
    have hu_order : orderOf u = 3 := by
      have hdvd : orderOf u ∣ 3 := by
        rw [← hU3]; exact Subgroup.orderOf_dvd_natCard B.U hu
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hu1
      · exact h
    have hUint_card : Nat.card ↥(B.U ⊓ (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)) = 3 := by
      have hdvd1 : Nat.card ↥(B.U ⊓ (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)) ∣ 3 := by
        have h := Subgroup.card_dvd_of_le (H := B.U ⊓ (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat))
          (K := B.U) inf_le_left
        rwa [hU3] at h
      have hdvd2 : 3 ∣ Nat.card ↥(B.U ⊓ (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)) := by
        have h := Subgroup.card_dvd_of_le (H := Subgroup.zpowers u)
          (K := B.U ⊓ (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)) (Subgroup.zpowers_le.mpr hu_mem)
        rwa [Nat.card_zpowers, hu_order] at h
      exact (Nat.dvd_antisymm hdvd2 hdvd1).symm
    have hUle : B.U ≤ B.Hhat ⊓ Work.GW2.conjSub y B.Hhat := by
      have heq : B.U ⊓ (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) = B.U :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hUint_card, hU3])
      rw [← heq]; exact inf_le_right
    -- `U^y` is a subgroup of `D` of order `3`, hence equals `U`
    have hcardUy : Nat.card ↥(Work.GW2.conjSub y B.U) = 3 := by
      show Nat.card ↥(B.U.map (MulAut.conj y).toMonoidHom) = 3
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hU3]
    have hconjU_le : Work.GW2.conjSub y B.U ≤ B.Hhat ⊓ Work.GW2.conjSub y B.Hhat := by
      rw [← hconjDs]
      exact Subgroup.map_mono hUle
    have hUy_eq : Work.GW2.conjSub y B.U = B.U :=
      eq_of_card_eq_three_of_card_six_of_le hD6 hconjU_le hUle hcardUy hU3
    -- hence `y ∈ N_G(U) = Ĥ`
    have hNU : Subgroup.normalizer (B.U : Set G) = B.Hhat :=
      _root_.Work.CORE3.normalizer_eq_of_isCoatom B.Hhat B.Hhat_coatom B.U hU_le_Hhat
        hUnormal hUbot
    have hyN : y ∈ Subgroup.normalizer (B.U : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have hz' : y * z * y⁻¹ ∈ Work.GW2.conjSub y B.U := by
          rw [mem_conjSub_iff hy1 B.U (y * z * y⁻¹), mul_conj_self' hy1]
          exact hz
        rwa [hUy_eq] at hz'
      · intro hz
        have hz' : z ∈ Work.GW2.conjSub y B.U := by
          rw [mem_conjSub_iff hy1 B.U z]
          exact hz
        rwa [hUy_eq] at hz'
    exact hyH (by rw [← hNU]; exact hyN)
  · -- ## case `v ≠ 1`: `v ∈ V# ⊓ D`
    have hvint_mem : v ∈ Work.GW2.pCoreIn 2 B.Hhat ⊓ (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) :=
      ⟨hv, hv_Ds⟩
    have hv_order : orderOf v = 2 := (orderOf_eq_two_iff_mul_self v).mpr ⟨hv_sq, hv1⟩
    have hVint_card : Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat ⊓
        (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)) = 2 := by
      have hdvd1 : Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat ⊓
          (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)) ∣ 2 := by
        have h1' := Subgroup.card_dvd_of_le (H := Work.GW2.pCoreIn 2 B.Hhat ⊓
          (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)) (K := Work.GW2.pCoreIn 2 B.Hhat) inf_le_left
        have h2' := Subgroup.card_dvd_of_le (H := Work.GW2.pCoreIn 2 B.Hhat ⊓
          (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat))
          (K := B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) inf_le_right
        rw [D.four.1] at h1'
        rw [hD6] at h2'
        exact Nat.dvd_gcd h1' h2'
      have hdvd2 : 2 ∣ Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat ⊓
          (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)) := by
        have h := Subgroup.card_dvd_of_le (H := Subgroup.zpowers v) (K := Work.GW2.pCoreIn 2 B.Hhat ⊓
          (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)) (Subgroup.zpowers_le.mpr hvint_mem)
        rwa [Nat.card_zpowers, hv_order] at h
      exact (Nat.dvd_antisymm hdvd2 hdvd1).symm
    -- `h := y*v*y ∈ D` is an involution
    have hh_Hhat : y * v * y ∈ B.Hhat := by
      obtain ⟨k, hk, hkv⟩ := Subgroup.mem_map.mp hv_Ds.2
      have hkv' : y * k * y⁻¹ = v := hkv
      rw [show y⁻¹ = y from inv_eq_of_mul_eq_one_right hy1] at hkv'
      rw [← hkv']
      rw [mul_conj_self hy1]; exact hk
    have hh_conj : y * v * y ∈ Work.GW2.conjSub y B.Hhat := by
      rw [mem_conjSub_iff hy1, show y⁻¹ = y from inv_eq_of_mul_eq_one_right hy1]
      rw [mul_conj_self hy1]
      exact hV_le_Hhat hv
    have hh_Ds : y * v * y ∈ B.Hhat ⊓ Work.GW2.conjSub y B.Hhat := ⟨hh_Hhat, hh_conj⟩
    have hh_sq : (y * v * y) * (y * v * y) = 1 := by
      have h1 : (y * v * y) * (y * v * y) = y * (v * (y * (y * (v * y)))) := by group
      rw [h1, ← mul_assoc y y (v * y), hy1, one_mul, ← mul_assoc v v y, hv_sq, one_mul, hy1]
    have hh_ne_one : y * v * y ≠ 1 := by
      intro h
      have h' := congrArg (fun t => y * t * y) h
      rw [mul_conj_self hy1, mul_one, hy1] at h'
      exact hv1 h'
    have hh_ne_v : y * v * y ≠ v := by
      intro h
      have hcomm' : y * v = v * y := by
        have h3 := congrArg (fun t => t * y) h
        simpa [mul_assoc, hy1] using h3
      have hyC : y ∈ Subgroup.centralizer ({v} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact hcomm'.symm
      exact hyH (_root_.Work.CORE3.claimA G hBc B I.T.fus h26 D.four hv hv1 hyC)
    -- `N := V ⊓ D` is normal in `D` with relative index `3`
    have hN_sub : Work.GW2.pCoreIn 2 B.Hhat ⊓ (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) ≤
        B.Hhat ⊓ Work.GW2.conjSub y B.Hhat := inf_le_right
    have hN_normal : ((Work.GW2.pCoreIn 2 B.Hhat ⊓
        (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)).subgroupOf
        (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hN_sub]
      intro z k hz hk
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hVnormal (hDs_le_Hhat hk)) z).mp hz.1,
        (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat).mul_mem
          ((B.Hhat ⊓ Work.GW2.conjSub y B.Hhat).mul_mem hk hz.2)
          ((B.Hhat ⊓ Work.GW2.conjSub y B.Hhat).inv_mem hk)⟩
    have hN_rel : (Work.GW2.pCoreIn 2 B.Hhat ⊓
        (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)).relIndex
        (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) = 3 := by
      have hmul := Subgroup.relIndex_mul_card (H := Work.GW2.pCoreIn 2 B.Hhat ⊓
        (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)) (K := B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)
      have hinf : (Work.GW2.pCoreIn 2 B.Hhat ⊓ (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)) ⊓
          (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) =
          Work.GW2.pCoreIn 2 B.Hhat ⊓ (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) :=
        inf_eq_left.mpr hN_sub
      rw [hinf, hVint_card, hD6] at hmul
      omega
    have hh_cube : (y * v * y) ^ 3 = y * v * y := by
      rw [pow_succ, pow_two, hh_sq, one_mul]
    have hh_mem : y * v * y ∈ Work.GW2.pCoreIn 2 B.Hhat ⊓
        (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) := by
      rw [← hh_cube]
      exact pow_three_mem_of_relIndex_three (N := Work.GW2.pCoreIn 2 B.Hhat ⊓
        (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)) (K := B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)
        hN_rel hh_Ds
    have hh_V : y * v * y ∈ Work.GW2.pCoreIn 2 B.Hhat := hh_mem.1
    -- `h` is conjugate to `v` inside `N(V) = Ĥ`, and `g⁻¹ * y` centralizes `v`
    have hno2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
      intro N hN h2
      haveI := hN
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
      · have hcard : Nat.card G = 2 := by
          rw [← Subgroup.index_bot, ← hb]; exact h2
        obtain ⟨x1, x2, hx12⟩ := hBc.nonab
        exact hx12 (by
          -- in a group of cardinality `2` all elements commute (local copy of
          -- `Work.CORE3.Work.CORE3.commute_of_card_two` from `Case1bFive.lean`, which this
          -- module cannot import without a cycle)
          have h2 : ∀ c : G, c * c = 1 := by
            intro c
            have hdvd : orderOf c ∣ 2 := by
              simpa [hcard] using orderOf_dvd_natCard c
            have h3 : c ^ orderOf c = 1 := pow_orderOf_eq_one c
            rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
            · rw [h1, pow_one] at h3
              rw [h3, one_mul]
            · rw [h1] at h3
              simpa [pow_two] using h3
          calc x1 * x2 = (x1 * x2)⁻¹ := (inv_eq_of_mul_eq_one_right (h2 (x1 * x2))).symm
            _ = x2⁻¹ * x1⁻¹ := mul_inv_rev x1 x2
            _ = x2 * x1 := by
                  rw [inv_eq_of_mul_eq_one_right (h2 x2), inv_eq_of_mul_eq_one_right (h2 x1)])
      · rw [ht, Subgroup.index_top] at h2
        exact absurd h2 (by norm_num)
    obtain ⟨n, hn2, hdih⟩ := _root_.Work.CORE3.SylowDihedral G hBc B
    obtain ⟨g, hg, hgt⟩ := (I.T.fus G B.S n hn2 hdih hno2).2 (Work.GW2.pCoreIn 2 B.Hhat)
      D.four v hv (y * v * y) hh_V hv1 hh_ne_one
    have hgH : g ∈ B.Hhat := by
      rw [← _root_.Work.CORE3.NormalizerPcoreEqHhat G hBc B D.four]; exact hg
    have hgz : (g⁻¹ * y) * v * (g⁻¹ * y)⁻¹ = v := by
      have hgt' : g * v * g⁻¹ = y * v * y := hgt
      have hginv : g⁻¹ * (y * v * y) * g = v := by
        have h := congrArg (fun t => g⁻¹ * t * g) hgt'
        simpa [mul_assoc, hy1, inv_mul_cancel, mul_inv_cancel] using h.symm
      calc (g⁻¹ * y) * v * (g⁻¹ * y)⁻¹ = g⁻¹ * y * v * y⁻¹ * g := by group
        _ = g⁻¹ * y * v * y * g := by
          rw [show y⁻¹ = y from inv_eq_of_mul_eq_one_right hy1]
        _ = g⁻¹ * (y * v * y) * g := by group
        _ = v := hginv
    have hzC : g⁻¹ * y ∈ Subgroup.centralizer ({v} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      have h' : (g⁻¹ * y) * v = v * (g⁻¹ * y) := by
        have h3 := congrArg (fun t => t * (g⁻¹ * y)) hgz
        simpa [mul_assoc] using h3
      exact h'.symm
    have hzH : g⁻¹ * y ∈ B.Hhat :=
      _root_.Work.CORE3.claimA G hBc B I.T.fus h26 D.four hv hv1 hzC
    refine hyH ?_
    have : y = g * (g⁻¹ * y) := by group
    rw [this]; exact B.Hhat.mul_mem hgH hzH

/-- B81 §3, p. 224: the fixed-point-free action of `KV = VU = O₂(Ĥ)·O(Ĥ)` on the `b₄`-cosets,
in the elementary form of a trivial stabilizer: for an involution `y ∉ Ĥ` whose coset `yĤ`
carries exactly four involutions (`y ∈ J₄`) and every `a ∈ VU = O₂(Ĥ)·O(Ĥ) = pCoreIn 2 B.Hhat ⊔ B.U`
with `a ≠ 1`, the conjugate `y * a * y` is *not* in `Ĥ`.  Equivalently the stabilizer of the
coset `yĤ` under the conjugation action of `VU` is trivial, i.e. `VU ⊓ (Ĥ ⊓ Ĥ^y) = ⊥`.
The `V`-part (`v ∈ O₂(Ĥ)`) follows from Bender (5); the `U`-part is the content of Bender (7). -/
theorem Case1bStabTrivial {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {y a : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (hy4 : Work.GW2.cosetInvCount B.Hhat y = 4)
    (ha : a ∈ Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) (ha1 : a ≠ 1) :
    y * a * y ∉ B.Hhat := by
  classical
  -- Bender's (6)/(7) data for the `J₄`-coset: an involution `z = h * y` inverting an odd `X`
  -- together with Bender's `N_Ĥ(X)`-witness `s ∈ Ĥ`.
  obtain ⟨z, hz2, ⟨h, hhH, hzy⟩, X, hXle, hXne, hXodd, hXinv, hCeven, hNeven,
    ⟨s, hsH, hs2, hsX⟩⟩ :=
    Work.CORE3.J4.J4CosetStep (G := G) I hBc B h1 D hy2 hyH hy4
  have hzH : z ∉ B.Hhat := by
    intro hcon
    apply hyH
    have h1' : h⁻¹ * z ∈ B.Hhat := B.Hhat.mul_mem (B.Hhat.inv_mem hhH) hcon
    rw [hzy] at h1'
    simpa using h1'
  -- the coset count of `z`: `z = h * y` with `h ∈ Ĥ`, and the count is invariant under
  -- right multiplication by `Ĥ` (`Work.CORE3.ncard_invSetIn_mul_eq`)
  have hy_sq : y * y = 1 := ((orderOf_eq_two_iff_mul_self y).mp hy2).1
  have hz_sq : z * z = 1 := ((orderOf_eq_two_iff_mul_self z).mp hz2).1
  have hyz_sq : (h * y) * (h * y) = 1 := by rw [← hzy]; exact hz_sq
  have hzH' : h * y ∉ B.Hhat := hzy ▸ hzH
  have hz4 : Work.GW2.cosetInvCount B.Hhat z = 4 := by
    have hmul : (Work.CORE3.invSetIn B.Hhat (h * y)).ncard =
        (Work.CORE3.invSetIn B.Hhat y).ncard :=
      Work.CORE3.ncard_invSetIn_mul_eq B.Hhat hhH hy_sq hyz_sq
    rw [hzy, ← Work.CORE3.ncard_invSetIn_eq_cosetInvCount B.Hhat (h * y) hyz_sq hzH',
      hmul, Work.CORE3.ncard_invSetIn_eq_cosetInvCount B.Hhat y hy_sq hyH, hy4]
  -- Bender (7), first half: `|U| = 3`
  have hU3 : Nat.card B.U = 3 :=
    BenderSevenU3 G I hBc B h1 D hz2 hzH X hXle hXne hXodd hXinv hCeven hsH hs2 hsX
  -- Bender (7), second half at `z`: `|Ĥ ⊓ Ĥ^z| = 6`
  have hD6z : Nat.card ↥(B.Hhat ⊓ Work.GW2.conjSub z B.Hhat) = 6 :=
    card_inf_conjSubOfThree I hBc B h1 D hz2 hzH X hXle hXne hXodd hXinv hCeven hNeven hU3 hz4
  -- transfer it to `y` along the bijection `x ↦ h⁻¹ * x * h`, which sends `Ĥ ⊓ Ĥ^z` onto
  -- `Ĥ ⊓ Ĥ^y` (as `z = h * y`: `(h * y)⁻¹ * (h⁻¹ * v * h) * (h * y) = y⁻¹ * v * y`)
  have hD6y : Nat.card ↥(B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) = 6 := by
    have hbij : Nat.card ↥(B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) =
        Nat.card ↥(B.Hhat ⊓ Work.GW2.conjSub z B.Hhat) := by
      have hmap : (B.Hhat ⊓ Work.GW2.conjSub z B.Hhat).map (MulAut.conj h⁻¹).toMonoidHom =
          B.Hhat ⊓ Work.GW2.conjSub y B.Hhat := by
        ext x
        rw [Subgroup.mem_map]
        constructor
        · rintro ⟨v, hv, rfl⟩
          obtain ⟨hvH, hvz⟩ := Subgroup.mem_inf.mp hv
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · show (MulAut.conj h⁻¹) v ∈ B.Hhat
            rw [MulAut.conj_apply, inv_inv]
            exact B.Hhat.mul_mem (B.Hhat.mul_mem (B.Hhat.inv_mem hhH) hvH) hhH
          · rw [Work.CORE2A.mem_conjSub_iff]
            have h3 : y⁻¹ * ((MulEquiv.toMonoidHom (MulAut.conj h⁻¹)) v) * y = z⁻¹ * v * z := by
              show y⁻¹ * (MulAut.conj h⁻¹) v * y = z⁻¹ * v * z
              rw [MulAut.conj_apply, inv_inv, hzy]; group
            rw [h3, ← Work.CORE2A.mem_conjSub_iff]
            exact hvz
        · intro hx
          obtain ⟨hxH, hxy⟩ := Subgroup.mem_inf.mp hx
          refine ⟨h * x * h⁻¹, ?_, ?_⟩
          · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
            · show h * x * h⁻¹ ∈ B.Hhat
              exact B.Hhat.mul_mem (B.Hhat.mul_mem hhH hxH) (B.Hhat.inv_mem hhH)
            · rw [Work.CORE2A.mem_conjSub_iff]
              have h3 : z⁻¹ * (h * x * h⁻¹) * z = y⁻¹ * x * y := by
                rw [hzy, mul_inv_rev]; group
              rw [h3, ← Work.CORE2A.mem_conjSub_iff]
              exact hxy
          · show (MulAut.conj h⁻¹) (h * x * h⁻¹) = x
            rw [MulAut.conj_apply, inv_inv]
            group
      calc Nat.card ↥(B.Hhat ⊓ Work.GW2.conjSub y B.Hhat)
          = Nat.card ↥((B.Hhat ⊓ Work.GW2.conjSub z B.Hhat).map
              (MulAut.conj h⁻¹).toMonoidHom) := by rw [← hmap]
        _ = Nat.card ↥(B.Hhat ⊓ Work.GW2.conjSub z B.Hhat) :=
            (Nat.card_congr (Subgroup.equivMapOfInjective _ _
              (MulAut.conj h⁻¹).injective).toEquiv).symm
    rw [hbij, hD6z]
  exact stabTrivial_of_card_data I hBc B h1 D hy2 hyH hU3 hD6y ha ha1

end Work.CORE3
