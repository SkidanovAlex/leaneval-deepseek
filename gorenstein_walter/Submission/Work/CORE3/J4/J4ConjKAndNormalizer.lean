import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.J4.J4GStructNoInvCentralizer
import Submission.Work.CORE3.J4.J4U3
import Submission.Work.CORE3.Case1bDStructure
import Submission.Work.CORE3.SevenConjU
import Submission.Work.CORE3.VUInvSetTrivial
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.odd_subgroup_le_oddCoreIn

/-!
# CORE3 / J4: the odd subgroup `X` is conjugate into `K`, with its normalizer in `Ĥ`

Setting: `G` a minimal counterexample (`Work.GW2.BenderCtx G`), `B` a Bender setup with
`Case1 B`, `V = O₂(Ĥ) = pCoreIn 2 B.Hhat` a four-group (`Work.GW2.Case1bData B`, so `|S| = 8`),
`U = O(Ĥ) = O(H)` and `K` the Hall subgroup of `F(U)` inverted by every involution of `Ĥ − V`
(Bender 1981, §3, p. 224, item (7)).

For an involution `y ∉ Ĥ` inverting a nontrivial odd-order subgroup `1 ≠ X ≤ Ĥ` with
`|C_G(X)|` even, the theorem produces `g : G` with

* `X ≤ K^g` (`K^g = Work.GW2.conjSub g D.K`), and
* `N_G(X) ≤ Ĥ^g`.

Route (Bender 1981 §3, p. 224): Bender's (5) (`Work.CORE3.VUInvSetTrivial`, no involution
outside `Ĥ` inverts a nontrivial element of `VU = O₂(Ĥ) ⊔ O(Ĥ)`) kills every involution of `Ĥ`
centralizing `X` (`Work.CORE3.J4.J4GStructNoInvCentralizer`), so the even order of `C_G(X)`
yields an involution `s ∈ C_G(X)` with `s ∉ Ĥ`.  Since all involutions of `G` are conjugate
(`LocalToolkit.fus`), `k s k⁻¹ = t` for some `k`; then `X^k ≤ C_G(t) = H = U ⊔ S` has odd order,
so `X^k ≤ U` (`odd_subgroup_le_oddCoreIn`).  The involution `k y k⁻¹` inverts `X^k`; Bender's (5)
forces `k y k⁻¹ ∈ Ĥ`, and it cannot lie in `V` (that would centralize `U` whence `X^k` would be
inverted by an element of `V ≤ C_G(U)`, making an element of `X^k` of order `≤ 2`, impossible for
odd order `≠ 1`).  So `k y k⁻¹ ∈ Ĥ − V` and `X^k ⊆ I_U(k y k⁻¹) = K` (Bender's `D.inv`).
Finally `N_G(X^k) ≤ Ĥ` by local control (`Case1`'s second conjunct), since `X^k` is a nontrivial
subgroup of `F(U)`.
-/

namespace Work.CORE3.J4

open Subgroup
open Work.GW2

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

theorem J4ConjKAndNormalizer {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (h : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    {X : Subgroup G} (hXle : X ≤ B.Hhat) (hXne : X ≠ ⊥) (hXodd : Odd (Nat.card X))
    (hinv : Work.GW2.Inverts y X)
    (hCeven : Even (Nat.card (Subgroup.centralizer (X : Set G)))) :
    ∃ g : G, X ≤ Work.GW2.conjSub g D.K ∧
      Subgroup.normalizer (X : Set G) ≤ Work.GW2.conjSub g B.Hhat := by
  classical
  -- ### Step 1: an involution `s ∈ C_G(X)` outside `Ĥ`
  obtain ⟨s, hsC, hs2⟩ := Work.CORE3.exists_involution_mem_of_even_card _ hCeven
  have hsH : s ∉ B.Hhat := fun hmem =>
    J4GStructNoInvCentralizer I h B h1 D hy2 hyH hXle hXne hXodd hinv ⟨s, hmem, hs2, hsC⟩
  -- ### Step 2: fusion: `k * s * k⁻¹ = B.t`
  obtain ⟨n, hn2, hdih⟩ := Work.CORE3.SylowDihedral G h B
  have hnoN : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := Work.CORE2A.bender_no_index_two h B
  obtain ⟨k, hk⟩ := isConj_iff.mp ((I.T.fus G B.S n hn2 hdih hnoN).1 s B.t hs2 B.t_order)
  -- `hk : k * s * k⁻¹ = B.t`
  have hXs : ∀ x ∈ X, x * s = s * x := fun x hx => Subgroup.mem_centralizer_iff.mp hsC x hx
  -- ### Step 3: `conjSub k X ≤ C_G(B.t) = B.H`
  have hZleH : Work.GW2.conjSub k X ≤ B.H := by
    intro z hz
    have hzx : k⁻¹ * z * k ∈ X := Work.CORE2A.mem_conjSub_iff.mp hz
    have hz_eq : z = k * (k⁻¹ * z * k) * k⁻¹ := by group
    have hxs : (k⁻¹ * z * k) * s = s * (k⁻¹ * z * k) := hXs _ hzx
    show z ∈ Subgroup.centralizer ({B.t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff, hz_eq, ← hk]
    calc k * (k⁻¹ * z * k) * k⁻¹ * (k * s * k⁻¹)
        = k * ((k⁻¹ * z * k) * s) * k⁻¹ := by group
      _ = k * (s * (k⁻¹ * z * k)) * k⁻¹ := by rw [hxs]
      _ = (k * s * k⁻¹) * (k * (k⁻¹ * z * k) * k⁻¹) := by group
  -- ### Step 4: `conjSub k X ≤ B.U`
  have hZleU : Work.GW2.conjSub k X ≤ B.U :=
    Work.CORE2A.odd_subgroup_le_oddCoreIn B.H B.U (B.S : Subgroup G) rfl
      (Work.CORE3.H_eq_U_sup_S G I.T h B) B.S.isPGroup' (Work.GW2.conjSub k X) hZleH
      (by rw [Work.CORE2A.card_conjSub]; exact hXodd)
  -- ### Step 5: an element `z ∈ conjSub k X` with `z ≠ 1`
  have hZne : Work.GW2.conjSub k X ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥(Work.GW2.conjSub k X) = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [Work.CORE2A.card_conjSub] at hcard
    exact hXne (Subgroup.card_eq_one.mp hcard)
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Work.GW2.conjSub k X, z ≠ 1 := by
    by_contra hcon
    apply hZne
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    by_contra hw1
    exact hcon ⟨w, hw, hw1⟩
  -- ### Step 6: `conjSub k X` is inverted by `k y k⁻¹`
  have hZinv : ∀ w ∈ Work.GW2.conjSub k X, (k * y * k⁻¹) * w * (k * y * k⁻¹)⁻¹ = w⁻¹ := by
    intro w hw
    have hwx : k⁻¹ * w * k ∈ X := Work.CORE2A.mem_conjSub_iff.mp hw
    have hw_eq : w = k * (k⁻¹ * w * k) * k⁻¹ := by group
    rw [hw_eq]
    have h1 : y * (k⁻¹ * w * k) * y⁻¹ = (k⁻¹ * w * k)⁻¹ := hinv _ hwx
    have h2 : (k * y * k⁻¹) * (k * (k⁻¹ * w * k) * k⁻¹) * (k * y * k⁻¹)⁻¹
        = k * (y * (k⁻¹ * w * k) * y⁻¹) * k⁻¹ := by group
    rw [h2, h1]
    group
  -- ### Step 7: `k y k⁻¹` lies in `Ĥ`
  have hyk2 : orderOf (k * y * k⁻¹) = 2 := by
    rw [Work.CORE3.orderOf_eq_two_iff_mul_self]
    have hy : y * y = 1 := ((Work.CORE3.orderOf_eq_two_iff_mul_self y).mp hy2).1
    refine ⟨?_, ?_⟩
    · calc (k * y * k⁻¹) * (k * y * k⁻¹) = k * (y * y) * k⁻¹ := by group
        _ = 1 := by rw [hy]; group
    · intro h1
      have hy1 : y = 1 := by
        have h2 : y = k⁻¹ * (k * y * k⁻¹) * k := by group
        rw [h2, h1]; group
      exact ((Work.CORE3.orderOf_eq_two_iff_mul_self y).mp hy2).2 hy1
  have hykH : k * y * k⁻¹ ∈ B.Hhat := by
    by_contra hcon
    have h5 : Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) (k * y * k⁻¹) = {1} :=
      Work.CORE3.VUInvSetTrivial G I h B h1 D (k * y * k⁻¹) hyk2 hcon
    have hzVU : z ∈ Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U := Subgroup.mem_sup_right (hZleU hzZ)
    have hmem : z ∈ Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) (k * y * k⁻¹) :=
      ⟨hzVU, hZinv z hzZ⟩
    rw [h5] at hmem
    exact hz1 (Set.mem_singleton_iff.mp hmem)
  -- ### Step 8: `k y k⁻¹ ∉ V = O₂(Ĥ)`
  have hVleCU : Work.GW2.pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    have h26 : Thm26Concl B := I.h26 G I.T.ft h B
    rw [← h26.2.1]
    exact inf_le_right
  have hykV : k * y * k⁻¹ ∉ Work.GW2.pCoreIn 2 B.Hhat := by
    intro hcon
    have hcomm : z * (k * y * k⁻¹) = (k * y * k⁻¹) * z :=
      Subgroup.mem_centralizer_iff.mp (hVleCU hcon) z (hZleU hzZ)
    have hinvz := hZinv z hzZ
    have hzsq : z * z = 1 := by
      have hz_eq : z⁻¹ = z := by
        rw [← hinvz, ← hcomm]
        group
      calc z * z = z * z⁻¹ := by rw [hz_eq]
        _ = 1 := mul_inv_cancel z
    have hdvd : orderOf z ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using hzsq
    have hdvdU : orderOf z ∣ Nat.card ↥B.U := Subgroup.orderOf_dvd_natCard B.U (hZleU hzZ)
    have hcop : Nat.Coprime 2 (Nat.card ↥B.U) :=
      (Nat.coprime_two_left).mpr (Work.CORE2A.bSetup_U_odd B)
    have hz1' : z = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd hdvdU)
    exact hz1 hz1'
  -- ### Step 9: `conjSub k X ≤ K`
  have hZK : Work.GW2.conjSub k X ≤ D.K := by
    intro w hw
    have hKD : w ∈ (D.K : Set G) := by
      rw [D.inv (k * y * k⁻¹) hykH hyk2 hykV]
      exact ⟨hZleU hw, hZinv w hw⟩
    exact hKD
  -- ### Step 10: `N_G(conjSub k X) ≤ Ĥ` by Case (1)
  have hNK : Subgroup.normalizer (Work.GW2.conjSub k X : Set G) ≤ B.Hhat :=
    h1.2 (Work.GW2.conjSub k X) hZne (hZK.trans (Work.CORE2A.isHallIn_le D.hall))
  refine ⟨k⁻¹, ?_, ?_⟩
  · -- `X ≤ conjSub k⁻¹ D.K`
    intro x hx
    show x ∈ Work.GW2.conjSub k⁻¹ D.K
    rw [Work.CORE2A.mem_conjSub_iff]
    simp only [inv_inv]
    have hmem : k * x * k⁻¹ ∈ Work.GW2.conjSub k X := by
      show k * x * k⁻¹ ∈ Work.GW2.conjSub k X
      rw [Work.CORE2A.mem_conjSub_iff]
      have hxx : k⁻¹ * (k * x * k⁻¹) * k = x := by group
      rw [hxx]
      exact hx
    exact hZK hmem
  · -- `N_G(X) ≤ conjSub k⁻¹ Ĥ`
    intro h' hh
    show h' ∈ Work.GW2.conjSub k⁻¹ B.Hhat
    rw [Work.CORE2A.mem_conjSub_iff]
    simp only [inv_inv]
    have hmemN : k * h' * k⁻¹ ∈ Subgroup.normalizer (Work.GW2.conjSub k X : Set G) := by
      rw [Subgroup.mem_normalizer_iff] at hh ⊢
      intro a
      have h1' : (k⁻¹ * a * k) ∈ X ↔ h' * (k⁻¹ * a * k) * h'⁻¹ ∈ X := hh (k⁻¹ * a * k)
      have h3' : (k * h' * k⁻¹) * a * (k * h' * k⁻¹)⁻¹
          = k * (h' * (k⁻¹ * a * k) * h'⁻¹) * k⁻¹ := by group
      rw [Work.CORE2A.mem_conjSub_iff, h3', Work.CORE2A.mem_conjSub_iff]
      have h4' : k⁻¹ * (k * (h' * (k⁻¹ * a * k) * h'⁻¹) * k⁻¹) * k
          = h' * (k⁻¹ * a * k) * h'⁻¹ := by group
      rw [h4']
      exact h1'
    exact hNK hmemN

end Work.CORE3.J4
