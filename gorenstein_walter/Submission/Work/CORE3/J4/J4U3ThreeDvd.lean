import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.J4.J4U3
import Submission.Work.CORE3.J4.J4U3CentralizerOdd
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.InvSetVUSingleton
import Submission.Work.CORE3.SevenNoInvolCentralizer
import Submission.Work.CORE3.SevenConjU
import Submission.Work.CORE2A.Basic

/-!
# `Work.CORE3.J4.J4U3ThreeDvd`

Bender 1981 §3, p. 224, (7), the *divisibility* half: in Case (1) of Bender's Theorem 2.10,
subcase `V = O₂(Ĥ)` of type `(2,2)`, an involution `y ∉ Ĥ` inverting a non-trivial odd-order
subgroup `X ≤ Ĥ` whose `G`-centralizer has even order forces `3 ∣ |U|` (`U = O(Ĥ) = O(H)`).

The extra hypothesis `Even |N_G(X)|` used by (7) to conclude `|U| = 3` is *not* needed for the
divisibility: the argument is

* `Even |C_G(X)|` gives an involution `s ∈ C_G(X)` (Cauchy);
* `s ∉ Ĥ` (`Work.CORE3.SevenNoInvolCentralizer`: no involution of `Ĥ` centralizes `X`);
* all involutions of `G` are conjugate (`LocalToolkit.fus`), so `s^k = t` for some `k`; then
  `X^k ≤ C_G(t) = B.H = B.U ⊔ B.S` and `X^k` has odd order, so `X^k ≤ B.U`
  (`Work.CORE2A.odd_subgroup_le_oddCoreIn` together with `Work.CORE3.H_eq_U_sup_S`);
* hence `|X| = |X^k|` divides `|B.U|`; and `|X| = 3`
  (`Work.CORE3.J4.card_X_eq_three`: `X` injects into `Ĥ/VU` of order `6`).
-/

namespace Work.CORE3.J4

open Subgroup

set_option linter.style.haveILetI false

/-- **Divisibility half of Bender (7).**  Under the hypotheses of `J4U3` (without the evenness of
`|N_G(X)|`) one has `3 ∣ |U|`. -/
theorem J4U3ThreeDvd {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    {X : Subgroup G} (hXH : X ≤ B.Hhat) (hX1 : X ≠ ⊥) (hXodd : Odd (Nat.card X))
    (hinv : Work.GW2.Inverts y X) (hC : Even (Nat.card (Subgroup.centralizer (X : Set G)))) :
    3 ∣ Nat.card B.U := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- (1) an involution `s` centralizing `X` exists
  obtain ⟨s, hsC, hs2⟩ :=
    Work.CORE3.exists_involution_mem_of_even_card (Subgroup.centralizer (X : Set G)) hC
  -- (2) `s ∉ Ĥ`
  have hsH : s ∉ B.Hhat := by
    intro hsmem
    refine Work.CORE3.SevenNoInvolCentralizer G I hBc B h1 D hy2 hyH hXH hX1 hXodd hinv
      ⟨s, hsmem, hs2, ?_⟩
    intro x hx
    exact ((Subgroup.mem_centralizer_iff.mp hsC) x hx).symm
  -- (3) all involutions are conjugate: `s^k = t`
  obtain ⟨n, hn2, hdih⟩ := Work.CORE3.SylowDihedral G hBc B
  have hnoN : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 :=
    Work.CORE2A.bender_no_index_two hBc B
  obtain ⟨k, hk⟩ := isConj_iff.mp ((I.T.fus G B.S n hn2 hdih hnoN).1 s B.t hs2 B.t_order)
  -- `hk : k * s * k⁻¹ = B.t`
  -- (4) `X^k ≤ B.H`
  have hconj_le : Work.GW2.conjSub k X ≤ B.H := by
    intro z hz
    rw [Work.CORE2A.conjSub_eq_map, Subgroup.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxs : s * x = x * s := ((Subgroup.mem_centralizer_iff.mp hsC) x hx).symm
    show MulAut.conj k x * B.t = B.t * MulAut.conj k x
    simp only [MulAut.conj_apply]
    rw [← hk]
    calc k * x * k⁻¹ * (k * s * k⁻¹) = k * (x * s) * k⁻¹ := by group
      _ = k * (s * x) * k⁻¹ := by rw [hxs]
      _ = (k * s * k⁻¹) * (k * x * k⁻¹) := by group
  -- (5) `X^k ≤ B.U` (an odd-order subgroup of `H = U ⊔ S` lies in `U`)
  have hBU : Work.GW2.conjSub k X ≤ B.U :=
    Work.CORE2A.odd_subgroup_le_oddCoreIn B.H B.U ((B.S : Subgroup G)) rfl
      (Work.CORE3.H_eq_U_sup_S G I.T hBc B) B.S.isPGroup' (Work.GW2.conjSub k X) hconj_le
      (by rw [Work.CORE2A.card_conjSub]; exact hXodd)
  -- (6) hence `|X| ∣ |B.U|`, and `|X| = 3`
  have hdvd : Nat.card X ∣ Nat.card B.U := by
    have h := Subgroup.card_dvd_of_le hBU
    rwa [Work.CORE2A.card_conjSub] at h
  have h3 : Nat.card X = 3 := card_X_eq_three I hBc B h1 D hy2 hyH hXH hX1 hXodd hinv
  rwa [h3] at hdvd

end Work.CORE3.J4
