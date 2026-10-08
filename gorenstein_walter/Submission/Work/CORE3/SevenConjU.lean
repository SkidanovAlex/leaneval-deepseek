import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.lemma22
import Submission.Work.CORE2A.odd_subgroup_le_oddCoreIn
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.VUInvSetTrivial
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.NotLeCentralizerOfIsFourGroup
import Submission.Work.CORE3.NoElemAbelianCardEight
import Submission.Work.CORE3.FourGroupOddOrderCommutingInvolution
import Submission.Work.CORE3.OddOrderMemOfMemSup

/-!
# CORE3, Bender (7) and the conjugacy of the odd subgroup `X`

Setting: `G` a minimal counterexample (`Work.GW2.BenderCtx G`), `B` a Bender setup with
`Case1 B`, `V = O₂(Ĥ) = pCoreIn 2 B.Hhat` a four-group (`Work.GW2.Case1bData B`, so also
`|S| = 8`), `U = O(Ĥ) = O(H)`, and an element `y ∉ Ĥ` of order `2` inverting an odd-order
subgroup `1 ≠ X ≤ Ĥ`.

The file proves the leaf `Work.CORE3.SevenConjU`: if moreover `|C_G(X)|` is even (and
`|U| = 3` is known), then `X` is a conjugate of `U`.

Route (Bender 1981 §3, p. 224; the docstring of `Case1bSeven`):

* `|C_G(X)|` even gives an involution `s ∈ C_G(X)` (Cauchy);
* `s ∉ Ĥ`: if `s ∈ Ĥ` then, since `x ∈ X` has odd order and commutes with the involution
  `s`, the four-group analysis (`fourGroup_oddOrder_conjCycle`,
  `FourGroupOddOrderCommutingInvolution`) forces `x ∈ U`, contradicting Bender's (5)
  (`VUInvSetTrivial`: no involution outside `Ĥ` inverts a non-trivial element of `V ⊔ U`);
* all involutions of `G` are conjugate (`LocalToolkit.fus`), so `s^k = t` for some `k`; then
  `X^k ≤ C_G(t) = B.H = B.U ⊔ B.S`, and `X^k` has odd order, so `X^k ≤ B.U`
  (`odd_subgroup_le_oddCoreIn`), whence `X ≤ (B.U)^k`;
* both sides have order `3` (`hU3`, `X ≠ ⊥` odd, `|X| ≤ |B.U|`), so `X = (B.U)^k`.
-/

namespace Work.CORE3

set_option linter.style.haveILetI false

open Subgroup
open Work.GW2

/-- A finite group of even cardinality has an element of order `2` (Cauchy).  Stated for a
subgroup of an ambient finite group, since that is the form in which it is used. -/
lemma exists_involution_mem_of_even_card {G : Type} [Group G] [Finite G] (C : Subgroup G)
    (hC : Even (Nat.card C)) : ∃ c ∈ C, orderOf c = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card ↥C := even_iff_two_dvd.mp hC
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 2 hdvd
  exact ⟨(c : G), c.2, by rw [Subgroup.orderOf_coe c, hc]⟩

/-- **The four-group step.**  `V` a four-group, `x, s ∈ N_G(V)`, `s` an involution of `V`
commuting with `x`, and `orderOf x` odd.  Then `x` centralizes `V`.

(If `x` did not centralize `V`, conjugation by `x` would be a `3`-cycle on the three
nonidentity elements of `V` (`fourGroup_oddOrder_conjCycle`), which contradicts the fact that
it fixes `s`.) -/
private lemma fourGroup_step_mem {G : Type} [Group G] [Finite G] {V : Subgroup G} {x s : G}
    (hV4 : IsFourGroup V) (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (hsV : s ∈ V) (hs1 : s ≠ 1) (hcomm : s * x = x * s) (hxo : Odd (orderOf x)) :
    x ∈ Subgroup.centralizer (V : Set G) := by
  by_contra hxcV
  obtain ⟨a, b, haV, hbV, ha1, hb1, hab, hVset, hxa, hxb, hxab⟩ :=
    fourGroup_oddOrder_conjCycle hV4 hxN hxo hxcV
  -- `x` fixes `s`
  have hconj_s : x * s * x⁻¹ = s := by
    rw [hcomm.symm, mul_assoc, mul_inv_cancel, mul_one]
  have hs_mem : s ∈ ({1, a, b, a * b} : Set G) := by rw [← hVset]; exact hsV
  rcases Set.mem_insert_iff.mp hs_mem with h | h
  · exact hs1 h
  · rcases Set.mem_insert_iff.mp h with h | h
    · -- `s = a`: `x * s * x⁻¹ = b` forces `b = s = a`
      rw [← h] at hxa
      rw [hxa] at hconj_s
      exact hab (hconj_s.trans h).symm
    · rcases Set.mem_insert_iff.mp h with h | h
      · -- `s = b`: `x * s * x⁻¹ = a * b` forces `a * b = s = b`, i.e. `a = 1`
        rw [← h] at hxb
        rw [hxb, h] at hconj_s
        have h2 : a * b = 1 * b := by
          calc a * b = b := hconj_s
            _ = 1 * b := (one_mul b).symm
        exact ha1 (mul_right_cancel h2)
      · -- `s = a * b`: `x * s * x⁻¹ = a` forces `a = s = a * b`, i.e. `b = 1`
        rw [← h] at hxab
        rw [hxab, h] at hconj_s
        have h2 : a * b = a * 1 := by
          calc a * b = a := hconj_s.symm
            _ = a * 1 := (mul_one a).symm
        exact hb1 (mul_left_cancel h2)

/-- **No involution of `Ĥ` centralizes `X`.**  Setting as in the module header. -/
private lemma no_involution_mem_centralizer {G : Type} [Group G] [Finite G]
    (I : Case1Inputs) (hBc : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B)
    (D : Case1bData B) {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    {X : Subgroup G} (hXH : X ≤ B.Hhat) (hXne : X ≠ ⊥) (hXodd : Odd (Nat.card X))
    (hinv : ∀ x ∈ X, y * x * y⁻¹ = x⁻¹)
    {s : G} (hsH : s ∈ B.Hhat) (hs2 : orderOf s = 2)
    (hsC : s ∈ Subgroup.centralizer (X : Set G)) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- an element `1 ≠ x ∈ X`, of odd order
  obtain ⟨x, hxX, hx1⟩ : ∃ x : G, x ∈ X ∧ x ≠ 1 := by
    by_contra hcon
    apply hXne
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    by_contra hz1
    exact hcon ⟨z, hz, hz1⟩
  have hxH : x ∈ B.Hhat := hXH hxX
  have hxodd : Odd (orderOf x) := Odd.of_dvd_nat hXodd (Subgroup.orderOf_dvd_natCard X hxX)
  have hxs : s * x = x * s := ((Subgroup.mem_centralizer_iff.mp hsC) x hxX).symm
  -- structure of `Ĥ`: `V = O₂(Ĥ)` is a four-group, normal in `Ĥ`
  have hV4 : IsFourGroup (pCoreIn 2 B.Hhat) := D.four
  have h26 : Thm26Concl B := I.h26 G I.T.ft hBc B
  have hUnorm : B.Hhat ≤ Subgroup.normalizer (((pCoreIn 2 B.Hhat) : Subgroup G) : Set G) := by
    simpa [pCoreIn] using le_normalizer_map_subtype B.Hhat (pCore 2 ↥B.Hhat)
  have hxN : x ∈ Subgroup.normalizer (((pCoreIn 2 B.Hhat) : Subgroup G) : Set G) := hUnorm hxH
  have hsN : s ∈ Subgroup.normalizer (((pCoreIn 2 B.Hhat) : Subgroup G) : Set G) := hUnorm hsH
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  -- `x` centralizes `V`
  have hxCV : x ∈ Subgroup.centralizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
    by_cases hsV : s ∈ pCoreIn 2 B.Hhat
    · exact fourGroup_step_mem hV4 hxN hsV hs1 hxs hxodd
    · -- `s ∉ V`: then `s ∉ C(V)` (`NotLeCentralizerOfIsFourGroup`), so if `x ∉ C(V)` the
      -- odd-order element `x` commuting with the involution `s` would force `s ∈ C(V)`
      -- (`FourGroupOddOrderCommutingInvolution`)
      have hdih4 : Nonempty (((B.S : Subgroup G)) ≃* DihedralGroup 4) := by
        obtain ⟨n, _hn2, ⟨e⟩⟩ := SylowDihedral G hBc B
        have hcardS : Nat.card (B.S : Subgroup G) = 2 * n := by
          rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
        have hn : n = 4 := by rw [D.S8] at hcardS; omega
        rw [hn] at e
        exact ⟨e⟩
      have hno : ¬ ∃ W : Subgroup G, Nat.card W = 8 ∧ ∀ z ∈ W, z ^ 2 = 1 :=
        NoElemAbelianCardEight B.S D.S8 hdih4
      have hs_not : ¬ (pCoreIn 2 B.Hhat) ≤ Subgroup.centralizer ({s} : Set G) :=
        NotLeCentralizerOfIsFourGroup (pCoreIn 2 B.Hhat) s hV4 hs2 hsV hno
      by_cases hxCV' : x ∈ Subgroup.centralizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G)
      · exact hxCV'
      · exact absurd (FourGroupOddOrderCommutingInvolution (V := pCoreIn 2 B.Hhat)
          (x := x) (c := s) hV4 hxN hsN hxodd hxCV' (by rw [pow_two]; exact hss) hxs)
          (fun hsCV' => hs_not (fun v hv => by
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact (Subgroup.mem_centralizer_iff.mp hsCV') v hv))
  -- hence `x ∈ V ⊔ U` ...
  have hxVU : x ∈ pCoreIn 2 B.Hhat ⊔ B.U := by
    rw [← CentralizerPcoreEqVU G I hBc B h1 D]
    exact ⟨hxCV, hxH⟩
  -- ... and `x` has odd order, so `x ∈ U`
  have hUodd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  have hdisj : pCoreIn 2 B.Hhat ⊓ B.U = ⊥ := by
    have hcopVU : Nat.Coprime (Nat.card (pCoreIn 2 B.Hhat)) (Nat.card B.U) := by
      rw [hV4.1, show (4 : ℕ) = 2 ^ 2 from rfl]
      exact Nat.Coprime.pow_left 2 ((hUodd.coprime_two_right).symm)
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcopVU)
  have hVU : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) :=
    (Work.CORE2A.thm26Concl_centralizer_eq h26) ▸ inf_le_right
  have hxU : x ∈ B.U := OddOrderMemOfMemSup hV4 hUodd hdisj hVU hxVU hxodd
  -- contradicting Bender's (5)
  have hxmem : x ∈ invSet (pCoreIn 2 B.Hhat ⊔ B.U) y :=
    ⟨hxVU, hinv x hxX⟩
  rw [VUInvSetTrivial G I hBc B h1 D y hy2 hyH] at hxmem
  exact hx1 (Set.mem_singleton_iff.mp hxmem)

theorem SevenConjU (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat) {X : Subgroup G} (hXH : X ≤ B.Hhat)
    (hXne : X ≠ ⊥) (hXodd : Odd (Nat.card X)) (hinv : ∀ x ∈ X, y * x * y⁻¹ = x⁻¹)
    (hC : Even (Nat.card (Subgroup.centralizer (X : Set G)))) :
    ∃ g : G, X = Work.GW2.conjSub g B.U := by
  classical
  -- (1) an involution `s` centralizing `X` exists; it cannot lie in `Ĥ`
  obtain ⟨s, hsC, hs2⟩ := exists_involution_mem_of_even_card _ hC
  have hsH : s ∉ B.Hhat := fun hmem =>
    no_involution_mem_centralizer I hBc B h1 D hy2 hyH hXH hXne hXodd hinv hmem hs2 hsC
  -- (2) all involutions are conjugate: `s^k = t`
  obtain ⟨n, hn2, hdih⟩ := SylowDihedral G hBc B
  have hnoN : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 :=
    Work.CORE2A.bender_no_index_two hBc B
  obtain ⟨k, hk⟩ := isConj_iff.mp ((I.T.fus G B.S n hn2 hdih hnoN).1 s B.t hs2 B.t_order)
  -- `hk : k * s * k⁻¹ = B.t`
  -- (3) `conjSub k X ≤ B.H`
  have hconj_le : conjSub k X ≤ B.H := by
    intro z hz
    rw [Work.CORE2A.conjSub_eq_map, Subgroup.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxs : s * x = x * s := ((Subgroup.mem_centralizer_iff.mp hsC) x hx).symm
    show (MulAut.conj k) x * B.t = B.t * (MulAut.conj k) x
    simp only [MulAut.conj_apply]
    rw [← hk]
    calc k * x * k⁻¹ * (k * s * k⁻¹) = k * (x * s) * k⁻¹ := by group
      _ = k * (s * x) * k⁻¹ := by rw [hxs]
      _ = (k * s * k⁻¹) * (k * x * k⁻¹) := by group
  -- (4) `conjSub k X ≤ B.U`
  have hBU : conjSub k X ≤ B.U :=
    Work.CORE2A.odd_subgroup_le_oddCoreIn B.H B.U ((B.S : Subgroup G)) rfl
      (H_eq_U_sup_S G I.T hBc B) B.S.isPGroup' (conjSub k X) hconj_le
      (by rw [Work.CORE2A.card_conjSub]; exact hXodd)
  -- (5) pull back and compare cardinalities
  have hle : X ≤ conjSub k⁻¹ B.U := by
    have h1' := Work.CORE2A.conjSub_mono hBU k⁻¹
    rwa [Work.CORE2A.conjSub_inv_conjSub] at h1'
  have hge : 2 ≤ Nat.card X := by
    by_contra hcon
    simp only [not_le] at hcon
    have hzero : Nat.card X ≠ 0 := fun h => by
      rw [h] at hXodd
      exact Nat.not_odd_zero hXodd
    have hone : Nat.card X = 1 := by omega
    exact hXne (Subgroup.card_eq_one.mp hone)
  have hXcard : Nat.card X = 3 := by
    have hle3 : Nat.card X ≤ Nat.card (conjSub k⁻¹ B.U) := by
      have h := Subgroup.card_le_card_group (X.subgroupOf (conjSub k⁻¹ B.U))
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
    rw [Work.CORE2A.card_conjSub, hU3] at hle3
    obtain ⟨m, hm⟩ := hXodd
    omega
  refine ⟨k⁻¹, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [Work.CORE2A.card_conjSub, hU3, hXcard]

end Work.CORE3
