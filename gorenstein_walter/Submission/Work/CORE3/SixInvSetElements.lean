import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.CosetInvCountBasic
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.CosetInvCountNeFiveOf

/-!
# The structure of a coset of `Ĥ` carrying six involutions

Bender 1981 §3 (5): if no involution `z ∉ Ĥ` inverts a nontrivial element of `VU = O₂(Ĥ)·O(Ĥ)`,
then the inverted set `I_Ĥ(y) = {x ∈ Ĥ | y x y = x⁻¹}` of an involution `y ∉ Ĥ` injects into
`Ĥ/VU`, which has order `6` (`Work.CORE3.ncard_invSetIn_le_relIndex`,
`Work.CORE3.relIndex_VU_Hhat`).  Hence `|I_Ĥ(y)| ≤ 6`, and if the coset `yĤ` carries six
involutions, that injection is a bijection onto `Ĥ/VU`.

The quotient `Ĥ/VU` is nonabelian of order `6` (Bender's Theorem 2.6).  Cauchy's theorem
supplies elements `q₂`, `q₃` of orders `2`, `3`; their preimages `b₁`, `a` in `I_Ĥ(y)` have
orders `2`, `3` in `G` (because `x^k ∈ I_Ĥ(y) ∩ VU = 1` for `k = orderOf (x·VU)`), and the
conjugate `q₃ q₂ q₃⁻¹ ≠ q₂` (otherwise `q₃ q₂` would have order `6`, making `Ĥ/VU` cyclic and
hence abelian) has a preimage `b₂ ≠ b₁`, again of order `2`.

This is the statement `Work.CORE3.SixInvSetElements`.
-/

namespace Work.CORE3

set_option maxHeartbeats 1000000 in
theorem SixInvSetElements (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (h : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B)
    (h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) z = {1}) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → Work.GW2.cosetInvCount B.Hhat y = 6 →
      ∃ a b1 b2 : G, a ∈ Work.CORE3.invSetIn B.Hhat y ∧ orderOf a = 3 ∧
        b1 ∈ Work.CORE3.invSetIn B.Hhat y ∧ orderOf b1 = 2 ∧
        b2 ∈ Work.CORE3.invSetIn B.Hhat y ∧ orderOf b2 = 2 ∧ b1 ≠ b2 := by
  intro y hy2 hyH hcnt6
  have hy : y * y = 1 := (orderOf_eq_two_iff_mul_self y).mp hy2 |>.1
  have h26 : Work.GW2.Thm26Concl B := I.h26 G I.T.ft h B
  let W : Subgroup G := Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U
  let N : Subgroup ↥B.Hhat := W.subgroupOf B.Hhat
  have hWle : W ≤ B.Hhat :=
    sup_le (Work.CORE2A.thm26Concl_O2_le_Hhat h26) (Work.CORE2A.thm26Concl_U_le_Hhat h26)
  have hWn : N.Normal := normal_VU_subgroupOf G I h B h1 D
  haveI : N.Normal := hWn
  have hcard6 : Nat.card (↥B.Hhat ⧸ N) = 6 := by
    rw [← Subgroup.index_eq_card N]
    exact relIndex_VU_Hhat G I h B h1 D
  -- `Ĥ/VU` is nonabelian (Bender's Theorem 2.6)
  have hQnab : ¬ IsMulCommutative (↥B.Hhat ⧸ N) := by
    intro hc
    have hnab0 : ∃ u ∈ B.Hhat, ∃ v ∈ B.Hhat,
        u * v * u⁻¹ * v⁻¹ ∉ (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) := by
      rcases h26.2.2 with ⟨hle, -⟩ | ⟨-, -, hnab⟩
      · exact absurd (isCyclic_of_le_of_isCyclic' hle B.S0_cyclic)
          (not_isCyclic_of_isFourGroup' D.four)
      · exact hnab
    obtain ⟨u, hu, v, hv, hcomm⟩ := hnab0
    apply hcomm
    have hcy := (isMulCommutative_iff.mp hc)
      (QuotientGroup.mk' N (⟨u, hu⟩ : ↥B.Hhat)) (QuotientGroup.mk' N (⟨v, hv⟩ : ↥B.Hhat))
    have h1 : QuotientGroup.mk' N
        ((⟨u, hu⟩ : ↥B.Hhat) * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcy]
      group
    have hN : ((⟨u, hu⟩ : ↥B.Hhat) * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹) ∈ N := by
      rw [← QuotientGroup.ker_mk' (N := N)]
      exact MonoidHom.mem_ker.mpr h1
    have hmem := Subgroup.mem_subgroupOf.mp hN
    simpa [N, W] using hmem
  have h5' : ∀ z : G, z * z = 1 → z ∉ B.Hhat → Work.GW2.invSet W z = {1} := by
    intro z hz hzH
    have hz1 : z ≠ 1 := by rintro rfl; exact hzH B.Hhat.one_mem
    exact h5 z ((orderOf_eq_two_iff_mul_self z).mpr ⟨hz, hz1⟩) hzH
  have hI6 : (invSetIn B.Hhat y).ncard = 6 := by
    rw [ncard_invSetIn_eq_cosetInvCount B.Hhat y hy hyH]
    exact hcnt6
  -- the quotient map is injective on `I_Ĥ(y)`
  have hInj : Set.InjOn (fun x : ↥B.Hhat => (QuotientGroup.mk x : ↥B.Hhat ⧸ N))
      {x : ↥B.Hhat | (x : G) ∈ invSetIn B.Hhat y} := by
    intro x hx x' hx' heq
    have heq' : (QuotientGroup.mk x : ↥B.Hhat ⧸ N) = QuotientGroup.mk x' := heq
    rw [QuotientGroup.eq] at heq'
    have hmem : (((x⁻¹ * x' : ↥B.Hhat)) : G) ∈ W := Subgroup.mem_subgroupOf.mp heq'
    have hmem' : (x : G)⁻¹ * (x' : G) ∈ W := by simpa using hmem
    have hconj : (x' : G) * (x : G)⁻¹ ∈ W := by
      have hnorm := (Subgroup.normal_subgroupOf_iff hWle).mp hWn
      have hh := hnorm ((x : G)⁻¹ * (x' : G)) (x : G) hmem' x.2
      simpa [mul_assoc] using hh
    exact Subtype.ext (invSetIn_eq_of_mul_inv_mem hWle h5' hy hyH hx' hx hconj).symm
  have hS : {x : ↥B.Hhat | (x : G) ∈ invSetIn B.Hhat y}.ncard = 6 := by
    rw [← hI6]
    refine Set.ncard_congr (fun x _ => (x : G)) ?_ ?_ ?_
    · intro x hx; exact hx
    · intro a b _ _ hab; exact Subtype.ext hab
    · intro b hb; exact ⟨⟨b, hb.1⟩, hb, rfl⟩
  -- consequently the quotient map is surjective on `I_Ĥ(y)`
  have hsurj : ∀ q : ↥B.Hhat ⧸ N, ∃ x : ↥B.Hhat,
      (x : G) ∈ invSetIn B.Hhat y ∧ QuotientGroup.mk x = q := by
    intro q
    have himg : ((fun x : ↥B.Hhat => (QuotientGroup.mk x : ↥B.Hhat ⧸ N)) ''
        {x : ↥B.Hhat | (x : G) ∈ invSetIn B.Hhat y}).ncard = 6 := by
      rw [hInj.ncard_image, hS]
    have heq : (fun x : ↥B.Hhat => (QuotientGroup.mk x : ↥B.Hhat ⧸ N)) ''
        {x : ↥B.Hhat | (x : G) ∈ invSetIn B.Hhat y} = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
      rw [Set.ncard_univ, himg, hcard6]
    have hq : q ∈ (fun x : ↥B.Hhat => (QuotientGroup.mk x : ↥B.Hhat ⧸ N)) ''
        {x : ↥B.Hhat | (x : G) ∈ invSetIn B.Hhat y} := by
      rw [heq]; exact Set.mem_univ q
    obtain ⟨x, hx, hxq⟩ := hq
    exact ⟨x, hx, hxq⟩
  -- an element of `I_Ĥ(y)` killed modulo `VU` is killed in `G`
  have hkill : ∀ (x : ↥B.Hhat), (x : G) ∈ invSetIn B.Hhat y → ∀ k : ℕ,
      (QuotientGroup.mk x : ↥B.Hhat ⧸ N) ^ k = 1 → (x : G) ^ k = 1 := by
    intro x hx k hk
    have hinvpow : y * (x : G) ^ k * y⁻¹ = ((x : G) ^ k)⁻¹ := by
      rw [inv_eq_of_mul_eq_one_right hy, conj_pow_of_inv hy hx.2 k, inv_pow]
    have hk' : QuotientGroup.mk' N (x ^ k) = 1 := by
      rw [map_pow]
      simpa [QuotientGroup.mk'_apply] using hk
    have hmemN : x ^ k ∈ N := by
      rw [← QuotientGroup.ker_mk' (N := N)]
      exact MonoidHom.mem_ker.mpr hk'
    have hmemW : ((x ^ k : ↥B.Hhat) : G) ∈ W := Subgroup.mem_subgroupOf.mp hmemN
    have hmemW' : (x : G) ^ k ∈ W := by simpa using hmemW
    have hmem : (x : G) ^ k ∈ Work.GW2.invSet W y := ⟨hmemW', hinvpow⟩
    have h5y : Work.GW2.invSet W y = ({1} : Set G) := h5 y hy2 hyH
    rw [h5y] at hmem
    exact Set.mem_singleton_iff.mp hmem
  -- Cauchy in the quotient, of orders `3` and `2`
  obtain ⟨q3, hq3⟩ := exists_prime_orderOf_dvd_card' (G := ↥B.Hhat ⧸ N) 3 (by rw [hcard6]; norm_num)
  obtain ⟨q2, hq2⟩ := exists_prime_orderOf_dvd_card' (G := ↥B.Hhat ⧸ N) 2 (by rw [hcard6]; norm_num)
  obtain ⟨x3, hx3mem, hx3q⟩ := hsurj q3
  obtain ⟨y1, hy1mem, hy1q⟩ := hsurj q2
  have hq3pow : q3 ^ 3 = 1 := by rw [← hq3]; exact pow_orderOf_eq_one q3
  have hq2pow : q2 ^ 2 = 1 := by rw [← hq2]; exact pow_orderOf_eq_one q2
  have hx3pow : (x3 : G) ^ 3 = 1 := hkill x3 hx3mem 3 (by rw [hx3q, hq3pow])
  have hx3ord : orderOf (x3 : G) = 3 := by
    refine orderOf_eq_prime hx3pow ?_
    intro hcon
    have hx3one : x3 = 1 := Subtype.ext hcon
    have hq3one : q3 = 1 := by rw [← hx3q, hx3one]; simp
    rw [hq3one] at hq3
    exact absurd hq3 (by norm_num)
  have hy1pow : (y1 : G) ^ 2 = 1 := hkill y1 hy1mem 2 (by rw [hy1q, hq2pow])
  have hy1ord : orderOf (y1 : G) = 2 := by
    refine orderOf_eq_prime hy1pow ?_
    intro hcon
    have hy1one : y1 = 1 := Subtype.ext hcon
    have hq2one : q2 = 1 := by rw [← hy1q, hy1one]; simp
    rw [hq2one] at hq2
    exact absurd hq2 (by norm_num)
  -- the conjugate of `q2` by `q3` is a second involution of the quotient
  have hw2 : (q3 * q2 * q3⁻¹) ^ 2 = 1 := by
    have hsq : (q3 * q2 * q3⁻¹) ^ 2 = q3 * q2 ^ 2 * q3⁻¹ := by
      rw [pow_two, pow_two]
      group
    rw [hsq, hq2pow, mul_one, mul_inv_cancel]
  have hwne1 : q3 * q2 * q3⁻¹ ≠ 1 := by
    intro hw
    have h : q3 * q2 = q3 := mul_inv_eq_one.mp hw
    have h2 : q2 = 1 := by
      have hh : q3 * q2 = q3 * 1 := by rw [h, mul_one]
      exact mul_left_cancel hh
    rw [h2] at hq2
    exact absurd hq2 (by norm_num)
  have hwne_q2 : q3 * q2 * q3⁻¹ ≠ q2 := by
    intro hwq
    have hcomm : Commute q3 q2 := by
      have h : q3 * q2 = q2 * q3 := by
        have h' := congrArg (fun z => z * q3) hwq
        rw [mul_assoc, inv_mul_cancel, mul_one] at h'
        exact h'
      exact h
    have hcop : (orderOf q3).Coprime (orderOf q2) := by rw [hq3, hq2]; norm_num
    have h6 : orderOf (q3 * q2) = 6 := by
      rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcomm hcop, hq3, hq2]
    have hcyc : IsCyclic (↥B.Hhat ⧸ N) := by
      refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨q3 * q2, ?_⟩
      refine Subgroup.eq_top_of_card_eq (Subgroup.zpowers (q3 * q2)) ?_
      rw [Nat.card_zpowers, h6, hcard6]
    exact hQnab (IsMulCommutative.of_comm (fun p q => by
      letI := IsCyclic.commGroup (α := ↥B.Hhat ⧸ N)
      exact mul_comm p q))
  obtain ⟨y2, hy2mem, hy2q⟩ := hsurj (q3 * q2 * q3⁻¹)
  have hy2pow : (y2 : G) ^ 2 = 1 := hkill y2 hy2mem 2 (by rw [hy2q, hw2])
  have hy2ord : orderOf (y2 : G) = 2 := by
    refine orderOf_eq_prime hy2pow ?_
    intro hcon
    have hy2one : y2 = 1 := Subtype.ext hcon
    have h1 : q3 * q2 * q3⁻¹ = 1 := by rw [← hy2q, hy2one]; simp
    exact hwne1 h1
  have hdistinct : (y1 : G) ≠ (y2 : G) := by
    intro hcon
    have hy12 : y1 = y2 := Subtype.ext hcon
    have h1 : q2 = q3 * q2 * q3⁻¹ := by rw [← hy2q, ← hy1q, hy12]
    exact hwne_q2 h1.symm
  exact ⟨(x3 : G), (y1 : G), (y2 : G), hx3mem, hx3ord, hy1mem, hy1ord, hy2mem, hy2ord,
    hdistinct⟩

end Work.CORE3
