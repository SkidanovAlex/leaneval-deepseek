import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_mem_or
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_index_zpowers_tau
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_sq_eq_of_notMem
import Submission.Work.BrauerSuzuki.Quaternion.coset_cover
import Submission.Work.BrauerSuzuki.Q8.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four
import Submission.Work.BrauerSuzuki.Q8.sylow_two_structure_and_centralizer
import Submission.Work.BrauerSuzuki.Sylow.hasFrobeniusCondition_two_of_cyclic_sylow
import Submission.Work.BrauerSuzuki.Q8.tau_conj_rho_pow
import Submission.Work.BrauerSuzuki.Q8.card_rho_tau_pow_le_four
import Submission.Work.BrauerSuzuki.Q8.mulAut_eq_one_of_odd_order_of_mem_zpowers_tau
import Submission.Work.BrauerSuzuki.Q8.isConjPGroup_two_of_le_sylow_ne
import Submission.Work.BrauerSuzuki.Q8.exists_mem_sylow_conj_of_orderOf_eq_four
import Submission.Work.NPC.All
import Submission.Work.NPC.Frobenius.hasFrobeniusCondition_iff_forall_le_sylow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Q8


open scoped Pointwise

/-- If `a`, `b` are conjugate inside a subgroup `H ≤ G` then they are conjugate in `G`. -/
private theorem isConj_of_coe_subtype {G : Type*} [Group G] {H : Subgroup G} {a b : ↥H}
    (h : IsConj a b) : IsConj ((a : ↥H) : G) ((b : ↥H) : G) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine isConj_iff.mpr ⟨((c : ↥H) : G), ?_⟩
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val hc

/-- The crux: if an element `g` of `G` induces on the Sylow `2`-subgroup `S ≅ Q₈`
an automorphism `σ` of odd prime order `p`, then all elements of order `4` of `G` are
conjugate. -/
private theorem crux {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2)
    {g : G} {σ : MulAut ↥S} (hσ : ∀ x : ↥S, (σ x : G) = g * (x : G) * g⁻¹)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hord : orderOf σ = p) :
    ∀ y z : G, orderOf y = 4 → orderOf z = 4 → IsConj y z := by
  classical
  have hp3 : 3 ≤ p := by have h := hp.two_le; omega
  have hσp : σ ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one σ
  have htau4 : orderOf d.tau = 4 := by rw [d.tau_order, h2]; norm_num
  have hτinv : d.tau⁻¹ = d.tau ^ 3 := by
    rw [eq_comm, eq_inv_iff_mul_eq_one, ← pow_succ]
    norm_num
    rw [← htau4]; exact pow_orderOf_eq_one d.tau
  -- order of σ ^ j for 1 ≤ j < p
  have hord_pow : ∀ j : ℕ, 1 ≤ j → j < p → orderOf (σ ^ j) = p := by
    intro j hj1 hjp
    have hgcd : p.gcd j = 1 := by
      rcases hp.eq_one_or_self_of_dvd (p.gcd j) (Nat.gcd_dvd_left p j) with h | h
      · exact h
      · exfalso
        have hpdvd : p ∣ j := h ▸ Nat.gcd_dvd_right p j
        have := Nat.le_of_dvd (by omega) hpdvd
        omega
    rw [orderOf_pow, hord, hgcd, Nat.div_one]
  -- σ ^ j τ ∉ ⟨τ⟩ for 1 ≤ j < p
  have hmem_not : ∀ j : ℕ, 1 ≤ j → j < p → (σ ^ j) d.tau ∉ Subgroup.zpowers d.tau := by
    intro j hj1 hjp hmem
    have hodd : Odd (orderOf (σ ^ j)) := by
      rw [hord_pow j hj1 hjp]; exact hp.odd_of_ne_two hp2
    have hone : σ ^ j = 1 := mulAut_eq_one_of_odd_order_of_mem_zpowers_tau d h2 hodd hmem
    have : orderOf (σ ^ j) = 1 := by rw [hone, orderOf_one]
    rw [hord_pow j hj1 hjp] at this
    omega
  -- distinctness of σ ^ i τ for different i
  have hD1 : ∀ i j : ℕ, 1 ≤ i → i < p → 1 ≤ j → j < p → i ≠ j →
      (σ ^ i) d.tau ≠ (σ ^ j) d.tau := by
    intro i j hi1 hip hj1 hjp hijne h
    rcases lt_or_gt_of_ne hijne with hij | hji
    · have hsplit : σ ^ j = σ ^ i * σ ^ (j - i) := by
        rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hij)]
      have h1 : d.tau = (σ ^ (j - i)) d.tau := by
        have h2' : (σ ^ i) d.tau = (σ ^ i) ((σ ^ (j - i)) d.tau) := by
          rw [← MulAut.mul_apply, ← hsplit]; exact h
        exact (σ ^ i).injective h2'
      exact hmem_not (j - i) (by omega) (by omega) (h1 ▸ Subgroup.mem_zpowers d.tau)
    · have hsplit : σ ^ i = σ ^ j * σ ^ (i - j) := by
        rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hji)]
      have h1 : d.tau = (σ ^ (i - j)) d.tau := by
        have h2' : (σ ^ j) d.tau = (σ ^ j) ((σ ^ (i - j)) d.tau) := by
          rw [← MulAut.mul_apply, ← hsplit]; exact h.symm
        exact (σ ^ j).injective h2'
      exact hmem_not (i - j) (by omega) (by omega) (h1 ▸ Subgroup.mem_zpowers d.tau)
  -- (σ τ)⁻¹ is not among the σ^j τ (1 ≤ j < p)
  have hD3 : ∀ j : ℕ, 1 ≤ j → j < p → (σ ^ j) d.tau ≠ (σ d.tau)⁻¹ := by
    intro j hj1 hjp h'
    have hval0 : (σ ^ (p - 1) * σ ^ j) d.tau = d.tau⁻¹ := by
      rw [MulAut.mul_apply, h', map_inv, ← MulAut.mul_apply,
        show σ ^ (p - 1) * σ = σ ^ p from by
          rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ p by omega)],
        hσp, MulAut.one_apply]
    have hval : (σ ^ ((p - 1) + j)) d.tau = d.tau⁻¹ := by
      rw [pow_add]; exact hval0
    set e := ((p - 1) + j) % p with he
    have hpow : σ ^ ((p - 1) + j) = σ ^ e := by
      rw [pow_eq_pow_iff_modEq, hord]
      exact (Nat.mod_modEq _ _).symm
    have hval' : (σ ^ e) d.tau = d.tau⁻¹ := by rw [← hpow]; exact hval
    have he_lt : e < p := Nat.mod_lt _ hp.pos
    rcases Nat.eq_zero_or_pos e with he0 | hepos
    · rw [he0, pow_zero, MulAut.one_apply] at hval'
      have h2 : d.tau * d.tau = 1 := by
        have hh := mul_inv_cancel d.tau
        rwa [← hval'] at hh
      have hdvd : orderOf d.tau ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]; rw [pow_two]; exact h2
      rw [htau4] at hdvd
      omega
    · exact hmem_not e hepos he_lt
        (by rw [hval']; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers d.tau))
  -- the "outside" set W
  let W : Set ↥S := {x | ∃ i : ℕ, x = d.rho * d.tau ^ i}
  have htoW : ∀ x : ↥S, x ∉ Subgroup.zpowers d.tau → x ∈ W := by
    intro x hx
    rcases Work.BrauerSuzuki.Quaternion.genQuaternionData_mem_or ↥S d x with hh | hh
    · exact absurd hh hx
    · exact hh
  have hWcard : Nat.card ↥W ≤ 4 := card_rho_tau_pow_le_four d h2
  have hu_notmem : σ d.tau ∉ Subgroup.zpowers d.tau := hmem_not 1 le_rfl (by omega)
  -- the injection (Fin (p-1) ⊕ Unit) → W
  let f : Fin (p - 1) ⊕ Unit → ↥W := fun q => match q with
    | Sum.inl j => ⟨(σ ^ ((j : ℕ) + 1)) d.tau,
        htoW _ (hmem_not ((j : ℕ) + 1) (by omega) (by omega))⟩
    | Sum.inr _ => ⟨(σ d.tau)⁻¹,
        htoW _ (fun hh => hu_notmem (by simpa using Subgroup.inv_mem _ hh))⟩
  have hfinj : Function.Injective f := by
    intro q1 q2 hq
    match q1, q2 with
    | Sum.inl j1, Sum.inl j2 =>
        have h' : (σ ^ ((j1 : ℕ) + 1)) d.tau = (σ ^ ((j2 : ℕ) + 1)) d.tau :=
          congrArg Subtype.val hq
        have : (j1 : ℕ) + 1 = (j2 : ℕ) + 1 := by
          by_contra hne
          exact hD1 ((j1:ℕ)+1) ((j2:ℕ)+1) (by omega) (by omega) (by omega) (by omega) hne h'
        rw [Sum.inl.injEq]; exact Fin.ext (by omega)
    | Sum.inl j, Sum.inr _ =>
        have h' : (σ ^ ((j : ℕ) + 1)) d.tau = (σ d.tau)⁻¹ := congrArg Subtype.val hq
        exact absurd h' (hD3 ((j:ℕ)+1) (by omega) (by omega))
    | Sum.inr _, Sum.inl j =>
        have h' : (σ d.tau)⁻¹ = (σ ^ ((j : ℕ) + 1)) d.tau := congrArg Subtype.val hq
        exact absurd h'.symm (hD3 ((j:ℕ)+1) (by omega) (by omega))
    | Sum.inr _, Sum.inr _ => rfl
  have hp_le4 : p ≤ 4 := by
    have hcard := Nat.card_le_card_of_injective f hfinj
    have h1 : Nat.card (Fin (p - 1) ⊕ Unit) = p := by
      rw [Nat.card_sum, Nat.card_fin]
      have : Nat.card Unit = 1 := by simp
      rw [this]
      omega
    rw [h1] at hcard
    omega
  have hp_eq : p = 3 := by
    have hodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
    omega
  have hσ3 : σ ^ 3 = 1 := by rw [← hp_eq]; exact hσp
  -- now the final conjugacy step
  have hv_notmem : (σ ^ 2) d.tau ∉ Subgroup.zpowers d.tau := hmem_not 2 (by norm_num) (by omega)
  have hu4 : orderOf (σ d.tau) = 4 := by rw [MulEquiv.orderOf_eq, htau4]
  have hv4 : orderOf ((σ ^ 2) d.tau) = 4 := by rw [MulEquiv.orderOf_eq, htau4]
  have hu_ne_huinv : σ d.tau ≠ (σ d.tau)⁻¹ := by
    intro h
    have h2 : (σ d.tau) * (σ d.tau) = 1 := by
      have hh := mul_inv_cancel (σ d.tau)
      rwa [← h] at hh
    have hdvd : orderOf (σ d.tau) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact h2
    rw [hu4] at hdvd; omega
  have hv_ne_hvinv : (σ ^ 2) d.tau ≠ ((σ ^ 2) d.tau)⁻¹ := by
    intro h
    have h2 : ((σ ^ 2) d.tau) * ((σ ^ 2) d.tau) = 1 := by
      have hh := mul_inv_cancel ((σ ^ 2) d.tau)
      rwa [← h] at hh
    have hdvd : orderOf ((σ ^ 2) d.tau) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact h2
    rw [hv4] at hdvd; omega
  have hmul2 : (σ ^ 2) d.tau = σ (σ d.tau) := MulAut.mul_apply ↥S σ σ d.tau
  have hu_ne_v : σ d.tau ≠ (σ ^ 2) d.tau := by
    intro h
    have h' : d.tau = σ d.tau := by
      have hh := congrArg (fun x => σ.symm x) h
      simpa [hmul2] using hh
    exact hu_notmem (h' ▸ Subgroup.mem_zpowers d.tau)
  have hu_ne_vinv : σ d.tau ≠ ((σ ^ 2) d.tau)⁻¹ := by
    intro h
    have h1 : (σ d.tau)⁻¹ = (σ ^ 2) d.tau := by simpa using congrArg Inv.inv h
    have h2 : (σ ^ 2) d.tau = σ (d.tau ^ 3) := by rw [← h1, ← map_inv, hτinv]
    have h3 : σ d.tau = d.tau ^ 3 := by
      have hh := congrArg (fun x => σ.symm x) h2
      simpa [hmul2] using hh
    rw [h3] at hu_notmem
    exact hu_notmem (Subgroup.npow_mem_zpowers d.tau 3)
  have huinv_ne_v : (σ d.tau)⁻¹ ≠ (σ ^ 2) d.tau := fun h => hu_ne_vinv (by rw [← h, inv_inv])
  have huinv_ne_vinv : (σ d.tau)⁻¹ ≠ ((σ ^ 2) d.tau)⁻¹ := fun h => hu_ne_v (inv_injective h)
  -- W is exactly the four elements
  have hW'sub : ({σ d.tau, (σ d.tau)⁻¹, (σ ^ 2) d.tau, ((σ ^ 2) d.tau)⁻¹} : Set ↥S) ⊆ W := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact htoW _ hu_notmem
    · exact htoW _ (fun hh => hu_notmem (by simpa using Subgroup.inv_mem _ hh))
    · exact htoW _ hv_notmem
    · exact htoW _ (fun hh => hv_notmem (by simpa using Subgroup.inv_mem _ hh))
  have hW'card : ({σ d.tau, (σ d.tau)⁻¹, (σ ^ 2) d.tau, ((σ ^ 2) d.tau)⁻¹} : Set ↥S).ncard = 4 := by
    have hnot1 : σ d.tau ∉ ({((σ d.tau)⁻¹), ((σ ^ 2) d.tau), (((σ ^ 2) d.tau)⁻¹)} : Set ↥S) := by
      simp [hu_ne_huinv, hu_ne_v, hu_ne_vinv]
    have hnot2 : (σ d.tau)⁻¹ ∉ ({((σ ^ 2) d.tau), (((σ ^ 2) d.tau)⁻¹)} : Set ↥S) := by
      simp [huinv_ne_v, huinv_ne_vinv]
    have hnot3 : (σ ^ 2) d.tau ∉ ({(((σ ^ 2) d.tau)⁻¹)} : Set ↥S) := by
      simpa using hv_ne_hvinv
    rw [Set.ncard_insert_of_notMem hnot1, Set.ncard_insert_of_notMem hnot2,
      Set.ncard_insert_of_notMem hnot3, Set.ncard_singleton]
  have hWeq : ({σ d.tau, (σ d.tau)⁻¹, (σ ^ 2) d.tau, ((σ ^ 2) d.tau)⁻¹} : Set ↥S) = W := by
    refine Set.eq_of_subset_of_ncard_le hW'sub ?_
    rw [hW'card, ← Nat.card_coe_set_eq]
    exact hWcard
  -- conjugacy facts
  have hconj_u : IsConj ((σ d.tau : ↥S) : G) ((d.tau : ↥S) : G) :=
    (isConj_iff.mpr ⟨g, (hσ d.tau).symm⟩).symm
  have hσu' : (((σ ^ 2) d.tau : ↥S) : G) = g * ((σ d.tau : ↥S) : G) * g⁻¹ := by
    have hh := hσ (σ d.tau)
    rwa [← hmul2] at hh
  have hconj_uv : IsConj ((σ d.tau : ↥S) : G) (((σ ^ 2) d.tau : ↥S) : G) :=
    isConj_iff.mpr ⟨g, hσu'.symm⟩
  have hconj_v : IsConj (((σ ^ 2) d.tau : ↥S) : G) ((d.tau : ↥S) : G) := hconj_uv.symm.trans hconj_u
  obtain ⟨iu, hiu⟩ : ∃ i : ℕ, σ d.tau = d.rho * d.tau ^ i := by
    rcases Work.BrauerSuzuki.Quaternion.genQuaternionData_mem_or ↥S d (σ d.tau) with hh | hh
    · exact absurd hh hu_notmem
    · exact hh
  have huinv_conj : IsConj (((σ d.tau : ↥S)) : G) ((((σ d.tau)⁻¹ : ↥S)) : G) :=
    isConj_of_coe_subtype (a := σ d.tau) (b := (σ d.tau)⁻¹) (by
      have key := tau_conj_rho_pow d h2 iu
      rw [← hiu] at key
      exact isConj_iff.mpr ⟨d.tau, key⟩)
  have hconj_uinv : IsConj ((((σ d.tau)⁻¹ : ↥S)) : G) ((d.tau : ↥S) : G) :=
    huinv_conj.symm.trans hconj_u
  obtain ⟨iv, hiv⟩ : ∃ i : ℕ, (σ ^ 2) d.tau = d.rho * d.tau ^ i := by
    rcases Work.BrauerSuzuki.Quaternion.genQuaternionData_mem_or ↥S d ((σ ^ 2) d.tau) with hh | hh
    · exact absurd hh hv_notmem
    · exact hh
  have hvinv_conj : IsConj ((((σ ^ 2) d.tau : ↥S)) : G) (((((σ ^ 2) d.tau)⁻¹ : ↥S)) : G) :=
    isConj_of_coe_subtype (a := (σ ^ 2) d.tau) (b := ((σ ^ 2) d.tau)⁻¹)
      (isConj_iff.mpr ⟨d.tau, by
        have key := tau_conj_rho_pow d h2 iv
        rw [← hiv] at key
        exact key⟩)
  have hconj_vinv : IsConj (((((σ ^ 2) d.tau)⁻¹ : ↥S)) : G) ((d.tau : ↥S) : G) :=
    hvinv_conj.symm.trans hconj_v
  -- every element of ↥S of order 4 is conjugate to τ
  have hS_conj : ∀ x : ↥S, orderOf x = 4 → IsConj ((x : ↥S) : G) ((d.tau : ↥S) : G) := by
    intro x hx4
    by_cases hxmem : x ∈ Subgroup.zpowers d.tau
    · rcases eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four
        (G := ↥S) (x := d.tau) (y := x) htau4 hxmem hx4 with h | h
      · rw [h]
      · rw [h]
        exact (isConj_of_coe_subtype (isConj_iff.mpr ⟨d.rho, d.rho_conj⟩)).symm
    · have hxW : x ∈ W := htoW x hxmem
      rw [← hWeq] at hxW
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxW
      rcases hxW with h | h | h | h
      · rw [h]; exact hconj_u
      · rw [h]; exact hconj_uinv
      · rw [h]; exact hconj_v
      · rw [h]; exact hconj_vinv
  intro y z hy4 hz4
  obtain ⟨x, hxS, hx4, hyx⟩ := exists_mem_sylow_conj_of_orderOf_eq_four S hy4
  obtain ⟨x', hx'S, hx'4, hzx⟩ := exists_mem_sylow_conj_of_orderOf_eq_four S hz4
  have hxconj : IsConj x ((d.tau : ↥S) : G) := by
    have := hS_conj ⟨x, hxS⟩ (by rw [Subgroup.orderOf_mk]; exact hx4)
    simpa using this
  have hx'conj : IsConj x' ((d.tau : ↥S) : G) := by
    have := hS_conj ⟨x', hx'S⟩ (by rw [Subgroup.orderOf_mk]; exact hx'4)
    simpa using this
  have hzconj : IsConj z ((d.tau : ↥S) : G) := hzx.trans hx'conj
  exact (hyx.trans hxconj).trans hzconj.symm

theorem step4b_frobenius {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2)
    (hnot : ∃ y z : G, orderOf y = 4 ∧ orderOf z = 4 ∧ ¬ IsConj y z) :
    Work.NPC.HasFrobeniusCondition 2 G := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Work.NPC.Frobenius.hasFrobeniusCondition_iff_forall_le_sylow (p := 2) S]
  intro Q hQle hQne
  by_cases hQS : Q = (S : Subgroup G)
  · rw [hQS]
    unfold Work.NPC.IsConjPGroup
    let φ : ↥(Subgroup.normalizer ((S : Subgroup G) : Set G)) →* MulAut ↥(S : Subgroup G) :=
      Subgroup.normalizerMonoidHom (S : Subgroup G)
    have hkey : IsPGroup 2 ↥φ.range := by
      refine IsPGroup.iff_orderOf.mpr fun x => ?_
      by_contra hx
      push_neg at hx
      obtain ⟨g, hg⟩ := x.2
      have hxord : orderOf x = orderOf (φ g) := by
        have h1 := Subgroup.orderOf_coe x
        rw [← hg] at h1
        exact h1.symm
      have hn0 : orderOf (φ g) ≠ 0 :=
        fun h0 => (orderOf_eq_zero_iff.mp h0) (isOfFinOrder_of_finite (φ g))
      have hex : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ orderOf (φ g) := by
        by_contra hcon
        have huniq : ∀ d : ℕ, Nat.Prime d → d ∣ orderOf (φ g) → d = 2 := by
          intro d hd hdiv
          by_contra hd2
          exact hcon ⟨d, hd, hd2, hdiv⟩
        have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) hn0
          (fun {d} hd hdiv => huniq d hd hdiv)
        exact hx _ (by rw [hxord]; exact hpow)
      obtain ⟨p, hp, hp2, hpdvd⟩ := hex
      have hm_eq : orderOf ((φ g) ^ (orderOf (φ g) / p)) = p := by
        rw [orderOf_pow, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hpdvd),
          Nat.div_div_self hpdvd hn0]
      have hord' : orderOf (φ (g ^ (orderOf (φ g) / p))) = p := by
        rw [map_pow]; exact hm_eq
      obtain ⟨y, z, hy4, hz4, hnc⟩ := hnot
      refine hnc (crux S d h2
        (g := ((g ^ (orderOf (φ g) / p) : ↥(Subgroup.normalizer ((S : Subgroup G) : Set G))) : G))
        (σ := φ (g ^ (orderOf (φ g) / p))) (fun x => rfl) hp hp2 hord' y z hy4 hz4)
    have hq : IsPGroup 2 (↥(Subgroup.normalizer ((S : Subgroup G) : Set G)) ⧸ φ.ker) :=
      IsPGroup.of_equiv hkey (QuotientGroup.quotientKerEquivRange φ).symm
    exact IsPGroup.of_equiv hq
      (QuotientGroup.quotientMulEquivOfEq (Subgroup.normalizerMonoidHom_ker (S : Subgroup G)))
  · exact isConjPGroup_two_of_le_sylow_ne S d h2 Q hQle hQne hQS

end Work.BrauerSuzuki.Q8
