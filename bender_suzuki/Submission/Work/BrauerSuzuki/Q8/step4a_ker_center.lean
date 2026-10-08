import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Q8.Ctx
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic
import Submission.Work.NPC.All
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.CharCore.charKernel_subgroup
import Submission.Work.BrauerSuzuki.Q8.oddCore_centralizer_map_normalized
import Submission.Work.BrauerSuzuki.Q8.sylow_two_structure_and_centralizer
import Submission.Work.BrauerSuzuki.Q8.exists_sylow_element_not_commuting
import Submission.Work.BrauerSuzuki.Q8.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four
import Submission.Work.BrauerSuzuki.Q8.step4a_lift_ih
import Submission.Work.BrauerSuzuki.Sylow.hasFrobeniusCondition_two_of_cyclic_sylow
import Submission.Work.NPC.Frobenius.exists_sylow_subgroupOf_inf
import Submission.Work.ThreePoints.map_oddCore_le_oddCore
import Submission.Work.FeitSibley.CharQ.prodChar_Q1_kernel_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Glauberman (1974), step (4)(a): the kernel of a character cannot contain `x ^ 2`

Auxiliary lemmas for `step4a_ker_center`.  The main statement is proved at the bottom of this
file; everything above it is a helper.
-/

namespace Work.BrauerSuzuki.Q8

/-- If `x` has order `4` then `x ^ 2` has order `2`. -/
theorem step4a_orderOf_sq {G : Type*} [Group G] [Finite G] {x : G} (hx4 : orderOf x = 4) :
    orderOf (x ^ 2) = 2 := by
  have h1 : orderOf (x ^ 2) = orderOf x / (orderOf x).gcd 2 := orderOf_pow (n := 2) x
  rw [hx4] at h1
  rw [h1]
  norm_num

/-- An element of the centre of a finite group with `O(G) = ⊥` has `2`-power order: if the order
of a central element `z` had an odd part, then `⟨z⟩` would contain a nontrivial central subgroup
of odd order, contradicting `O(G) = ⊥`. -/
theorem step4a_orderOf_center_eq_two_pow {G : Type*} [Group G] [Finite G]
    (hO : Submission.Blueprint.oddCore G = ⊥) {z : G} (hz : z ∈ Subgroup.center G) :
    ∃ a : ℕ, orderOf z = 2 ^ a := by
  have hmain : ∀ n : ℕ, ∀ w : G, w ∈ Subgroup.center G → orderOf w = n → ∃ a : ℕ, n = 2 ^ a := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih w hw hn
    rcases Nat.even_or_odd n with hev | hodd
    · -- `n` even: pass to `w ^ 2`, whose order is `n / 2 < n`
      have hdiv : 2 ∣ n := even_iff_two_dvd.mp hev
      have hnpos : 0 < n := by rw [← hn]; exact orderOf_pos w
      have hw2 : w ^ 2 ∈ Subgroup.center G := Subgroup.pow_mem _ hw 2
      have hord : orderOf (w ^ 2) = n / 2 := by
        rw [orderOf_pow (n := 2), hn, Nat.gcd_eq_right hdiv]
      have hlt : n / 2 < n := Nat.div_lt_self hnpos (by norm_num)
      obtain ⟨b, hb⟩ := ih (n / 2) hlt (w ^ 2) hw2 hord
      exact ⟨b + 1, by rw [pow_succ, ← hb, Nat.div_mul_cancel hdiv]⟩
    · -- `n` odd: `⟨w⟩` is a normal subgroup of odd order `n`, hence trivial in `O(G) = ⊥`
      rcases eq_or_ne n 1 with h1 | h1
      · exact ⟨0, by rw [h1]; norm_num⟩
      · exfalso
        have hnorm : (Subgroup.zpowers w).Normal := by
          rw [Subgroup.normal_iff_map_conj_eq]
          intro g
          have hgw : ((MulAut.conj g : G →* G)) w = w := by
            calc ((MulAut.conj g : G →* G)) w = g * w * g⁻¹ := MulAut.conj_apply g w
              _ = w := by rw [(Subgroup.mem_center_iff.mp hw) g]; group
          rw [MonoidHom.map_zpowers, hgw]
        have hle : Subgroup.zpowers w ≤ Submission.Blueprint.oddCore G :=
          Work.BrauerSuzuki.OddCore.le_of_normal_odd hnorm (by
            rw [Nat.card_zpowers, hn]; exact hodd)
        have hw1 : w = 1 := by
          have hmem : w ∈ Submission.Blueprint.oddCore G := hle (Subgroup.mem_zpowers w)
          rw [hO, Subgroup.mem_bot] at hmem
          exact hmem
        rw [hw1, orderOf_one] at hn
        exact h1 hn.symm
  obtain ⟨a, ha⟩ := hmain (orderOf z) z hz rfl
  exact ⟨a, ha⟩

/-- **The centre of `G` lies in `⟨x ^ 2⟩`.**  If `z ∈ Z(G)` and `z ∉ ⟨x ^ 2⟩`, then `z` has even
order `2 ^ a` with `a ≥ 2` (odd order forces `z = 1`), and `ζ = z ^ (2 ^ (a - 2))` is a central
element of order `4` commuting with `x`; the structural lemma on `Q₈`-type Sylow subgroups
(`sylow_two_structure_and_centralizer`) then puts `ζ` in `⟨x⟩`, so `x` is a power of the central
element `ζ`, contradicting `exists_sylow_element_not_commuting`. -/
theorem step4a_center_le_zpowers_sq {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2) {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hx4 : orderOf x = 4)
    (hO : Submission.Blueprint.oddCore G = ⊥) :
    Subgroup.center G ≤ Subgroup.zpowers (x ^ 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2ord : orderOf (x ^ 2) = 2 := step4a_orderOf_sq hx4
  have hinvconj : ∀ y z : G, orderOf y = 2 → orderOf z = 2 → IsConj y z :=
    fun y z hy hz => Work.BrauerSuzuki.Q8.isConj_involutions_of_genQuaternionData S d hy hz
  have hstruct := Work.BrauerSuzuki.Q8.sylow_two_structure_and_centralizer S d h2
  intro z hz
  obtain ⟨a, ha⟩ := step4a_orderOf_center_eq_two_pow hO hz
  rcases Nat.eq_zero_or_pos a with h0 | hapos
  · -- `orderOf z = 1`, so `z = 1`
    subst h0
    rw [pow_zero] at ha
    have hz1 : z = 1 := orderOf_eq_one_iff.mp ha
    rw [hz1]
    exact Subgroup.one_mem _
  · -- `a ≥ 1`: the element of order two in `⟨z⟩` is `x ^ 2`
    have hu_center : z ^ 2 ^ (a - 1) ∈ Subgroup.center G := Subgroup.pow_mem _ hz _
    have h2a : 2 ^ (a - 1) * 2 = 2 ^ a := by
      rw [← pow_succ, show a - 1 + 1 = a by omega]
    have hu2 : (z ^ 2 ^ (a - 1)) ^ 2 = 1 := by
      rw [← pow_mul, h2a, ← ha]
      exact pow_orderOf_eq_one z
    have hu_ne : z ^ 2 ^ (a - 1) ≠ 1 := by
      intro h
      have hd : 2 ^ a ∣ 2 ^ (a - 1) := by
        rw [← ha]
        exact orderOf_dvd_iff_pow_eq_one.mpr h
      have hlt : 2 ^ (a - 1) < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) (by omega)
      exact absurd (Nat.le_of_dvd (by positivity) hd) (not_le.mpr hlt)
    have hu_ord : orderOf (z ^ 2 ^ (a - 1)) = 2 := orderOf_eq_prime hu2 hu_ne
    have hu_eq : z ^ 2 ^ (a - 1) = x ^ 2 := by
      obtain ⟨c, hc⟩ := isConj_iff.mp (hinvconj _ _ hu_ord hx2ord)
      calc z ^ 2 ^ (a - 1) = c * (z ^ 2 ^ (a - 1)) * c⁻¹ := by
            rw [(Subgroup.mem_center_iff.mp hu_center) c]
            group
        _ = x ^ 2 := hc
    rcases eq_or_ne a 1 with ha1 | ha1
    · -- `orderOf z = 2`, so `z = x ^ 2` (all involutions are conjugate, and `z` is central)
      have hz2 : orderOf z = 2 := by rw [ha1, pow_one] at ha; exact ha
      have hz_eq : z = x ^ 2 := by
        obtain ⟨c, hc⟩ := isConj_iff.mp (hinvconj _ _ hz2 hx2ord)
        calc z = c * z * c⁻¹ := by
              rw [(Subgroup.mem_center_iff.mp hz) c]
              group
          _ = x ^ 2 := hc
      rw [hz_eq]
      exact Subgroup.mem_zpowers (x ^ 2)
    · -- `a ≥ 2`: `ζ = z ^ (2 ^ (a - 2))` is central of order `4` and commutes with `x`
      exfalso
      have ha2 : 2 ≤ a := by omega
      have hzeta_center : z ^ 2 ^ (a - 2) ∈ Subgroup.center G := Subgroup.pow_mem _ hz _
      have h2b : 2 ^ (a - 2) * 2 = 2 ^ (a - 1) := by
        rw [← pow_succ, show a - 2 + 1 = a - 1 by omega]
      have h2c : 2 ^ (a - 2) * 4 = 2 ^ a := by
        rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add, show a - 2 + 2 = a by omega]
      have hzeta_sq_eq : (z ^ 2 ^ (a - 2)) ^ 2 = z ^ 2 ^ (a - 1) := by
        rw [← pow_mul, h2b]
      have hzeta_four : (z ^ 2 ^ (a - 2)) ^ 4 = 1 := by
        rw [← pow_mul, h2c, ← ha]
        exact pow_orderOf_eq_one z
      have hzeta_ne1 : z ^ 2 ^ (a - 2) ≠ 1 := by
        intro h
        have hd : 2 ^ a ∣ 2 ^ (a - 2) := by
          rw [← ha]
          exact orderOf_dvd_iff_pow_eq_one.mpr h
        have hlt : 2 ^ (a - 2) < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) (by omega)
        exact absurd (Nat.le_of_dvd (by positivity) hd) (not_le.mpr hlt)
      have hzeta_ne2 : (z ^ 2 ^ (a - 2)) ^ 2 ≠ 1 := by
        intro h
        exact hu_ne (hzeta_sq_eq ▸ h)
      have hzeta_ord : orderOf (z ^ 2 ^ (a - 2)) = 4 := by
        have hdvd : orderOf (z ^ 2 ^ (a - 2)) ∣ 4 :=
          orderOf_dvd_iff_pow_eq_one.mpr hzeta_four
        have hne1 : orderOf (z ^ 2 ^ (a - 2)) ≠ 1 :=
          fun h => hzeta_ne1 (orderOf_eq_one_iff.mp h)
        have hne2 : orderOf (z ^ 2 ^ (a - 2)) ≠ 2 := by
          intro h
          apply hzeta_ne2
          calc (z ^ 2 ^ (a - 2)) ^ 2
              = (z ^ 2 ^ (a - 2)) ^ orderOf (z ^ 2 ^ (a - 2)) := by rw [h]
            _ = 1 := pow_orderOf_eq_one _
        have hne3 : orderOf (z ^ 2 ^ (a - 2)) ≠ 3 := by
          intro h
          rw [h] at hdvd
          norm_num at hdvd
        have hle : orderOf (z ^ 2 ^ (a - 2)) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
        have hpos : 0 < orderOf (z ^ 2 ^ (a - 2)) := orderOf_pos _
        omega
      have hzeta_comm : (z ^ 2 ^ (a - 2)) * x = x * (z ^ 2 ^ (a - 2)) :=
        ((Subgroup.mem_center_iff.mp hzeta_center) x).symm
      have hmem : z ^ 2 ^ (a - 2) ∈ Subgroup.zpowers x :=
        hstruct.2.2 x hxS hx4 (z ^ 2 ^ (a - 2)) hzeta_comm ⟨2, by rw [hzeta_ord]; norm_num⟩
      have hxcent : x ∈ Subgroup.center G := by
        rcases Work.BrauerSuzuki.Q8.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four hx4 hmem
          hzeta_ord with h | h
        · rw [← h]; exact hzeta_center
        · have hxinv : x = (z ^ 2 ^ (a - 2))⁻¹ := by rw [h, inv_inv]
          rw [hxinv]
          exact Subgroup.inv_mem _ hzeta_center
      obtain ⟨s, _hsS, hsx⟩ :=
        Work.BrauerSuzuki.Q8.exists_sylow_element_not_commuting S d h2 hxS hx4
      exact hsx ((Subgroup.mem_center_iff.mp hxcent) s)

/-- In a `Q₈`-type Sylow `2`-subgroup there is an element of order `4` outside `⟨x⟩`: if
`x ∈ ⟨τ⟩` take `ρ`, otherwise take `τ`. -/
theorem step4a_exists_four_notMem_zpowers {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2) {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hx4 : orderOf x = 4) :
    ∃ y ∈ (S : Subgroup G), orderOf y = 4 ∧ y ∉ Subgroup.zpowers x := by
  have hbasic := Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d
  have htau4 : orderOf d.tau = 4 := by rw [d.tau_order, h2]; norm_num
  have hrho_notMem : d.rho ∉ Subgroup.zpowers d.tau := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hconj : d.rho * d.tau * d.rho⁻¹ = d.tau := by rw [← hk]; group
    have htau_inv : d.tau⁻¹ = d.tau := by rw [← d.rho_conj, hconj]
    have hsq : d.tau ^ 2 = 1 := by
      rw [sq, mul_eq_one_iff_inv_eq]
      exact htau_inv
    have hdvd : orderOf d.tau ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
    rw [htau4] at hdvd
    norm_num at hdvd
  have hrho4 : orderOf d.rho = 4 := (hbasic.2.2.2.2 d.rho hrho_notMem).1
  let xt : ↥S := ⟨x, hxS⟩
  have hxt4 : orderOf xt = 4 := by rw [← Subgroup.orderOf_coe xt]; exact hx4
  by_cases hmem : xt ∈ Subgroup.zpowers d.tau
  · -- `x ∈ ⟨τ⟩`: use `ρ`
    refine ⟨(d.rho : G), d.rho.2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe d.rho]; exact hrho4
    · intro hcon
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcon
      have hmem' : d.rho ∈ Subgroup.zpowers xt := by
        rw [Subgroup.mem_zpowers_iff]
        exact ⟨k, by apply Subtype.ext; show x ^ k = (d.rho : G); exact hk⟩
      exact hrho_notMem (Subgroup.zpowers_le.mpr hmem hmem')
  · -- `x ∉ ⟨τ⟩`: use `τ`
    refine ⟨(d.tau : G), d.tau.2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe d.tau]; exact htau4
    · intro hcon
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcon
      have hmem' : d.tau ∈ Subgroup.zpowers xt := by
        rw [Subgroup.mem_zpowers_iff]
        exact ⟨k, by apply Subtype.ext; show x ^ k = (d.tau : G); exact hk⟩
      rcases Work.BrauerSuzuki.Q8.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four hxt4 hmem'
        htau4 with h | h
      · exact hmem (by rw [h]; exact Subgroup.mem_zpowers xt)
      · have hxinv : xt = d.tau⁻¹ := by rw [h, inv_inv]
        exact hmem (by rw [hxinv]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers d.tau))

/-- In a finite group, membership in `zpowers` is witnessed by a *natural* power. -/
theorem step4a_mem_zpowers_iff_exists_nat {G : Type*} [Group G] [Finite G] {g h : G} :
    h ∈ Subgroup.zpowers g ↔ ∃ k : ℕ, g ^ k = h := by
  have hx : IsOfFinOrder g := isOfFinOrder_of_finite g
  constructor
  · intro hh
    exact (Submonoid.mem_powers_iff h g).mp (hx.mem_powers_iff_mem_zpowers.mpr hh)
  · rintro ⟨k, hk⟩
    exact hx.mem_powers_iff_mem_zpowers.mp ((Submonoid.mem_powers_iff h g).mpr ⟨k, hk⟩)

/-- A subgroup of a `Q₈`-type Sylow `2`-subgroup containing no element of order `4` has at most
two elements: every one of its elements is `1` or the unique involution `τ ^ 2` of `S`. -/
theorem step4a_card_le_two {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2) {R : Subgroup G}
    (hRS : R ≤ (S : Subgroup G)) (h4 : ∀ y ∈ R, orderOf y ≠ 4) : Nat.card ↥R ≤ 2 := by
  have hbasic := Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d
  have hmem : ∀ y ∈ R, y = 1 ∨ y = ((d.tau ^ 2 : ↥S) : G) := by
    intro y hy
    have hyS : y ∈ (S : Subgroup G) := hRS hy
    have hyne : orderOf y ≠ 4 := h4 y hy
    have ho : orderOf (⟨y, hyS⟩ : ↥S) = orderOf y := (Subgroup.orderOf_coe _).symm
    by_cases htau : (⟨y, hyS⟩ : ↥S) ∈ Subgroup.zpowers d.tau
    · -- `y = τ ^ k`: its order divides `4` and is not `4`, hence divides `2`
      obtain ⟨k, hk⟩ := step4a_mem_zpowers_iff_exists_nat.mp htau
      have hdvd : orderOf y ∣ 4 := by
        rw [← ho, ← hk, orderOf_pow, d.tau_order, h2]
        simpa using Nat.div_dvd_of_dvd (Nat.gcd_dvd_left 4 k)
      have h2dvd : orderOf y ∣ 2 := by
        obtain ⟨i, _hi, hieq⟩ :=
          (Nat.dvd_prime_pow (p := 2) Nat.prime_two (m := 2)).mp (by simpa using hdvd)
        interval_cases i
        · rw [hieq, pow_zero]; exact one_dvd 2
        · rw [hieq]; norm_num
        · exact absurd hieq hyne
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp h2dvd with h1 | h2'
      · left; exact orderOf_eq_one_iff.mp h1
      · right
        have hord : orderOf ((d.tau ^ 2 : ↥S)) = 2 := by
          have h := hbasic.2.2.1
          rwa [show 2 ^ (d.n - 1) = 2 by rw [h2]; norm_num] at h
        obtain ⟨z, _hz2, hzu⟩ := Work.BrauerSuzuki.Q8.hasUniqueInvolution_of_genQuaternionData d
        have hzy : (⟨y, hyS⟩ : ↥S) = z := by
          apply hzu
          rw [ho]
          exact h2'
        have hz2 : (d.tau ^ 2 : ↥S) = z := hzu _ hord
        exact congrArg Subtype.val (hzy.trans hz2.symm)
    · -- `y ∉ ⟨τ⟩` forces `orderOf y = 4`
      have h4' : orderOf y = 4 := by
        rw [← ho]
        exact (hbasic.2.2.2.2 _ htau).1
      exact absurd h4' hyne
  haveI : Fintype ↥R := Fintype.ofFinite _
  have hinj : Function.Injective (fun y : ↥R => if (y : G) = 1 then (0 : Fin 2) else 1) := by
    intro a b hab
    by_cases ha : (a : G) = 1
    · by_cases hb : (b : G) = 1
      · exact Subtype.ext (by rw [ha, hb])
      · exact absurd hab (by simp [ha, hb])
    · by_cases hb : (b : G) = 1
      · exact absurd hab (by simp [ha, hb])
      · have h1 := (hmem (a : G) a.2).resolve_left ha
        have h2' := (hmem (b : G) b.2).resolve_left hb
        exact Subtype.ext (by rw [h1, h2'])
  have hle : Fintype.card ↥R ≤ 2 := by
    have := Fintype.card_le_of_injective _ hinj
    simpa using this
  rwa [Nat.card_eq_fintype_card]

/-- In a `Q₈`-type Sylow subgroup the intersection `S ⊓ K` with a normal subgroup `K` cannot have
order `4`: either `x ∈ K` and then `S ⊓ K = ⟨x⟩`, so the order-`4` element of `S` outside `⟨x⟩`
lies outside `K` although all order-`4` elements are conjugate; or `x ∉ K`, so no order-`4`
element lies in `K`, and `S ⊓ K` has at most two elements. -/
theorem step4a_false_of_card_inf_eq_four {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (hK : K.Normal) (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2)
    {x : G} (hxS : x ∈ (S : Subgroup G)) (hx4 : orderOf x = 4)
    (hconj : ∀ y z : G, orderOf y = 4 → orderOf z = 4 → IsConj y z)
    (hcard : Nat.card ↥((S : Subgroup G) ⊓ K) = 4) : False := by
  by_cases hxK : x ∈ K
  · have hxle : Subgroup.zpowers x ≤ (S : Subgroup G) ⊓ K :=
      le_inf (Subgroup.zpowers_le.mpr hxS) (Subgroup.zpowers_le.mpr hxK)
    have hReq : (S : Subgroup G) ⊓ K = Subgroup.zpowers x := by
      symm
      refine Subgroup.eq_of_le_of_card_ge hxle ?_
      have hc4 : Nat.card ↥((S : Subgroup G) ⊓ K) = 4 := hcard
      have hx4card : Nat.card ↥(Subgroup.zpowers x) = 4 := by rw [Nat.card_zpowers, hx4]
      omega
    obtain ⟨y, hyS, hy4, hynot⟩ := step4a_exists_four_notMem_zpowers S d h2 hxS hx4
    obtain ⟨c, hc⟩ := isConj_iff.mp (hconj x y hx4 hy4)
    exact hynot (hReq ▸ ⟨hyS, hc ▸ hK.conj_mem x hxK c⟩)
  · have h4 : ∀ y ∈ (S : Subgroup G) ⊓ K, orderOf y ≠ 4 := by
      intro y hy hy4
      obtain ⟨c, hc⟩ := isConj_iff.mp (hconj y x hy4 hx4)
      exact hxK (hc ▸ hK.conj_mem y hy.2 c)
    have := step4a_card_le_two S d h2 inf_le_left h4
    omega

/-- The image under `K.subtype` of the odd core of a normal subgroup `K` lies in the odd core of
`G` (universe-polymorphic version of `Work.ThreePoints.map_oddCore_le_oddCore`). -/
theorem step4a_map_oddCore_le {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (hK : K.Normal) :
    (Submission.Blueprint.oddCore ↥K).map K.subtype ≤ Submission.Blueprint.oddCore G := by
  haveI : K.Normal := hK
  haveI : (Submission.Blueprint.oddCore ↥K).Characteristic := oddCore_characteristic
  haveI : ((Submission.Blueprint.oddCore ↥K).map K.subtype).Normal := inferInstance
  refine Work.BrauerSuzuki.OddCore.le_of_normal_odd inferInstance ?_
  rw [Subgroup.card_map_of_injective K.subtype_injective]
  exact Work.BrauerSuzuki.OddCore.oddCard_oddCore

/-- If `K ⊴ G` meets a `Q₈`-type Sylow `2`-subgroup in a group of order `2`, then `|K| = 2`:
`K` has a cyclic Sylow `2`-subgroup of order `2`, so by Frobenius' normal `2`-complement theorem
it has a normal `2`-complement `N`; `N` is an odd normal subgroup of `K`, hence
`N ≤ O(K) ≤ O(G) = ⊥`. -/
theorem step4a_card_eq_two_of_card_inf_eq_two {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) (hK : K.Normal) (S : Sylow 2 G)
    (hO : Submission.Blueprint.oddCore G = ⊥)
    (hcard : Nat.card ↥((S : Subgroup G) ⊓ K) = 2) : Nat.card ↥K = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : K.Normal := hK
  obtain ⟨T, hT⟩ := Work.NPC.Frobenius.exists_sylow_subgroupOf_inf (p := 2) S (M := K)
  have hTcard : Nat.card ↥((T : Subgroup ↥K)) = 2 := by
    rw [hT]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : K ⊓ (S : Subgroup G) ≤ K)).toEquiv]
    rw [inf_comm, hcard]
  have hcyc : IsCyclic ↥T := isCyclic_of_prime_card (p := 2) hTcard
  have hfrob : Work.NPC.HasFrobeniusCondition 2 ↥K :=
    Work.BrauerSuzuki.Sylow.hasFrobeniusCondition_two_of_cyclic_sylow T hcyc
  obtain ⟨N, hN⟩ := Work.NPC.frobenius_npc (p := 2) hfrob
  have hNodd : Odd (Nat.card ↥N) := Nat.coprime_two_right.mp hN.coprime_card
  have hNbot : N = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro n hn
    have h1 : (n : G) ∈ Subgroup.map K.subtype (Submission.Blueprint.oddCore ↥K) :=
      Subgroup.mem_map.mpr ⟨n,
        Work.BrauerSuzuki.OddCore.le_of_normal_odd hN.normal hNodd hn, rfl⟩
    have hmap := step4a_map_oddCore_le hK
    have h2 : (n : G) ∈ Submission.Blueprint.oddCore G := hmap h1
    rw [hO, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hTtop : (T : Subgroup ↥K) = ⊤ := by
    have hsup := (Work.NPC.Basic.isNormalPComplement_complement_sylow hN T).sup_eq_top
    rwa [hNbot, bot_sup_eq] at hsup
  have hcardK : Nat.card ↥((T : Subgroup ↥K)) = Nat.card ↥K := by
    rw [hTtop, Subgroup.card_top]
  rw [← hcardK, hTcard]

/-- In a group, the cyclic subgroup generated by an element of order `2` consists of `1` and
that element. -/
theorem step4a_mem_zpowers_of_orderOf_eq_two {G : Type*} [Group G] [Finite G] {a z : G}
    (ha : orderOf a = 2) (hz : z ∈ Subgroup.zpowers a) : z = 1 ∨ z = a := by
  obtain ⟨k, hk⟩ := step4a_mem_zpowers_iff_exists_nat.mp hz
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  rcases Nat.even_or_odd k with hev | hodd
  · obtain ⟨m, hm⟩ := hev
    left
    rw [← hk, hm, ← two_mul, pow_mul, ha2, one_pow]
  · obtain ⟨m, hm⟩ := hodd
    right
    rw [← hk, hm, pow_succ, pow_mul, ha2, one_pow, one_mul]

/-- **The `S ≤ K` case.**  If the `Q₈`-type Sylow `2`-subgroup `S` of `G` is contained in a
proper normal subgroup `K`, then `S` is a Sylow `2`-subgroup of `K`; the induction hypothesis
applied to `K` (whose odd core is trivial because `O(K) ≤ O(G) = ⊥`) shows that `x ^ 2` is central
in `K`, and `Z(K)` is characteristic in `K ⊴ G`.  Since `Z(K) ≤ Z(S) = ⟨x ^ 2⟩`, the subgroup
`⟨x ^ 2⟩` is normal in `G`, hence `x ^ 2 ∈ Z(G)`. -/
theorem step4a_sq_mem_center_of_le_sylow {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (hK : K.Normal) (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2)
    (hSK : (S : Subgroup G) ≤ K) (hO : Submission.Blueprint.oddCore G = ⊥) (hKne : K ≠ ⊤)
    {x : G} (hxS : x ∈ (S : Subgroup G)) (hx4 : orderOf x = 4)
    (hIH : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G →
      ∀ (T : Sylow 2 H) (e : Work.BrauerSuzuki.GenQuaternionData ↥T), e.n = 2 →
      ∀ y : H, y ∈ (T : Subgroup H) → orderOf y = 4 →
      ∀ k : H, y ^ 2 * k * (y ^ 2)⁻¹ * k⁻¹ ∈ Submission.Blueprint.oddCore H) :
    x ^ 2 ∈ Subgroup.center G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : K.Normal := hK
  -- `K` is a proper subgroup
  have hKcard : Nat.card ↥K < Nat.card G := by
    rcases lt_or_ge (Nat.card ↥K) (Nat.card G) with h | h
    · exact h
    · exfalso
      have hle : Nat.card ↥(⊤ : Subgroup G) ≤ Nat.card ↥K := by
        rw [Subgroup.card_top]; exact h
      exact hKne (Subgroup.eq_of_le_of_card_ge le_top hle)
  -- the Sylow `2`-subgroup of `K` induced by `S`, carrying `Q₈` data
  let T : Sylow 2 ↥K := S.subtype hSK
  have hT : (T : Subgroup ↥K) = (S : Subgroup G).subgroupOf K := Sylow.coe_subtype S hSK
  have e₀ : ↥T ≃* ↥S := (MulEquiv.subgroupCongr hT).trans (Subgroup.subgroupOfEquivOfLe hSK)
  let e : Work.BrauerSuzuki.GenQuaternionData ↥T :=
    { n := d.n
      hn := d.hn
      tau := e₀.symm d.tau
      rho := e₀.symm d.rho
      tau_order := by rw [MulEquiv.orderOf_eq, d.tau_order]
      rho_conj := by
        have hc := congrArg e₀.symm d.rho_conj
        simpa [map_mul, map_inv] using hc
      rho_sq := by rw [← map_pow, ← map_pow, d.rho_sq]
      closure_eq_top := by
        rw [show ({e₀.symm d.tau, e₀.symm d.rho} : Set ↥T) =
            (e₀.symm : ↥S →* ↥T) '' ({d.tau, d.rho} : Set ↥S) from by ext q; simp,
          ← MonoidHom.map_closure (e₀.symm : ↥S →* ↥T), d.closure_eq_top, Subgroup.map_top,
          MonoidHom.range_eq_top.mpr e₀.symm.surjective] }
  have he2 : e.n = 2 := h2
  -- `O(K) = ⊥`
  have hOK : Submission.Blueprint.oddCore ↥K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have h1 : (z : G) ∈ Subgroup.map K.subtype (Submission.Blueprint.oddCore ↥K) :=
      Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    have h2' : (z : G) ∈ Submission.Blueprint.oddCore G := step4a_map_oddCore_le hK h1
    rw [hO, Subgroup.mem_bot] at h2'
    exact Subtype.ext h2'
  -- the element of `T` corresponding to `x`, and the induction hypothesis at `K`
  let xK : ↥K := ⟨x, hSK hxS⟩
  have hxK4 : orderOf xK = 4 := by rw [← Subgroup.orderOf_coe xK]; exact hx4
  have hxT_mem : xK ∈ (T : Subgroup ↥K) := by
    rw [hT, Subgroup.mem_subgroupOf]
    exact hxS
  have hIHK : ∀ k : ↥K, xK ^ 2 * k * (xK ^ 2)⁻¹ * k⁻¹ ∈ Submission.Blueprint.oddCore ↥K :=
    fun k => step4a_lift_ih hIH ↥K hKcard T e he2 xK hxT_mem hxK4 k
  -- `x ^ 2` is central in `K`
  have hxK_center : (xK ^ 2 : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    have hcomm : xK ^ 2 * k * (xK ^ 2)⁻¹ * k⁻¹ ∈ Submission.Blueprint.oddCore ↥K := hIHK k
    rw [hOK, Subgroup.mem_bot] at hcomm
    have h3 : xK ^ 2 * k * (xK ^ 2)⁻¹ = k := by
      have := congrArg (fun t : ↥K => t * k) hcomm
      simpa [mul_assoc] using this
    calc k * xK ^ 2 = (xK ^ 2 * k * (xK ^ 2)⁻¹) * xK ^ 2 := by rw [h3]
      _ = xK ^ 2 * k := by group
  -- the upper bound at `K` gives `Z(K) = ⟨x ^ 2⟩`
  have hupper : Subgroup.center ↥K ≤ Subgroup.zpowers (xK ^ 2) :=
    step4a_center_le_zpowers_sq T e he2 hxT_mem hxK4 hOK
  have hcenter_K : Subgroup.center ↥K = Subgroup.zpowers (xK ^ 2) :=
    le_antisymm hupper (Subgroup.zpowers_le.mpr hxK_center)
  -- whose image in `G` is `⟨x ^ 2⟩`, a normal subgroup of `G`
  have hmap_eq : (Subgroup.center ↥K).map K.subtype = Subgroup.zpowers (x ^ 2) := by
    rw [hcenter_K, MonoidHom.map_zpowers]
    have : K.subtype (xK ^ 2) = x ^ 2 := by rw [map_pow]; rfl
    rw [this]
  have hnorm_z2 : (Subgroup.zpowers (x ^ 2)).Normal := by
    have hnorm : ((Subgroup.center ↥K).map K.subtype).Normal := inferInstance
    rwa [hmap_eq] at hnorm
  -- hence `x ^ 2` is central in `G`
  refine Subgroup.mem_center_iff.mpr fun g => ?_
  have hmem : g * x ^ 2 * g⁻¹ ∈ Subgroup.zpowers (x ^ 2) :=
    hnorm_z2.conj_mem (x ^ 2) (Subgroup.mem_zpowers (x ^ 2)) g
  have hne : g * x ^ 2 * g⁻¹ ≠ 1 := by
    intro h1
    have h2' : orderOf (g * x ^ 2 * g⁻¹) = 2 := by
      have hconjeq : g * x ^ 2 * g⁻¹ = (MulAut.conj g) (x ^ 2) := by rw [MulAut.conj_apply]
      rw [hconjeq, MulEquiv.orderOf_eq (MulAut.conj g) (x ^ 2), step4a_orderOf_sq hx4]
    rw [h1, orderOf_one] at h2'
    omega
  have hconj : g * x ^ 2 * g⁻¹ = x ^ 2 := by
    rcases step4a_mem_zpowers_of_orderOf_eq_two (step4a_orderOf_sq hx4) hmem with h | h
    · exact absurd h hne
    · exact h
  calc g * x ^ 2 = g * x ^ 2 * g⁻¹ * g := by group
    _ = x ^ 2 * g := by rw [hconj]

/-- An irreducible complex character which is constant (equal to its value at `1`) is the
principal character (universe-polymorphic version of
`Work.FeitSibley.CharQ.eq_principal_of_irr_of_constant`). -/
theorem step4a_eq_one_of_irr_const {G : Type*} [Group G] [Fintype G] {θ : G → ℂ}
    (hθ : θ ∈ Work.CharCore.Irr G) (hconst : ∀ x : G, θ x = θ 1) :
    θ = fun _ => 1 := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hself : Work.CharCore.cfInner θ θ = 1 := by
    simpa using Work.CharCore.irr_orthonormal θ θ hθ hθ
  have hsum : (∑ x : G, θ x * starRingEnd ℂ (θ x)) =
      (Fintype.card G : ℂ) * (θ 1 * starRingEnd ℂ (θ 1)) := by
    calc (∑ x : G, θ x * starRingEnd ℂ (θ x))
        = ∑ _x : G, θ 1 * starRingEnd ℂ (θ 1) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hconst x]
      _ = (Fintype.card G) • (θ 1 * starRingEnd ℂ (θ 1)) := Finset.sum_const _
      _ = (Fintype.card G : ℂ) * (θ 1 * starRingEnd ℂ (θ 1)) := by
          rw [nsmul_eq_mul]
  have hprod : θ 1 * starRingEnd ℂ (θ 1) = 1 := by
    have h := hself
    rw [Work.CharCore.cfInner, hsum, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul] at h
    exact h
  have hne : θ 1 ≠ 0 := by
    intro h0
    rw [h0, map_zero, mul_zero] at hprod
    exact one_ne_zero hprod.symm
  have hcf : Work.CharCore.cfInner θ (fun _ : G => (1 : ℂ)) = θ 1 := by
    rw [Work.CharCore.cfInner]
    have hsum2 : (∑ x : G, θ x * starRingEnd ℂ ((fun _ : G => (1 : ℂ)) x)) =
        (Fintype.card G : ℂ) * θ 1 := by
      calc (∑ x : G, θ x * starRingEnd ℂ ((fun _ : G => (1 : ℂ)) x))
          = ∑ _x : G, θ 1 * 1 := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [hconst x]
            simp
        _ = (Fintype.card G) • (θ 1 * 1) := Finset.sum_const _
        _ = (Fintype.card G : ℂ) * θ 1 := by
            rw [nsmul_eq_mul]
            ring
    rw [hsum2, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  by_cases h : θ = fun _ : G => 1
  · exact h
  · have hprin := Work.CharCore.irr_orthonormal θ (fun _ : G => (1 : ℂ)) hθ
        Work.CharCore.principalChar_mem_Irr
    have hzero : (if θ = (fun _ : G => 1) then (1 : ℂ) else 0) = 0 := by simp [h]
    rw [hcf, hzero] at hprin
    exact absurd hprin hne

/-- If `⟨x ^ 2⟩` is normal in `G`, then `x ^ 2` is central: the only elements of `⟨x ^ 2⟩` are
`1` and `x ^ 2`, and a conjugate of `x ^ 2` is an involution, hence not `1`. -/
theorem step4a_mem_center_of_zpowers_normal {G : Type*} [Group G] [Finite G] {x : G}
    (hx4 : orderOf x = 4) (hnorm : (Subgroup.zpowers (x ^ 2)).Normal) :
    x ^ 2 ∈ Subgroup.center G := by
  refine Subgroup.mem_center_iff.mpr fun g => ?_
  have hmem : g * x ^ 2 * g⁻¹ ∈ Subgroup.zpowers (x ^ 2) :=
    hnorm.conj_mem (x ^ 2) (Subgroup.mem_zpowers (x ^ 2)) g
  have hne1 : g * x ^ 2 * g⁻¹ ≠ 1 := by
    intro h1
    have h2 : orderOf (g * x ^ 2 * g⁻¹) = 2 := by
      rw [show g * x ^ 2 * g⁻¹ = (MulAut.conj g) (x ^ 2) by rw [MulAut.conj_apply]]
      rw [MulEquiv.orderOf_eq (MulAut.conj g) (x ^ 2), step4a_orderOf_sq hx4]
    rw [h1, orderOf_one] at h2
    omega
  have hconj_eq : g * x ^ 2 * g⁻¹ = x ^ 2 := by
    rcases step4a_mem_zpowers_of_orderOf_eq_two (step4a_orderOf_sq hx4) hmem with h | h
    · exact absurd h hne1
    · exact h
  calc g * x ^ 2 = g * x ^ 2 * g⁻¹ * g := by group
    _ = x ^ 2 * g := by rw [hconj_eq]

open Classical in
theorem step4a_ker_center {G : Type*} [Group G] [Fintype G]
    (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2)
    (x : G) (hxS : x ∈ (S : Subgroup G)) (hx4 : orderOf x = 4)
    (hO : Submission.Blueprint.oddCore G = ⊥)
    (hconj : ∀ y z : G, orderOf y = 4 → orderOf z = 4 → IsConj y z)
    (hIH : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G →
      ∀ (T : Sylow 2 H) (e : Work.BrauerSuzuki.GenQuaternionData ↥T), e.n = 2 →
      ∀ y : H, y ∈ (T : Subgroup H) → orderOf y = 4 →
      ∀ k : H, y ^ 2 * k * (y ^ 2)⁻¹ * k⁻¹ ∈ Submission.Blueprint.oddCore H)
    {χ : G → ℂ} (hχ : χ ∈ Work.CharCore.Irr G) (hne : χ ≠ (fun _ => (1 : ℂ)))
    (hker : χ (x ^ 2) = χ 1) :
    Nat.card ↥(Subgroup.center G) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `K = ker χ` is a normal subgroup containing `x ^ 2`
  obtain ⟨K, hKnorm, hKset⟩ := Work.CharCore.charKernel_subgroup hχ
  haveI : K.Normal := hKnorm
  have hx2K : x ^ 2 ∈ K := by
    rw [← SetLike.mem_coe, hKset, Work.CharCore.charKernel]
    exact hker
  have hKne : K ≠ ⊤ := by
    intro htop
    refine hne (step4a_eq_one_of_irr_const hχ fun g => ?_)
    have hg : g ∈ K := htop ▸ Subgroup.mem_top g
    rw [← SetLike.mem_coe, hKset, Work.CharCore.charKernel] at hg
    exact hg
  -- the centre of `G` lies in `⟨x ^ 2⟩`, so it suffices to show `x ^ 2 ∈ Z(G)`
  have hupper : Subgroup.center G ≤ Subgroup.zpowers (x ^ 2) :=
    step4a_center_le_zpowers_sq S d h2 hxS hx4 hO
  have hcardS : Nat.card ↥(S : Subgroup G) = 8 := by
    have h := (Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d).1
    have hpow : (2 : ℕ) ^ (d.n + 1) = 8 := by rw [h2]; norm_num
    rw [hpow] at h
    exact h
  have key : x ^ 2 ∈ Subgroup.center G := by
    have hx2ord : orderOf (x ^ 2) = 2 := step4a_orderOf_sq hx4
    have hdvd : Nat.card ↥((S : Subgroup G) ⊓ K) ∣ 8 := by
      rw [← hcardS]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hge : 2 ≤ Nat.card ↥((S : Subgroup G) ⊓ K) := by
      have hle : Subgroup.zpowers (x ^ 2) ≤ (S : Subgroup G) ⊓ K :=
        le_inf (Subgroup.zpowers_le.mpr ((S : Subgroup G).pow_mem hxS 2))
          (Subgroup.zpowers_le.mpr hx2K)
      calc (2 : ℕ) = Nat.card ↥(Subgroup.zpowers (x ^ 2)) := by rw [Nat.card_zpowers, hx2ord]
        _ ≤ Nat.card ↥((S : Subgroup G) ⊓ K) := Subgroup.card_le_of_le hle
    obtain ⟨i, hi, hieq⟩ :=
      (Nat.dvd_prime_pow (p := 2) Nat.prime_two (m := 3)).mp (show Nat.card ↥((S : Subgroup G) ⊓ K) ∣ 2 ^ 3 from hdvd)
    interval_cases i
    · -- `|S ⊓ K| = 1` contradicts `2 ≤ |S ⊓ K|`
      rw [pow_zero] at hieq
      omega
    · -- `|S ⊓ K| = 2`: then `K = ⟨x ^ 2⟩` is normal
      have hcard2 : Nat.card ↥((S : Subgroup G) ⊓ K) = 2 := by
        rw [hieq, show (2 : ℕ) ^ 1 = 2 from rfl]
      have hK2 : Nat.card ↥K = 2 := step4a_card_eq_two_of_card_inf_eq_two K hKnorm S hO hcard2
      have hKeq : K = Subgroup.zpowers (x ^ 2) := by
        symm
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx2K) ?_
        rw [Nat.card_zpowers, hx2ord, hK2]
      exact step4a_mem_center_of_zpowers_normal hx4 (hKeq ▸ hKnorm)
    · -- `|S ⊓ K| = 4` is impossible
      exact (step4a_false_of_card_inf_eq_four K hKnorm S d h2 hxS hx4 hconj
        (by rw [hieq, show (2 : ℕ) ^ 2 = 4 from rfl])).elim
    · -- `|S ⊓ K| = 8`, so `S ≤ K` and the induction hypothesis applies
      have h8 : Nat.card ↥((S : Subgroup G) ⊓ K) = 8 := by
        rw [hieq, show (2 : ℕ) ^ 3 = 8 from rfl]
      have hSK : (S : Subgroup G) ≤ K := by
        have heq : (S : Subgroup G) ⊓ K = (S : Subgroup G) :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, hcardS])
        exact inf_eq_left.mp heq
      exact step4a_sq_mem_center_of_le_sylow K hKnorm S d h2 hSK hO hKne hxS hx4 hIH
  have hcenter : Subgroup.center G = Subgroup.zpowers (x ^ 2) :=
    le_antisymm hupper (Subgroup.zpowers_le.mpr key)
  rw [hcenter, Nat.card_zpowers, step4a_orderOf_sq hx4]

end Work.BrauerSuzuki.Q8
