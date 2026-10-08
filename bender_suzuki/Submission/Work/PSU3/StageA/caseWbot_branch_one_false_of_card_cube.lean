import Mathlib
import Submission.Work.PSU3.StageA.caseWbot_setup
import Submission.Work.PSU3.StageB.card_centralizer_eq_cube
import Submission.Work.Frobenius.Complement.exists_fixed_of_isFpf_module
import Submission.Work.PSU3.StageA.exists_prime_dvd_pow_sub_one_not_dvd
import Submission.Work.PSU3.StageA.caseWbot_K_centralizer_card
import Submission.Work.PSU3.StageA.caseWbot_K_elt_fpf_quotient
import Submission.Work.PSU3.StageA.exists_fixed_of_fpf_elementaryAbelian

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

open scoped commutatorElement

/-- **The mod-`Q₀` fixed point (`𝔽₂`-module `Q/Q₀` version of the classical `p`-`q` lemma).**

Let `P ≤ centD H t` have prime order, let `k ∈ Ksub H t` have odd prime order and act
fixed-point-freely on `Q/Q₀`, and suppose `P` conjugates `k` to a *different* element (in
particular `⟨k⟩ ⋊ P` is non-abelian, `p ≠ q`).  Then some `x ∈ Q ∖ Q₀` is fixed modulo `Q₀` by
all of `P`.

The proof passes to the `𝔽₂[↥D]`-module `Q/Q₀` (`D = twoPoint H t` acts by conjugation, `Q₀`
being the centre of the Suzuki `2`-group `Q`), where `k` acts fixed-point-freely, and applies
`Work.PSU3.StageA.exists_fixed_of_fpf_elementaryAbelian`. -/
theorem caseWbot_fixed_mod_Q0sub_aux {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) (hPp : (Nat.card P).Prime)
    {k : G} (hk : k ∈ Work.ThmF.Ksub H t) (hkq : (orderOf k).Prime) (hkodd : Odd (orderOf k))
    (hkfpf : ∀ x ∈ Q, k⁻¹ * x * k * x⁻¹ ∈ Work.ThmF.Q0sub H → x ∈ Work.ThmF.Q0sub H)
    (hknc : ∃ p ∈ P, p * k * p⁻¹ ≠ k) :
    ∃ x ∈ Q, x ∉ Work.ThmF.Q0sub H ∧ ∀ p ∈ P, p⁻¹ * x * p * x⁻¹ ∈ Work.ThmF.Q0sub H := by
  classical
  have hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q := caseWbot_isSuzukiTwoGroup hS hFT hC4 hnab
  have hHig := Work.Higman.higmanProp ↥Q hSuz
  have hcenterQ : Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q :=
    caseWbot_center_subgroupOf hS hFT hC4 hnab
  have hPodd : Odd (Nat.card P) :=
    (Work.ThmF.split_odd_card_twoPoint hS.split).of_dvd_nat
      (Subgroup.card_dvd_of_le (hPV.trans (Work.ThmF.centD_le_twoPoint (H := H) t)))
  -- ## 1. The quotient `Q/Q₀` and the conjugation action of `D = twoPoint H t`
  haveI hNnormal : ((Work.ThmF.Q0sub H).subgroupOf Q).Normal := hcenterQ ▸ Subgroup.instNormalCenter
  let N : Subgroup ↥Q := (Work.ThmF.Q0sub H).subgroupOf Q
  have hDnorm : Submission.Blueprint.twoPoint H t ≤ Subgroup.normalizer (Q : Set G) :=
    le_trans inf_le_left hS.split.normal
  let φ : ↥(Submission.Blueprint.twoPoint H t) →* MulAut ↥Q :=
    (Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hDnorm)
  have phi_apply : ∀ (a : ↥(Submission.Blueprint.twoPoint H t)) (x : ↥Q),
      (((φ a) x : ↥Q) : G) = (a : G) * (x : G) * (a : G)⁻¹ := fun a x => rfl
  have phi_apply' : ∀ (a : ↥(Submission.Blueprint.twoPoint H t)) (x : ↥Q),
      (((MulEquiv.toMonoidHom (φ a)) x : ↥Q) : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    fun a x => rfl
  have hpres : ∀ a : ↥(Submission.Blueprint.twoPoint H t), Subgroup.map (φ a).toMonoidHom N = N := by
    intro a
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [phi_apply' a x]
      exact Work.ThmF.ChV12.conj_mem_Q0sub (H := H) (Subgroup.mem_inf.mp a.2).1 hx
    · intro y hy
      rw [Subgroup.mem_map]
      refine ⟨(φ a).symm y, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        have hsymm : (((φ a).symm y : ↥Q) : G) = (a : G)⁻¹ * (y : G) * (a : G) := by
          have h1 : ((φ a).symm : ↥Q ≃* ↥Q) = φ a⁻¹ := by rw [map_inv]; rfl
          rw [h1]
          simpa using phi_apply a⁻¹ y

        rw [hsymm]
        have h2 := Work.ThmF.ChV12.conj_mem_Q0sub (H := H)
          (H.inv_mem (Subgroup.mem_inf.mp a.2).1) (Subgroup.mem_subgroupOf.mp hy)
        simpa using h2
      · exact MulEquiv.apply_symm_apply (φ a) y
  let ρ : ↥(Submission.Blueprint.twoPoint H t) →* MulAut (↥Q ⧸ N) :=
    { toFun := fun a => QuotientGroup.congr N N (φ a) (hpres a)
      map_one' := by
        apply MulEquiv.ext
        intro x
        refine QuotientGroup.induction_on x ?_
        intro q
        show QuotientGroup.congr N N (φ 1) (hpres 1) (QuotientGroup.mk q) = QuotientGroup.mk q
        rw [QuotientGroup.congr_mk N N (φ 1) (hpres 1) q]
        simp
      map_mul' := by
        intro a b
        apply MulEquiv.ext
        intro x
        refine QuotientGroup.induction_on x ?_
        intro q
        show QuotientGroup.congr N N (φ (a * b)) (hpres (a * b)) (QuotientGroup.mk q)
          = (QuotientGroup.congr N N (φ a) (hpres a))
              ((QuotientGroup.congr N N (φ b) (hpres b)) (QuotientGroup.mk q))
        rw [QuotientGroup.congr_mk N N (φ b) (hpres b) q,
          QuotientGroup.congr_mk N N (φ a) (hpres a) ((φ b) q),
          QuotientGroup.congr_mk N N (φ (a * b)) (hpres (a * b)) q,
          map_mul φ a b, MulAut.mul_apply] }
  let QN : Type := ↥Q ⧸ N
  letI : MulDistribMulAction ↥(Submission.Blueprint.twoPoint H t) QN :=
    MulDistribMulAction.compHom QN ρ
  have smul_mk : ∀ (d : ↥(Submission.Blueprint.twoPoint H t)) (x : ↥Q),
      d • (QuotientGroup.mk x : QN) = QuotientGroup.mk (φ d x) := by
    intro d x
    show QuotientGroup.congr N N (φ d) (hpres d) (QuotientGroup.mk x) = QuotientGroup.mk (φ d x)
    rw [QuotientGroup.congr_mk N N (φ d) (hpres d) x]
  have hNexp : ∀ n : ↥Q ⧸ N, n * n = 1 := by
    intro n
    refine QuotientGroup.induction_on n ?_
    intro x
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    show x * x ∈ (Work.ThmF.Q0sub H).subgroupOf Q
    rw [← hcenterQ]
    simpa [pow_two] using hHig.2.1 x
  have hNcomm : ∀ a b : ↥Q ⧸ N, a * b = b * a := by
    intro a b
    refine QuotientGroup.induction_on a ?_
    intro x
    refine QuotientGroup.induction_on b ?_
    intro y
    have h1 : (QuotientGroup.mk (x * y) : ↥Q ⧸ N) * (QuotientGroup.mk (y * x))⁻¹ = 1 := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      show (x * y) * (y * x)⁻¹ ∈ (Work.ThmF.Q0sub H).subgroupOf Q
      have hxy : (x * y) * (y * x)⁻¹ = ⁅x, y⁆ := by rw [commutatorElement_def]; group
      rw [hxy, ← hcenterQ, ← hHig.2.2.1]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    have h2 : (QuotientGroup.mk (x * y) : ↥Q ⧸ N) = QuotientGroup.mk (y * x) :=
      mul_inv_eq_one.mp h1
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h2]
  -- ## 2. The two acting elements and the relation `p₀ k p₀⁻¹ = k ^ s`
  obtain ⟨p₀, hp₀P, hp₀nc⟩ := hknc
  have hp₀ne : p₀ ≠ 1 := by
    intro h
    rw [h, one_mul, inv_one, mul_one] at hp₀nc
    exact hp₀nc rfl
  have hp₀D : p₀ ∈ Submission.Blueprint.twoPoint H t := (hPV hp₀P).1
  have hkD : k ∈ Submission.Blueprint.twoPoint H t := Work.ThmF.Ksub_le_twoPoint (H := H) t hk
  have hp₀ord : orderOf p₀ = Nat.card P := by
    have hdvd : orderOf p₀ ∣ Nat.card P := by
      have h := orderOf_dvd_natCard (⟨p₀, hp₀P⟩ : ↥P)
      rw [← Subgroup.orderOf_coe (⟨p₀, hp₀P⟩ : ↥P)] at h
      exact h
    rcases hPp.eq_one_or_self_of_dvd (orderOf p₀) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hp₀ne
    · exact h
  obtain ⟨hKcyc, hKset, hKn⟩ := caseWbot_K_facts hS hFT hC4
  have hbK : p₀ * k * p₀⁻¹ ∈ Work.ThmF.Ksub H t := by
    have h := hKn.conj_mem (⟨k, hkD⟩ : ↥(Submission.Blueprint.twoPoint H t))
      (Subgroup.mem_subgroupOf.mpr hk) (⟨p₀, hp₀D⟩ : ↥(Submission.Blueprint.twoPoint H t))
    exact Subgroup.mem_subgroupOf.mp h
  have hbord : orderOf (p₀ * k * p₀⁻¹) = orderOf k := by
    have h := orderOf_injective (MulAut.conj p₀).toMonoidHom (MulAut.conj p₀).injective k
    simpa [MulAut.conj_apply] using h
  have hmemz : p₀ * k * p₀⁻¹ ∈ Subgroup.zpowers k := by
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hKcyc
    have hkg : (⟨k, hk⟩ : ↥(Work.ThmF.Ksub H t)) ∈ Subgroup.zpowers g := by
      rw [hg]; exact Subgroup.mem_top _
    have hbg : (⟨p₀ * k * p₀⁻¹, hbK⟩ : ↥(Work.ThmF.Ksub H t)) ∈ Subgroup.zpowers g := by
      rw [hg]; exact Subgroup.mem_top _
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hkg
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hbg
    have hcard : Nat.card ↥(Work.ThmF.Ksub H t) = orderOf g :=
      (orderOf_eq_card_of_forall_mem_zpowers (fun x => by rw [hg]; exact Subgroup.mem_top x)).symm
    have hkg' : (⟨k, hk⟩ : ↥(Work.ThmF.Ksub H t)) = g ^ i := hi.symm
    have hbg' : (⟨p₀ * k * p₀⁻¹, hbK⟩ : ↥(Work.ThmF.Ksub H t)) = g ^ j := hj.symm
    have hgi : Nat.card ↥(Subgroup.zpowers (g ^ i)) = orderOf k := by
      rw [Nat.card_zpowers, ← hkg']
      exact (Subgroup.orderOf_coe (⟨k, hk⟩ : ↥(Work.ThmF.Ksub H t))).symm
    have hgj : Nat.card ↥(Subgroup.zpowers (g ^ j)) = orderOf k := by
      rw [Nat.card_zpowers, ← hbg']
      exact (Subgroup.orderOf_coe (⟨p₀ * k * p₀⁻¹, hbK⟩ : ↥(Work.ThmF.Ksub H t))).symm.trans hbord
    have hi' : Nat.card ↥(Subgroup.zpowers (g ^ i)) * (Subgroup.zpowers (g ^ i)).index
        = Nat.card ↥(Work.ThmF.Ksub H t) :=
      Subgroup.card_mul_index _
    have hj' : Nat.card ↥(Subgroup.zpowers (g ^ j)) * (Subgroup.zpowers (g ^ j)).index
        = Nat.card ↥(Work.ThmF.Ksub H t) :=
      Subgroup.card_mul_index _
    rw [Subgroup.index_zpowers_zpow hg i] at hi'
    rw [Subgroup.index_zpowers_zpow hg j] at hj'
    rw [hcard, hgi] at hi'
    rw [hcard, hgj] at hj'
    have hgcd : i.gcd (orderOf g : ℤ) = j.gcd (orderOf g : ℤ) :=
      Nat.mul_left_cancel (orderOf_pos k) (hi'.trans hj'.symm)
    have hz : Subgroup.zpowers (g ^ i) = Subgroup.zpowers (g ^ j) :=
      (Subgroup.zpowers_eq_zpowers_iff' g i j).mpr hgcd
    have hmem' : (⟨p₀ * k * p₀⁻¹, hbK⟩ : ↥(Work.ThmF.Ksub H t)) ∈
        Subgroup.zpowers (g ^ i) := by
      rw [hz, ← hbg']; exact Subgroup.mem_zpowers _
    have hmem'' : (⟨p₀ * k * p₀⁻¹, hbK⟩ : ↥(Work.ThmF.Ksub H t)) ∈
        Subgroup.zpowers (⟨k, hk⟩ : ↥(Work.ThmF.Ksub H t)) := by
      rw [hkg']; exact hmem'
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem''
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmemz
  obtain ⟨s, hs⟩ : ∃ s : ℕ, k ^ s = p₀ * k * p₀⁻¹ := by
    refine ⟨(m % (orderOf k : ℤ)).toNat, ?_⟩
    have hnonneg : 0 ≤ m % (orderOf k : ℤ) :=
      Int.emod_nonneg m (by exact_mod_cast (orderOf_pos k).ne')
    have hcast : ((((m % (orderOf k : ℤ)).toNat : ℕ)) : ℤ) = m % (orderOf k : ℤ) :=
      Int.toNat_of_nonneg hnonneg
    have hmod : k ^ ((((m % (orderOf k : ℤ)).toNat : ℕ)) : ℤ) = k ^ m := by
      rw [hcast, zpow_eq_zpow_iff_modEq]
      exact Int.mod_modEq m _
    have hmod' : k ^ ((m % (orderOf k : ℤ)).toNat) = k ^ m := by
      rw [← zpow_natCast]; exact hmod
    rw [hmod', hm]
  have hsne : s % orderOf k ≠ 1 := by
    intro hcon
    have h2 : s ≡ 1 [MOD orderOf k] := by
      show s % orderOf k = 1 % orderOf k
      rw [hcon, Nat.mod_eq_of_lt hkq.one_lt]
    have h3 : k ^ s = k ^ 1 := pow_eq_pow_iff_modEq.mpr h2
    rw [pow_one] at h3
    exact hp₀nc (hs.symm.trans h3)
  -- ## 3. The `p`-`q` lemma
  have hrel : (⟨p₀, hp₀D⟩ : ↥(Submission.Blueprint.twoPoint H t))
      * (⟨k, hkD⟩ : ↥(Submission.Blueprint.twoPoint H t))
      * (⟨p₀, hp₀D⟩ : ↥(Submission.Blueprint.twoPoint H t))⁻¹
      = (⟨k, hkD⟩ : ↥(Submission.Blueprint.twoPoint H t)) ^ s := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    exact hs.symm
  have hfpf : ∀ n : ↥Q ⧸ N,
      (⟨k, hkD⟩ : ↥(Submission.Blueprint.twoPoint H t)) • n = n → n = 1 := by
    intro n hn
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective n
    rw [smul_mk] at hn
    have hn' : (QuotientGroup.mk ((φ (⟨k, hkD⟩ : ↥(Submission.Blueprint.twoPoint H t))) x) : QN)
        = QuotientGroup.mk x := hn
    have hmem : (((φ (⟨k, hkD⟩ : ↥(Submission.Blueprint.twoPoint H t))) x) * x⁻¹ : ↥Q) ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hn',
        mul_inv_cancel]
    rw [Subgroup.mem_subgroupOf] at hmem
    have hmem' : k⁻¹ * (x : G) * k * (x : G)⁻¹ ∈ Work.ThmF.Q0sub H := by
      have hcoe : ((((φ (⟨k, hkD⟩ : ↥(Submission.Blueprint.twoPoint H t))) x
          * x⁻¹ : ↥Q) : G)) = k * (x : G) * k⁻¹ * (x : G)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, phi_apply]
      have hconj : k⁻¹ * (x : G) * k * (x : G)⁻¹
          = k⁻¹ * (k * (x : G) * k⁻¹ * (x : G)⁻¹)⁻¹ * k := by group
      rw [hconj]
      have hconj2 := Work.ThmF.ChV12.conj_mem_Q0sub (H := H)
        (H.inv_mem (Work.ThmF.ChV12.Ksub_le_H H t hk))
        ((Work.ThmF.Q0sub H).inv_mem (show k * (x : G) * k⁻¹ * (x : G)⁻¹ ∈ Work.ThmF.Q0sub H from by
          rw [← hcoe]; exact hmem))
      simpa using hconj2
    exact QuotientGroup.eq_one_iff _ |>.mpr (Subgroup.mem_subgroupOf.mpr (hkfpf x x.2 hmem'))
  have hp2 : ((Nat.card P : ℕ) : ZMod 2) ≠ 0 := by
    intro h0
    have h2 : 2 ∣ Nat.card P := (CharP.cast_eq_zero_iff (ZMod 2) 2 (Nat.card P)).mp h0
    exact (Nat.not_even_iff_odd.mpr hPodd) (even_iff_two_dvd.mpr h2)
  have hq2 : (((orderOf k : ℕ)) : ZMod 2) ≠ 0 := by
    intro h0
    have h2 : 2 ∣ orderOf k := (CharP.cast_eq_zero_iff (ZMod 2) 2 (orderOf k)).mp h0
    exact (Nat.not_even_iff_odd.mpr hkodd) (even_iff_two_dvd.mpr h2)
  haveI : Nontrivial (↥Q ⧸ N) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    refine hnab (fun x hx y hy => ?_)
    have hcommH : ∀ u ∈ Submission.Blueprint.involutions (H : Set G),
        ∀ v ∈ Submission.Blueprint.involutions (H : Set G), u * v = v * u :=
      Work.ThmF.ChV12.involutions_of_H_commute hS.situation hC4 H Q t hS.split
    have hel := Work.ThmF.ChV12.Q0sub_elementary H hcommH
    have hxN : (⟨x, hx⟩ : ↥Q) ∈ N := by rw [htop]; exact Subgroup.mem_top _
    have hyN : (⟨y, hy⟩ : ↥Q) ∈ N := by rw [htop]; exact Subgroup.mem_top _
    exact hel.2.1 x (Subgroup.mem_subgroupOf.mp hxN) y (Subgroup.mem_subgroupOf.mp hyN)
  obtain ⟨n, hn1, hnsmul⟩ :=
    exists_fixed_of_fpf_elementaryAbelian (A := ↥(Submission.Blueprint.twoPoint H t))
      (N := ↥Q ⧸ N) hPp hkq hp2 hq2 hsne hNexp hNcomm
      (Subgroup.orderOf_coe (⟨k, hkD⟩ : ↥(Submission.Blueprint.twoPoint H t))).symm
      ((Subgroup.orderOf_coe (⟨p₀, hp₀D⟩ : ↥(Submission.Blueprint.twoPoint H t))).symm.trans
        (by simpa using hp₀ord))
      hrel hfpf
  -- ## 4. Unwrapping: the class of `x₀` is fixed by all of `P`
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective n
  rw [smul_mk] at hnsmul
  have hx0Q : (x₀ : G) ∈ Q := x₀.2
  have hx0not : (x₀ : G) ∉ Work.ThmF.Q0sub H := by
    intro hcon
    exact hn1 (QuotientGroup.eq_one_iff _ |>.mpr (Subgroup.mem_subgroupOf.mpr hcon))
  have hstab : ∀ (p : G) (hp : p ∈ P), (⟨p, (hPV hp).1⟩ : ↥(Submission.Blueprint.twoPoint H t))
      • (QuotientGroup.mk x₀ : ↥Q ⧸ N) = QuotientGroup.mk x₀ := by
    intro p hp
    have hgen : Subgroup.zpowers (⟨p₀, hp₀D⟩ : ↥(Submission.Blueprint.twoPoint H t))
        = P.subgroupOf (Submission.Blueprint.twoPoint H t) := by
      apply Subgroup.eq_of_le_of_card_ge
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_subgroupOf.mpr hp₀P
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPV.trans
          (Work.ThmF.centD_le_twoPoint (H := H) t))).toEquiv, Nat.card_zpowers]
        exact le_of_eq (((Subgroup.orderOf_coe (⟨p₀, hp₀D⟩ : ↥(Submission.Blueprint.twoPoint H t))).symm.trans
          (by simpa using hp₀ord))).symm
    have hmem : (⟨p, (hPV hp).1⟩ : ↥(Submission.Blueprint.twoPoint H t))
        ∈ Subgroup.zpowers (⟨p₀, hp₀D⟩ : ↥(Submission.Blueprint.twoPoint H t)) := by
      rw [hgen]; exact Subgroup.mem_subgroupOf.mpr hp
    have hle : Subgroup.zpowers (⟨p₀, hp₀D⟩ : ↥(Submission.Blueprint.twoPoint H t))
        ≤ MulAction.stabilizer ↥(Submission.Blueprint.twoPoint H t) (QuotientGroup.mk x₀ : QN) := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
      exact hnsmul
    exact MulAction.mem_stabilizer_iff.mp (hle hmem)
  refine ⟨x₀, hx0Q, hx0not, fun p hp => ?_⟩
  have hfixed : p * x₀ * p⁻¹ * x₀⁻¹ ∈ Work.ThmF.Q0sub H := by
    let pd : ↥(Submission.Blueprint.twoPoint H t) := ⟨p, (hPV hp).1⟩
    have hstab' : (QuotientGroup.mk ((φ pd) x₀) : QN) = QuotientGroup.mk x₀ := hstab p hp
    have hmem : (((φ pd) x₀ * x₀⁻¹ : ↥Q) ∈ N) := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hstab',
        mul_inv_cancel]
    rw [Subgroup.mem_subgroupOf] at hmem
    have hcoe : ((((φ pd) x₀ * x₀⁻¹ : ↥Q) : G)) = p * (x₀ : G) * p⁻¹ * (x₀ : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, phi_apply]
    rwa [hcoe] at hmem
  have hpH : p ∈ H := (Subgroup.mem_inf.mp (hPV hp).1).1
  have hconj : p⁻¹ * (x₀ : G) * p * (x₀ : G)⁻¹
      = p⁻¹ * (p * (x₀ : G) * p⁻¹ * (x₀ : G)⁻¹)⁻¹ * p := by group
  rw [hconj]
  have hfin := Work.ThmF.ChV12.conj_mem_Q0sub (H := H) (H.inv_mem hpH)
    ((Work.ThmF.Q0sub H).inv_mem hfixed)
  simpa using hfin


theorem caseWbot_branch_one_false_of_card_cube {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} {s r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (hW : Work.ThmF.W H t = ⊥)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 3)
    {P : Subgroup G} (hP : P ≤ Submission.Blueprint.centD H t) (hp : (Nat.card P).Prime) :
    ¬ (orderOf (s * t) = 3 ∧
      Submission.Blueprint.IsAbelianSubgroup (Q ⊓ Subgroup.centralizer (P : Set G)) ∧
      Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)) =
        Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G))) := by
  rintro ⟨h3, -, hcardC⟩
  classical
  set ℓ : ℕ := Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) with hℓdef
  have hcardC' : Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)) = ℓ := by
    rw [hℓdef]; exact hcardC
  -- ## 0. Elementary facts about the configuration
  have hPW : P ⊓ Work.ThmF.W H t = ⊥ := by rw [hW, inf_bot_eq]
  have hPD : P ≤ Submission.Blueprint.twoPoint H t :=
    hP.trans (Work.ThmF.centD_le_twoPoint (H := H) t)
  have hDodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
    hS.split.stronglyEmbedded.2.2 t hS.split.not_mem
  have hPodd : Odd (Nat.card P) := hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hPD)
  have hPp2 : Nat.card P ≠ 2 := by
    intro h2
    rw [h2] at hPodd
    exact absurd hPodd (by norm_num)
  -- `s` is a non-trivial element of `C_{Q₀}(P)`
  have hsInv : s ∈ Submission.Blueprint.involutions (H : Set G) := ⟨hS.split.le hs, hs2⟩
  have hV : Submission.Blueprint.centD H t =
      Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G) :=
    Work.PSU3.StageA.centD_eq_centralizer_s hS hs hs2 hr hsr
  have hsQ0sub : s ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H hsInv)
  have hsGc : s ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqV : q ∈ Submission.Blueprint.centD H t := hP hq
    rw [hV] at hqV
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hqV).2
  have hs_mem : s ∈ Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) := ⟨hsQ0sub, hsGc⟩
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  have hℓ2 : 2 ≤ ℓ := by
    rw [hℓdef]
    haveI : Fintype ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) := Fintype.ofFinite _
    have hlt : 1 < Fintype.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) :=
      Fintype.one_lt_card_iff.mpr ⟨⟨s, hs_mem⟩, 1, fun h => hs1 (Subtype.ext_iff.mp h)⟩
    rw [Nat.card_eq_fintype_card]
    omega
  -- ## 1. Ch. V §1 Prop. 2 / Prop. 3 and the exponent identity `ℓ ^ |P| = |Q₀|`
  obtain ⟨hKcyc, hKset, hKn⟩ := caseWbot_K_facts (H := H) (Q := Q) (t := t) hS hFT hC4
  have hcommH : ∀ u ∈ Submission.Blueprint.involutions (H : Set G),
      ∀ v ∈ Submission.Blueprint.involutions (H : Set G), u * v = v * u :=
    Work.ThmF.ChV12.involutions_of_H_commute hS.situation hC4 H Q t hS.split
  have hreg := Work.ThmF.L5.Kset_regular hS.split
  obtain ⟨F, hFld, hFt, e, κ, ρ, hcardF, -, hρact, hker⟩ :=
    Work.ThmF.ChV12.prop3 H Q t hS.split hcommH hKset hKcyc hKn hreg s hsInv hV
  letI : Field F := hFld
  letI : Fintype F := hFt
  have hstr : ∃ (F' : Type) (_ : Field F') (_ : Fintype F')
      (e' : ↥(Work.ThmF.Q0sub H) ≃* Multiplicative F')
      (ρ' : ↥(Submission.Blueprint.centD H t) →* (F' ≃+* F')),
      ρ'.ker = (Work.ThmF.W H t).subgroupOf (Submission.Blueprint.centD H t) ∧
        ∀ (v : ↥(Submission.Blueprint.centD H t)) (x : ↥(Work.ThmF.Q0sub H))
          (hx : (v : G) * x * (v : G)⁻¹ ∈ Work.ThmF.Q0sub H),
          Multiplicative.toAdd (e' ⟨(v : G) * x * (v : G)⁻¹, hx⟩) =
            ρ' v (Multiplicative.toAdd (e' x)) :=
    ⟨F, hFld, hFt, e, ρ, hker, hρact⟩
  have hℓpow : ℓ ^ Nat.card P = Nat.card ↥(Work.ThmF.Q0sub H) :=
    Work.ThmF.ChV12.prop3_card_fixed_pow H Q t hP hPW hp hstr
  obtain ⟨n, hn⟩ := caseWbot_Q0sub_card_pow_two (H := H) (Q := Q) (t := t) hS hC4
  have hnpos : 1 ≤ n := by
    have h3le : 3 ≤ 2 ^ n := by
      have h1 : 2 ≤ (Submission.Blueprint.involutions (H : Set G)).ncard :=
        Work.ThmF.Bender.cardInvGeTwo hS.split.stronglyEmbedded hS.situation.1.1
      have h2 : Nat.card ↥(Work.ThmF.Q0sub H) =
          (Submission.Blueprint.involutions (H : Set G)).ncard + 1 :=
        Work.PSU3.StageA.caseC_card_Q0sub_eq hS hC4
      omega
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at h3le
    omega
  -- `ℓ = 2 ^ m` and `n = m * |P|`
  have hℓdvd : ℓ ∣ 2 ^ n := by
    rw [hℓdef, ← hn]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨m, hm⟩ : ∃ m, ℓ = 2 ^ m := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hℓdvd
    exact ⟨m, hm⟩
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, pow_zero] at hm
      omega
    · exact h
  have hmul : m * Nat.card P = n := by
    have h1 : (2 : ℕ) ^ (m * Nat.card P) = 2 ^ n := by
      rw [pow_mul, ← hm, hℓpow, hn]
    exact Nat.pow_right_injective (le_refl 2) h1
  -- ## 2. A prime `tt | 2 ^ n - 1` with `tt ∤ ℓ - 1`
  obtain ⟨tt, httprime, httdvd, httndvd⟩ :=
    exists_prime_dvd_pow_sub_one_not_dvd (A := ℓ) (p := Nat.card P) hℓ2 hp hPp2
  have httdvd' : tt ∣ 2 ^ n - 1 := by
    have h := httdvd
    rwa [hℓpow, hn] at h
  have httodd : Odd tt := by
    refine Odd.of_dvd_nat ?_ httdvd'
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h
    obtain ⟨v, hv⟩ := h
    have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hnpos]
    have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    omega
  -- ## 3. An element `k ∈ Ksub H t` of order `tt`, not centralised by `P`
  have hKcard : Nat.card ↥(Work.ThmF.Ksub H t) = Nat.card ↥(Work.ThmF.Q0sub H) - 1 := by
    rw [Nat.card_congr κ.toEquiv, Nat.card_units, hcardF]
  have httdvdK : tt ∣ Nat.card ↥(Work.ThmF.Ksub H t) := by
    rw [hKcard, hn]; exact httdvd'
  haveI : Fact tt.Prime := ⟨httprime⟩
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Work.ThmF.Ksub H t)) tt httdvdK
  let k : G := (x : ↥(Work.ThmF.Ksub H t))
  have hkKsub : k ∈ Work.ThmF.Ksub H t := x.2
  have hkord : orderOf k = tt := (Subgroup.orderOf_coe x).trans hxord
  have hk1 : k ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hkord
    exact httprime.ne_one hkord.symm
  have hkodd : Odd (orderOf k) := by rw [hkord]; exact httodd
  have hkfpf := caseWbot_K_elt_fpf_quotient hS hC4 hFT hnab hkKsub hk1
  have hknc : ∃ p ∈ P, p * k * p⁻¹ ≠ k := by
    by_contra hc
    push Not at hc
    have hkcent : k ∈ Work.ThmF.Ksub H t ⊓ Subgroup.centralizer (P : Set G) :=
      ⟨hkKsub, Subgroup.mem_centralizer_iff.mpr (fun p hpv => by
        have h := hc p hpv
        calc p * k = (p * k * p⁻¹) * p := by group
          _ = k * p := by rw [h])⟩
    have hdvd : orderOf k ∣
        Nat.card ↥(Work.ThmF.Ksub H t ⊓ Subgroup.centralizer (P : Set G)) := by
      have h := orderOf_dvd_natCard (⟨k, hkcent⟩ : ↥(Work.ThmF.Ksub H t ⊓
        Subgroup.centralizer (P : Set G)))
      rwa [← Subgroup.orderOf_coe ⟨k, hkcent⟩] at h
    rw [caseWbot_K_centralizer_card hS hC4 hFT hP hp hPW, hkord] at hdvd
    exact httndvd hdvd
  -- ## 4. The `p`-`q` step: an element of `Q ∖ Q₀` fixed by `P`
  obtain ⟨x₀, hx0Q, hx0not, hx0fix⟩ :=
    caseWbot_fixed_mod_Q0sub_aux hS hC4 hFT hnab hP hp hkKsub (hkord ▸ httprime) hkodd hkfpf hknc
  obtain ⟨y, hyQ, hy0, hyfix⟩ :=
    Work.PSU3.StageA.caseC_exists_fixed_of_fixed_mod_Q0 hS hC4 hPD hPodd hx0Q hx0not hx0fix
  -- ## 5. The local trichotomy forces `|C| = ℓ³`, contradicting branch (i)
  have hcube : Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)) = ℓ ^ 3 :=
    Work.PSU3.StageB.card_centralizer_eq_cube hS hC4 Work.PSU3.benderSTProp hs hs2 hr hsr h3
      hP hp hyQ hy0 hyfix
  have hEq : ℓ = ℓ ^ 3 := hcardC'.symm.trans hcube
  have hmul : ℓ * ℓ ^ 2 = ℓ := by
    have h3' : ℓ ^ 3 = ℓ * ℓ ^ 2 := by ring
    rw [← h3']; exact hEq.symm
  have hℓpos : 0 < ℓ := by omega
  have hsq : ℓ ^ 2 = 1 := Nat.mul_left_cancel hℓpos (by rw [mul_one]; exact hmul)
  nlinarith [hsq, hℓ2]

end Work.PSU3.StageA
