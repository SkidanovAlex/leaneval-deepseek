import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.sec5_setup
import Submission.Work.NormalComplement.appI_five_b
import Submission.Work.NormalComplement.p3Normal_of_chIIFourP3Subnormal
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.appI_two
import Submission.Work.Fitting.piCore_isPiNat
import Submission.Work.GlaubermanZJ.pPrimeCore_eq_fitting
import Submission.Work.NormalComplement.Sec5Fix.benderLift
import Submission.Work.NormalComplement.Sec5Fix.ngpInverted
import Submission.Work.NormalComplement.Sec5Fix.msetAbelianOdd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-- If `P` is contained in the centraliser of `T` then `T` normalises `P` (mutual commutation). -/
lemma le_normalizer_of_le_centralizer {G : Type} [Group G] {T P : Subgroup G}
    (h : P ≤ Subgroup.centralizer (T : Set G)) :
    T ≤ Subgroup.normalizer (P : Set G) := by
  intro x hxT
  have hxinv : x⁻¹ ∈ T := T.inv_mem hxT
  have hcomm : ∀ y ∈ P, y * x = x * y := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp (h hy)) x hxT |>.symm
  have hcomm' : ∀ y ∈ P, x⁻¹ * y = y * x⁻¹ := fun y hy => by
    calc x⁻¹ * y = x⁻¹ * (y * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * y) * x⁻¹ := by rw [hcomm y hy]
      _ = y * x⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · intro hp
    have : x * p * x⁻¹ = p := by rw [← hcomm p hp]; group
    rw [this]; exact hp
  · intro hp
    have hq : x * p * x⁻¹ ∈ P := hp
    have h2 : p = x * p * x⁻¹ := by
      calc p = x⁻¹ * (x * p * x⁻¹) * x := by group
        _ = (x⁻¹ * (x * p * x⁻¹)) * x := rfl
        _ = ((x * p * x⁻¹) * x⁻¹) * x := by rw [hcomm' (x * p * x⁻¹) hq]
        _ = x * p * x⁻¹ := by group
    rw [h2]; exact hq

/-- **Ruling out `T` being an `f`-group.** -/
theorem not_isPGroup_of_cyclic_le_normalizer_not_le_centralizer {G : Type} [Group G] [Finite G]
    {T P : Subgroup G} {f p : ℕ}
    (hTcyc : IsCyclic ↥T) (hf : f.Prime) (hfle : f ≤ 5)
    (hp : p.Prime) (hp7 : 7 ≤ p) (hPp : Nat.card P = p)
    (hpT : P ≤ Subgroup.normalizer (T : Set G))
    (hCnc : ¬ P ≤ Subgroup.centralizer (T : Set G)) :
    ¬ IsPGroup f ↥T := by
  intro hTp
  haveI : Fact f.Prime := ⟨hf⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hTp
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · exfalso
      rw [h0, pow_zero] at hk
      have hbot : T = ⊥ := Subgroup.card_eq_one.mp hk
      apply hCnc
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hbot] at hy
      rw [Subgroup.mem_bot.mp hy]; simp
    · exact h
  have hCin : P ⊓ Subgroup.centralizer (T : Set G) = ⊥ := by
    by_contra hne
    have hdvd := Subgroup.card_dvd_of_le (inf_le_left : P ⊓ Subgroup.centralizer (T : Set G) ≤ P)
    rw [hPp] at hdvd
    have hne1 : Nat.card ↥(P ⊓ Subgroup.centralizer (T : Set G)) ≠ 1 := by
      intro h1
      exact hne (Subgroup.card_eq_one.mp h1)
    have heqc : Nat.card ↥(P ⊓ Subgroup.centralizer (T : Set G)) = p := by
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have heq2 : P ⊓ Subgroup.centralizer (T : Set G) = P :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [heqc, hPp])
    exact hCnc (le_trans (le_of_eq heq2.symm) inf_le_right)
  set ψ : ↥P →* MulAut ↥T :=
    (Subgroup.normalizerMonoidHom T).comp (Subgroup.inclusion hpT) with hψ
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have hmem : a * b⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    rw [hψ] at hmem
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply] at hmem
    have hker := Subgroup.normalizerMonoidHom_ker (H := T)
    have h2 : Subgroup.inclusion hpT (a * b⁻¹) ∈
        (Subgroup.centralizer (T : Set G)).subgroupOf (Subgroup.normalizer (T : Set G)) := by
      rw [← hker]; exact hmem
    have h3 : ((Subgroup.inclusion hpT (a * b⁻¹) : ↥(Subgroup.normalizer (T : Set G))) : G) ∈
        Subgroup.centralizer (T : Set G) := Subgroup.mem_subgroupOf.mp h2
    have h4 : ((a * b⁻¹ : ↥P) : G) ∈ Subgroup.centralizer (T : Set G) := by
      simpa using h3
    have h5 : ((a * b⁻¹ : ↥P) : G) ∈ P ⊓ Subgroup.centralizer (T : Set G) :=
      ⟨(a * b⁻¹).2, h4⟩
    rw [hCin] at h5
    have h6 : ((a * b⁻¹ : ↥P) : G) = 1 := Subgroup.mem_bot.mp h5
    have h7 : (a * b⁻¹ : ↥P) = 1 := Subtype.ext h6
    exact mul_inv_eq_one.mp h7
  have hcardP : Nat.card ↥(ψ.range) = Nat.card ↥P := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hψinj, Subgroup.card_top]
  have hpdvd : p ∣ Nat.card (MulAut ↥T) := by
    have h1 := Subgroup.card_dvd_of_le (le_top : ψ.range ≤ ⊤)
    rwa [Subgroup.card_top, hcardP, hPp] at h1
  rw [IsCyclic.card_mulAut, hk, Nat.totient_prime_pow hf hkpos] at hpdvd
  rcases hp.dvd_mul.mp hpdvd with h | h
  · have hpf : p ∣ f := hp.dvd_of_dvd_pow h
    have hEq : p = f := (Nat.prime_dvd_prime_iff_eq hp hf).mp hpf
    omega
  · have h2 : f - 1 ≤ 4 := Nat.sub_le_sub_right hfle 1
    have h3 : p ≤ f - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hf.one_lt) h
    omega

/-- If `n ≠ 1` is not a prime power of `f`, then `n` has a prime divisor `≠ f`. -/
lemma exists_prime_dvd_ne_of_not_prime_pow {n f : ℕ} (hn0 : n ≠ 0)
    (hn : ∀ k, n ≠ f ^ k) :
    ∃ ℓ, ℓ.Prime ∧ ℓ ∣ n ∧ ℓ ≠ f := by
  by_contra h
  push_neg at h
  have h1 : n = f ^ n.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hn0 (fun {d} hd hdn => h d hd hdn)
  exact hn n.primeFactorsList.length h1

lemma coprime_card_pPrimeCore_inner {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime) :
    Nat.Coprime (Nat.card ↥(Submission.Blueprint.pPrimeCore p H)) p := by
  have h := Work.Fitting.piCore_isPiNat H (fun q => q ≠ p)
  rw [Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
  exact (Work.GlaubermanZJ.isPiNat_ne_iff_coprime hp).mp h

/-- A cyclic group that is not an `f`-group has an element `≠ 1` of order prime to `f`. -/
lemma exists_coprime_order_of_not_isPGroup {G : Type} [Group G] [Finite G] {T : Subgroup G}
    {f : ℕ} (hf : f.Prime) (hcyc : IsCyclic ↥T) (h : ¬ IsPGroup f ↥T) :
    ∃ z : G, z ∈ T ∧ z ≠ 1 ∧ Nat.Coprime (orderOf z) f := by
  haveI : Fact f.Prime := ⟨hf⟩
  have hn : ∀ k, Nat.card ↥T ≠ f ^ k := fun k hk => h (IsPGroup.iff_card.mpr ⟨k, hk⟩)
  have hn0 : Nat.card ↥T ≠ 0 := by
    haveI : Nonempty ↥T := ⟨⟨1, T.one_mem⟩⟩
    exact Nat.card_pos.ne'
  obtain ⟨ℓ, hℓp, hℓdvd, hℓne⟩ := exists_prime_dvd_ne_of_not_prime_pow hn0 hn
  have hnpos : 0 < Nat.card ↥T := Nat.pos_of_ne_zero hn0
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  have hgord : orderOf g = Nat.card ↥T := orderOf_eq_card_of_zpowers_eq_top hg
  set m : ℕ := Nat.card ↥T / ℓ with hm
  have hmul : m * ℓ = Nat.card ↥T := Nat.div_mul_cancel hℓdvd
  have hmpos : 0 < m := Nat.div_pos (Nat.le_of_dvd hnpos hℓdvd) hℓp.pos
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  have hord : orderOf (g ^ m) = ℓ := by
    rw [orderOf_eq_prime_iff]
    refine ⟨?_, ?_⟩
    · rw [← pow_mul, hmul, ← hgord, pow_orderOf_eq_one]
    · intro h1
      have hdvd : Nat.card ↥T ∣ m := by
        rw [← hgord]; exact orderOf_dvd_iff_pow_eq_one.mpr h1
      have hle : Nat.card ↥T ≤ m := Nat.le_of_dvd hmpos hdvd
      have hlt : m < Nat.card ↥T := Nat.div_lt_self (by omega) hℓp.one_lt
      omega
  refine ⟨((g ^ m : ↥T) : G), (g ^ m).2, ?_, ?_⟩
  · intro hz1
    have h1 : orderOf ((g ^ m : ↥T) : G) = 1 := by rw [hz1]; exact orderOf_one
    rw [Subgroup.orderOf_coe, hord] at h1
    exact hℓp.ne_one h1
  · rw [Subgroup.orderOf_coe, hord]
    exact (Nat.coprime_primes hℓp hf).mpr hℓne

/-- Assembly of §5 Prop. 2 (d): if `Mset u t` is an abelian subgroup of odd order, then
`O_{f'}(M) ≠ 1` and `P` acts fixed-point-freely on it, where `f = orderOf (u * t)`. -/
theorem sec5_clause_d (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp) (hC : Submission.Blueprint.ThmCProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop)
    (hCor1 : Work.NormalComplement.Design.ChISixCor1Prop)
    (hBC : Work.NormalComplement.Design.BurnsideClassProp)
    (hBP : Work.NormalComplement.BenderPrelimProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G))
    (M : Subgroup G) (hM : (M : Set G) = Work.NormalComplement.Design.Mset u t)
    (hp7 : 7 ≤ p)
    (hbf : orderOf (u * t) = 3 ∨ orderOf (u * t) = 5)
    (hbd : let C := Subgroup.centralizer (A : Set G)
      let F₀ := (Submission.Blueprint.oddResidual ↥C).map C.subtype
      ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (φ : F₀ →* Y) (HY : Subgroup Y),
        Function.Surjective φ ∧ φ.ker = Subgroup.center ↥F₀ ∧
        LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y ∧
        LeanEval.GroupTheory.Defs.IsStronglyEmbedded HY ∧
        Submission.Blueprint.IsZassenhaus HY ∧
        (Submission.Blueprint.involutions (HY : Set Y)).ncard = 2 ^ p - 1 ∧
        ∃ (hu0 : u ∈ F₀) (ht0 : t ∈ F₀),
          φ ⟨u, hu0⟩ ∈ HY ∧ orderOf (φ ⟨u, hu0⟩) = 2 ∧ φ ⟨t, ht0⟩ ∉ HY ∧
          orderOf (φ ⟨t, ht0⟩) = 2 ∧
          ∀ x : F₀, (x : G) ∈ H → φ x ∈ HY)
    :
    Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M ≠ ⊥ ∧
      Work.NormalComplement.Design.FpfOn P
        (Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M : Set G) := by
  classical
  obtain ⟨hMab, hModd⟩ :=
    Work.NormalComplement.Sec5Fix.msetAbelianOdd hFT hA hC hC4 hP3 hIII hMF2 hCor1 hBC hBP
      h u hu hbf M hM
  have hfprime : (orderOf (u * t)).Prime := by
    rcases hbf with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  have hfodd : Odd (orderOf (u * t)) := by
    rcases hbf with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  have hfle : orderOf (u * t) ≤ 5 := by omega
  have hfpos : 0 < orderOf (u * t) := hfprime.pos
  haveI : Fact (Nat.Prime (orderOf (u * t))) := ⟨hfprime⟩
  obtain ⟨T, hTcyc, hTcard, hTinv, hTut, hTnorm⟩ :=
    Work.NormalComplement.Sec5Fix.benderLift hFT hA hC hC4 hP3 hIII hMF2 hCor1 hBC hBP h u hu hp7 hbd
  haveI hTcomm : IsMulCommutative ↥T := hTcyc.isMulCommutative
  -- ## `T` is not an `f`-group
  have hTnot : ¬ IsPGroup (orderOf (u * t)) ↥T := by
    intro hTp
    have hTodd : Odd (Nat.card ↥T) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hTp
      rw [hk]; exact hfodd.pow
    let U : Subgroup ↥T := (Subgroup.normalizer (P : Set G)).subgroupOf T
    haveI hUcyc : IsCyclic ↥U := Subgroup.isCyclic U
    have hUcard : Nat.card ↥U ∣ orderOf (u * t) := by
      obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hUcyc
      rw [← orderOf_eq_card_of_zpowers_eq_top hg]
      have hgmem : (((g : ↥T)) : G) ∈ T := (g : ↥T).2
      have hgN : (((g : ↥T)) : G) ∈ Subgroup.normalizer (P : Set G) :=
        Subgroup.mem_subgroupOf.mp g.2
      have hodd : Odd (orderOf (((g : ↥T)) : G)) :=
        Odd.of_dvd_nat hTodd (Subgroup.orderOf_dvd_natCard T hgmem)
      have hinv : u * (((g : ↥T)) : G) * u⁻¹ = ((((g : ↥T)) : G))⁻¹ := hTinv _ hgmem
      have hres :=
        Work.NormalComplement.Sec5Fix.ngpInverted hFT hA hC hC4 hP3 hIII hMF2 hCor1 hBC hBP h u hu hgN hodd hinv
      have hcoe : orderOf g = orderOf (((g : ↥T)) : G) :=
        (Subgroup.orderOf_coe g).symm.trans (Subgroup.orderOf_coe (g : ↥T)).symm
      rwa [hcoe]
    have hUnT : ¬ T ≤ Subgroup.normalizer (P : Set G) := by
      intro hle
      have hUtop : U = ⊤ := Subgroup.subgroupOf_eq_top.mpr hle
      rw [hUtop, Subgroup.card_top] at hUcard
      have hle' : Nat.card ↥T ≤ orderOf (u * t) := Nat.le_of_dvd hfpos hUcard
      omega
    have hCnc : ¬ P ≤ Subgroup.centralizer (T : Set G) :=
      fun hc => hUnT (le_normalizer_of_le_centralizer hc)
    exact not_isPGroup_of_cyclic_le_normalizer_not_le_centralizer hTcyc hfprime hfle
      h.prime hp7 h.P_card hTnorm hCnc hTp
  -- ## an element of `M` of order prime to `f`
  have hconj1 : Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M ≠ ⊥ := by
    obtain ⟨z₀, hz₀T, hz₀ne, hz₀cop⟩ :=
      exists_coprime_order_of_not_isPGroup hfprime hTcyc hTnot
    have hcomm_ut : z₀ * (u * t) = (u * t) * z₀ :=
      congrArg Subtype.val (mul_comm' (⟨z₀, hz₀T⟩ : ↥T) ⟨u * t, hTut⟩)
    have hz₀M : z₀ ∈ M := by
      change z₀ ∈ (M : Set G)
      rw [hM]
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcomm_ut, ?_⟩
      have hu2 : u * u = 1 := by
        have h' := pow_orderOf_eq_one u
        rw [hu.2.1] at h'; simpa [pow_two] using h'
      have ht_eq : t = u * (u * t) := by rw [← mul_assoc, hu2, one_mul]
      calc t * z₀ * t⁻¹ = (u * (u * t)) * z₀ * (u * (u * t))⁻¹ := by rw [← ht_eq]
        _ = u * ((u * t) * z₀ * (u * t)⁻¹) * u⁻¹ := by group
        _ = u * z₀ * u⁻¹ := by
              rw [show (u * t) * z₀ * (u * t)⁻¹ = z₀ from by rw [← hcomm_ut]; group]
        _ = z₀⁻¹ := hTinv z₀ hz₀T
    haveI : IsMulCommutative ↥M :=
      isMulCommutative_iff.mpr (fun a b => Subtype.ext (hMab a a.2 b b.2))
    intro hbot
    have hsub : Subgroup.zpowers (⟨z₀, hz₀M⟩ : ↥M) ≤
        Submission.Blueprint.pPrimeCore (orderOf (u * t)) ↥M :=
      le_sSup (s := {N : Subgroup ↥M | N.Normal ∧
          Nat.Coprime (Nat.card ↥N) (orderOf (u * t))})
        ⟨Subgroup.normal_of_isMulCommutative _,
          by simpa [Nat.card_zpowers, Subgroup.orderOf_coe] using hz₀cop⟩
    have hzp : (⟨z₀, hz₀M⟩ : ↥M) ∈ Submission.Blueprint.pPrimeCore (orderOf (u * t)) ↥M :=
      hsub (Subgroup.mem_zpowers _)
    have hz₀mem : z₀ ∈ Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M :=
      Subgroup.mem_map.mpr ⟨⟨z₀, hz₀M⟩, hzp, rfl⟩
    rw [hbot] at hz₀mem
    exact hz₀ne (Subgroup.mem_bot.mp hz₀mem)
  refine ⟨hconj1, ?_⟩
  -- ## `P` acts fixed-point-freely on `O_{f'}(M)`
  have hOcop : Nat.Coprime
      (Nat.card ↥(Work.NormalComplement.pPrimeCoreSub (orderOf (u * t)) M))
      (orderOf (u * t)) := by
    rw [Work.NormalComplement.pPrimeCoreSub,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective M)]
    exact coprime_card_pPrimeCore_inner hfprime
  intro x hxP xne k hkS hfix
  have hkM : k ∈ M := Subgroup.map_subtype_le _ hkS
  have hkodd : Odd (orderOf k) :=
    Odd.of_dvd_nat hModd (Subgroup.orderOf_dvd_natCard M hkM)
  have hkmset : k ∈ Work.NormalComplement.Design.Mset u t := hM ▸ hkM
  have hkcomm_ut : k * (u * t) = (u * t) * k :=
    Subgroup.mem_centralizer_singleton_iff.mp hkmset.1
  -- `x` generates `P` (of prime order `p`), so `k` commutes with all of `P`
  have hxord : orderOf x = Nat.card P := by
    rw [h.P_card]
    have hodd : orderOf x ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hxP
    rw [h.P_card] at hodd
    rcases (Nat.dvd_prime h.prime).mp hodd with h1 | h1
    · exact absurd h1 (fun h1 => xne (orderOf_eq_one_iff.mp h1))
    · exact h1
  have hxgen : Subgroup.zpowers x = P :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxP) (by
      rw [Nat.card_zpowers, hxord])
  have hxk_eq : x * k = k * x := by
    calc x * k = (x * k * x⁻¹) * x := by group
      _ = k * x := by rw [hfix]
  have hxcent : x ∈ Subgroup.centralizer ({k} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxk_eq
  have hPk : P ≤ Subgroup.centralizer ({k} : Set G) := by
    rw [← hxgen]; exact Subgroup.zpowers_le.mpr hxcent
  have hkcent : k ∈ Subgroup.centralizer (P : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hPk hy))
  have hkN : k ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.centralizer_le_normalizer (P : Set G) hkcent
  have hkinv : u * k * u⁻¹ = k⁻¹ := by
    have hu2 : u * u = 1 := by
      have h' := pow_orderOf_eq_one u
      rw [hu.2.1] at h'; simpa [pow_two] using h'
    have ht_eq : u * (u * t) = t := by rw [← mul_assoc, hu2, one_mul]
    have htinv : t * k * t⁻¹ = k⁻¹ := hkmset.2
    have h1 : u * k * u⁻¹ = u * ((u * t) * k * (u * t)⁻¹) * u⁻¹ := by
      rw [show (u * t) * k * (u * t)⁻¹ = k from by rw [← hkcomm_ut]; group]
    have h2 : u * ((u * t) * k * (u * t)⁻¹) * u⁻¹
        = (u * (u * t)) * k * (u * (u * t))⁻¹ := by group
    rw [h1, h2, ht_eq, htinv]
  have hkord : orderOf k ∣ orderOf (u * t) :=
    Work.NormalComplement.Sec5Fix.ngpInverted hFT hA hC hC4 hP3 hIII hMF2 hCor1 hBC hBP h u hu hkN hkodd hkinv
  have hkcop : Nat.Coprime (orderOf k) (orderOf (u * t)) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard _ hkS) hOcop
  exact orderOf_eq_one_iff.mp (hkcop.eq_one_of_dvd hkord)

end Work.NormalComplement
