import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.ThmC.coprime_generation
import Submission.Work.ThreePoints.ThmC.pPrimeCoreSub_conj
import Submission.Work.ThreePoints.ThmC.eq_iSup_sylow
import Submission.Work.ThreePoints.ThmC.isSolvable_sup_zpowers
import Submission.Work.ThreePoints.ThmC.card_sup_zpowers_dvd
import Submission.Work.Coprime.All
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.ThmC.app1_2
import Submission.Work.DoubleTransitivity.App1.app1_2
import Submission.Work.GlaubermanZJ.pPrimeCore_eq_fitting
import Submission.Work.Fitting.piCore_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Work.ThreePoints.ThmC

open Submission.Blueprint

/-- **Peterfalvi I Ch. I §6 Prop. 2, Step 1.**  Let `H₁`, `H₂` be conjugates of a strongly
embedded `H`, `s` an involution in `H₁`, and `K ≤ H₁ ⊓ H₂` a `p`-subgroup with `K^s = K` all of
whose inverted elements lie in a subgroup whose centralizer meets `H₂ ⊓ H₂^s` inside `H₁`.  If
`H₂ ⊓ H₂^s` has odd order, then `O_{p'}(H₂ ⊓ H₂^s) ≤ O_{p'}(H₁ ⊓ H₂ ⊓ H₂^s)`. -/
theorem step1_pPrimeCore {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {p : ℕ} (hp : p.Prime)
    {H₁ H₂ K : Subgroup G} {s : G}
    (hH₁ : ∃ g : G, H₁ = Submission.Blueprint.conj g H)
    (hH₂ : ∃ g : G, H₂ = Submission.Blueprint.conj g H)
    (hs : orderOf s = 2) (hsH₁ : s ∈ H₁)
    (hKH₁ : K ≤ H₁) (hKH₂ : K ≤ H₂) (hKs : Submission.Blueprint.conj s K = K)
    (hKp : IsPGroup p K)
    (hodd : Odd (Nat.card (H₂ ⊓ Submission.Blueprint.conj s H₂ : Subgroup G)))
    (hC : Subgroup.centralizer
        (Subgroup.closure (Submission.Blueprint.invertedBy K s) : Set G) ⊓ H₂ ⊓
        Submission.Blueprint.conj s H₂ ≤ H₁) :
    Work.ThreePoints.ThmC.pPrimeCoreSub p (H₂ ⊓ Submission.Blueprint.conj s H₂) ≤
      Work.ThreePoints.ThmC.pPrimeCoreSub p (H₁ ⊓ H₂ ⊓ Submission.Blueprint.conj s H₂) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g₁, hg₁⟩ := hH₁
  obtain ⟨g₂, hg₂⟩ := hH₂
  have hH1se : IsStronglyEmbedded H₁ := by rw [hg₁]; exact conj_stronglyEmbedded hH g₁
  have hH2se : IsStronglyEmbedded H₂ := by rw [hg₂]; exact conj_stronglyEmbedded hH g₂
  -- membership helpers for `K ⊔ ⟨s⟩`
  have hsupL : ∀ {x : G}, x ∈ K → x ∈ K ⊔ Subgroup.zpowers s :=
    fun hx => (le_sup_left : (K : Subgroup G) ≤ K ⊔ Subgroup.zpowers s) hx
  have hsupR : ∀ {x : G}, x ∈ Subgroup.zpowers s → x ∈ K ⊔ Subgroup.zpowers s :=
    fun hx => (le_sup_right : (Subgroup.zpowers s : Subgroup G) ≤ K ⊔ Subgroup.zpowers s) hx
  -- `s` is an involution
  have hs1 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs] at h
    simpa [pow_two] using h
  have hconj_ss : ∀ X : Subgroup G, conj s (conj s X) = X := by
    intro X
    rw [← conj_mul, hs1, conj_one]
  have hconj_inf : ∀ (g : G) (A B : Subgroup G), conj g (A ⊓ B) = conj g A ⊓ conj g B := by
    intro g A B
    exact Subgroup.map_inf A B (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hH2sse : IsStronglyEmbedded (conj s H₂) := conj_stronglyEmbedded hH2se s
  have hN2 : Subgroup.normalizer (H₂ : Set G) = H₂ := IsStronglyEmbedded.normalizer_eq hH2se
  have hN2s : Subgroup.normalizer (conj s H₂ : Set G) = conj s H₂ :=
    IsStronglyEmbedded.normalizer_eq hH2sse
  -- abbreviations
  set D : Subgroup G := H₂ ⊓ conj s H₂ with hDdef
  set Y : Subgroup G := pPrimeCoreSub p D with hYdef
  have hDconj : conj s D = D := by
    rw [hDdef, hconj_inf s, hconj_ss, inf_comm]
  have hYD : Y ≤ D := by rw [hYdef]; exact Subgroup.map_subtype_le _
  have hYH2 : Y ≤ H₂ := hYD.trans (by rw [hDdef]; exact inf_le_left)
  have hYH2s : Y ≤ conj s H₂ := hYD.trans (by rw [hDdef]; exact inf_le_right)
  have hoddY : Odd (Nat.card ↥Y) := Odd.of_dvd (Subgroup.card_dvd_of_le hYD) hodd
  have hcopY : Nat.Coprime (Nat.card ↥Y) p := by
    rw [hYdef, Subgroup.card_map_of_injective D.subtype_injective]
    rw [Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
    exact (Work.GlaubermanZJ.isPiNat_ne_iff_coprime hp).mp
      (Work.Fitting.piCore_isPiNat ↥D (fun q => q ≠ p))
  have hKD : K ≤ D := by
    rw [hDdef]
    refine le_inf hKH₂ ?_
    rw [← hKs]
    exact Subgroup.map_mono hKH₂
  have hKodd : Odd (Nat.card ↥K) := Odd.of_dvd (Subgroup.card_dvd_of_le hKD) hodd
  have hYs : conj s Y = Y := by
    rw [hYdef, ← pPrimeCoreSub_conj p hp D s, hDconj]
  have hsNY : s ∈ Subgroup.normalizer (Y : Set G) :=
    (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer s Y).mp hYs
  have hDNY : D ≤ Subgroup.normalizer (Y : Set G) := by
    intro d hd
    rw [← Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer d Y]
    have hdA : d ∈ H₂ := (Subgroup.mem_inf.mp (hDdef ▸ hd)).1
    have hdB : d ∈ conj s H₂ := (Subgroup.mem_inf.mp (hDdef ▸ hd)).2
    have h1 : conj d H₂ = H₂ :=
      (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer d H₂).mpr (by rw [hN2]; exact hdA)
    have h2 : conj d (conj s H₂) = conj s H₂ :=
      (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer d (conj s H₂)).mpr
        (by rw [hN2s]; exact hdB)
    rw [hYdef, ← pPrimeCoreSub_conj p hp D d, hDdef, hconj_inf d, h1, h2]
  have hMle : K ⊔ Subgroup.zpowers s ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le (hKD.trans hDNY) (Subgroup.zpowers_le.mpr hsNY)
  have hMleH1 : K ⊔ Subgroup.zpowers s ≤ H₁ :=
    sup_le hKH₁ (Subgroup.zpowers_le.mpr hsH₁)
  have hsolM : Group.IsSolvable ↥(K ⊔ Subgroup.zpowers s) := Work.ThreePoints.ThmC.isSolvable_sup_zpowers hp hKp hs hKs
  have hcopM : Nat.Coprime (Nat.card ↥(K ⊔ Subgroup.zpowers s)) (Nat.card ↥Y) := by
    refine Nat.Coprime.coprime_dvd_left (Work.ThreePoints.ThmC.card_sup_zpowers_dvd (G := G) hs hKs) ?_
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hKp
    rw [ha, Nat.coprime_mul_iff_left]
    refine ⟨?_, Nat.Coprime.pow_left a hcopY.symm⟩
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)]
    rintro ⟨b, hb⟩
    obtain ⟨c, hc⟩ := hoddY
    omega
  haveI : FT.Normalizes (K ⊔ Subgroup.zpowers s) Y := ⟨hMle⟩
  -- choose the invariant Sylows
  have hEx : ∀ q : ℕ, q.Prime → ∃ P : Sylow q ↥Y,
      ∀ a : ↥(K ⊔ Subgroup.zpowers s), a • P = P := by
    intro q hq
    haveI : Fact q.Prime := ⟨hq⟩
    exact Work.Coprime.exists_invariant_sylow ↥(K ⊔ Subgroup.zpowers s) hcopM (Or.inl hsolM) q
  let Q : (q : ℕ) → Sylow q ↥Y := fun q =>
    if hq : q.Prime then (hEx q hq).choose else Classical.arbitrary _
  have hQinv : ∀ (q : ℕ) (hq : q.Prime) (a : ↥(K ⊔ Subgroup.zpowers s)), a • Q q = Q q := by
    intro q hq a
    have h : Q q = (hEx q hq).choose := by
      show (if hq' : q.Prime then (hEx q hq').choose else Classical.arbitrary _)
        = (hEx q hq).choose
      rw [dif_pos hq]
    rw [h]
    exact (hEx q hq).choose_spec a
  have hQinv' : ∀ (q : ℕ) (hq : q.Prime) (a : ↥(K ⊔ Subgroup.zpowers s)),
      a • (Q q : Subgroup ↥Y) = (Q q : Subgroup ↥Y) := by
    intro q hq a
    rw [← Sylow.pointwise_smul_def]
    exact congrArg (fun S : Sylow q ↥Y => (S : Subgroup ↥Y)) (hQinv q hq a)
  -- each invariant Sylow lies in `H₁`
  have hQle : ∀ q, q ∈ (Nat.card ↥Y).primeFactors →
      ((Q q : Subgroup ↥Y).map Y.subtype) ≤ H₁ := by
    intro q hq
    have hqprime : q.Prime := (Nat.mem_primeFactors.mp hq).1
    haveI : Fact q.Prime := ⟨hqprime⟩
    set QG : Subgroup G := (Q q : Subgroup ↥Y).map Y.subtype with hQG
    have hQGY : QG ≤ Y := Subgroup.map_subtype_le _
    have hQGle : QG ≤ D := hQGY.trans hYD
    have hQGp : IsPGroup q QG := IsPGroup.map (Q q).isPGroup' Y.subtype
    haveI : Group.IsSolvable ↥QG := by
      haveI : Group.IsNilpotent ↥QG := hQGp.isNilpotent
      exact IsNilpotent.to_isSolvable
    have hMnormQG : K ⊔ Subgroup.zpowers s ≤ Subgroup.normalizer (QG : Set G) := by
      intro m hm
      have hmY : m ∈ Subgroup.normalizer (Y : Set G) := hMle hm
      rw [← Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer m QG]
      rw [hQG, Work.DoubleTransitivity.App1.conj_map_subtype Y m hmY (Q q : Subgroup ↥Y)]
      have hca : Work.DoubleTransitivity.App1.conjAut Y m hmY
          = MulDistribMulAction.toMulAut ↥(K ⊔ Subgroup.zpowers s) ↥Y ⟨m, hm⟩ :=
        Work.DoubleTransitivity.App1.conjAut_eq_toMulAut ⟨m, hm⟩
      rw [hca]
      rw [← Work.DoubleTransitivity.App1.smul_eq_map,
        Work.DoubleTransitivity.App1.smul_eq_toMulAut_smul]
      exact congrArg (fun S : Subgroup ↥Y => S.map Y.subtype) (hQinv' q hqprime ⟨m, hm⟩)
    haveI hyNQ : FT.Normalizes (K ⊔ Subgroup.zpowers s) QG := ⟨hMnormQG⟩
    have hcopQG : Nat.Coprime (Nat.card ↥(K ⊔ Subgroup.zpowers s)) (Nat.card ↥QG) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hQGY) hcopM
    let u : ↥(K ⊔ Subgroup.zpowers s) := ⟨s, hsupR (Subgroup.mem_zpowers s)⟩
    have hu : orderOf u = 2 := by
      rw [← Subgroup.orderOf_coe u]
      exact hs
    have huX : ∀ x ∈ K.subgroupOf (K ⊔ Subgroup.zpowers s),
        u * x * u⁻¹ ∈ K.subgroupOf (K ⊔ Subgroup.zpowers s) := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      show s * (x : G) * s⁻¹ ∈ K
      have hmem : (MulAut.conj s) (x : G) ∈ conj s K :=
        Subgroup.mem_map_of_mem _ hx
      rw [hKs] at hmem
      simpa [MulAut.conj_apply] using hmem
    have htop : K.subgroupOf (K ⊔ Subgroup.zpowers s) ⊔ Subgroup.zpowers u = ⊤ := by
      have hle : Subgroup.zpowers s ≤ Subgroup.normalizer (K : Set G) :=
        Subgroup.zpowers_le.mpr
          ((Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer s K).mp hKs)
      have hcoe : (↑(K ⊔ Subgroup.zpowers s) : Set G) =
          (K : Set G) * (Subgroup.zpowers s : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left K (Subgroup.zpowers s) hle
      rw [eq_top_iff]
      intro m _
      have hm : (m : G) ∈ (K : Set G) * (Subgroup.zpowers s : Set G) := by
        have hm' : (m : G) ∈ (↑(K ⊔ Subgroup.zpowers s) : Set G) := m.2
        rw [hcoe] at hm'
        exact hm'
      obtain ⟨k, hk, t, ht, hkt⟩ := hm
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ht
      have hut : (⟨t, hsupR ht⟩ : ↥(K ⊔ Subgroup.zpowers s)) = u ^ n := by
        apply Subtype.ext
        show t = (s : G) ^ n
        exact hn.symm
      have hmul : m = (⟨k, hsupL hk⟩ : ↥(K ⊔ Subgroup.zpowers s)) *
          (⟨t, hsupR ht⟩ : ↥(K ⊔ Subgroup.zpowers s)) := by
        apply Subtype.ext
        rw [Subgroup.coe_mul]
        exact hkt.symm
      rw [hmul, hut]
      refine Subgroup.mul_mem _ ?_ ?_
      · exact (le_sup_left : (K.subgroupOf (K ⊔ Subgroup.zpowers s) : Subgroup ↥(K ⊔ Subgroup.zpowers s))
            ≤ K.subgroupOf (K ⊔ Subgroup.zpowers s) ⊔ Subgroup.zpowers u)
          (Subgroup.mem_subgroupOf.mpr hk)
      · exact (le_sup_right : (Subgroup.zpowers u : Subgroup ↥(K ⊔ Subgroup.zpowers s))
            ≤ K.subgroupOf (K ⊔ Subgroup.zpowers s) ⊔ Subgroup.zpowers u)
          (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩)
    have hgen := coprime_generation (M := ↥(K ⊔ Subgroup.zpowers s)) (Y := ↥QG)
      (X := K.subgroupOf (K ⊔ Subgroup.zpowers s)) (u := u)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv]; exact hKodd)
      hu huX htop hcopQG ‹Group.IsSolvable ↥QG›
    have hsub : (Subgroup.closure
        (({y : ↥QG | ∀ x : ↥(K ⊔ Subgroup.zpowers s), x ∈ K.subgroupOf (K ⊔ Subgroup.zpowers s) →
              u * x * u⁻¹ = x⁻¹ → x • y = y} : Set ↥QG) ∪
          (⋃ v ∈ ({v : ↥(K ⊔ Subgroup.zpowers s) | orderOf v = 2} : Set _),
              ({y : ↥QG | v • y = y} : Set ↥QG)))) ≤ (H₁ ⊓ QG).subgroupOf QG := by
      rw [Subgroup.closure_le]
      rintro y (hy | hy)
      · rw [Set.mem_ofPred_eq] at hy
        have hyD : (y : G) ∈ D := hQGle y.2
        have hyD2 : (y : G) ∈ H₂ := (Subgroup.mem_inf.mp (hDdef ▸ hyD)).1
        have hyD2s : (y : G) ∈ conj s H₂ := (Subgroup.mem_inf.mp (hDdef ▸ hyD)).2
        have hycent : (y : G) ∈ Subgroup.centralizer
            (Subgroup.closure (Submission.Blueprint.invertedBy K s) : Set G) := by
          rw [Subgroup.centralizer_closure]
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          obtain ⟨hzK, hzinv⟩ := hz
          have hx : (⟨z, hsupL hzK⟩ : ↥(K ⊔ Subgroup.zpowers s))
              ∈ K.subgroupOf (K ⊔ Subgroup.zpowers s) := Subgroup.mem_subgroupOf.mpr hzK
          have hux : u * (⟨z, hsupL hzK⟩ : ↥(K ⊔ Subgroup.zpowers s)) * u⁻¹
              = (⟨z, hsupL hzK⟩ : ↥(K ⊔ Subgroup.zpowers s))⁻¹ := by
            apply Subtype.ext
            simpa [u, Subgroup.coe_mul, Subgroup.coe_inv] using hzinv
          have hfix : (⟨z, hsupL hzK⟩ : ↥(K ⊔ Subgroup.zpowers s)) • y = y := hy _ hx hux
          have hfix' : z * (y : G) * z⁻¹ = (y : G) := by
            have := congrArg (Subtype.val) hfix
            rwa [FT.conj_smul_coe] at this
          show z * (y : G) = (y : G) * z
          have h := congrArg (· * z) hfix'
          simpa [mul_assoc] using h
        refine Subgroup.mem_subgroupOf.mpr ⟨hC ⟨⟨hycent, hyD2⟩, hyD2s⟩, y.2⟩
      · rw [Set.mem_iUnion] at hy
        obtain ⟨v, hyv⟩ := hy
        rw [Set.mem_iUnion] at hyv
        obtain ⟨hv2, hyfix⟩ := hyv
        rw [Set.mem_ofPred_eq] at hyfix hv2
        have hvH1 : (v : G) ∈ H₁ := hMleH1 v.2
        have hvord : orderOf (v : G) = 2 := by
          rw [Subgroup.orderOf_coe]; exact hv2
        have hvfix : (v : G) * (y : G) * (v : G)⁻¹ = (y : G) := by
          have := congrArg (Subtype.val) hyfix
          rwa [FT.conj_smul_coe] at this
        have hcent : (y : G) ∈ Subgroup.centralizer ({(v : G)} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have h := congrArg (· * (v : G)) hvfix
          have h' : (v : G) * (y : G) = (y : G) * (v : G) := by simpa [mul_assoc] using h
          exact h'.symm
        exact Subgroup.mem_subgroupOf.mpr
          ⟨IsStronglyEmbedded.centralizer_le hH1se hvH1 (by omega) hcent, y.2⟩
    rw [hgen] at hsub
    intro x hx
    exact (Subgroup.mem_subgroupOf.mp (hsub (Subgroup.mem_top (⟨x, hx⟩ : ↥QG)))).1
  have hYH1 : Y ≤ H₁ := by
    rw [eq_iSup_sylow Y Q]
    exact iSup_le fun q => iSup_le fun hq => hQle q hq
  set NN : Subgroup G := H₁ ⊓ H₂ ⊓ conj s H₂ with hNNdef
  have hYleN : Y ≤ NN := le_inf (le_inf hYH1 hYH2) hYH2s
  have hNleD : NN ≤ D := by
    rw [hNNdef, hDdef]
    exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hNnorm : (Y.subgroupOf NN).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hYleN]
    intro y n hy hn
    have hn' : n ∈ D := hNleD hn
    have hnrm : n ∈ Subgroup.normalizer (Y : Set G) := hDNY hn'
    exact (Subgroup.mem_normalizer_iff.mp hnrm y).mp hy
  have hpi : Work.Fitting.IsPiNat (fun q => q ≠ p) (Nat.card ↥(Y.subgroupOf NN)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYleN).toEquiv]
    exact (Work.GlaubermanZJ.isPiNat_ne_iff_coprime hp).mpr hcopY
  have hcore : Y.subgroupOf NN ≤ Work.Fitting.pPrimeCore p ↥NN :=
    Work.Fitting.le_piCore hNnorm hpi
  have hfinal : Y ≤ pPrimeCoreSub p NN := by
    have h1 : Y ≤ (Work.Fitting.pPrimeCore p ↥NN).map NN.subtype := by
      calc Y = (Y.subgroupOf NN).map NN.subtype := (Subgroup.map_subgroupOf_eq_of_le hYleN).symm
        _ ≤ _ := Subgroup.map_mono hcore
    have h2 : (Work.Fitting.pPrimeCore p ↥NN) = Submission.Blueprint.pPrimeCore p ↥NN :=
      (Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp).symm
    rw [h2] at h1
    exact h1
  rw [hYdef, hDdef, hNNdef] at hfinal
  exact hfinal

end Work.ThreePoints.ThmC
