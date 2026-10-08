import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.sec4_one_d
import Submission.Work.NormalComplement.p3Normal_of_chIIFourP3Subnormal
import Submission.Work.NormalComplement.section3_prop2
import Submission.Work.NormalComplement.pResidual_strategy
import Submission.Work.NormalComplement.appI_five_d_corrected
import Submission.Work.LocalPrelim.relIndex_sup_eq_relIndex_inf
import Submission.Work.NPC.Engine
import Submission.Work.Grun.pResidual

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.NormalComplement

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

theorem sec5_lemma1 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (X : Subgroup G) (hPX : P ≤ X)
    (hXV : X ≤ Submission.Blueprint.centD H t)
    (hN : H ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    X = P := by
  classical
  have hPleV : P ≤ Submission.Blueprint.centD H t := h.P_le.trans inf_le_right
  have hPleD : P ≤ Submission.Blueprint.twoPoint H t :=
    h.P_le.trans (inf_le_left.trans inf_le_right)
  have hXnA : X ≤ Subgroup.normalizer (A : Set G) := hXV.trans h.A_normal
  have hPnA : P ≤ Subgroup.normalizer (A : Set G) := hPleV.trans h.A_normal
  have hXsup : X ⊓ A ⊔ P = X := by
    refine le_antisymm (sup_le inf_le_left hPX) ?_
    intro x hx
    have hxV : x ∈ A ⊔ P := h.A_sup ▸ (hXV hx)
    have hxAP : x ∈ (↑A : Set G) * (↑P : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A P hPnA]; exact hxV
    obtain ⟨a, ha, q, hq, haq⟩ := hxAP
    have haX : a ∈ X := by
      have h1 : a = x * q⁻¹ := by rw [← haq]; group
      rw [h1]; exact X.mul_mem hx (X.inv_mem (hPX hq))
    rw [← haq]
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨haX, ha⟩) hq
  have hXinf : X ⊓ A ⊓ P = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hx1 : x ∈ X ⊓ A := (Subgroup.mem_inf.mp hx).1
    have hx2 : x ∈ P := (Subgroup.mem_inf.mp hx).2
    have hxAP : x ∈ A ⊓ P :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx1).2, hx2⟩
    simpa [h.A_inf] using hxAP
  by_cases hXA : X ⊓ A = ⊥
  · rw [← hXsup, hXA, bot_sup_eq]
  · exfalso
    have hYleX : X ⊓ A ≤ X := inf_le_left
    have hXnormY : X ≤ Subgroup.normalizer ((X ⊓ A : Subgroup G) : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro x hx y hy
      rw [Subgroup.mem_inf] at hy ⊢
      exact ⟨X.mul_mem (X.mul_mem hx hy.1) (X.inv_mem hx),
        (Subgroup.mem_normalizer_iff.mp (hXnA hx) y).mp hy.2⟩
    have hsub : Submission.Blueprint.IsSubnormalIn (X ⊓ A) X :=
      Relation.ReflTransGen.single
        ⟨hYleX, (Subgroup.normal_subgroupOf_iff_le_normalizer hYleX).mpr hXnormY⟩
    -- a nontrivial `k ∈ C_K(A)` normalising `X ⊓ A`
    have hcardCK : (Design.CK H t A).ncard = 2 ^ p - 1 := h.A_CK
    have hp2 : 2 ≤ p := h.prime.two_le
    have hpow : 2 ^ p - 1 ≠ 1 := by
      have h1 : (2 : ℕ) ^ 2 ≤ 2 ^ p := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hp2
      have h4 : 4 ≤ 2 ^ p := by simpa using h1
      omega
    have h1mem : (1 : G) ∈ Design.CK H t A := by
      refine ⟨⟨(Submission.Blueprint.twoPoint H t).one_mem, by simp⟩, ?_⟩
      exact (Subgroup.centralizer (A : Set G)).one_mem
    obtain ⟨k, hk, hk1⟩ : ∃ k ∈ Design.CK H t A, k ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have hsingle : Design.CK H t A = {1} :=
        Set.eq_singleton_iff_unique_mem.mpr ⟨h1mem, hcon⟩
      rw [hsingle, Set.ncard_singleton] at hcardCK
      exact hpow hcardCK.symm
    have hkK : k ∈ Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t := hk.1
    have hkC : k ∈ Subgroup.centralizer (A : Set G) := hk.2
    have hkN : k ∈ Subgroup.normalizer ((X ⊓ A : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      apply le_antisymm
      · intro x hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        rw [Subgroup.mem_inf] at hy ⊢
        have hcomm : y * k = k * y := (Subgroup.mem_centralizer_iff.mp hkC) y hy.2
        have hyx' : k * y * k⁻¹ = x := by
          rw [← hyx]
          exact (MulAut.conj_apply k y).symm
        have hxy : x = y := by rw [← hyx']; rw [← hcomm]; group
        rw [hxy]; exact hy
      · intro x hx
        refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
        rw [Subgroup.mem_inf] at hx
        have hcomm : x * k = k * x := (Subgroup.mem_centralizer_iff.mp hkC) x hx.2
        have h1 : (↑(MulAut.conj k) : G →* G) x = k * x * k⁻¹ := MulAut.conj_apply k x
        rw [h1, ← hcomm]; group
    have hkIn : ∃ k' ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t,
        k' ≠ 1 ∧ k' ∈ Subgroup.normalizer ((X ⊓ A : Subgroup G) : Set G) :=
      ⟨k, hkK, hk1, hkN⟩
    have hP3 := hP3 G h.sit H h.se t h.invol h.notMem X (X ⊓ A) hXV hXA hsub hkIn
    obtain ⟨hNG, S, hS2, hSleFH, -, hSN, -, hSsup⟩ := hP3
    -- ## `N_H(P) ≤ C_H(P)`
    have hPleC : P ≤ Subgroup.centralizer (P : Set G) := by
      haveI : Fact p.Prime := ⟨h.prime⟩
      haveI : IsCyclic ↥P := isCyclic_of_prime_card h.P_card
      haveI : IsMulCommutative ↥P := IsCyclic.isMulCommutative
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hc : (⟨y, hy⟩ : ↥P) * ⟨x, hx⟩ = (⟨x, hx⟩ : ↥P) * ⟨y, hy⟩ :=
        isMulCommutative_iff.mp (inferInstance : IsMulCommutative ↥P) ⟨y, hy⟩ ⟨x, hx⟩
      simpa using congrArg Subtype.val hc
    have hNH_le_C : H ⊓ Subgroup.normalizer (P : Set G) ≤
        Subgroup.centralizer (P : Set G) := by
      intro h0 hh0
      obtain ⟨hh0H, hh0NP⟩ := Subgroup.mem_inf.mp hh0
      have h0mem : h0 ∈ H ⊓ Subgroup.normalizer (X : Set G) :=
        Subgroup.mem_inf.mpr ⟨hh0H, hN hh0⟩
      rw [← hSsup] at h0mem
      have hBnormS : (Submission.Blueprint.twoPoint H t ⊓
          Subgroup.normalizer (X : Set G)) ≤ Subgroup.normalizer (S : Set G) :=
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans hSN
      have h0mem' : h0 ∈ (↑S : Set G) *
          (↑(Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left S _ hBnormS]
        exact h0mem
      obtain ⟨s, hs, d, hd, hsd⟩ := h0mem'
      have hsC : s ∈ Subgroup.centralizer (P : Set G) := by
        have hsF : s ∈ (oddResidual ↥(Subgroup.centralizer (X : Set G))).map
            (Subgroup.centralizer (X : Set G)).subtype :=
          (Subgroup.mem_inf.mp (hSleFH hs)).1
        exact (Subgroup.centralizer_le hPX) ((Subgroup.map_subtype_le _) hsF)
      have hdD : d ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp hd).1
      have hdNP : d ∈ Subgroup.normalizer (P : Set G) := by
        have hsNP : s ∈ Subgroup.normalizer (P : Set G) :=
          Subgroup.centralizer_le_normalizer _ hsC
        have h1 : d = s⁻¹ * h0 := by rw [← hsd]; group
        rw [h1]
        exact (Subgroup.normalizer (P : Set G)).mul_mem
          ((Subgroup.normalizer (P : Set G)).inv_mem hsNP) hh0NP
      have hdDP : d ∈ Submission.Blueprint.twoPoint H t ⊓
          Subgroup.normalizer (P : Set G) := Subgroup.mem_inf.mpr ⟨hdD, hdNP⟩
      have hdC : d ∈ Subgroup.centralizer (P : Set G) := by
        rw [(sec4_one_c hFT h.toSetup45A).1] at hdDP
        exact (sup_le inf_le_right hPleC) hdDP
      rw [← hsd]
      exact (Subgroup.centralizer (P : Set G)).mul_mem hsC hdC
    -- ## `P` is a Sylow `p`-subgroup of `W`: `D` is a Hall subgroup of `H`
    haveI : Fact p.Prime := ⟨h.prime⟩
    have hHall : Nat.Coprime (Nat.card ↥(Submission.Blueprint.twoPoint H t))
        ((Submission.Blueprint.twoPoint H t).subgroupOf H).index := by sorry
    have hPsylW : IsSylowIn p P W := by
      have hPleE : P ≤ Design.Egrp H t W := fun x hx => (h.P_le hx).1
      refine ⟨?_, hPleE.trans inf_le_left, ?_⟩
      · exact IsPGroup.iff_card.mpr ⟨1, by rw [pow_one]; exact h.P_card⟩
      · -- `p ∤ [W : P]`
        have hpD : p ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
          have hd := Subgroup.card_dvd_of_le (H := P) (K := Submission.Blueprint.twoPoint H t)
            hPleD
          rwa [h.P_card] at hd
        have hDidx : ¬ p ∣ ((Submission.Blueprint.twoPoint H t).subgroupOf H).index := by
          intro hb
          have h1 : p ∣ 1 := by
            rw [← hHall]
            exact Nat.dvd_gcd hpD hb
          exact h.prime.ne_one (Nat.dvd_one.mp h1)
        have hDNN : Submission.Blueprint.twoPoint H t ≤
            Subgroup.normalizer (W : Set G) :=
          (inf_le_left).trans h.normal
        have hDW : ((Design.Egrp H t W).subgroupOf W).index =
            ((Submission.Blueprint.twoPoint H t).subgroupOf H).index := by
          have hkey := Work.LocalPrelim.relIndex_sup_eq_relIndex_inf_auxL
            (H := Submission.Blueprint.twoPoint H t) (W := W) hDNN
          rw [sup_comm (Submission.Blueprint.twoPoint H t) W, h.sup] at hkey
          rw [show Design.Egrp H t W =
            Submission.Blueprint.twoPoint H t ⊓ W from inf_comm _ _]
          exact hkey.symm
        have hEWidx : ¬ p ∣ ((Design.Egrp H t W).subgroupOf W).index := by
          rw [hDW]; exact hDidx
        have hPEidx : ¬ p ∣ (P.subgroupOf (Design.Egrp H t W)).index :=
          (sylowIn_of_le_of_le (p := p) h.P_syl hPleE inf_le_right).2.2
        intro hd
        have hkey := Subgroup.relIndex_mul_relIndex (H := P)
          (K := Design.Egrp H t W) (L := W) hPleE inf_le_left
        have hd' : p ∣ P.relIndex W := hd
        rw [← hkey] at hd'
        rcases h.prime.dvd_mul.mp hd' with h' | h'
        · exact hPEidx h'
        · exact hEWidx h'
    have hPpW : IsPGroup p (P.subgroupOf W) :=
      hPsylW.1.comap_of_injective W.subtype W.subtype_injective
    -- `N_W(P) ≤ C_G(P)` in the ambient group
    have hNW_le_CG : (Subgroup.normalizer (P : Set G)).subgroupOf W ≤
        (Subgroup.centralizer (P : Set G)).subgroupOf W := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hNH_le_C (Subgroup.mem_inf.mpr ⟨h.le x.2, hx⟩)
    -- the Burnside hypothesis inside `↥W`
    have hBurnHyp : Subgroup.normalizer
          ((hPpW.toSylow hPsylW.2.2 : Sylow p ↥W) : Set ↥W) ≤
        Subgroup.centralizer ((hPpW.toSylow hPsylW.2.2 : Sylow p ↥W) : Set ↥W) := by
      have hcoe : ((hPpW.toSylow hPsylW.2.2 : Sylow p ↥W) : Set ↥W) =
          (P.subgroupOf W : Set ↥W) :=
        congrArg (fun K : Subgroup ↥W => (K : Set ↥W))
          (IsPGroup.toSylow_coe hPpW hPsylW.2.2)
      rw [hcoe, ← Subgroup.subgroupOf_normalizer_eq (H := P) hPsylW.2.1]
      refine hNW_le_CG.trans ?_
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyP : (y : G) ∈ P := by simpa [Subgroup.mem_subgroupOf] using hy
      have hxy : (y : G) * (x : G) = (x : G) * (y : G) :=
        (Subgroup.mem_centralizer_iff.mp hx) (y : G) hyP
      exact Subtype.ext hxy
    have hburn : Work.NPC.HasNormalPComplement p ↥W :=
      Work.NPC.burnside_npc (hPpW.toSylow hPsylW.2.2) hBurnHyp
    obtain ⟨Nn, hNn⟩ := hburn
    haveI : Nn.Normal := hNn.normal
    have hNne : Nn ≠ ⊤ := by
      intro htop
      have hpW : p ∣ Nat.card ↥W := by
        have hd := Subgroup.card_dvd_of_le (H := P) (K := W) hPsylW.2.1
        rwa [h.P_card] at hd
      have hpd : p ∣ Nat.card Nn := by rw [htop, Subgroup.card_top]; exact hpW
      have hp1 : p ∣ 1 := by
        have hg : Nat.gcd (Nat.card Nn) p = 1 := hNn.coprime_card
        rw [← hg]; exact Nat.dvd_gcd hpd (dvd_refl p)
      exact h.prime.ne_one (Nat.dvd_one.mp hp1)
    -- `O^p(W) ≤ Nn`, hence `O^p(W) < W`
    have hprN : Work.NPC.Frobenius.pResidual p ↥W ≤ Nn := by
      rw [Work.NPC.Frobenius.pResidual, Subgroup.closure_le]
      rintro x hx
      have hdvd : orderOf ((QuotientGroup.mk' Nn) x) ∣ orderOf x := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      obtain ⟨kk, hkk⟩ := (IsPGroup.iff_orderOf.mp hNn.isPGroup_quotient)
        ((QuotientGroup.mk' Nn) x)
      have hpk : p ^ kk ∣ orderOf x := hkk ▸ hdvd
      have hk0 : kk = 0 := by
        by_contra hk
        have hpkk : p ∣ p ^ kk := by
          simpa using (pow_dvd_pow p (Nat.one_le_iff_ne_zero.mpr hk) : p ^ 1 ∣ p ^ kk)
        exact hx (hpkk.trans hpk)
      have hone : (QuotientGroup.mk' Nn) x = 1 := by
        rw [← orderOf_eq_one_iff, hkk, hk0, pow_zero]
      rw [← QuotientGroup.ker_mk' Nn]
      exact MonoidHom.mem_ker.mpr hone
    have hpr_lt : Work.Grun.pResidual p W < W := by
      have hle : Work.Grun.pResidual p W ≤ Nn.map W.subtype := by
        rw [Work.Grun.pResidual_eq_map_pResidual p W]
        exact Subgroup.map_mono hprN
      have hlt : Nn.map W.subtype < W := by
        refine lt_of_le_of_ne (Subgroup.map_subtype_le _) ?_
        intro heq
        apply hNne
        rw [eq_top_iff]
        intro x _
        have hxW : (x : G) ∈ Nn.map W.subtype := by rw [heq]; exact x.2
        obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hxW
        have hnx' : n = x := Subtype.ext hnx
        rw [← hnx']; exact hn
      exact lt_of_le_of_lt hle hlt
    have hpr_ne : ¬ W ≤ Work.Grun.pResidual p W := hpr_lt.2
    obtain ⟨y, hyW, hyK⟩ := Set.not_subset.mp hpr_ne
    have hEidx : ¬ p ∣ ((Design.Egrp H t W).subgroupOf W).index := by
      intro hd
      have hle : (P.subgroupOf W) ≤ (Design.Egrp H t W).subgroupOf W := by
        intro z hz
        rw [Subgroup.mem_subgroupOf] at hz ⊢
        exact (h.P_le hz).1
      exact hPsylW.2.2 (hd.trans (Subgroup.index_dvd_of_le hle))
    obtain ⟨W₁, hW₁lt, hW₁H, hHW₁, hW₁D⟩ :=
      pResidual_strategy (p := p) (E := Design.Egrp H t W) (W := W)
        (D := Submission.Blueprint.twoPoint H t) (H := H) (y := y)
        inf_le_left inf_le_right hEidx h.le h.normal h.sup hyW hyK
    have hcard := h.minW.2.2.2 W₁ hW₁H hHW₁ hW₁D
    have hcardlt : Nat.card ↥W₁ < Nat.card ↥W := by
      refine Nat.lt_of_le_of_ne
        (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hW₁lt.1)) ?_
      intro heq
      have hWW₁ : W ≤ W₁ :=
        le_of_eq (Subgroup.eq_of_le_of_card_ge hW₁lt.1 (le_of_eq heq.symm)).symm
      exact hW₁lt.2 hWW₁
    omega

end Work.NormalComplement
