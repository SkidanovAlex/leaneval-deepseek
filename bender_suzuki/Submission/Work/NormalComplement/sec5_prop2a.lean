import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.p3Normal_of_chIIFourP3Subnormal
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3Sub.prop3b_support
import Submission.Work.ThreePoints.P3Sub.p3pkg_of_subnormal
import Submission.Work.ThreePoints.P3NeBot.app3_1
import Submission.Work.ThreePoints.P3NeBot.maximal_of_twoTransitive
import Submission.Work.ThreePoints.chIIFourP3Subnormal
import Submission.Work.ThreePoints.sec4_prop3_cd_ne_bot
import Submission.Work.ThreePoints.even_card_centralizer_fixes_three_aux
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.BrauerSuzuki.Main
import Submission.Work.ThmF.ChV12.glaubermanZJ_free
import Submission.Work.DoubleTransitivity.Sec7.ThmA
import Submission.Work.Models.models
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.NormalComplement.p2a_invol_unique
import Submission.Work.NormalComplement.p2a_pow_four
import Submission.Work.NormalComplement.p2a_appIII_data
import Submission.Work.NormalComplement.p2a_appIII_cyclic
import Submission.Work.NormalComplement.p2a_arith
import Submission.Work.ThreePoints.P3Sub.Helpers

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## Auxiliary facts for `sec5_prop2a`

Throughout, `D = twoPoint H t`, `V = centD H t = C_D(t)`, `F = O^{2'}(C_G(V))` (as the ambient
subgroup `Work.ThreePoints.p3F V`), and `S` is the Sylow `2`-subgroup of `F ⊓ H` produced by
Ch. II §4 Prop. 3 at `X = V`, `Y = A`. -/

section Aux

variable {G : Type} [Group G] [Finite G]

/-- The hypothesis `N_K(A) ≠ 1` of Ch. II §4 Prop. 3 for `X = A`: `A` is normal in `V` and
`|C_K(A)| = 2^p - 1 ≥ 3` (`Setup45A.A_CK`). -/
lemma p2a_HasNonTrivialNK_A {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ}
    {P A : Subgroup G} {r : ℕ} (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    Work.ThreePoints.HasNonTrivialNK H t A := by
  classical
  have hp2 : 2 ≤ p := h.prime.two_le
  have hcard : 3 ≤ (Work.NormalComplement.Design.CK H t A).ncard := by
    rw [h.A_CK]
    have h4 : 4 ≤ 2 ^ p := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp2
    omega
  obtain ⟨k, hk, hk1⟩ : ∃ k ∈ Work.NormalComplement.Design.CK H t A, k ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsub : Work.NormalComplement.Design.CK H t A ⊆ ({1} : Set G) := fun x hx => by
      simpa using hcon x hx
    have h1 : (Work.NormalComplement.Design.CK H t A).ncard ≤ 1 := by
      calc (Work.NormalComplement.Design.CK H t A).ncard ≤ ({1} : Set G).ncard :=
            Set.ncard_le_ncard hsub (Set.finite_singleton 1)
        _ = 1 := Set.ncard_singleton 1
    omega
  have hkK : k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t := by
    have h := hk.1
    simpa [Work.NormalComplement.Design.CK, Work.ThmF.Kset] using h
  refine ⟨k, hkK, hk1, ?_⟩
  exact Subgroup.centralizer_le_normalizer _ hk.2

/-- `A` is subnormal in `V = centD H t`: `A ≤ V` and `V ≤ N_G(A)` (`Setup45A`). -/
lemma p2a_IsSubnormalIn_A_V {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ}
    {P A : Subgroup G} {r : ℕ} (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    Submission.Blueprint.IsSubnormalIn A (Submission.Blueprint.centD H t) := by
  refine Relation.ReflTransGen.single ⟨h.A_le, ?_⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer h.A_le).mpr h.A_normal

/-- For a set in a finite type, `Nat.card ↥t = t.ncard`. -/
lemma p2a_natCard_set_eq_ncard {α : Type} [Finite α] (t : Set α) : Nat.card ↥t = t.ncard := by
  rw [Set.ncard_def]; rfl

/-- For a subgroup of a finite group, `Nat.card ↥S = (S : Set G).ncard`. -/
lemma p2a_natCard_sub_eq_ncard (S : Subgroup G) : Nat.card ↥S = (S : Set G).ncard := by
  rw [Set.ncard_def]; rfl

/-- Ch. II §4 Prop. 3 at `X = V = centD H t` with `Y = A`: the Sylow `2`-subgroup `S` of `F ⊓ H`
(`F = O^{2'}(C_G(V))`, the ambient subgroup `Work.ThreePoints.p3F V`), together with the orbit
count `|Ω_V| = |S| + 1` (Ch. II §4 Prop. 3 (a), (b)). -/
lemma p2a_p3_data (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ}
    {P A : Subgroup G} {r : ℕ} (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧
      S ≤ Work.ThreePoints.p3F (Submission.Blueprint.centD H t) ⊓ H ∧
      ¬ 2 ∣ (S.subgroupOf (Work.ThreePoints.p3F (Submission.Blueprint.centD H t) ⊓ H)).index ∧
      H ⊓ Subgroup.normalizer (Submission.Blueprint.centD H t : Set G) ≤
        Subgroup.normalizer (S : Set G) ∧
      S ⊓ Submission.Blueprint.twoPoint H t = ⊥ ∧
      S ⊔ (Submission.Blueprint.twoPoint H t ⊓
            Subgroup.normalizer (Submission.Blueprint.centD H t : Set G)) =
        H ⊓ Subgroup.normalizer (Submission.Blueprint.centD H t : Set G) ∧
      (Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t)).ncard =
        (S : Set G).ncard + 1 := by
  classical
  have hBrSz : Submission.Blueprint.BrauerSuzukiProp := Work.BrauerSuzuki.brauerSuzuki
  have hZJ : Submission.Blueprint.GlaubermanZJProp := Work.ThmF.ChV12.glaubermanZJ_free
  have hA : Submission.Blueprint.ThmAProp :=
    Work.DoubleTransitivity.Sec7.ThmA hFT hZJ hBrSz
  have hMod : Submission.Blueprint.ModelFactsProp := Work.Models.models hFT
  have hPkg : Work.ThreePoints.P3Pkg H t (Submission.Blueprint.centD H t) :=
    Work.ThreePoints.p3pkg hFT hC hA hZJ hBrSz hMod h.sit h.se h.invol h.notMem
      (Submission.Blueprint.centD H t) le_rfl
      ⟨A, h.A_ne, p2a_IsSubnormalIn_A_V h, p2a_HasNonTrivialNK_A h⟩
  obtain ⟨hP3ab, h2t⟩ := hPkg
  obtain ⟨hNGeq, S, hSpg, hSle, hSidx, hSnorm, hSD, hSsup⟩ := hP3ab
  refine ⟨S, hSpg, hSle, hSidx, hSnorm, hSD, hSsup, ?_⟩
  have ht : orderOf t = 2 := h.invol
  have htH : t ∉ H := h.notMem
  have huniq := Work.ThreePoints.P3Sub.sharpTrans_of_P3Ab_aux (H := H)
    (X₀ := Submission.Blueprint.centD H t) ht htH le_rfl h2t hSle hSnorm hSD hSsup
  have hmk : (QuotientGroup.mk t : G ⧸ H) ∈
      Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t) :=
    Work.ThreePoints.mk_t_mem_fixedPts_of_le_centD le_rfl
  have hne : (QuotientGroup.mk (1 : G) : G ⧸ H) ≠ QuotientGroup.mk t :=
    Work.ThreePoints.P3Sub.mk_one_ne_mk_t htH
  have hmem : ∀ q : ↥S, (q : G) • (QuotientGroup.mk t : G ⧸ H) ∈
      Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t) \
        {QuotientGroup.mk (1 : G)} := by
    intro q
    have hqN : (q : G) ∈ Subgroup.normalizer (Submission.Blueprint.centD H t : Set G) :=
      Work.ThreePoints.p3F_le_normalizer _ (hSle q.2).1
    have hqH : (q : G) ∈ H := (hSle q.2).2
    refine ⟨Work.ThreePoints.smul_mem_fixedPts_of_mem_normalizer hqN hmk, ?_⟩
    intro hcon
    have h2 : (q : G)⁻¹ • (QuotientGroup.mk (1 : G) : G ⧸ H) =
        (q : G)⁻¹ • ((q : G) • (QuotientGroup.mk t : G ⧸ H)) := by rw [hcon]
    rw [inv_smul_smul] at h2
    have h3 : (q : G)⁻¹ • (QuotientGroup.mk (1 : G) : G ⧸ H) =
        (QuotientGroup.mk (1 : G) : G ⧸ H) := by
      rw [Work.DoubleTransitivity.smul_mk, mul_one]
      exact QuotientGroup.eq.mpr (by simpa using H.inv_mem hqH)
    rw [h3] at h2
    exact hne h2
  have hcarddif : (Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t) \
      {QuotientGroup.mk (1 : G)}).ncard = (S : Set G).ncard := by
    refine Eq.symm (Set.ncard_congr (s := (S : Set G))
      (t := Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t) \
        {QuotientGroup.mk (1 : G)})
      (fun q : G => fun _ => q • (QuotientGroup.mk t : G ⧸ H))
      (fun (q : G) (hq : q ∈ (S : Set G)) => hmem ⟨q, hq⟩) ?_ ?_)
    · intro q₁ q₂ hq₁ hq₂ h
      have h2 : (q₂⁻¹ * q₁) • (QuotientGroup.mk t : G ⧸ H) =
          (QuotientGroup.mk t : G ⧸ H) := by
        rw [mul_smul, h, inv_smul_smul]
      have h3 : q₂⁻¹ * q₁ ∈ S ⊓ Submission.Blueprint.twoPoint H t := by
        refine Subgroup.mem_inf.mpr ⟨S.mul_mem (S.inv_mem hq₂) hq₁, ?_⟩
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact H.mul_mem (H.inv_mem (hSle hq₂).2) (hSle hq₁).2
        · have h4 : q₂⁻¹ * q₁ ∈
              MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H) :=
            MulAction.mem_stabilizer_iff.mpr h2
          rwa [Work.ThreePoints.stabilizer_mk] at h4
      have h5 : q₂⁻¹ * q₁ = 1 := by
        have h6 := h3
        rw [hSD] at h6
        simpa using h6
      exact (inv_mul_eq_one.mp h5).symm
    · intro c hc
      obtain ⟨q, hq, -⟩ := huniq c hc.1 (by simpa using hc.2)
      exact ⟨(q : G), q.2, hq⟩
  have hpt : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈
      Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t) :=
    Work.ThreePoints.pt_mem_fixedPts_of_le_centD le_rfl
  have hlt : 1 ≤ (Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t)).ncard := by
    have hpos : 0 < (Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t)).ncard :=
      Set.ncard_pos (Set.toFinite _) |>.mpr ⟨_, hpt⟩
    omega
  have hsplit := Set.ncard_sdiff_singleton_of_mem hpt
  omega

end Aux

/-- **Peterfalvi I Ch. III §5 Proposition 2 (a)** (p.184): `ut` has order `f ∈ {3,5}`.

In the §5 configuration (`Setup5`) let `D = twoPoint H t`, `V = centD H t = C_D(t)` and
`F = O^{2'}(C_G(V))` (the ambient subgroup `Work.ThreePoints.p3F V`), and let `u ∈ H` be an
involution centralising `V`.

* Ch. II §4 Prop. 3 at `X = V` with the normal `Y = A ⊴ V` (`hP3`, through `p2a_p3_data`) gives a
  Sylow `2`-subgroup `S` of `F ⊓ H`, of odd index in `F ⊓ H`, with `S ⊓ D = ⊥`,
  `S ⊔ (D ⊓ N_G(V)) = H ⊓ N_G(V)`, and the orbit count `|Ω_V| = |S| + 1`.
* `S ≤ F ≤ C_G(V)`, so the involutions of `S` are involutions of `C_H(V)`, of which there is
  exactly one (`p2a_invol_unique`): `|Inv S| = 1`.  Since `3 ≤ |Ω_V|`, also `2 ∣ |S|`.
* Every `x ∈ S` has `2`-power order and, as `S ≤ C_G(V) ≤ C_G(A)`, lies in `O^{2'}(C_G(A)) = p3F A`;
  so `p2a_pow_four` yields `x ^ 4 = 1` for all `x ∈ S`.
* Appendix III applied to `F ⧸ Z`, where `Z` is the kernel of the action on `Ω_V`
  (`p2a_appIII_data`), produces a prime `f`, an exponent `m ≥ 1` with `|Ω_V| = f ^ m`, and
  `Z ≤ D`, `F ≤ N_G(Z)`, `(u t) ^ f ∈ Z`.
* If `m = 1`, then `p2a_appIII_cyclic` gives `|S| ≤ 4`, so that `f = |S| + 1 ∈ {3,5}`; if `m ≥ 2`,
  then `p2a_arith` applied to `f ^ m = |S| + 1 = 2 ^ k + 1` forces `f = 3`.
* Finally `u` inverts `u * t`, hence inverts `(u t) ^ f`, while `t` centralises `Z` (Theorem C,
  `hC`); so `(u t) ^ f` equals its own inverse.  It lies in the odd-order group `D`, hence
  `(u t) ^ f = 1`, and then `orderOf (u * t) ∣ f` with `orderOf (u * t) ≠ 1`, i.e.
  `orderOf (u * t) = f ∈ {3,5}`. -/
theorem sec5_prop2a (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    orderOf (u * t) = 3 ∨ orderOf (u * t) = 5 := by
  classical
  -- ## Ch. II §4, Prop. 3 at `X = V = centD H t` with `Y = A`: the normal Sylow `2`-subgroup `S`
  -- of `F ⊓ H`, where `F = O^{2'}(C_G(V))`, together with `|Ω_V| = |S| + 1`.
  obtain ⟨S, hSpg, hSle, hSidx, hSnorm, hSD, hSsup, hScard⟩ := p2a_p3_data (G := G) hFT hC h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSleH : S ≤ H := fun x hx => (hSle hx).2
  have hSleF : S ≤ Work.ThreePoints.p3F (Submission.Blueprint.centD H t) :=
    fun x hx => (hSle hx).1
  -- ## every element of the `2`-group `S` has `2`-power order
  have hpowS : ∀ x ∈ S, ∃ k : ℕ, orderOf x = 2 ^ k := by
    intro x hx
    have hsub : IsPGroup 2 ↥(Subgroup.zpowers x) :=
      hSpg.to_le (Subgroup.zpowers_le.mpr hx)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(Subgroup.zpowers x))).mp hsub
    exact ⟨k, by rw [← Nat.card_zpowers x]; exact hk⟩
  -- ## `3 ≤ |Ω_V|`, so `|S| ≥ 2`
  have h3Ω : 3 ≤ (Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t)).ncard :=
    Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_centD h.se h.invol h.notMem
  have hSge2 : 2 ≤ (S : Set G).ncard := by
    have h : 3 ≤ (S : Set G).ncard + 1 := hScard ▸ h3Ω
    omega
  have hSge2c : 2 ≤ Nat.card ↥S := by
    rw [p2a_natCard_sub_eq_ncard S]; exact hSge2
  have hS2pow : ∃ k : ℕ, (S : Set G).ncard = 2 ^ k := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥S)).mp hSpg
    exact ⟨n, (p2a_natCard_sub_eq_ncard S).symm.trans hn⟩
  -- ## `S` has exactly one involution: `|Inv S| ≤ |Inv C_H(V)| = 1` and `2 ∣ |S|`
  have huniqS : (Submission.Blueprint.involutions (S : Set G)).ncard = 1 := by
    have hsub : Submission.Blueprint.involutions (S : Set G) ⊆
        Submission.Blueprint.involutions
          ((H ⊓ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) : Subgroup G)
            : Set G) := by
      rintro x ⟨hxS, hx2⟩
      exact ⟨Subgroup.mem_inf.mpr
        ⟨hSleH hxS, Work.ThreePoints.p3F_le_centralizer _ (hSleF hxS)⟩, hx2⟩
    have hcard := p2a_invol_unique (G := G) hFT hC hC4 hP3 h
    have hle : (Submission.Blueprint.involutions (S : Set G)).ncard ≤
        (Submission.Blueprint.involutions ((H ⊓ Subgroup.centralizer
          (Submission.Blueprint.centD H t : Set G) : Subgroup G) : Set G)).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have hdvdS : 2 ∣ Nat.card ↥S := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥S)).mp hSpg
      have hn0 : n ≠ 0 := by
        by_contra hcon
        have h0 : n = 0 := by omega
        rw [h0, pow_zero] at hn
        omega
      rw [hn]; exact dvd_pow_self 2 hn0
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) 2 hdvdS
    have hmem : (y : G) ∈ Submission.Blueprint.involutions (S : Set G) :=
      ⟨y.2, (Subgroup.orderOf_coe y).trans hy⟩
    have hpos : 0 < (Submission.Blueprint.involutions (S : Set G)).ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨(y : G), hmem⟩
    omega
  -- ## `S ≤ O^{2'}(C_G(A))`: `S` centralises `V ≥ A` and has `2`-power exponent
  have hSleA : ∀ x ∈ S, x ∈ Work.ThreePoints.p3F A := by
    intro x hx
    have hxCV : x ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) :=
      Work.ThreePoints.p3F_le_centralizer _ (hSleF hx)
    have hxCA : x ∈ Subgroup.centralizer (A : Set G) :=
      Subgroup.centralizer_le (fun y hy => h.A_le hy) hxCV
    obtain ⟨k, hk⟩ := hpowS x hx
    exact Work.ThreePoints.mem_p3F_of_two_pow_order hxCA hk
  -- ## the exponent of `S` divides `4` (Bender model facts through Ch. II §4 Prop. 3 at `A`)
  have hexpS : ∀ x ∈ S, x ^ 4 = 1 := fun x hx =>
    p2a_pow_four (G := G) hFT hC hC4 hMF2 h x (hSleH hx) (hSleA x hx) (hpowS x hx)
  -- ## Appendix III on the action of `F ⧸ Z` on `Ω_V`: `|Ω_V|` is a prime power
  obtain ⟨f, m, Z, hfprime, hfm, hZleD, hFleNZ, hZclause⟩ :=
    p2a_appIII_data (G := G) hFT hC hIII h hSpg hSle hSnorm hSD hSsup hSidx huniqS hScard
  haveI hfprimeI : Fact (Nat.Prime f) := ⟨hfprime⟩
  obtain ⟨k, hk⟩ := hS2pow
  have hk2 : 2 ≤ 2 ^ k := by rw [← hk]; exact hSge2
  have hfm' : f ^ m = 2 ^ k + 1 := by rw [← hfm, hScard, hk]
  -- ## `f ∈ {3, 5}`
  have hf35 : f = 3 ∨ f = 5 := by
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h
      · exfalso; rw [h0, pow_zero] at hfm'; omega
      · exact h
    rcases lt_or_ge m 2 with hm1 | hm2
    · -- ## `m = 1`: `S` has exponent at most `4` and a unique involution, so `|S| ≤ 4`
      have hm1' : m = 1 := by omega
      have hSle4 : (S : Set G).ncard ≤ 4 :=
        p2a_appIII_cyclic (G := G) hFT hC hIII h hSpg hSle hSnorm hSD hSsup hSidx huniqS
          hScard hexpS f m hfprime hfm hm1'
      have hfx : f = 2 ^ k + 1 := by rw [hm1', pow_one] at hfm'; exact hfm'
      have h4 : 2 ^ k ≤ 4 := by rw [← hk]; exact hSle4
      have h3f : 3 ≤ f := by omega
      have h5f : f ≤ 5 := by omega
      interval_cases f
      · exact Or.inl rfl
      · exact absurd hfprime (by norm_num)
      · exact Or.inr rfl
    · -- ## `m ≥ 2`: `f ^ m = 2 ^ k + 1` with `k ≥ 1` forces `f = 3`
      have hfne2 : f ≠ 2 := by
        intro h2
        rw [h2] at hfm'
        have hk1 : 1 ≤ k := by
          by_contra hcon
          have h0 : k = 0 := by omega
          rw [h0, pow_zero] at hk2
          omega
        have h2m : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega : m ≠ 0)
        have h2k : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega : k ≠ 0)
        rw [hfm'] at h2m
        obtain ⟨s, hs⟩ := h2m
        obtain ⟨t, ht⟩ := h2k
        omega
      exact Or.inl (p2a_arith hfprime hfne2 hm2 hfm')
  -- ## `u ∈ F` and `t` centralises the kernel `Z` (Theorem C)
  have huF : u ∈ Work.ThreePoints.p3F (Submission.Blueprint.centD H t) :=
    Work.ThreePoints.mem_p3F_of_involution hu.2.2 hu.2.1
  have hwZ : (u * t) ^ f ∈ Z := hZclause u hu.1 hu.2.1 hu.2.2
  have hwD : (u * t) ^ f ∈ Submission.Blueprint.twoPoint H t := hZleD hwZ
  -- ## `u` inverts `u * t`, hence inverts `(u * t) ^ f`
  have ht2 : t * t = 1 := by rw [← pow_two, ← h.invol]; exact pow_orderOf_eq_one t
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu.2.1]; exact pow_orderOf_eq_one u
  have hconj1 : u * (u * t) * u⁻¹ = (u * t)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hu2, inv_eq_of_mul_eq_one_right ht2]
    calc u * (u * t) * u = (u * u) * (t * u) := by group
      _ = t * u := by rw [hu2, one_mul]
  have huinv : u * (u * t) ^ f * u⁻¹ = ((u * t) ^ f)⁻¹ := by
    calc u * (u * t) ^ f * u⁻¹ = (u * (u * t) * u⁻¹) ^ f := by
          have h := map_pow (MulAut.conj u).toMonoidHom (u * t) f
          simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
      _ = ((u * t)⁻¹) ^ f := by rw [hconj1]
      _ = ((u * t) ^ f)⁻¹ := inv_pow _ _
  have huw : u * (u * t) ^ f = (u * t) ^ f * u :=
    hC G h.sit H h.se t h.notMem u ⟨hu.1, hu.2.1⟩ Z hZleD (hFleNZ huF) ((u * t) ^ f) hwZ
  -- ## `(u * t) ^ f` is its own inverse and lies in the odd-order group `D = twoPoint H t`
  have hxsq : (u * t) ^ f * (u * t) ^ f = 1 := by
    have h1 : (u * t) ^ f = ((u * t) ^ f)⁻¹ := by rw [← huinv, huw]; group
    have h2 : (u * t) ^ f * (u * t) ^ f = (u * t) ^ f * ((u * t) ^ f)⁻¹ :=
      congrArg (fun y => (u * t) ^ f * y) h1
    rw [h2, mul_inv_cancel]
  have hxone : (u * t) ^ f = 1 := by
    have hdvd2 : orderOf ((u * t) ^ f) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact hxsq
    have hdvdD : orderOf ((u * t) ^ f) ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) :=
      Subgroup.orderOf_dvd_natCard _ hwD
    have hodd : Odd (orderOf ((u * t) ^ f)) := Odd.of_dvd_nat (h.se.2.2 t h.notMem) hdvdD
    have h1 : orderOf ((u * t) ^ f) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h1
      · exact h1
      · rw [h1] at hodd
        obtain ⟨j, hj⟩ := hodd
        omega
    exact orderOf_eq_one_iff.mp h1
  -- ## so `orderOf (u * t)` is `f`, a prime in `{3, 5}`
  have hdvd : orderOf (u * t) ∣ f := by
    rw [orderOf_dvd_iff_pow_eq_one]; exact hxone
  have hne1 : orderOf (u * t) ≠ 1 := by
    intro h1
    have h2 : u * t = 1 := orderOf_eq_one_iff.mp h1
    have h3 : t = u := by
      calc t = u⁻¹ * (u * t) := by group
        _ = u⁻¹ := by rw [h2, mul_one]
        _ = u := inv_eq_of_mul_eq_one_right hu2
    exact h.notMem (h3 ▸ hu.1)
  rcases hfprime.eq_one_or_self_of_dvd (orderOf (u * t)) hdvd with h1 | h1
  · exact absurd h1 hne1
  · rcases hf35 with h3 | h5
    · left; rw [h1, h3]
    · right; rw [h1, h5]

end Work.NormalComplement
