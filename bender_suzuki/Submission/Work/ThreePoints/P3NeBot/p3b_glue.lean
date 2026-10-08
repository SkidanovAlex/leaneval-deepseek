import Mathlib
import Submission.Work.ThreePoints.P3NeBot.p3_b_aux
import Submission.Work.ThreePoints.P3NeBot.p3_lemma1
import Submission.Work.ThreePoints.P3NeBot.p3_appI_one
import Submission.Work.ThreePoints.P3NeBot.maximal_of_twoTransitive
import Submission.Work.ThreePoints.P3Sub.ch1s4_prop1
import Submission.Work.ThreePoints.P3Sub.prop3b_support
import Submission.Work.ThreePoints.P3Sub.modelSplitB
import Submission.Work.ThreePoints.P3NeBot.sylow_le_normalizer
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThreePoints.Sec2b
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.ThreePoints.P3NeBot.app3_1
import Submission.Work.ThreePoints.P3Sub.Helpers
import Submission.Work.ThreePoints.involutions_conj_of_stronglyEmbedded
import Submission.Work.DoubleTransitivity.App2.app2_2
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.ThreePoints.P3Sub.p3F_subgroupOf_normalizer_normal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints.P3NeBot

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! ## Ch. II §4 Prop. 1 (a)/(b) -/

/-- Peterfalvi I Ch. II §4 Prop. 1 (a): for `X` fixing at least three points of `Ω = G ⧸ H`, the
centraliser `C_M(X)` of `X` in a fixed point `M = H^g ⊇ X` has even order.  (This is
`Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz`, with Ch. I §4 Prop. 2
supplied by `Work.ThreePoints.P3Sub.ch1_s4_prop2_of_brsz`; the `hA` argument is unused but kept
in the signature for compatibility.) -/
theorem even_card_centralizer_of_fixes_three
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X M : Subgroup G}
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (hM : ∃ g : G, M = Submission.Blueprint.conj g H) (hXM : X ≤ M) :
    Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :=
  Work.ThreePoints.even_card_inf_centralizer_of_fixes_three hFT hC hBrSz hS hH hX3 hM hXM

/-- Peterfalvi I Ch. II §4 Prop. 1 (b) for `F = p3F X = O^{2'}(C_G(X))`. -/
theorem p3_prop1b (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hA : Submission.Blueprint.ThmAProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      ((Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X)) :=
  Work.ThreePoints.stronglyEmbedded_p3F_inf_H hFT hC hBrSz hS hH ht htH hX

/-- `p3F X = O^{2'}(C_G(X))` is contained in `N_G(X)`. -/
theorem p3F_le_normalizer (X : Subgroup G) :
    Work.ThreePoints.p3F X ≤ Subgroup.normalizer (X : Set G) :=
  (Work.ThreePoints.p3F_le_centralizer X).trans (Subgroup.centralizer_le_normalizer (X : Set G))

/-! ## Ch. II §4 Prop. 2 (c) -/

/-- Peterfalvi I Ch. II §4 Prop. 2 (c): every non-trivial `x ∈ K = J(D,t)` fixes exactly two
points of `Ω = G ⧸ H`. -/
theorem p3_prop2c (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hA : Submission.Blueprint.ThmAProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {x : G}
    (hx : x ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t) (hx1 : x ≠ 1) :
    (Submission.Blueprint.fixedPts H (Subgroup.zpowers x)).ncard = 2 := by
  classical
  have hxD : x ∈ Submission.Blueprint.twoPoint H t := hx.1
  have hxH : x ∈ H := (Subgroup.mem_inf.mp hxD).1
  have hxHt : x ∈ Submission.Blueprint.conj t H := (Subgroup.mem_inf.mp hxD).2
  have hleH : Subgroup.zpowers x ≤ H := Subgroup.zpowers_le.mpr hxH
  have hmem1 : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈
      Submission.Blueprint.fixedPts H (Subgroup.zpowers x) := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, Work.DoubleTransitivity.conj_one]
    exact hleH
  have hmemt : (QuotientGroup.mk t : G ⧸ H) ∈
      Submission.Blueprint.fixedPts H (Subgroup.zpowers x) := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
    exact Subgroup.zpowers_le.mpr hxHt
  have h1t : (QuotientGroup.mk (1 : G) : G ⧸ H) ≠ (QuotientGroup.mk t : G ⧸ H) := by
    intro hcon
    rw [QuotientGroup.eq] at hcon
    exact htH (by simpa using hcon)
  have hge : 2 ≤ (Submission.Blueprint.fixedPts H (Subgroup.zpowers x)).ncard := by
    have hsub : ({(QuotientGroup.mk (1 : G) : G ⧸ H), (QuotientGroup.mk t : G ⧸ H)} : Set (G ⧸ H))
        ⊆ Submission.Blueprint.fixedPts H (Subgroup.zpowers x) := by
      intro ω hω
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hω
      rcases hω with rfl | rfl
      · exact hmem1
      · exact hmemt
    calc 2 = ({(QuotientGroup.mk (1 : G) : G ⧸ H),
          (QuotientGroup.mk t : G ⧸ H)} : Set (G ⧸ H)).ncard := (Set.ncard_pair h1t).symm
      _ ≤ _ := Set.ncard_le_ncard hsub
  have hle2 : (Submission.Blueprint.fixedPts H (Subgroup.zpowers x)).ncard ≤ 2 := by
    by_contra hcon
    have h3 : 2 < (Submission.Blueprint.fixedPts H (Subgroup.zpowers x)).ncard :=
      lt_of_not_ge hcon
    have hX3 : 3 ≤ (Submission.Blueprint.fixedPts H (Subgroup.zpowers x)).ncard := by omega
    have hev := even_card_centralizer_of_fixes_three hFT hC hA hBrSz hS hH hX3
      ⟨1, by rw [Work.DoubleTransitivity.conj_one]⟩ hleH
    obtain ⟨u, hu, hu2⟩ := exists_orderOf_two_of_even_card hev
    have huH : u ∈ H := hu.1
    have hux : x * u * x⁻¹ = u := by
      have hcomm : x * u = u * x :=
        Subgroup.mem_centralizer_iff.mp hu.2 x (Subgroup.mem_zpowers x)
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hinj := Work.ThreePoints.invertedBy_conj_injective hH ht htH huH hu2
    have h1K : (1 : G) ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t :=
      ⟨Subgroup.one_mem _, by rw [mul_one, inv_one, mul_inv_cancel]⟩
    have heq : x * u * x⁻¹ = 1 * u * 1⁻¹ := by rw [hux]; simp
    exact hx1 (hinj hx h1K heq)
  omega

/-! ## Ch. II §4 Prop. 3 (a), first half: `F₁ = ⟨Inv C_G(X)⟩` is 2-transitive on `Ω_X` -/

theorem p3_twoTransitive (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hA : Submission.Blueprint.ThmAProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    Work.DoubleTransitivity.IsTwoTransitiveOnSub (Work.ThreePoints.p3F1 X)
      (Submission.Blueprint.fixedPts H X) := by
  classical
  obtain ⟨k, hkK, hk1, hkN⟩ := hNX
  have hkD : k ∈ Submission.Blueprint.twoPoint H t := hkK.1
  have hkt : t * k * t⁻¹ = k⁻¹ := hkK.2
  have hoddk : Odd (orderOf k) := by
    have hdvd : orderOf k ∣ Nat.card (Submission.Blueprint.twoPoint H t : Subgroup G) := by
      rw [← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hkD)
    exact Odd.of_dvd_nat (IsStronglyEmbedded.odd_card_inf_conj hH htH) hdvd
  have hk1' : orderOf k ≠ 1 := fun h => hk1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hk1'
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hoddk) (even_iff_two_dvd.mpr hpdvd)
  set e : ℕ := orderOf k / p with he
  have hep : orderOf k = e * p := by rw [he]; exact (Nat.div_mul_cancel hpdvd).symm
  have hepos : 0 < e := by
    rw [he]
    exact Nat.div_pos (Nat.le_of_dvd (orderOf_pos k) hpdvd) hpp.pos
  have hedvd : e ∣ orderOf k := ⟨p, hep⟩
  set k₀ : G := k ^ e with hk0
  have hordk0 : orderOf k₀ = p := by
    rw [hk0, orderOf_pow, Nat.gcd_eq_right hedvd]
    exact Nat.div_eq_of_eq_mul_right hepos hep
  have hk0D : k₀ ∈ Submission.Blueprint.twoPoint H t := by
    rw [hk0]
    exact (Submission.Blueprint.twoPoint H t).pow_mem hkD e
  have hk0inv : t * k₀ * t⁻¹ = k₀⁻¹ := by
    have h1 : MulAut.conj t k = k⁻¹ := by rw [MulAut.conj_apply]; exact hkt
    rw [hk0]
    calc t * k ^ e * t⁻¹ = (MulAut.conj t) (k ^ e) := by rw [MulAut.conj_apply]
      _ = ((MulAut.conj t) k) ^ e := map_pow _ _ _
      _ = (k⁻¹) ^ e := by rw [h1]
      _ = (k ^ e)⁻¹ := inv_pow k e
  have hk0K : k₀ ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t :=
    ⟨hk0D, hk0inv⟩
  have hk0ne : k₀ ≠ 1 := by
    intro h
    have h1 : orderOf k₀ = 1 := by rw [h]; exact orderOf_one
    rw [hordk0] at h1
    exact hpp.ne_one h1
  have hk0N : k₀ ∈ Subgroup.normalizer (X : Set G) := by
    rw [hk0]; exact Subgroup.pow_mem _ hkN e
  have hfix2 : (Submission.Blueprint.fixedPts H (Subgroup.zpowers k₀)).ncard = 2 :=
    p3_prop2c hFT hC hA hBrSz hS hH ht htH hk0K hk0ne
  have hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard :=
    three_le_ncard_fixedPts_of_le_centD hH ht htH hX
  have hXH : X ≤ H := hX.trans (le_trans inf_le_left inf_le_left)
  have hXHt : X ≤ Submission.Blueprint.conj t H := hX.trans (le_trans inf_le_left inf_le_right)
  have hpair : Submission.Blueprint.fixedPts H (Subgroup.zpowers k₀) =
      {(QuotientGroup.mk (1 : G) : G ⧸ H), (QuotientGroup.mk t : G ⧸ H)} := by
    have hsub1 : ({(QuotientGroup.mk (1 : G) : G ⧸ H),
        (QuotientGroup.mk t : G ⧸ H)} : Set (G ⧸ H)) ⊆
        Submission.Blueprint.fixedPts H (Subgroup.zpowers k₀) := by
      intro ω hω
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hω
      rcases hω with rfl | rfl
      · rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, Work.DoubleTransitivity.conj_one]
        exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hk0D).1
      · rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
        exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hk0D).2
    have h1t : (QuotientGroup.mk (1 : G) : G ⧸ H) ≠ (QuotientGroup.mk t : G ⧸ H) := by
      intro hcon
      rw [QuotientGroup.eq] at hcon
      exact htH (by simpa using hcon)
    refine (Set.eq_of_subset_of_ncard_le hsub1 ?_).symm
    rw [hfix2, Set.ncard_pair h1t]
  have hsub : Submission.Blueprint.fixedPts H (Subgroup.zpowers k₀) ⊆
      Submission.Blueprint.fixedPts H X := by
    intro ω hω
    rw [hpair] at hω
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hω
    rcases hω with rfl | rfl
    · rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, Work.DoubleTransitivity.conj_one]
      exact hXH
    · rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
      exact hXHt
  have hfix : ((Submission.Blueprint.fixedPts H (Subgroup.zpowers k₀)) ∩
      (Submission.Blueprint.fixedPts H X)).ncard = 2 := by
    rw [Set.inter_eq_left.mpr hsub]; exact hfix2
  have hP : IsPGroup p (Subgroup.zpowers k₀) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hordk0, pow_one])
  have hPN : Subgroup.zpowers k₀ ≤ Work.ThreePoints.p3F1 X := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem _ (p3_lemma1 hFT hC hA hBrSz hS hH ht htH hX hkK hkN) e
  have hSE : LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      ((Work.ThreePoints.p3F1 X ⊓ H).subgroupOf (Work.ThreePoints.p3F1 X)) := by
    have hmain := stronglyEmbedded_subgroupOf_inf_conj_of_even_card
      (F := Work.ThreePoints.p3F1 X) (g := 1) hH hX3
      (fun u hu => Subgroup.subset_closure hu)
      (by rw [Work.DoubleTransitivity.conj_one]; exact hXH)
      (fun {X'} {M'} h3 hM' hXM' =>
        even_card_centralizer_of_fixes_three hFT hC hA hBrSz hS hH h3 hM' hXM')
    simpa [Work.DoubleTransitivity.conj_one] using hmain
  exact Work.ThreePoints.P3Sub.ch1s4_prop1 hH hBrSz hXH (Work.ThreePoints.p3F1_le_normalizer X)
    (fun u hu => Subgroup.subset_closure hu)
    (fun M hM hXM => even_card_centralizer_of_fixes_three hFT hC hA hBrSz hS hH hX3 hM hXM)
    hSE hpp hp2 hPN hP hfix

/-! ## Ch. II §4 Prop. 3 (a), second half: `N_G(X) = F·N_V(X)` -/

/-- **Ch. II §4 Prop. 3 (a), decomposition form.**  Every element `g ∈ N_G(X)` becomes an element
of the two-point stabiliser `D ⊓ N_G(X)` after right multiplication by a suitable
`y ∈ F₁ = ⟨Inv C_G(X)⟩ ⊆ F = O^{2'}(C_G(X))`.  This is the content of the proof of `p3_a`
(the elementwise half of `N_G(X) = F·N_V(X)`), in the form needed by the final step of Prop. 3 (b):
it provides the product decomposition `N_H(X) = (D ⊓ N_G(X))·S`. -/
theorem p3_a_decomp (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hA : Submission.Blueprint.ThmAProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    ∀ g ∈ Subgroup.normalizer (X : Set G), ∃ y ∈ Work.ThreePoints.p3F X,
      g * y ∈ Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G) := by
  classical
  intro g hg
  have hXH : X ≤ H := hX.trans (le_trans inf_le_left inf_le_left)
  have hXtH : X ≤ Submission.Blueprint.conj t H := hX.trans (le_trans inf_le_left inf_le_right)
  have hcS : ((1 : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H X := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, Work.DoubleTransitivity.conj_one]
    exact hXH
  have hdS : ((t : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H X := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
    exact hXtH
  have hcd : ((1 : G) : G ⧸ H) ≠ ((t : G) : G ⧸ H) := by
    intro hcon
    exact htH (by
      have := QuotientGroup.eq.mp hcon
      simpa using this)
  have hpres : ∀ h ∈ Subgroup.normalizer (X : Set G),
      ∀ ω ∈ Submission.Blueprint.fixedPts H X,
        h • ω ∈ Submission.Blueprint.fixedPts H X := by
    intro h hh ω hω
    rw [mem_fixedPts] at hω ⊢
    intro x hx
    have hxh : h⁻¹ * x * h ∈ X := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) x).mp hx
    calc x • (h • ω) = (x * h) • ω := by rw [mul_smul]
      _ = (h * (h⁻¹ * x * h)) • ω := by rw [show x * h = h * (h⁻¹ * x * h) from by group]
      _ = h • ((h⁻¹ * x * h) • ω) := by rw [mul_smul]
      _ = h • ω := by rw [hω _ hxh]
  have h2t := p3_twoTransitive hFT hC hA hBrSz hS hH ht htH hX0 hX hNX
  have hg'inv : g⁻¹ ∈ Subgroup.normalizer (X : Set G) := Subgroup.inv_mem _ hg
  have hcd' : g⁻¹ • ((1 : G) : G ⧸ H) ≠ g⁻¹ • ((t : G) : G ⧸ H) := fun hcon => hcd (by
    have := congrArg (fun p : G ⧸ H => g • p) hcon
    simpa only [← mul_smul, mul_inv_cancel, one_smul] using this)
  obtain ⟨y, hyF1, hyc, hyd⟩ :=
    h2t ((1 : G) : G ⧸ H) hcS ((t : G) : G ⧸ H) hdS hcd
      (g⁻¹ • ((1 : G) : G ⧸ H)) (hpres g⁻¹ hg'inv _ hcS)
      (g⁻¹ • ((t : G) : G ⧸ H)) (hpres g⁻¹ hg'inv _ hdS) hcd'
  have hgyc : (g * y) • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
    rw [mul_smul, hyc, ← mul_smul, mul_inv_cancel, one_smul]
  have hgyd : (g * y) • ((t : G) : G ⧸ H) = ((t : G) : G ⧸ H) := by
    rw [mul_smul, hyd, ← mul_smul, mul_inv_cancel, one_smul]
  have hgyD : g * y ∈ Submission.Blueprint.twoPoint H t := by
    rw [Work.ThreePoints.twoPoint_eq, Subgroup.mem_inf]
    constructor
    · have h1 : g * y ∈ MulAction.stabilizer G ((1 : G) : G ⧸ H) := by
        rw [MulAction.mem_stabilizer_iff]; exact hgyc
      rwa [stabilizer_mk, Work.DoubleTransitivity.conj_one] at h1
    · have h1 : g * y ∈ MulAction.stabilizer G ((t : G) : G ⧸ H) := by
        rw [MulAction.mem_stabilizer_iff]; exact hgyd
      rwa [stabilizer_mk] at h1
  have hyN : y ∈ Subgroup.normalizer (X : Set G) := Work.ThreePoints.p3F1_le_normalizer X hyF1
  have hgyN : g * y ∈ Subgroup.normalizer (X : Set G) := Subgroup.mul_mem _ hg hyN
  exact ⟨y, Work.ThreePoints.p3F1_le_p3F X hyF1, hgyD, hgyN⟩

/-- **Ch. II §4 Prop. 3 (a), second half**: `N_G(X) = F·N_V(X)` where `F = O^{2'}(C_G(X))` and
`V = C_D(t)`.  Immediate from the decomposition `p3_a_decomp`. -/
theorem p3_a (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hA : Submission.Blueprint.ThmAProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    Subgroup.normalizer (X : Set G) = Work.ThreePoints.p3F X ⊔
      (Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G)) := by
  refine le_antisymm ?_ (sup_le (p3F_le_normalizer X) inf_le_right)
  intro g hg
  obtain ⟨y, hyF, hgyD, hgyN⟩ :=
    p3_a_decomp hFT hC hA hBrSz hS hH ht htH hX0 hX hNX g hg
  have hgyV : g * y ∈ Work.ThreePoints.p3F X ⊔
      (Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G)) :=
    (sup_le_sup (Work.ThreePoints.p3F1_le_p3F X) le_rfl)
      (p3_appI_one hFT hC hA hBrSz hS hH ht htH hX ⟨hgyD, hgyN⟩)
  have hyinv : y⁻¹ ∈ Work.ThreePoints.p3F X := Subgroup.inv_mem _ hyF
  have hg_eq : g = (g * y) * y⁻¹ := by group
  rw [hg_eq]
  exact Subgroup.mul_mem _ hgyV (Subgroup.mem_sup_left hyinv)

/-! ## `t ∈ p3F X` and `HasFourGroup (p3F X)` -/

/-- `t ∈ p3F X` for `X ≤ centD H t`: `t` is an involution of `C_G(X)`, and the involution of a
finite group lies in its `O^{2'}`. -/
theorem t_mem_p3F {H : Subgroup G} {t : G} (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X ≤ Submission.Blueprint.centD H t) : t ∈ Work.ThreePoints.p3F X := by
  have htC : t ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (mem_centD.mp (hX hx)).2.2
  rw [Work.ThreePoints.mem_p3F]
  refine ⟨⟨t, htC⟩, ?_, rfl⟩
  refine involution_mem_oddResidual (x := (⟨t, htC⟩ : ↥(Subgroup.centralizer (X : Set G)))) ?_
  exact Subtype.ext (mul_self_eq_one_of_orderOf_eq_two ht)

/-- **Peterfalvi I Ch. II §4 Prop. 3 (c), first half**: `F = p3F X = O^{2'}(C_G(X))` has
`2`-rank `≥ 2` (`HasFourGroup`) when `X ≠ ⊥`, `X ≤ V = centD H t` and `N_K(X) ≠ 1`. -/
theorem hasFourGroup_p3F (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hA : Submission.Blueprint.ThmAProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    Submission.Blueprint.HasFourGroup ↥(Work.ThreePoints.p3F X) := by
  classical
  by_contra h4
  have hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard :=
    three_le_ncard_fixedPts_of_le_centD hH ht htH hX
  have hXH : X ≤ H := hX.trans (le_trans inf_le_left inf_le_left)
  have hXtH : X ≤ Submission.Blueprint.conj t H := hX.trans (le_trans inf_le_left inf_le_right)
  have hFN : Work.ThreePoints.p3F X ≤ Subgroup.normalizer (X : Set G) := p3F_le_normalizer X
  have h2t1 := p3_twoTransitive hFT hC hA hBrSz hS hH ht htH hX0 hX hNX
  have h2t : Work.DoubleTransitivity.IsTwoTransitiveOnSub (Work.ThreePoints.p3F X)
      (Submission.Blueprint.fixedPts H X) := by
    intro a ha b hb hab c hc d hd hcd
    obtain ⟨y, hy, hy1, hy2⟩ := h2t1 a ha b hb hab c hc d hd hcd
    exact ⟨y, Work.ThreePoints.p3F1_le_p3F X hy, hy1, hy2⟩
  have hFSE : LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      ((Work.ThreePoints.p3F X ⊓ H).subgroupOf (Work.ThreePoints.p3F X)) :=
    p3_prop1b hFT hC hA hBrSz hS hH ht htH hX0 hX
  have hmax : ∀ M : Subgroup G, Work.ThreePoints.p3F X ⊓ H ≤ M →
      M ≤ Work.ThreePoints.p3F X →
      M = Work.ThreePoints.p3F X ⊓ H ∨ M = Work.ThreePoints.p3F X :=
    fun M hHM hMF => maximal_of_twoTransitive hXH hFN hX3 h2t hHM hMF
  have htF : t ∈ Work.ThreePoints.p3F X := t_mem_p3F ht hX
  obtain ⟨ω, hωfix, -⟩ := existsUnique_fixedPts_of_orderOf_eq_two hH ht
  have happ := app3_1 hFT hBrSz hH hFN h2t hFSE hmax h4 ht htF htH hωfix
  obtain ⟨k, hkK, hk1, hkN⟩ := hNX
  have hkF : k ∈ Work.ThreePoints.p3F X :=
    Work.ThreePoints.p3F1_le_p3F X (p3_lemma1 hFT hC hA hBrSz hS hH ht htH hX hkK hkN)
  have hkD : k ∈ Submission.Blueprint.twoPoint H t := hkK.1
  have hkω : k • ω = ω := happ ⟨hkF, hkD⟩
  have hleH : Subgroup.zpowers k ≤ H := Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hkD).1
  have hleHt : Subgroup.zpowers k ≤ Submission.Blueprint.conj t H :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hkD).2
  have hleS : Subgroup.zpowers k ≤ MulAction.stabilizer G ω :=
    Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hkω)
  have hm1 : ((1 : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers k) := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, Work.DoubleTransitivity.conj_one]
    exact hleH
  have hmt : ((t : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers k) := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
    exact hleHt
  have hmω : ω ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers k) := by
    rw [mem_fixedPts_iff_le_stabilizer]
    exact hleS
  have h1t : ((1 : G) : G ⧸ H) ≠ ((t : G) : G ⧸ H) := by
    intro hcon
    rw [QuotientGroup.eq] at hcon
    exact htH (by simpa using hcon)
  have hω1 : ω ≠ ((1 : G) : G ⧸ H) := by
    intro hcon
    have hthis : t • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by rw [← hcon]; exact hωfix
    have h1 := (Work.DoubleTransitivity.smul_mk_eq_mk_iff (g := t) (x := 1) (H := H)).mp hthis
    rw [Work.DoubleTransitivity.conj_one] at h1
    exact htH h1
  have hωt : ω ≠ ((t : G) : G ⧸ H) := by
    intro hcon
    have hthis : t • ((t : G) : G ⧸ H) = ((t : G) : G ⧸ H) := by rw [← hcon]; exact hωfix
    have h1 := (Work.DoubleTransitivity.smul_mk_eq_mk_iff (g := t) (x := t) (H := H)).mp hthis
    rw [Work.ThreePoints.mem_conj_iff] at h1
    exact htH (by simpa using h1)
  have h3 : 3 ≤ (Submission.Blueprint.fixedPts H (Subgroup.zpowers k)).ncard := by
    have hsub : ({((1 : G) : G ⧸ H), ((t : G) : G ⧸ H), ω} : Set (G ⧸ H)) ⊆
        Submission.Blueprint.fixedPts H (Subgroup.zpowers k) := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact hm1
      · exact hmt
      · exact hmω
    have hcard : ({((1 : G) : G ⧸ H), ((t : G) : G ⧸ H), ω} : Set (G ⧸ H)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
            exact ⟨h1t, fun h => hω1 h.symm⟩),
        Set.ncard_insert_of_notMem (by simp only [Set.mem_singleton_iff]; exact fun h => hωt h.symm),
        Set.ncard_singleton]
    calc 3 = _ := hcard.symm
      _ ≤ _ := Set.ncard_le_ncard hsub
  have h2 := p3_prop2c hFT hC hA hBrSz hS hH ht htH hkK hk1
  omega

/-! ## `N_G(X) = F₁·N_D(X)` and `F₁ = F` -/

/-- Ch. II §4 Prop. 3 (a) with `F₁ = ⟨Inv C_G(X)⟩`: `N_G(X) = F₁·N_D(X)`. -/
theorem p3_a_F1 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hA : Submission.Blueprint.ThmAProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    Subgroup.normalizer (X : Set G) = Work.ThreePoints.p3F1 X ⊔
      (Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G)) := by
  classical
  refine le_antisymm ?_ (sup_le (Work.ThreePoints.p3F1_le_normalizer X) inf_le_right)
  intro g hg
  have hXH : X ≤ H := hX.trans (le_trans inf_le_left inf_le_left)
  have hXtH : X ≤ Submission.Blueprint.conj t H := hX.trans (le_trans inf_le_left inf_le_right)
  have hcS : ((1 : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H X := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, Work.DoubleTransitivity.conj_one]
    exact hXH
  have hdS : ((t : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H X := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
    exact hXtH
  have hcd : ((1 : G) : G ⧸ H) ≠ ((t : G) : G ⧸ H) := by
    intro hcon
    exact htH (by
      have := QuotientGroup.eq.mp hcon
      simpa using this)
  have hpres : ∀ h ∈ Subgroup.normalizer (X : Set G),
      ∀ ω ∈ Submission.Blueprint.fixedPts H X,
        h • ω ∈ Submission.Blueprint.fixedPts H X := by
    intro h hh ω hω
    rw [mem_fixedPts] at hω ⊢
    intro x hx
    have hxh : h⁻¹ * x * h ∈ X := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) x).mp hx
    calc x • (h • ω) = (x * h) • ω := by rw [mul_smul]
      _ = (h * (h⁻¹ * x * h)) • ω := by rw [show x * h = h * (h⁻¹ * x * h) from by group]
      _ = h • ((h⁻¹ * x * h) • ω) := by rw [mul_smul]
      _ = h • ω := by rw [hω _ hxh]
  have h2t := p3_twoTransitive hFT hC hA hBrSz hS hH ht htH hX0 hX hNX
  have hg'inv : g⁻¹ ∈ Subgroup.normalizer (X : Set G) := Subgroup.inv_mem _ hg
  have hcd' : g⁻¹ • ((1 : G) : G ⧸ H) ≠ g⁻¹ • ((t : G) : G ⧸ H) := fun hcon => hcd (by
    have := congrArg (fun p : G ⧸ H => g • p) hcon
    simpa only [← mul_smul, mul_inv_cancel, one_smul] using this)
  obtain ⟨y, hyF1, hyc, hyd⟩ :=
    h2t ((1 : G) : G ⧸ H) hcS ((t : G) : G ⧸ H) hdS hcd
      (g⁻¹ • ((1 : G) : G ⧸ H)) (hpres g⁻¹ hg'inv _ hcS)
      (g⁻¹ • ((t : G) : G ⧸ H)) (hpres g⁻¹ hg'inv _ hdS) hcd'
  have hgyc : (g * y) • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
    rw [mul_smul, hyc, ← mul_smul, mul_inv_cancel, one_smul]
  have hgyd : (g * y) • ((t : G) : G ⧸ H) = ((t : G) : G ⧸ H) := by
    rw [mul_smul, hyd, ← mul_smul, mul_inv_cancel, one_smul]
  have hgyD : g * y ∈ Submission.Blueprint.twoPoint H t := by
    rw [Work.ThreePoints.twoPoint_eq, Subgroup.mem_inf]
    constructor
    · have h1 : g * y ∈ MulAction.stabilizer G ((1 : G) : G ⧸ H) := by
        rw [MulAction.mem_stabilizer_iff]; exact hgyc
      rwa [stabilizer_mk, Work.DoubleTransitivity.conj_one] at h1
    · have h1 : g * y ∈ MulAction.stabilizer G ((t : G) : G ⧸ H) := by
        rw [MulAction.mem_stabilizer_iff]; exact hgyd
      rwa [stabilizer_mk] at h1
  have hyN : y ∈ Subgroup.normalizer (X : Set G) := Work.ThreePoints.p3F1_le_normalizer X hyF1
  have hgyN : g * y ∈ Subgroup.normalizer (X : Set G) := Subgroup.mul_mem _ hg hyN
  have hgyV : g * y ∈ Work.ThreePoints.p3F1 X ⊔
      (Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G)) :=
    p3_appI_one hFT hC hA hBrSz hS hH ht htH hX ⟨hgyD, hgyN⟩
  have hyinv : y⁻¹ ∈ Work.ThreePoints.p3F1 X := Subgroup.inv_mem _ hyF1
  have hg_eq : g = (g * y) * y⁻¹ := by group
  rw [hg_eq]
  exact Subgroup.mul_mem _ hgyV (Subgroup.mem_sup_left hyinv)

/-- `F₁ = ⟨Inv C_G(X)⟩` is normal in `N_G(X)`: conjugation by an element of `N_G(X)` preserves
`C_G(X)`, hence permutes its involutions. -/
theorem normalizer_le_normalizer_p3F1 (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (Work.ThreePoints.p3F1 X : Set G) := by
  rw [Work.ThreePoints.p3F1, Subgroup.le_normalizer_closure_iff]
  intro h hh g hg
  refine Subgroup.subset_closure ⟨Work.ThreePoints.p3F_conj_mem_centralizer hh hg.1, ?_⟩
  have h1 : h * g * h⁻¹ = (MulAut.conj h) g := MulAut.conj_apply h g
  rw [h1, (MulAut.conj h).orderOf_eq g, hg.2]

/-- Ch. II §4 Prop. 3 (a), first half (conclusion): `F = O^{2'}(C_G(X))` equals
`F₁ = ⟨Inv C_G(X)⟩`.  From `N_G(X) = F₁·N_D(X)`, `F₁` is normal in `C_G(X)` with odd index, so
minimality of `O^{2'}` gives `F ≤ F₁`; the converse is `p3F1_le_p3F`. -/
theorem p3F1_eq_p3F (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hA : Submission.Blueprint.ThmAProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    Work.ThreePoints.p3F1 X = Work.ThreePoints.p3F X := by
  classical
  refine le_antisymm (Work.ThreePoints.p3F1_le_p3F X) ?_
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hNdef
  set A : Subgroup ↥N := (Work.ThreePoints.p3F1 X).subgroupOf N with hAdef
  set B : Subgroup ↥N := (Submission.Blueprint.centD H t ⊓ N).subgroupOf N with hBdef
  have hAN : Work.ThreePoints.p3F1 X ≤ N := Work.ThreePoints.p3F1_le_normalizer X
  have hA_normal : A.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAN).mpr (normalizer_le_normalizer_p3F1 X)
  have hsup : A ⊔ B = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, hAdef, hBdef, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, Subgroup.map_top]
    rw [inf_eq_left.mpr hAN, inf_eq_left.mpr inf_le_right, Subgroup.range_subtype]
    exact (p3_a_F1 hFT hC hA hBrSz hS hH ht htH hX0 hX hNX).symm
  have hB_odd : Odd (Nat.card ↥B) := by
    have hmap : Nat.card ↥B = Nat.card ↥(B.map N.subtype) :=
      (Subgroup.card_map_of_injective (f := N.subtype) Subtype.coe_injective).symm
    rw [hmap, hBdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
    have hle : Submission.Blueprint.centD H t ⊓ N ≤ Submission.Blueprint.twoPoint H t :=
      le_trans (inf_le_left : Submission.Blueprint.centD H t ⊓ N ≤
        Submission.Blueprint.centD H t) (inf_le_left : Submission.Blueprint.centD H t ≤
        Submission.Blueprint.twoPoint H t)
    exact Odd.of_dvd_nat (IsStronglyEmbedded.odd_card_inf_conj hH htH)
      (Subgroup.card_dvd_of_le hle)
  have hArelB : A.index = A.relIndex B := by
    rw [← Subgroup.relIndex_top_right A, ← hsup, Subgroup.relIndex_sup_left]
  have hoddA : Odd ((Work.ThreePoints.p3F1 X).relIndex N) := by
    have h1 : (Work.ThreePoints.p3F1 X).relIndex N = A.relIndex B := hArelB
    rw [h1]
    exact Odd.of_dvd_nat hB_odd (show A.relIndex B ∣ Nat.card ↥B from
      Subgroup.index_dvd_card (A.subgroupOf B))
  have hAC : Work.ThreePoints.p3F1 X ≤ Subgroup.centralizer (X : Set G) :=
    Work.ThreePoints.p3F1_le_centralizer X
  have hACN : Subgroup.centralizer (X : Set G) ≤ N := Subgroup.centralizer_le_normalizer (X : Set G)
  have hoddC : Odd ((Work.ThreePoints.p3F1 X).relIndex (Subgroup.centralizer (X : Set G))) := by
    have hmul := Subgroup.relIndex_mul_relIndex (H := Work.ThreePoints.p3F1 X)
      (K := Subgroup.centralizer (X : Set G)) (L := N) hAC hACN
    exact Odd.of_dvd_nat hoddA ⟨(Subgroup.centralizer (X : Set G)).relIndex N, hmul.symm⟩
  have hnormC : ((Work.ThreePoints.p3F1 X).subgroupOf
      (Subgroup.centralizer (X : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAC).mpr
      (hACN.trans (normalizer_le_normalizer_p3F1 X))
  have hle : Submission.Blueprint.oddResidual ↥(Subgroup.centralizer (X : Set G))
      ≤ (Work.ThreePoints.p3F1 X).subgroupOf (Subgroup.centralizer (X : Set G)) :=
    (oddResidual_basic (G := ↥(Subgroup.centralizer (X : Set G)))).2.2.1
      _ hnormC hoddC
  intro x hx
  have hx'' : x ∈ (Submission.Blueprint.oddResidual ↥(Subgroup.centralizer (X : Set G))).map
      (Subgroup.centralizer (X : Set G)).subtype := hx
  obtain ⟨c, hc, rfl⟩ := hx''
  exact Subgroup.mem_subgroupOf.mp (hle hc)

/-! ## `F` acts 2-transitively on `Ω_X`; `Z(F) ≤ O_{2'}(F)` -/

/-- `F = p3F X` acts `2`-transitively on `Ω_X` (from `F₁ = ⟨Inv C_G(X)⟩ ≤ F`). -/
theorem p3_twoTransitive_F (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hA : Submission.Blueprint.ThmAProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    Work.DoubleTransitivity.IsTwoTransitiveOnSub (Work.ThreePoints.p3F X)
      (Submission.Blueprint.fixedPts H X) := by
  intro a ha b hb hab c hc d hd hcd
  obtain ⟨y, hy, hy1, hy2⟩ :=
    p3_twoTransitive hFT hC hA hBrSz hS hH ht htH hX0 hX hNX a ha b hb hab c hc d hd hcd
  exact ⟨y, Work.ThreePoints.p3F1_le_p3F X hy, hy1, hy2⟩

/-- `Z(F) ≤ O_{2'}(F)`: a central involution `z` of `F` would satisfy `F ≤ C_G(z) ≤ H(z)`, so
that `F` would fix a point of `Ω_X`, contradicting the transitivity of `F` there; hence `Z(F)`
has odd order. -/
theorem orderOf_coe_coe {K : Subgroup G} {L : Subgroup ↥K} (a : ↥L) :
    orderOf ((a : ↥K) : G) = orderOf a := by
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]

theorem center_le_oddCore_p3F (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hA : Submission.Blueprint.ThmAProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    Subgroup.center ↥(Work.ThreePoints.p3F X) ≤
      Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X) := by
  classical
  refine le_sSup ⟨inferInstance, ?_⟩
  rw [← Nat.not_even_iff_odd]
  intro hev
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
  have hz2 : orderOf (((x : ↥(Subgroup.center ↥(Work.ThreePoints.p3F X))) :
      ↥(Work.ThreePoints.p3F X)) : G) = 2 := (orderOf_coe_coe x).trans hx2
  have hzmem : (((x : ↥(Subgroup.center ↥(Work.ThreePoints.p3F X))) :
      ↥(Work.ThreePoints.p3F X)) : G) ∈ Work.ThreePoints.p3F X :=
    ((x : ↥(Subgroup.center ↥(Work.ThreePoints.p3F X))) : ↥(Work.ThreePoints.p3F X)).2
  have hxcent : ∀ g : ↥(Work.ThreePoints.p3F X),
      g * ((x : ↥(Subgroup.center ↥(Work.ThreePoints.p3F X))) : ↥(Work.ThreePoints.p3F X)) =
      ((x : ↥(Subgroup.center ↥(Work.ThreePoints.p3F X))) : ↥(Work.ThreePoints.p3F X)) * g :=
    fun g => Subgroup.mem_center_iff.mp x.2 g
  obtain ⟨y, hy⟩ := Work.ThreePoints.exists_conj_mem hH hz2
  have hH' : LeanEval.GroupTheory.Defs.IsStronglyEmbedded (Submission.Blueprint.conj y H) :=
    conj_stronglyEmbedded hH y
  have hcent_le : Subgroup.centralizer
      (singleton ((((x : ↥(Subgroup.center ↥(Work.ThreePoints.p3F X))) :
        ↥(Work.ThreePoints.p3F X)) : G)) : Set G) ≤ Submission.Blueprint.conj y H :=
    IsStronglyEmbedded.centralizer_le hH' hy (by simp [hz2])
  have hFX : X ≤ Submission.Blueprint.conj y H := by
    intro a ha
    apply hcent_le
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (Work.ThreePoints.p3F_le_centralizer X hzmem) a ha
  have hFle_stab : Work.ThreePoints.p3F X ≤ MulAction.stabilizer G ((y : G) : G ⧸ H) := by
    intro f hf
    rw [stabilizer_mk]
    apply hcent_le
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg (fun u : ↥(Work.ThreePoints.p3F X) => (u : G)) (hxcent ⟨f, hf⟩)
  have hfix : ((y : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H X := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
    exact hFX
  have hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard :=
    three_le_ncard_fixedPts_of_le_centD hH ht htH hX
  obtain ⟨c, hc, hcne⟩ := Set.exists_ne_of_one_lt_ncard
    (by omega : 1 < (Submission.Blueprint.fixedPts H X).ncard) ((y : G) : G ⧸ H)
  obtain ⟨f, hfF, hfc⟩ := (p3_twoTransitive_F hFT hC hA hBrSz hS hH ht htH hX0 hX hNX).isTransitiveOnSub
    ((y : G) : G ⧸ H) hfix c hc
  have h1 : f • ((y : G) : G ⧸ H) = ((y : G) : G ⧸ H) := hFle_stab hfF
  exact hcne (hfc.symm.trans h1)

/-! ## `O_{2'}(F) ≤ Z(F)` -/

/-- `O_{2'}(F) ≤ Z(F)`: `F = F₁ = ⟨Inv C_G(X)⟩`, and every involution `u` of `C_G(X)` centralises
`O_{2'}(F)` by Theorem C (`hC`), applied inside the strongly embedded subgroup `H(u)`.
(From `p3F1_eq_p3F`: `F = ⟨Inv C_G(X)⟩`.) -/
theorem oddCore_le_center_p3F (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hA : Submission.Blueprint.ThmAProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X) ≤
      Subgroup.center ↥(Work.ThreePoints.p3F X) := by
  classical
  set F : Subgroup G := Work.ThreePoints.p3F X with hFdef
  set Z : Subgroup G := (Submission.Blueprint.oddCore ↥F).map F.subtype with hZdef
  have hZH : Z ≤ H := by
    have h4 : Submission.Blueprint.HasFourGroup ↥F := hasFourGroup_p3F hFT hC hA hBrSz hS hH ht htH hX0 hX hNX
    have hFSE : LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((F ⊓ H).subgroupOf F) :=
      p3_prop1b hFT hC hA hBrSz hS hH ht htH hX0 hX
    have h1 := Work.ThreePoints.oddCore_le_of_stronglyEmbedded (G := ↥F) hFSE h4
    calc Z = (Submission.Blueprint.oddCore ↥F).map F.subtype := rfl
      _ ≤ ((F ⊓ H).subgroupOf F).map F.subtype := Subgroup.map_mono h1
      _ = (F ⊓ H) ⊓ F := Subgroup.subgroupOf_map_subtype (F ⊓ H) F
      _ = F ⊓ H := inf_eq_left.mpr inf_le_left
      _ ≤ H := inf_le_right
  have hZnorm : ∀ m ∈ F, Z.map (MulAut.conj m).toMonoidHom = Z := by
    have hle : F ≤ Subgroup.normalizer (Z : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro h hh k hk
      obtain ⟨g, -, rfl⟩ : ∃ g : ↥F, (g : G) = h := ⟨⟨h, hh⟩, rfl⟩
      obtain ⟨z, hz, hzk⟩ := Subgroup.mem_map.mp hk
      rw [← hzk]
      exact Subgroup.mem_map.mpr ⟨g * z * g⁻¹,
        (inferInstance : (Submission.Blueprint.oddCore ↥F).Normal).conj_mem z hz g, rfl⟩
    intro m hm
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hle hm)
  have hZm : ∀ m ∈ F, Z ≤ Submission.Blueprint.conj m H := by
    intro m hm
    calc Z = Z.map (MulAut.conj m).toMonoidHom := (hZnorm m hm).symm
      _ ≤ H.map (MulAut.conj m).toMonoidHom := Subgroup.map_mono hZH
  have h2t := p3_twoTransitive_F hFT hC hA hBrSz hS hH ht htH hX0 hX hNX
  have hXH : X ≤ H := hX.trans (le_trans inf_le_left inf_le_left)
  have hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard :=
    three_le_ncard_fixedPts_of_le_centD hH ht htH hX
  -- the key: every involution of `C_G(X)` centralises `Z`
  have hgen : ∀ u ∈ Submission.Blueprint.involutions (Subgroup.centralizer (X : Set G) : Set G),
      ∀ z ∈ Z, u * z = z * u := by
    intro u hu z hz
    have huF : u ∈ F :=
      Work.ThreePoints.mem_p3F_of_involution hu.1 hu.2
    -- the unique fixed point of `u` lies in `Ω_X`
    obtain ⟨ω, hωfix, hωuniq⟩ := existsUnique_fixedPts_of_orderOf_eq_two hH hu.2
    have hωX : ω ∈ Submission.Blueprint.fixedPts H X := by
      rw [mem_fixedPts]
      intro x hx
      have hxu : x * u = u * x := Subgroup.mem_centralizer_iff.mp hu.1 x hx
      have hfix : u • (x • ω) = x • ω := by
        rw [← mul_smul, hxu.symm, mul_smul, hωfix]
      exact hωuniq (x • ω) hfix
    -- `f ∈ F` with `f • pt H = ω`, so that `H(u) = conj f H` is an `F`-conjugate
    have hpt : Work.DoubleTransitivity.pt H ∈ Submission.Blueprint.fixedPts H X := by
      rw [mem_fixedPts_iff_le_stabilizer, Work.ThreePoints.stabilizer_mk,
        Work.DoubleTransitivity.conj_one]
      exact hXH
    obtain ⟨f, hfF, hfω⟩ := h2t.isTransitiveOnSub (Work.DoubleTransitivity.pt H) hpt ω hωX
    have hstab : MulAction.stabilizer G ω = Submission.Blueprint.conj f H := by
      rw [← hfω, Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj,
        Work.ThreePoints.stabilizer_mk, Work.DoubleTransitivity.conj_one]
    have hH' : LeanEval.GroupTheory.Defs.IsStronglyEmbedded (Submission.Blueprint.conj f H) :=
      conj_stronglyEmbedded hH f
    have huH' : u ∈ Submission.Blueprint.conj f H := by
      rw [← hstab]
      exact MulAction.mem_stabilizer_iff.mpr hωfix
    -- choose `g ∈ F` with `g ∉ H'`
    obtain ⟨g, hgF, hgnot⟩ : ∃ g ∈ F, g ∉ Submission.Blueprint.conj f H := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨c, hc, hcne⟩ := Set.exists_ne_of_one_lt_ncard
        (by omega : 1 < (Submission.Blueprint.fixedPts H X).ncard) ω
      obtain ⟨g', hg'F, hg'c⟩ := h2t.isTransitiveOnSub ω hωX c hc
      have h1 : g' ∈ MulAction.stabilizer G ω := by rw [hstab]; exact hcon g' hg'F
      exact hcne (hg'c ▸ (MulAction.mem_stabilizer_iff.mp h1))
    -- `Z ≤ H'` and `Z ≤ conj g H'`
    have hZH' : Z ≤ Submission.Blueprint.conj f H := hZm f hfF
    have hZH'g : Z ≤ Submission.Blueprint.conj g (Submission.Blueprint.conj f H) := by
      rw [← Work.DoubleTransitivity.conj_mul]
      exact hZm (g * f) (F.mul_mem hgF hfF)
    have hZu : u ∈ Subgroup.normalizer (Z : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hZnorm u huF
    -- Theorem C
    exact hC G hS (Submission.Blueprint.conj f H) hH' g hgnot u ⟨huH', hu.2⟩ Z
      (le_inf hZH' hZH'g) hZu z hz
  -- conclude: `F = ⟨Inv C_G(X)⟩` commutes with `Z`, so `O_{2'}(F) ≤ Z(F)`
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hle : Work.ThreePoints.p3F1 X ≤ Subgroup.centralizer ({(z : G)} : Set G) := by
    rw [Work.ThreePoints.p3F1, Subgroup.closure_le]
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (hgen u hu (z : G) (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩))
  have hg : (g : G) ∈ Subgroup.centralizer ({(z : G)} : Set G) :=
    hle (by
      rw [p3F1_eq_p3F hFT hC hA hBrSz hS hH ht htH hX0 hX hNX]
      exact g.2)
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hg)

/-! ## `O_{2'}(F) = Z(F)`, `|F| < |G|`, and `F/Z(F)` is a simple Bender group -/

/-- **Peterfalvi I Ch. II §4 Prop. 3 (c), the centre**: `O_{2'}(F) = Z(F)`. -/
theorem oddCore_p3F_eq_center (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hA : Submission.Blueprint.ThmAProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X) =
      Subgroup.center ↥(Work.ThreePoints.p3F X) :=
  le_antisymm (oddCore_le_center_p3F hFT hC hA hBrSz hS hH ht htH hX0 hX hNX)
    (center_le_oddCore_p3F hFT hC hA hBrSz hS hH ht htH hX0 hX hNX)

/-- `O^{2'}` is invariant under group isomorphisms. -/
theorem oddResidual_map_mulEquiv {H H' : Type} [Group H] [Finite H] [Group H'] [Finite H']
    (e : H ≃* H') :
    (Submission.Blueprint.oddResidual H).map e.toMonoidHom = Submission.Blueprint.oddResidual H' := by
  have hmapodd : Odd ((Submission.Blueprint.oddResidual H).map e.toMonoidHom).index := by
    rw [show (Submission.Blueprint.oddResidual H).map e.toMonoidHom =
        (Submission.Blueprint.oddResidual H).comap e.symm.toMonoidHom from
      Subgroup.map_equiv_eq_comap_symm e _, Subgroup.index_comap_of_surjective _ e.symm.surjective]
    exact (oddResidual_basic (G := H)).2.1
  have hmapnorm : ((Submission.Blueprint.oddResidual H).map e.toMonoidHom).Normal :=
    (oddResidual_basic (G := H)).1.map e.toMonoidHom e.surjective
  refine le_antisymm ?_ ((oddResidual_basic (G := H')).2.2.1 _ hmapnorm hmapodd)
  rw [Subgroup.map_le_iff_le_comap]
  refine (oddResidual_basic (G := H)).2.2.1 _ ?_ ?_
  · exact (oddResidual_basic (G := H')).1.comap e.toMonoidHom
  · rw [Subgroup.index_comap_of_surjective _ e.surjective]
    exact (oddResidual_basic (G := H')).2.1

/-- `|F| < |G|` for `F = p3F X`, `X ≠ ⊥`, `X ≤ C_D(t)`: `F ≤ C_G(X) < G`. -/
theorem card_p3F_lt (hFT : Submission.Blueprint.FeitThompsonProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (htH : t ∉ H)
    {X : Subgroup G} (hX0 : X ≠ ⊥) (hX : X ≤ Submission.Blueprint.centD H t) :
    Nat.card ↥(Work.ThreePoints.p3F X) < Nat.card G := by
  have hCne : Subgroup.centralizer (X : Set G) ≠ ⊤ := by
    intro hCt
    apply hX0
    have hXn : X.Normal := ⟨fun x hx g => by
      have hg : g ∈ Subgroup.centralizer (X : Set G) := hCt ▸ Subgroup.mem_top g
      have hc : x * g = g * x := Subgroup.mem_centralizer_iff.mp hg x hx
      rw [← hc, mul_inv_cancel_right]; exact hx⟩
    have hXD : X ≤ Submission.Blueprint.twoPoint H t := hX.trans inf_le_left
    have hDodd : Odd (Nat.card (Submission.Blueprint.twoPoint H t)) :=
      IsStronglyEmbedded.odd_card_inf_conj hH htH
    have hXodd : Odd (Nat.card X) :=
      Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le hXD)
    have hXO : X ≤ Submission.Blueprint.oddCore G :=
      Work.BrauerSuzuki.OddCore.le_of_normal_odd hXn hXodd
    rw [hS.2.2] at hXO
    exact le_bot_iff.mp hXO
  calc Nat.card ↥(Work.ThreePoints.p3F X)
      ≤ Nat.card ↥(Subgroup.centralizer (X : Set G)) :=
        Subgroup.card_le_of_le (Work.ThreePoints.p3F_le_centralizer X)
    _ < Nat.card G := by
        have h := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hCne)
        simpa [Subgroup.card_top] using h

/-! ## `F/Z(F)` is a simple Bender group -/

/-- **Peterfalvi I Ch. II §4 Prop. 3 (c)**: `F/O_{2'}(F) = F/Z(F)` is isomorphic to one of
`PSL(2,q)`, `Sz(q)`, `PSU(3,q)` (`IsSimpleBenderGroup`), obtained by applying `(B1)` to `F`. -/
theorem p3F_quotient_model (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hA : Submission.Blueprint.ThmAProp)
    (hZJ : Submission.Blueprint.GlaubermanZJProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hMod : Submission.Blueprint.ModelFactsProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (φ : ↥(Work.ThreePoints.p3F X) →* Y),
      Function.Surjective φ ∧ φ.ker = Subgroup.center ↥(Work.ThreePoints.p3F X) ∧
        LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y := by
  classical
  set F : Subgroup G := Work.ThreePoints.p3F X with hFdef
  haveI : Finite ↥F := Subtype.finite
  have hlt : Nat.card ↥F < Nat.card G := by
    rw [hFdef]; exact card_p3F_lt hFT hS hH htH hX0 hX
  have h4 : Submission.Blueprint.HasFourGroup ↥F :=
    hasFourGroup_p3F hFT hC hA hBrSz hS hH ht htH hX0 hX hNX
  have hSE : LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((F ⊓ H).subgroupOf F) := by
    rw [hFdef]; exact p3_prop1b hFT hC hA hBrSz hS hH ht htH hX0 hX
  obtain ⟨L, hLnorm, -, hLodd, Y, hYG, φ, hφsurj, hφker, hBender⟩ :=
    hS.2.1 ↥F hlt ⟨h4, ⟨(F ⊓ H).subgroupOf F, hSE⟩⟩
  letI := hYG
  have hLtop : L = ⊤ := by
    have hle : Submission.Blueprint.oddResidual ↥F ≤ L :=
      (oddResidual_basic (G := ↥F)).2.2.1 _ hLnorm hLodd
    have htop : Submission.Blueprint.oddResidual ↥F = ⊤ := by
      have e : ↥(Submission.Blueprint.oddResidual ↥(Subgroup.centralizer (X : Set G))) ≃* ↥F := by
        rw [hFdef, Work.ThreePoints.p3F]
        exact Subgroup.equivMapOfInjective _ _ Subtype.coe_injective
      have h1 := oddResidual_map_mulEquiv e
      rw [Work.Reductions.oddResidual_self_eq_top] at h1
      rw [← h1, Subgroup.map_top]
      exact MonoidHom.range_eq_top.mpr e.surjective
    rw [htop] at hle
    exact top_le_iff.mp hle
  subst hLtop
  refine ⟨Y, hYG, Finite.of_surjective φ hφsurj,
    φ.comp (Subgroup.topEquiv (G := ↥F)).symm.toMonoidHom,
    hφsurj.comp (Subgroup.topEquiv (G := ↥F)).symm.surjective, ?_, hBender⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hφker,
    Subgroup.mem_subgroupOf, oddCore_p3F_eq_center hFT hC hA hBrSz hS hH ht htH hX0 hX hNX,
    Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  exact forall_congr' (fun g => by
    have hx : (((Subgroup.topEquiv (G := ↥F)).symm.toMonoidHom x : ↥(⊤ : Subgroup ↥F)) : ↥F) = x := rfl
    rw [hx])

/-- A divisor of a power of `2` which is odd equals `1`. -/
theorem eq_one_of_dvd_two_pow_of_odd {m n : ℕ} (h : m ∣ 2 ^ n) (hodd : Odd m) : m = 1 := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  rcases k with _ | j
  · rw [hk, pow_zero]
  · exfalso
    have h2 : Even (2 ^ (j + 1)) := ⟨2 ^ j, by rw [pow_succ, Nat.mul_two]⟩
    exact Nat.not_even_iff_odd.mpr (hk ▸ hodd) h2

/-- `(conj x A).map F.subtype = conj x (A.map F.subtype)` for a subgroup `A ≤ ↥F` and `x ∈ F`. -/
theorem map_conj_subtype' {G : Type} [Group G] {F : Subgroup G} (A : Subgroup ↥F) (x : ↥F) :
    (Submission.Blueprint.conj x A).map F.subtype =
      Submission.Blueprint.conj (x : G) (A.map F.subtype) := by
  show (A.map (MulAut.conj x).toMonoidHom).map F.subtype =
    (A.map F.subtype).map (MulAut.conj (x : G)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  have h : ((F.subtype.comp (MulAut.conj x).toMonoidHom) : ↥F →* G) =
      (MulAut.conj (x : G)).toMonoidHom.comp F.subtype := by
    ext a
    simp [MulAut.conj_apply]
  rw [h]

/-- Peterfalvi I Ch. II §4 Prop. 3 (b) — the assembly; see `Work.ThreePoints.P3NeBot.p3_b`. -/
theorem p3_b_proof {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) {X : Subgroup G} (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ Work.ThreePoints.p3F X ⊓ H ∧
      ¬ 2 ∣ (S.subgroupOf (Work.ThreePoints.p3F X ⊓ H)).index ∧
      H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (S : Set G) ∧
      S ⊓ Submission.Blueprint.twoPoint H t = ⊥ ∧
      S ⊔ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) =
        H ⊓ Subgroup.normalizer (X : Set G) := by
  classical
  let F : Subgroup G := Work.ThreePoints.p3F X
  let D : Subgroup G := Submission.Blueprint.twoPoint H t
  let N : Subgroup G := H ⊓ Subgroup.normalizer (X : Set G)
  have htF : t ∈ F := t_mem_p3F ht hX
  have hFXH : F ≤ Subgroup.normalizer (X : Set G) := p3F_le_normalizer X
  -- ## 1. the model data for `F = p3F X`
  obtain ⟨Y, hYG, hYFin, φ, hφsurj, hφker, hBender⟩ :=
    p3F_quotient_model hFT hC hA hZJ hBrSz hMod hS hH ht htH hX0 hX hNX
  letI := hYG
  haveI : Finite Y := hYFin
  let H₀ : Subgroup ↥F := (F ⊓ H).subgroupOf F
  let t₀ : ↥F := ⟨t, htF⟩
  have hSE : IsStronglyEmbedded H₀ := p3_prop1b hFT hC hA hBrSz hS hH ht htH hX0 hX
  have ht0 : orderOf t₀ = 2 := by rw [← Subgroup.orderOf_coe t₀]; exact ht
  have ht0H : t₀ ∉ H₀ := fun hmem => htH (Subgroup.mem_subgroupOf.mp hmem).2
  have hcenter : Submission.Blueprint.oddCore ↥F = Subgroup.center ↥F :=
    oddCore_p3F_eq_center hFT hC hA hBrSz hS hH ht htH hX0 hX hNX
  obtain ⟨S₀, hS0pg, hS0le, hS0idx, hH0N, hS0inf, hS0sup⟩ :=
    Work.ThreePoints.P3Sub.model_split_b hMod hSE ht0 ht0H hcenter
      ⟨Y, hYG, φ, hφsurj, hφker, hBender⟩
  -- ## 2. the image `S = S₀.map F.subtype`
  have hmapH₀ : H₀.map F.subtype = F ⊓ H := by
    show ((F ⊓ H).subgroupOf F).map F.subtype = F ⊓ H
    rw [Subgroup.subgroupOf_map_subtype (F ⊓ H) F]
    exact inf_eq_left.mpr inf_le_left
  have htwoPoint : (Submission.Blueprint.twoPoint H₀ t₀).map F.subtype = F ⊓ D := by
    have hconjF : F.map (MulAut.conj t).toMonoidHom = F :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (F.le_normalizer htF)
    calc (Submission.Blueprint.twoPoint H₀ t₀).map F.subtype
        = (H₀ ⊓ Submission.Blueprint.conj t₀ H₀).map F.subtype := rfl
      _ = H₀.map F.subtype ⊓ (Submission.Blueprint.conj t₀ H₀).map F.subtype :=
          Subgroup.map_inf H₀ (Submission.Blueprint.conj t₀ H₀) F.subtype Subtype.coe_injective
      _ = (F ⊓ H) ⊓ Submission.Blueprint.conj t (F ⊓ H) := by
          rw [map_conj_subtype' H₀ t₀, hmapH₀]
      _ = F ⊓ D := by
          show (F ⊓ H) ⊓ Submission.Blueprint.conj t (F ⊓ H) =
            F ⊓ Submission.Blueprint.twoPoint H t
          rw [Submission.Blueprint.conj, Subgroup.map_inf (f := (MulAut.conj t).toMonoidHom)
            (hf := (MulAut.conj t).injective), hconjF]
          show (F ⊓ H) ⊓ (F ⊓ H.map (MulAut.conj t).toMonoidHom) =
            F ⊓ (H ⊓ H.map (MulAut.conj t).toMonoidHom)
          ext x
          simp only [Subgroup.mem_inf]
          tauto
  have hSle : S₀.map F.subtype ≤ F ⊓ H := by
    rw [← hmapH₀]; exact Subgroup.map_mono hS0le
  have hidx : ¬ 2 ∣ ((S₀.map F.subtype).subgroupOf (F ⊓ H)).index := by
    have hrel : Subgroup.relIndex (S₀.map F.subtype) (H₀.map F.subtype) =
        Subgroup.relIndex S₀ H₀ :=
      Subgroup.relIndex_map_map_of_injective (f := F.subtype) S₀ H₀ Subtype.coe_injective
    have h : ¬ 2 ∣ ((S₀.map F.subtype).subgroupOf (H₀.map F.subtype)).index := by
      show ¬ 2 ∣ Subgroup.relIndex (S₀.map F.subtype) (H₀.map F.subtype)
      rw [hrel]
      exact hS0idx
    rwa [hmapH₀] at h
  -- ## 3. `F ⊓ H ≤ N_G(S)` and `N ≤ N_G(S)`
  have hBH : F ⊓ H ≤ Subgroup.normalizer ((S₀.map F.subtype : Subgroup G) : Set G) := by
    rw [← hmapH₀, Subgroup.le_normalizer_iff]
    intro b hb a ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    exact Subgroup.mem_map.mpr ⟨b₀ * a₀ * b₀⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hH0N hb₀) a₀).mp ha₀, rfl⟩
  have hNGX : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (F : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (p3F_le_normalizer X)).mp
      (Work.ThreePoints.p3F_subgroupOf_normalizer_normal X)
  have hNB : N ≤ Subgroup.normalizer ((F ⊓ H : Subgroup G) : Set G) := by
    have h1 : N ≤ Subgroup.normalizer (F : Set G) := le_trans inf_le_right hNGX
    have h2 : N ≤ Subgroup.normalizer (H : Set G) := le_trans inf_le_left Subgroup.le_normalizer
    exact le_trans (le_inf h1 h2) Subgroup.inf_normalizer_le_normalizer_inf
  have hNS : N ≤ Subgroup.normalizer ((S₀.map F.subtype : Subgroup G) : Set G) :=
    sylow_le_normalizer hSle hBH (hS0pg.map F.subtype) hidx hNB
  -- ## 4. `S ⊓ D = ⊥`
  have hDodd : Odd (Nat.card ↥D) := hH.2.2 t htH
  have hSD : S₀.map F.subtype ⊓ D = ⊥ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS0pg
    have hcardS : Nat.card ↥(S₀.map F.subtype) = 2 ^ n := by
      rw [Subgroup.card_map_of_injective (f := F.subtype) Subtype.coe_injective, hn]
    have hdiv : Nat.card ↥(S₀.map F.subtype ⊓ D) ∣ 2 ^ n := by
      rw [← hcardS]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hodd : Odd (Nat.card ↥(S₀.map F.subtype ⊓ D)) :=
      Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le inf_le_right)
    have hcard : Nat.card ↥(S₀.map F.subtype ⊓ D) = 1 :=
      eq_one_of_dvd_two_pow_of_odd hdiv hodd
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hdvd1 : orderOf x ∣ 1 := by
      have h := Subgroup.orderOf_dvd_natCard (S₀.map F.subtype ⊓ D) hx
      rwa [hcard] at h
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  -- ## 5. `S ⊔ (D ⊓ N_G(X)) = N`
  have hsplit : S₀.map F.subtype ⊔ (F ⊓ D) = F ⊓ H := by
    have h := congrArg (Subgroup.map F.subtype) hS0sup
    rw [Subgroup.map_sup] at h
    rw [htwoPoint, hmapH₀] at h
    exact h
  refine ⟨S₀.map F.subtype, hS0pg.map F.subtype, hSle, hidx, hNS, hSD, ?_⟩
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ ?_
    · exact le_inf (hSle.trans inf_le_right) (hSle.trans inf_le_left |>.trans hFXH)
    · exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  · have hFHle : F ⊓ H ≤ S₀.map F.subtype ⊔ (D ⊓ Subgroup.normalizer (X : Set G)) := by
      rw [← hsplit]
      refine sup_le le_sup_left ?_
      intro x hx
      exact Subgroup.mem_sup_right (le_inf inf_le_right (inf_le_left.trans hFXH) hx)
    intro n hn
    obtain ⟨hnH, hnNG⟩ := Subgroup.mem_inf.mp hn
    obtain ⟨y, hyF, hnyD, hnyN⟩ :=
      p3_a_decomp hFT hC hA hBrSz hS hH ht htH hX0 hX hNX n hnNG
    have hnySup : n * y ∈ S₀.map F.subtype ⊔ (D ⊓ Subgroup.normalizer (X : Set G)) :=
      Subgroup.mem_sup_right ⟨hnyD, hnyN⟩
    have hyH : y ∈ H := by
      have h : y = n⁻¹ * (n * y) := by group
      rw [h]
      exact H.mul_mem (H.inv_mem hnH) ((inf_le_left : D ≤ H) hnyD)
    have hySup : y ∈ S₀.map F.subtype ⊔ (D ⊓ Subgroup.normalizer (X : Set G)) :=
      hFHle ⟨hyF, hyH⟩
    have hEq : n = (n * y) * y⁻¹ := by group
    rw [hEq]
    exact Subgroup.mul_mem _ hnySup (Subgroup.inv_mem _ hySup)

end Work.ThreePoints.P3NeBot
