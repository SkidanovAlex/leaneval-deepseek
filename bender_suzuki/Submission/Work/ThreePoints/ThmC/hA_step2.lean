import Mathlib
import Submission.Work.ThreePoints.ThmC.hAprereq
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.ThmC.app1_2
import Submission.Work.ThreePoints.ThmC.Base
import Submission.Work.ThreePoints.ThmC.pPrimeCoreSub_conj
import Submission.Work.ThreePoints.involutions_commute_of_below
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.Models.models
import Submission.Work.GlaubermanZJ.ZJ_ne_bot
import Submission.Work.GlaubermanZJ.normalizer_ZJ
import Submission.Work.GlaubermanZJ.ZJ_le
import Submission.Work.GlaubermanZJ.pPrimeCore_characteristic
import Submission.Work.GlaubermanZJ.pPrimeCore_eq_fitting
import Submission.Work.Fitting.piCore_isPiNat
import Submission.Work.Fitting.isPSolvable_of_solvable
import Submission.Work.NPC.Frobenius.lt_normalizer_of_lt_of_isPGroup
import Submission.Work.ThompsonFrobenius.ZJ_subgroupOf
import Submission.Work.ThompsonFrobenius.ZJ_map_of_ker_inf_eq_bot
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000

namespace Work.ThreePoints.ThmC

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-! ## Small helpers -/

/-- The two-point stabiliser `H ⊓ H^g` is invariant under conjugation by `g`, when `g² = 1`. -/
theorem conj_twoPoint_self {G : Type} [Group G] {H : Subgroup G} {g : G} (hg2 : g * g = 1) :
    Submission.Blueprint.conj g (Submission.Blueprint.twoPoint H g) =
      Submission.Blueprint.twoPoint H g := by
  change Submission.Blueprint.conj g (H ⊓ Submission.Blueprint.conj g H) =
    H ⊓ Submission.Blueprint.conj g H
  rw [Work.ThreePoints.conj_inf, ← Work.DoubleTransitivity.conj_mul g g H, hg2,
    Work.DoubleTransitivity.conj_one, inf_comm]

/-- If `twoPoint H s = twoPoint H t` and `t ∉ H`, then `s ∉ H`. -/
theorem not_mem_of_twoPoint_eq {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H)
    {s t : G} (hsD : Submission.Blueprint.twoPoint H s = Submission.Blueprint.twoPoint H t)
    (htH : t ∉ H) : s ∉ H := by
  intro hsH
  have hconj : Submission.Blueprint.conj s H = H := Work.ThreePoints.conj_eq_self_of_mem hsH
  have hH' : Submission.Blueprint.twoPoint H t = H := by
    rw [← hsD]
    change H ⊓ Submission.Blueprint.conj s H = H
    rw [hconj, inf_idem]
  have hle : H ≤ Submission.Blueprint.conj t H := by
    have h2 : Submission.Blueprint.twoPoint H t ≤ Submission.Blueprint.conj t H := inf_le_right
    rwa [hH'] at h2
  have hcard : Nat.card ↥(Submission.Blueprint.conj t H) = Nat.card ↥H :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hEq : H = Submission.Blueprint.conj t H :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
  have htN : t ∈ Subgroup.normalizer (H : Set G) :=
    (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer t H).mp hEq.symm
  rw [Work.ThreePoints.IsStronglyEmbedded.normalizer_eq hH] at htN
  exact htH htN

/-- `O_{p'}(X) = ⊥` as a subgroup of `G` iff the same holds inside `↥X`. -/
theorem pPrimeCoreSub_eq_bot_iff {G : Type} [Group G] {p : ℕ} (X : Subgroup G) :
    Work.ThreePoints.ThmC.pPrimeCoreSub p X = ⊥ ↔
      Submission.Blueprint.pPrimeCore p ↥X = ⊥ := by
  have hker : (X.subtype).ker = ⊥ := Subgroup.ker_subtype X
  constructor
  · intro h
    have h1 : (Submission.Blueprint.pPrimeCore p ↥X).map X.subtype = ⊥ := h
    have h2 := (Subgroup.map_eq_bot_iff _).mp h1
    rwa [hker, le_bot_iff] at h2
  · intro h
    rw [Work.ThreePoints.ThmC.pPrimeCoreSub, h, Subgroup.map_bot]

/-- `|O_{p'}(Y)|` is coprime to `p`. -/
theorem coprime_card_pPrimeCore {p : ℕ} (hp : p.Prime) (Y : Type) [Group Y] [Finite Y] :
    Nat.Coprime (Nat.card ↥(Submission.Blueprint.pPrimeCore p Y)) p := by
  have h := Work.Fitting.piCore_isPiNat Y (fun q => q ≠ p)
  rw [Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
  exact (Work.GlaubermanZJ.isPiNat_ne_iff_coprime hp).mp h

/-- A `p`-subgroup of `D` which is a `p`-Sylow of its own normaliser in `D` is a `p`-Sylow of
`D`.  (Standard "Sylow subgroup of the normaliser" fact.) -/
theorem sylow_of_normalizer {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Q D F : Subgroup G} (hQD : Q ≤ D) (hQF : Q ≤ F)
    (hN : Subgroup.normalizer (Q : Set G) ⊓ D ≤ F)
    (hQp : IsPGroup p Q)
    (h : Work.ThreePoints.ThmC.IsSylowOf p Q (F ⊓ D)) :
    Work.ThreePoints.ThmC.IsSylowOf p Q D := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨hQD, hQp, ?_⟩
  intro S hQS hSD hSp
  by_contra hne
  have hlt : Q < S := lt_of_le_of_ne hQS (fun h => hne h.symm)
  have hgrowth := Work.NPC.Frobenius.lt_normalizer_of_lt_of_isPGroup hSp hlt
  have hle : Subgroup.normalizer (Q : Set G) ⊓ S ≤ F ⊓ D :=
    le_inf (le_trans (le_inf inf_le_left (le_trans inf_le_right hSD)) hN)
      (le_trans inf_le_right hSD)
  have hpg : IsPGroup p (Subgroup.normalizer (Q : Set G) ⊓ S : Subgroup G) :=
    hSp.to_le inf_le_right
  exact hgrowth.ne (h.2.2 _ hgrowth.le hle hpg).symm

/-- `IsSylowOf` is transported across the passage to a subgroup: `R` is a `p`-Sylow of `L` (with
`R, L ≤ K`) iff `R.subgroupOf K` is a `p`-Sylow of `L.subgroupOf K` inside `↥K`. -/
theorem isSylowOf_subgroupOf_iff {G : Type} [Group G] {p : ℕ} {K R L : Subgroup G}
    (hRK : R ≤ K) (hLK : L ≤ K) :
    Work.ThreePoints.ThmC.IsSylowOf p (R.subgroupOf K) (L.subgroupOf K) ↔
      Work.ThreePoints.ThmC.IsSylowOf p R L := by
  constructor
  · intro h
    have hRL : R ≤ L := by
      intro x hx
      have hx' : (⟨x, hRK hx⟩ : ↥K) ∈ R.subgroupOf K := Subgroup.mem_subgroupOf.mpr hx
      exact Subgroup.mem_subgroupOf.mp (h.1 hx')
    refine ⟨hRL, ?_, ?_⟩
    · exact h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hRK)
    · intro S hRS hSL hSp
      have hSK : S ≤ K := hSL.trans hLK
      have h1 : S.subgroupOf K = R.subgroupOf K :=
        h.2.2 (S.subgroupOf K) (Subgroup.subgroupOf_mono K hRS) (Subgroup.subgroupOf_mono K hSL)
          (hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm)
      have h2 := congrArg (Subgroup.map K.subtype) h1
      rwa [Subgroup.map_subgroupOf_eq_of_le hSK, Subgroup.map_subgroupOf_eq_of_le hRK] at h2
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact Subgroup.mem_subgroupOf.mpr (h.1 (Subgroup.mem_subgroupOf.mp hz))
    · exact h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hRK).symm
    · intro S' hRS' hS'L hS'p
      have hmap : S'.map K.subtype = R := by
        refine h.2.2 (S'.map K.subtype) ?_ ?_ (hS'p.map K.subtype)
        · rw [← Subgroup.map_subgroupOf_eq_of_le hRK]
          exact Subgroup.map_mono hRS'
        · rw [← Subgroup.map_subgroupOf_eq_of_le hLK]
          exact Subgroup.map_mono hS'L
      have hthis : R.subgroupOf K = S' :=
        Subgroup.map_injective K.subtype_injective (by
          rw [Subgroup.map_subgroupOf_eq_of_le hRK, hmap])
      exact hthis.symm

/-- `O_{p'}` of `X` is trivial iff `O_{p'}` of `X.subgroupOf K` is trivial (for `X ≤ K`). -/
theorem pPrimeCore_subgroupOf_eq_bot_iff {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X K : Subgroup G} (hXK : X ≤ K) :
    Submission.Blueprint.pPrimeCore p ↥(X.subgroupOf K) = ⊥ ↔
      Submission.Blueprint.pPrimeCore p ↥X = ⊥ := by
  have e : ↥(X.subgroupOf K) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXK
  have hmap : (Work.Fitting.pPrimeCore p ↥(X.subgroupOf K)).map e.toMonoidHom =
      Work.Fitting.pPrimeCore p ↥X :=
    Work.Fitting.piCore_map_mulEquiv (π := fun q => q ≠ p) e
  rw [Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp, Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
  constructor
  · intro h
    have h2 := congrArg (Subgroup.map e.toMonoidHom) h
    rw [hmap, Subgroup.map_bot] at h2
    exact h2
  · intro h
    exact Subgroup.map_injective e.injective (by rw [hmap, h, Subgroup.map_bot])

/-- Peterfalvi Appendix IV applied in the group `↥D`: if `P` is a `p`-Sylow of `P·C_D(P)` and
`O_{p'}(D) = ⊥`, then `O_{p'}(F ⊓ D) = ⊥` for any `F ⊇ P`. -/
theorem pPrimeCoreSub_inf_eq_bot (hFT : Submission.Blueprint.FeitThompsonProp)
    (happ4 : Work.ThreePoints.ThmC.App4Hyp)
    {G : Type} [Group G] [Finite G] {D P F : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hpodd : p ≠ 2) (hoddD : Odd (Nat.card ↥D))
    (hPp : IsPGroup p P) (hPD : P ≤ D)
    (hPC : Work.ThreePoints.ThmC.IsSylowOf p P
      (P ⊔ (Subgroup.centralizer (P : Set G) ⊓ D)))
    (hPF : P ≤ F)
    (hbot : Work.ThreePoints.ThmC.pPrimeCoreSub p D = ⊥) :
    Work.ThreePoints.ThmC.pPrimeCoreSub p (F ⊓ D) = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set X : Subgroup G := Work.ThreePoints.ThmC.pPrimeCoreSub p (F ⊓ D) with hX
  have hXFD : X ≤ F ⊓ D := by
    rw [hX, Work.ThreePoints.ThmC.pPrimeCoreSub]
    exact Subgroup.map_subtype_le _
  have hXD : X ≤ D := hXFD.trans inf_le_right
  have hXcop : Nat.Coprime (Nat.card ↥(X.subgroupOf D)) p := by
    have h1 : Nat.card ↥(X.subgroupOf D) = Nat.card ↥X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXD).toEquiv
    have h3 : Nat.card ↥X = Nat.card ↥(Submission.Blueprint.pPrimeCore p ↥(F ⊓ D)) := by
      rw [hX, Work.ThreePoints.ThmC.pPrimeCoreSub]
      exact (Nat.card_congr
        (Subgroup.equivMapOfInjective _ _ (F ⊓ D).subtype_injective).toEquiv).symm
    rw [h1, h3]
    exact coprime_card_pPrimeCore hp ↥(F ⊓ D)
  have hXn : (F ⊓ D) ≤ Subgroup.normalizer (X : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change Submission.Blueprint.conj g (Work.ThreePoints.ThmC.pPrimeCoreSub p (F ⊓ D)) =
      Work.ThreePoints.ThmC.pPrimeCoreSub p (F ⊓ D)
    have hconj : Submission.Blueprint.conj g (F ⊓ D) = F ⊓ D := by
      rw [Work.ThreePoints.conj_inf,
        (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer g F).mpr
          (Subgroup.le_normalizer hg.1),
        (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer g D).mpr
          (Subgroup.le_normalizer hg.2)]
    have hc := Work.ThreePoints.ThmC.pPrimeCoreSub_conj p hp (F ⊓ D) g
    rw [hconj] at hc
    exact hc.symm
  have hPN : P.subgroupOf D ≤ Subgroup.normalizer (X.subgroupOf D : Set ↥D) := by
    have h1 : P.subgroupOf D ≤ (Subgroup.normalizer (X : Set G)).subgroupOf D :=
      (Subgroup.subgroupOf_mono D (le_inf hPF hPD)).trans (Subgroup.subgroupOf_mono D hXn)
    rwa [Subgroup.subgroupOf_normalizer_eq hXD] at h1
  have hcond : ∀ x : ↥D, x ∈ Subgroup.centralizer (P.subgroupOf D : Set ↥D) →
      orderOf x = p → x ∈ P.subgroupOf D := by
    intro x hx hxo
    have hxo' : orderOf (x : G) = p := (Subgroup.orderOf_mk (x : G) x.2).symm.trans hxo
    have hxG : (x : G) ∈ Subgroup.centralizer (P : Set G) ⊓ D := by
      refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, x.2⟩
      intro y hy
      have hyPD : (⟨y, hPD hy⟩ : ↥D) ∈ P.subgroupOf D := Subgroup.mem_subgroupOf.mpr hy
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hx) ⟨y, hPD hy⟩ hyPD)
    have hxN : (x : G) ∈ Subgroup.normalizer (P : Set G) :=
      Subgroup.centralizer_le_normalizer (P : Set G) hxG.1
    have hzp : IsPGroup p (Subgroup.zpowers (x : G) : Subgroup G) := by
      refine IsPGroup.iff_card.mpr ⟨1, ?_⟩
      rw [Nat.card_zpowers, hxo', pow_one]
    have hzpN : Subgroup.zpowers (x : G) ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.zpowers_le.mpr hxN
    have hsup : IsPGroup p (P ⊔ Subgroup.zpowers (x : G) : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hPp hzp hzpN
    have hle : P ⊔ Subgroup.zpowers (x : G) ≤ P ⊔ (Subgroup.centralizer (P : Set G) ⊓ D) := by
      refine sup_le le_sup_left ?_
      exact (Subgroup.zpowers_le.mpr hxG).trans le_sup_right
    have hsupQ : P ⊔ Subgroup.zpowers (x : G) = P := hPC.2.2 _ le_sup_left hle hsup
    rw [Subgroup.mem_subgroupOf, ← hsupQ]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (x : G))
  have hsol : Group.IsSolvable ↥D := hFT ↥D hoddD
  have hPpD : IsPGroup p (P.subgroupOf D) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
  have hmain : X.subgroupOf D ≤ Submission.Blueprint.pPrimeCore p ↥D :=
    happ4 ↥D hp hpodd hsol (P := P.subgroupOf D) (X := X.subgroupOf D) hPpD hcond hXcop hPN
  have h2 : X ≤ ⊥ := by
    have h3 := Subgroup.map_mono (f := D.subtype) hmain
    rw [Subgroup.map_subgroupOf_eq_of_le hXD, ← Work.ThreePoints.ThmC.pPrimeCoreSub, hbot] at h3
    exact h3
  rw [hX] at h2
  exact le_bot_iff.mp h2

theorem hA_step2 (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (happ4 : Work.ThreePoints.ThmC.App4Hyp) (hlem1 : Work.ThreePoints.ThmC.Lem1Hyp)
    (hlem3 : Work.ThreePoints.ThmC.Lem3Hyp)
    {G : Type} [Group G] [Finite G] (hSit : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    {t u : G} (ht : orderOf t = 2) (htH : t ∉ H)
    (hu : u ∈ Submission.Blueprint.involutions (H : Set G))
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) {P : Subgroup G}
    (hP : Work.ThreePoints.ThmC.IsSylowOf p P (Submission.Blueprint.twoPoint H t ⊓
      Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H t)))
    (huP : u ∈ Subgroup.normalizer (P : Set G))
    {s : G} (hsP : s ∈ Subgroup.normalizer (P : Set G)) (hs2 : orderOf s = 2)
    (hsD : Submission.Blueprint.twoPoint H s = Submission.Blueprint.twoPoint H t)
    (hSylowPC : Work.ThreePoints.ThmC.IsSylowOf p P
      (P ⊔ (Subgroup.centralizer (P : Set G) ⊓ Submission.Blueprint.twoPoint H t)))
    (hnc : ∃ x ∈ P, u * x ≠ x * u)
    (hbot : Work.ThreePoints.ThmC.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t) = ⊥) :
    ∃ Q : Subgroup G, Work.ThreePoints.ThmC.IsSylowOf p Q (Submission.Blueprint.twoPoint H t) ∧
      u ∈ Subgroup.normalizer (Submission.Blueprint.ZJ Q : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Subgroup G := Submission.Blueprint.twoPoint H t with hDdef
  have hDH : D ≤ H := by rw [hDdef]; exact inf_le_left
  have hDDt : D ≤ Submission.Blueprint.conj t H := by rw [hDdef]; exact inf_le_right
  have hHD : H ⊓ Submission.Blueprint.conj s H = D := by
    rw [hDdef]; exact hsD
  have hoddD : Odd (Nat.card ↥D) := by
    show Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t))
    exact hH.2.2 t htH
  have hs2' : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2, pow_two] at h
    exact h
  have hsH : s ∉ H := not_mem_of_twoPoint_eq hH hsD htH
  have hD_s : Submission.Blueprint.conj s D = D := by
    rw [hDdef]
    have h := conj_twoPoint_self (G := G) (H := H) (g := s) hs2'
    rwa [hsD] at h
  have hsND : s ∈ Subgroup.normalizer (D : Set G) :=
    (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer s D).mp hD_s
  have h2t : Submission.Blueprint.IsTwoTransitiveOn H := hA G hSit.1.1 H hH
  obtain ⟨_, h2tN, hclauseC, _⟩ := hlem1 hH h2t hBrSz hFT htH hu hp hpodd hP huP
  -- the family `𝒫`
  let fam : Set (Subgroup G) := {Q : Subgroup G | P ≤ Q ∧ Q ≤ D ∧ IsPGroup p Q ∧
      s ∈ Subgroup.normalizer (Q : Set G) ∧
      Submission.Blueprint.involutions (Subgroup.normalizer (P : Set G) ⊓ H : Set G) ⊆
        (Subgroup.normalizer (Submission.Blueprint.ZJ Q : Set G) : Set G)}
  have hP_fam : P ∈ fam := by
    refine ⟨le_refl P, hP.1.trans inf_le_left, hP.2.1, hsP, ?_⟩
    intro x hx
    exact Work.GlaubermanZJ.normalizer_ZJ P (Subgroup.mem_inf.mp hx.1).1
  haveI : Fintype (Subgroup G) := Fintype.ofFinite (Subgroup G)
  obtain ⟨Q₀, hQ₀mem, hQ₀max⟩ :=
    Finset.exists_max_image (Finset.univ.filter (fun Q : Subgroup G => Q ∈ fam))
      (fun Q : Subgroup G => Nat.card ↥Q)
      ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP_fam⟩⟩
  have hQ₀fam : Q₀ ∈ fam := (Finset.mem_filter.mp hQ₀mem).2
  obtain ⟨hQ₀le, hQ₀D, hQ₀p, hQ₀s, hQ₀3⟩ := hQ₀fam
  have hmaxcard : ∀ Q ∈ fam, Nat.card ↥Q ≤ Nat.card ↥Q₀ := fun Q hQ =>
    hQ₀max Q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ⟩)
  refine ⟨Q₀, ?_, hQ₀3 ⟨⟨huP, hu.1⟩, hu.2⟩⟩
  by_contra hnsyl
  by_cases hnoP : ¬ HasFourGroup (Subgroup.normalizer (P : Set G))
  · have hPDsyl : IsSylowOf p P D := hclauseC hnoP
    have hQP : Q₀ = P := hPDsyl.2.2 Q₀ hQ₀le hQ₀D hQ₀p
    subst hQP
    exact hnsyl hPDsyl
  · have hfourP : HasFourGroup (Subgroup.normalizer (P : Set G)) := not_not.mp hnoP
    -- Case B: `N_G(P)` has 2-rank ≥ 2
    have hstrongNp : IsStronglyEmbedded
        ((Subgroup.normalizer (P : Set G) ⊓ H).subgroupOf (Subgroup.normalizer (P : Set G))) := by
      have hpp : P ≤ Submission.Blueprint.conj (1 : G) H := by
        rw [Work.DoubleTransitivity.conj_one]
        exact hQ₀le.trans (hQ₀D.trans hDH)
      have h := h2tN.2 1 hpp
      rwa [Work.DoubleTransitivity.conj_one] at h
    set F : Subgroup G := Subgroup.normalizer (Submission.Blueprint.ZJ Q₀ : Set G) with hFdef
    have hsF : s ∈ F := by
      rw [hFdef]; exact Work.GlaubermanZJ.normalizer_ZJ Q₀ hQ₀s
    have hQF : Q₀ ≤ F := by
      rw [hFdef]
      exact fun x hx => Work.GlaubermanZJ.normalizer_ZJ Q₀ (Subgroup.le_normalizer hx)
    have hPF : P ≤ F := hQ₀le.trans hQF
    have hfourF : HasFourGroup F := by
      obtain ⟨a, b, ha, hb, ha2, hb2, hne, hcomm⟩ :=
        Work.ThreePoints.ThmC.exists_involutions_mem_of_stronglyEmbedded hstrongNp hfourP
      have ha_inv : (a : G) ∈ Submission.Blueprint.involutions
          (Subgroup.normalizer (P : Set G) ⊓ H : Set G) :=
        ⟨Subgroup.mem_subgroupOf.mp ha, (Subgroup.orderOf_mk (a : G) a.2).symm.trans ha2⟩
      have hb_inv : (b : G) ∈ Submission.Blueprint.involutions
          (Subgroup.normalizer (P : Set G) ⊓ H : Set G) :=
        ⟨Subgroup.mem_subgroupOf.mp hb, (Subgroup.orderOf_mk (b : G) b.2).symm.trans hb2⟩
      have haF : (a : G) ∈ F := hQ₀3 ha_inv
      have hbF : (b : G) ∈ F := hQ₀3 hb_inv
      refine ⟨⟨(a : G), haF⟩, ⟨(b : G), hbF⟩, ?_, ?_, ?_, ?_⟩
      · rw [Subgroup.orderOf_mk]
        exact (Subgroup.orderOf_mk (a : G) a.2).symm.trans ha2
      · rw [Subgroup.orderOf_mk]
        exact (Subgroup.orderOf_mk (b : G) b.2).symm.trans hb2
      · intro hab
        exact hne (Subtype.ext (congrArg (fun z : ↥F => (z : G)) hab))
      · apply Subtype.ext
        simpa using congrArg Subtype.val hcomm
    -- `F` is proper.
    have hFne : F ≠ ⊤ := by
      intro hFtop
      have hAnorm : (Submission.Blueprint.ZJ Q₀).Normal := by
        rw [← Subgroup.normalizer_eq_top_iff, ← hFdef]
        exact hFtop
      have hAodd : Odd (Nat.card ↥(Submission.Blueprint.ZJ Q₀)) := by
        have hpg : IsPGroup p (Submission.Blueprint.ZJ Q₀ : Subgroup G) :=
          IsPGroup.to_le (H := Submission.Blueprint.ZJ Q₀) hQ₀p (Work.GlaubermanZJ.ZJ_le Q₀)
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
        rw [hn]
        exact Odd.pow (hp.odd_of_ne_two hpodd)
      have hAle := Work.BrauerSuzuki.OddCore.le_of_normal_odd hAnorm hAodd
      rw [hSit.2.2, le_bot_iff] at hAle
      have hPne : P ≠ ⊥ := by
        rintro hPbot
        obtain ⟨x, hx, hxu⟩ := hnc
        rw [hPbot, Subgroup.mem_bot] at hx
        exact hxu (by rw [hx]; simp)
      have hQ₀ne : Q₀ ≠ ⊥ := by
        rintro hQ₀bot
        exact hPne (le_bot_iff.mp (hQ₀le.trans (le_of_eq hQ₀bot)))
      exact (Work.GlaubermanZJ.ZJ_ne_bot hp Q₀ hQ₀p hQ₀ne) hAle
    have hcardFG : Nat.card ↥F < Nat.card G := by
      have hlt : F < ⊤ := lt_of_le_of_ne le_top hFne
      have hh := Subgroup.card_lt_of_lt hlt
      rwa [Subgroup.card_top] at hh
    -- `H_F = F ⊓ H` is strongly embedded in `F`.
    have hproperFH : (F ⊓ H).subgroupOf F ≠ ⊤ := by
      intro htop
      have hFH : F ≤ H := by
        intro x hx
        have hx' : (⟨x, hx⟩ : ↥F) ∈ (F ⊓ H).subgroupOf F := by rw [htop]; trivial
        exact (Subgroup.mem_subgroupOf.mp hx').2
      exact hsH (hFH hsF)
    have huF : u ∈ F := hQ₀3 ⟨⟨huP, hu.1⟩, hu.2⟩
    have hevFH : Even (Nat.card ↥(F ⊓ H)) := by
      have h2 : 2 ∣ Nat.card ↥(F ⊓ H) := by
        have hd := Subgroup.card_dvd_of_le
          (Subgroup.zpowers_le.mpr (show u ∈ F ⊓ H from ⟨huF, hu.1⟩))
        rwa [Nat.card_zpowers, hu.2] at hd
      exact even_iff_two_dvd.mpr h2
    have hHF : IsStronglyEmbedded ((F ⊓ H).subgroupOf F) :=
      Work.ThreePoints.IsStronglyEmbedded.subgroupOf_inf hH hproperFH hevFH
    have hcommF : ∀ a b : ↥F,
        a ∈ Submission.Blueprint.involutions (((F ⊓ H).subgroupOf F : Subgroup F) : Set ↥F) →
        b ∈ Submission.Blueprint.involutions (((F ⊓ H).subgroupOf F : Subgroup F) : Set ↥F) →
        a * b * a⁻¹ * b⁻¹ ∈ Submission.Blueprint.oddCore ↥F :=
      fun a b ha hb => Work.ThreePoints.involutions_commute_of_below (Nat.card G) hSit.2.1
        Work.Models.models_prop hcardFG hfourF hHF ha hb
    -- an `s`-invariant `p`-Sylow `R` of `F ⊓ D` containing `Q₀`.
    have hsNFD : s ∈ Subgroup.normalizer ((F ⊓ D : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hsF, hsND⟩
    have hcopFD : Nat.Coprime (Nat.card ↥(F ⊓ D)) 2 :=
      Nat.coprime_two_right.mpr (Odd.of_dvd_nat hoddD (Subgroup.card_dvd_of_le inf_le_right))
    obtain ⟨R, hQR, hRsyl, hsR⟩ :=
      (Work.ThreePoints.ThmC.app1_2 (d := 2) (t := s) (X := F ⊓ D) Nat.prime_two hs2 hcopFD
        hsNFD (p := p) hp).1 Q₀ (le_inf hQF hQ₀D) hQ₀p hQ₀s
    have hRF : R ≤ F := hRsyl.1.trans inf_le_left
    have hRD : R ≤ D := hRsyl.1.trans inf_le_right
    have hneRQ : R ≠ Q₀ := by
      rintro hRQ
      have hQ₀sylFD : IsSylowOf p Q₀ (F ⊓ D) := hRQ ▸ hRsyl
      have hNN : Subgroup.normalizer (Q₀ : Set G) ⊓ D ≤ F :=
        le_trans inf_le_left (Work.GlaubermanZJ.normalizer_ZJ Q₀)
      exact hnsyl (sylow_of_normalizer hp hQ₀D hQF hNN hQ₀p hQ₀sylFD)
    have hltQR : Q₀ < R := lt_of_le_of_ne hQR (fun h => hneRQ h.symm)
    -- `R ∈ 𝒫`
    have hR_fam : R ∈ fam := by
      refine ⟨hQ₀le.trans hQR, hRD, hRsyl.2.1, hsR, ?_⟩
      intro y hy
      have hyF : y ∈ F := hQ₀3 hy
      have hyH : y ∈ H := (Subgroup.mem_inf.mp hy.1).2
      have hy2 : orderOf y = 2 := hy.2
      -- `twoPoint H_F s_F = (F ⊓ D).subgroupOf F`
      have h1F : ((F ⊓ H).subgroupOf F).map F.subtype = F ⊓ H := by
        rw [Subgroup.subgroupOf_map_subtype]
        simp only [inf_assoc, inf_left_comm, inf_comm, inf_idem]
      have h2F : (Subgroup.map (MulAut.conj (⟨s, hsF⟩ : ↥F)).toMonoidHom
            ((F ⊓ H).subgroupOf F)).map F.subtype =
            Submission.Blueprint.conj s (F ⊓ H) := by
        rw [Subgroup.map_map]
        have hcomp : F.subtype.comp (MulAut.conj (⟨s, hsF⟩ : ↥F)).toMonoidHom =
            (MulAut.conj s).toMonoidHom.comp F.subtype := by
          ext x
          exact Work.ThreePoints.ThmC.subtype_conj_apply F (⟨s, hsF⟩ : ↥F) x
        rw [hcomp, ← Subgroup.map_map, h1F]
      have hcF : Submission.Blueprint.conj s F = F :=
        (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer s F).mpr
          (Subgroup.le_normalizer hsF)
      have htwo : Submission.Blueprint.twoPoint ((F ⊓ H).subgroupOf F) (⟨s, hsF⟩ : ↥F)
          = (F ⊓ D).subgroupOf F := by
        apply Subgroup.map_injective F.subtype_injective
        rw [Work.ThreePoints.twoPoint_eq,
          Subgroup.map_inf_eq _ _ F.subtype F.subtype_injective, h1F, h2F,
          Subgroup.subgroupOf_map_subtype, Work.ThreePoints.conj_inf, hcF, ← hHD]
        simp only [inf_assoc, inf_left_comm, inf_comm, inf_idem]
      have hR_F : IsSylowOf p (R.subgroupOf F) ((F ⊓ D).subgroupOf F) :=
        (isSylowOf_subgroupOf_iff (p := p) (K := F) hRF inf_le_left).mpr hRsyl
      have hR_F' : IsSylowOf p (R.subgroupOf F)
          (Submission.Blueprint.twoPoint ((F ⊓ H).subgroupOf F) (⟨s, hsF⟩ : ↥F)) := by
        rw [htwo]; exact hR_F
      have hsF2 : orderOf (⟨s, hsF⟩ : ↥F) = 2 := by
        rw [Subgroup.orderOf_mk]; exact hs2
      have hsFH : (⟨s, hsF⟩ : ↥F) ∉ ((F ⊓ H).subgroupOf F) := by
        intro hmem
        exact hsH (Subgroup.mem_subgroupOf.mp hmem).2
      have hOp'FD : Submission.Blueprint.pPrimeCore p ↥(F ⊓ D) = ⊥ :=
        (pPrimeCoreSub_eq_bot_iff (F ⊓ D)).mp
          (pPrimeCoreSub_inf_eq_bot hFT happ4 hp hpodd hoddD hP.2.1 (hP.1.trans inf_le_left)
            hSylowPC hPF hbot)
      have hOp'_F : Submission.Blueprint.pPrimeCore p
          ↥(Submission.Blueprint.twoPoint ((F ⊓ H).subgroupOf F) (⟨s, hsF⟩ : ↥F)) = ⊥ := by
        rw [htwo]
        exact (pPrimeCore_subgroupOf_eq_bot_iff hp inf_le_left).mpr hOp'FD
      have hPcond : ∃ Q' : Subgroup ↥F,
          Q' ≤ Submission.Blueprint.twoPoint ((F ⊓ H).subgroupOf F) (⟨s, hsF⟩ : ↥F) ∧
          IsPGroup p Q' ∧
          ∃ u' ∈ Submission.Blueprint.involutions
              (((F ⊓ H).subgroupOf F : Subgroup ↥F) : Set ↥F),
            u' ∈ Subgroup.normalizer (Q' : Set ↥F) ∧ ¬ ∀ x ∈ Q', u' * x = x * u' := by
        refine ⟨P.subgroupOf F, ?_, ?_, ⟨⟨u, huF⟩, ?_, ?_, ?_⟩⟩
        · rw [htwo]
          exact Subgroup.subgroupOf_mono F (le_inf hPF (hQ₀le.trans hQ₀D))
        · exact hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPF).symm
        · exact ⟨Subgroup.mem_subgroupOf.mpr ⟨huF, hu.1⟩, (Subgroup.orderOf_mk u huF).trans hu.2⟩
        · refine Work.ThreePoints.ThmC.mem_normalizer_of_mapsTo ?_
          intro w hw
          rw [Subgroup.mem_subgroupOf] at hw
          show u * (w : G) * u⁻¹ ∈ P
          exact (Subgroup.mem_normalizer_iff.mp huP) (w : G) |>.mp hw
        · rintro hall
          obtain ⟨x, hxP, hxu⟩ := hnc
          have hxF : x ∈ F := hPF hxP
          have key := hall ⟨x, hxF⟩ (Subgroup.mem_subgroupOf.mpr hxP)
          exact hxu (congrArg Subtype.val key)
      -- `hlem3` in `F`
      have hres := hlem3 (F := ↥F) hFT hZJ hfourF hHF hcommF hsF2 hsFH hp hpodd hR_F'
        hOp'_F hPcond
      have hy_F : (⟨y, hyF⟩ : ↥F) ∈ Submission.Blueprint.involutions
          (((F ⊓ H).subgroupOf F : Subgroup ↥F) : Set ↥F) :=
        ⟨Subgroup.mem_subgroupOf.mpr ⟨hyF, hyH⟩, (Subgroup.orderOf_mk y hyF).trans hy2⟩
      have hyNF : (⟨y, hyF⟩ : ↥F) ∈ Subgroup.normalizer
          (Submission.Blueprint.ZJ (R.subgroupOf F) : Set ↥F) := hres hy_F
      refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
      show Submission.Blueprint.conj y (Submission.Blueprint.ZJ R) = Submission.Blueprint.ZJ R
      have hyNF' : Subgroup.map (MulAut.conj (⟨y, hyF⟩ : ↥F)).toMonoidHom
            ((Submission.Blueprint.ZJ R).subgroupOf F) =
            (Submission.Blueprint.ZJ R).subgroupOf F := by
        rw [← Work.ThompsonFrobenius.ZJ_subgroupOf hRF]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hyNF
      have hconjF : Submission.Blueprint.conj y (Submission.Blueprint.ZJ R) =
          (Subgroup.map (MulAut.conj (⟨y, hyF⟩ : ↥F)).toMonoidHom
            ((Submission.Blueprint.ZJ R).subgroupOf F)).map F.subtype := by
        rw [Subgroup.map_map]
        have hcomp : F.subtype.comp (MulAut.conj (⟨y, hyF⟩ : ↥F)).toMonoidHom =
            (MulAut.conj y).toMonoidHom.comp F.subtype := by
          ext x
          exact Work.ThreePoints.ThmC.subtype_conj_apply F (⟨y, hyF⟩ : ↥F) x
        rw [hcomp, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr (le_trans (Work.GlaubermanZJ.ZJ_le R) hRF)]
      rw [hconjF, hyNF']
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr (le_trans (Work.GlaubermanZJ.ZJ_le R) hRF)
    have hcardR := hmaxcard R hR_fam
    have hcardlt : Nat.card ↥Q₀ < Nat.card ↥R := Subgroup.card_lt_of_lt hltQR
    omega

end Work.ThreePoints.ThmC
