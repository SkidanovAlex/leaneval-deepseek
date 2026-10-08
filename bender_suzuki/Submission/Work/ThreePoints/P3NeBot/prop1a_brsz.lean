import Mathlib
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.ThreePoints.ch1_lem2
import Submission.Work.ThreePoints.odd_card_of_fixes_three
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.sec3_lemma2
import Submission.Work.ThreePoints.twoTransitive_stabilizer_even_of_brsz
import Submission.Work.ThreePoints.involutions_conj_of_stronglyEmbedded
import Submission.Work.ThreePoints.exists_descent_odd_solvable
import Submission.Work.DoubleTransitivity.App1.Defs
import Submission.Work.DoubleTransitivity.App1.app1_1b
import Submission.Work.DoubleTransitivity.App1.app1_2
import Submission.Work.DoubleTransitivity.Sec4.Defs
import Submission.Work.DoubleTransitivity.Sec4.prop2
import Submission.Work.Coprime.exists_invariant_sylow_ge

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.P3NeBot

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

/-- A subgroup of even order contains an element of order two (Cauchy's theorem). -/
theorem exists_mem_orderOf_eq_two_of_even_card {K : Subgroup G} (h : Even (Nat.card K)) :
    ∃ x : G, x ∈ K ∧ orderOf x = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp h)
  exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

/-- If `Inv C_G(Y) ⊆ F` and `|M ⊓ C_G(Y)|` is even, then `|F ⊓ M|` is even. -/
theorem even_card_inf_of_even_card_inf_centralizer {Y F M : Subgroup G}
    (hev : Even (Nat.card (M ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G)))
    (hFY : involutions (Subgroup.centralizer (Y : Set G) : Set G) ⊆ F) :
    Even (Nat.card (F ⊓ M : Subgroup G)) := by
  obtain ⟨u, hu, hu2⟩ := exists_mem_orderOf_eq_two_of_even_card hev
  have huF : u ∈ F := hFY ⟨hu.2, hu2⟩
  have huFM : u ∈ F ⊓ M := ⟨huF, hu.1⟩
  have hdvd : Nat.card (Subgroup.zpowers u : Subgroup G) ∣ Nat.card (F ⊓ M : Subgroup G) :=
    Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr huFM)
  rw [even_iff_two_dvd]
  rwa [Nat.card_zpowers, hu2] at hdvd

/-- If `Y` fixes at least three points of `Ω` then, for any prescribed `g`, some other coset `g'H`
is also fixed by `Y`. -/
theorem exists_mk_fixedPts_ne {H Y : Subgroup G} {g : G} (hY3 : 3 ≤ (fixedPts H Y).ncard) :
    ∃ g' : G, (g' : G ⧸ H) ∈ fixedPts H Y ∧ (g' : G ⧸ H) ≠ (g : G ⧸ H) := by
  have h2 : 1 < (fixedPts H Y).ncard := by omega
  obtain ⟨ω₁, hω₁, ω₂, hω₂, hne⟩ := (Set.one_lt_ncard (s := fixedPts H Y)).mp h2
  by_cases h : ω₁ = (g : G ⧸ H)
  · obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective ω₂
    refine ⟨g', hg'.symm ▸ hω₂, fun hcontra => hne ?_⟩
    rw [h, ← hg']
    exact hcontra.symm
  · obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective ω₁
    exact ⟨g', hg'.symm ▸ hω₁, fun hcontra => h (by rw [← hg', hcontra])⟩

/-- **Peterfalvi I Ch. II §4 Prop. 1 (b)**, conditional form restricted to a single subgroup `Y`. -/
theorem isStronglyEmbedded_inf_of_even {H Y F : Subgroup G} {g : G}
    (hH : IsStronglyEmbedded H) (hY3 : 3 ≤ (fixedPts H Y).ncard)
    (hFY : involutions (Subgroup.centralizer (Y : Set G) : Set G) ⊆ F)
    (hg : Y ≤ conj g H)
    (hEV : ∀ {M' : Subgroup G}, (∃ g' : G, M' = conj g' H) → Y ≤ M' →
      Even (Nat.card (M' ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G))) :
    IsStronglyEmbedded ((F ⊓ conj g H).subgroupOf F) := by
  have hM : IsStronglyEmbedded (conj g H) := conj_stronglyEmbedded hH g
  have hev : Even (Nat.card (F ⊓ conj g H : Subgroup G)) :=
    even_card_inf_of_even_card_inf_centralizer (hEV ⟨g, rfl⟩ hg) hFY
  have hproper : (F ⊓ conj g H).subgroupOf F ≠ ⊤ := by
    obtain ⟨g', hfix, hne_pt⟩ := exists_mk_fixedPts_ne (H := H) (Y := Y) (g := g) hY3
    have hYg' : Y ≤ conj g' H := by
      rw [← stabilizer_mk H g']
      exact mem_fixedPts_iff_le_stabilizer.mp hfix
    have hconjne : conj g H ≠ conj g' H := by
      intro heq
      exact hne_pt (mk_eq_of_conj_eq hH heq.symm)
    obtain ⟨u, hu, hu2⟩ := exists_mem_orderOf_eq_two_of_even_card (hEV ⟨g', rfl⟩ hYg')
    have huF : u ∈ F := hFY ⟨hu.2, hu2⟩
    have huNotM : u ∉ conj g H := by
      intro huM
      have huinf : u ∈ conj g H ⊓ conj g' H := ⟨huM, hu.1⟩
      have hdvd : Nat.card (Subgroup.zpowers u : Subgroup G) ∣
          Nat.card (conj g H ⊓ conj g' H : Subgroup G) :=
        Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr huinf)
      rw [Nat.card_zpowers, hu2] at hdvd
      exact Nat.not_even_iff_odd.mpr (card_inf_conj_odd hH hconjne)
        (even_iff_two_dvd.mpr hdvd)
    intro htop
    have hmem : u ∈ F ⊓ conj g H := by
      refine ⟨huF, ?_⟩
      have h' : (⟨u, huF⟩ : F) ∈ (F ⊓ conj g H).subgroupOf F := by rw [htop]; trivial
      exact (Subgroup.mem_subgroupOf.mp h').2
    exact huNotM hmem.2
  exact IsStronglyEmbedded.subgroupOf_inf hM hproper hev

/-- Mapping a conjugate of a subgroup of `F` down to `G` commutes with conjugation. -/
theorem map_conj_subtype {F : Subgroup G} (A : Subgroup F) (x : F) :
    ((Submission.Blueprint.conj x A).map F.subtype : Subgroup G) =
      Submission.Blueprint.conj (x : G) (A.map F.subtype) := by
  show (A.map (MulAut.conj x).toMonoidHom).map F.subtype =
    (A.map F.subtype).map (MulAut.conj (x : G)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  have h : ((F.subtype.comp (MulAut.conj x).toMonoidHom) : F →* G) =
      (MulAut.conj (x : G)).toMonoidHom.comp F.subtype := by
    ext a
    simp [MulAut.conj_apply]
  rw [h]

/-- `A ≤ B` inside `F` iff the images in `G` are ordered. -/
theorem map_subtype_le_map_subtype_iff {F : Subgroup G} (A B : Subgroup F) :
    A ≤ B ↔ A.map F.subtype ≤ B.map F.subtype :=
  ⟨Subgroup.map_mono, fun h a ha => by
    have : (a : G) ∈ B.map F.subtype := h (Subgroup.mem_map_of_mem F.subtype ha)
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp this
    have hba' : b = a := Subtype.ext hba
    rw [← hba']
    exact hb⟩

/-- Two conjugates `M ≠ M'` of a strongly embedded subgroup with `M ⊓ F = M' ⊓ F` for
`F ⊇ C_G(Y)` contradict the evenness of `|M ⊓ C_G(Y)|` and `|M' ⊓ C_G(Y)|`. -/
theorem eq_of_inf_eq_of_even {H Y F : Subgroup G} (hH : IsStronglyEmbedded H)
    {M M' : Subgroup G} {g g' : G} (hgM : M = conj g H) (hg'M : M' = conj g' H)
    (hCYF : Subgroup.centralizer (Y : Set G) ≤ F)
    (h2 : Even (Nat.card (M ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G)))
    (h2' : Even (Nat.card (M' ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G)))
    (hinf : F ⊓ M = F ⊓ M') : M = M' := by
  by_contra hne
  have hne' : conj g H ≠ conj g' H := by
    intro hcon
    exact hne (hgM.trans (hcon.trans hg'M.symm))
  obtain ⟨u, hu, hu2⟩ := exists_mem_orderOf_eq_two_of_even_card h2
  have huF : u ∈ F := hCYF hu.2
  have huM' : u ∈ M' := by
    have hmem : u ∈ F ⊓ M' := by rw [← hinf]; exact ⟨huF, hu.1⟩
    exact hmem.2
  have huinf : u ∈ M ⊓ M' := ⟨hu.1, huM'⟩
  have hdvd : Nat.card (Subgroup.zpowers u : Subgroup G) ∣ Nat.card (M ⊓ M' : Subgroup G) :=
    Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr huinf)
  rw [Nat.card_zpowers, hu2, hgM, hg'M] at hdvd
  exact Nat.not_even_iff_odd.mpr (card_inf_conj_odd hH hne') (even_iff_two_dvd.mpr hdvd)

/-- The two external inputs. -/
structure Inputs (G : Type) [Group G] [Finite G] : Prop where
  s4 : ∀ {F : Type} [Group F] [Finite F], BrauerSuzukiProp → ThmAProp →
    {K : Subgroup F} → IsStronglyEmbedded K → {p : ℕ} → p.Prime → p ≠ 2 → {Q : Subgroup F} →
    Q ≤ K → IsPGroup p Q → 3 ≤ (fixedPts K Q).ncard →
    (∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R → 3 ≤ (fixedPts K R).ncard → R = Q) →
    ∃ u : F, u ∈ K ∧ u ∈ Subgroup.normalizer (Q : Set F) ∧ orderOf u = 2
  descent : ∀ {X : Subgroup G}, X ≠ ⊥ → Odd (Nat.card X) → Group.IsSolvable ↥X →
    ∃ (Y P : Subgroup G) (p : ℕ), Y ≤ X ∧ (Y.subgroupOf X).Normal ∧ Nat.card Y < Nat.card X ∧
      p.Prime ∧ p ≠ 2 ∧ IsPGroup p P ∧ P ≤ X ∧ Y ⊔ P = X

/-- Main induction: given the two inputs, Prop. 1 (a) holds. -/
theorem even_of_fixes_three_of_inputs (hIn : Inputs G)
    (hFT : FeitThompsonProp) (hC : ThmCProp) (hA : ThmAProp) (hBrSz : BrauerSuzukiProp)
    (hS : Situation G) {H : Subgroup G} (hH : IsStronglyEmbedded H)
    {X M : Subgroup G} (hX3 : 3 ≤ (fixedPts H X).ncard)
    (hM : ∃ g : G, M = conj g H) (hXM : X ≤ M) :
    Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) := by
  classical
  have main : ∀ n : ℕ, ∀ X M : Subgroup G, Nat.card X = n → 3 ≤ (fixedPts H X).ncard →
      (∃ g : G, M = conj g H) → X ≤ M →
      Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro X M hcard hX3 hM hXM
      rcases eq_or_ne X ⊥ with rfl | hXbot
      · obtain ⟨g, rfl⟩ := hM
        have h2 : Even (Nat.card (conj g H)) := (conj_stronglyEmbedded hH g).2.1
        have hcent : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
          rw [Subgroup.centralizer_eq_top_iff_subset]
          intro x hx
          change x ∈ Subgroup.center G
          rw [Subgroup.mem_center_iff]
          intro y
          rw [show x = 1 from by simpa using hx]
          simp
        rw [hcent, inf_top_eq]
        exact h2
      · have hXodd : Odd (Nat.card X) := odd_card_of_fixes_three hH hX3
        obtain ⟨Y, P, p, hYX, hYN, hYlt, hpprime, hp2, hPp, hPX, hYP⟩ :=
          hIn.descent hXbot hXodd (hFT ↥X hXodd)
        have hY3 : 3 ≤ (fixedPts H Y).ncard :=
          le_trans hX3 (Set.ncard_mono (fixedPts_mono hYX))
        have hIHY : ∀ M' : Subgroup G, (∃ g : G, M' = conj g H) → Y ≤ M' →
            Even (Nat.card (M' ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G)) := by
          intro M' hM' hYM'
          exact ih (Nat.card Y) (by rw [← hcard]; exact hYlt) Y M' rfl hY3 hM' hYM'
        obtain ⟨g₀, hg₀⟩ := hM
        set F : Subgroup G := Subgroup.normalizer (Y : Set G) with hFdef
        have hCYF : Subgroup.centralizer (Y : Set G) ≤ F := by
          rw [hFdef]
          exact Subgroup.centralizer_le_normalizer (Y : Set G)
        have hXF : X ≤ F := by
          rw [hFdef]
          intro x hx
          rw [Subgroup.mem_normalizer_iff_map_conj_eq]
          have key := (Subgroup.normal_subgroupOf_iff hYX).mp hYN
          have h1 : (conj x Y : Subgroup G) ≤ Y := by
            rintro y ⟨z, hz, rfl⟩
            simpa using key z x hz hx
          have h3 : (conj x⁻¹ Y : Subgroup G) ≤ Y := by
            rintro y ⟨z, hz, rfl⟩
            simpa using key z x⁻¹ hz (X.inv_mem hx)
          have h4 : Y ≤ conj x Y := by
            have h6 : (conj x (conj x⁻¹ Y) : Subgroup G) ≤ conj x Y := Subgroup.map_mono h3
            have h7 : (conj x (conj x⁻¹ Y) : Subgroup G) = Y := by
              have h8 := Work.DoubleTransitivity.conj_inv_conj (x⁻¹) Y
              rwa [inv_inv] at h8
            rwa [h7] at h6
          exact le_antisymm h1 h4
        have hYF : Y ≤ F := by rw [hFdef]; exact Subgroup.le_normalizer
        have hPF : P ≤ F := le_trans hPX hXF
        have hMstrong : IsStronglyEmbedded M := by rw [hg₀]; exact conj_stronglyEmbedded hH g₀
        have hKse : IsStronglyEmbedded ((F ⊓ M).subgroupOf F) := by
          rw [hg₀]
          refine isStronglyEmbedded_inf_of_even (F := F) (g := g₀) hH hY3 ?_ ?_ ?_
          · intro u hu
            exact hCYF hu.1
          · rw [← hg₀]; exact le_trans hYX hXM
          · intro M' hM' hYM'
            exact hIHY M' hM' hYM'
        set KF : Subgroup F := (F ⊓ M).subgroupOf F with hKFdef
        have hKFmap : KF.map F.subtype = F ⊓ M := Subgroup.map_subgroupOf_eq_of_le inf_le_left
        set PF : Subgroup F := P.subgroupOf F with hPFdef
        have hPFmap : PF.map F.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPF
        have hPFKF : PF ≤ KF := by
          rw [map_subtype_le_map_subtype_iff, hPFmap, hKFmap]
          exact fun x hx => ⟨hPF hx, hPX.trans hXM hx⟩
        have hPFp : IsPGroup p PF := hPp.comap_of_injective F.subtype Subtype.coe_injective
        -- the three fixed points of PF
        have hPF3 : 3 ≤ (fixedPts KF PF).ncard := by
          have hfix : ∀ (x : F) (g : G), (conj x KF).map F.subtype = F ⊓ conj g H →
              P ≤ conj g H → ((x : F) : F ⧸ KF) ∈ fixedPts KF PF := by
            intro x g hx hPg
            rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer, Work.ThreePoints.stabilizer_mk,
              map_subtype_le_map_subtype_iff, hx, hPFmap]
            exact fun y hy => ⟨hPF hy, hPg hy⟩
          have key : ∀ ω : G ⧸ H, ω ∈ fixedPts H X →
              ∃ (g : G) (x : F), ω = (g : G ⧸ H) ∧
                MulAction.stabilizer G ω = conj g H ∧
                (conj x KF).map F.subtype = F ⊓ conj g H := by
            intro ω hω
            obtain ⟨g₂, hg₂⟩ := QuotientGroup.mk_surjective ω
            have hstab : MulAction.stabilizer G ω = conj g₂ H := by
              rw [← hg₂, Work.ThreePoints.stabilizer_mk]
            have hXg₂ : X ≤ conj g₂ H := by
              rw [← hstab]
              exact Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mp hω
            have hYg₂ : Y ≤ conj g₂ H := le_trans hYX hXg₂
            have h2 : Even (Nat.card (F ⊓ conj g₂ H : Subgroup G)) :=
              even_card_inf_of_even_card_inf_centralizer
                (hIHY (conj g₂ H) ⟨g₂, rfl⟩ hYg₂) (by intro u hu; exact hCYF hu.1)
            by_cases hcase : conj g₂ H = M
            · refine ⟨g₂, 1, hg₂.symm, hstab, ?_⟩
              have hconj1 : Submission.Blueprint.conj (1 : F) KF = KF := by
                ext y
                rw [Submission.Blueprint.conj, Subgroup.mem_map]
                constructor
                · rintro ⟨z, hz, hzy⟩
                  have hzy' : z = y := by simpa [MulAut.conj_apply] using hzy
                  rwa [hzy'] at hz
                · intro hy
                  exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
              rw [hconj1, hKFmap, hcase]
            · have hne : conj g₀ H ≠ conj g₂ H := by
                intro hcon
                apply hcase
                rw [← hcon]
                exact hg₀.symm
              have h1 : Even (Nat.card (F ⊓ conj g₀ H : Subgroup G)) :=
                even_card_inf_of_even_card_inf_centralizer
                  (hIHY (conj g₀ H) ⟨g₀, rfl⟩ (by rw [← hg₀]; exact le_trans hYX hXM))
                  (by intro u hu; exact hCYF hu.1)
              obtain ⟨t, htinv, ht⟩ := (Work.ThreePoints.ch1_lem2 hH hne h1 h2).1
              have htF : t ∈ F := (Work.ThreePoints.mem_involutions.mp htinv).1
              refine ⟨g₂, ⟨t, htF⟩, hg₂.symm, hstab, ?_⟩
              rw [map_conj_subtype, hKFmap, Work.ThreePoints.conj_inf,
                Work.ThreePoints.conj_eq_self_of_mem htF]
              congr 1
              rw [hg₀]; exact ht
          have hdist : ∀ (x y : F) (g g' : G), Y ≤ conj g H → Y ≤ conj g' H →
              (conj x KF).map F.subtype = F ⊓ conj g H →
              (conj y KF).map F.subtype = F ⊓ conj g' H →
              conj g H ≠ conj g' H → ((x : F) : F ⧸ KF) ≠ ((y : F) : F ⧸ KF) := by
            intro x y g g' hYg hYg' hx hy hne heq
            have h1 : MulAction.stabilizer ↥F ((x : F) : F ⧸ KF) =
                MulAction.stabilizer ↥F ((y : F) : F ⧸ KF) := by rw [heq]
            rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.stabilizer_mk] at h1
            have h1' : (conj x KF).map F.subtype = (conj y KF).map F.subtype := by rw [h1]
            rw [hx, hy] at h1'
            exact hne (eq_of_inf_eq_of_even hH (by rfl) (by rfl) hCYF
              (hIHY (conj g H) ⟨g, rfl⟩ hYg) (hIHY (conj g' H) ⟨g', rfl⟩ hYg') h1')
          obtain ⟨ω₁, hω₁⟩ := (Set.ncard_pos (s := fixedPts H X)).mp (by omega)
          obtain ⟨ω₂, hω₂, hne₂⟩ := Set.exists_ne_of_one_lt_ncard
            (by omega : 1 < (fixedPts H X).ncard) ω₁
          have h4 : 1 < ((fixedPts H X) \ {ω₁}).ncard := by
            have h1 := Set.ncard_sdiff_singleton_add_one hω₁
            omega
          obtain ⟨ω₃, hω₃⟩ := Set.exists_ne_of_one_lt_ncard h4 ω₂
          have hω₃mem : ω₃ ∈ fixedPts H X := hω₃.1.1
          have hω₃ne₁ : ω₃ ≠ ω₁ := hω₃.1.2
          have hω₃ne : ω₃ ≠ ω₂ := hω₃.2
          obtain ⟨g₁, x₁, hg₁, hstab₁, hx₁⟩ := key ω₁ hω₁
          obtain ⟨g₂, x₂, hg₂, hstab₂, hx₂⟩ := key ω₂ hω₂
          obtain ⟨g₃, x₃, hg₃, hstab₃, hx₃⟩ := key ω₃ hω₃mem
          have hY₁ : Y ≤ conj g₁ H := by
            rw [← hstab₁]; exact le_trans hYX (Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mp hω₁)
          have hY₂ : Y ≤ conj g₂ H := by
            rw [← hstab₂]; exact le_trans hYX (Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mp hω₂)
          have hY₃ : Y ≤ conj g₃ H := by
            rw [← hstab₃]; exact le_trans hYX (Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mp hω₃mem)
          have hP₁ : P ≤ conj g₁ H := by
            rw [← hstab₁]
            exact hPX.trans (Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mp hω₁)
          have hP₂ : P ≤ conj g₂ H := by
            rw [← hstab₂]
            exact hPX.trans (Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mp hω₂)
          have hP₃ : P ≤ conj g₃ H := by
            rw [← hstab₃]
            exact hPX.trans (Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mp hω₃mem)
          have hf₁ : ((x₁ : F) : F ⧸ KF) ∈ fixedPts KF PF := hfix x₁ g₁ hx₁ hP₁
          have hf₂ : ((x₂ : F) : F ⧸ KF) ∈ fixedPts KF PF := hfix x₂ g₂ hx₂ hP₂
          have hf₃ : ((x₃ : F) : F ⧸ KF) ∈ fixedPts KF PF := hfix x₃ g₃ hx₃ hP₃
          have hne₁₂ : ((x₁ : F) : F ⧸ KF) ≠ ((x₂ : F) : F ⧸ KF) :=
            hdist x₁ x₂ g₁ g₂ hY₁ hY₂ hx₁ hx₂ (by
              intro hcon
              exact hne₂ (hg₁.trans ((mk_eq_of_conj_eq hH hcon).trans hg₂.symm)).symm)
          have hne₁₃ : ((x₁ : F) : F ⧸ KF) ≠ ((x₃ : F) : F ⧸ KF) :=
            hdist x₁ x₃ g₁ g₃ hY₁ hY₃ hx₁ hx₃ (by
              intro hcon
              exact hω₃ne₁ (hg₁.trans ((mk_eq_of_conj_eq hH hcon).trans hg₃.symm)).symm)
          have hne₂₃ : ((x₂ : F) : F ⧸ KF) ≠ ((x₃ : F) : F ⧸ KF) :=
            hdist x₂ x₃ g₂ g₃ hY₂ hY₃ hx₂ hx₃ (by
              intro hcon
              exact hω₃ne (hg₂.trans ((mk_eq_of_conj_eq hH hcon).trans hg₃.symm)).symm)
          have htwo : 2 < (fixedPts KF PF).ncard := by
            rw [Set.two_lt_ncard]
            exact ⟨_, hf₁, _, hf₂, _, hf₃, hne₁₂, hne₁₃, hne₂₃⟩
          omega

        obtain ⟨QF, hQFmem, hQFmax⟩ := Set.Finite.exists_maximal
          (s := {R : Subgroup F | PF ≤ R ∧ R ≤ KF ∧ IsPGroup p R ∧
            3 ≤ (fixedPts KF R).ncard})
          (Set.toFinite _) ⟨PF, le_rfl, hPFKF, hPFp, hPF3⟩
        obtain ⟨hPFQF, hQFKK, hQFp, hQF3⟩ := hQFmem
        have hQFmax' : ∀ R : Subgroup F, QF ≤ R → R ≤ KF → IsPGroup p R →
            3 ≤ (fixedPts KF R).ncard → R = QF := by
          intro R hQR hRK hRp hR3
          exact le_antisymm (hQFmax ⟨le_trans hPFQF hQR, hRK, hRp, hR3⟩ hQR) hQR
        obtain ⟨uF, huFK, huFN, huF2⟩ := hIn.s4 hBrSz hA hKse hpprime hp2 hQFKK hQFp hQF3 hQFmax'
        set Q : Subgroup G := QF.map F.subtype with hQdef
        have hQK : Q ≤ F ⊓ M := by
          rw [hQdef, ← hKFmap]
          exact Subgroup.map_mono hQFKK
        have hPQ : P ≤ Q := by
          rw [hQdef, ← hPFmap]
          exact Subgroup.map_mono hPFQF
        have huFM' : ((uF : ↥F) : G) ∈ F ⊓ M := by
          have h : ((uF : ↥F) : G) ∈ KF.map F.subtype := Subgroup.mem_map_of_mem F.subtype huFK
          rwa [hKFmap] at h
        have huM : ((uF : ↥F) : G) ∈ M := huFM'.2
        have huY : ((uF : ↥F) : G) ∈ Subgroup.normalizer (Y : Set G) := (uF : ↥F).2
        have huQ : ((uF : ↥F) : G) ∈ Subgroup.normalizer (Q : Set G) := by
          have h1 : QF.map (MulAut.conj uF).toMonoidHom = QF :=
            Subgroup.mem_normalizer_iff_map_conj_eq.mp huFN
          have h3 : ((QF.map (MulAut.conj uF).toMonoidHom).map F.subtype : Subgroup G) =
              QF.map F.subtype := by rw [h1]
          rw [Subgroup.map_map] at h3
          rw [show ((F.subtype.comp (MulAut.conj uF).toMonoidHom) : ↥F →* G) =
              (MulAut.conj ((uF : ↥F) : G)).toMonoidHom.comp F.subtype from by
                ext a; simp [MulAut.conj_apply]] at h3
          rw [← Subgroup.map_map] at h3
          rw [hQdef]
          exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h3
        have hu2 : orderOf (((uF : ↥F) : G)) = 2 := by
          rw [Subgroup.orderOf_coe (H := F) uF]
          exact huF2
        -- a fixed point of `QF` different from the point of `1`
        have hconj1 : Submission.Blueprint.conj (1 : ↥F) KF = KF := by
          ext y
          rw [Submission.Blueprint.conj, Subgroup.mem_map]
          constructor
          · rintro ⟨z, hz, hzy⟩
            have hzy' : z = y := by simpa [MulAut.conj_apply] using hzy
            rwa [hzy'] at hz
          · intro hy
            exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
        have hpt1 : ((1 : ↥F) : ↥F ⧸ KF) ∈ fixedPts KF QF := by
          rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer, Work.ThreePoints.stabilizer_mk,
            hconj1]
          exact hQFKK
        obtain ⟨ω, hω, hωne⟩ := Set.exists_ne_of_one_lt_ncard
          (by omega : 1 < (fixedPts KF QF).ncard) ((1 : ↥F) : ↥F ⧸ KF)
        obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective ω
        have hQFstab : QF ≤ conj x KF := by
          have h1 : QF ≤ MulAction.stabilizer ↥F ω :=
            Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mp hω
          rwa [← hx, Work.ThreePoints.stabilizer_mk] at h1
        have hQx : Q ≤ conj ((x : ↥F) : G) M := by
          have h1 : (conj (x : ↥F) KF).map F.subtype = conj ((x : ↥F) : G) (F ⊓ M) := by
            rw [map_conj_subtype, hKFmap]
          rw [hQdef]
          refine le_trans (Subgroup.map_mono hQFstab) ?_
          rw [h1]
          exact Subgroup.map_mono inf_le_right
        have hxnotM : ((x : ↥F) : G) ∉ M := by
          intro hxM
          have hxKF : (x : ↥F) ∈ KF := by
            rw [hKFdef]
            refine Subgroup.mem_subgroupOf.mpr ⟨?_, hxM⟩
            exact x.2
          have hxpt : (x : ↥F ⧸ KF) = ((1 : ↥F) : ↥F ⧸ KF) :=
            QuotientGroup.eq.mpr (by simpa using KF.inv_mem hxKF)
          exact hωne (hx.symm.trans hxpt)
        have hYx : Y ≤ conj ((x : ↥F) : G) M := by
          have hxN : (conj ((x : ↥F) : G) Y : Subgroup G) = Y :=
            Subgroup.mem_normalizer_iff_map_conj_eq.mp (x : ↥F).2
          rw [← hxN]
          exact Subgroup.map_mono (le_trans hYX hXM)
        have hZle : (Y ⊔ Q : Subgroup G) ≤ M ⊓ conj ((x : ↥F) : G) M := by
          refine le_inf ?_ ?_
          · refine sup_le ?_ ?_
            · exact le_trans hYX hXM
            · exact hQK.trans inf_le_right
          · refine sup_le ?_ ?_
            · exact hYx
            · exact hQx
        have hcentY : ∀ z ∈ Y, ((uF : ↥F) : G) * z = z * ((uF : ↥F) : G) :=
          hC G hS M hMstrong x hxnotM _ ⟨huM, hu2⟩ Y (le_trans le_sup_left hZle) huY
        have hcentQ : ∀ z ∈ Q, ((uF : ↥F) : G) * z = z * ((uF : ↥F) : G) :=
          hC G hS M hMstrong x hxnotM _ ⟨huM, hu2⟩ Q (le_trans le_sup_right hZle) huQ
        refine even_iff_two_dvd.mpr ?_
        have hmem : ((uF : ↥F) : G) ∈ (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
          refine ⟨huM, ?_⟩
          change ((uF : ↥F) : G) ∈ Subgroup.centralizer (X : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [← hYP] at hh
          have hsub : (Y ⊔ P : Subgroup G) ≤ Subgroup.centralizer ({((uF : ↥F) : G)} : Set G) := by
            refine sup_le ?_ ?_
            · intro y hy
              rw [Subgroup.mem_centralizer_iff]
              intro z hz
              rw [Set.mem_singleton_iff] at hz
              rw [hz]
              exact hcentY y hy
            · intro p hp
              rw [Subgroup.mem_centralizer_iff]
              intro z hz
              rw [Set.mem_singleton_iff] at hz
              rw [hz]
              exact hcentQ p (hPQ hp)
          exact (Subgroup.mem_centralizer_iff.mp (hsub hh) _ (Set.mem_singleton _)).symm
        have hord : orderOf (⟨((uF : ↥F) : G), hmem⟩ :
            ↥(M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) = 2 := by
          rw [Subgroup.orderOf_mk]; exact hu2
        have hdvd := orderOf_dvd_natCard (⟨((uF : ↥F) : G), hmem⟩ :
            ↥(M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G))
        rwa [hord] at hdvd
  exact main (Nat.card X) X M rfl hX3 hM hXM


/-- An element of `K` normalising `Q.subgroupOf K` (as a subgroup of `↥K`) normalises `Q`
(as a subgroup of `F`). -/
theorem mem_normalizer_of_mem_normalizer_subgroupOf {F : Type} [Group F] {K Q : Subgroup F}
    (hQK : Q ≤ K) {x : ↥K} (hx : x ∈ Subgroup.normalizer (Q.subgroupOf K : Set K)) :
    (x : F) ∈ Subgroup.normalizer (Q : Set F) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro y
  constructor
  · intro hy
    have hyK : y ∈ K := hQK hy
    exact (Subgroup.mem_normalizer_iff''.mp hx (⟨y, hyK⟩ : ↥K)).mp hy
  · intro hy
    have hyK : y ∈ K := by
      by_contra h
      apply h
      have hyK2 : (x : F)⁻¹ * y * (x : F) ∈ K := hQK hy
      have h2 : y = (x : F) * ((x : F)⁻¹ * y * (x : F)) * (x : F)⁻¹ := by group
      rw [h2]
      exact K.mul_mem (K.mul_mem x.2 hyK2) (K.inv_mem x.2)
    exact (Subgroup.mem_normalizer_iff''.mp hx (⟨y, hyK⟩ : ↥K)).mpr hy

/-- A subgroup of a `p`-group intersected with a centraliser is again a `p`-group (the
`subgroupOf`/`subgroupOfEquivOfLe` transport of `IsPGroup.to_subgroup`). -/
theorem isPGroup_inf_centralizer {G : Type} [Group G] {P C : Subgroup G} {p : ℕ}
    (hPp : IsPGroup p ↥P) : IsPGroup p ↥(P ⊓ C) := by
  have h1 : IsPGroup p ↥((P ⊓ C).subgroupOf P) := hPp.to_subgroup ((P ⊓ C).subgroupOf P)
  exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left)

/-- If `T ≤ X` is normalised by `t` (an involution normalising `X`), then `T.subgroupOf X` is
invariant under the conjugation action of `⟨t⟩` on `X` (the instance form of `exists_invariant_sylow_ge`).
`T` is `⟨t⟩`-invariant because its normaliser is a subgroup containing `t`. -/
theorem isInvariant_subgroupOf_zpowers {G : Type} [Group G] {X : Subgroup G} {t : G}
    [FT.Normalizes (Subgroup.zpowers t) X] {T : Subgroup G}
    (hTX : T ≤ X) (hTt : t ∈ Subgroup.normalizer (T : Set G)) :
    FT.IsInvariant (Subgroup.zpowers t) (T.subgroupOf X) := by
  refine ⟨fun a => ?_⟩
  have haN : (a : G) ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.zpowers_le.mpr hTt a.2
  refine Subgroup.ext fun y => ?_
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf]
  have hcoe : (↑(a⁻¹ • y : ↥X) : G) = (a : G)⁻¹ * (y : G) * (a : G) := by
    show ((FT.conjSmul (Subgroup.zpowers t) X _ a⁻¹ y : ↥X) : G) =
      (a : G)⁻¹ * (y : G) * (a : G)
    simp only [FT.conjSmul_coe, Subgroup.coe_inv, inv_inv]
  rw [hcoe]
  simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
    (Subgroup.inv_mem (Subgroup.normalizer (T : Set G)) haN) (y : G)).symm

/-- **Step (1) of App. I (3)(a):** if a `p`-Sylow `P'` of `↥X` is fixed by the conjugation action
of `⟨t⟩`, then `t` normalises the image of `P'` in `G`.  (`[FT.Normalizes (Subgroup.zpowers t) X]`
is a parameter: the statement itself needs the resulting `MulDistribMulAction`.) -/
theorem mem_normalizer_map_subtype_of_invariant {G : Type} [Group G] [Finite G] {X : Subgroup G}
    {t : G} [FT.Normalizes (Subgroup.zpowers t) X] {p : ℕ} (hp : p.Prime)
    {P' : Sylow p ↥X}
    (hP'inv : ∀ a : ↥(Subgroup.zpowers t), a • P' = P') :
    t ∈ Subgroup.normalizer ((P' : Subgroup ↥X).map X.subtype : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have htX : t ∈ Subgroup.normalizer (X : Set G) :=
    (FT.Normalizes.le_normalizer (A := Subgroup.zpowers t) (G := X)) (Subgroup.mem_zpowers t)
  -- the `↥X`-level statement, with the `MulAut ↥X`-action pinned
  have hPsmul : Work.DoubleTransitivity.App1.conjAut X t htX • (P' : Subgroup ↥X) =
      (P' : Subgroup ↥X) := by
    have h2 : (⟨t, Subgroup.mem_zpowers t⟩ : ↥(Subgroup.zpowers t)) • (P' : Subgroup ↥X) =
        (P' : Subgroup ↥X) := by
      have h3 := congrArg (fun S : Sylow p ↥X => (S : Subgroup ↥X))
        (hP'inv ⟨t, Subgroup.mem_zpowers t⟩)
      rwa [Sylow.pointwise_smul_def] at h3
    rw [← Work.DoubleTransitivity.App1.smul_eq_toMulAut_smul,
      ← Work.DoubleTransitivity.App1.conjAut_eq_toMulAut
        (a := (⟨t, Subgroup.mem_zpowers t⟩ : ↥(Subgroup.zpowers t)))] at h2
    exact h2
  have hfix : Submission.Blueprint.conj t ((P' : Subgroup ↥X).map X.subtype) =
      (P' : Subgroup ↥X).map X.subtype := by
    rw [Work.DoubleTransitivity.App1.conj_map_subtype (X := X) (t := t) (ht := htX)
      (S := (P' : Subgroup ↥X)),
      ← Work.DoubleTransitivity.App1.conjAut_smul_eq_map (X := X) (t := t) (ht := htX)
        (S := (P' : Subgroup ↥X))]
    rw [hPsmul]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hfix

/-- **App. I (2), conjugacy part:** two `t`-invariant `p`-Sylows of an odd-order subgroup `X` are
conjugate by an element of `C_X(t)`.  (`app1_2` provides one `t`-invariant Sylow `P₀` and the
conjugacy of any `t`-invariant Sylow to it; composing gives the statement for arbitrary pairs.) -/
theorem conj_sylow_of_invariant {G : Type} [Group G] [Finite G] {X : Subgroup G} {t : G}
    (ht : orderOf t = 2) (htX : t ∈ Subgroup.normalizer (X : Set G))
    (hodd : Odd (Nat.card X)) {p : ℕ} (hp : p.Prime)
    {P Q : Subgroup G} (hP : Work.DoubleTransitivity.IsSylowSubgroupOf p P X)
    (hPt : t ∈ Subgroup.normalizer (P : Set G))
    (hQ : Work.DoubleTransitivity.IsSylowSubgroupOf p Q X)
    (hQt : t ∈ Subgroup.normalizer (Q : Set G)) :
    ∃ w ∈ X ⊓ Subgroup.centralizer ({t} : Set G), Submission.Blueprint.conj w P = Q := by
  have hcop : Nat.Coprime 2 (Nat.card X) := Nat.coprime_two_left.mpr hodd
  obtain ⟨P₀, -, -, hconj⟩ :=
    Work.DoubleTransitivity.App1.app1_2 (X := X) (t := t) (d := 2) Nat.prime_two ht hcop htX hp
  obtain ⟨v₁, hv₁, hc₁⟩ := hconj P hP hPt
  obtain ⟨v₂, hv₂, hc₂⟩ := hconj Q hQ hQt
  have hP₀ : P₀ = Submission.Blueprint.conj v₁⁻¹ P := by
    have h := congrArg (Submission.Blueprint.conj v₁⁻¹) hc₁
    rw [← Work.DoubleTransitivity.conj_mul, inv_mul_cancel, Work.DoubleTransitivity.conj_one] at h
    exact h
  refine ⟨v₂ * v₁⁻¹, ?_, ?_⟩
  · exact (X ⊓ Subgroup.centralizer ({t} : Set G)).mul_mem hv₂ (Subgroup.inv_mem _ hv₁)
  · rw [Work.DoubleTransitivity.conj_mul, ← hP₀, hc₂]

/-- Conjugation by an element of `C_G(t)` fixes `C_G(t)` (cardinality input of the sandwich in
App. I (3)(a)). -/
theorem conj_centralizer_of_mem {G : Type} [Group G] {t w : G}
    (hw : w ∈ Subgroup.centralizer ({t} : Set G)) :
    Submission.Blueprint.conj w (Subgroup.centralizer ({t} : Set G)) =
      Subgroup.centralizer ({t} : Set G) := by
  have hiff : ∀ x : G, x ∈ Subgroup.centralizer ({t} : Set G) ↔ t * x = x * t := by
    intro x
    rw [Subgroup.mem_centralizer_iff]
    exact ⟨fun h => h t (Set.mem_singleton t),
      fun h h' hh' => by rw [Set.mem_singleton_iff.mp hh']; exact h⟩
  have hwt : t * w = w * t := (hiff w).mp hw
  have hwinv : t * w⁻¹ = w⁻¹ * t := by
    rw [show t * w⁻¹ = w⁻¹ * (w * t) * w⁻¹ by group, ← hwt]
    group
  ext x
  simp only [Submission.Blueprint.conj, Subgroup.mem_map, hiff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    calc t * (w * y * w⁻¹) = (t * w) * y * w⁻¹ := by group
      _ = (w * t) * y * w⁻¹ := by rw [hwt]
      _ = w * (t * y) * w⁻¹ := by group
      _ = w * (y * t) * w⁻¹ := by rw [hy]
      _ = w * y * (t * w⁻¹) := by group
      _ = w * y * (w⁻¹ * t) := by rw [hwinv]
      _ = w * y * w⁻¹ * t := by group
  · intro hx
    refine ⟨w⁻¹ * x * w, ?_, by show w * (w⁻¹ * x * w) * w⁻¹ = x; group⟩
    calc t * (w⁻¹ * x * w) = (t * w⁻¹) * x * w := by group
      _ = (w⁻¹ * t) * x * w := by rw [hwinv]
      _ = w⁻¹ * (t * x) * w := by group
      _ = w⁻¹ * (x * t) * w := by rw [hx]
      _ = w⁻¹ * x * (t * w) := by group
      _ = w⁻¹ * x * (w * t) := by rw [hwt]
      _ = w⁻¹ * x * w * t := by group

/-- Any subgroup of `C_G(t)` is `t`-invariant.  (Used to feed the invariant-Sylow extension in
App. I (3)(a).) -/
theorem conj_eq_self_of_le_centralizer {G : Type} [Group G] {t : G} {V T : Subgroup G}
    (hV : V ≤ Subgroup.centralizer ({t} : Set G)) (hTV : T ≤ V) :
    Submission.Blueprint.conj t T = T := by
  have h1 : ∀ y ∈ T, t * y * t⁻¹ = y := by
    intro y hy
    have h2 : t * y = y * t :=
      (Subgroup.mem_centralizer_iff.mp (hV (hTV hy))) t (Set.mem_singleton t)
    rw [h2]; group
  ext y
  rw [Submission.Blueprint.conj, Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    change t * z * t⁻¹ ∈ T
    rw [h1 z hz]
    exact hz
  · intro hy
    refine ⟨y, hy, ?_⟩
    change t * y * t⁻¹ = y
    exact h1 y hy

/-- A `p`-group, viewed inside a larger subgroup (`subgroupOf` transport of `IsPGroup` along the
inclusion).  This is the `comap_of_injective` idiom used in
`even_card_normalizer_of_maximal_p_subgroup`. -/
theorem isPGroup_subgroupOf {G : Type} [Group G] {H K : Subgroup G} {p : ℕ}
    (hH : IsPGroup p ↥H) (hHK : H ≤ K) : IsPGroup p ↥(H.subgroupOf K) :=
  hH.comap_of_injective K.subtype Subtype.coe_injective

/-- **App. I (1) for the conjugation orbit:** for a subgroup `X` of odd order normalised by an
involution `t`, the conjugation orbit `t^X` and `J(X,t) = invertedBy X t` have the same
cardinality (`t^X` maps bijectively onto `{[t,x]} = commutatorSet t X` via `u ↦ t⁻¹u`, and
`{[t,x]} = J(X,t)` because `|X|` is odd). -/
theorem ncard_conjOrbit_eq_ncard_invertedBy {G : Type} [Group G] {X : Subgroup G}
    (hodd : Odd (Nat.card X)) {t : G} (ht : orderOf t = 2)
    (hnorm : t ∈ Subgroup.normalizer (X : Set G)) :
    (Work.DoubleTransitivity.conjOrbit X t).ncard =
      (Submission.Blueprint.invertedBy X t).ncard := by
  have hset : Work.DoubleTransitivity.commutatorSet t X = Submission.Blueprint.invertedBy X t :=
    Set.Subset.antisymm
      (Work.DoubleTransitivity.App1.commutatorSet_subset_invertedBy (X := X) (t := t) ht hnorm)
      (Work.DoubleTransitivity.App1.invertedBy_subset_commutatorSet (X := X) (t := t) ht hodd)
  have himg := Work.DoubleTransitivity.image_conjOrbit_eq_commutatorSet X t
  have hinj : Function.Injective (fun u : G => t⁻¹ * u) := fun a b h => by
    simpa using congrArg (fun z : G => t * z) h
  rw [← hset, ← himg, Set.ncard_image_of_injective _ hinj]

/-- **The structure behind Ch. I §4 Prop. 1 (b).**  Let `K` be a strongly embedded subgroup,
`P ≤ G` a subgroup normalised by an involution `u` which fixes the point `ω₁`, and let
`ω₂ ≠ ω₁` be another point fixed by `P`.  Then `P` does not fix exactly two points.

Indeed an involution has a *unique* fixed point (`Work.DoubleTransitivity.Sec1.unique_fixed`), so
`u` has no fixed point other than `ω₁`; but `u` permutes the fixed points of any subgroup it
normalises, so if `Ω_P = {ω₁, ω₂}` then `u • ω₂ ∈ Ω_P`, and `u • ω₂ ≠ ω₂` forces
`u • ω₂ = ω₁ = u • ω₁`, i.e. `ω₂ = ω₁` — a contradiction. -/
theorem ncard_fixedPts_ne_two_of_mem_normalizer {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K) {P : Subgroup G} {ω₁ ω₂ : G ⧸ K}
    (hne : ω₁ ≠ ω₂) (h₁ : ω₁ ∈ Submission.Blueprint.fixedPts K P)
    (h₂ : ω₂ ∈ Submission.Blueprint.fixedPts K P) {u : G} (hu : orderOf u = 2)
    (huP : u ∈ Subgroup.normalizer (P : Set G)) (huω : u • ω₁ = ω₁) :
    (Submission.Blueprint.fixedPts K P).ncard ≠ 2 := by
  intro hcard
  obtain ⟨ωu, _, huniq⟩ := existsUnique_fixedPts_of_orderOf_eq_two hK hu
  have hu1 : ωu = ω₁ := (huniq ω₁ huω).symm
  -- `u` permutes the fixed points of `P` (which it normalises)
  have hinv : ∀ ω ∈ Submission.Blueprint.fixedPts K P,
      u • ω ∈ Submission.Blueprint.fixedPts K P := by
    intro ω hω q hq
    have hqP : u⁻¹ * q * u ∈ P := by
      have h := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (P : Set G)).inv_mem huP) q).mp hq
      simpa only [inv_inv] using h
    calc q • (u • ω) = (q * u) • ω := by rw [mul_smul]
      _ = (u * (u⁻¹ * q * u)) • ω := by rw [show u * (u⁻¹ * q * u) = q * u from by group]
      _ = u • ((u⁻¹ * q * u) • ω) := by rw [mul_smul]
      _ = u • ω := by rw [hω (u⁻¹ * q * u) hqP]
  have hcard2 : ({ω₁, ω₂} : Set (G ⧸ K)).ncard = 2 := Set.ncard_pair hne
  have hsub : ({ω₁, ω₂} : Set (G ⧸ K)) ⊆ Submission.Blueprint.fixedPts K P := by
    intro x hx
    rcases hx with h | h
    · rw [h]; exact h₁
    · rw [h]; exact h₂
  have hle : (Submission.Blueprint.fixedPts K P).ncard ≤ 2 := by
    have := Set.ncard_le_ncard hsub
    rw [hcard2] at this
    omega
  have hset : Submission.Blueprint.fixedPts K P = {ω₁, ω₂} :=
    (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard2]; exact hle)).symm
  have hmem : u • ω₂ ∈ Submission.Blueprint.fixedPts K P := hinv ω₂ h₂
  rw [hset] at hmem
  have hne2 : u • ω₂ ≠ ω₂ := by
    intro h
    exact hne ((huniq ω₂ h).trans hu1).symm
  rcases hmem with h | h
  · exact hne (smul_left_cancel u (h.trans huω.symm)).symm
  · exact hne2 h

/-- **App. I (3)(a):** if `X` has odd order, `t` is an involution normalising `X` and `P` is a
`t`-invariant `p`-Sylow of `X`, then `C_P(t) = P ⊓ C_G(t)` is a `p`-Sylow of `C_X(t) = X ⊓ C_G(t)`. -/
theorem isSylowSubgroupOf_inf_centralizer {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hodd : Odd (Nat.card X)) {t : G} (ht : orderOf t = 2)
    (htX : t ∈ Subgroup.normalizer (X : Set G)) {p : ℕ} (hp : p.Prime)
    {P : Subgroup G} (hP : Work.DoubleTransitivity.IsSylowSubgroupOf p P X)
    (htP : t ∈ Subgroup.normalizer (P : Set G)) :
    Work.DoubleTransitivity.IsSylowSubgroupOf p (P ⊓ Subgroup.centralizer ({t} : Set G))
      (X ⊓ Subgroup.centralizer ({t} : Set G)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hC
  set V : Subgroup G := X ⊓ C with hV
  set VP : Subgroup G := P ⊓ C with hVP
  have hPV : P ≤ X := hP.1
  have hVPle : VP ≤ V := inf_le_inf hPV le_rfl
  have hVPp : IsPGroup p ↥VP := isPGroup_inf_centralizer hP.isPGroup
  have hVPp' : IsPGroup p ↥(VP.subgroupOf V) := isPGroup_subgroupOf hVPp hVPle
  obtain ⟨T, hVPT⟩ := IsPGroup.exists_le_sylow hVPp'
  set Tg : Subgroup G := (T : Subgroup ↥V).map V.subtype with hTg
  have hTgle : Tg ≤ V := Subgroup.map_subtype_le _
  have hTgX : Tg ≤ X := hTgle.trans inf_le_left
  have hTgC : Tg ≤ C := hTgle.trans inf_le_right
  have hVPTg : VP ≤ Tg := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hVPle hx⟩, hVPT (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hVleC : V ≤ Subgroup.centralizer ({t} : Set G) := by rw [hV]; exact inf_le_right
  have hTgt : t ∈ Subgroup.normalizer (Tg : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (conj_eq_self_of_le_centralizer hVleC hTgle)
  haveI hNorm : FT.Normalizes (Subgroup.zpowers t) X := ⟨Subgroup.zpowers_le.mpr htX⟩
  haveI hInvTg : FT.IsInvariant (Subgroup.zpowers t) (Tg.subgroupOf X) :=
    isInvariant_subgroupOf_zpowers hTgX hTgt
  have hcopt : (Nat.card ↥(Subgroup.zpowers t)).Coprime (Nat.card ↥X) := by
    rw [Nat.card_zpowers, ht]
    exact Nat.coprime_two_left.mpr hodd
  obtain ⟨P', hTgP', hP'inv⟩ := Work.Coprime.exists_invariant_sylow_ge
    (Subgroup.zpowers t) hcopt (Or.inl inferInstance) p (Tg.subgroupOf X)
    (isPGroup_subgroupOf (T.isPGroup'.map V.subtype) hTgX)
  set P'g : Subgroup G := (P' : Subgroup ↥X).map X.subtype with hP'g
  have hP'gs : Work.DoubleTransitivity.IsSylowSubgroupOf p P'g X :=
    Work.DoubleTransitivity.App1.isSylowSubgroupOf_map_subtype hp P'
  have hP'gt : t ∈ Subgroup.normalizer (P'g : Set G) :=
    mem_normalizer_map_subtype_of_invariant hp hP'inv
  have hTgP'g : Tg ≤ P'g := by
    have h1 : Tg = (Tg.subgroupOf X).map X.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hTgX).symm
    rw [h1, hP'g]
    exact Subgroup.map_mono hTgP'
  obtain ⟨w, hw, hwP⟩ := conj_sylow_of_invariant ht htX hodd hp hP htP hP'gs hP'gt
  have hwC : Submission.Blueprint.conj w C = C := conj_centralizer_of_mem hw.2
  have hcard : Nat.card ↥(P'g ⊓ C) = Nat.card ↥VP := by
    have h1 : Submission.Blueprint.conj w (P ⊓ C) = P'g ⊓ C := by
      rw [Work.ThreePoints.conj_inf, hwP, hwC]
    rw [← h1, hVP]
    show Nat.card ↥(Subgroup.map (MulAut.conj w).toMonoidHom (P ⊓ C)) = Nat.card ↥(P ⊓ C)
    exact Subgroup.card_map_of_injective (MulAut.conj w).injective
  have hle : Tg ≤ P'g ⊓ C := le_inf hTgP'g hTgC
  have hcardle : Nat.card ↥Tg ≤ Nat.card ↥VP := by
    calc Nat.card ↥Tg ≤ Nat.card ↥(P'g ⊓ C) :=
          Nat.card_le_card_of_injective
            (fun a : ↥Tg => (⟨(a : G), hle a.2⟩ : ↥(P'g ⊓ C)))
            (fun a b h => Subtype.ext (congrArg (fun z : ↥(P'g ⊓ C) => (z : G)) h))
      _ = Nat.card ↥VP := hcard
  have hTgVP : Tg = VP := (Subgroup.eq_of_le_of_card_ge hVPTg hcardle).symm
  refine ⟨hVPle, hVPp, ?_⟩
  have hcomm : (Tg.subgroupOf V) = (T : Subgroup ↥V) := by
    ext x
    rw [Subgroup.mem_subgroupOf, hTg, Subgroup.mem_map]
    exact ⟨fun ⟨y, hy, hyx⟩ => Subgroup.subtype_injective V hyx ▸ hy,
      fun hx => ⟨x, hx, rfl⟩⟩
  rw [← hTgVP, hcomm]
  exact Sylow.not_dvd_index T

/-- **Peterfalvi I Ch. I §4 Prop. 2** (p. 156–157), uniformly in the `2`-rank of `F`: if `K ≤ F` is
strongly embedded, `p ≠ 2` is a prime and `Q ≤ K` is a `p`-subgroup maximal among the `p`-subgroups
of `K` fixing at least three points of `Ω = F ⧸ K`, then `Q` is normalised by an involution of `K`.

This is `Work.DoubleTransitivity.Sec4.prop2` (which gives both `MaxFixesThree p K Q` and
`Even |N_F(Q) ⊓ K|`) followed by Cauchy's theorem.  It uses neither `ThmAProp` nor a `2`-rank
hypothesis: the source's Ch. I §4 analysis of `p`-regular intersections handles the `𝓡_p = ∅` case
(Ch. I §4 Prop. 1 (a): `F` is two-transitive on `Ω`) and the `𝓡_p ≠ ∅` case (Prop. 1 (b): no
`p`-subgroup has exactly two fixed points) directly. -/
theorem s4prop2_uniform {F : Type} [Group F] [Finite F]
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {K : Subgroup F} (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup F} (hQK : Q ≤ K)
    (hQp : IsPGroup p Q) (hQ3 : 3 ≤ (Submission.Blueprint.fixedPts K Q).ncard)
    (hQmax : ∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) :
    ∃ u : F, u ∈ K ∧ u ∈ Subgroup.normalizer (Q : Set F) ∧ orderOf u = 2 := by
  have hP : Work.DoubleTransitivity.MaxFixesThreeIn p K Q :=
    ⟨hQp, hQK, hQ3, fun R hRp hRK hR3 hQR => le_of_eq (hQmax R hQR hRK hRp hR3)⟩
  obtain ⟨-, heven⟩ := Work.DoubleTransitivity.Sec4.prop2 hBrSz hK hp hp2 hP
  obtain ⟨u, hu, hu2⟩ := exists_mem_orderOf_eq_two_of_even_card heven
  exact ⟨u, hu.2, hu.1, hu2⟩

/-- **Peterfalvi I Ch. I §4 Prop. 2**, the `2`-rank `≤ 1` case (which by
`Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup` is the only remaining case):
in a finite group `F` without a four-group, a `p`-subgroup `Q ≤ K` (`p ≠ 2`) of a strongly
embedded subgroup `K`, maximal among the `p`-subgroups of `K` fixing at least three points of
`F ⧸ K`, is normalised by an involution of `K`.

**Route.**  The workspace already contains a complete proof of the corresponding *evenness*
statement, `Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_nofour`
(`Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K))`), whose only
unresolved input is `Work.ThreePoints.S4Prop2.no_two_fixed_pts` (Ch. I §4 Prop. 1 (b) for
`2`-rank `1`: in a group without a four-group with a strongly embedded subgroup `H`, no
`p`-subgroup with `p ≠ 2` fixes exactly two points of `G ⧸ H`).  Once that statement is
available, this lemma is Cauchy's theorem (`exists_mem_orderOf_eq_two_of_even_card`) plus
`mem_normalizer_of_mem_normalizer_subgroupOf`.

**Plan for `no_two_fixed_pts`** (all ingredients are in the workspace).  Assume
`¬ HasFourGroup G`, `H` strongly embedded, `p ≠ 2` prime and `|Ω_P| = 2` for a `p`-subgroup `P`.
* *Every Sylow `2`-subgroup of `G` has a unique involution*:
  `Work.BrauerSuzuki.Group.uniqueInvolution_of_pgroup`; hence by
  `Work.BrauerSuzuki.Group.isConj_of_orderOf_eq_two` **all involutions of `G` are conjugate**,
  and by `Work.DoubleTransitivity.Sec1.unique_fixed` every involution has a unique fixed point.
* *`R_p ≠ ∅`*: since `H ≠ ⊤` there are distinct conjugates `H ≠ H'`, `D := H ⊓ H' ∈ 𝓓`.  If
  `p ∤ |D|` then `⊥` is a `p`-Sylow of `D` and `N(⊥) ⊓ H = H` has even order, so `(D,H) ∈ R_p`.
  Otherwise `p ∣ |D|` and `D` is normalised by `t ∈ Inv(G∖H)` with `H^t = H'`; by
  `Work.DoubleTransitivity.App1.app1_2` there is a `t`-invariant `p`-Sylow `P₀` of `D`, so that
  `t ∈ N(P₀)` and `N(P₀)` has even order; conjugating an involution of `N(P₀)` into `H`
  (conjugacy of involutions) produces a `p`-Sylow `cP₀c⁻¹` of `cDc⁻¹ ∈ 𝓓` normalised by an
  involution of `H`, i.e. `(cDc⁻¹, H) ∈ R_p` (`IsRegularIntersection`).
* *`R_p ≠ ∅` kills `|Ω_P| = 2`*: extend `P` to a `p`-Sylow `S` with `|Ω_S| = 2` (App. II (1),
  `Work.DoubleTransitivity.App2.app2_1`, using `p ≠ 2`); on the other hand the regular
  intersection yields a `p`-subgroup with `≥ 3` fixed points, and a Sylow containing it is
  conjugate to `S`, contradicting `|Ω_S| = 2`.

**The isolated sub-step is now proved** as `ncard_fixedPts_ne_two_of_mem_normalizer` above:
if `P ∈ Syl_p(H₁ ⊓ H₂)` and an involution `u ∈ N(P) ⊓ H₁` exists (which is exactly what
`Even |N(P) ⊓ H₁|` provides), then `P` cannot have exactly two fixed points — an involution has a
*unique* fixed point, yet permutes the fixed points of any subgroup it normalises.  This is the
source's remark "`|N_H(P)|` even, so `|Ω_P| ≥ 3`" (p. 155), together with `2 ≤ |Ω_P|` from the two
points `H₁, H₂`.

**What is left** is one statement — the *normalizer-climb* of Ch. I §4 Lemma 2, in the sharpened
form an exhaustive GAP check over all `¬HasFourGroup` groups of order `≤ 100` confirms (no
counterexample):

> If `Q ∈ Syl_p(K₁ ⊓ K₂)`, `|N_G(Q) ⊓ K₁|` is even, and `K₃ ∈ Ω` with `Q ≤ K₁ ⊓ K₃`, then
> `Q ∈ Syl_p(K₁ ⊓ K₃)`.

Its use is the whole finish: `R_p ≠ ∅` (construction above) yields such a `Q` with an involution
`u ∈ N(Q) ⊓ K₁`, hence `3 ≤ |Ω_Q|` by `ncard_fixedPts_ne_two_of_mem_normalizer`; if a `p`-Sylow
`S ⊇ Q` of `G` had `|Ω_S| = 2 = {ω₁, ω₂}` then `Q ≤ K₁ ⊓ K₂` and `S ≤ K₁ ⊓ K₂`, so the climb
gives `Q ∈ Syl_p(K₁ ⊓ K₂)` and hence `S = Q`, whence `|Ω_S| = |Ω_Q| ≥ 3` — contradicting
`|Ω_S| = 2`.  (In the source this is Ch. I §4 Lemma 2 part 1, proved through App. I (1), (3)(b)
and §2 Lemma 1, i.e. via `|u^P| ≥ n_p`; the normalizer condition
`Work.Coprime.lt_inf_normalizer_of_lt` is the alternative handle inside the `p`-group `S`.)
-/
theorem s4prop2_nofour {F : Type} [Group F] [Finite F]
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hA : Submission.Blueprint.ThmAProp)
    {K : Subgroup F} (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup F} (hQK : Q ≤ K)
    (hQp : IsPGroup p Q) (hQ3 : 3 ≤ (Submission.Blueprint.fixedPts K Q).ncard)
    (hQmax : ∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q)
    (hno4 : ¬ Submission.Blueprint.HasFourGroup F) :
    ∃ u : F, u ∈ K ∧ u ∈ Subgroup.normalizer (Q : Set F) ∧ orderOf u = 2 := by
  exact s4prop2_uniform hBrSz hK hp hp2 hQK hQp hQ3 hQmax

/-- **Peterfalvi I Ch. I §4 Prop. 2** (input): in a finite group `F` with a strongly embedded
subgroup `K`, a `p`-subgroup `Q ≤ K` (`p ≠ 2`) which is maximal among the `p`-subgroups of `K`
fixing at least three points of `F ⧸ K` is normalised by an involution of `K`.
(The case `HasFourGroup F` follows from `Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup`;
only the `2`-rank-`1` case is new.) -/
theorem s4prop2_input {F : Type} [Group F] [Finite F]
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hA : Submission.Blueprint.ThmAProp)
    {K : Subgroup F} (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup F} (hQK : Q ≤ K)
    (hQp : IsPGroup p Q) (hQ3 : 3 ≤ (Submission.Blueprint.fixedPts K Q).ncard)
    (hQmax : ∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) :
    ∃ u : F, u ∈ K ∧ u ∈ Subgroup.normalizer (Q : Set F) ∧ orderOf u = 2 :=
  s4prop2_uniform hBrSz hK hp hp2 hQK hQp hQ3 hQmax

/-- **The descent** (input): a finite solvable group `X ≠ ⊥` of odd order has a proper normal
subgroup `Y` with `X/Y` a `p`-group for an odd prime `p`, and a `p`-Sylow `P ≤ X` with
`Y ⊔ P = X`.  Immediately from `Work.ThreePoints.exists_descent_odd_solvable`, which produces
`Y ≠ X` in place of `|Y| < |X|`. -/
theorem descent_input {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : X ≠ ⊥) (hodd : Odd (Nat.card X)) (hsol : Group.IsSolvable ↥X) :
    ∃ (Y P : Subgroup G) (p : ℕ), Y ≤ X ∧ (Y.subgroupOf X).Normal ∧
      Nat.card Y < Nat.card X ∧ p.Prime ∧ p ≠ 2 ∧ IsPGroup p P ∧ P ≤ X ∧ Y ⊔ P = X := by
  obtain ⟨p, Y, P, hpp, hp2, hYX, hYN, hYne, hPp, hPX, hYP⟩ :=
    Work.ThreePoints.exists_descent_odd_solvable (X := X) hX hodd hsol
  exact ⟨Y, P, p, hYX, hYN, Subgroup.card_lt_of_lt (lt_of_le_of_ne hYX hYne),
    hpp, hp2, hPp, hPX, hYP⟩

/-- Peterfalvi I Ch. II §4 Prop. 1 (a) with the Brauer–Suzuki black box: under (B0)–(B2), if
the subgroup `X <= G` fixes at least three points of `Ω = G ⧸ H` and `M = H^g` is one of them
(`X ≤ M`), then `C_M(X)` has even order.
Avoid importing any module whose transitive closure still contains `hole`
(notably `Submission.Work.ThreePoints.prop1a_even_card_centralizer` and
`Submission.Work.ThreePoints.even_card_centralizer_of_fixes_three`): re-prove the needed
`prop1a_of_involution_normalizing` reduction directly. -/
theorem prop1a_brsz {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X M : Subgroup G}
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (hM : ∃ g : G, M = Submission.Blueprint.conj g H) (hXM : X ≤ M) :
    Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :=
  even_of_fixes_three_of_inputs
    ⟨fun {F} _ _ => s4prop2_input (F := F), fun {X} => descent_input (X := X)⟩
    hFT hC hA hBrSz hS hH hX3 hM hXM

end Work.ThreePoints.P3NeBot
