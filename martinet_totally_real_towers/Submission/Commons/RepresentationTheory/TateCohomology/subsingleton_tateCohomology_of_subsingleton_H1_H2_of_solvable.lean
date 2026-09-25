import Mathlib
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso
import Submission.Commons.RepresentationTheory.GroupCohomology.groupCohomology_subsingleton_of_isCyclic_of_H1_H2
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_tateCohomology_zero_cyclic
import Submission.Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1
import Submission.Commons.RepresentationTheory.GroupCohomology.norm_eq_quotient_norm_comp
import Submission.Commons.RepresentationTheory.GroupCohomology.range_infNatTrans_eq_ker_resNatTrans_of_subsingleton
import Submission.Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_neg_of_pos


namespace Commons.RepresentationTheory.TateCohomology

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory
open Commons.RepresentationTheory

attribute [local instance] Classical.propDecidable


/-! ## Piece 1: `Ĥ⁰` via invariants and norms -/

theorem subsingleton_tateCohomology_zero_of_invariants_le_range_norm
    {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℤ V]
    (ρ : Representation ℤ G V) (h : ρ.invariants ≤ LinearMap.range ρ.norm) :
    Subsingleton (tateCohomology (Rep.of ρ) 0) := by
  letI : Module ℤ ↥ρ.invariants := ρ.invariants.module
  obtain ⟨e⟩ := TateCohomology.tateCohomology_zero_iso ρ
  haveI : Subsingleton (↥ρ.invariants ⧸
      Submodule.comap ρ.invariants.subtype (LinearMap.range ρ.norm)) :=
    Submodule.Quotient.subsingleton_iff.2 (Submodule.comap_subtype_eq_top.2 h)
  exact ⟨fun a b => e.toEquiv.injective (Subsingleton.elim _ _)⟩

theorem invariants_le_range_norm_of_subsingleton_tateCohomology_zero
    {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℤ V]
    (ρ : Representation ℤ G V) (h : Subsingleton (tateCohomology (Rep.of ρ) 0)) :
    ρ.invariants ≤ LinearMap.range ρ.norm := by
  letI : Module ℤ ↥ρ.invariants := ρ.invariants.module
  obtain ⟨e⟩ := TateCohomology.tateCohomology_zero_iso ρ
  have hquot : Subsingleton (↥ρ.invariants ⧸
      Submodule.comap ρ.invariants.subtype (LinearMap.range ρ.norm)) :=
    ⟨fun a b => e.toEquiv.symm.injective <| Subsingleton.elim (e.toEquiv.symm a) (e.toEquiv.symm b)⟩
  exact Submodule.comap_subtype_eq_top.1 (Submodule.Quotient.subsingleton_iff.1 hquot)

/-! ## Piece 2: cyclic groups, positive degrees -/

theorem subsingleton_tateCohomology_zero_of_isCyclic_of_H2_rep
    {G V : Type} [Group G] [Fintype G] [IsCyclic G] [AddCommGroup V] [Module ℤ V]
    (ρ : Representation ℤ G V) (h2 : Subsingleton (groupCohomology (Rep.of ρ) 2)) :
    Subsingleton (tateCohomology (Rep.of ρ) 0) := by
  have hcard := GroupCohomology.natCard_groupCohomology_two_eq_tateCohomology_zero_cyclic ρ
  haveI : Subsingleton (groupCohomology (Rep.of ρ) 2) := h2
  haveI : Nonempty (groupCohomology (Rep.of ρ) 2) := ⟨0⟩
  have h1 : Nat.card ↑(groupCohomology (Rep.of ρ) 2) = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩
  rw [hcard] at h1
  exact (Nat.card_eq_one_iff_unique.1 h1).1

theorem subsingleton_tateCohomology_zero_of_isCyclic_of_H2 {G : Type} [Group G] [Fintype G]
    [IsCyclic G] (A : Rep ℤ G) (h2 : Subsingleton (groupCohomology A 2)) :
    Subsingleton (tateCohomology A 0) := by
  letI : Module ℤ A.V := A.hV2
  exact subsingleton_tateCohomology_zero_of_isCyclic_of_H2_rep A.ρ h2

/-! ## Piece 3: quotients -/

theorem subsingleton_groupCohomology_one_quotient {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    (A : Rep ℤ G) (h : Subsingleton (groupCohomology A 1)) :
    Subsingleton (groupCohomology (A.quotientToInvariants N) 1) := by
  haveI : Subsingleton (groupCohomology.H1InfRes A N).X₂ := h
  have hinj : Function.Injective (groupCohomology.H1InfRes A N).f.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact ⟨fun a b => hinj (Subsingleton.elim _ _)⟩

theorem subsingleton_groupCohomology_two_quotient {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    (A : Rep ℤ G) (hN : Subsingleton (groupCohomology (Rep.res N.subtype A) 1))
    (h : Subsingleton (groupCohomology A 2)) :
    Subsingleton (groupCohomology (A.quotientToInvariants N) 2) := by
  have hinj := GroupCohomology.H2_inflation_injective_of_subsingleton_H1 N A hN
  exact ⟨fun a b => hinj (h.elim _ _)⟩


/-! ## Piece 2b: positive vanishing for cyclic groups -/

theorem subsingleton_tateCohomology_of_isCyclic_of_H1_H2 {G : Type} [Group G] [Fintype G]
    [IsCyclic G] (A : Rep ℤ G) (h1 : Subsingleton (groupCohomology A 1))
    (h2 : Subsingleton (groupCohomology A 2)) :
    ∀ r : ℤ, 0 ≤ r → Subsingleton (tateCohomology A r) := by
  intro r hr
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
  cases n with
  | zero => exact subsingleton_tateCohomology_zero_of_isCyclic_of_H2 A h2
  | succ m =>
    haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
    have hsub := GroupCohomology.groupCohomology_subsingleton_of_isCyclic_of_H1_H2 A h1 h2 (m + 1)
      (by omega)
    refine ⟨fun a b => ?_⟩
    exact (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) (m + 1)).app A |>.toLinearEquiv.injective
      (hsub.elim _ _)

/-! ## Piece 4: `Ĥ⁰` in the induction step -/

theorem subsingleton_tateCohomology_zero_of_normal {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] [DecidablePred (· ∈ N)] (A : Rep ℤ G)
    (hN : Subsingleton (tateCohomology (Rep.res N.subtype A) 0))
    (hQ : Subsingleton (tateCohomology (A.quotientToInvariants N) 0)) :
    Subsingleton (tateCohomology A 0) := by
  classical
  letI : Module ℤ A.V := A.hV2
  letI : Module ℤ (A.quotientToInvariants N).V := (A.quotientToInvariants N).hV2
  letI : Module ℤ (Rep.res N.subtype A).V := (Rep.res N.subtype A).hV2
  refine subsingleton_tateCohomology_zero_of_invariants_le_range_norm A.ρ ?_
  intro z hzG
  have hzN : z ∈ (Rep.res N.subtype A).ρ.invariants :=
    fun n => (Representation.mem_invariants A.ρ z).1 hzG n.1
  let zQ : (A.quotientToInvariants N).V := ⟨z, hzN⟩
  have hzQinv : zQ ∈ (A.quotientToInvariants N).ρ.invariants := by
    rw [Representation.mem_invariants]
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      apply Subtype.ext
      show A.ρ g z = z
      exact (Representation.mem_invariants A.ρ z).1 hzG g
  have hGN := invariants_le_range_norm_of_subsingleton_tateCohomology_zero
      (A.quotientToInvariants N).ρ hQ
  obtain ⟨y, hy⟩ := hGN hzQinv
  have hNN := invariants_le_range_norm_of_subsingleton_tateCohomology_zero
      (Rep.res N.subtype A).ρ hN
  obtain ⟨w, hw⟩ := hNN y.2
  refine ⟨w, ?_⟩
  rw [GroupCohomology.norm_eq_quotient_norm_comp N A w]
  have h2 : (A.quotientToInvariants N).ρ.norm
      ⟨(Rep.res N.subtype A).ρ.norm w,
        (Representation.mem_invariants ((Rep.res N.subtype A).ρ) _).2
          (fun g => Representation.self_norm_apply (Rep.res N.subtype A).ρ g w)⟩ = zQ := by
    rw [← hy]
    exact congrArg _ (Subtype.ext hw)
  rw [h2]


/-! ## Piece 3b: transferring between Tate and group cohomology -/

theorem subsingleton_groupCohomology_of_subsingleton_tateCohomology {G : Type} [Group G] [Fintype G]
    (A : Rep ℤ G) (n : ℕ) [NeZero n] (h : Subsingleton (tateCohomology A (n : ℤ))) :
    Subsingleton (groupCohomology A n) := by
  have e := (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) n).app A |>.toLinearEquiv
  exact ⟨fun a b => e.symm.injective (h.elim (e.symm a) (e.symm b))⟩

theorem subsingleton_tateCohomology_of_subsingleton_groupCohomology {G : Type} [Group G] [Fintype G]
    (A : Rep ℤ G) (n : ℕ) [NeZero n] (h : Subsingleton (groupCohomology A n)) :
    Subsingleton (tateCohomology A (n : ℤ)) := by
  have e := (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) n).app A |>.toLinearEquiv
  exact ⟨fun a b => e.injective (h.elim (e a) (e b))⟩

/-! ## Piece 5: positive vanishing from a normal subgroup -/

theorem subsingleton_tateCohomology_of_normal {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] [DecidablePred (· ∈ N)] (A : Rep ℤ G)
    (hN : ∀ r : ℤ, 0 ≤ r → Subsingleton (tateCohomology (Rep.res N.subtype A) r))
    (hQ : ∀ r : ℤ, 0 ≤ r → Subsingleton (tateCohomology (A.quotientToInvariants N) r))
    (h1 : Subsingleton (groupCohomology A 1))
    (h2 : Subsingleton (groupCohomology A 2)) :
    ∀ r : ℤ, 0 ≤ r → Subsingleton (tateCohomology A r) := by
  intro r hr
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
  cases n with
  | zero => exact subsingleton_tateCohomology_zero_of_normal N A (hN 0 le_rfl) (hQ 0 le_rfl)
  | succ m =>
    have hQt : Subsingleton (tateCohomology (A.quotientToInvariants N) ((m + 1 : ℕ) : ℤ)) :=
      hQ ((m + 1 : ℕ) : ℤ) (by positivity)
    have hNt : Subsingleton (tateCohomology (Rep.res N.subtype A) ((m + 1 : ℕ) : ℤ)) :=
      hN ((m + 1 : ℕ) : ℤ) (by positivity)
    have hQn : Subsingleton (groupCohomology (A.quotientToInvariants N) (m + 1)) :=
      subsingleton_groupCohomology_of_subsingleton_tateCohomology _ (m + 1) hQt
    have hNn : Subsingleton (groupCohomology (Rep.res N.subtype A) (m + 1)) :=
      subsingleton_groupCohomology_of_subsingleton_tateCohomology _ (m + 1) hNt
    have hGA : Subsingleton (groupCohomology A (m + 1)) := by
      cases m with
      | zero => exact h1
      | succ k =>
        have hNR : ∀ j, 0 < j → j < k + 2 →
            Subsingleton (groupCohomology (Rep.res N.subtype A) j) := by
          intro j hj _
          haveI : NeZero j := ⟨hj.ne'⟩
          exact subsingleton_groupCohomology_of_subsingleton_tateCohomology _ j (hN j (by positivity))
        have hex := GroupCohomology.range_infNatTrans_eq_ker_resNatTrans_of_subsingleton
          (k := ℤ) N (A := A) (r := k + 2) (by omega) hNR
        have hsurj : Function.Surjective
            ((groupCohomology.infNatTrans ℤ N (k + 2)).app A).hom := by
          intro x
          have hx : ((groupCohomology.resNatTrans ℤ (G := N) (H := G) N.subtype (k + 2)).app A).hom x
              = 0 := hNn.elim _ _
          have hxk : x ∈ LinearMap.ker ((groupCohomology.resNatTrans ℤ (G := N) (H := G)
              N.subtype (k + 2)).app A).hom := hx
          rw [← hex] at hxk
          exact hxk
        refine ⟨fun a b => ?_⟩
        obtain ⟨a', rfl⟩ := hsurj a
        obtain ⟨b', rfl⟩ := hsurj b
        rw [hQn.elim a' b']
    exact subsingleton_tateCohomology_of_subsingleton_groupCohomology _ (m + 1) hGA


section Main

variable {G : Type} [Group G] [Fintype G]

/-- The hypotheses of the main theorem. -/
abbrev Hyp (A : Rep ℤ G) : Prop :=
  ∀ H : Subgroup G, Subsingleton (groupCohomology (Rep.res H.subtype A) 1) ∧
      Subsingleton (groupCohomology (Rep.res H.subtype A) 2)

/-- Cohomology of a restricted representation only depends on the image subgroup. -/
theorem groupCohomology_res_iso_range {k : Type} [CommRing k] {G H : Type} [Group G] [Group H]
    (f : H →* G) (hf : Function.Injective f) (A : Rep k G) (m : ℕ) :
    Nonempty (groupCohomology (Rep.res f A) m ≅ groupCohomology (Rep.res f.range.subtype A) m) := by
  refine ⟨?_⟩
  let e : H ≃* ↥f.range := MonoidHom.ofInjective hf
  refine groupCohomology.mapIso (k := k) (G := H) (H := ↥f.range)
    (B := Rep.res f A) (A := Rep.res f.range.subtype A) e ?_ ?_ m
  · exact LinearEquiv.refl k A.V
  · intro g
    ext x
    show (((Rep.res f A).ρ) g) x = (((Rep.res f.range.subtype A).ρ) (e g)) x
    simp [e, MonoidHom.ofInjective_apply]

/-- The hypotheses pass to a subgroup. -/
theorem hyp_restrict (N : Subgroup G) (A : Rep ℤ G) (hA : Hyp (G := G) A) :
    ∀ K : Subgroup ↥N,
      Subsingleton (groupCohomology (Rep.res K.subtype (Rep.res N.subtype A)) 1) ∧
      Subsingleton (groupCohomology (Rep.res K.subtype (Rep.res N.subtype A)) 2) := by
  have hmain : ∀ (m : ℕ) (K : Subgroup ↥N),
      Subsingleton (groupCohomology (Rep.res (K.map N.subtype).subtype A) m) →
      Subsingleton (groupCohomology (Rep.res K.subtype (Rep.res N.subtype A)) m) := by
    intro m K h
    let f : ↥K →* G := N.subtype.comp K.subtype
    have hf : Function.Injective f := fun a b hab => Subtype.ext (N.subtype_injective hab)
    have hrange : f.range = K.map N.subtype := by
      ext y; constructor
      · rintro ⟨k, rfl⟩; exact ⟨k.1, k.2, rfl⟩
      · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, hk⟩, rfl⟩
    obtain ⟨e⟩ := groupCohomology_res_iso_range (k := ℤ) f hf A m
    have hsub : Subsingleton (groupCohomology (Rep.res f.range.subtype A) m) := by
      rwa [hrange]
    exact ⟨fun a b => e.toLinearEquiv.injective
      (hsub.elim (e.toLinearEquiv a) (e.toLinearEquiv b))⟩
  intro K
  exact ⟨hmain 1 K (hA (K.map N.subtype)).1, hmain 2 K (hA (K.map N.subtype)).2⟩

end Main


theorem exists_maximal_normal_of_not_isCyclic {G : Type} [Group G] [Fintype G]
    [Group.IsSolvable G] (h : ¬ IsCyclic G) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧ (∀ M : Subgroup G, M.Normal → N < M → M = ⊤) := by
  classical
  have hnt : Nontrivial G := by
    by_contra h'
    haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp h'
    exact h (isCyclic_of_subsingleton (α := G))
  have hbot : (⊥ : Subgroup G) ≠ ⊤ := by
    intro hb
    obtain ⟨a, b, hab⟩ := exists_pair_ne G
    have ha : a = 1 := by
      have : a ∈ (⊥ : Subgroup G) := by rw [hb]; trivial
      simpa using this
    have hb' : b = 1 := by
      have : b ∈ (⊥ : Subgroup G) := by rw [hb]; trivial
      simpa using this
    exact hab (ha.trans hb'.symm)
  have hne : (Finset.univ.filter (fun N : Subgroup G => N.Normal ∧ N ≠ ⊤)).Nonempty :=
    ⟨⊥, by simp [Subgroup.normal_bot, hbot]⟩
  obtain ⟨N, hNmax⟩ :=
    Finset.exists_maximal (s := Finset.univ.filter (fun N : Subgroup G => N.Normal ∧ N ≠ ⊤)) hne
  have hNS : N.Normal ∧ N ≠ ⊤ := by
    simpa using hNmax.1
  exact ⟨N, hNS.1, hNS.2, fun M hM hNM => by
    by_contra hMt
    have hMem : M ∈ Finset.univ.filter (fun N : Subgroup G => N.Normal ∧ N ≠ ⊤) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hM, hMt⟩
    exact absurd (hNmax.2 hMem hNM.le) (not_le_of_gt hNM)⟩

theorem isCyclic_quotient_of_maximal_normal {G : Type} [Group G] [Group.IsSolvable G]
    (N : Subgroup G) [N.Normal] (hmax : ∀ M : Subgroup G, M.Normal → N < M → M = ⊤) :
    IsCyclic (G ⧸ N) := by
  classical
  by_cases hNtop : N = ⊤
  · haveI : Subsingleton (G ⧸ N) := QuotientGroup.subsingleton_iff.mpr hNtop
    exact isCyclic_of_subsingleton (α := G ⧸ N)
  · haveI : Nontrivial (G ⧸ N) :=
      not_subsingleton_iff_nontrivial.mp fun hs => hNtop (QuotientGroup.subsingleton_iff.mp hs)
    have hsimple : ∀ L : Subgroup (G ⧸ N), L.Normal → L = ⊥ ∨ L = ⊤ := by
      intro L hL
      have hMnorm : (L.comap (QuotientGroup.mk' N)).Normal := hL.comap (QuotientGroup.mk' N)
      have hle : N ≤ L.comap (QuotientGroup.mk' N) := fun n hn => by
        rw [Subgroup.mem_comap]
        rw [show (QuotientGroup.mk' N) n = 1 from (QuotientGroup.eq_one_iff n).2 hn]
        exact L.one_mem
      have hmap : Subgroup.map (QuotientGroup.mk' N) (L.comap (QuotientGroup.mk' N)) = L :=
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) L
      rcases eq_or_lt_of_le hle with heq | hlt
      · left
        rw [← hmap, ← heq, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      · right
        rw [← hmap, hmax _ hMnorm hlt,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    have hcomm : ∀ a b : G ⧸ N, a * b = b * a := by
      by_contra hc
      push Not at hc
      obtain ⟨a, b, hab⟩ := hc
      have hbot : commutator (G ⧸ N) ≠ ⊥ := fun hb =>
        hab (((commutator_eq_bot_iff (G ⧸ N)).mp hb).is_comm.comm a b)
      have htop : commutator (G ⧸ N) ≠ ⊤ :=
        ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial (G ⧸ N))
      rcases hsimple _ (inferInstance : (commutator (G ⧸ N)).Normal) with h1 | h2
      · exact hbot h1
      · exact htop h2
    obtain ⟨g, hg⟩ := exists_ne (1 : G ⧸ N)
    have hnormal : (Subgroup.zpowers g).Normal := by
      refine ⟨fun n hn x => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hconj : x * g ^ k * x⁻¹ = g ^ k := by
        rw [hcomm x (g ^ k)]
        simp
      rw [hconj]
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
    rcases hsimple _ hnormal with h1 | h2
    · exfalso
      apply hg
      have hmem : g ∈ Subgroup.zpowers g := Subgroup.mem_zpowers g
      rw [h1] at hmem
      simpa using hmem
    · exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, h2⟩


/-- Restriction to the whole group does not change group cohomology. -/
theorem groupCohomology_top_iso {k : Type} [CommRing k] {G : Type} [Group G] (A : Rep k G) (m : ℕ) :
    Nonempty (groupCohomology (Rep.res (⊤ : Subgroup G).subtype A) m ≅ groupCohomology A m) := by
  refine ⟨?_⟩
  refine groupCohomology.mapIso (k := k) (G := ↥(⊤ : Subgroup G)) (H := G)
    (B := Rep.res (⊤ : Subgroup G).subtype A) (A := A) (Subgroup.topEquiv) ?_ ?_ m
  · exact LinearEquiv.refl k A.V
  · intro g
    ext x
    show (((Rep.res (⊤ : Subgroup G).subtype A).ρ) g) x = (A.ρ (Subgroup.topEquiv g)) x
    rw [Subgroup.topEquiv_apply]
    rfl

/-- A `Subsingleton` statement for the restriction to `⊤` transfers to the group itself. -/
theorem subsingleton_groupCohomology_top {k : Type} [CommRing k] {G : Type} [Group G]
    (A : Rep k G) (m : ℕ)
    (h : Subsingleton (groupCohomology (Rep.res (⊤ : Subgroup G).subtype A) m)) :
    Subsingleton (groupCohomology A m) := by
  obtain ⟨e⟩ := groupCohomology_top_iso A m
  exact ⟨fun a b => (e.toLinearEquiv.symm).injective
    (h.elim (e.toLinearEquiv.symm a) (e.toLinearEquiv.symm b))⟩

theorem positive_vanishing_aux : ∀ (n : ℕ) (G : Type) [Group G] [Fintype G] [Group.IsSolvable G],
    Fintype.card G = n → ∀ (A : Rep ℤ G), Hyp (G := G) A →
      ∀ r : ℤ, 0 ≤ r → Subsingleton (tateCohomology A r) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ _ hcard A hA r hr
    by_cases hcyc : IsCyclic G
    · exact subsingleton_tateCohomology_of_isCyclic_of_H1_H2 A
        (subsingleton_groupCohomology_top A 1 (hA ⊤).1)
        (subsingleton_groupCohomology_top A 2 (hA ⊤).2) r hr
    · classical
      obtain ⟨N, hNnorm, hNtop, hNmax⟩ := exists_maximal_normal_of_not_isCyclic (G := G) hcyc
      haveI : N.Normal := hNnorm
      have hcardN : Fintype.card ↥N < n := by
        have hxN : ∃ x : G, x ∉ N := by
          by_contra h
          push Not at h
          exact hNtop (le_antisymm le_top fun y _ => h y)
        obtain ⟨x, hx⟩ := hxN
        have := Fintype.card_subtype_lt (p := fun y : G => y ∈ N) hx
        omega
      have hNpos : ∀ r : ℤ, 0 ≤ r → Subsingleton (tateCohomology (Rep.res N.subtype A) r) :=
        ih (Fintype.card ↥N) hcardN ↥N rfl (Rep.res N.subtype A) (hyp_restrict N A hA)
      haveI : IsCyclic (G ⧸ N) := isCyclic_quotient_of_maximal_normal N hNmax
      have hN1 : Subsingleton (groupCohomology (Rep.res N.subtype A) 1) :=
        subsingleton_groupCohomology_of_subsingleton_tateCohomology _ 1 (hNpos 1 (by norm_num))
      have hA1 : Subsingleton (groupCohomology A 1) := subsingleton_groupCohomology_top A 1 (hA ⊤).1
      have hA2 : Subsingleton (groupCohomology A 2) := subsingleton_groupCohomology_top A 2 (hA ⊤).2
      have hq1 : Subsingleton (groupCohomology (A.quotientToInvariants N) 1) :=
        subsingleton_groupCohomology_one_quotient N A hA1
      have hq2 : Subsingleton (groupCohomology (A.quotientToInvariants N) 2) :=
        subsingleton_groupCohomology_two_quotient N A hN1 hA2
      have hQpos : ∀ r : ℤ, 0 ≤ r → Subsingleton (tateCohomology (A.quotientToInvariants N) r) :=
        subsingleton_tateCohomology_of_isCyclic_of_H1_H2 (A.quotientToInvariants N) hq1 hq2
      exact subsingleton_tateCohomology_of_normal N A hNpos hQpos hA1 hA2 r hr

open Commons.RepresentationTheory.TateCohomology in
/-- Negative degrees, using only the positive-degree vanishing for solvable groups. -/
theorem neg_of_solvable {G : Type} [Group G] [Fintype G] [Group.IsSolvable G] (A : Rep ℤ G)
    (hpos : ∀ (K : Type) [Group K] [Fintype K] [Group.IsSolvable K] (B : Rep ℤ K),
        (∀ H : Subgroup K, Subsingleton (groupCohomology (Rep.res H.subtype B) 1) ∧
          Subsingleton (groupCohomology (Rep.res H.subtype B) 2)) →
        ∀ r : ℤ, 0 ≤ r → Subsingleton (tateCohomology B r))
    (hA : ∀ H : Subgroup G, Subsingleton (groupCohomology (Rep.res H.subtype A) 1) ∧
        Subsingleton (groupCohomology (Rep.res H.subtype A) 2)) :
    ∀ r : ℤ, r < 0 → Subsingleton (tateCohomology A r) := by
  classical
  have hPA : PosTateVanishing A := by
    intro H r hr
    refine hpos ↥H (Rep.res H.subtype A) ?_ r hr
    intro H'
    obtain ⟨e1⟩ := groupCohomology_res_res_iso H H' A 1
    obtain ⟨e2⟩ := groupCohomology_res_res_iso H H' A 2
    obtain ⟨h1, h2⟩ := hA (H'.map H.subtype)
    exact ⟨e1.toLinearEquiv.injective.subsingleton, e2.toLinearEquiv.injective.subsingleton⟩
  have main : ∀ n : ℕ, 1 ≤ n → ∀ (B : Rep ℤ G), PosTateVanishing B →
      Subsingleton (tateCohomology B (-(n : ℤ))) ∧
        ∀ H : Subgroup G, Subsingleton (tateCohomology (Rep.res H.subtype B) (-(n : ℤ))) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn B hB
      rcases (by omega : n = 1 ∨ 2 ≤ n) with hn1 | hn2
      · subst hn1
        constructor
        · obtain ⟨e⟩ := acyclicShortComplex_shift_up B (-1)
          rw [show (-1 : ℤ) + 1 = 0 from by norm_num] at e
          haveI : Subsingleton (tateCohomology (acyclicShortComplex B).X₁ 0) :=
            hpos G (acyclicShortComplex B).X₁
              (fun H => subsingleton_groupCohomology_kernel_one_two hB H) 0 le_rfl
          exact e.injective.subsingleton
        · intro H
          obtain ⟨e⟩ := acyclicShortComplex_shift_restrict_up B H (-1)
          rw [show (-1 : ℤ) + 1 = 0 from by norm_num] at e
          haveI : Subsingleton (tateCohomology (Rep.res H.subtype (acyclicShortComplex B).X₁) 0) :=
            hpos ↥H (Rep.res H.subtype (acyclicShortComplex B).X₁) (fun H' => ?_) 0 le_rfl
          · exact e.injective.subsingleton
          · obtain ⟨e1⟩ := groupCohomology_res_res_iso H H' (acyclicShortComplex B).X₁ 1
            obtain ⟨e2⟩ := groupCohomology_res_res_iso H H' (acyclicShortComplex B).X₁ 2
            obtain ⟨h1, h2⟩ := subsingleton_groupCohomology_kernel_one_two hB (H'.map H.subtype)
            exact ⟨e1.toLinearEquiv.injective.subsingleton,
              e2.toLinearEquiv.injective.subsingleton⟩
      · have hneg : ∀ H : Subgroup G,
            Subsingleton (tateCohomology (Rep.res H.subtype B) (-1)) := by
          intro H
          have h1 := (ih 1 (by omega) (by omega) B hB).2 H
          simpa using h1
        have hD : PosTateVanishing (acyclicShortComplex B).X₁ := posTateVanishing_kernel hB hneg
        constructor
        · obtain ⟨e⟩ := acyclicShortComplex_shift_up B (-(n : ℤ))
          rw [show -(n : ℤ) + 1 = -(((n - 1 : ℕ)) : ℤ) from by omega] at e
          haveI : Subsingleton (tateCohomology (acyclicShortComplex B).X₁
              (-((n - 1 : ℕ) : ℤ))) := (ih (n - 1) (by omega) (by omega) _ hD).1
          exact e.injective.subsingleton
        · intro H
          obtain ⟨e⟩ := acyclicShortComplex_shift_restrict_up B H (-(n : ℤ))
          rw [show -(n : ℤ) + 1 = -(((n - 1 : ℕ)) : ℤ) from by omega] at e
          haveI : Subsingleton (tateCohomology
              (Rep.res H.subtype (acyclicShortComplex B).X₁) (-((n - 1 : ℕ) : ℤ))) :=
            (ih (n - 1) (by omega) (by omega) _ hD).2 H
          exact e.injective.subsingleton
  intro r hr
  have hrepr : r = -(((-r).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  rw [hrepr]
  exact (main ((-r).toNat) (by omega) A hPA).1

/-- **Cohomologically trivial modules (Milne, Class Field Theory, II.3.10), solvable case.** Let `A` be a `ℤ`-linear representation of a finite solvable group `G` such that `H¹(H,A) = 0` and `H²(H,A) = 0` for every subgroup `H ≤ G`. Then the Tate cohomology of `A` vanishes in every degree: `Ĥ^r(G,A) = 0` for all `r`. -/
theorem subsingleton_tateCohomology_of_subsingleton_H1_H2_of_solvable
    {G : Type} [Group G] [Fintype G] [Group.IsSolvable G] (A : Rep ℤ G)
    (h : ∀ H : Subgroup G, Subsingleton (groupCohomology (Rep.res H.subtype A) 1) ∧
        Subsingleton (groupCohomology (Rep.res H.subtype A) 2)) :
    ∀ r : ℤ, Subsingleton (tateCohomology A r) := by
  intro r
  by_cases hr : 0 ≤ r
  · exact positive_vanishing_aux (Fintype.card G) G rfl A h r hr
  · push Not at hr
    exact neg_of_solvable A
      (fun K _ _ _ B hB => positive_vanishing_aux (Fintype.card K) K rfl B hB) h r hr


end Commons.RepresentationTheory.TateCohomology
