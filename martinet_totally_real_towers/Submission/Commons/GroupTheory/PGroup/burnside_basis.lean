import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Frattini
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.GroupTheory.PGroup.index_coatom_eq_prime

open scoped IsMulCommutative

namespace Commons.GroupTheory.PGroup

open Subgroup

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- In a finite `p`-group the derived subgroup is contained in the Frattini subgroup: every
maximal subgroup has index `p`, hence has abelian quotient. -/
private lemma commutator_le_frattini {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) : commutator G ≤ frattini G := by
  rw [frattini, Order.radical]
  refine le_iInf fun M => le_iInf fun hM => ?_
  haveI : Group.IsNilpotent G := hG.isNilpotent
  haveI hMn : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M
      (Group.normalizerCondition_of_isNilpotent (G := G)) hM
  have hcard : Nat.card (G ⧸ M) = p := by
    rw [← Subgroup.index_eq_card]
    exact index_coatom_eq_prime hG hM
  haveI hcomm : IsMulCommutative (G ⧸ M) := (isCyclic_of_prime_card hcard).isMulCommutative
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := M)).mp hcomm

/-- In a finite `p`-group, every `p`-th power lies in the Frattini subgroup. -/
private lemma pow_mem_frattini {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) (g : G) : g ^ p ∈ frattini G := by
  rw [frattini, Order.radical]
  refine Subgroup.mem_iInf.mpr fun M => Subgroup.mem_iInf.mpr fun hM => ?_
  haveI : Group.IsNilpotent G := hG.isNilpotent
  haveI hMn : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M
      (Group.normalizerCondition_of_isNilpotent (G := G)) hM
  have hcard : Nat.card (G ⧸ M) = p := by
    rw [← Subgroup.index_eq_card]
    exact index_coatom_eq_prime hG hM
  have h1 : ((g : G ⧸ M)) ^ p = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  exact (QuotientGroup.eq_one_iff (g ^ p)).mp (by rw [QuotientGroup.mk_pow]; exact h1)

/-- In a `ZMod n`-module, the submodule span and the additive subgroup closure of a
set have the same top element: every additive subgroup is a `ZMod n`-submodule. -/
private lemma span_eq_top_iff_closure_eq_top {n : ℕ} {V : Type*} [AddCommGroup V]
    [Module (ZMod n) V] (s : Set V) :
    Submodule.span (ZMod n) s = ⊤ ↔ AddSubgroup.closure s = ⊤ := by
  have hle : Submodule.span (ZMod n) s ≤ AddSubgroup.toZModSubmodule n (AddSubgroup.closure s) :=
    Submodule.span_le.mpr (fun x hx => AddSubgroup.subset_closure hx)
  have hle2 : AddSubgroup.closure s ≤ Submodule.toAddSubgroup (Submodule.span (ZMod n) s) :=
    (AddSubgroup.closure_le _).mpr (fun x hx => Submodule.subset_span hx)
  constructor
  · intro h
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span (ZMod n) s := by rw [h]; trivial
    simpa using hle hx
  · intro h
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ AddSubgroup.closure s := by rw [h]; trivial
    exact hle2 hx

/-- Group generation of `Q` is the same as additive generation of `Additive Q`. -/
private lemma subgroup_closure_eq_top_iff_additive {Q : Type*} [Group Q] (s : Set Q) :
    Subgroup.closure s = ⊤ ↔ AddSubgroup.closure (Additive.ofMul '' s) = ⊤ := by
  have hpre : Additive.toMul ⁻¹' s = Additive.ofMul '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨x.toMul, hx, ofMul_toMul x⟩
    · rintro ⟨g, hg, rfl⟩
      simpa using hg
  rw [← hpre, ← Subgroup.toAddSubgroup_closure s]
  constructor
  · intro h
    rw [h]
    exact OrderIso.map_top _
  · intro h
    refine Subgroup.toAddSubgroup.injective ?_
    rw [h]
    exact (OrderIso.map_top _).symm

/-- **Burnside's basis theorem**, minimal-generating-set form: a finite `p`-group `G` has a
generating set `S` whose cardinality equals `log_p |G/Φ(G)|`, and every generating set of `G`
has at least that many elements. -/
theorem burnside_basis {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) :
    ∃ S : Finset G, Nat.card (G ⧸ frattini G) = p ^ S.card ∧
      Subgroup.closure (S : Set G) = ⊤ ∧
      ∀ T : Finset G, Subgroup.closure (T : Set G) = ⊤ → S.card ≤ T.card := by
  classical
  -- `G ⧸ Φ(G)` is an elementary abelian `p`-group.
  have hQcomm : IsMulCommutative (G ⧸ frattini G) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := frattini G)).mpr
      (commutator_le_frattini hG)
  haveI : IsMulCommutative (G ⧸ frattini G) := hQcomm
  have hQexp : ∀ x : G ⧸ frattini G, x ^ p = 1 := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (frattini G) x
    rw [← map_pow, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (g ^ p)).mpr (pow_mem_frattini hG g)
  -- view `G ⧸ Φ(G)` as a vector space over `ZMod p`.
  let V := Additive (G ⧸ frattini G)
  have hpV : ∀ x : V, p • x = 0 := by
    intro x
    rw [← ofMul_toMul x]
    rw [← ofMul_pow, hQexp, ofMul_one]
  haveI hmod : Module (ZMod p) V := AddCommGroup.zmodModule hpV
  have hZModcard : Nat.card (ZMod p) = p := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hcardV : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := V), hZModcard]
  have hVQ : Nat.card V = Nat.card (G ⧸ frattini G) := Nat.card_congr Additive.ofMul
  -- a basis of the vector space
  have hb := Module.finBasis (ZMod p) V
  have hclosV : AddSubgroup.closure (Set.range hb) = ⊤ :=
    (span_eq_top_iff_closure_eq_top (Set.range hb)).mp hb.span_eq
  have hclosQ : Subgroup.closure (Set.range (fun i => (hb i).toMul)) = ⊤ := by
    have h1 := AddSubgroup.toSubgroup'_closure (Set.range hb)
    rw [hclosV, OrderIso.map_top] at h1
    have hpre : Additive.ofMul ⁻¹' Set.range hb = Set.range (fun i => (hb i).toMul) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_range]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, (congrArg Additive.toMul hi).trans (toMul_ofMul x)⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, by rw [← hi]; exact (ofMul_toMul (hb i)).symm⟩
    rw [hpre] at h1
    exact h1.symm
  -- lift the basis to elements of `G`
  choose g hg using fun i => QuotientGroup.mk'_surjective (frattini G) ((hb i).toMul)
  have hgenQ : Subgroup.closure
      ((QuotientGroup.mk' (frattini G)) '' Set.range g) = ⊤ := by
    have hrange : (QuotientGroup.mk' (frattini G)) '' Set.range g =
        Set.range (fun i => (hb i).toMul) := by
      ext y
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, hxy⟩
        exact ⟨i, (hg i).symm.trans hxy⟩
      · rintro ⟨i, hi⟩
        exact ⟨g i, ⟨i, rfl⟩, (hg i).trans hi⟩
    rw [hrange]
    exact hclosQ
  -- the lifted elements generate `G`, by the Frattini non-generator property
  have hgenG : Subgroup.closure (Set.range g) = ⊤ := by
    have hmap : Subgroup.map (QuotientGroup.mk' (frattini G))
        (Subgroup.closure (Set.range g)) = ⊤ := by
      rw [MonoidHom.map_closure, hgenQ]
    have hsup : Subgroup.closure (Set.range g) ⊔ frattini G = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : (QuotientGroup.mk' (frattini G)) x ∈
          Subgroup.map (QuotientGroup.mk' (frattini G)) (Subgroup.closure (Set.range g)) := by
        rw [hmap]; trivial
      rw [Subgroup.mem_map] at hx
      obtain ⟨h, hh, hhx⟩ := hx
      have hmem : h⁻¹ * x ∈ frattini G := by
        rw [← QuotientGroup.ker_mk' (frattini G), MonoidHom.mem_ker, map_mul, map_inv, hhx,
          inv_mul_cancel]
      rw [Subgroup.mem_sup_of_normal_right]
      exact ⟨h, hh, h⁻¹ * x, hmem, by group⟩
    exact frattini_nongenerating hsup
  -- the counting bound: any generating set of `G` has at least `finrank` elements
  have hbound : ∀ T : Finset G, Subgroup.closure (T : Set G) = ⊤ →
      Module.finrank (ZMod p) V ≤ T.card := by
    intro T hT
    have hTQ : Subgroup.closure ((QuotientGroup.mk' (frattini G)) '' (T : Set G)) = ⊤ := by
      rw [← MonoidHom.map_closure, hT]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    have hTspan : Submodule.span (ZMod p)
        (Additive.ofMul '' ((QuotientGroup.mk' (frattini G)) '' (T : Set G))) = ⊤ :=
      (span_eq_top_iff_closure_eq_top (n := p) (V := V) _).mpr
        ((subgroup_closure_eq_top_iff_additive _).mp hTQ)
    have hrange : Set.range (fun x : ↥T =>
          Additive.ofMul ((QuotientGroup.mk' (frattini G)) (x : G))) =
        Additive.ofMul '' ((QuotientGroup.mk' (frattini G)) '' (T : Set G)) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨_, ⟨x, x.2, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    have hfin := finrank_le_of_span_eq_top (R := ZMod p)
      (v := fun x : ↥T => Additive.ofMul ((QuotientGroup.mk' (frattini G)) (x : G)))
      (by rw [hrange]; exact hTspan)
    simpa [Fintype.card_coe] using hfin
  have hSle : (Finset.univ.image g).card ≤ Module.finrank (ZMod p) V := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin (Module.finrank (ZMod p) V)))) (f := g)
  have hgenS : Subgroup.closure ((Finset.univ.image g : Finset G) : Set G) = ⊤ := by
    simpa using hgenG
  have hSeq : (Finset.univ.image g).card = Module.finrank (ZMod p) V :=
    le_antisymm hSle (hbound _ hgenS)
  exact ⟨Finset.univ.image g, by rw [hSeq, ← hVQ, hcardV], hgenS, fun T hT => by
    rw [hSeq]; exact hbound T hT⟩

end Commons.GroupTheory.PGroup