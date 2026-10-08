import Mathlib
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The number of elements in the union of the conjugates of a TI subgroup

Let `S ≤ G` be a subgroup such that distinct conjugates of `S` meet trivially, in the form used
by the challenge (`IsStronglyEmbedded`): for every `g ∉ N_G(S)` one has `S ⊓ conj g S = ⊥`.
Then the union of *all* conjugates of `S` consists of the identity together with the non-identity
elements of the `[G : N_G(S)]` distinct conjugates, whence

`(⋃ g, conj g S).ncard = 1 + (Subgroup.normalizer S).index * (Nat.card S - 1)`.

The proof has three ingredients.
* `iUnion_conj_eq_iUnion_quotient`: the union over `G` equals the union over the coset
  representatives `Quotient.out q`, `q : G ⧸ N_G(S)` (one conjugate per coset).
* `pairwiseDisjoint_conj_sdiff_one`: two distinct conjugates meet only in `1` (this is the TI
  hypothesis, packaged through `conj_inv_mul_mem_normalizer`), so their punctured versions are
  disjoint.
* counting: `⋃ q, C q = insert 1 (⋃ q, C q \ {1})`, and the punctured union is the disjoint
  union of `[G : N_G(S)]` sets each of size `|S| - 1`.
-/

namespace Work.ZassenhausSuzuki

/-- If a non-identity element `x` lies in two conjugates of the TI subgroup `S`, then the two
conjugating elements differ by an element of the normaliser `N_G(S)`. -/
theorem conj_inv_mul_mem_normalizer {G : Type} [Group G] {S : Subgroup G}
    (hTI : ∀ g : G, g ∉ Subgroup.normalizer (S : Set G) →
      S ⊓ Submission.Blueprint.conj g S = ⊥)
    {x a b : G} (hx : x ≠ 1) (ha : x ∈ Submission.Blueprint.conj a S)
    (hb : x ∈ Submission.Blueprint.conj b S) :
    a⁻¹ * b ∈ Subgroup.normalizer (S : Set G) := by
  by_contra h
  have hu : a⁻¹ * x * a ∈ S := Work.Models.mem_conj_iff.mp ha
  have hv : b⁻¹ * x * b ∈ S := Work.Models.mem_conj_iff.mp hb
  have hu' : a⁻¹ * x * a ∈ Submission.Blueprint.conj (a⁻¹ * b) S := by
    rw [Work.Models.mem_conj_iff]
    have h1 : (a⁻¹ * b)⁻¹ * (a⁻¹ * x * a) * (a⁻¹ * b) = b⁻¹ * x * b := by group
    rw [h1]
    exact hv
  have hm : a⁻¹ * x * a ∈ S ⊓ Submission.Blueprint.conj (a⁻¹ * b) S := ⟨hu, hu'⟩
  rw [hTI (a⁻¹ * b) h] at hm
  have h1 : a⁻¹ * x * a = 1 := by simpa using hm
  refine hx ?_
  have h2 : x = a * (a⁻¹ * x * a) * a⁻¹ := by group
  rw [h2, h1]
  group

/-- The conjugates of `S` are exactly the conjugates of the coset representatives of `N_G(S)`:
the union over `G` coincides with the union over `G ⧸ N_G(S)`. -/
theorem iUnion_conj_eq_iUnion_quotient {G : Type} [Group G] (S : Subgroup G) :
    (⋃ g : G, (Submission.Blueprint.conj g S : Set G)) =
      ⋃ q : G ⧸ Subgroup.normalizer (S : Set G),
        (Submission.Blueprint.conj (Quotient.out q) S : Set G) := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨g, hx⟩
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.normalizer (S : Set G)) g
    have hthis : Submission.Blueprint.conj
          (Quotient.out ((g : G ⧸ Subgroup.normalizer (S : Set G)))) S
        = Submission.Blueprint.conj g S := by
      rw [hn, Work.Models.conj_mul, Work.Models.conj_self_of_mem_normalizer n.2]
    exact ⟨((g : G ⧸ Subgroup.normalizer (S : Set G))), by rw [hthis]; exact hx⟩
  · rintro ⟨q, hx⟩
    exact ⟨Quotient.out q, hx⟩

/-- The punctured conjugates of a TI subgroup, indexed by the cosets of `N_G(S)`, are pairwise
disjoint. -/
theorem pairwiseDisjoint_conj_sdiff_one {G : Type} [Group G] (S : Subgroup G)
    (hTI : ∀ g : G, g ∉ Subgroup.normalizer (S : Set G) →
      S ⊓ Submission.Blueprint.conj g S = ⊥) :
    Pairwise (Function.onFun Disjoint fun q : G ⧸ Subgroup.normalizer (S : Set G) =>
      ((Submission.Blueprint.conj (Quotient.out q) S : Set G) \ {1})) := by
  intro q q' hne
  show Disjoint ((Submission.Blueprint.conj (Quotient.out q) S : Set G) \ {1})
    ((Submission.Blueprint.conj (Quotient.out q') S : Set G) \ {1})
  rw [Set.disjoint_left]
  intro x hx hx'
  have hx1 : x ∈ (Submission.Blueprint.conj (Quotient.out q) S : Set G) :=
    hx.1
  have hx2 : x ∈ (Submission.Blueprint.conj (Quotient.out q') S : Set G) :=
    hx'.1
  have hxne : x ≠ 1 := fun h1 => hx.2 (Set.mem_singleton_iff.mpr h1)
  have hmemN := conj_inv_mul_mem_normalizer (S := S) hTI hxne hx1 hx2
  have heq : q = q' := by
    have h1 : ((Quotient.out q : G) : G ⧸ Subgroup.normalizer (S : Set G))
        = ((Quotient.out q' : G) : G ⧸ Subgroup.normalizer (S : Set G)) :=
      QuotientGroup.eq.mpr hmemN
    rwa [QuotientGroup.out_eq' q, QuotientGroup.out_eq' q'] at h1
  exact hne heq

/-- A conjugate of `S` has as many elements as `S`. -/
theorem ncard_conj {G : Type} [Group G] (S : Subgroup G) (g : G) :
    (Submission.Blueprint.conj g S : Set G).ncard = Nat.card ↥S := by
  rw [Submission.Blueprint.conj]
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective (K := S)]
  exact (Nat.card_coe_set_eq (S.map (MulAut.conj g).toMonoidHom : Set G)).symm

/-- A conjugate of `S` has `|S| - 1` non-identity elements. -/
theorem ncard_conj_sdiff_one {G : Type} [Group G] (S : Subgroup G) (g : G) :
    ((Submission.Blueprint.conj g S : Set G) \ {1}).ncard = Nat.card ↥S - 1 := by
  have h1 : (1 : G) ∈ (Submission.Blueprint.conj g S : Set G) := by
    rw [SetLike.mem_coe, Work.Models.mem_conj_iff]
    simp
  rw [Set.ncard_sdiff_singleton_of_mem (s := (Submission.Blueprint.conj g S : Set G)) (a := 1) h1,
    ncard_conj]

theorem ncard_iUnion_conj {G : Type} [Group G] [Finite G] (S : Subgroup G)
    (hTI : ∀ g : G, g ∉ Subgroup.normalizer (S : Set G) →
      S ⊓ Submission.Blueprint.conj g S = ⊥) :
    (⋃ g : G, (Submission.Blueprint.conj g S : Set G)).ncard =
      1 + (Subgroup.normalizer (S : Set G)).index * (Nat.card ↥S - 1) := by
  classical
  haveI : Fintype (G ⧸ Subgroup.normalizer (S : Set G)) := Fintype.ofFinite _
  rw [iUnion_conj_eq_iUnion_quotient S]
  -- the union is the identity together with the union of the punctured conjugates
  have hdecomp : (⋃ q : G ⧸ Subgroup.normalizer (S : Set G),
        (Submission.Blueprint.conj (Quotient.out q) S : Set G))
      = insert 1 (⋃ q : G ⧸ Subgroup.normalizer (S : Set G),
          ((Submission.Blueprint.conj (Quotient.out q) S : Set G) \ {1})) := by
    ext x
    constructor
    · intro hx
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
      by_cases h : x = 1
      · exact Set.mem_insert_iff.mpr (Or.inl h)
      · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_iUnion.mpr
          ⟨q, ⟨hq, fun hh => h (Set.mem_singleton_iff.mp hh)⟩⟩))
    · intro hx
      rcases Set.mem_insert_iff.mp hx with h | hmem
      · rw [h]
        exact Set.mem_iUnion.mpr ⟨((1 : G) : G ⧸ Subgroup.normalizer (S : Set G)),
          by rw [SetLike.mem_coe, Work.Models.mem_conj_iff]; simp⟩
      · obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hmem
        exact Set.mem_iUnion.mpr ⟨q, hq.1⟩
  rw [hdecomp]
  have hmem1 : (1 : G) ∉ (⋃ q : G ⧸ Subgroup.normalizer (S : Set G),
      ((Submission.Blueprint.conj (Quotient.out q) S : Set G) \ {1})) := by
    intro h
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp h
    exact hq.2 (Set.mem_singleton_iff.mpr rfl)
  rw [Set.ncard_insert_of_notMem hmem1 (Set.toFinite _)]
  rw [Set.ncard_iUnion_of_finite
    (s := fun q : G ⧸ Subgroup.normalizer (S : Set G) =>
      ((Submission.Blueprint.conj (Quotient.out q) S : Set G) \ {1}))
    (fun _ => Set.toFinite _) (pairwiseDisjoint_conj_sdiff_one S hTI)]
  have hterm : ∀ q : G ⧸ Subgroup.normalizer (S : Set G),
      ((Submission.Blueprint.conj (Quotient.out q) S : Set G) \ {1}).ncard
        = Nat.card ↥S - 1 :=
    fun q => ncard_conj_sdiff_one S (Quotient.out q)
  rw [finsum_congr hterm,
    finsum_eq_finsetSum_of_support_subset (fun _ : G ⧸ Subgroup.normalizer (S : Set G) =>
      (Nat.card ↥S - 1)) (s := Finset.univ) (by intro x _; simp),
    Finset.sum_const, Finset.card_univ]
  have hcard : Fintype.card (G ⧸ Subgroup.normalizer (S : Set G))
      = (Subgroup.normalizer (S : Set G)).index := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
  rw [hcard, nsmul_eq_mul, Nat.cast_id, Nat.add_comm]

end Work.ZassenhausSuzuki
