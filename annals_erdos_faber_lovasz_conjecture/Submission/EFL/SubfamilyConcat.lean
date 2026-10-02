import Submission.EFL.GreedyListColouring
import Mathlib.Data.Set.Card

/-!
# Concatenating orderings of two disjoint subfamilies

The paper's proofs of Theorem 1.3 and Theorem 6.1 concatenate orderings of
several subfamilies into a single ordering of the union (Theorem 1.3: the
blocks `W₁, …, W_{k-1}` and `𝓗₁^good, …, 𝓗_k^good`; Theorem 6.1, Figure 3:
the blocks `𝓗₃, W₂, 𝓗₂^good, 𝓗₁^good`).

This module provides the two-piece concatenation *at the level of
subfamilies of `𝓗`*, phrased directly in terms of the quantity that is used
downstream: the number of *preceding neighbours* `d⪯(e)` of an edge.

If `𝓖 = 𝓖₁ ⊔ 𝓖₂` is a disjoint cover and `⪯₁`, `⪯₂` order the two parts,
then putting all of `𝓖₁` before all of `𝓖₂` gives an ordering `⪯` of `𝓖`
with

* `d⪯_𝓖(e) = d⪯_{𝓖₁}(e)` for `e ∈ 𝓖₁`, and
* `d⪯_𝓖(e) = |{f ∈ 𝓖₁ : f ∩ e ≠ ∅}| + d⪯_{𝓖₂}(e)` for `e ∈ 𝓖₂`

(`precedingDegree_concat_of_mem₁`, `precedingDegree_concat_of_mem₂`), and
the packaged form `exists_ordering_of_disjoint_cover` used by the loop of
Theorem 1.3.  The utility `setSumEquiv` (a disjoint cover is a sum) supplies
the cardinality bookkeeping.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ} {𝓖₁ 𝓖₂ 𝓖 : Hypergraph (Fin n)}

/-- the inclusion of `𝓖₁` into a cover `𝓖 = 𝓖₁ ∪ 𝓖₂` -/
def lift₁ (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) (e : 𝓖₁) : 𝓖 :=
  ⟨e.1, by rw [← hcover]; exact Or.inl e.2⟩

/-- the inclusion of `𝓖₂` into a cover `𝓖 = 𝓖₁ ∪ 𝓖₂` -/
def lift₂ (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) (e : 𝓖₂) : 𝓖 :=
  ⟨e.1, by rw [← hcover]; exact Or.inr e.2⟩

lemma lift₁_val (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) (e : 𝓖₁) : ((lift₁ hcover e : 𝓖) : Set (Fin n)) = e.1 := rfl

lemma lift₂_val (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) (e : 𝓖₂) : ((lift₂ hcover e : 𝓖) : Set (Fin n)) = e.1 := rfl

lemma lift₁_injective (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) : Function.Injective (lift₁ hcover : 𝓖₁ → 𝓖) := by
  intro a b hab
  exact Subtype.ext (congrArg (fun x : 𝓖 => (x : Set (Fin n))) hab)

lemma lift₂_injective (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) : Function.Injective (lift₂ hcover : 𝓖₂ → 𝓖) := by
  intro a b hab
  exact Subtype.ext (congrArg (fun x : 𝓖 => (x : Set (Fin n))) hab)

lemma lift₁_not_lift₂ (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) (hdisj : Disjoint 𝓖₁ 𝓖₂)
    (a : 𝓖₁) (b : 𝓖₂) : lift₁ hcover a ≠ lift₂ hcover b := by
  intro hab
  have hset : ((lift₁ hcover a : 𝓖) : Set (Fin n)) = ((lift₂ hcover b : 𝓖) : Set (Fin n)) :=
    congrArg (fun x : 𝓖 => (x : Set (Fin n))) hab
  rw [lift₁_val, lift₂_val] at hset
  exact (Set.disjoint_left.mp hdisj a.2) (hset ▸ b.2)

/-- an element of the second part is not in the first -/
lemma not_mem_left_of_mem_right (hdisj : Disjoint 𝓖₁ 𝓖₂) {x : Set (Fin n)}
    (hx : x ∈ 𝓖₂) : x ∉ 𝓖₁ :=
  fun hx₁ => (Set.disjoint_left.mp hdisj hx₁) hx

/-- the second part of a cover, for an element outside the first part -/
lemma mem_right_of_notMem (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) {e : 𝓖}
    (he : (e : Set (Fin n)) ∉ 𝓖₁) : (e : Set (Fin n)) ∈ 𝓖₂ := by
  have h : (e : Set (Fin n)) ∈ 𝓖₁ ∪ 𝓖₂ := by rw [hcover]; exact e.2
  exact h.resolve_left he

/-- the map from a disjoint cover to the sum of the two parts -/
def setSumFun (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) (e : 𝓖) : (𝓖₁ ⊕ 𝓖₂) := by
  classical
  exact if h : (e : Set (Fin n)) ∈ 𝓖₁ then Sum.inl ⟨e.1, h⟩
    else Sum.inr ⟨e.1, mem_right_of_notMem hcover h⟩

lemma setSumFun_of_mem (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) {e : 𝓖} (h : (e : Set (Fin n)) ∈ 𝓖₁) :
    setSumFun hcover e = Sum.inl ⟨e.1, h⟩ := by
  classical
  rw [setSumFun, dif_pos h]

lemma setSumFun_of_notMem (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) {e : 𝓖} (h : (e : Set (Fin n)) ∉ 𝓖₁) :
    setSumFun hcover e = Sum.inr ⟨e.1, mem_right_of_notMem hcover h⟩ := by
  classical
  rw [setSumFun, dif_neg h]

/-- **A disjoint cover is a sum**: the elements of `𝓖 = 𝓖₁ ⊔ 𝓖₂` split
bijectively into the elements of `𝓖₁` and those of `𝓖₂`. -/
def setSumEquiv (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) (hdisj : Disjoint 𝓖₁ 𝓖₂) : 𝓖 ≃ (𝓖₁ ⊕ 𝓖₂) where
  toFun := setSumFun hcover
  invFun s := match s with
    | Sum.inl x => lift₁ hcover x
    | Sum.inr y => lift₂ hcover y
  left_inv e := by
    by_cases h : (e : Set (Fin n)) ∈ 𝓖₁
    · rw [setSumFun_of_mem hcover h]
      exact Subtype.ext rfl
    · rw [setSumFun_of_notMem hcover h]
      exact Subtype.ext rfl
  right_inv s := by
    rcases s with x | y
    · rw [setSumFun_of_mem hcover x.2]
      exact congrArg Sum.inl (Subtype.ext rfl)
    · rw [setSumFun_of_notMem hcover (not_mem_left_of_mem_right hdisj y.2)]
      exact congrArg Sum.inr (Subtype.ext rfl)

lemma natCard_eq_add_of_cover (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) (hdisj : Disjoint 𝓖₁ 𝓖₂)
    {k₁ k₂ : ℕ} (ord₁ : 𝓖₁ ≃ Fin k₁) (ord₂ : 𝓖₂ ≃ Fin k₂) :
    Nat.card 𝓖 = k₁ + k₂ := by
  classical
  letI : Fintype (Set (Fin n)) := Fintype.ofFinite (Set (Fin n))
  letI : Fintype 𝓖 := Fintype.ofFinite 𝓖
  letI : Fintype 𝓖₁ := Fintype.ofFinite 𝓖₁
  letI : Fintype 𝓖₂ := Fintype.ofFinite 𝓖₂
  have h1 : Fintype.card 𝓖₁ = k₁ := by rw [Fintype.card_congr ord₁, Fintype.card_fin]
  have h2 : Fintype.card 𝓖₂ = k₂ := by rw [Fintype.card_congr ord₂, Fintype.card_fin]
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (setSumEquiv hcover hdisj),
    Fintype.card_sum, h1, h2]

/-! ## The concatenated rank and ordering -/

/-- the rank of the concatenation: all of `𝓖₁` before all of `𝓖₂` -/
def concatRankS (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) {k₁ k₂ : ℕ} (ord₁ : 𝓖₁ ≃ Fin k₁)
    (ord₂ : 𝓖₂ ≃ Fin k₂) (e : 𝓖) : ℕ := by
  classical
  exact if h : (e : Set (Fin n)) ∈ 𝓖₁ then (ord₁ ⟨e.1, h⟩ : ℕ)
    else k₁ + (ord₂ ⟨e.1, mem_right_of_notMem hcover h⟩ : ℕ)

lemma concatRankS_of_mem (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) {k₁ k₂ : ℕ} {ord₁ : 𝓖₁ ≃ Fin k₁}
    {ord₂ : 𝓖₂ ≃ Fin k₂} {e : 𝓖} (h : (e : Set (Fin n)) ∈ 𝓖₁) :
    concatRankS hcover ord₁ ord₂ e = (ord₁ ⟨e.1, h⟩ : ℕ) := by
  rw [concatRankS, dif_pos h]

lemma concatRankS_of_notMem (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) {k₁ k₂ : ℕ} {ord₁ : 𝓖₁ ≃ Fin k₁}
    {ord₂ : 𝓖₂ ≃ Fin k₂} {e : 𝓖} (h : (e : Set (Fin n)) ∉ 𝓖₁) :
    concatRankS hcover ord₁ ord₂ e
      = k₁ + (ord₂ ⟨e.1, mem_right_of_notMem hcover h⟩ : ℕ) := by
  rw [concatRankS, dif_neg h]

lemma concatRankS_lift₁ (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) {k₁ k₂ : ℕ} (ord₁ : 𝓖₁ ≃ Fin k₁)
    (ord₂ : 𝓖₂ ≃ Fin k₂) (e : 𝓖₁) :
    concatRankS hcover ord₁ ord₂ (lift₁ hcover e) = (ord₁ e : ℕ) := by
  rw [concatRankS_of_mem hcover e.2]
  exact congrArg (fun x : 𝓖₁ => (ord₁ x : ℕ)) (Subtype.ext rfl)

lemma concatRankS_lift₂ (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) (hdisj : Disjoint 𝓖₁ 𝓖₂) {k₁ k₂ : ℕ}
    (ord₁ : 𝓖₁ ≃ Fin k₁) (ord₂ : 𝓖₂ ≃ Fin k₂) (e : 𝓖₂) :
    concatRankS hcover ord₁ ord₂ (lift₂ hcover e) = k₁ + (ord₂ e : ℕ) := by
  classical
  rw [concatRankS_of_notMem hcover (e := lift₂ hcover e)
    (not_mem_left_of_mem_right hdisj e.2)]
  exact congrArg (fun x : 𝓖₂ => k₁ + (ord₂ x : ℕ)) (Subtype.ext rfl)

lemma concatRankS_lt (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) {k₁ k₂ : ℕ} (ord₁ : 𝓖₁ ≃ Fin k₁)
    (ord₂ : 𝓖₂ ≃ Fin k₂) (e : 𝓖) : concatRankS hcover ord₁ ord₂ e < k₁ + k₂ := by
  by_cases h : (e : Set (Fin n)) ∈ 𝓖₁
  · rw [concatRankS_of_mem hcover h]
    exact lt_of_lt_of_le (ord₁ ⟨e.1, h⟩).isLt (Nat.le_add_right k₁ k₂)
  · rw [concatRankS_of_notMem hcover h]
    have := (ord₂ ⟨e.1, mem_right_of_notMem hcover h⟩).isLt
    omega

lemma concatRankS_injective (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) (hdisj : Disjoint 𝓖₁ 𝓖₂)
    {k₁ k₂ : ℕ} (ord₁ : 𝓖₁ ≃ Fin k₁) (ord₂ : 𝓖₂ ≃ Fin k₂) :
    Function.Injective (concatRankS hcover ord₁ ord₂) := by
  intro e f hef
  by_cases he : (e : Set (Fin n)) ∈ 𝓖₁
  · by_cases hf : (f : Set (Fin n)) ∈ 𝓖₁
    · rw [concatRankS_of_mem hcover he, concatRankS_of_mem hcover hf] at hef
      have := ord₁.injective (Fin.ext hef)
      exact Subtype.ext (congrArg (fun x : 𝓖₁ => (x : Set (Fin n))) this)
    · rw [concatRankS_of_mem hcover he, concatRankS_of_notMem hcover hf] at hef
      have := (ord₁ ⟨e.1, he⟩).isLt
      omega
  · by_cases hf : (f : Set (Fin n)) ∈ 𝓖₁
    · rw [concatRankS_of_notMem hcover he, concatRankS_of_mem hcover hf] at hef
      have := (ord₁ ⟨f.1, hf⟩).isLt
      omega
    · rw [concatRankS_of_notMem hcover he, concatRankS_of_notMem hcover hf] at hef
      have hEq : (ord₂ ⟨e.1, mem_right_of_notMem hcover he⟩ : ℕ)
          = (ord₂ ⟨f.1, mem_right_of_notMem hcover hf⟩ : ℕ) := by omega
      have := ord₂.injective (Fin.ext hEq)
      exact Subtype.ext (congrArg (fun x : 𝓖₂ => (x : Set (Fin n))) this)

/-- **Concatenation of two orderings of a disjoint cover**: all of `𝓖₁`
before all of `𝓖₂`. -/
def concatOrderingS (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) (hdisj : Disjoint 𝓖₁ 𝓖₂)
    {k₁ k₂ : ℕ} (ord₁ : 𝓖₁ ≃ Fin k₁) (ord₂ : 𝓖₂ ≃ Fin k₂) : 𝓖 ≃ Fin (k₁ + k₂) :=
  Equiv.ofBijective
    (fun e => (⟨concatRankS hcover ord₁ ord₂ e, concatRankS_lt hcover ord₁ ord₂ e⟩ :
      Fin (k₁ + k₂)))
    ⟨fun e f hef => concatRankS_injective hcover hdisj ord₁ ord₂ (congrArg Fin.val hef),
      by
        intro x
        classical
        letI : Fintype (Set (Fin n)) := Fintype.ofFinite (Set (Fin n))
        letI : Fintype 𝓖 := Fintype.ofFinite 𝓖
        set F : 𝓖 → Fin (k₁ + k₂) := fun e =>
          (⟨concatRankS hcover ord₁ ord₂ e, concatRankS_lt hcover ord₁ ord₂ e⟩ :
            Fin (k₁ + k₂)) with hF
        have hinj : Function.Injective F := fun e g hefg =>
          concatRankS_injective hcover hdisj ord₁ ord₂ (congrArg Fin.val hefg)
        have himg : (Finset.univ.image F).card = Nat.card 𝓖 := by
          rw [Finset.card_image_of_injective (s := (Finset.univ : Finset 𝓖)) (f := F) hinj,
            Finset.card_univ, Nat.card_eq_fintype_card]
        have hEq : (Finset.univ.image F) = (Finset.univ : Finset (Fin (k₁ + k₂))) := by
          apply Finset.eq_of_subset_of_card_le
          · intro y _
            simp
          · rw [himg, natCard_eq_add_of_cover hcover hdisj ord₁ ord₂]
            simp
        have hx : x ∈ Finset.univ.image F := by rw [hEq]; simp
        rcases Finset.mem_image.mp hx with ⟨y, _hy, hEqx⟩
        exact ⟨y, hEqx⟩⟩

lemma concatOrderingS_apply (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) (hdisj : Disjoint 𝓖₁ 𝓖₂)
    {k₁ k₂ : ℕ} (ord₁ : 𝓖₁ ≃ Fin k₁) (ord₂ : 𝓖₂ ≃ Fin k₂) (e : 𝓖) :
    ((concatOrderingS hcover hdisj ord₁ ord₂ e : Fin (k₁ + k₂)) : ℕ)
      = concatRankS hcover ord₁ ord₂ e := rfl

lemma concatOrderingS_lift₁_le_iff (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) (hdisj : Disjoint 𝓖₁ 𝓖₂)
    {k₁ k₂ : ℕ} (ord₁ : 𝓖₁ ≃ Fin k₁) (ord₂ : 𝓖₂ ≃ Fin k₂) (a b : 𝓖₁) :
    ((concatOrderingS hcover hdisj ord₁ ord₂ (lift₁ hcover a) : Fin (k₁ + k₂)) : ℕ)
        ≤ ((concatOrderingS hcover hdisj ord₁ ord₂ (lift₁ hcover b) : Fin (k₁ + k₂)) : ℕ)
      ↔ (ord₁ a : ℕ) ≤ (ord₁ b : ℕ) := by
  rw [concatOrderingS_apply, concatOrderingS_apply, concatRankS_lift₁, concatRankS_lift₁]

lemma concatOrderingS_lift₁_lt (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) (hdisj : Disjoint 𝓖₁ 𝓖₂)
    {k₁ k₂ : ℕ} (ord₁ : 𝓖₁ ≃ Fin k₁) (ord₂ : 𝓖₂ ≃ Fin k₂) (a : 𝓖₁) :
    ((concatOrderingS hcover hdisj ord₁ ord₂ (lift₁ hcover a) : Fin (k₁ + k₂)) : ℕ) < k₁ := by
  rw [concatOrderingS_apply, concatRankS_lift₁]
  exact (ord₁ a).isLt

lemma concatOrderingS_lift₂_ge (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) (hdisj : Disjoint 𝓖₁ 𝓖₂)
    {k₁ k₂ : ℕ} (ord₁ : 𝓖₁ ≃ Fin k₁) (ord₂ : 𝓖₂ ≃ Fin k₂) (a : 𝓖₂) :
    k₁ ≤ ((concatOrderingS hcover hdisj ord₁ ord₂ (lift₂ hcover a) : Fin (k₁ + k₂)) : ℕ) := by
  rw [concatOrderingS_apply, concatRankS_lift₂ hcover hdisj]
  exact Nat.le_add_right k₁ _

lemma concatOrderingS_lift₂_le_iff (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) (hdisj : Disjoint 𝓖₁ 𝓖₂)
    {k₁ k₂ : ℕ} (ord₁ : 𝓖₁ ≃ Fin k₁) (ord₂ : 𝓖₂ ≃ Fin k₂) (a b : 𝓖₂) :
    ((concatOrderingS hcover hdisj ord₁ ord₂ (lift₂ hcover a) : Fin (k₁ + k₂)) : ℕ)
        ≤ ((concatOrderingS hcover hdisj ord₁ ord₂ (lift₂ hcover b) : Fin (k₁ + k₂)) : ℕ)
      ↔ (ord₂ a : ℕ) ≤ (ord₂ b : ℕ) := by
  rw [concatOrderingS_apply, concatOrderingS_apply, concatRankS_lift₂ hcover hdisj,
    concatRankS_lift₂ hcover hdisj]
  omega

end
end ErdosFaberLovaszConjecture

/-! ## Preceding degrees in the concatenation -/

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ} {𝓖₁ 𝓖₂ 𝓖 : Hypergraph (Fin n)}

lemma card_filter_eq_natCard {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = Nat.card {a : α // p a} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- the second part of a cover, for an element outside the first part -/
lemma mem_right_of_cover (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖) {x : Set (Fin n)} (hx : x ∈ 𝓖) (h : x ∉ 𝓖₁) :
    x ∈ 𝓖₂ := (show x ∈ 𝓖₁ ∪ 𝓖₂ from by rw [hcover]; exact hx).resolve_left h

/-- The preceding degree as a `Nat.card` of a subtype (the form used for
cardinality comparisons). -/
lemma precedingDegree_eq_natCard {k : ℕ} (𝓖 : Hypergraph (Fin n)) (ord : 𝓖 ≃ Fin k) (e : 𝓖) :
    precedingDegree 𝓖 ord e = Nat.card
      {f : 𝓖 // f ≠ e ∧ ord f ≤ ord e ∧
        ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} := by
  classical
  rw [precedingDegree, precedingNeighbours]
  exact card_filter_eq_natCard _

/-- **First block**: for `e ∈ 𝓖₁`, the preceding neighbours in the
concatenated ordering are the preceding neighbours in `𝓖₁`. -/
theorem precedingDegree_concatOrderingS_of_mem (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖)
    (hdisj : Disjoint 𝓖₁ 𝓖₂) {k₁ k₂ : ℕ} (ord₁ : 𝓖₁ ≃ Fin k₁) (ord₂ : 𝓖₂ ≃ Fin k₂)
    {e : 𝓖} (he : (e : Set (Fin n)) ∈ 𝓖₁) :
    precedingDegree 𝓖 (concatOrderingS hcover hdisj ord₁ ord₂) e
      ≤ precedingDegree 𝓖₁ ord₁ ⟨e.1, he⟩ := by
  classical
  set ord := concatOrderingS hcover hdisj ord₁ ord₂ with horddef
  have hval : ∀ f : 𝓖, ((ord f : Fin (k₁ + k₂)) : ℕ) = concatRankS hcover ord₁ ord₂ f :=
    fun f => concatOrderingS_apply hcover hdisj ord₁ ord₂ f
  have key : ∀ f : 𝓖, f ≠ e → ord f ≤ ord e → (f : Set (Fin n)) ∈ 𝓖₁ := by
    intro f _ hle
    by_contra hcon
    have hk : k₁ ≤ concatRankS hcover ord₁ ord₂ f := by
      rw [concatRankS_of_notMem hcover hcon]; exact Nat.le_add_right _ _
    have hek : concatRankS hcover ord₁ ord₂ e < k₁ := by
      rw [concatRankS_of_mem hcover he]; exact (ord₁ ⟨e.1, he⟩).isLt
    have hfle : concatRankS hcover ord₁ ord₂ f ≤ concatRankS hcover ord₁ ord₂ e := by
      rw [← hval f, ← hval e, ← Fin.le_iff_val_le_val]; exact hle
    omega
  rw [precedingDegree_eq_natCard, precedingDegree_eq_natCard]
  refine Nat.card_le_card_of_injective (fun f : {f : 𝓖 // f ≠ e ∧ ord f ≤ ord e ∧
      ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} =>
    (⟨⟨f.1.1, key f.1 f.2.1 f.2.2.1⟩, ?_, ?_, ?_⟩ :
      {g : 𝓖₁ // g ≠ ⟨e.1, he⟩ ∧ ord₁ g ≤ ord₁ ⟨e.1, he⟩ ∧
        ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty})) ?_
  · intro hc
    exact f.2.1 (Subtype.ext (congrArg (fun x : 𝓖₁ => (x.1 : Set (Fin n))) hc))
  · have h1 : ((ord₁ ⟨f.1.1, key f.1 f.2.1 f.2.2.1⟩ : Fin k₁) : ℕ)
        = concatRankS hcover ord₁ ord₂ f.1 :=
      (concatRankS_of_mem hcover (key f.1 f.2.1 f.2.2.1)).symm
    have h2 : ((ord₁ ⟨e.1, he⟩ : Fin k₁) : ℕ) = concatRankS hcover ord₁ ord₂ e :=
      (concatRankS_of_mem hcover he).symm
    have h3 : concatRankS hcover ord₁ ord₂ f.1 ≤ concatRankS hcover ord₁ ord₂ e := by
      rw [← hval f.1, ← hval e, ← Fin.le_iff_val_le_val]; exact f.2.2.1
    rw [Fin.le_iff_val_le_val]
    omega
  · have h1 : ((⟨f.1.1, key f.1 f.2.1 f.2.2.1⟩ : 𝓖₁) : Set (Fin n))
        = (f.1 : Set (Fin n)) := rfl
    have h2 : ((⟨e.1, he⟩ : 𝓖₁) : Set (Fin n)) = (e : Set (Fin n)) := rfl
    simpa only [h1, h2] using f.2.2.2
  · intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun x : {g : 𝓖₁ // g ≠ ⟨e.1, he⟩ ∧
        ord₁ g ≤ ord₁ ⟨e.1, he⟩ ∧
        ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} =>
        (x.1.1 : Set (Fin n))) hab))

/-- **Second block**: for `e ∈ 𝓖₂`, the preceding neighbours in the
concatenated ordering are the members of `𝓖₁` meeting `e` together with the
preceding neighbours of `e` inside `𝓖₂`. -/
theorem precedingDegree_concatOrderingS_of_notMem (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖)
    (hdisj : Disjoint 𝓖₁ 𝓖₂) {k₁ k₂ : ℕ} (ord₁ : 𝓖₁ ≃ Fin k₁) (ord₂ : 𝓖₂ ≃ Fin k₂)
    {e : 𝓖} (he : (e : Set (Fin n)) ∉ 𝓖₁) :
    precedingDegree 𝓖 (concatOrderingS hcover hdisj ord₁ ord₂) e
      ≤ Nat.card {f : 𝓖₁ // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty}
        + precedingDegree 𝓖₂ ord₂ ⟨e.1, mem_right_of_cover hcover e.2 he⟩ := by
  classical
  set ord := concatOrderingS hcover hdisj ord₁ ord₂ with horddef
  have hval : ∀ f : 𝓖, ((ord f : Fin (k₁ + k₂)) : ℕ) = concatRankS hcover ord₁ ord₂ f :=
    fun f => concatOrderingS_apply hcover hdisj ord₁ ord₂ f
  have he₂ : (e : Set (Fin n)) ∈ 𝓖₂ := mem_right_of_cover hcover e.2 he
  have hB : concatRankS hcover ord₁ ord₂ e = k₁ + (ord₂ ⟨e.1, he₂⟩ : ℕ) :=
    concatRankS_of_notMem hcover he
  -- the splitting of the preceding-neighbour subtype
  have hsplit : Nat.card
      {f : 𝓖 // f ≠ e ∧ ord f ≤ ord e ∧
        ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty}
      = Nat.card
        ({f : 𝓖₁ // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} ⊕
          {g : 𝓖₂ // g ≠ ⟨e.1, he₂⟩ ∧ ord₂ g ≤ ord₂ ⟨e.1, he₂⟩ ∧
            ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty}) := by
    apply Nat.card_congr
    let toF : {f : 𝓖 // f ≠ e ∧ ord f ≤ ord e ∧
        ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} →
        ({f : 𝓖₁ // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} ⊕
          {g : 𝓖₂ // g ≠ ⟨e.1, he₂⟩ ∧ ord₂ g ≤ ord₂ ⟨e.1, he₂⟩ ∧
            ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty}) := fun f => by
      by_cases h : (f.1 : Set (Fin n)) ∈ 𝓖₁
      · exact Sum.inl ⟨⟨f.1.1, h⟩, by simpa using f.2.2.2⟩
      · have h₂ : (f.1 : Set (Fin n)) ∈ 𝓖₂ := mem_right_of_cover hcover f.1.2 h
        refine Sum.inr ⟨⟨f.1.1, h₂⟩, ?_, ?_, ?_⟩
        · intro hc
          exact f.2.1 (Subtype.ext (congrArg (fun x : 𝓖₂ => (x.1 : Set (Fin n))) hc))
        · have hA : concatRankS hcover ord₁ ord₂ f.1 = k₁ + (ord₂ ⟨f.1.1, h₂⟩ : ℕ) :=
            concatRankS_of_notMem hcover h
          have hle : concatRankS hcover ord₁ ord₂ f.1 ≤ concatRankS hcover ord₁ ord₂ e := by
            rw [← hval f.1, ← hval e, ← Fin.le_iff_val_le_val]; exact f.2.2.1
          rw [Fin.le_iff_val_le_val]
          omega
        · have h1 : ((⟨f.1.1, h₂⟩ : 𝓖₂) : Set (Fin n)) = (f.1 : Set (Fin n)) := rfl
          have h2 : ((⟨e.1, he₂⟩ : 𝓖₂) : Set (Fin n)) = (e : Set (Fin n)) := rfl
          simpa only [h1, h2] using f.2.2.2
    let inF : ({f : 𝓖₁ // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} ⊕
          {g : 𝓖₂ // g ≠ ⟨e.1, he₂⟩ ∧ ord₂ g ≤ ord₂ ⟨e.1, he₂⟩ ∧
            ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty}) →
        {f : 𝓖 // f ≠ e ∧ ord f ≤ ord e ∧
          ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} := fun s => by
      rcases s with a | b
      · refine ⟨lift₁ hcover a.1, ?_, ?_, ?_⟩
        · intro hc
          have hthis : (a.1.1 : Set (Fin n)) = (e : Set (Fin n)) :=
            congrArg (fun x : 𝓖 => (x.1 : Set (Fin n))) hc
          exact he (hthis ▸ a.1.2)
        · have hA : ((ord (lift₁ hcover a.1) : Fin (k₁ + k₂)) : ℕ) = (ord₁ a.1 : ℕ) := by
            rw [hval]; exact concatRankS_lift₁ hcover ord₁ ord₂ a.1
          have hlt : (ord₁ a.1 : ℕ) < k₁ := (ord₁ a.1).isLt
          have hE : (ord e : ℕ) = k₁ + (ord₂ ⟨e.1, he₂⟩ : ℕ) := by
            rw [hval e]; exact hB
          rw [Fin.le_iff_val_le_val]
          omega
        · have h1 : ((lift₁ hcover a.1 : 𝓖) : Set (Fin n)) = (a.1 : Set (Fin n)) := rfl
          simpa only [h1] using a.2
      · refine ⟨lift₂ hcover b.1, ?_, ?_, ?_⟩
        · intro hc
          have : (b.1.1 : Set (Fin n)) = (e : Set (Fin n)) :=
            congrArg (fun x : 𝓖 => (x.1 : Set (Fin n))) hc
          have hb : (b.1 : 𝓖₂) = ⟨e.1, he₂⟩ := Subtype.ext this
          exact b.2.1 hb
        · have hA : ((ord (lift₂ hcover b.1) : Fin (k₁ + k₂)) : ℕ)
              = k₁ + (ord₂ b.1 : ℕ) := by
            rw [hval]; exact concatRankS_lift₂ hcover hdisj ord₁ ord₂ b.1
          have hle : (ord₂ b.1 : ℕ) ≤ (ord₂ ⟨e.1, he₂⟩ : ℕ) := by
            rw [← Fin.le_iff_val_le_val]; exact b.2.2.1
          have hE : (ord e : ℕ) = k₁ + (ord₂ ⟨e.1, he₂⟩ : ℕ) := by
            rw [hval e]; exact hB
          rw [Fin.le_iff_val_le_val]
          omega
        · have h1 : ((lift₂ hcover b.1 : 𝓖) : Set (Fin n)) = (b.1 : Set (Fin n)) := rfl
          have h2 : ((⟨e.1, he₂⟩ : 𝓖₂) : Set (Fin n)) = (e : Set (Fin n)) := rfl
          simpa only [h1, h2] using b.2.2.2
    refine ⟨toF, inF, ?_, ?_⟩
    · intro f
      show inF (toF f) = f
      dsimp only [toF, inF]
      split_ifs with hc
      · exact Subtype.ext (Subtype.ext rfl)
      · exact Subtype.ext (Subtype.ext rfl)
    · intro s
      rcases s with a | b
      · show toF (inF (Sum.inl a)) = Sum.inl a
        dsimp only [inF, toF]
        split_ifs with hc
        · exact congrArg Sum.inl (Subtype.ext rfl)
        · exact absurd a.1.2 hc
      · show toF (inF (Sum.inr b)) = Sum.inr b
        dsimp only [inF, toF]
        split_ifs with hc
        · exact absurd (by simpa [lift₂_val] using hc) (not_mem_left_of_mem_right hdisj b.1.2)
        · exact congrArg Sum.inr (Subtype.ext rfl)
  rw [precedingDegree_eq_natCard, precedingDegree_eq_natCard, hsplit]
  haveI : Fintype (𝓖₁ ⊕ 𝓖₂) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_sum]

/-- **Concatenation of two orderings, with the preceding-degree bound**: if
`⪯₁` and `⪯₂` order the two parts of a disjoint cover `𝓖 = 𝓖₁ ⊔ 𝓖₂`, and the
preceding degrees are bounded by `b` (for `𝓖₂`: counting the members of `𝓖₁`
meeting the edge, plus the preceding degree inside `𝓖₂`), then `𝓖` has an
ordering with all preceding degrees at most `b`. -/
theorem exists_ordering_of_disjoint_cover (hcover : 𝓖₁ ∪ 𝓖₂ = 𝓖)
    (hdisj : Disjoint 𝓖₁ 𝓖₂) {k₁ k₂ : ℕ} (ord₁ : 𝓖₁ ≃ Fin k₁) (ord₂ : 𝓖₂ ≃ Fin k₂)
    {b : ℝ}
    (h₁ : ∀ e : 𝓖₁, (precedingDegree 𝓖₁ ord₁ e : ℝ) ≤ b)
    (h₂ : ∀ e : 𝓖₂, ((Nat.card {f : 𝓖₁ // ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty} :
          ℝ) + (precedingDegree 𝓖₂ ord₂ e : ℝ)) ≤ b) :
    ∃ ord : 𝓖 ≃ Fin (k₁ + k₂), ∀ e : 𝓖, (precedingDegree 𝓖 ord e : ℝ) ≤ b := by
  classical
  refine ⟨concatOrderingS hcover hdisj ord₁ ord₂, ?_⟩
  intro e
  by_cases he : (e : Set (Fin n)) ∈ 𝓖₁
  · exact le_trans (by
      exact_mod_cast precedingDegree_concatOrderingS_of_mem hcover hdisj ord₁ ord₂ he)
      (h₁ _)
  · refine le_trans ?_ (h₂ ⟨e.1, mem_right_of_cover hcover e.2 he⟩)
    exact_mod_cast precedingDegree_concatOrderingS_of_notMem hcover hdisj ord₁ ord₂ he

end
end ErdosFaberLovaszConjecture
