import Mathlib

set_option linter.style.haveILetI false

namespace Work.Mostow.Margulis

/-! ### Auxiliary construction for the coset lemma (Thurston 4.1.15)

For a group `G`, a set `S ⊆ G` and a subgroup `H ≤ G` we build the sets
`shortProd S j` of elements of `G` expressible as a product of at most `j` elements of `S`,
and their image `cosetSpan S H j` in the left-coset space `G ⧸ H`. -/

/-- The subgroup of elements `g` of `G` which preserve a set `X` of the quotient, together
with their inverses.  (This is a subgroup without any finiteness assumption.) -/
def presSubgroup {G : Type*} [Group G] {H : Subgroup G} (X : Set (G ⧸ H)) : Subgroup G where
  carrier := {g | (∀ q ∈ X, g • q ∈ X) ∧ (∀ q ∈ X, g⁻¹ • q ∈ X)}
  one_mem' := ⟨fun q hq => by simpa using hq, fun q hq => by simpa using hq⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · rw [mul_smul]; exact hg1 _ (hh1 q hq)
    · rw [mul_inv_rev, mul_smul]; exact hh2 _ (hg2 q hq)
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    exact ⟨fun q hq => hg2 q hq, fun q hq => by simpa using hg1 q hq⟩

section

variable {G : Type*} [Group G]
variable (S : Set G) (H : Subgroup G)

/-- Elements of `G` that are products of at most `j` elements of `S`. -/
def shortProd (j : ℕ) : Set G :=
  {g | ∃ l : List G, l.length ≤ j ∧ (∀ x ∈ l, x ∈ S) ∧ l.prod = g}

/-- The image of `shortProd S j` in the left coset space `G ⧸ H`. -/
def cosetSpan (j : ℕ) : Set (G ⧸ H) := (fun g : G => (↑g : G ⧸ H)) '' shortProd S j

lemma one_mem_shortProd (j : ℕ) : (1 : G) ∈ shortProd S j :=
  ⟨[], by simp, by simp, by simp⟩

lemma eq_one_of_mem_shortProd_zero {g : G} (hg : g ∈ shortProd S 0) : g = 1 := by
  rcases hg with ⟨l, hl, -, hp⟩
  have hl' : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
  subst hl'
  simpa using hp.symm

lemma cosetSpan_zero : cosetSpan S H 0 = {(↑(1 : G) : G ⧸ H)} := by
  ext q
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [eq_one_of_mem_shortProd_zero S hg]
    rfl
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨1, one_mem_shortProd S 0, rfl⟩

lemma shortProd_mono {j k : ℕ} (h : j ≤ k) : shortProd S j ⊆ shortProd S k :=
  fun _ ⟨l, hl, hS, hp⟩ => ⟨l, le_trans hl h, hS, hp⟩

lemma smul_mem_shortProd_succ {s : G} (hs : s ∈ S) {j : ℕ} {g : G}
    (hg : g ∈ shortProd S j) : s * g ∈ shortProd S (j + 1) := by
  rcases hg with ⟨l, hl, hSl, rfl⟩
  refine ⟨s :: l, ?_, ?_, ?_⟩
  · simp only [List.length_cons]; omega
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hs
    · exact hSl x hx
  · simp only [List.prod_cons]

lemma cosetSpan_mono {j k : ℕ} (h : j ≤ k) : cosetSpan S H j ⊆ cosetSpan S H k :=
  Set.image_mono (shortProd_mono S h)

lemma cosetSpan_succ (j : ℕ) : cosetSpan S H j ⊆ cosetSpan S H (j + 1) :=
  cosetSpan_mono S H (Nat.le_succ j)

lemma mem_cosetSpan_succ_of_mem {s : G} (hs : s ∈ S) {j : ℕ} {q : G ⧸ H}
    (hq : q ∈ cosetSpan S H j) : s • q ∈ cosetSpan S H (j + 1) := by
  rcases hq with ⟨g, hg, rfl⟩
  exact ⟨s * g, smul_mem_shortProd_succ S hs hg, rfl⟩

/-- If the `cosetSpan` chain stabilises at step `j`, then already `cosetSpan S H j = univ`:
the stabilised set is invariant under the (left) action of all of `G`, because `S` is a
symmetric generating set, and the action on a nonempty set of cosets is transitive. -/
lemma cosetSpan_closed_eq_univ (hgen : Subgroup.closure S = ⊤) (hS : S = S⁻¹) {j : ℕ}
    (h : cosetSpan S H j = cosetSpan S H (j + 1)) : cosetSpan S H j = Set.univ := by
  have hSsub : S ⊆ (presSubgroup (cosetSpan S H j) : Set G) := by
    intro s hs
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · have h1 : s • q ∈ cosetSpan S H (j + 1) := mem_cosetSpan_succ_of_mem S H hs hq
      rwa [← h] at h1
    · have hs' : s⁻¹ ∈ S := by rw [hS]; simpa using hs
      have h1 : s⁻¹ • q ∈ cosetSpan S H (j + 1) := mem_cosetSpan_succ_of_mem S H hs' hq
      rwa [← h] at h1
  have hle : ⊤ ≤ presSubgroup (cosetSpan S H j) := by
    rw [← hgen]
    exact (Subgroup.closure_le (presSubgroup (cosetSpan S H j))).mpr hSsub
  have htop : presSubgroup (cosetSpan S H j) = ⊤ := top_le_iff.mp hle
  have hall : ∀ g : G, ∀ q ∈ cosetSpan S H j, g • q ∈ cosetSpan S H j :=
    fun g q hq => ((htop ▸ Subgroup.mem_top g : g ∈ presSubgroup (cosetSpan S H j))).1 q hq
  apply Set.eq_univ_of_univ_subset
  intro q _
  obtain ⟨a, rfl⟩ := Quotient.exists_rep q
  have hx : (↑(1 : G) : G ⧸ H) ∈ cosetSpan S H j := ⟨1, one_mem_shortProd S j, rfl⟩
  have := hall a _ hx
  simpa using this

/-- Pigeonhole: if `H` has index `> n`, then `cosetSpan S H n` meets at least `n + 1` cosets. -/
lemma ncard_cosetSpan_ge (hgen : Subgroup.closure S = ⊤) (hS : S = S⁻¹) {n : ℕ}
    (hindex : n < H.index) : n + 1 ≤ (cosetSpan S H n).ncard := by
  haveI hFin : Finite (G ⧸ H) :=
    (Nat.card_ne_zero.mp (by rw [← Subgroup.index_eq_card]; omega)).2
  by_contra hcon
  have hcon' : (cosetSpan S H n).ncard ≤ n := by omega
  have hpos : ∃ j, j < n ∧ cosetSpan S H j = cosetSpan S H (j + 1) := by
    by_contra hno
    rw [not_exists] at hno
    have hstrict : ∀ j, j < n → (cosetSpan S H j).ncard < (cosetSpan S H (j + 1)).ncard := by
      intro j hj
      have hno' : cosetSpan S H j ≠ cosetSpan S H (j + 1) := fun he => hno j ⟨hj, he⟩
      have hle : (cosetSpan S H j).ncard ≤ (cosetSpan S H (j + 1)).ncard :=
        Set.ncard_le_ncard (cosetSpan_succ S H j) (Set.toFinite _)
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · exact absurd (Set.eq_of_subset_of_ncard_le (cosetSpan_succ S H j) (le_of_eq heq.symm)
          (Set.toFinite _)) hno'
    have key : ∀ j, j ≤ n → j + 1 ≤ (cosetSpan S H j).ncard := by
      intro j
      induction j with
      | zero => intro _; rw [cosetSpan_zero S H]; simp
      | succ k ih =>
        intro hk
        have hk' : k < n := by omega
        have h1 := hstrict k hk'
        have h2 := ih (by omega)
        omega
    have := key n le_rfl
    omega
  obtain ⟨j, hj, hjeq⟩ := hpos
  have huniv : cosetSpan S H j = Set.univ := cosetSpan_closed_eq_univ S H hgen hS hjeq
  have hjn : cosetSpan S H j ⊆ cosetSpan S H n := cosetSpan_mono S H hj.le
  have hXn : cosetSpan S H n = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← huniv]; exact hjn
  rw [hXn, Set.ncard_univ, ← Subgroup.index_eq_card] at hcon'
  omega

end

/-- **Coset lemma (Thurston 4.1.15).** Let `S` be a symmetric generating set of a group `G` and
let `H ≤ G` be a subgroup of index `> n`. Then there are `n+1` elements of `G`, each a product of
at most `n` elements of `S`, lying in pairwise distinct left cosets of `H` (so
`(a i)⁻¹ * (a j) ∉ H` for `i ≠ j`).

Proof sketch. Let `A_j ⊆ G` be the set of products of at most `j` elements of `S` and let
`X_j ⊆ G ⧸ H` be its image in the quotient by the left-coset relation. Then `A_0 = {1}`, so
`|X_0| = 1`, and `A_{j+1} = A_j ∪ (S * A_j)`, so `X_{j+1} ⊆ X_j ∪ (S • X_j)`. If `X_{j+1} = X_j`
then `S • X_j ⊆ X_j`, hence `S^t • X_j ⊆ X_j` for all `t`, hence `X_j = G ⧸ H` because `S`
generates `G`. Now suppose `H.index > n`. Then `G ⧸ H` is finite (`Nat.card` is `0` for infinite
types, so `> n` rules that out). If `ncard X_n ≤ n`, the chain `X_0 ⊆ X_1 ⊆ ⋯ ⊆ X_n` (with
`ncard X_0 = 1` and `ncard X_n ≤ n`) has a repetition of cardinality, i.e. some `X_j = X_{j-1}`,
whence `X_j = G ⧸ H` and `H.index = ncard X_j ≤ ncard X_n ≤ n`, contradiction. So
`ncard X_n ≥ n+1`: pick `n+1` distinct cosets in `X_n` and a short representative for each. -/
theorem cosetLemma {G : Type*} [Group G] (S : Set G) (H : Subgroup G) (n : ℕ)
    (hgen : Subgroup.closure S = ⊤) (hS : S = S⁻¹) (hindex : n < H.index) :
    ∃ a : Fin (n + 1) → G,
      (∀ i, ∃ l : List G, l.length ≤ n ∧ (∀ x ∈ l, x ∈ S) ∧ l.prod = a i) ∧
      (∀ i j, i ≠ j → (a i)⁻¹ * (a j) ∉ H) := by
  haveI hFin : Finite (G ⧸ H) :=
    (Nat.card_ne_zero.mp (by rw [← Subgroup.index_eq_card]; omega)).2
  have hmain : n + 1 ≤ (cosetSpan S H n).ncard := ncard_cosetSpan_ge S H hgen hS hindex
  have hfin : (cosetSpan S H n).Finite := Set.toFinite _
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
      (α := Fin (n + 1)) (s := hfin.toFinset) (by
        rw [Fintype.card_fin, ← Set.ncard_eq_toFinset_card (cosetSpan S H n) hfin]
        exact hmain)
  have hmem : ∀ i, ∃ g : G, g ∈ shortProd S n ∧ (↑g : G ⧸ H) = f i := by
    intro i
    have h1 : f i ∈ hfin.toFinset := hf (Set.mem_range_self i)
    rw [Set.Finite.mem_toFinset] at h1
    exact h1
  choose a ha using hmem
  refine ⟨a, ?_, ?_⟩
  · intro i; exact (ha i).1
  · intro i j hij hmemH
    have hfij : f i ≠ f j := fun he => hij (f.injective he)
    have hne : (↑(a i) : G ⧸ H) ≠ ↑(a j) := by
      intro he
      exact hfij (by rw [← (ha i).2, ← (ha j).2]; exact he)
    exact hne (QuotientGroup.eq.mpr hmemH)

end Work.Mostow.Margulis
