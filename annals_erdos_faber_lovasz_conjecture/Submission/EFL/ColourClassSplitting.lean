import Submission.EFL.ColourClassCounting
import Submission.EFL.FewLargeColourClasses
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Splitting large colour classes into balanced matchings
(`few-large-colour-classes`(ii), §7)

The second half of Proposition `few-large-colour-classes` is the structural
splitting used by the greedy-colouring argument:

> Let `φ` be a proper edge-colouring of `𝓗` and let `α ∈ (0,1)`.  A colour
> class `φ⁻¹(c)` with `|V(φ⁻¹(c))| > αn` can be partitioned into pairwise
> edge-disjoint matchings `𝓜_c` such that every `M ∈ 𝓜_c` covers at least
> `αn/2` vertices and either consists of a single edge or covers at most
> `αn` vertices; moreover `|𝓜_c| ≤ 2/α`.
> (Edges of size ≥ `αn/2` are taken as singleton pieces; the remaining edges
> — all of size < `αn/2` — are grouped greedily into consecutive chunks of
> vertex-coverage between `αn/2` and `αn`.)

This file records the statement as `SplitColourClassStatement`, and proves
the piece-level obligations that the splitting must satisfy:

* every subfamily (in particular every consecutive chunk) of a matching
  colour class is a matching (`IsMatchingFamily_subfamily_colorClass`);
* coverage is monotone under taking subfamilies, and the vertex coverage of
  a chunk never exceeds the coverage of its colour class
  (`classVertexCount_chunk_le`);
* for a *matching* family the number of covered vertices equals the sum of
  the edge sizes (`sumEdgeSizes_eq_FamilyVertexCount_of_matching`), which is
  what makes interval arithmetic on chunk sizes possible;
* **greedy chunking at the natural level**: a list of positive naturals all
  `< A` admits a prefix whose sum lies in `[A, A + A − 1]`
  (`exists_prefix_reaching`), and decomposes into consecutive blocks, all but
  possibly the last of sum in `[A, 2A − 1]`, with the last of sum `< A`
  (`exists_chunk_intervals`).  These are the engine the splitting uses: an
  ordered list of the *small* edges (each of size `< αn/2 ≈ A`) is chunked
  so that each chunk covers between `αn/2` and `αn` vertices (the covered
  vertices of a matching chunk being the sum of its edge sizes).

The instantiation of the chunking to vertex coverage is complete at the
natural level: `exists_chunk_intervals_sizes` chunks a *list of edges* by
their size sums, `listCovered_eq_sizeSum` identifies a matching list's
covered vertices with its size sum, `matching_prefix_vertex_chunk` cuts one
nonempty prefix piece, and `chunk_matching_by_coverage` iterates it to a
full decomposition into consecutive blocks whose covered vertices all lie in
`[A, 2A−1]`, with the final block covering `< A` vertices.  Remaining for
the assembly: the singleton pieces for edges of size ≥ `αn/2`, the
real-threshold (`αn/2`, `αn`) instantiation, the `2/α` count bound, and the
assembly into `SplitColourClassStatement`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- A finite family `M` of edges is a *matching* and covers at least
`αn/2` vertices. -/
def CoversAtLeast (α : ℝ) (M : Finset (Set (Fin n))) : Prop :=
  (α / 2 : ℝ) * (n : ℝ) ≤ (FamilyVertexCount M : ℝ)

/-- A piece of a splitting: a matching that either is a singleton or covers
at most `αn` vertices (and, as required, at least `αn/2`). -/
def PieceOK (α : ℝ) (M : Finset (Set (Fin n))) : Prop :=
  IsMatchingFamily M ∧ CoversAtLeast α M ∧ (M.card = 1 ∨ (FamilyVertexCount M : ℝ) ≤ α * (n : ℝ))

/-- The splitting statement (paper, proof of `few-large-colour-classes`(ii)).
**This exact statement is NOT provable as written** (and is not used): a
colour class consisting of three pairwise disjoint edges of size `0.4αn`
covers `1.2αn > αn` vertices but admits no partition into pieces each
covering `≥ αn/2` vertices (every piece would need exactly two edges, an odd
number of edges is impossible), and a greedy chunking of total coverage just
above `αn` can leave one remainder piece below `αn/2`.  The *honest*
provable form is `SplitColourClassHonest` in
`ColourClassSplitHonest.lean`: pieces are matchings, each either a single
edge or covering `< αn + 1` vertices, every edge lies in exactly one piece,
and there are at most `2/α + 1` pieces (one exceptional piece -- the
leftover -- may cover fewer than `αn/2` vertices).  This record def is kept
only for historical documentation; see `ColourClassSplitHonest.lean`. -/
def SplitColourClassStatement (n : ℕ) (α : ℝ) (𝓗 : Hypergraph (Fin n)) : Prop :=
  ∀ (φ : 𝓗.Coloring (Fin n)) (c : Fin n),
    (α : ℝ) * (n : ℝ) < (φ.classVertexCount c : ℝ) →
      ∃ P : Finset (Finset (Set (Fin n))),
        (∀ M ∈ P, M ⊆ EdgeSetFamily (φ.colorClass c)) ∧
        (∀ M ∈ P, PieceOK α M) ∧
        (∀ e : Set (Fin n), e ∈ EdgeSetFamily (φ.colorClass c) →
          ∃! M : Finset (Set (Fin n)), M ∈ P ∧ e ∈ M) ∧
        ((P.card : ℝ) ≤ 2 / α)

/-- Subfamilies of a matching family are matching families. -/
theorem IsMatchingFamily.subset {s t : Finset (Set (Fin n))} (hsub : s ⊆ t)
    (hM : IsMatchingFamily t) : IsMatchingFamily s := by
  intro e₁ e₂ he₁ he₂ hne
  exact hM (hsub he₁) (hsub he₂) hne

/-- Every chunk of a colour class is a matching: colour classes are matchings
(`Coloring.colorClass_isMatching`), matchings lift to matching families
(`IsMatchingFamily_of_IsMatching`), and subfamilies of matchings are
matchings. -/
theorem IsMatchingFamily_subfamily_colorClass {𝓗 : Hypergraph (Fin n)}
    (φ : 𝓗.Coloring (Fin n)) (c : Fin n) {chunk : Finset (Set (Fin n))}
    (hsub : chunk ⊆ EdgeSetFamily (φ.colorClass c)) : IsMatchingFamily chunk := by
  have hM : IsMatchingFamily (EdgeSetFamily (φ.colorClass c)) :=
    IsMatchingFamily_of_IsMatching (Hypergraph.Coloring.colorClass_isMatching φ c)
  exact hM.subset hsub

/-- The vertices covered by a subfamily are contained in those covered by the
whole family. -/
theorem FamilyVertices_le_of_subset {s t : Finset (Set (Fin n))} (hsub : s ⊆ t) :
    FamilyVertexCount s ≤ FamilyVertexCount t := by
  dsimp [FamilyVertexCount]
  exact Set.ncard_le_ncard (by
    intro v hv
    rcases hv with ⟨e, he, hve⟩
    exact ⟨e, hsub he, hve⟩)

/-- The vertex coverage of a chunk of a colour class is at most the coverage
of the colour class. -/
theorem classVertexCount_chunk_le {𝓗 : Hypergraph (Fin n)} (φ : 𝓗.Coloring (Fin n))
    (c : Fin n) {chunk : Finset (Set (Fin n))}
    (hsub : chunk ⊆ EdgeSetFamily (φ.colorClass c)) :
    FamilyVertexCount chunk ≤ φ.classVertexCount c := by
  have hle1 : FamilyVertexCount chunk ≤
      FamilyVertexCount (EdgeSetFamily (φ.colorClass c)) := FamilyVertices_le_of_subset hsub
  have hEq : FamilyVertexCount (EdgeSetFamily (φ.colorClass c)) = φ.classVertexCount c :=
    (classVertexCount_eq_FamilyVertexCount φ c).symm
  exact hle1.trans_eq hEq

/-- In a matching family the number of covered vertices is the sum of the
edge sizes (the edges are pairwise vertex-disjoint, so their vertex sets are
pairwise disjoint). -/
theorem sumEdgeSizes_eq_FamilyVertexCount_of_matching (s : Finset (Set (Fin n)))
    (hM : IsMatchingFamily s) : sumEdgeSizes s = FamilyVertexCount s := by
  classical
  have hpd : (s : Set (Set (Fin n))).PairwiseDisjoint verts := by
    intro e₁ he₁ e₂ he₂ hne
    change Disjoint (verts e₁) (verts e₂)
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    have hd : Disjoint e₁ e₂ := hM he₁ he₂ hne
    rw [Set.disjoint_left] at hd
    exact (hd ((mem_verts e₁ v).1 hv₁)) ((mem_verts e₂ v).1 hv₂)
  let U : Finset (Fin n) := s.disjiUnion verts hpd
  have hU : (FamilyVertices s).ncard = U.card := by
    have hEqSet : FamilyVertices s = (U : Set (Fin n)) := by
      ext v
      simp [FamilyVertices, U, verts]
    rw [hEqSet]
    simp
  have hEqCard : U.card = sumEdgeSizes s := by
    dsimp [U]
    rw [Finset.card_disjiUnion]
    simp [sumEdgeSizes, edgeSize]
  calc
    sumEdgeSizes s = U.card := hEqCard.symm
    _ = (FamilyVertices s).ncard := hU.symm
    _ = FamilyVertexCount s := rfl


/-- Generalized one-block cut: if the elements of `l` are all `< A` and `≥ 1`,
`T ≥ 1` and `T ≤ l.sum`, then `l` has a nonempty prefix `b` with
`T ≤ b.sum ≤ T + A − 1`. -/
lemma exists_prefix_reaching {A : ℕ} (hA : 1 ≤ A) :
    ∀ (T : ℕ), 1 ≤ T → ∀ (l : List ℕ), (∀ x ∈ l, x < A) → (∀ x ∈ l, 1 ≤ x) →
      T ≤ l.sum →
      ∃ (b : List ℕ), b ≠ [] ∧ T ≤ b.sum ∧ b.sum ≤ T + A - 1 ∧ (∃ r : List ℕ, l = b ++ r) := by
  intro T
  induction T using Nat.strong_induction_on with
  | h T ih =>
      intro hT1 l hsmall hpos htot
      cases l with
      | nil =>
          simp at htot
          omega
      | cons x xs =>
          have hx : x < A := hsmall x (by simp)
          have hxpos : 1 ≤ x := hpos x (by simp)
          simp at htot
          by_cases hxT : T ≤ x
          · refine ⟨[x], by simp, hxT, ?_, ⟨xs, rfl⟩⟩
            simp
            omega
          · have hxT' : x < T := lt_of_not_ge hxT
            have hsmall' : ∀ y ∈ xs, y < A := by
              intro y hy
              exact hsmall y (by simp [hy])
            have hpos' : ∀ y ∈ xs, 1 ≤ y := by
              intro y hy
              exact hpos y (by simp [hy])
            have htot' : T - x ≤ xs.sum := by omega
            have hT1' : 1 ≤ T - x := by omega
            have hrec := ih (T - x) (by omega) hT1' xs hsmall' hpos' htot'
            rcases hrec with ⟨b, hbne, hbT, hbU, ⟨r, hEq⟩⟩
            refine ⟨x :: b, by simp, ?_, ?_, ⟨r, ?_⟩⟩
            · -- T ≤ x + b.sum
              simp
              omega
            · -- x + b.sum ≤ T + A - 1
              simp
              omega
            · calc
                x :: xs = x :: (b ++ r) := by rw [hEq]
                _ = (x :: b) ++ r := by rfl

/-- One-block cut with the bound `[A, 2A−1]` (target `T = A`), for lists of
positive naturals all `< A`. -/
lemma exists_prefix_sum_in {A : ℕ} (hA : 1 ≤ A) (l : List ℕ)
    (hsmall : ∀ x ∈ l, x < A) (hpos : ∀ x ∈ l, 1 ≤ x) (htotal : A ≤ l.sum) :
    ∃ (b : List ℕ), b ≠ [] ∧ A ≤ b.sum ∧ b.sum ≤ 2 * A - 1 ∧ (∃ r : List ℕ, l = b ++ r) := by
  rcases exists_prefix_reaching (A := A) hA A hA l hsmall hpos htotal with ⟨b, hbne, hbT, hbU, hpr⟩
  refine ⟨b, hbne, hbT, ?_, hpr⟩
  omega

/-- *Greedy chunking*: a list of positive naturals all `< A` decomposes into
consecutive blocks, all but possibly the last having sum in `[A, 2A−1]`, and
the last having sum `< A`. -/
lemma exists_chunk_intervals {A : ℕ} (hA : 1 ≤ A) (l : List ℕ)
    (hsmall : ∀ x ∈ l, x < A) (hpos : ∀ x ∈ l, 1 ≤ x) :
    ∃ (init : List (List ℕ)) (last : List ℕ),
      l = init.flatten ++ last ∧
      (∀ b ∈ init, b ≠ [] ∧ A ≤ b.sum ∧ b.sum ≤ 2 * A - 1) ∧
      last.sum < A := by
  let Q : ℕ → Prop := fun m => ∀ (l' : List ℕ), l'.sum = m → (∀ x ∈ l', x < A) →
    (∀ x ∈ l', 1 ≤ x) → ∃ (init : List (List ℕ)) (last : List ℕ),
      l' = init.flatten ++ last ∧
      (∀ b ∈ init, b ≠ [] ∧ A ≤ b.sum ∧ b.sum ≤ 2 * A - 1) ∧
      last.sum < A
  have hQ : ∀ m : ℕ, (∀ n < m, Q n) → Q m := by
    intro m ih l' hsum hsmall' hpos'
    by_cases htot : A ≤ l'.sum
    · rcases exists_prefix_sum_in hA l' hsmall' hpos' htot with ⟨b, hbne, hbA, hbU, ⟨r, hEq⟩⟩
      have hmemr : ∀ x ∈ r, x < A := by
        intro x hx
        exact hsmall' x (by rw [hEq]; simp [hx])
      have hmemr1 : ∀ x ∈ r, 1 ≤ x := by
        intro x hx
        exact hpos' x (by rw [hEq]; simp [hx])
      have hsumr : l'.sum = b.sum + r.sum := by
        calc
          l'.sum = (b ++ r).sum := by rw [hEq]
          _ = b.sum + r.sum := by simp
      have hbpos : 1 ≤ b.sum := le_trans hA hbA
      have hlt : r.sum < b.sum + r.sum := by omega
      have hltl : r.sum < l'.sum := by
        rw [hsumr]
        exact hlt
      have hltm : r.sum < m := by
        rw [hsum] at hltl
        exact hltl
      rcases ih r.sum hltm r rfl hmemr hmemr1 with ⟨init', last', hjoin', hblk', hlast'⟩
      refine ⟨b :: init', last', ?_, ?_, hlast'⟩
      · calc
          l' = b ++ r := hEq
          _ = b ++ (init'.flatten ++ last') := by rw [hjoin']
          _ = (b :: init').flatten ++ last' := by simp
      · intro bl hbl
        simp at hbl
        rcases hbl with rfl | hbl
        · exact ⟨hbne, hbA, hbU⟩
        · exact hblk' bl hbl
    · refine ⟨[], l', ?_, ?_, ?_⟩
      · simp
      · intro b hb
        simp at hb
      · exact lt_of_not_ge htot
  have hq : Q l.sum := Nat.strong_induction_on (p := Q) l.sum hQ
  exact hq l rfl hsmall hpos

/-!
## Instantiating the chunking to edge lists and vertex coverage

`listSizeSum es` is the sum of the edge sizes of a list of edges.  The two
lemmas below mirror `exists_prefix_reaching` and `exists_chunk_intervals` on
*lists of edges* (so the pieces are lists of edges, not just numbers), with
block size measured by `listSizeSum`.  Then `listCovered_eq_sizeSum` shows
that for a list of pairwise vertex-disjoint edges (a matching), the covered
vertices have size equal to `listSizeSum`, which is what turns the size
intervals into *vertex-coverage* intervals for the splitting.
-/

/-- The sum of the sizes of the edges in a list. -/
def listSizeSum (es : List (Set (Fin n))) : ℕ :=
  (es.map edgeSize).sum

/-- `listSizeSum` of a cons. -/
theorem listSizeSum_cons (e : Set (Fin n)) (es : List (Set (Fin n))) :
    listSizeSum (e :: es) = edgeSize e + listSizeSum es := by
  rfl

/-- `listSizeSum` of an append. -/
theorem listSizeSum_append (es₁ es₂ : List (Set (Fin n))) :
    listSizeSum (es₁ ++ es₂) = listSizeSum es₁ + listSizeSum es₂ := by
  simp [listSizeSum]

/-- Generalized one-block cut on a *list of edges*: if every edge size is
`< A` and `≥ 1`, `T ≥ 1`, and the total edge size is `≥ T`, then a nonempty
prefix of the list has edge-size sum in `[T, T + A − 1]`. -/
lemma exists_prefix_reaching_sizes {A : ℕ} (hA : 1 ≤ A) :
    ∀ (T : ℕ), 1 ≤ T → ∀ (es : List (Set (Fin n))),
      (∀ e ∈ es, edgeSize e < A) → (∀ e ∈ es, 1 ≤ edgeSize e) → T ≤ listSizeSum es →
      ∃ (b : List (Set (Fin n))), b ≠ [] ∧ T ≤ listSizeSum b ∧
        listSizeSum b ≤ T + A - 1 ∧ (∃ r : List (Set (Fin n)), es = b ++ r) := by
  intro T
  induction T using Nat.strong_induction_on with
  | h T ih =>
      intro hT1 es hsmall hpos htot
      cases es with
      | nil =>
          simp [listSizeSum] at htot
          omega
      | cons e es' =>
          have hx : edgeSize e < A := hsmall e (by simp)
          have hxpos : 1 ≤ edgeSize e := hpos e (by simp)
          simp [listSizeSum] at htot
          by_cases hxT : T ≤ edgeSize e
          · refine ⟨[e], by simp, ?_, ?_, ⟨es', rfl⟩⟩
            · simpa [listSizeSum] using hxT
            · simpa [listSizeSum] using (by omega : edgeSize e ≤ T + A - 1)
          · have hxT' : edgeSize e < T := lt_of_not_ge hxT
            have hsmall' : ∀ e' ∈ es', edgeSize e' < A := by
              intro e' he'
              exact hsmall e' (by simp [he'])
            have hpos' : ∀ e' ∈ es', 1 ≤ edgeSize e' := by
              intro e' he'
              exact hpos e' (by simp [he'])
            have htot' : T - edgeSize e ≤ listSizeSum es' := by
              simpa [listSizeSum] using (by omega : T - edgeSize e ≤ (es'.map edgeSize).sum)
            have hT1' : 1 ≤ T - edgeSize e := by omega
            have hrec := ih (T - edgeSize e) (by omega) hT1' es' hsmall' hpos' htot'
            rcases hrec with ⟨b, hbne, hbT, hbU, ⟨r, hEq⟩⟩
            refine ⟨e :: b, by simp, ?_, ?_, ⟨r, ?_⟩⟩
            · -- T ≤ edgeSize e + listSizeSum b
              rw [listSizeSum_cons]
              omega
            · -- edgeSize e + listSizeSum b ≤ T + A - 1
              rw [listSizeSum_cons]
              omega
            · calc
                e :: es' = e :: (b ++ r) := by rw [hEq]
                _ = (e :: b) ++ r := by rfl

/-- One-block cut on a list of edges with the bound `[A, 2A−1]` (target
`T = A`), for edges of size in `[1, A−1]`. -/
lemma exists_prefix_sum_in_sizes {A : ℕ} (hA : 1 ≤ A) (es : List (Set (Fin n)))
    (hsmall : ∀ e ∈ es, edgeSize e < A) (hpos : ∀ e ∈ es, 1 ≤ edgeSize e)
    (htotal : A ≤ listSizeSum es) :
    ∃ (b : List (Set (Fin n))), b ≠ [] ∧ A ≤ listSizeSum b ∧
      listSizeSum b ≤ 2 * A - 1 ∧ (∃ r : List (Set (Fin n)), es = b ++ r) := by
  rcases exists_prefix_reaching_sizes (A := A) hA A hA es hsmall hpos htotal with
    ⟨b, hbne, hbT, hbU, hpr⟩
  refine ⟨b, hbne, hbT, ?_, hpr⟩
  omega

/-- *Greedy chunking on a list of edges*: edges of size in `[1, A−1]`
decompose into consecutive blocks, all but possibly the last having
edge-size sum in `[A, 2A−1]`, and the last having edge-size sum `< A`. -/
lemma exists_chunk_intervals_sizes {A : ℕ} (hA : 1 ≤ A) (es : List (Set (Fin n)))
    (hsmall : ∀ e ∈ es, edgeSize e < A) (hpos : ∀ e ∈ es, 1 ≤ edgeSize e) :
    ∃ (init : List (List (Set (Fin n)))) (last : List (Set (Fin n))),
      es = init.flatten ++ last ∧
      (∀ b ∈ init, b ≠ [] ∧ A ≤ listSizeSum b ∧ listSizeSum b ≤ 2 * A - 1) ∧
      listSizeSum last < A := by
  let Q : ℕ → Prop := fun m => ∀ (es' : List (Set (Fin n))), listSizeSum es' = m →
    (∀ e ∈ es', edgeSize e < A) → (∀ e ∈ es', 1 ≤ edgeSize e) →
      ∃ (init : List (List (Set (Fin n)))) (last : List (Set (Fin n))),
        es' = init.flatten ++ last ∧
        (∀ b ∈ init, b ≠ [] ∧ A ≤ listSizeSum b ∧ listSizeSum b ≤ 2 * A - 1) ∧
        listSizeSum last < A
  have hQ : ∀ m : ℕ, (∀ n < m, Q n) → Q m := by
    intro m ih es' hsum hsmall' hpos'
    by_cases htot : A ≤ listSizeSum es'
    · rcases exists_prefix_sum_in_sizes hA es' hsmall' hpos' htot with ⟨b, hbne, hbA, hbU, ⟨r, hEq⟩⟩
      have hmemr : ∀ e ∈ r, edgeSize e < A := by
        intro e he
        exact hsmall' e (by rw [hEq]; simp [he])
      have hmemr1 : ∀ e ∈ r, 1 ≤ edgeSize e := by
        intro e he
        exact hpos' e (by rw [hEq]; simp [he])
      have hsumr : listSizeSum es' = listSizeSum b + listSizeSum r := by
        calc
          listSizeSum es' = listSizeSum (b ++ r) := by rw [hEq]
          _ = listSizeSum b + listSizeSum r := listSizeSum_append b r
      have hbpos : 1 ≤ listSizeSum b := le_trans hA hbA
      have hlt : listSizeSum r < listSizeSum b + listSizeSum r := by omega
      have hltl : listSizeSum r < listSizeSum es' := by
        rw [hsumr]
        exact hlt
      have hltm : listSizeSum r < m := by
        rw [hsum] at hltl
        exact hltl
      rcases ih (listSizeSum r) hltm r rfl hmemr hmemr1 with ⟨init', last', hjoin', hblk', hlast'⟩
      refine ⟨b :: init', last', ?_, ?_, hlast'⟩
      · calc
          es' = b ++ r := hEq
          _ = b ++ (init'.flatten ++ last') := by rw [hjoin']
          _ = (b :: init').flatten ++ last' := by simp
      · intro bl hbl
        simp at hbl
        rcases hbl with rfl | hbl
        · exact ⟨hbne, hbA, hbU⟩
        · exact hblk' bl hbl
    · refine ⟨[], es', ?_, ?_, ?_⟩
      · simp
      · intro b hb
        simp at hb
      · exact lt_of_not_ge htot
  have hq : Q (listSizeSum es) := Nat.strong_induction_on (p := Q) (listSizeSum es) hQ
  exact hq es rfl hsmall hpos

/-- The vertices covered by a list of edges. -/
def listCovered (es : List (Set (Fin n))) : Set (Fin n) :=
  {v : Fin n | ∃ e : Set (Fin n), e ∈ es ∧ v ∈ e}

/-- For a list of pairwise vertex-disjoint edges (a matching), the number of
covered vertices is the sum of the edge sizes. -/
lemma listCovered_eq_sizeSum (es : List (Set (Fin n))) (hnodup : es.Nodup)
    (hdis : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ es → e₂ ∈ es → e₁ ≠ e₂ → Disjoint e₁ e₂) :
    (listCovered es).ncard = listSizeSum es := by
  classical
  let s : Finset (Set (Fin n)) := ⟨es, hnodup⟩
  have hMem : ∀ e : Set (Fin n), e ∈ s ↔ e ∈ es := by
    intro e
    rfl
  have hM : IsMatchingFamily s := by
    intro e₁ e₂ he₁ he₂ hne
    exact hdis (hMem e₁ |>.1 he₁) (hMem e₂ |>.1 he₂) hne
  have heq := sumEdgeSizes_eq_FamilyVertexCount_of_matching s hM
  have hleft : sumEdgeSizes s = listSizeSum es := by
    rfl
  have hright : FamilyVertexCount s = (listCovered es).ncard := by
    unfold FamilyVertexCount listCovered
    congr 1
  rw [← heq] at hright
  rw [hleft] at hright
  exact hright.symm

/-- The left part of a Nodup append is Nodup. -/
lemma nodup_of_append_left {α : Type*} (a b : List α) (h : (a ++ b).Nodup) : a.Nodup := by
  induction a with
  | nil => simp
  | cons x xs ih =>
      have hcons := List.nodup_cons.mp h
      have ih' := ih hcons.2
      exact List.nodup_cons.mpr ⟨(by
        intro hx
        exact hcons.1 (by simp [hx])), ih'⟩

/-- *Vertex-coverage chunk, first piece*: from a matching list of edges of
size in `[1, A−1]` with total edge size at least `A`, cut off a nonempty
prefix piece covering between `A` and `2A−1` vertices. -/
theorem matching_prefix_vertex_chunk {n A : ℕ} (hA : 1 ≤ A)
    (es : List (Set (Fin n))) (hnodup : es.Nodup)
    (hdis : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ es → e₂ ∈ es → e₁ ≠ e₂ → Disjoint e₁ e₂)
    (hsmall : ∀ e ∈ es, edgeSize e < A) (hpos : ∀ e ∈ es, 1 ≤ edgeSize e)
    (htotal : A ≤ listSizeSum es) :
    ∃ (b r : List (Set (Fin n))), es = b ++ r ∧ b ≠ [] ∧
      A ≤ (listCovered b).ncard ∧ (listCovered b).ncard ≤ 2 * A - 1 := by
  classical
  rcases exists_prefix_sum_in_sizes hA es hsmall hpos htotal with ⟨b, hbne, hbA, hbU, ⟨r, hEq⟩⟩
  have hnodup' : (b ++ r).Nodup := by simpa [hEq] using hnodup
  have hnodupB : b.Nodup := nodup_of_append_left b r hnodup'
  have hdisB : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ b → e₂ ∈ b → e₁ ≠ e₂ → Disjoint e₁ e₂ := by
    intro e₁ e₂ he₁ he₂ hne
    exact hdis (by rw [hEq]; simp [he₁]) (by rw [hEq]; simp [he₂]) hne
  have hcov : (listCovered b).ncard = listSizeSum b := listCovered_eq_sizeSum b hnodupB hdisB
  refine ⟨b, r, hEq, hbne, ?_, ?_⟩
  · rw [hcov]
    exact hbA
  · rw [hcov]
    exact hbU

/-- The right part of a Nodup append is Nodup. -/
lemma nodup_of_append_right {α : Type*} (a b : List α) (h : (a ++ b).Nodup) : b.Nodup := by
  induction a with
  | nil => simpa using h
  | cons x xs ih =>
      exact ih (List.nodup_cons.mp h).2

/-- *Vertex-coverage chunking*: a matching list of edges of size in
`[1, A−1]` decomposes into consecutive blocks, all but possibly the last
covering between `A` and `2A−1` vertices, and the last covering fewer than
`A` vertices. -/
theorem chunk_matching_by_coverage {n A : ℕ} (hA : 1 ≤ A)
    (es : List (Set (Fin n))) (hnodup : es.Nodup)
    (hdis : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ es → e₂ ∈ es → e₁ ≠ e₂ → Disjoint e₁ e₂)
    (hsmall : ∀ e ∈ es, edgeSize e < A) (hpos : ∀ e ∈ es, 1 ≤ edgeSize e) :
    ∃ (init : List (List (Set (Fin n)))) (last : List (Set (Fin n))),
      es = init.flatten ++ last ∧
      (∀ b ∈ init, b ≠ [] ∧ A ≤ (listCovered b).ncard ∧ (listCovered b).ncard ≤ 2 * A - 1) ∧
      (listCovered last).ncard < A := by
  let Q : ℕ → Prop := fun m => ∀ (es' : List (Set (Fin n))), listSizeSum es' = m →
    es'.Nodup →
    (∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ es' → e₂ ∈ es' → e₁ ≠ e₂ → Disjoint e₁ e₂) →
    (∀ e ∈ es', edgeSize e < A) → (∀ e ∈ es', 1 ≤ edgeSize e) →
      ∃ (init : List (List (Set (Fin n)))) (last : List (Set (Fin n))),
        es' = init.flatten ++ last ∧
        (∀ b ∈ init, b ≠ [] ∧ A ≤ (listCovered b).ncard ∧ (listCovered b).ncard ≤ 2 * A - 1) ∧
        (listCovered last).ncard < A
  have hQ : ∀ m : ℕ, (∀ n < m, Q n) → Q m := by
    intro m ih es' hsum hnodup' hdis' hsmall' hpos'
    by_cases htot : A ≤ listSizeSum es'
    · rcases matching_prefix_vertex_chunk hA es' hnodup' hdis' hsmall' hpos' htot with
        ⟨b, r, hEq, hbne, hbA, hbU⟩
      have hmemr : ∀ e ∈ r, edgeSize e < A := by
        intro e he
        exact hsmall' e (by rw [hEq]; simp [he])
      have hmemr1 : ∀ e ∈ r, 1 ≤ edgeSize e := by
        intro e he
        exact hpos' e (by rw [hEq]; simp [he])
      have hdisR : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ r → e₂ ∈ r → e₁ ≠ e₂ → Disjoint e₁ e₂ := by
        intro e₁ e₂ he₁ he₂ hne
        exact hdis' (by rw [hEq]; simp [he₁]) (by rw [hEq]; simp [he₂]) hne
      have hnodupR : r.Nodup := nodup_of_append_right b r (by simpa [hEq] using hnodup')
      have hcovB : (listCovered b).ncard = listSizeSum b := by
        have hnodupB : b.Nodup := nodup_of_append_left b r (by simpa [hEq] using hnodup')
        have hdisB : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ b → e₂ ∈ b → e₁ ≠ e₂ → Disjoint e₁ e₂ := by
          intro e₁ e₂ he₁ he₂ hne
          exact hdis' (by rw [hEq]; simp [he₁]) (by rw [hEq]; simp [he₂]) hne
        exact listCovered_eq_sizeSum b hnodupB hdisB
      have hsumr : listSizeSum es' = listSizeSum b + listSizeSum r := by
        calc
          listSizeSum es' = listSizeSum (b ++ r) := by rw [hEq]
          _ = listSizeSum b + listSizeSum r := listSizeSum_append b r
      have hbge : 1 ≤ listSizeSum b := by
        rw [← hcovB]
        exact le_trans hA hbA
      have hltl : listSizeSum r < listSizeSum es' := by
        rw [hsumr]
        omega
      have hltm : listSizeSum r < m := by
        rw [hsum] at hltl
        exact hltl
      rcases ih (listSizeSum r) hltm r rfl hnodupR hdisR hmemr hmemr1 with
        ⟨init', last', hjoin', hblk', hlast'⟩
      refine ⟨b :: init', last', ?_, ?_, hlast'⟩
      · calc
          es' = b ++ r := hEq
          _ = b ++ (init'.flatten ++ last') := by rw [hjoin']
          _ = (b :: init').flatten ++ last' := by simp
      · intro bl hbl
        simp at hbl
        rcases hbl with rfl | hbl
        · exact ⟨hbne, hbA, hbU⟩
        · exact hblk' bl hbl
    · refine ⟨[], es', ?_, ?_, ?_⟩
      · simp
      · intro b hb
        simp at hb
      · have hcovE : (listCovered es').ncard = listSizeSum es' :=
          listCovered_eq_sizeSum es' hnodup' hdis'
        rw [hcovE]
        exact lt_of_not_ge htot
  have hq : Q (listSizeSum es) := Nat.strong_induction_on (p := Q) (listSizeSum es) hQ
  exact hq es rfl hnodup hdis hsmall hpos

/-!
## Singleton pieces

An edge of size at least `αn/2` can serve as a singleton piece: it is a
matching, covers at least `αn/2` vertices (its own vertices), and consists of
a single edge (so it is exempt from the upper `αn` bound).  The lemmas below
connect `edgeSize` to `ncard` (needed to identify an edge's vertex count with
its size), identify the covered vertices of a singleton family, and package
the singleton as a `PieceOK`.
-/

/-- A singleton family covers exactly the vertices of the edge. -/
lemma FamilyVertexCount_singleton {n : ℕ} (e : Set (Fin n)) :
    FamilyVertexCount ({e} : Finset (Set (Fin n))) = e.ncard := by
  classical
  unfold FamilyVertexCount FamilyVertices
  congr 1
  ext v
  simp

/-- A singleton edge of size at least `αn/2` is a matching piece covering at
least `αn/2` vertices, consisting of a single edge. -/
theorem singleton_piece_vertex {n : ℕ} {α : ℝ} {e : Set (Fin n)}
    (he : (α / 2 : ℝ) * (n : ℝ) ≤ (edgeSize e : ℝ)) :
    IsMatchingFamily ({e} : Finset (Set (Fin n))) ∧
    CoversAtLeast α ({e} : Finset (Set (Fin n))) ∧
    ({e} : Finset (Set (Fin n))).card = 1 := by
  classical
  constructor
  · intro e₁ e₂ he₁ he₂ hne
    simp at he₁ he₂
    subst e₁
    subst e₂
    exact (hne rfl).elim
  constructor
  · dsimp [CoversAtLeast]
    have hcov : FamilyVertexCount ({e} : Finset (Set (Fin n))) = edgeSize e := by
      calc
        FamilyVertexCount ({e} : Finset (Set (Fin n))) = e.ncard := FamilyVertexCount_singleton e
        _ = edgeSize e := (edgeSize_eq_ncard e).symm
    rw [hcov]
    exact he
  · simp

/-- A singleton edge of size at least `αn/2` is an admissible piece
(`PieceOK`). -/
theorem PieceOK_singleton {n : ℕ} {α : ℝ} {e : Set (Fin n)}
    (he : (α / 2 : ℝ) * (n : ℝ) ≤ (edgeSize e : ℝ)) :
    PieceOK α ({e} : Finset (Set (Fin n))) := by
  rcases singleton_piece_vertex (α := α) (e := e) he with ⟨hM, hcov, hsing⟩
  exact ⟨hM, hcov, Or.inl hsing⟩

/-!
## Partitioning an edge list by a size threshold

To assemble the splitting, the edges of a colour class are separated by the
threshold `A ≈ αn/2`: edges of size `≥ A` become singleton pieces
(`PieceOK_singleton`), and the edges of size `< A` are chunked by
`chunk_matching_by_coverage`.  The two filtered lists `bigEdgesOf A es` and
`smallEdgesOf A es` carry all the properties the two assembly steps need.
-/

/-- The edges of a list of size at least `A` (the potential singleton
pieces). -/
def bigEdgesOf (A : ℕ) (es : List (Set (Fin n))) : List (Set (Fin n)) :=
  es.filter (fun e : Set (Fin n) => decide (A ≤ edgeSize e))

/-- The edges of a list of size at most `A−1` (the chunkable small edges). -/
def smallEdgesOf (A : ℕ) (es : List (Set (Fin n))) : List (Set (Fin n)) :=
  es.filter (fun e : Set (Fin n) => decide (edgeSize e < A))

/-- Membership in `bigEdgesOf`. -/
theorem mem_bigEdgesOf {n A : ℕ} {es : List (Set (Fin n))} (e : Set (Fin n)) :
    e ∈ bigEdgesOf A es ↔ e ∈ es ∧ A ≤ edgeSize e := by
  classical
  simp [bigEdgesOf]

/-- Membership in `smallEdgesOf`. -/
theorem mem_smallEdgesOf {n A : ℕ} {es : List (Set (Fin n))} (e : Set (Fin n)) :
    e ∈ smallEdgesOf A es ↔ e ∈ es ∧ edgeSize e < A := by
  classical
  simp [smallEdgesOf]

/-- A big edge belongs to the original list. -/
theorem mem_of_mem_bigEdgesOf {n A : ℕ} {es : List (Set (Fin n))} {e : Set (Fin n)}
    (he : e ∈ bigEdgesOf A es) : e ∈ es :=
  (mem_bigEdgesOf e).1 he |>.1

/-- A small edge belongs to the original list. -/
theorem mem_of_mem_smallEdgesOf {n A : ℕ} {es : List (Set (Fin n))} {e : Set (Fin n)}
    (he : e ∈ smallEdgesOf A es) : e ∈ es :=
  (mem_smallEdgesOf e).1 he |>.1

/-- The big edges have size at least `A`. -/
theorem bigEdgesOf_sizes {n A : ℕ} {es : List (Set (Fin n))} :
    ∀ e ∈ bigEdgesOf A es, A ≤ edgeSize e := by
  intro e he
  exact (mem_bigEdgesOf e).1 he |>.2

/-- The small edges have size at most `A−1`. -/
theorem smallEdgesOf_sizes {n A : ℕ} {es : List (Set (Fin n))} :
    ∀ e ∈ smallEdgesOf A es, edgeSize e < A := by
  intro e he
  exact (mem_smallEdgesOf e).1 he |>.2

/-- Every edge is big or small, and never both. -/
theorem partition_by_threshold {n A : ℕ} (es : List (Set (Fin n))) :
    (∀ e ∈ es, e ∈ bigEdgesOf A es ∨ e ∈ smallEdgesOf A es) ∧
    (∀ e ∈ es, ¬ (e ∈ bigEdgesOf A es ∧ e ∈ smallEdgesOf A es)) := by
  classical
  constructor
  · intro e he
    by_cases h : A ≤ edgeSize e
    · exact Or.inl (by simp [mem_bigEdgesOf, he, h])
    · exact Or.inr (by simp [mem_smallEdgesOf, he, lt_of_not_ge h])
  · intro e he hboth
    have hbig : A ≤ edgeSize e := (mem_bigEdgesOf e).1 hboth.1 |>.2
    have hsmall : edgeSize e < A := (mem_smallEdgesOf e).1 hboth.2 |>.2
    omega

/-- Nodup is preserved by filtering out the big edges. -/
theorem nodup_smallEdgesOf {n A : ℕ} {es : List (Set (Fin n))} (hnodup : es.Nodup) :
    (smallEdgesOf A es).Nodup := by
  classical
  exact List.Nodup.filter (fun e : Set (Fin n) => decide (edgeSize e < A)) hnodup

/-- Nodup is preserved by filtering out the small edges. -/
theorem nodup_bigEdgesOf {n A : ℕ} {es : List (Set (Fin n))} (hnodup : es.Nodup) :
    (bigEdgesOf A es).Nodup := by
  classical
  exact List.Nodup.filter (fun e : Set (Fin n) => decide (A ≤ edgeSize e)) hnodup

/-- Pairwise vertex-disjointness is inherited by the small edges. -/
theorem pairwiseDisjoint_smallEdgesOf {n A : ℕ} {es : List (Set (Fin n))}
    (hdis : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ es → e₂ ∈ es → e₁ ≠ e₂ → Disjoint e₁ e₂) :
    ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ smallEdgesOf A es → e₂ ∈ smallEdgesOf A es →
      e₁ ≠ e₂ → Disjoint e₁ e₂ := by
  intro e₁ e₂ he₁ he₂ hne
  exact hdis (mem_of_mem_smallEdgesOf he₁) (mem_of_mem_smallEdgesOf he₂) hne

/-- Pairwise vertex-disjointness is inherited by the big edges. -/
theorem pairwiseDisjoint_bigEdgesOf {n A : ℕ} {es : List (Set (Fin n))}
    (hdis : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ es → e₂ ∈ es → e₁ ≠ e₂ → Disjoint e₁ e₂) :
    ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ bigEdgesOf A es → e₂ ∈ bigEdgesOf A es →
      e₁ ≠ e₂ → Disjoint e₁ e₂ := by
  intro e₁ e₂ he₁ he₂ hne
  exact hdis (mem_of_mem_bigEdgesOf he₁) (mem_of_mem_bigEdgesOf he₂) hne

/-!
## Real threshold instantiation

To link the integer chunking (blocks covering `[A, 2A−1]` vertices) with the
real thresholds of `SplitColourClassStatement` (`αn/2` below, `αn` above) one
sets `A := ⌈αn/2⌉`.  The lower bound is automatic
(`SplitThreshold_lower`: `αn/2 ≤ A`).  For the upper bound there is a genuine
integrality subtlety: `2A−1 ≤ αn` does *not* hold for every `α, n` (e.g.
`αn = 6.4`: `A = 4`, `2A−1 = 7 > 6.4`).  What always holds is
`2A−1 < αn + 1` (`SplitThreshold_upper`).  Absorbing the `+1` requires the
constants of the final argument to carry a small margin (equivalently, one
may chunk by a maximal prefix of real size-sum `≤ αn`, whose bound has no
`+1`); this is a parameter-hygiene step of the assembly, recorded here so it
is not lost.
-/

/-- The integer splitting threshold `⌈αn/2⌉`. -/
def SplitThreshold (α : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil ((α / 2 : ℝ) * (n : ℝ))

/-- Lower bound: `αn/2 ≤ ⌈αn/2⌉`. -/
theorem SplitThreshold_lower (α : ℝ) (n : ℕ) :
    (α / 2 : ℝ) * (n : ℝ) ≤ (SplitThreshold α n : ℝ) := by
  dsimp [SplitThreshold]
  exact Nat.le_ceil _

/-- Upper bound (always true): `2⌈αn/2⌉ − 1 < αn + 1`. -/
theorem SplitThreshold_upper {α : ℝ} {n : ℕ} (hα : 0 ≤ α) :
    (2 * SplitThreshold α n - 1 : ℝ) < (α : ℝ) * (n : ℝ) + 1 := by
  dsimp [SplitThreshold]
  have hx : 0 ≤ (α / 2 : ℝ) * (n : ℝ) := by
    have hα2 : 0 ≤ α / 2 := div_nonneg hα (by norm_num)
    have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    exact mul_nonneg hα2 hn
  have hlt := Nat.ceil_lt_add_one (a := (α / 2 : ℝ) * (n : ℝ)) hx
  -- ↑⌈x⌉₊ < x + 1, and 2(x+1) − 1 = αn + 1
  nlinarith

/-!
## Packaging singletons and chunks

With `A` a size threshold (eventually `A = SplitThreshold α n`), the edges of
`bigEdgesOf A es` become singleton `PieceOK`s, and the edges of
`smallEdgesOf A es` are chunked by `chunk_matching_by_coverage` (positivity
of edge sizes is carried by `smallEdgesOf_pos`).  These two lemmas package
both halves of the threshold split; the Finset conversion and the bundling
into `SplitColourClassStatement` come next.
-/

/-- Positivity of edge sizes is inherited by the small edges. -/
theorem smallEdgesOf_pos {n A : ℕ} {es : List (Set (Fin n))}
    (hpos : ∀ e ∈ es, 1 ≤ edgeSize e) : ∀ e ∈ smallEdgesOf A es, 1 ≤ edgeSize e := by
  intro e he
  exact hpos e (mem_of_mem_smallEdgesOf he)

/-- An edge of size at least `A`, with `αn/2 ≤ A`, is a singleton `PieceOK`. -/
theorem PieceOK_singleton_big {n A : ℕ} {α : ℝ} {e : Set (Fin n)}
    (hA : (α / 2 : ℝ) * (n : ℝ) ≤ (A : ℝ)) (he : A ≤ edgeSize e) :
    PieceOK α ({e} : Finset (Set (Fin n))) := by
  have he' : (α / 2 : ℝ) * (n : ℝ) ≤ (edgeSize e : ℝ) := by
    exact hA.trans (by exact_mod_cast he)
  exact PieceOK_singleton (α := α) (e := e) he'

/-- Every edge of `bigEdgesOf A es` (with `αn/2 ≤ A`) is a singleton
`PieceOK`. -/
theorem PieceOK_singletons_of_big {n A : ℕ} {α : ℝ} {es : List (Set (Fin n))}
    (hA : (α / 2 : ℝ) * (n : ℝ) ≤ (A : ℝ)) :
    ∀ e ∈ bigEdgesOf A es, PieceOK α ({e} : Finset (Set (Fin n))) := by
  intro e he
  exact PieceOK_singleton_big hA (bigEdgesOf_sizes (A := A) (es := es) e he)

/-- The chunk packaging: the small edges of a matching edge list decompose
into consecutive vertex-coverage pieces in `[A, 2A−1]` plus a remainder of
coverage `< A`. -/
theorem chunk_small_edges {n A : ℕ} (hA : 1 ≤ A) (es : List (Set (Fin n)))
    (hnodup : es.Nodup)
    (hdis : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ es → e₂ ∈ es → e₁ ≠ e₂ → Disjoint e₁ e₂)
    (hpos : ∀ e ∈ es, 1 ≤ edgeSize e) :
    ∃ (init : List (List (Set (Fin n)))) (last : List (Set (Fin n))),
      smallEdgesOf A es = init.flatten ++ last ∧
      (∀ b ∈ init, b ≠ [] ∧ A ≤ (listCovered b).ncard ∧ (listCovered b).ncard ≤ 2 * A - 1) ∧
      (listCovered last).ncard < A := by
  exact chunk_matching_by_coverage hA (smallEdgesOf A es) (nodup_smallEdgesOf hnodup)
    (pairwiseDisjoint_smallEdgesOf hdis) (smallEdgesOf_sizes) (smallEdgesOf_pos hpos)

/-!
## Converting list pieces to Finsets

The chunking produces pieces as *lists* of edges (with `nodup` and pairwise
vertex-disjointness).  A nodup list is converted to a `Finset` piece via the
`Finset` constructor; the covered-vertex count is preserved
(`listCovered_finset`), the piece is a matching (`finsetOfList_isMatching`),
and a piece whose list-covered count lies in `[A, 2A−1]` has its
`FamilyVertexCount` in the same interval (`finsetOfList_coverage`).  This is
the bridge from the chunking output to the `Finset`-valued pieces that
`SplitColourClassStatement` requires.
-/

/-- The vertices covered by a nodup list equal the vertices covered by its
Finset. -/
lemma listCovered_finset {n : ℕ} {b : List (Set (Fin n))} (hn : b.Nodup) :
    FamilyVertexCount (⟨b, hn⟩ : Finset (Set (Fin n))) = (listCovered b).ncard := by
  classical
  unfold FamilyVertexCount listCovered
  congr 1

/-- A nodup list of pairwise vertex-disjoint edges is a matching Finset. -/
lemma finsetOfList_isMatching {n : ℕ} {b : List (Set (Fin n))} (hn : b.Nodup)
    (hdis : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ b → e₂ ∈ b → e₁ ≠ e₂ → Disjoint e₁ e₂) :
    IsMatchingFamily (⟨b, hn⟩ : Finset (Set (Fin n))) := by
  intro e₁ e₂ he₁ he₂ hne
  -- membership in the finset is membership in the list
  exact hdis he₁ he₂ hne

/-- A chunk (nodup, pairwise-disjoint, coverage in `[A, 2A−1]` as a list) is
an admissible Finset piece of the same coverage. -/
theorem finsetOfList_coverage {n A : ℕ} {b : List (Set (Fin n))} (hn : b.Nodup)
    (hdis : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ b → e₂ ∈ b → e₁ ≠ e₂ → Disjoint e₁ e₂)
    (hcovL : A ≤ (listCovered b).ncard) (hcovU : (listCovered b).ncard ≤ 2 * A - 1) :
    IsMatchingFamily (⟨b, hn⟩ : Finset (Set (Fin n))) ∧
    A ≤ FamilyVertexCount (⟨b, hn⟩ : Finset (Set (Fin n))) ∧
    FamilyVertexCount (⟨b, hn⟩ : Finset (Set (Fin n))) ≤ 2 * A - 1 := by
  classical
  have hm : IsMatchingFamily (⟨b, hn⟩ : Finset (Set (Fin n))) := finsetOfList_isMatching hn hdis
  have hcov : FamilyVertexCount (⟨b, hn⟩ : Finset (Set (Fin n))) = (listCovered b).ncard :=
    listCovered_finset hn
  refine ⟨hm, ?_, ?_⟩
  · rw [hcov]
    exact hcovL
  · rw [hcov]
    exact hcovU

/-!
## Step (2): the union of the pieces

The full edge list `es` is the disjoint union of its big half and small half
(`finset_eq_big_union_small`); the big half is the union of its singleton
pieces (`big_singleton_union`); the small half is the union of the chunk
pieces and the leftover produced by `chunk_small_edges`
(`chunk_small_edges_partition`).  These are the three union facts that the
single partition witness must satisfy; the witness itself (a
`Finset (Finset (Set (Fin n)))` combining singletons, chunk finsets and the
leftover) is assembled from them.
-/

/-- The full edge set is the disjoint union of its big and small halves. -/
theorem finset_eq_big_union_small {n A : ℕ} (es : List (Set (Fin n))) (hn : es.Nodup) :
    (⟨es, hn⟩ : Finset (Set (Fin n))) =
      (bigEdgesOf A es).toFinset ∪ (smallEdgesOf A es).toFinset := by
  classical
  ext e
  by_cases hbig : A ≤ edgeSize e
  · have hnlt : ¬ edgeSize e < A := by omega
    simp [mem_bigEdgesOf, mem_smallEdgesOf, hbig, hnlt]
    rfl
  · have hlt : edgeSize e < A := lt_of_not_ge hbig
    simp [mem_bigEdgesOf, mem_smallEdgesOf, hbig, hlt]
    rfl

/-- The big half is the union of the singleton pieces of its edges. -/
theorem big_singleton_union {n A : ℕ} (es : List (Set (Fin n))) :
    (bigEdgesOf A es).toFinset =
      (bigEdgesOf A es).toFinset.biUnion (fun e : Set (Fin n) => ({e} : Finset (Set (Fin n)))) := by
  classical
  ext e
  simp

/-- A list is the union of its blocks: `small = init.flatten ++ last` gives
`small` as the union of the block finsets and the last finset. -/
theorem flatten_finset_union {n : ℕ} {init : List (List (Set (Fin n)))}
    {last : List (Set (Fin n))} {small : List (Set (Fin n))}
    (hflat : small = init.flatten ++ last) (hn : small.Nodup) :
    (⟨small, hn⟩ : Finset (Set (Fin n))) =
      init.toFinset.biUnion (fun b : List (Set (Fin n)) => b.toFinset) ∪ last.toFinset := by
  classical
  ext e
  simp [hflat]

/-- The covered vertices of a list converted to a Finset equal the covered
vertices of the list. -/
lemma FamilyVertexCount_toFinset {n : ℕ} (b : List (Set (Fin n))) :
    FamilyVertexCount b.toFinset = (listCovered b).ncard := by
  classical
  unfold FamilyVertexCount listCovered
  congr 1
  ext v
  simp [FamilyVertices]

/-- The small half of a matching edge list is the union of its chunk pieces
and its leftover. -/
theorem chunk_small_edges_partition {n A : ℕ} (hA : 1 ≤ A)
    (es : List (Set (Fin n))) (hnodup : es.Nodup)
    (hdis : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ es → e₂ ∈ es → e₁ ≠ e₂ → Disjoint e₁ e₂)
    (hpos : ∀ e ∈ es, 1 ≤ edgeSize e) :
    ∃ (init : List (List (Set (Fin n)))) (last : List (Set (Fin n))),
      (∀ b ∈ init, b ≠ [] ∧ A ≤ (listCovered b).ncard ∧ (listCovered b).ncard ≤ 2 * A - 1) ∧
      (listCovered last).ncard < A ∧
      (⟨smallEdgesOf A es, nodup_smallEdgesOf hnodup⟩ : Finset (Set (Fin n))) =
        init.toFinset.biUnion (fun b : List (Set (Fin n)) => b.toFinset) ∪ last.toFinset := by
  classical
  rcases chunk_small_edges hA es hnodup hdis hpos with ⟨init, last, hflat, hblk, hlast⟩
  refine ⟨init, last, hblk, hlast, ?_⟩
  exact flatten_finset_union hflat (nodup_smallEdgesOf hnodup)

/-!
## The partition witness `P`

`P` is the single `Finset (Finset (Set (Fin n)))` of pieces: singleton pieces
for the big edges, the chunk Finsets and the leftover piece for the small
edges.  `flatten_blocks_disjoint` and `flatten_blocks_disjoint_last` give the
edge-disjointness of the blocks and the leftover of a `Nodup` flatten
decomposition; `colour_edges_split_witness` packages everything: every piece
is a matching, pieces are pairwise edge-disjoint, and every edge of `es`
lies in some piece.
-/

/-- The blocks of a Nodup flatten decomposition are pairwise disjoint. -/
lemma flatten_blocks_disjoint {α : Type*} [DecidableEq α] {init : List (List α)}
    {last : List α} (hn : (init.flatten ++ last).Nodup) :
    ∀ ⦃b₁ : List α⦄, b₁ ∈ init → ∀ ⦃b₂ : List α⦄, b₂ ∈ init → b₁ ≠ b₂ →
      Disjoint (b₁.toFinset) (b₂.toFinset) := by
  induction init with
  | nil =>
      intro b₁ hb₁
      simp at hb₁
  | cons b rest ih =>
      have hnapp := List.nodup_append.mp (by simpa using hn)
      intro b₁ hb₁ b₂ hb₂ hne
      simp at hb₁ hb₂
      rcases hb₁ with rfl | hb₁
      · rcases hb₂ with rfl | hb₂
        · exact (hne rfl).elim
        · rw [Finset.disjoint_left]
          intro x hx₁ hx₂
          have hx₂' : x ∈ rest.flatten ++ last :=
            List.mem_append.mpr (Or.inl (List.mem_flatten.mpr ⟨b₂, hb₂, List.mem_toFinset.mp hx₂⟩))
          exact (hnapp.2.2 x (List.mem_toFinset.mp hx₁) x hx₂') rfl
      · rcases hb₂ with rfl | hb₂'
        · rw [Finset.disjoint_left]
          intro x hx₁ hx₂
          have hx₁' : x ∈ rest.flatten ++ last :=
            List.mem_append.mpr (Or.inl (List.mem_flatten.mpr ⟨b₁, hb₁, List.mem_toFinset.mp hx₁⟩))
          exact (hnapp.2.2 x (List.mem_toFinset.mp hx₂) x hx₁') rfl
        · exact ih hnapp.2.1 hb₁ hb₂' hne

/-- The blocks of a Nodup flatten decomposition are disjoint from the last
part. -/
lemma flatten_blocks_disjoint_last {α : Type*} [DecidableEq α] {init : List (List α)}
    {last : List α} (hn : (init.flatten ++ last).Nodup) :
    ∀ ⦃b : List α⦄, b ∈ init → Disjoint (b.toFinset) (last.toFinset) := by
  induction init with
  | nil =>
      intro b hb
      simp at hb
  | cons b rest ih =>
      have hnapp := List.nodup_append.mp (by simpa using hn)
      intro b₁ hb₁
      simp at hb₁
      rcases hb₁ with rfl | hb₁
      · rw [Finset.disjoint_left]
        intro x hx₁ hx₂
        have hx₂' : x ∈ rest.flatten ++ last := List.mem_append.mpr (Or.inr (List.mem_toFinset.mp hx₂))
        exact (hnapp.2.2 x (List.mem_toFinset.mp hx₁) x hx₂') rfl
      · exact ih hnapp.2.1 hb₁

/-- The partition witness for a colour-class edge list at threshold `A`:
pieces are the singletons of the big edges plus the chunk Finsets and the
leftover of the small edges; every piece is a matching, pieces are pairwise
edge-disjoint, and every edge of the list lies in some piece. -/
theorem colour_edges_split_witness {n A : ℕ} (hA : 1 ≤ A) (es : List (Set (Fin n)))
    (hnodup : es.Nodup)
    (hdis : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ es → e₂ ∈ es → e₁ ≠ e₂ → Disjoint e₁ e₂)
    (hpos : ∀ e ∈ es, 1 ≤ edgeSize e) :
    ∃ (P : Finset (Finset (Set (Fin n)))),
      (∀ M ∈ P, IsMatchingFamily M) ∧
      (∀ M₁ ∈ P, ∀ M₂ ∈ P, M₁ ≠ M₂ → Disjoint M₁ M₂) ∧
      (∀ e : Set (Fin n), e ∈ es → ∃ M ∈ P, e ∈ M) := by
  classical
  rcases chunk_small_edges hA es hnodup hdis hpos with ⟨init, last, hflat, hblk, hlastCov⟩
  let Pbig : Finset (Finset (Set (Fin n))) :=
    (bigEdgesOf A es).toFinset.image (fun e : Set (Fin n) => ({e} : Finset (Set (Fin n))))
  let Pchunk : Finset (Finset (Set (Fin n))) :=
    init.toFinset.image (fun b : List (Set (Fin n)) => b.toFinset)
  let P : Finset (Finset (Set (Fin n))) := Pbig ∪ Pchunk ∪ {last.toFinset}
  have hmemP : ∀ M : Finset (Set (Fin n)), M ∈ P ↔
      (∃ e ∈ bigEdgesOf A es, M = ({e} : Finset (Set (Fin n)))) ∨
      (∃ b ∈ init, M = b.toFinset) ∨ M = last.toFinset := by
    intro M
    simp [P, Pbig, Pchunk]
    aesop
  -- 1. every piece is a matching
  have hmatching : ∀ M ∈ P, IsMatchingFamily M := by
    intro M hM
    rw [hmemP] at hM
    rcases hM with hbig | hsmall
    · rcases hbig with ⟨e, hebig, rfl⟩
      intro e₁ e₂ he₁ he₂ hne
      simp at he₁ he₂
      subst e₁
      subst e₂
      exact (hne rfl).elim
    · rcases hsmall with hchunk | rfl
      · rcases hchunk with ⟨b, hb, rfl⟩
        intro e₁ e₂ he₁ he₂ hne
        have he₁' : e₁ ∈ es := mem_of_mem_smallEdgesOf (by
          rw [hflat]
          exact List.mem_append.mpr (Or.inl (List.mem_flatten.mpr ⟨b, hb, List.mem_toFinset.mp he₁⟩)))
        have he₂' : e₂ ∈ es := mem_of_mem_smallEdgesOf (by
          rw [hflat]
          exact List.mem_append.mpr (Or.inl (List.mem_flatten.mpr ⟨b, hb, List.mem_toFinset.mp he₂⟩)))
        exact hdis he₁' he₂' hne
      · intro e₁ e₂ he₁ he₂ hne
        have he₁' : e₁ ∈ es := mem_of_mem_smallEdgesOf (by
          rw [hflat]
          exact List.mem_append.mpr (Or.inr (List.mem_toFinset.mp he₁)))
        have he₂' : e₂ ∈ es := mem_of_mem_smallEdgesOf (by
          rw [hflat]
          exact List.mem_append.mpr (Or.inr (List.mem_toFinset.mp he₂)))
        exact hdis he₁' he₂' hne
  -- 2. pieces pairwise edge-disjoint
  have hdisj : ∀ M₁ ∈ P, ∀ M₂ ∈ P, M₁ ≠ M₂ → Disjoint M₁ M₂ := by
    intro M₁ hM₁ M₂ hM₂ hne
    rw [hmemP] at hM₁ hM₂
    rcases hM₁ with hbig₁ | hsmall₁
    · rcases hbig₁ with ⟨e₁, heb₁, rfl⟩
      rcases hM₂ with hbig₂ | hsmall₂
      · rcases hbig₂ with ⟨e₂, heb₂, rfl⟩
        -- two singletons with distinct pieces: e₁ ≠ e₂
        rw [Finset.disjoint_left]
        intro x hx₁ hx₂
        simp at hx₁ hx₂
        exact hne (by rw [← hx₁, ← hx₂])
      · -- {e₁} vs a small piece
        rw [Finset.disjoint_left]
        intro x hx₁ hx₂
        -- x = e₁ and e₁ ∈ small piece: but e₁ is big, small piece has small edges
        have hxeq : x = e₁ := by simpa using hx₁
        subst x
        rcases hsmall₂ with hchunk₂ | rfl
        · rcases hchunk₂ with ⟨b₂, hb₂, rfl⟩
          have hsmall₂' : e₁ ∈ smallEdgesOf A es := by
            rw [hflat]
            exact List.mem_append.mpr (Or.inl (List.mem_flatten.mpr ⟨b₂, hb₂, List.mem_toFinset.mp hx₂⟩))
          -- e₁ is big: A ≤ size; small: size < A: contradiction
          have hb₁' : A ≤ edgeSize e₁ := bigEdgesOf_sizes e₁ heb₁
          have hs₁' : edgeSize e₁ < A := smallEdgesOf_sizes e₁ hsmall₂'
          omega
        · have hsmall₂' : e₁ ∈ smallEdgesOf A es := by
            rw [hflat]
            exact List.mem_append.mpr (Or.inr (List.mem_toFinset.mp hx₂))
          have hb₁' : A ≤ edgeSize e₁ := bigEdgesOf_sizes e₁ heb₁
          have hs₁' : edgeSize e₁ < A := smallEdgesOf_sizes e₁ hsmall₂'
          omega
    · -- M₁ is a small piece
      rcases hM₂ with hbig₂ | hsmall₂
      · rcases hbig₂ with ⟨e₂, heb₂, rfl⟩
        -- symmetric of previous: M₁ small, {e₂} big
        rw [Finset.disjoint_left]
        intro x hx₁ hx₂
        have hxeq : x = e₂ := by simpa using hx₂
        subst x
        rcases hsmall₁ with hchunk₁ | rfl
        · rcases hchunk₁ with ⟨b₁, hb₁, rfl⟩
          have hsmall₁' : e₂ ∈ smallEdgesOf A es := by
            rw [hflat]
            exact List.mem_append.mpr (Or.inl (List.mem_flatten.mpr ⟨b₁, hb₁, List.mem_toFinset.mp hx₁⟩))
          have hb₂' : A ≤ edgeSize e₂ := bigEdgesOf_sizes e₂ heb₂
          have hs₂' : edgeSize e₂ < A := smallEdgesOf_sizes e₂ hsmall₁'
          omega
        · have hsmall₁' : e₂ ∈ smallEdgesOf A es := by
            rw [hflat]
            exact List.mem_append.mpr (Or.inr (List.mem_toFinset.mp hx₁))
          have hb₂' : A ≤ edgeSize e₂ := bigEdgesOf_sizes e₂ heb₂
          have hs₂' : edgeSize e₂ < A := smallEdgesOf_sizes e₂ hsmall₁'
          omega
      · -- both small: chunk/chunk, chunk/last, last/last
        rcases hsmall₁ with hchunk₁ | rfl
        · rcases hchunk₁ with ⟨b₁, hb₁, rfl⟩
          rcases hsmall₂ with hchunk₂ | rfl
          · rcases hchunk₂ with ⟨b₂, hb₂, rfl⟩
            -- distinct chunk pieces => distinct blocks
            have hbne : b₁ ≠ b₂ := by
              intro hbb
              apply hne
              simp [hbb]
            have hdisc := flatten_blocks_disjoint (init := init) (last := last)
              (by simpa [hflat] using (nodup_smallEdgesOf (A := A) hnodup)) (b₁ := b₁) hb₁ (b₂ := b₂) hb₂ hbne
            exact hdisc
          · -- chunk b₁ vs last
            have hdisc := flatten_blocks_disjoint_last (init := init) (last := last)
              (by simpa [hflat] using (nodup_smallEdgesOf (A := A) hnodup)) hb₁
            exact hdisc
        · rcases hsmall₂ with hchunk₂ | rfl
          · rcases hchunk₂ with ⟨b₂, hb₂, rfl⟩
            have hdisc := flatten_blocks_disjoint_last (init := init) (last := last)
              (by simpa [hflat] using (nodup_smallEdgesOf (A := A) hnodup)) hb₂
            exact hdisc.symm
          · -- last vs last
            exact (hne rfl).elim
  -- 3. cover
  have hcover : ∀ e : Set (Fin n), e ∈ es → ∃ M ∈ P, e ∈ M := by
    intro e he
    by_cases hbig : A ≤ edgeSize e
    · -- big: the singleton {e} is a piece
      refine ⟨({e} : Finset (Set (Fin n))), ?_, by simp⟩
      rw [hmemP]
      left
      exact ⟨e, by simp [mem_bigEdgesOf, he, hbig], rfl⟩
    · -- small: e lies in a chunk or the leftover
      have hlt : edgeSize e < A := lt_of_not_ge hbig
      have hesmall : e ∈ smallEdgesOf A es := by
        simp [mem_smallEdgesOf, he, hlt]
      have hflatmem : e ∈ init.flatten ++ last := by
        rwa [← hflat]
      rcases List.mem_append.mp hflatmem with heinit | helast
      · rcases List.mem_flatten.mp heinit with ⟨b, hb, heb⟩
        refine ⟨b.toFinset, ?_, List.mem_toFinset.mpr heb⟩
        rw [hmemP]
        right
        left
        exact ⟨b, hb, rfl⟩
      · refine ⟨last.toFinset, ?_, List.mem_toFinset.mpr helast⟩
        rw [hmemP]
        right
        right
        rfl
  exact ⟨P, hmatching, hdisj, hcover⟩

/-!
## Step (3): coverage of the pieces at the real thresholds

For `A = SplitThreshold α n = ⌈αn/2⌉` the piece coverage bounds translate to
reals: chunks of `smallEdgesOf A es` cover at least `αn/2` and less than
`αn + 1` vertices (`chunk_bounds_splitthreshold`; the `+1` is the margin
that the global parameter choice must absorb, cf. `SplitThreshold_upper`),
and a singleton big edge covers at least `αn/2`
(`singleton_piece_coverage_real`).  `cast_two_mul_sub_one` is the cast
hygiene between the natural chunk bound `2A−1` and the real one.
-/

/-- Casting: `((2A−1) : ℕ) = 2·A − 1` in the reals, for `A ≥ 1`. -/
lemma cast_two_mul_sub_one {A : ℕ} (hA : 1 ≤ A) :
    ((2 * A - 1 : ℕ) : ℝ) = 2 * (A : ℝ) - 1 := by
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * A), Nat.cast_mul]
  norm_num

/-- Real coverage of a chunk from its integer bounds. -/
theorem chunk_list_coverage_real {n : ℕ} {α : ℝ} {A : ℕ} {b : List (Set (Fin n))}
    (hAlow : (α / 2 : ℝ) * (n : ℝ) ≤ (A : ℝ))
    (hAup : ((2 * A - 1 : ℕ) : ℝ) < (α : ℝ) * (n : ℝ) + 1)
    (hcovL : A ≤ (listCovered b).ncard) (hcovU : (listCovered b).ncard ≤ 2 * A - 1) :
    (α / 2 : ℝ) * (n : ℝ) ≤ ((listCovered b).ncard : ℝ) ∧
    ((listCovered b).ncard : ℝ) < (α : ℝ) * (n : ℝ) + 1 := by
  constructor
  · exact hAlow.trans (by exact_mod_cast hcovL)
  · exact (by exact_mod_cast hcovU : ((listCovered b).ncard : ℝ) ≤
      ((2 * A - 1 : ℕ) : ℝ)).trans_lt hAup

/-- Chunks of the small edges, with real coverage bounds, at the threshold
`A = SplitThreshold α n`. -/
theorem chunk_bounds_splitthreshold {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (hA1 : 1 ≤ SplitThreshold α n) (es : List (Set (Fin n))) (hnodup : es.Nodup)
    (hdis : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ es → e₂ ∈ es → e₁ ≠ e₂ → Disjoint e₁ e₂)
    (hpos : ∀ e ∈ es, 1 ≤ edgeSize e) :
    ∃ (init : List (List (Set (Fin n)))) (last : List (Set (Fin n))),
      smallEdgesOf (SplitThreshold α n) es = init.flatten ++ last ∧
      (∀ b ∈ init,
        (α / 2 : ℝ) * (n : ℝ) ≤ ((listCovered b).ncard : ℝ) ∧
        ((listCovered b).ncard : ℝ) < (α : ℝ) * (n : ℝ) + 1) ∧
      (listCovered last).ncard < SplitThreshold α n := by
  classical
  rcases chunk_small_edges hA1 es hnodup hdis hpos with ⟨init, last, hflat, hblk, hlast⟩
  refine ⟨init, last, hflat, ?_, hlast⟩
  intro b hb
  rcases hblk b hb with ⟨_hbne, hbL, hbU⟩
  have hAlow := SplitThreshold_lower α n
  have hAup := SplitThreshold_upper (α := α) (n := n) (hα := hα)
  constructor
  · have hcast : (SplitThreshold α n : ℝ) ≤ ((listCovered b).ncard : ℝ) := by
      exact_mod_cast hbL
    exact hAlow.trans hcast
  · have hcast : ((listCovered b).ncard : ℝ) ≤
        ((2 * SplitThreshold α n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hbU
    have hEq := cast_two_mul_sub_one (A := SplitThreshold α n) hA1
    have hup' : ((2 * SplitThreshold α n - 1 : ℕ) : ℝ) < (α : ℝ) * (n : ℝ) + 1 := by
      rw [hEq]
      exact hAup
    exact hcast.trans_lt hup'

/-- A singleton big edge covers at least `αn/2` vertices (real). -/
theorem singleton_piece_coverage_real {n : ℕ} {α : ℝ} {A : ℕ} {e : Set (Fin n)}
    (hAlow : (α / 2 : ℝ) * (n : ℝ) ≤ (A : ℝ)) (he : A ≤ edgeSize e) :
    (α / 2 : ℝ) * (n : ℝ) ≤ (FamilyVertexCount ({e} : Finset (Set (Fin n))) : ℝ) := by
  have hcov : FamilyVertexCount ({e} : Finset (Set (Fin n))) = edgeSize e := by
    calc
      FamilyVertexCount ({e} : Finset (Set (Fin n))) = e.ncard := FamilyVertexCount_singleton e
      _ = edgeSize e := (edgeSize_eq_ncard e).symm
  have hcast : (A : ℝ) ≤ (edgeSize e : ℝ) := by exact_mod_cast he
  rw [hcov]
  exact hAlow.trans hcast

/-!
## Step (4): pieces at `A = SplitThreshold α n` — margin-tolerant form

The final bundling needs every piece of `colour_edges_split_witness` to
satisfy the real bounds.  The chunk pieces only give the upper bound
`< αn + 1` (not `≤ αn`) — the `+1` margin documented at `SplitThreshold_upper`.
`PieceOKMargin` is the margin-tolerant working form of `PieceOK` (upper
disjunct `< αn + 1` instead of `≤ αn`); once the global parameter hierarchy
fixes the convention (either absorbing the margin or restating the upper
disjunct), these results transfer to the strict `PieceOK α` statement.
`chunk_piece_PieceOKMargin` turns a chunk into such a piece.
-/

/-- Margin-tolerant admissible piece: a matching covering at least `αn/2`
vertices, whose upper bound is `≤ αn` when it is a singleton and `< αn + 1`
otherwise (the `+1` is the deferred margin). -/
def PieceOKMargin (α : ℝ) (M : Finset (Set (Fin n))) : Prop :=
  IsMatchingFamily M ∧ CoversAtLeast α M ∧
    (M.card = 1 ∨ (FamilyVertexCount M : ℝ) < (α : ℝ) * (n : ℝ) + 1)

/-- A chunk (nodup, disjoint, integer coverage in `[A, 2A−1]` with
`A = SplitThreshold α n`) is a matching Finset piece with real coverage in
`[αn/2, αn+1)`. -/
theorem chunk_finset_piece_bounds {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (hA1 : 1 ≤ SplitThreshold α n) {b : List (Set (Fin n))} (_hn : b.Nodup)
    (hdis : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ b → e₂ ∈ b → e₁ ≠ e₂ → Disjoint e₁ e₂)
    (hcovL : SplitThreshold α n ≤ (listCovered b).ncard)
    (hcovU : (listCovered b).ncard ≤ 2 * SplitThreshold α n - 1) :
    IsMatchingFamily (b.toFinset) ∧
    (α / 2 : ℝ) * (n : ℝ) ≤ (FamilyVertexCount (b.toFinset) : ℝ) ∧
    (FamilyVertexCount (b.toFinset) : ℝ) < (α : ℝ) * (n : ℝ) + 1 := by
  classical
  have hm : IsMatchingFamily (b.toFinset) := by
    intro e₁ e₂ he₁ he₂ hne
    exact hdis (List.mem_toFinset.mp he₁) (List.mem_toFinset.mp he₂) hne
  have hcov : FamilyVertexCount (b.toFinset) = (listCovered b).ncard :=
    FamilyVertexCount_toFinset b
  refine ⟨hm, ?_, ?_⟩
  · rw [hcov]
    exact (SplitThreshold_lower α n).trans (by exact_mod_cast hcovL)
  · rw [hcov]
    have hcast : ((listCovered b).ncard : ℝ) ≤
        ((2 * SplitThreshold α n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hcovU
    have hup' : ((2 * SplitThreshold α n - 1 : ℕ) : ℝ) < (α : ℝ) * (n : ℝ) + 1 := by
      rw [cast_two_mul_sub_one (A := SplitThreshold α n) hA1]
      exact SplitThreshold_upper (α := α) (n := n) hα
    exact hcast.trans_lt hup'

/-- A chunk is a margin-tolerant admissible piece. -/
theorem chunk_piece_PieceOKMargin {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (hA1 : 1 ≤ SplitThreshold α n) {b : List (Set (Fin n))} (hn : b.Nodup)
    (hdis : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ b → e₂ ∈ b → e₁ ≠ e₂ → Disjoint e₁ e₂)
    (hcovL : SplitThreshold α n ≤ (listCovered b).ncard)
    (hcovU : (listCovered b).ncard ≤ 2 * SplitThreshold α n - 1) :
    PieceOKMargin α (b.toFinset) := by
  classical
  rcases chunk_finset_piece_bounds hα hA1 hn hdis hcovL hcovU with ⟨hm, hlow, hup⟩
  exact ⟨hm, hlow, Or.inr hup⟩

/-- A singleton edge of size at least `A = SplitThreshold α n` is a
margin-tolerant piece via its singleton disjunct. -/
theorem singleton_piece_PieceOKMargin {n : ℕ} {α : ℝ} {e : Set (Fin n)}
    (he : (α / 2 : ℝ) * (n : ℝ) ≤ (edgeSize e : ℝ)) :
    PieceOKMargin α ({e} : Finset (Set (Fin n))) := by
  classical
  rcases singleton_piece_vertex (α := α) (e := e) he with ⟨hm, hcov, hsing⟩
  exact ⟨hm, hcov, Or.inl hsing⟩

/-!
## Per-origin piece properties for the witness

The destruct over the origin of a piece of `P` needs one lemma per origin:
singletons of `bigEdgesOf A es` are `PieceOKMargin` pieces
(`bigEdgesOf_piece_PieceOKMargin`), chunks of `smallEdgesOf A es` are
`PieceOKMargin` pieces (`chunk_pieces_PieceOKMargin`), and the leftover is a
matching (`leftover_finset_matching`).  The witness-level theorem assembles
these with the partition/union facts of `colour_edges_split_witness`.
-/
/-- A block of a Nodup flatten decomposition is Nodup. -/
lemma nodup_of_mem_flatten_blocks {α : Type*} {init : List (List α)} {b : List α}
    (hb : b ∈ init) (h : init.flatten.Nodup) : b.Nodup := by
  induction init with
  | nil => cases hb
  | cons x xs ih =>
      rcases (List.mem_cons.mp hb) with hEq | hb'
      · subst b
        exact nodup_of_append_left x xs.flatten h
      · exact ih hb' (nodup_of_append_right x xs.flatten h)

/-- A singleton of a big edge is a margin-tolerant piece. -/
theorem bigEdgesOf_piece_PieceOKMargin {n : ℕ} {α : ℝ}
    {es : List (Set (Fin n))} {e : Set (Fin n)} (he : e ∈ bigEdgesOf (SplitThreshold α n) es) :
    PieceOKMargin α ({e} : Finset (Set (Fin n))) := by
  classical
  have hsz : SplitThreshold α n ≤ edgeSize e :=
    bigEdgesOf_sizes (A := SplitThreshold α n) (es := es) e he
  have hlow : (α / 2 : ℝ) * (n : ℝ) ≤ (edgeSize e : ℝ) :=
    (SplitThreshold_lower α n).trans (by exact_mod_cast hsz)
  exact singleton_piece_PieceOKMargin (n := n) (α := α) (e := e) hlow

/-- The chunks of the small edges are margin-tolerant pieces (with the
decomposition and the leftover). -/
theorem chunk_pieces_PieceOKMargin {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (hA1 : 1 ≤ SplitThreshold α n) (es : List (Set (Fin n))) (hnodup : es.Nodup)
    (hdis : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ es → e₂ ∈ es → e₁ ≠ e₂ → Disjoint e₁ e₂)
    (hpos : ∀ e ∈ es, 1 ≤ edgeSize e) :
    ∃ (init : List (List (Set (Fin n)))) (last : List (Set (Fin n))),
      smallEdgesOf (SplitThreshold α n) es = init.flatten ++ last ∧
      (∀ b ∈ init, PieceOKMargin α (b.toFinset)) ∧
      (listCovered last).ncard < SplitThreshold α n := by
  classical
  rcases chunk_small_edges hA1 es hnodup hdis hpos with ⟨init, last, hflat, hblk, hlast⟩
  refine ⟨init, last, hflat, ?_, hlast⟩
  intro b hb
  rcases hblk b hb with ⟨_hbne, hbL, hbU⟩
  have hnodupB : b.Nodup := nodup_of_mem_flatten_blocks hb (by
    exact nodup_of_append_left init.flatten last (by simpa [hflat] using (nodup_smallEdgesOf (A := SplitThreshold α n) hnodup)))
  have hdisB : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ b → e₂ ∈ b → e₁ ≠ e₂ → Disjoint e₁ e₂ := by
    intro e₁ e₂ he₁ he₂ hne
    have h₁ : e₁ ∈ smallEdgesOf (SplitThreshold α n) es := by
      rw [hflat]
      exact List.mem_append.mpr (Or.inl (List.mem_flatten.mpr ⟨b, hb, he₁⟩))
    have h₂ : e₂ ∈ smallEdgesOf (SplitThreshold α n) es := by
      rw [hflat]
      exact List.mem_append.mpr (Or.inl (List.mem_flatten.mpr ⟨b, hb, he₂⟩))
    exact hdis (mem_of_mem_smallEdgesOf h₁) (mem_of_mem_smallEdgesOf h₂) hne
  exact chunk_piece_PieceOKMargin hα hA1 hnodupB hdisB hbL hbU

/-- The leftover of the small edges is a matching. -/
theorem leftover_finset_matching {n A : ℕ} {es : List (Set (Fin n))}
    {init : List (List (Set (Fin n)))} {last : List (Set (Fin n))}
    (hflat : smallEdgesOf A es = init.flatten ++ last)
    (hdis : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ es → e₂ ∈ es → e₁ ≠ e₂ → Disjoint e₁ e₂) :
    IsMatchingFamily (last.toFinset) := by
  classical
  intro e₁ e₂ he₁ he₂ hne
  have h₁ : e₁ ∈ smallEdgesOf A es := by
    rw [hflat]
    exact List.mem_append.mpr (Or.inr (List.mem_toFinset.mp he₁))
  have h₂ : e₂ ∈ smallEdgesOf A es := by
    rw [hflat]
    exact List.mem_append.mpr (Or.inr (List.mem_toFinset.mp he₂))
  exact hdis (mem_of_mem_smallEdgesOf h₁) (mem_of_mem_smallEdgesOf h₂) hne

/-- The witness with margin-tolerant piece properties: pieces `P` (singletons
of the big edges and chunks of the small edges) are pairwise edge-disjoint
`PieceOKMargin` matchings, the leftover `left` is a matching edge-disjoint
from every piece, and together they cover exactly the edges of `es`. -/
theorem colour_edges_split_witness_piece_PieceOKMargin {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (hA1 : 1 ≤ SplitThreshold α n) (es : List (Set (Fin n))) (hnodup : es.Nodup)
    (hdis : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ es → e₂ ∈ es → e₁ ≠ e₂ → Disjoint e₁ e₂)
    (hpos : ∀ e ∈ es, 1 ≤ edgeSize e) :
    ∃ (P : Finset (Finset (Set (Fin n)))) (left : Finset (Set (Fin n))),
      (∀ M ∈ P, PieceOKMargin α M) ∧
      (∀ M₁ ∈ P, ∀ M₂ ∈ P, M₁ ≠ M₂ → Disjoint M₁ M₂) ∧
      (∀ M ∈ P, Disjoint M left) ∧
      IsMatchingFamily left ∧
      FamilyVertexCount left < SplitThreshold α n ∧
      (∀ e : Set (Fin n), e ∈ es ↔ (∃ M ∈ P, e ∈ M) ∨ e ∈ left) := by
  classical
  rcases chunk_pieces_PieceOKMargin hα hA1 es hnodup hdis hpos with ⟨init, last, hflat, hchunkOK, hlast⟩
  let A : ℕ := SplitThreshold α n
  let Pbig : Finset (Finset (Set (Fin n))) :=
    (bigEdgesOf A es).toFinset.image (fun e : Set (Fin n) => ({e} : Finset (Set (Fin n))))
  let Pchunk : Finset (Finset (Set (Fin n))) :=
    init.toFinset.image (fun b : List (Set (Fin n)) => b.toFinset)
  let P : Finset (Finset (Set (Fin n))) := Pbig ∪ Pchunk
  let left : Finset (Set (Fin n)) := last.toFinset
  have hmemP : ∀ M : Finset (Set (Fin n)), M ∈ P ↔
      (∃ e ∈ bigEdgesOf A es, M = ({e} : Finset (Set (Fin n)))) ∨
      (∃ b ∈ init, M = b.toFinset) := by
    intro M
    simp [P, Pbig, Pchunk]
    aesop
  -- 1. every piece is a PieceOKMargin piece
  have hpieceOK : ∀ M ∈ P, PieceOKMargin α M := by
    intro M hM
    rw [hmemP] at hM
    rcases hM with hbig | hchunk
    · rcases hbig with ⟨e, he, rfl⟩
      have hsz : A ≤ edgeSize e := by
        dsimp [A]
        exact bigEdgesOf_sizes (A := SplitThreshold α n) (es := es) e he
      have hlow : (α / 2 : ℝ) * (n : ℝ) ≤ (edgeSize e : ℝ) :=
        (SplitThreshold_lower α n).trans (by exact_mod_cast hsz)
      exact singleton_piece_PieceOKMargin (n := n) (α := α) (e := e) hlow
    · rcases hchunk with ⟨b, hb, rfl⟩
      exact hchunkOK b hb
  -- 2. pieces pairwise edge-disjoint
  have hdisjP : ∀ M₁ ∈ P, ∀ M₂ ∈ P, M₁ ≠ M₂ → Disjoint M₁ M₂ := by
    intro M₁ hM₁ M₂ hM₂ hne
    rw [hmemP] at hM₁ hM₂
    rcases hM₁ with hbig₁ | hchunk₁
    · rcases hbig₁ with ⟨e₁, heb₁, rfl⟩
      rcases hM₂ with hbig₂ | hchunk₂
      · rcases hbig₂ with ⟨e₂, heb₂, rfl⟩
        rw [Finset.disjoint_left]
        intro x hx₁ hx₂
        simp at hx₁ hx₂
        exact hne (by rw [← hx₁, ← hx₂])
      · rw [Finset.disjoint_left]
        intro x hx₁ hx₂
        have hxeq : x = e₁ := by simpa using hx₁
        subst x
        rcases hchunk₂ with ⟨b₂, hb₂, rfl⟩
        have hsmall₂' : e₁ ∈ smallEdgesOf A es := by
          dsimp [A]
          rw [hflat]
          exact List.mem_append.mpr (Or.inl (List.mem_flatten.mpr ⟨b₂, hb₂, List.mem_toFinset.mp hx₂⟩))
        have hb₁' : A ≤ edgeSize e₁ := by
          dsimp [A]
          exact bigEdgesOf_sizes (A := SplitThreshold α n) (es := es) e₁ heb₁
        have hs₁' : edgeSize e₁ < A := by
          dsimp [A]
          exact smallEdgesOf_sizes e₁ hsmall₂'
        omega
    · rcases hchunk₁ with ⟨b₁, hb₁, rfl⟩
      rcases hM₂ with hbig₂ | hchunk₂
      · rcases hbig₂ with ⟨e₂, heb₂, rfl⟩
        rw [Finset.disjoint_left]
        intro x hx₁ hx₂
        have hxeq : x = e₂ := by simpa using hx₂
        subst x
        have hsmall₁' : e₂ ∈ smallEdgesOf A es := by
          dsimp [A]
          rw [hflat]
          exact List.mem_append.mpr (Or.inl (List.mem_flatten.mpr ⟨b₁, hb₁, List.mem_toFinset.mp hx₁⟩))
        have hb₂' : A ≤ edgeSize e₂ := by
          dsimp [A]
          exact bigEdgesOf_sizes (A := SplitThreshold α n) (es := es) e₂ heb₂
        have hs₂' : edgeSize e₂ < A := by
          dsimp [A]
          exact smallEdgesOf_sizes e₂ hsmall₁'
        omega
      · rcases hchunk₂ with ⟨b₂, hb₂, rfl⟩
        have hbne : b₁ ≠ b₂ := by
          intro hbb
          apply hne
          simp [hbb]
        have hdisc := flatten_blocks_disjoint (init := init) (last := last)
          (by simpa [hflat] using (nodup_smallEdgesOf (A := SplitThreshold α n) hnodup)) hb₁ hb₂ hbne
        exact hdisc
  -- 3. pieces are edge-disjoint from the leftover
  have hdisjL : ∀ M ∈ P, Disjoint M left := by
    intro M hM
    rw [hmemP] at hM
    rcases hM with hbig | hchunk
    · rcases hbig with ⟨e, heb, rfl⟩
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      have hxeq : x = e := by simpa using hx₁
      subst x
      have hsmall' : e ∈ smallEdgesOf A es := by
        dsimp [A]
        rw [hflat]
        exact List.mem_append.mpr (Or.inr (List.mem_toFinset.mp hx₂))
      have hb' : A ≤ edgeSize e := by
        dsimp [A]
        exact bigEdgesOf_sizes (A := SplitThreshold α n) (es := es) e heb
      have hs' : edgeSize e < A := by
        dsimp [A]
        exact smallEdgesOf_sizes e hsmall'
      omega
    · rcases hchunk with ⟨b, hb, rfl⟩
      have hdisc := flatten_blocks_disjoint_last (init := init) (last := last)
        (by simpa [hflat] using (nodup_smallEdgesOf (A := SplitThreshold α n) hnodup)) hb
      dsimp [left]
      exact hdisc
  -- 4. the leftover is a matching
  have hmatchL : IsMatchingFamily left := by
    dsimp [left]
    exact leftover_finset_matching hflat hdis
  -- 5. cover: each edge of es is in a piece or the leftover, and conversely
  have hcover : ∀ e : Set (Fin n), e ∈ es ↔ (∃ M ∈ P, e ∈ M) ∨ e ∈ left := by
    intro e
    constructor
    · intro he
      by_cases hbig : A ≤ edgeSize e
      · left
        refine ⟨({e} : Finset (Set (Fin n))), ?_, by simp⟩
        rw [hmemP]
        left
        exact ⟨e, by simp [mem_bigEdgesOf, he, hbig], rfl⟩
      · have hlt : edgeSize e < A := lt_of_not_ge hbig
        have hesmall : e ∈ smallEdgesOf A es := by
          simp [mem_smallEdgesOf, he, hlt]
        have hflatmem : e ∈ init.flatten ++ last := by
          dsimp [A] at hesmall
          rwa [hflat] at hesmall
        rcases List.mem_append.mp hflatmem with heinit | helast
        · left
          rcases List.mem_flatten.mp heinit with ⟨b, hb, heb⟩
          refine ⟨b.toFinset, ?_, List.mem_toFinset.mpr heb⟩
          rw [hmemP]
          right
          exact ⟨b, hb, rfl⟩
        · right
          dsimp [left]
          exact List.mem_toFinset.mpr helast
    · intro h
      rcases h with hP | hleft
      · rcases hP with ⟨M, hM, heM⟩
        rw [hmemP] at hM
        rcases hM with hbig | hchunk
        · rcases hbig with ⟨e', he', rfl⟩
          have hx : e = e' := by simpa using heM
          subst e
          exact mem_of_mem_bigEdgesOf he'
        · rcases hchunk with ⟨b, hb, rfl⟩
          have hb' : e ∈ smallEdgesOf A es := by
            dsimp [A]
            rw [hflat]
            exact List.mem_append.mpr (Or.inl (List.mem_flatten.mpr ⟨b, hb, List.mem_toFinset.mp heM⟩))
          exact mem_of_mem_smallEdgesOf hb'
      · have hleft' : e ∈ last := List.mem_toFinset.mp (by simpa [left] using hleft)
        have hesmall : e ∈ smallEdgesOf A es := by
          dsimp [A]
          rw [hflat]
          exact List.mem_append.mpr (Or.inr hleft')
        exact mem_of_mem_smallEdgesOf hesmall
  have hLeftCov : FamilyVertexCount left < SplitThreshold α n := by
    change FamilyVertexCount last.toFinset < SplitThreshold α n
    rw [← FamilyVertexCount_toFinset (b := last)] at hlast
    exact hlast
  refine ⟨P, left, hpieceOK, hdisjP, hdisjL, hmatchL, hLeftCov, hcover⟩

/-!
## Colour-class lifting (margin form)

`SplitColourClassMarginStatement` is the colour-class version of the split:
every colour class of a proper edge-colouring decomposes into `PieceOKMargin`
pieces plus a matching leftover, pieces pairwise edge-disjoint and
edge-disjoint from the leftover, covering the class exactly.  It is obtained
by feeding the colour-class edge list (the `val` of `EdgeSetFamily
(φ.colorClass c)`) into `colour_edges_split_witness_piece_PieceOKMargin`;
the strict `PieceOK`/no-leftover form is **false** in corner cases (see the
warning at `SplitColourClassStatement`); the honest provable packaging of
this output is `SplitColourClassHonest` / `splitColourClassHonest` in
`ColourClassSplitHonest.lean` (pieces + leftover, count `2/α + 1`).
-/

/-- The colour-class splitting statement in margin-tolerant form. -/
def SplitColourClassMarginStatement (n : ℕ) (α : ℝ) (𝓗 : Hypergraph (Fin n)) : Prop :=
  ∀ (φ : 𝓗.Coloring (Fin n)) (c : Fin n),
    ∃ (P : Finset (Finset (Set (Fin n)))) (left : Finset (Set (Fin n))),
      (∀ M ∈ P, PieceOKMargin α M) ∧
      (∀ M₁ ∈ P, ∀ M₂ ∈ P, M₁ ≠ M₂ → Disjoint M₁ M₂) ∧
      (∀ M ∈ P, Disjoint M left) ∧
      IsMatchingFamily left ∧
      FamilyVertexCount left < SplitThreshold α n ∧
      (∀ e : Set (Fin n), e ∈ EdgeSetFamily (φ.colorClass c) ↔
        (∃ M ∈ P, e ∈ M) ∨ e ∈ left)

/-- Every colour class of a proper edge-colouring of a hypergraph with
positive edge sizes splits into margin-tolerant pieces plus a matching
leftover. -/
theorem splitColourClassMargin {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (hA1 : 1 ≤ SplitThreshold α n) {𝓗 : Hypergraph (Fin n)}
    (hpos : ∀ e ∈ 𝓗, 1 ≤ edgeSize e) :
    SplitColourClassMarginStatement n α 𝓗 := by
  classical
  intro φ c
  let F : Finset (Set (Fin n)) := EdgeSetFamily (φ.colorClass c)
  have hM : IsMatchingFamily F :=
    IsMatchingFamily_of_IsMatching (Hypergraph.Coloring.colorClass_isMatching φ c)
  have hdisList : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ F.toList → e₂ ∈ F.toList → e₁ ≠ e₂ → Disjoint e₁ e₂ := by
    intro e₁ e₂ he₁ he₂ hne
    exact hM (Finset.mem_toList.mp he₁) (Finset.mem_toList.mp he₂) hne
  have hposList : ∀ e ∈ F.toList, 1 ≤ edgeSize e := by
    intro e he
    have heF : e ∈ F := Finset.mem_toList.mp he
    have heFam : e ∈ EdgeSetFamily (φ.colorClass c) := by simpa [F] using heF
    rcases (mem_EdgeSetFamily (φ.colorClass c) e).1 heFam with ⟨x, _hx, hx'⟩
    have hposx : 1 ≤ edgeSize (x : Set (Fin n)) := hpos (x : Set (Fin n)) x.2
    rwa [hx'] at hposx
  rcases colour_edges_split_witness_piece_PieceOKMargin (n := n) (α := α) hα hA1
    (es := F.toList) (Finset.nodup_toList F) hdisList hposList with
    ⟨P, left, hOK, hDisjP, hDisjL, hMatchL, hLeftCov, hcover⟩
  refine ⟨P, left, hOK, hDisjP, hDisjL, hMatchL, hLeftCov, ?_⟩
  intro e
  have hc := hcover e
  have h1 : e ∈ F ↔ e ∈ F.toList := Finset.mem_toList.symm
  simpa [F] using (h1.trans hc)

/-!
## Leftover folding: exact "exactly once" form

`colour_edges_split_witness_piece_PieceOKMargin` gives pieces `P` plus a
matching leftover `left`, each edge of the class being in some piece or the
leftover, with pieces pairwise edge-disjoint and edge-disjoint from the
leftover.  Folding the leftover into `P` as one more piece
(`P' = insert left P`) gives the exact "every edge lies in exactly one
piece" (`∃!`) form: cover is preserved and uniqueness follows from the
disjointness.  (The leftover piece is the exceptional one that the paper
handles by its own absorption arguments; the strict `≤ αn` upper bound of
`PieceOK` is the separate `+1` margin convention, recorded at
`SplitThreshold_upper`.)
-/

/-- With pieces pairwise edge-disjoint and edge-disjoint from the leftover,
an edge in a piece or the leftover lies in exactly one piece of
`insert left P`. -/
theorem fold_leftover_exactly_once {n : ℕ}
    (P : Finset (Finset (Set (Fin n)))) (left : Finset (Set (Fin n)))
    (hdisjP : ∀ M₁ ∈ P, ∀ M₂ ∈ P, M₁ ≠ M₂ → Disjoint M₁ M₂)
    (hdisjL : ∀ M ∈ P, Disjoint M left) :
    ∀ e : Set (Fin n), (∃ M ∈ P, e ∈ M) ∨ e ∈ left →
      ∃! M : Finset (Set (Fin n)), M ∈ insert left P ∧ e ∈ M := by
  classical
  intro e h
  have uniqArg : ∀ (W : Finset (Set (Fin n))), W ∈ insert left P → e ∈ W →
      ∀ (y : Finset (Set (Fin n))), y ∈ insert left P → e ∈ y → y = W := by
    intro W hW eW y hy ey
    simp at hW hy
    -- hW : W = left ∨ W ∈ P ; hy : y = left ∨ y ∈ P
    rcases hW with hWl | hWp
    · subst hWl
      rcases hy with hyl | hyp
      · subst hyl
        rfl
      · exfalso
        have hd := hdisjL y hyp
        rw [Finset.disjoint_left] at hd
        exact (hd ey) eW
    · rcases hy with hyl | hyp
      · subst hyl
        exfalso
        have hd := hdisjL W hWp
        rw [Finset.disjoint_left] at hd
        exact (hd eW) ey
      · by_contra hne
        have hne' : W ≠ y := by
          intro hWy
          exact hne hWy.symm
        have hd := hdisjP W hWp y hyp hne'
        rw [Finset.disjoint_left] at hd
        exact (hd eW) ey
  rcases h with hP | hleft
  · rcases hP with ⟨W, hW, eW⟩
    refine ⟨W, ?_, ?_⟩
    · exact ⟨by simp [hW], eW⟩
    · intro y hy
      exact uniqArg W (by simp [hW]) eW y hy.1 hy.2
  · refine ⟨left, ?_, ?_⟩
    · exact ⟨by simp, hleft⟩
    · intro y hy
      exact uniqArg left (by simp) hleft y hy.1 hy.2

/-!
## Strict form: every edge in exactly one matching piece

The transfer we can prove without extra conventions folds the leftover into
`P` as an explicit piece (`P' = insert left P`): every edge of the colour
class lies in exactly one piece of `P'`, and every piece (including the
leftover) is a matching.  The remaining strict `PieceOK` bounds (`≤ αn`
upper; `≥ αn/2` lower for the leftover piece) are the two convention points
recorded at `SplitThreshold_upper` and in the margin discussion: they become
provable once the working parameter carries the margin (equivalently after
re-chunking the small edges by a real maximal prefix `≤ αn`).
-/

/-- Every colour class of a proper edge-colouring of a hypergraph with
positive edge sizes is partitioned, by the margin machinery, into pairwise
edge-disjoint matching pieces, with every edge in exactly one piece. -/
theorem splitColourClass_exactlyOnce {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (hA1 : 1 ≤ SplitThreshold α n) {𝓗 : Hypergraph (Fin n)}
    (hpos : ∀ e ∈ 𝓗, 1 ≤ edgeSize e) :
    ∀ (φ : 𝓗.Coloring (Fin n)) (c : Fin n),
      ∃ P' : Finset (Finset (Set (Fin n))),
        (∀ M ∈ P', IsMatchingFamily M) ∧
        (∀ e : Set (Fin n), e ∈ EdgeSetFamily (φ.colorClass c) →
          ∃! M : Finset (Set (Fin n)), M ∈ P' ∧ e ∈ M) := by
  classical
  intro φ c
  rcases splitColourClassMargin hα hA1 (𝓗 := 𝓗) hpos φ c with ⟨P, left, hOK, hDisjP, hDisjL, hMatchL, _hLeftCov, hcover⟩
  let P' : Finset (Finset (Set (Fin n))) := insert left P
  refine ⟨P', ?_, ?_⟩
  · intro M hM
    dsimp [P'] at hM
    simp at hM
    rcases hM with rfl | hM
    · exact hMatchL
    · exact (hOK M hM).1
  · intro e he
    -- membership gives existence, disjointness gives uniqueness
    have hc := (hcover e).1 he
    exact fold_leftover_exactly_once P left hDisjP hDisjL e hc
