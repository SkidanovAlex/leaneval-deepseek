import Mathlib

open scoped Simplicial

/-!
# The `(p,q)`-shuffle index

A `(p,q)`-shuffle (a lattice path from `(0,0)` to `(p,q)`) is encoded by the set `S` of positions of
the `q` "`N`-steps" among the `p+q` steps.  For a vertex `i` of `⦋p+q⦌` the number of `N`-steps
before `i` is `pB S i` and the number of `E`-steps before `i` is `pA S i`; the pair of monotone maps
`(aHom S, bHom S) : ⦋p+q⦌ ⟶ ⦋p⦌ × ⦋q⦌` is the corresponding maximal simplex of the prism
`Δ[p] × Δ[q]`, and the twenty `(3,3)`-shuffles are the case `p = q = 3`.

This file is self-contained: it contains only the combinatorial index and the basic value lemmas,
so that the Eilenberg–Zilber shuffle chain and its chain-map (prism cancellation) property can be
stated and split into sub-lemmas without depending on any in-flight definition of the shuffle.

## Main definitions and results

* `PShuffle p q` — the type of `(p,q)`-shuffles;
* `pA`, `pB` — the `E`- and `N`-counts before a vertex, with `pA_monotone`, `pB_monotone`,
  `pB_le`, `pA_le` bounding them by `q` and `p`;
* `aHom`, `bHom` — the two monotone maps `⦋p+q⦌ ⟶ ⦋p⦌`, `⦋p+q⦌ ⟶ ⦋q⦌` with the value lemmas
  `aHom_val`, `bHom_val`;
* `invCount`, `shufSign` — the number of pairs (an `N`-step before an `E`-step) and the
  Eilenberg–Zilber sign `(-1)^invCount` of a shuffle (`pB` counts the `N`-steps, so this is the
  sign of the associated shuffle permutation).
-/

namespace Work.Cohomology.Crux33

noncomputable section

/-- A `(p,q)`-shuffle: the positions of the `q` `N`-steps among the `p+q` steps. -/
abbrev PShuffle (p q : ℕ) : Type := {S : Finset (Fin (p + q)) // S.card = q}

variable {p q : ℕ}

/-- The number of `N`-steps before the vertex `i`. -/
def pB (S : Finset (Fin (p + q))) (i : Fin (p + q + 1)) : ℕ :=
  (S.filter (fun j => j.val < i.val)).card

/-- The number of `E`-steps before the vertex `i`. -/
def pA (S : Finset (Fin (p + q))) (i : Fin (p + q + 1)) : ℕ :=
  (((Finset.univ : Finset (Fin (p + q))).filter (fun j => j.val < i.val)) \ S).card

lemma pB_monotone (S : Finset (Fin (p + q))) : Monotone (pB S) := by
  intro i j hij
  refine Finset.card_le_card (fun x hx => ?_)
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, lt_of_lt_of_le hx.2 hij⟩

lemma pA_monotone (S : Finset (Fin (p + q))) : Monotone (pA S) := by
  intro i j hij
  refine Finset.card_le_card (fun x hx => ?_)
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact ⟨lt_of_lt_of_le hx.1 hij, hx.2⟩

lemma pB_le (S : Finset (Fin (p + q))) (hS : S.card = q) (i : Fin (p + q + 1)) : pB S i ≤ q :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hS

lemma pA_le (S : Finset (Fin (p + q))) (hS : S.card = q) (i : Fin (p + q + 1)) : pA S i ≤ p := by
  rw [pA]
  calc (((Finset.univ : Finset (Fin (p + q))).filter fun j => j.val < i.val) \ S).card
      ≤ ((Finset.univ : Finset (Fin (p + q))) \ S).card :=
        Finset.card_le_card (fun x hx => by
          simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact hx.2)
    _ = (p + q) - q := by
        rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ, hS]
    _ = p := by omega

lemma pB_zero (S : Finset (Fin (p + q))) : pB S ⟨0, by omega⟩ = 0 := by
  simp [pB]

lemma pB_last (S : Finset (Fin (p + q))) : pB S ⟨p + q, by omega⟩ = S.card := by
  rw [pB]
  congr 1
  ext j
  simp

lemma pA_zero (S : Finset (Fin (p + q))) : pA S ⟨0, by omega⟩ = 0 := by
  simp [pA]

/-- The number of `E`-steps before the vertex `i`, as a function of `i.val` (avoids the `Fin`
coercion in statements: `pANat S i.val = pA S i`). -/
def pANat (S : Finset (Fin (p + q))) (n : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin (p + q))).filter (fun j => j.val < n)) \ S).card

/-- The number of `N`-steps before the vertex `i`, as a function of `i.val`. -/
def pBNat (S : Finset (Fin (p + q))) (n : ℕ) : ℕ :=
  (S.filter (fun j => j.val < n)).card

@[simp] lemma pANat_apply (S : Finset (Fin (p + q))) (i : Fin (p + q + 1)) :
    pANat S i.val = pA S i := rfl

@[simp] lemma pBNat_apply (S : Finset (Fin (p + q))) (i : Fin (p + q + 1)) :
    pBNat S i.val = pB S i := rfl

/-- The `(p,q)`-shuffle as a map `⦋p+q⦌ ⟶ ⦋p⦌`: the number of `E`-steps taken. -/
def aHom (S : Finset (Fin (p + q))) (hS : S.card = q) : ⦋p + q⦌ ⟶ ⦋p⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨pA S i, by have := pA_le S hS i; simp only [SimplexCategory.len_mk]; omega⟩
      monotone' := fun _ _ hij => by
        simp only [Fin.le_def]
        exact pA_monotone S hij }

/-- The `(p,q)`-shuffle as a map `⦋p+q⦌ ⟶ ⦋q⦌`: the number of `N`-steps taken. -/
def bHom (S : Finset (Fin (p + q))) (hS : S.card = q) : ⦋p + q⦌ ⟶ ⦋q⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨pB S i, by have := pB_le S hS i; simp only [SimplexCategory.len_mk]; omega⟩
      monotone' := fun _ _ hij => by
        simp only [Fin.le_def]
        exact pB_monotone S hij }

@[simp] lemma aHom_val (S : Finset (Fin (p + q))) (hS : S.card = q) (i : Fin (p + q + 1)) :
    ((aHom S hS : ⦋p + q⦌ ⟶ ⦋p⦌) i).val = pA S i := rfl

@[simp] lemma bHom_val (S : Finset (Fin (p + q))) (hS : S.card = q) (i : Fin (p + q + 1)) :
    ((bHom S hS : ⦋p + q⦌ ⟶ ⦋q⦌) i).val = pB S i := rfl

/-- The number of "inversions" of a shuffle: the pairs (an `N`-step before an `E`-step), i.e.
`∑_{j ∉ S} #{s ∈ S : s < j}` (summing over the `E`-steps the `N`-steps before them).  Summing over
`S` instead would give the constant `q(q+1)/2`, making the sign identically `1`. -/
def invCount (S : Finset (Fin (p + q))) : ℕ :=
  ((Finset.univ : Finset (Fin (p + q))) \ S).sum (fun j => pBNat S j.val)

/-- The Eilenberg–Zilber sign of a `(p,q)`-shuffle. -/
def shufSign (S : Finset (Fin (p + q))) : ℤ := (-1 : ℤ) ^ invCount S

/-! ## Face identification for the `(3,3)`-shuffle

`aHom`/`bHom` are the `E`- and `N`-count maps of a shuffle; the front `3`-face of the shuffle cell
of the prism is the restriction of `aHom` to the first four vertices, and the back `3`-face of the
second coordinate is the restriction of `bHom` to the last four vertices.  The two facts below are
what makes the Eilenberg–Zilber shuffle computation work: the front face is injective exactly for
the shuffle `E E E N N N` (all `N`-steps last), and for that shuffle the back face is the identity.

There are only twenty `(3,3)`-shuffles, so both facts are settled by a finite check over
`Finset.powersetCard 3 Finset.univ`, and then transferred to an arbitrary `S` with `S.card = 3`.
-/

/-- The `E`-count map of a `(3,3)`-shuffle, at the canonical type `Fin 6`. -/
abbrev A6 (S : Finset (Fin 6)) (n : ℕ) : ℕ := pANat (p := 3) (q := 3) S n

/-- The `N`-count map of a `(3,3)`-shuffle, at the canonical type `Fin 6`. -/
abbrev B6 (S : Finset (Fin 6)) (n : ℕ) : ℕ := pBNat (p := 3) (q := 3) S n

/-- The Eilenberg–Zilber sign of a `(3,3)`-shuffle, at the canonical type `Fin 6`. -/
abbrev sign6 (S : Finset (Fin 6)) : ℤ := shufSign (p := 3) (q := 3) S

/-- **Finite check** over the twenty `(3,3)`-shuffles:

* the `E`-count map `pANat S` restricted to the first four vertices is injective iff all three
  `N`-steps are in the last three positions;
* for the shuffle `E E E N N N` (`S = {3,4,5}`) the `N`-count map on the last four vertices is the
  identity `i ↦ i`. -/
lemma shuffleFaceIdent_finite :
    ∀ S ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      ((∀ i j : Fin 4, A6 S i.val = A6 S j.val → i = j)
        ↔ (∀ j : Fin 6, j ∈ S ↔ 2 < j.val))
      ∧ ((∀ i : Fin 4, B6 S (3 + i.val) = i.val)
        ↔ (∀ j : Fin 6, j ∈ S ↔ 2 < j.val)) := by
  decide

/-- **Face identification for the `(3,3)`-shuffle.**

For a shuffle `S` (three `N`-positions among six steps):

* the front face (first four vertices) of the `E`-count map `aHom S` is injective **iff** all the
  `N`-steps are in the last three positions — equivalently, iff the shuffle is `E E E N N N`;
* for that shuffle the `N`-count map `bHom S` on the back face (last four vertices) is the identity.

Hence for every shuffle other than `E E E N N N` the front face of the first coordinate of the
shuffle cell is a non-injective monotone map, and the unique shuffle whose front and back faces are
both the identity is `E E E N N N`. -/
theorem shuffleFaceIdent (S : Finset (Fin 6)) (hS : S.card = 3) :
    ((∀ i j : Fin 4, A6 S i.val = A6 S j.val → i = j)
      ↔ (∀ j : Fin 6, j ∈ S ↔ 2 < j.val))
    ∧ ((∀ i : Fin 4, B6 S (3 + i.val) = i.val)
      ↔ (∀ j : Fin 6, j ∈ S ↔ 2 < j.val)) :=
  shuffleFaceIdent_finite S (by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hS⟩)
/-! ## The faces of a shuffle cell

The `j`-th face of the shuffle cell `(σ ∘ a_S, τ ∘ b_S)` is `(σ ∘ (a_S ∘ δ_j), τ ∘ (b_S ∘ δ_j))`,
and on vertices `δ_j` acts by `delV j k = if k < j then k else k + 1`.  So the pair of monotone
maps `(a_S ∘ δ_j, b_S ∘ δ_j)` is completely described by the two `ℕ`-valued functions
`k ↦ A6 S (delV j k)`, `k ↦ B6 S (delV j k)` on `k ∈ {0,…,5}`, which makes the first seam of the
coefficient computation — *which* pairs `(α, β)` arise, and with which total coefficient — a
finite `decide` check over the `20 × 7` pairs, exactly as `shuffleFaceIdent` was. -/

/-- The `j`-th face map on vertices: `δ_j k = if k < j then k else k + 1`. -/
def delV (j k : ℕ) : ℕ := if k < j then k else k + 1

/-- The first coordinate of the `j`-th face of the shuffle cell of `S`, on vertices. -/
def faceA (S : Finset (Fin 6)) (j : ℕ) (k : ℕ) : ℕ := A6 S (delV j k)

/-- The second coordinate of the `j`-th face of the shuffle cell of `S`, on vertices. -/
def faceB (S : Finset (Fin 6)) (j : ℕ) (k : ℕ) : ℕ := B6 S (delV j k)

/-- The total coefficient with which a face pair `(α, β)` (given by its vertex values on
`k ∈ {0,…,5}`) occurs in `∂ (ezC)` — the sum of `shufSign S · (-1)^j` over the `(S, j)` whose face
is that pair.  This is the finite object the coefficient computation cancels. -/
def faceCoeff (α β : Fin 6 → ℕ) : ℤ :=
  ((Finset.univ : Finset (PShuffle 3 3)).product (Finset.univ : Finset (Fin 7))).sum
    (fun p => if (∀ k : Fin 6, faceA p.1.1 p.2.val k.val = α k)
                ∧ (∀ k : Fin 6, faceB p.1.1 p.2.val k.val = β k)
              then shufSign p.1.1 * (-1 : ℤ) ^ (p.2.val) else 0)

/-! ## Sanity checks for the sign

These pin the sign convention and are the first thing to reach for when the coefficient
computation looks wrong.  The vanishing of the total sign is the Gaussian binomial identity at
`q = -1`; it is exactly what makes `ezGen_isCycle` true for the one-point simplicial set. -/

/-- The signs of the twenty `(3,3)`-shuffles sum to zero (the Gaussian binomial at `-1`). -/
lemma sum_shufSign_eq_zero : (∑ S : PShuffle 3 3, shufSign S.1) = 0 := by
  decide

/-- The good shuffle `E E E N N N` (`S = {3,4,5}`) has sign `+1`: it is the cell whose front and
back faces are both the identity (`shuffleFaceIdent`). -/
lemma shufSign_good : sign6 (Finset.univ.filter (fun j : Fin 6 => 2 < j.val)) = 1 := by
  decide

/-- The mirror shuffle `N N N E E E` has sign `-1`. -/
lemma shufSign_bad : sign6 (Finset.univ.filter (fun j : Fin 6 => j.val < 3)) = -1 := by
  decide

/-! ## Seam 1: the face pairs are shuffle pairs

The finite object of the coefficient computation is `faceCoeff`, and the first thing to know about
the pairs `(α, β) = (a_S ∘ δ_j, b_S ∘ δ_j)` that occur is that at every vertex the `E`-count and
the `N`-count of the face map add up to the image vertex index: face pairs are again "shuffle
pairs" of the smaller prism (the face of a `(3,3)`-shuffle cell is a `(3,2)`- or `(2,3)`-cell, i.e.
it is indexed by the same construction for the bidegrees `(3,2)`, `(2,3)` and the general
`PShuffle p q` of this file).  Twenty shuffles times seven faces times six vertices is a `decide`
(the statement is quantified over the fintypes so that it is closed). -/

/-- **Complementarity of the two coordinates of a face of a shuffle cell.**  For a `(3,3)`-shuffle
`S`, a face index `j` and a vertex `k` of `⦋5⦌`, the `E`-count and the `N`-count of the face map at
`k` add up to the index of the image vertex. -/
lemma faceA_add_faceB : ∀ (S : PShuffle 3 3) (j : Fin 7) (k : Fin 6),
    faceA S.1 j.val k.val + faceB S.1 j.val k.val = delV j.val k.val := by
  decide
/-! ## The `(2,3)` and `(3,2)` bidegrees: where the faces of a shuffle cell live

A face of the prism `Δ[3] × Δ[3]` is `Δ[3] × Δ[2]` or `Δ[2] × Δ[3]`, so the `j`-th face of a
`(3,3)`-shuffle cell is indexed by the bidegrees `(2,3)` and `(3,2)` — not by `(3,3)`.  (A
statement that every face pair is the pair of some `(3,3)`-shuffle is therefore false; see §10 of
`CUP_WITNESS_NOTES.md`.)  The structure is: `a_S ∘ δ_j` factors as a face inclusion of `⦋2⦌` in
`⦋3⦌` composed with the first coordinate of a `(2,3)`-shuffle, and dually for `b_S ∘ δ_j` with a
`(3,2)`-shuffle.

These are the pinned spellings of the two smaller bidegrees (compare `A6`/`B6`/`sign6`), so that
the statements of the next sub-lemmas are closed and `decide`-able, and so that no downstream
statement has to fight the implicit `{p q}`. -/

/-- A `(2,3)`-shuffle: the positions of the three `N`-steps among five steps. -/
abbrev Q23 : Type := PShuffle 2 3

/-- The `E`-count map of a `(2,3)`-shuffle, at the canonical type `Fin 5`. -/
abbrev C23 (T : Finset (Fin 5)) (n : ℕ) : ℕ := pANat (p := 2) (q := 3) T n

/-- The `N`-count map of a `(2,3)`-shuffle, at the canonical type `Fin 5`. -/
abbrev D23 (T : Finset (Fin 5)) (n : ℕ) : ℕ := pBNat (p := 2) (q := 3) T n

/-- A `(3,2)`-shuffle: the positions of the two `N`-steps among five steps. -/
abbrev Q32 : Type := PShuffle 3 2

/-- The `E`-count map of a `(3,2)`-shuffle, at the canonical type `Fin 5`. -/
abbrev C32 (T : Finset (Fin 5)) (n : ℕ) : ℕ := pANat (p := 3) (q := 2) T n

/-- The `N`-count map of a `(3,2)`-shuffle, at the canonical type `Fin 5`. -/
abbrev D32 (T : Finset (Fin 5)) (n : ℕ) : ℕ := pBNat (p := 3) (q := 2) T n

/-! ## Seam 1: interior cancellation

A face pair is a **boundary** pair when one of its two coordinates factors through a face inclusion
of `⦋2⦌` in `⦋3⦌` — these are the faces of the prism that survive in the Eilenberg–Zilber
expansion.  Every other pair is **interior**, and interior face pairs cancel pairwise: each one is
the common face of two neighbouring shuffle cells with opposite orientations.  This is the finite
content of the prism cancellation at the level of the shuffle index.

Only pairs with values in `Fin 4` can arise (the coordinates are counts of steps among at most
`p + q` steps landing in `⦋3⦌`), so the quantification below is over a fintype and the statement is
a closed `decide`. -/

/-- The pair `(α, β)` is a boundary face pair: one of its coordinates factors through a face
inclusion of `⦋2⦌` in `⦋3⦌` (`delV i`), i.e. misses the top vertex of `⦋2⦌` after reindexing. -/
abbrev IsBoundaryPair (α β : Fin 6 → ℕ) : Prop :=
  (∃ (i : Fin 4) (a' : Fin 6 → Fin 4), ∀ k : Fin 6, α k = delV i.val (a' k).val)
  ∨ (∃ (i : Fin 4) (b' : Fin 6 → Fin 4), ∀ k : Fin 6, β k = delV i.val (b' k).val)

/-! ## The interior faces and the flip map

The face of a shuffle cell that omits the vertex `j` of `⦋6⦌` lies in the boundary of the prism
exactly when the state `(a_S(j), b_S(j))` of the lattice path at `j` is on the boundary of the
rectangle `⦋3⦌ × ⦋3⦌`, i.e. when one of the two coordinates is `0` or `3`.  All the other faces are
*interior*: each is the common `4`-face of two neighbouring cells of the prism triangulation, which
cancel pairwise in `∂ (ezC)`.  This is the criterion the flip map is indexed by — `j ↦` the
neighbour is obtained by exchanging the two steps adjacent to the omitted vertex (one `E`, one `N`,
so that the flip is an involution and preserves the omitted state) — and it is what replaces the
`decide` that failed in §12 of `CUP_WITNESS_NOTES.md`. -/

/-- A face of a shuffle cell is **interior** when the state of the lattice path at the omitted
vertex has both coordinates in `{1,2}`. -/
abbrev IsInteriorFace (S : Finset (Fin 6)) (j : Fin 7) : Prop :=
  1 ≤ A6 S j.val ∧ A6 S j.val ≤ 2 ∧ 1 ≤ B6 S j.val ∧ B6 S j.val ≤ 2

/-- A face of a shuffle cell is **on the boundary of the prism** when one of the two coordinates of
the state at the omitted vertex is `0` or `3`. -/
abbrev IsBoundaryFace (S : Finset (Fin 6)) (j : Fin 7) : Prop :=
  A6 S j.val = 0 ∨ A6 S j.val = 3 ∨ B6 S j.val = 0 ∨ B6 S j.val = 3

/-- Every face is either interior or on the boundary of the prism. -/
lemma interior_or_boundary (S : Finset (Fin 6)) (hS : S.card = 3) (j : Fin 7) :
    IsInteriorFace S j ∨ IsBoundaryFace S j := by
  have h1 : A6 S j.val ≤ 3 :=
    pA_le (p := 3) (q := 3) S hS (⟨j.val, by have := j.isLt; omega⟩ : Fin 7)
  have h2 : B6 S j.val ≤ 3 :=
    pB_le (p := 3) (q := 3) S hS (⟨j.val, by have := j.isLt; omega⟩ : Fin 7)
  simp only [IsInteriorFace, IsBoundaryFace]
  omega

/-- **The good shuffle `E E E N N N` is a boundary path**: every face of its cell lies on the
boundary of the prism, so it contributes no interior face at all (and its own contribution to the
shuffle sum is the one that survives). -/
lemma good_no_interior : ∀ j : Fin 7,
    ¬ IsInteriorFace (Finset.univ.filter (fun j : Fin 6 => 2 < j.val)) j := by
  decide

/-! ## The flip map across an interior face

An interior face of a shuffle cell is shared with exactly one neighbouring cell: inside the unit
square of the lattice path, the two orderings `E N` and `N E` of the two steps adjacent to the
omitted vertex give the two cells of the triangulation of the square, and they meet along the
diagonal.  So the neighbour of `(S, j)` is obtained by *exchanging* the two steps adjacent to the
vertex `j`; by the analysis in `CUP_WITNESS_NOTES.md` §13, this flip

* is an involution and preserves the number of `N`-steps (hence maps shuffles to shuffles);
* preserves the face index `j` (in a path through the square, the vertex at index `j` keeps its
  index: the two steps before and after it are swapped, and the vertex count does not change);
* preserves the face pair `(faceA, faceB)`, because the two paths agree at every vertex except the
  omitted index `j`, while `faceA`/`faceB` only evaluate the path at `delV j k ≠ j`;
* **reverses `shufSign`** (exchanging the adjacent steps `E N` into `N E` changes the number of
  `N`-before-`E` inversions by one, i.e. the Gaussian-binomial sign).

Consequently the two terms of `faceCoeff (faceA S j ·) (faceB S j ·)` contributed by `(S,j)` and by
its flip cancel, which is the interior cancellation of §12. -/

/-- **The flip** of a shuffle across an interior face: exchange the two steps adjacent to the vertex
`j` of the lattice path (the step into `j` and the step out of it).  For `j` outside `1 ≤ j ≤ 5` the
vertex is not interior and the map is the identity (that case is never used). -/
def flipS (S : Finset (Fin 6)) (j : ℕ) : Finset (Fin 6) :=
  if h : 1 ≤ j ∧ j ≤ 5 then
    (if (⟨j - 1, by omega⟩ : Fin 6) ∈ S
      then insert (⟨j, by omega⟩ : Fin 6) (S.erase ⟨j - 1, by omega⟩)
      else insert (⟨j - 1, by omega⟩ : Fin 6) (S.erase ⟨j, by omega⟩))
  else S

/-- A vertex `j` of the lattice path of `S` is a **corner** when the two steps adjacent to it are
one `E`- and one `N`-step, i.e. exactly one of `j - 1`, `j` is in `S` (the indices of the
`N`-steps).  Only corners are *interior vertices* of the prism triangulation, and only a corner has
a well-defined flip: when both adjacent steps are of the same kind the vertex lies in the interior
of an edge of the path, its state is never a "corner" of the grid, and exchanging the (equal) steps
is not an involution.  This is why `flipS_involutive` needs the corner hypothesis, and why the
interior faces to be cancelled are the *corners with interior state* — `IsInteriorFace S j` alone is
not enough (see §14 of `CUP_WITNESS_NOTES.md`). -/
abbrev IsCorner (S : Finset (Fin 6)) (j : ℕ) : Prop :=
  ∃ (_ : 1 ≤ j) (_ : j ≤ 5),
    ((⟨j - 1, by omega⟩ : Fin 6) ∈ S) ≠ ((⟨j, by omega⟩ : Fin 6) ∈ S)

/-- The interior faces which the flip pairs up: a corner whose state is interior, i.e. the faces of
the prism triangulation that do not lie on the boundary. -/
abbrev IsInteriorCorner (S : Finset (Fin 6)) (j : Fin 7) : Prop :=
  IsCorner S j.val ∧ IsInteriorFace S j

/-! ## Items 1–4 of §13: the flip laws

Each law is a closed finite statement about the `64` subsets of `Fin 6` and the `7` candidate face
indices, so each is settled by `decide` over the fintypes (the route suggested by the two reviewers
of `flipS_involutive`), and then transported to an arbitrary corner by `j < 7`. -/

/-- Finite form of the involution law. -/
lemma flipS_involutive_finite : ∀ (S : Finset (Fin 6)) (j : Fin 7),
    IsCorner S j.val → flipS (flipS S j.val) j.val = S := by
  decide

/-- **Item 1: `flipS` is an involution on corners.**  The corner hypothesis is necessary: when both
adjacent steps are equal the vertex lies in the interior of an edge of the path and the second flip
does not return `S` (see §14 of `CUP_WITNESS_NOTES.md`). -/
lemma flipS_involutive (S : Finset (Fin 6)) (j : ℕ) (h : IsCorner S j) :
    flipS (flipS S j) j = S := by
  refine flipS_involutive_finite S ⟨j, ?_⟩ h
  obtain ⟨h1, h5, -⟩ := h
  omega

/-- Finite form of the cardinality law. -/
lemma flipS_card_finite : ∀ (S : Finset (Fin 6)) (j : Fin 7),
    IsCorner S j.val → (flipS S j.val).card = S.card := by
  decide

/-- **Item 2: the flip preserves the number of `N`-steps** (so it maps shuffles to shuffles). -/
lemma flipS_card (S : Finset (Fin 6)) (j : ℕ) (h : IsCorner S j) :
    (flipS S j).card = S.card := by
  refine flipS_card_finite S ⟨j, ?_⟩ h
  obtain ⟨h1, h5, -⟩ := h
  omega

/-- Finite form of the sign law. -/
lemma flipS_sign_finite : ∀ (S : Finset (Fin 6)) (j : Fin 7),
    IsCorner S j.val → sign6 (flipS S j.val) = - sign6 S := by
  decide

/-- **Item 3: the flip reverses the Eilenberg–Zilber sign.**  Exchanging the adjacent steps `E N` for
`N E` changes the number of `N`-before-`E` inversions by one, hence flips `shufSign`.  Together with
`flipS_face_finite` below this is what makes the two members of a `flipS`-orbit cancel in
`faceCoeff`. -/
lemma flipS_sign (S : Finset (Fin 6)) (j : ℕ) (h : IsCorner S j) :
    sign6 (flipS S j) = - sign6 S := by
  refine flipS_sign_finite S ⟨j, ?_⟩ h
  obtain ⟨h1, h5, -⟩ := h
  omega

/-- Finite form of the face-pair law. -/
lemma flipS_face_finite : ∀ (S : Finset (Fin 6)) (j : Fin 7),
    IsCorner S j.val →
      (∀ k : Fin 6, faceA (flipS S j.val) j.val k.val = faceA S j.val k.val)
      ∧ (∀ k : Fin 6, faceB (flipS S j.val) j.val k.val = faceB S j.val k.val) := by
  decide

/-- **Item 4: the flip preserves the face pair.**  The two paths agree at every vertex of `⦋6⦌`
except the omitted index `j`, while `faceA`/`faceB` evaluate the path only at `delV j k ≠ j`; so
`(flipS S j, j)` and `(S, j)` contribute the *same* pair `(faceA, faceB)` to `faceCoeff`, with
opposite signs by item 3. -/
lemma flipS_face (S : Finset (Fin 6)) (j : ℕ) (h : IsCorner S j) :
    (∀ k : Fin 6, faceA (flipS S j) j k.val = faceA S j k.val)
      ∧ (∀ k : Fin 6, faceB (flipS S j) j k.val = faceB S j k.val) := by
  refine flipS_face_finite S ⟨j, ?_⟩ h
  obtain ⟨h1, h5, -⟩ := h
  omega

/-! ## Item 5: the orbit of a corner cancels

`faceCoeff α β` sums `sign6 S · (-1)^j` over the `(S, j)` whose face pair is `(α, β)`.  By items
3 and 4 the paired tuple `(flipS S j, j)` has the *same* face pair and the *same* `(-1)^j`, but the
opposite sign — so the two members of a `flipS`-orbit contribute opposite amounts and cancel.  Note
that the pairing is available for *every corner* (items 1–4 need only `IsCorner`): the cancellation
does not require the omitted state to be interior, which **sharpens §13**: the terms of `faceCoeff`
that survive the flip pairing are precisely the *non-corner* faces, not the "boundary-state" ones.
-/

/-- **The two members of a `flipS`-orbit of a corner cancel in `faceCoeff`.** -/
lemma flipS_orbit_cancel (S : Finset (Fin 6)) (j : Fin 7) (h : IsCorner S j.val) :
    sign6 S * (-1 : ℤ) ^ j.val + sign6 (flipS S j.val) * (-1 : ℤ) ^ j.val = 0 := by
  rw [flipS_sign S j.val h]
  ring

/-- The flip of a corner is fixed-point-free: `flipS S j ≠ S` (the swap changes the membership of
`j - 1` and of `j`, which differ precisely because `j` is a corner). -/
lemma flipS_ne_self (S : Finset (Fin 6)) (j : ℕ) (h : IsCorner S j) : flipS S j ≠ S := by
  intro hc
  have hmem : (⟨j - 1, by obtain ⟨h1, h5, -⟩ := h; omega⟩ : Fin 6) ∈ S
      ↔ (⟨j - 1, by obtain ⟨h1, h5, -⟩ := h; omega⟩ : Fin 6) ∈ flipS S j := by rw [hc]
  obtain ⟨h1, h5, hne⟩ := h
  unfold flipS at hmem
  rw [dif_pos ⟨h1, h5⟩] at hmem
  by_cases ha : (⟨j - 1, by omega⟩ : Fin 6) ∈ S
  · rw [if_pos ha] at hmem
    have : (⟨j - 1, by omega⟩ : Fin 6) ∉ insert (⟨j, by omega⟩ : Fin 6)
        (S.erase ⟨j - 1, by omega⟩) := by
      simp only [Finset.mem_insert, Finset.mem_erase]
      rintro (hEq | ⟨hne', -⟩)
      · exact absurd hEq (by intro hcc; have := congrArg Fin.val hcc; simp at this; omega)
      · exact hne' rfl
    exact this (hmem.mp ha)
  · rw [if_neg ha] at hmem
    exact ha (hmem.mpr (Finset.mem_insert_self _ _))

/-- Finite form: the flip *preserves* the corner condition (forward implication only: the converse
is false, a vertex in the interior of an edge being sent to a corner). -/
lemma flipS_isCorner_finite : ∀ (S : Finset (Fin 6)) (j : Fin 7),
    IsCorner S j.val → IsCorner (flipS S j.val) j.val := by
  decide

/-- **The flip preserves corners.**  The corner condition is exactly that one of `j - 1`, `j` lies in
`S`, and the flip exchanges their membership, so it preserves corners as well as their face pairs
(item 4) and the index `j`; together with items 1–3 this is what makes the `flipS`-pairing an
involution of the *corner* part of the index set of `faceCoeff`, which is the hypothesis
`Finset.sum_involution` consumes. -/
lemma flipS_isCorner (S : Finset (Fin 6)) (j : ℕ) (h : IsCorner S j) :
    IsCorner (flipS S j) j := by
  refine flipS_isCorner_finite S ⟨j, ?_⟩ h
  obtain ⟨h1, h5, -⟩ := h
  omega

end

end Work.Cohomology.Crux33
