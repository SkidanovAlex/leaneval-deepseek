import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

open scoped Simplicial
namespace Work.SSSR.Cohomology.Crux33

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

/-! ## The faces of a shuffle cell

The `j`-th face of the shuffle cell `(σ ∘ a_S, τ ∘ b_S)` is `(σ ∘ (a_S ∘ δ_j), τ ∘ (b_S ∘ δ_j))`,
and on vertices `δ_j` acts by `delV j k = if k < j then k else k + 1`.  So the pair of monotone
maps `(a_S ∘ δ_j, b_S ∘ δ_j)` is completely described by the two `ℕ`-valued functions
`k ↦ A6 S (delV j k)`, `k ↦ B6 S (delV j k)` on `k ∈ {0,…,5}`, which makes the first seam of the
coefficient computation — *which* pairs `(α, β)` arise, and with which total coefficient — a
finite `decide` check over the `20 × 7` pairs, exactly as `shuffleFaceIdent` was. -/

/-- The `j`-th face map on vertices: `δ_j k = if k < j then k else k + 1`. -/
def delV (j k : ℕ) : ℕ := if k < j then k else k + 1

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

end

end Work.SSSR.Cohomology.Crux33
