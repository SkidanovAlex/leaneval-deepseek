import Mathlib
import Submission.Work.Drive.boxParity
import Submission.Work.Drive.intersection_bordism
import Submission.Work.Drive.cofactor_restrict_surjective

/-!
# The triple intersection number of `2`-chains in `ℝ³` is a bordism invariant

`Submission/Work/Drive/intersection_triple.lean` proves the Leibniz rule for the mod-2 triple pairing
of three `3`-chains in `ℝ⁴` (the parity bookkeeping of Hugelmeyer's Lemmas 3–4) and
`Submission/Work/Drive/intersection_bordism.lean` proves the bordism invariance of the *double*
pairing.  This file is the missing **three-dimensional** chapter, the one that
`Submission/Work/Drive/SQUARE_PRESENTATION_NOTES.md` §3 records as non-existent: the mod-2 triple
intersection number of three `2`-chains in a `3`-manifold, and its invariance under a bordism of one
of the chains.

It is what the *end contribution* of the chain route needs (`SQUARE_PRESENTATION_NOTES.md` §3 and §6,
`ENDS_AND_SEAMS_NOTES.md`): the three `ω`-chains of Hugelmeyer's Lemma 4 have their bottom faces in
one level `{r = ε} ≅ ℝP³`, and the parity `Σ_k bottom_k ≡ 1` is computed by replacing each bottom
face through a bordism inside that level by a *linear* projective plane — a `3`-manifold statement,
proved here in the local vector-space model `ℝ³`.

## The statement

A `3`-chain `W : ℝ³ → ℝ³` (modelled on the unit cube, with `W₀ = W(0, ·, ·)` and `W₁ = W(1, ·, ·)`
its two `x₀`-faces) and two `2`-chains `A B : ℝ² → ℝ³` are given.  The difference map

`tri3Diff W A B : ℝ⁷ → ℝ⁶,  x ↦ (W (wPt x) − A (aPt x),  W (wPt x) − B (bPt x))`

(where `wPt x ∈ [0,1]³`, `aPt x ∈ [0,1]²`, `bPt x ∈ [0,1]²` are the three blocks of the seven-box)
has `0` as a regular value; its zero set is the triple intersection `W ⋔ A ⋔ B`, a compact
`1`-manifold whose boundary is the union of the seven coordinate faces of the box.  The zeros on the
two faces `x (wI 0) = 0` and `x (wI 0) = 1` are exactly the triple intersections `W₀ ⋔ A ⋔ B` and
`W₁ ⋔ A ⋔ B`; if the triple intersection avoids all the other faces, their numbers have an even sum:

> **`W₀ ⋔ A ⋔ B` and `W₁ ⋔ A ⋔ B` have the same parity** (`even_ncard_wFaceMeet_add_wFaceMeet`).

That is the bordism invariance of the triple intersection number of `2`-cycles in a `3`-manifold:
`W` is a bordism between the two `2`-cycles `W₀` and `W₁`, and the pairing with the fixed
`2`-cycles `A`, `B` is unchanged.

As in `intersection_bordism.lean`, the hypothesis that the *other* faces carry no zeros is the
convenient (and, in the application, generic) way of disposing of the remaining boundary terms; the
chapter also records the total parity (`even_ncard_tri3Diff_bdy`) and the finiteness of the pieces.
-/

set_option maxHeartbeats 0

namespace Work.Drive

open Submission.Drive
open scoped Manifold ContDiff Topology

noncomputable section

/-! ## The seven-box as `cube × square × square` -/

/-- The three coordinates of the seven-box carrying the `3`-chain (the first block). -/
def wI (j : Fin 3) : Fin 7 := ⟨j.val, by omega⟩

/-- The two coordinates of the seven-box carrying the first `2`-chain (the middle block). -/
def aI2 (j : Fin 2) : Fin 7 := ⟨3 + j.val, by omega⟩

/-- The two coordinates of the seven-box carrying the second `2`-chain (the last block). -/
def bI2 (j : Fin 2) : Fin 7 := ⟨5 + j.val, by omega⟩

@[simp] lemma wI_val (j : Fin 3) : (wI j).val = j.val := rfl
@[simp] lemma aI2_val (j : Fin 2) : (aI2 j).val = 3 + j.val := rfl
@[simp] lemma bI2_val (j : Fin 2) : (bI2 j).val = 5 + j.val := rfl

lemma wI_ne_aI2 (j : Fin 3) (j' : Fin 2) : wI j ≠ aI2 j' := by
  intro h
  have h' := congrArg Fin.val h
  simp only [wI_val, aI2_val] at h'
  omega

lemma wI_ne_bI2 (j : Fin 3) (j' : Fin 2) : wI j ≠ bI2 j' := by
  intro h
  have h' := congrArg Fin.val h
  simp only [wI_val, bI2_val] at h'
  omega

lemma aI2_ne_bI2 (j j' : Fin 2) : aI2 j ≠ bI2 j' := by
  intro h
  have h' := congrArg Fin.val h
  simp only [aI2_val, bI2_val] at h'
  omega

/-- Every coordinate of the seven-box lies in the `3`-block, the first `2`-block or the second
`2`-block. -/
lemma exists_block (i : Fin 7) :
    (∃ j : Fin 3, i = wI j) ∨ (∃ j : Fin 2, i = aI2 j) ∨ (∃ j : Fin 2, i = bI2 j) := by
  rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5
    ∨ i.val = 6 by omega) with h | h | h | h | h | h | h
  · exact Or.inl ⟨0, Fin.ext (by rw [h]; rfl)⟩
  · exact Or.inl ⟨1, Fin.ext (by rw [h]; rfl)⟩
  · exact Or.inl ⟨2, Fin.ext (by rw [h]; rfl)⟩
  · exact Or.inr (Or.inl ⟨0, Fin.ext (by rw [h]; rfl)⟩)
  · exact Or.inr (Or.inl ⟨1, Fin.ext (by rw [h]; rfl)⟩)
  · exact Or.inr (Or.inr ⟨0, Fin.ext (by rw [h]; rfl)⟩)
  · exact Or.inr (Or.inr ⟨1, Fin.ext (by rw [h]; rfl)⟩)

/-- **Splitting the seven-box into the three blocks.** -/
lemma exists_fin_seven_iff (P : Fin 7 → Prop) :
    (∃ i, P i) ↔ (∃ j : Fin 3, P (wI j)) ∨ (∃ j : Fin 2, P (aI2 j))
      ∨ (∃ j : Fin 2, P (bI2 j)) := by
  constructor
  · rintro ⟨i, hi⟩
    rcases exists_block i with ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
    · exact Or.inl ⟨j, by rw [← hj]; exact hi⟩
    · exact Or.inr (Or.inl ⟨j, by rw [← hj]; exact hi⟩)
    · exact Or.inr (Or.inr ⟨j, by rw [← hj]; exact hi⟩)
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩)
    · exact ⟨wI j, hj⟩
    · exact ⟨aI2 j, hj⟩
    · exact ⟨bI2 j, hj⟩

/-- The projection of the seven-box onto the `3`-block. -/
def wPt (x : EuclideanSpace ℝ (Fin 7)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun j => x (wI j)

/-- The projection of the seven-box onto the first `2`-block. -/
def aPt (x : EuclideanSpace ℝ (Fin 7)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun j => x (aI2 j)

/-- The projection of the seven-box onto the second `2`-block. -/
def bPt (x : EuclideanSpace ℝ (Fin 7)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun j => x (bI2 j)

@[simp] lemma wPt_apply (x : EuclideanSpace ℝ (Fin 7)) (j : Fin 3) : wPt x j = x (wI j) := rfl
@[simp] lemma aPt_apply (x : EuclideanSpace ℝ (Fin 7)) (j : Fin 2) : aPt x j = x (aI2 j) := rfl
@[simp] lemma bPt_apply (x : EuclideanSpace ℝ (Fin 7)) (j : Fin 2) : bPt x j = x (bI2 j) := rfl

/-- **Some coordinate of the `3`-block other than `x₀` lies on a face of the seven-box.**  These are
the boundary faces of the `3`-chain `W` other than the two slices `x₀ = 0`, `x₀ = 1` that the bordism
invariance compares. -/
def onWFaceOther (x : EuclideanSpace ℝ (Fin 7)) : Prop :=
  ∃ j : Fin 3, j ≠ 0 ∧ (x (wI j) = 0 ∨ x (wI j) = 1)

/-- The first `2`-block lies on a face of the seven-box. -/
def onAFace (x : EuclideanSpace ℝ (Fin 7)) : Prop :=
  ∃ j : Fin 2, x (aI2 j) = 0 ∨ x (aI2 j) = 1

/-- The second `2`-block lies on a face of the seven-box. -/
def onBFace (x : EuclideanSpace ℝ (Fin 7)) : Prop :=
  ∃ j : Fin 2, x (bI2 j) = 0 ∨ x (bI2 j) = 1

/-- **The auxiliary faces** of the triple intersection: a face of the `3`-chain other than the two
slices, or a face of one of the two `2`-chains.  These are the boundary terms that a bordism
contributes in addition to the two slices `x₀ = 0`, `x₀ = 1`, and which the hypothesis `haux` of
`Work.Drive.even_ncard_wFaceMeet_add_wFaceMeet` disposes of. -/
def tri3AuxFace (x : EuclideanSpace ℝ (Fin 7)) : Prop :=
  onAFace x ∨ onBFace x ∨ onWFaceOther x

lemma mem_unitBox_seven_iff (x : EuclideanSpace ℝ (Fin 7)) :
    x ∈ unitBox 6 ↔ wPt x ∈ unitBox 2 ∧ aPt x ∈ unitBox 1 ∧ bPt x ∈ unitBox 1 := by
  constructor
  · intro h
    exact ⟨fun j => h (wI j), fun j => h (aI2 j), fun j => h (bI2 j)⟩
  · rintro ⟨h0, h1, h2⟩ i
    rcases exists_block i with ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [hj]; exact h0 j
    · rw [hj]; exact h1 j
    · rw [hj]; exact h2 j

lemma mem_unitBoxBdry_seven_iff (x : EuclideanSpace ℝ (Fin 7)) :
    x ∈ unitBoxBdry 6 ↔ x ∈ unitBox 6 ∧
      (tri3AuxFace x ∨ x (wI 0) = 0 ∨ x (wI 0) = 1) := by
  constructor
  · rintro ⟨hbox, i, hi⟩
    refine ⟨hbox, ?_⟩
    rcases (exists_fin_seven_iff (fun i => x i = 0 ∨ x i = 1)).mp ⟨i, hi⟩ with
      ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
    · rcases (show j = 0 ∨ j ≠ 0 by tauto) with h | h
      · subst h; exact Or.inr hj
      · exact Or.inl (Or.inr (Or.inr ⟨j, h, hj⟩))
    · exact Or.inl (Or.inl ⟨j, hj⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨j, hj⟩))
  · rintro ⟨hbox, h | h | h⟩
    · rcases h with hD | hE | hC
      · obtain ⟨j, hj⟩ := hD
        exact ⟨hbox, aI2 j, hj⟩
      · obtain ⟨j, hj⟩ := hE
        exact ⟨hbox, bI2 j, hj⟩
      · obtain ⟨j, hne, hj⟩ := hC
        exact ⟨hbox, wI j, hj⟩
    · exact ⟨hbox, wI 0, Or.inl h⟩
    · exact ⟨hbox, wI 0, Or.inr h⟩

/-! ## The difference map of a `3`-chain and two `2`-chains -/

/-- Two vectors of `ℝ³` stacked into a vector of `ℝ⁶`. -/
def stack3 (a b : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 6) :=
  WithLp.toLp 2 fun k : Fin 6 =>
    if h : k.val < 3 then a ⟨k.val, h⟩ else b ⟨k.val - 3, by omega⟩

@[simp] lemma stack3_apply_fst (a b : EuclideanSpace ℝ (Fin 3)) (k : Fin 3) :
    stack3 a b (Fin.castAdd 3 k) = a k := by
  simp only [stack3, WithLp.ofLp_toLp]
  rw [dif_pos (by simp)]
  exact congrArg a (Fin.ext (by simp))

@[simp] lemma stack3_apply_snd (a b : EuclideanSpace ℝ (Fin 3)) (k : Fin 3) :
    stack3 a b (Fin.natAdd 3 k) = b k := by
  simp only [stack3, WithLp.ofLp_toLp]
  rw [dif_neg (by simp)]
  exact congrArg b (Fin.ext (by simp))

/-- `stack3` vanishes exactly when both components do. -/
lemma stack3_eq_zero_iff (a b : EuclideanSpace ℝ (Fin 3)) :
    stack3 a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    constructor
    · ext k
      have hk := congrArg (fun z : EuclideanSpace ℝ (Fin 6) => z (Fin.castAdd 3 k)) h
      simpa [stack3] using hk
    · ext k
      have hk := congrArg (fun z : EuclideanSpace ℝ (Fin 6) => z (Fin.natAdd 3 k)) h
      simpa [stack3] using hk
  · rintro ⟨h1, h2⟩
    rw [WithLp.ext_iff]
    funext k
    simp only [stack3, WithLp.ofLp_toLp]
    split_ifs with h
    · have hk := congrArg (fun y : EuclideanSpace ℝ (Fin 3) => y ⟨k.val, h⟩) h1
      simpa using hk
    · have hk := congrArg (fun y : EuclideanSpace ℝ (Fin 3) => y ⟨k.val - 3, by omega⟩) h2
      simpa using hk

/-- **The difference map of a `3`-chain and two `2`-chains in `ℝ³`.**  Its zeros in the seven-box are
the common intersection points of the three chains. -/
def tri3Diff (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 7) → EuclideanSpace ℝ (Fin 6) :=
  fun x => stack3 (W (wPt x) - A (aPt x)) (W (wPt x) - B (bPt x))

/-- The zeros of the difference map, in components. -/
lemma tri3Diff_eq_zero_iff (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 7)) :
    tri3Diff W A B x = 0 ↔ W (wPt x) = A (aPt x) ∧ W (wPt x) = B (bPt x) := by
  rw [tri3Diff, stack3_eq_zero_iff]
  exact ⟨fun h => ⟨sub_eq_zero.mp h.1, sub_eq_zero.mp h.2⟩,
    fun h => ⟨sub_eq_zero.mpr h.1, sub_eq_zero.mpr h.2⟩⟩

/-- **The face `x (wI 0) = e` of the `3`-chain `W` against the two `2`-chains**: the triple
intersections of the `e`-face of the bordism `W` with `A` and `B`.  For `e = 0` this is
`W₀ ⋔ A ⋔ B` and for `e = 1` it is `W₁ ⋔ A ⋔ B`; the two are the terms whose parities
`Work.Drive.even_ncard_wFaceMeet_add_wFaceMeet` compares. -/
def wFaceMeet (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (e : ℝ) :
    Set (EuclideanSpace ℝ (Fin 7)) :=
  {x | x ∈ unitBox 6 ∧ x (wI 0) = e ∧ tri3Diff W A B x = 0}

/-- **The auxiliary boundary faces of the triple intersection.**  An intersection point at which a
coordinate of the `3`-block *other* than `x₀` is on a face, or a coordinate of one of the two
`2`-blocks is on a face, and with `x₀` strictly inside — the boundary terms of the Leibniz rule other
than the two slices `x₀ = 0`, `x₀ = 1`. -/
def tri3AuxMeet (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    Set (EuclideanSpace ℝ (Fin 7)) :=
  {x | x ∈ unitBox 6 ∧ tri3AuxFace x ∧ x (wI 0) ≠ 0 ∧ x (wI 0) ≠ 1
    ∧ tri3Diff W A B x = 0}

/-- **The boundary of the triple intersection.**  The zeros of `tri3Diff W A B` on the boundary of
the seven-box are exactly the auxiliary faces together with the two slices `x₀ = 0` and `x₀ = 1`. -/
theorem bdyZeros_tri3Diff_eq (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    bdyZeros (tri3Diff W A B) =
      tri3AuxMeet W A B ∪ wFaceMeet W A B 0 ∪ wFaceMeet W A B 1 := by
  ext x
  have hbd : x ∈ bdyZeros (tri3Diff W A B) ↔
      x ∈ unitBoxBdry 6 ∧ tri3Diff W A B x = 0 := Iff.rfl
  have hmem : x ∈ unitBoxBdry 6 ↔ x ∈ unitBox 6 ∧
      (tri3AuxFace x ∨ x (wI 0) = 0 ∨ x (wI 0) = 1) := mem_unitBoxBdry_seven_iff x
  have h0 : x ∈ tri3AuxMeet W A B ↔ x ∈ unitBox 6 ∧ tri3AuxFace x ∧ x (wI 0) ≠ 0
      ∧ x (wI 0) ≠ 1 ∧ tri3Diff W A B x = 0 := Iff.rfl
  have h1 : x ∈ wFaceMeet W A B 0 ↔ x ∈ unitBox 6 ∧ x (wI 0) = 0
      ∧ tri3Diff W A B x = 0 := Iff.rfl
  have h2 : x ∈ wFaceMeet W A B 1 ↔ x ∈ unitBox 6 ∧ x (wI 0) = 1
      ∧ tri3Diff W A B x = 0 := Iff.rfl
  rw [hbd, hmem, Set.mem_union, Set.mem_union, h0, h1, h2]
  tauto

/-! ## Pairwise disjointness of the three pieces -/

lemma disjoint_tri3Aux_wFaceMeet_zero
    (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    Disjoint (tri3AuxMeet W A B) (wFaceMeet W A B 0) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, -, hz, -, -⟩ ⟨-, h0, -⟩
  exact hz h0

lemma disjoint_tri3Aux_wFaceMeet_one
    (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    Disjoint (tri3AuxMeet W A B) (wFaceMeet W A B 1) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, -, -, ho, -⟩ ⟨-, h1, -⟩
  exact ho h1

lemma disjoint_wFaceMeet_zero_one
    (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    Disjoint (wFaceMeet W A B 0) (wFaceMeet W A B 1) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, h0, -⟩ ⟨-, h1, -⟩
  rw [h0] at h1
  norm_num at h1

/-! ## The parity of the boundary -/

/-- **The triple-intersection Leibniz rule in `ℝ³`.**  For a `3`-chain `W`, two `2`-chains `A`, `B`
satisfying the three hypotheses of `Submission.Drive.ParityProp` for the difference map, the number
of boundary points of the compact `1`-manifold `W ⋔ A ⋔ B` — split into the auxiliary faces and the
two slices `x₀ = 0`, `x₀ = 1` — is even. -/
theorem even_ncard_tri3Diff_bdy
    (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tri3Diff W A B))
    (hreg : ∀ x ∈ unitBox 6, tri3Diff W A B x = 0 →
      Function.Surjective (fderiv ℝ (tri3Diff W A B) x))
    (hface : ∀ x ∈ unitBoxBdry 6, tri3Diff W A B x = 0 → ∃ i : Fin (6 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb 6 // v i = 0} =>
        fderiv ℝ (tri3Diff W A B) x v.1)) :
    Even ((tri3AuxMeet W A B).ncard + (wFaceMeet W A B 0).ncard
      + (wFaceMeet W A B 1).ncard) := by
  obtain ⟨hfin, heven⟩ := boxParity 6 (tri3Diff W A B) hF hreg hface
  have hfin' : (bdyZeros (tri3Diff W A B)).Finite := hfin
  have heven' : Even (bdyZeros (tri3Diff W A B)).ncard := heven
  rw [bdyZeros_tri3Diff_eq] at hfin' heven'
  have hfA : (tri3AuxMeet W A B).Finite :=
    hfin'.subset (fun x hx => by simp only [Set.mem_union]; exact Or.inl (Or.inl hx))
  have hf0 : (wFaceMeet W A B 0).Finite :=
    hfin'.subset (fun x hx => by simp only [Set.mem_union]; exact Or.inl (Or.inr hx))
  have hf1 : (wFaceMeet W A B 1).Finite :=
    hfin'.subset (fun x hx => by simp only [Set.mem_union]; exact Or.inr hx)
  have dA0 := disjoint_tri3Aux_wFaceMeet_zero W A B
  have dA1 := disjoint_tri3Aux_wFaceMeet_one W A B
  have d01 := disjoint_wFaceMeet_zero_one W A B
  have dA01 : Disjoint (tri3AuxMeet W A B ∪ wFaceMeet W A B 0) (wFaceMeet W A B 1) := by
    rw [Set.disjoint_left]
    rintro x (hx | hx) hy
    · exact Set.disjoint_left.mp dA1 hx hy
    · exact Set.disjoint_left.mp d01 hx hy
  rw [Set.ncard_union_eq (s := tri3AuxMeet W A B ∪ wFaceMeet W A B 0)
      (t := wFaceMeet W A B 1) dA01 (hfA.union hf0) hf1,
    Set.ncard_union_eq (s := tri3AuxMeet W A B) (t := wFaceMeet W A B 0) dA0 hfA hf0]
    at heven'
  exact heven'

/-- **Finiteness of the three pieces of the boundary.**  Under the transversality hypotheses of
`Submission.Drive.ParityProp` all the pieces are finite, so the parities above are not vacuous. -/
theorem finite_tri3AuxMeet_and_wFaceMeet
    (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tri3Diff W A B))
    (hreg : ∀ x ∈ unitBox 6, tri3Diff W A B x = 0 →
      Function.Surjective (fderiv ℝ (tri3Diff W A B) x))
    (hface : ∀ x ∈ unitBoxBdry 6, tri3Diff W A B x = 0 → ∃ i : Fin (6 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb 6 // v i = 0} =>
        fderiv ℝ (tri3Diff W A B) x v.1)) :
    (tri3AuxMeet W A B).Finite ∧ (wFaceMeet W A B 0).Finite
      ∧ (wFaceMeet W A B 1).Finite := by
  obtain ⟨hfin, -⟩ := boxParity 6 (tri3Diff W A B) hF hreg hface
  have hfin' : (bdyZeros (tri3Diff W A B)).Finite := hfin
  rw [bdyZeros_tri3Diff_eq] at hfin'
  refine ⟨hfin'.subset ?_, hfin'.subset ?_, hfin'.subset ?_⟩
  · intro x hx; simp only [Set.mem_union]; exact Or.inl (Or.inl hx)
  · intro x hx; simp only [Set.mem_union]; exact Or.inl (Or.inr hx)
  · intro x hx; simp only [Set.mem_union]; exact Or.inr hx

/-- **The triple intersection number of `2`-cycles in a `3`-manifold is a bordism invariant.**  Let
`W` be a bordism between the `2`-cycles `W₀ = W(0, ·, ·)` and `W₁ = W(1, ·, ·)`, and let `A`, `B` be
two further `2`-chains, all three in general position (the `ParityProp` hypotheses).  If the triple
intersection `W ⋔ A ⋔ B` avoids the auxiliary boundary faces — i.e. only the two slices `x₀ = 0` and
`x₀ = 1` meet it — then the numbers of triple intersections of `A` and `B` with the two faces of the
bordism have the same parity. -/
theorem even_ncard_wFaceMeet_add_wFaceMeet
    (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tri3Diff W A B))
    (hreg : ∀ x ∈ unitBox 6, tri3Diff W A B x = 0 →
      Function.Surjective (fderiv ℝ (tri3Diff W A B) x))
    (hface : ∀ x ∈ unitBoxBdry 6, tri3Diff W A B x = 0 → ∃ i : Fin (6 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb 6 // v i = 0} =>
        fderiv ℝ (tri3Diff W A B) x v.1))
    (haux : ∀ x, x ∈ unitBox 6 → tri3AuxFace x → tri3Diff W A B x ≠ 0) :
    Even ((wFaceMeet W A B 0).ncard + (wFaceMeet W A B 1).ncard) := by
  have hmain := even_ncard_tri3Diff_bdy W A B hF hreg hface
  have hempty : tri3AuxMeet W A B = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hf, hz, ho, hFx⟩
    exact haux x hx hf hFx
  rw [hempty, Set.ncard_empty, zero_add] at hmain
  exact hmain

/-- **The bordism invariance in the cofactor form of the face hypothesis.**  As in
`Work.Drive.even_ncard_blockMeet_sum_cofactor`, the third hypothesis is replaced by the scalar
condition that the tangential direction of the triple intersection `1`-manifold at each boundary zero
is not tangent to the face. -/
theorem even_ncard_wFaceMeet_add_wFaceMeet_cofactor
    (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tri3Diff W A B))
    (hreg : ∀ x ∈ unitBox 6, tri3Diff W A B x = 0 →
      Function.Surjective (fderiv ℝ (tri3Diff W A B) x))
    (hface : ∀ x ∈ unitBoxBdry 6, tri3Diff W A B x = 0 → ∃ i : Fin (6 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      cofactorVectorF (tri3Diff W A B) x i ≠ 0)
    (haux : ∀ x, x ∈ unitBox 6 → tri3AuxFace x → tri3Diff W A B x ≠ 0) :
    Even ((wFaceMeet W A B 0).ncard + (wFaceMeet W A B 1).ncard) :=
  even_ncard_wFaceMeet_add_wFaceMeet W A B hF hreg
    (fun x hx h0 => by
      obtain ⟨i, hi, hoth, hne⟩ := hface x hx h0
      exact ⟨i, hi, hoth, (surjective_domRestrict_iff_cofactorVec_ne_zero
        (fderiv ℝ (tri3Diff W A B) x) (hreg x hx.1 h0) i).mpr hne⟩)
    haux

/-- **The total boundary parity in the cofactor form of the face hypothesis.** -/
theorem even_ncard_tri3Diff_bdy_cofactor
    (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tri3Diff W A B))
    (hreg : ∀ x ∈ unitBox 6, tri3Diff W A B x = 0 →
      Function.Surjective (fderiv ℝ (tri3Diff W A B) x))
    (hface : ∀ x ∈ unitBoxBdry 6, tri3Diff W A B x = 0 → ∃ i : Fin (6 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      cofactorVectorF (tri3Diff W A B) x i ≠ 0) :
    Even ((tri3AuxMeet W A B).ncard + (wFaceMeet W A B 0).ncard
      + (wFaceMeet W A B 1).ncard) :=
  even_ncard_tri3Diff_bdy W A B hF hreg (fun x hx h0 => by
    obtain ⟨i, hi, hoth, hne⟩ := hface x hx h0
    exact ⟨i, hi, hoth, (surjective_domRestrict_iff_cofactorVec_ne_zero
      (fderiv ℝ (tri3Diff W A B) x) (hreg x hx.1 h0) i).mpr hne⟩)


/-! ## The two faces of the bordism, componentwise -/

/-- **The face intersections, in components.**  The set `wFaceMeet W A B e` is exactly the set of box
points at which the `e`-slice `W_e = W(e, ·, ·)` of the bordism meets both `A` and `B`.  For `e = 0`
this is `W₀ ⋔ A ⋔ B` and for `e = 1` it is `W₁ ⋔ A ⋔ B`, the two terms whose parities
`Work.Drive.even_ncard_wFaceMeet_add_wFaceMeet` compares. -/
lemma wFaceMeet_iff (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (e : ℝ)
    (x : EuclideanSpace ℝ (Fin 7)) :
    x ∈ wFaceMeet W A B e ↔ x ∈ unitBox 6 ∧ x (wI 0) = e ∧
      W (wPt x) = A (aPt x) ∧ W (wPt x) = B (bPt x) := by
  rw [wFaceMeet, Set.mem_setOf_eq, tri3Diff_eq_zero_iff]

/-- **The auxiliary faces, in components.** -/
lemma mem_tri3AuxMeet_iff (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 7)) :
    x ∈ tri3AuxMeet W A B ↔ x ∈ unitBox 6 ∧ tri3AuxFace x ∧ x (wI 0) ≠ 0
      ∧ x (wI 0) ≠ 1 ∧ W (wPt x) = A (aPt x) ∧ W (wPt x) = B (bPt x) := by
  rw [tri3AuxMeet, Set.mem_setOf_eq, tri3Diff_eq_zero_iff]

/-- **The hypothesis `haux` in components.**  The auxiliary faces carry no triple intersection
exactly when every point of the box at which the three chains meet and which lies on an auxiliary
face is excluded. -/
lemma tri3AuxFace_zero_free_iff (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    (∀ x, x ∈ unitBox 6 → tri3AuxFace x → tri3Diff W A B x ≠ 0) ↔
      ∀ x ∈ unitBox 6, tri3AuxFace x → ¬ (W (wPt x) = A (aPt x) ∧ W (wPt x) = B (bPt x)) := by
  constructor
  · intro h x hx hf hconj
    exact h x hx hf ((tri3Diff_eq_zero_iff W A B x).mpr hconj)
  · intro h x hx hf hzero
    exact h x hx hf ((tri3Diff_eq_zero_iff W A B x).mp hzero)


/-! ## The two `2`-chains as *closed* chains (identified faces)

In the application the two `2`-chains `A`, `B` are `2`-cycles of the level `≅ ℝP³`, presented in the
Heegaard (lens space) model by box maps whose *opposite faces are identified*: the gluing identifies
the four faces of each square in pairs.  For such chains the four side faces of the seven-box on which
`A` or `B` is on a face do **not** carry no zeros — instead their zeros are *paired* by the face
reflections, so they contribute an even number and drop out of the parity.  The vocabulary and the
resulting version of the bordism invariance are below. -/

/-- The point `(s, t)` of the unit square, as a point of `EuclideanSpace ℝ (Fin 2)`. -/
def sqPoint (s t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun j : Fin 2 => if j = 0 then s else t)

@[simp] lemma sqPoint_zero (s t : ℝ) : sqPoint s t 0 = s := by
  simp [sqPoint]

@[simp] lemma sqPoint_one (s t : ℝ) : sqPoint s t 1 = t := by
  simp [sqPoint]

/-- **A `2`-chain presented on the square with identified opposite faces**: the chain is *closed*
(`∂A = 0` as a chain, i.e. the gluing of the Heegaard model). -/
def IsClosedSq (A : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) : Prop :=
  (∀ t : ℝ, A (sqPoint 0 t) = A (sqPoint 1 t)) ∧
    (∀ s : ℝ, A (sqPoint s 0) = A (sqPoint s 1))

/-- The reflection of the first coordinate of the first `2`-block of the seven-box. -/
def flipA (x : EuclideanSpace ℝ (Fin 7)) : EuclideanSpace ℝ (Fin 7) :=
  WithLp.toLp 2 fun i => if i = aI2 0 then 1 - x i else x i

/-- The reflection of the first coordinate of the second `2`-block of the seven-box. -/
def flipB (x : EuclideanSpace ℝ (Fin 7)) : EuclideanSpace ℝ (Fin 7) :=
  WithLp.toLp 2 fun i => if i = bI2 0 then 1 - x i else x i

/-- One of the four side faces of the two `2`-chains is met. -/
def onABFace (x : EuclideanSpace ℝ (Fin 7)) : Prop := onAFace x ∨ onBFace x

/-- The reflection at the first coordinate of a block, read on that coordinate. -/
@[simp] lemma flipA_apply_zero (x : EuclideanSpace ℝ (Fin 7)) : flipA x (aI2 0) = 1 - x (aI2 0) := by
  simp [flipA]

lemma flipA_of_ne (x : EuclideanSpace ℝ (Fin 7)) {i : Fin 7} (h : i ≠ aI2 0) :
    flipA x i = x i := by
  simp [flipA, h]

@[simp] lemma flipB_apply_zero (x : EuclideanSpace ℝ (Fin 7)) : flipB x (bI2 0) = 1 - x (bI2 0) := by
  simp [flipB]

lemma flipB_of_ne (x : EuclideanSpace ℝ (Fin 7)) {i : Fin 7} (h : i ≠ bI2 0) :
    flipB x i = x i := by
  simp [flipB, h]

lemma flipA_flipA (x : EuclideanSpace ℝ (Fin 7)) : flipA (flipA x) = x := by
  rw [WithLp.ext_iff]
  funext i
  by_cases h : i = aI2 0 <;> simp [flipA, h]

lemma flipB_flipB (x : EuclideanSpace ℝ (Fin 7)) : flipB (flipB x) = x := by
  rw [WithLp.ext_iff]
  funext i
  by_cases h : i = bI2 0 <;> simp [flipB, h]

lemma flipA_mem_unitBox (x : EuclideanSpace ℝ (Fin 7)) {i : Fin 7} (hi : x i ∈ Set.Icc (0 : ℝ) 1) :
    flipA x i ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : i = aI2 0
  · subst h
    rw [flipA_apply_zero]
    exact ⟨by linarith [hi.2], by linarith [hi.1]⟩
  · rw [flipA_of_ne x h]; exact hi

lemma flipB_mem_unitBox (x : EuclideanSpace ℝ (Fin 7)) {i : Fin 7} (hi : x i ∈ Set.Icc (0 : ℝ) 1) :
    flipB x i ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : i = bI2 0
  · subst h
    rw [flipB_apply_zero]
    exact ⟨by linarith [hi.2], by linarith [hi.1]⟩
  · rw [flipB_of_ne x h]; exact hi

lemma flipA_ne_self (x : EuclideanSpace ℝ (Fin 7)) (h : x (aI2 0) = 0 ∨ x (aI2 0) = 1) :
    flipA x ≠ x := by
  intro heq
  have hc := congrArg (fun y : EuclideanSpace ℝ (Fin 7) => y (aI2 0)) heq
  rw [flipA_apply_zero] at hc
  rcases h with h | h <;> rw [h] at hc <;> norm_num at hc

lemma flipB_ne_self (x : EuclideanSpace ℝ (Fin 7)) (h : x (bI2 0) = 0 ∨ x (bI2 0) = 1) :
    flipB x ≠ x := by
  intro heq
  have hc := congrArg (fun y : EuclideanSpace ℝ (Fin 7) => y (bI2 0)) heq
  rw [flipB_apply_zero] at hc
  rcases h with h | h <;> rw [h] at hc <;> norm_num at hc

/-- `wPt` is unchanged by both reflections (they move only coordinates of the `2`-blocks). -/
lemma wPt_flipA (x : EuclideanSpace ℝ (Fin 7)) : wPt (flipA x) = wPt x := by
  rw [WithLp.ext_iff]
  funext j
  exact flipA_of_ne x (fun h => wI_ne_aI2 j 0 h)

lemma wPt_flipB (x : EuclideanSpace ℝ (Fin 7)) : wPt (flipB x) = wPt x := by
  rw [WithLp.ext_iff]
  funext j
  exact flipB_of_ne x (fun h => wI_ne_bI2 j 0 h)

/-- The first reflection exchanges the two faces `x (aI2 0) = 0` and `x (aI2 0) = 1`. -/
lemma aPt_flipA (x : EuclideanSpace ℝ (Fin 7)) :
    aPt (flipA x) = sqPoint (1 - x (aI2 0)) (x (aI2 1)) := by
  rw [WithLp.ext_iff]
  funext j
  fin_cases j
  · simp only [WithLp.ofLp_toLp, aPt_apply, sqPoint_zero]
    exact flipA_apply_zero x
  · simp only [WithLp.ofLp_toLp, aPt_apply, sqPoint_one]
    exact flipA_of_ne x (by decide)

/-- The second reflection exchanges the two faces `x (bI2 0) = 0` and `x (bI2 0) = 1`. -/
lemma bPt_flipB (x : EuclideanSpace ℝ (Fin 7)) :
    bPt (flipB x) = sqPoint (1 - x (bI2 0)) (x (bI2 1)) := by
  rw [WithLp.ext_iff]
  funext j
  fin_cases j
  · simp only [WithLp.ofLp_toLp, bPt_apply, sqPoint_zero]
    exact flipB_apply_zero x
  · simp only [WithLp.ofLp_toLp, bPt_apply, sqPoint_one]
    exact flipB_of_ne x (by decide)

lemma aPt_flipB (x : EuclideanSpace ℝ (Fin 7)) : aPt (flipB x) = aPt x := by
  rw [WithLp.ext_iff]
  funext j
  exact flipB_of_ne x (fun h => aI2_ne_bI2 j 0 h)

lemma bPt_flipA (x : EuclideanSpace ℝ (Fin 7)) : bPt (flipA x) = bPt x := by
  rw [WithLp.ext_iff]
  funext j
  exact flipA_of_ne x (fun h => (aI2_ne_bI2 0 j h.symm))


/-- The point `(a, b, c)` of the unit cube, as a point of `EuclideanSpace ℝ (Fin 3)`. -/
def t3 (a b c : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun j : Fin 3 => if j = 0 then a else if j = 1 then b else c

@[simp] lemma t3_zero (a b c : ℝ) : t3 a b c 0 = a := by simp [t3]
@[simp] lemma t3_one (a b c : ℝ) : t3 a b c 1 = b := by simp [t3]
@[simp] lemma t3_two (a b c : ℝ) : t3 a b c 2 = c := by simp [t3]

/-- **A `3`-chain presented on the cube whose two *transverse* coordinate directions are identified
in pairs**: a bordism inside a closed `3`-manifold.  Only the two `x₀`-faces survive in the chain
boundary, so `W` is a bordism between its two ends `W(0, ·, ·)` and `W(1, ·, ·)`. -/
def IsBordism3 (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : Prop :=
  (∀ a c : ℝ, W (t3 a 0 c) = W (t3 a 1 c)) ∧
    (∀ a b : ℝ, W (t3 a b 0) = W (t3 a b 1))

/-- The first `2`-block of the seven-box as a point of the square *without* the reflection. -/
lemma aPt_eq_sqPoint (x : EuclideanSpace ℝ (Fin 7)) :
    aPt x = sqPoint (x (aI2 0)) (x (aI2 1)) := by
  rw [WithLp.ext_iff]
  funext j
  fin_cases j <;> simp [sqPoint, aPt]

/-- The second `2`-block of the seven-box as a point of the square *without* the reflection. -/
lemma bPt_eq_sqPoint (x : EuclideanSpace ℝ (Fin 7)) :
    bPt x = sqPoint (x (bI2 0)) (x (bI2 1)) := by
  rw [WithLp.ext_iff]
  funext j
  fin_cases j <;> simp [sqPoint, bPt]

/-- The `3`-block of the seven-box as a point of the cube *without* the reflections. -/
lemma wPt_eq_t3 (x : EuclideanSpace ℝ (Fin 7)) :
    wPt x = t3 (x (wI 0)) (x (wI 1)) (x (wI 2)) := by
  rw [WithLp.ext_iff]
  funext j
  fin_cases j <;> simp [t3, wPt]


/-- The last two coordinates of the `3`-block of the seven-box. -/
def w2Pt (x : EuclideanSpace ℝ (Fin 7)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun j : Fin 2 => x (wI (Fin.succ j))

/-- The point of the cube with first coordinate `e` and last two coordinates those of `y`. -/
def mk3lev (e : ℝ) (y : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) := t3 e (y 0) (y 1)

/-- **The `e`-face of the `3`-chain `W`, as a `2`-chain.**  For `e = 0` this is `W₀ = W(0, ·, ·)` and
for `e = 1` it is `W₁ = W(1, ·, ·)`, the two ends of the bordism. -/
def faceChain (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (e : ℝ) :
    EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3) := fun y => W (mk3lev e y)

/-- The `3`-block of a box point with `x (wI 0) = e` is `mk3lev e` applied to its last two
coordinates. -/
lemma wPt_eq_mk3lev {x : EuclideanSpace ℝ (Fin 7)} {e : ℝ} (h : x (wI 0) = e) :
    wPt x = mk3lev e (w2Pt x) := by
  rw [WithLp.ext_iff]
  funext i
  fin_cases i <;> simp [wPt, mk3lev, t3, w2Pt, h]

/-- **The face intersections are the triple intersections of the face chain.**  The set
`wFaceMeet W A B e` is exactly the set of box points at which the face chain `W_e = faceChain W e`
(the `e`-slice of the bordism) meets both `A` and `B`.  Together with
`Work.Drive.even_ncard_wFaceMeet_add_wFaceMeet` this is the bordism invariance of the triple
intersection number of the two `2`-cycles `W₀`, `W₁` (the ends of the bordism) with the two fixed
`2`-chains `A`, `B`. -/
lemma wFaceMeet_iff_faceChain (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (e : ℝ)
    (x : EuclideanSpace ℝ (Fin 7)) :
    x ∈ wFaceMeet W A B e ↔ x ∈ unitBox 6 ∧ x (wI 0) = e ∧
      faceChain W e (w2Pt x) = A (aPt x) ∧ faceChain W e (w2Pt x) = B (bPt x) := by
  rw [wFaceMeet_iff]
  constructor
  · rintro ⟨hbox, h0, h1, h2⟩
    have hkey : wPt x = mk3lev e (w2Pt x) := wPt_eq_mk3lev h0
    exact ⟨hbox, h0, by rw [faceChain, ← hkey]; exact h1,
      by rw [faceChain, ← hkey]; exact h2⟩
  · rintro ⟨hbox, h0, h1, h2⟩
    have hkey : wPt x = mk3lev e (w2Pt x) := wPt_eq_mk3lev h0
    refine ⟨hbox, h0, ?_, ?_⟩
    · rw [faceChain, ← hkey] at h1
      exact h1
    · rw [faceChain, ← hkey] at h2
      exact h2


/-! ## The count as a `ZMod 2`-valued function

The fleet's order function is `ZMod 2`-valued (`Work.Drive.ParityCore`, `Work.Drive.OrderWitness`), so
the two slice counts are recorded here in that form, together with the arithmetic that turns the
parity statement of `even_ncard_wFaceMeet_add_wFaceMeet` into an equality of `ZMod 2` values. -/

/-- In `ZMod 2`, `m + n` even implies `m = n`. -/
lemma zmod2_eq_of_even_add {m n : ℕ} (h : Even (m + n)) : (m : ZMod 2) = (n : ZMod 2) := by
  have h2 : ((m : ZMod 2) + (n : ZMod 2)) = 0 := by
    obtain ⟨k, hk⟩ := h
    rw [← Nat.cast_add, hk, Nat.cast_add]
    exact CharTwo.add_self_eq_zero _
  have h3 : (m : ZMod 2) = -(n : ZMod 2) := add_eq_zero_iff_eq_neg.mp h2
  rw [h3, CharTwo.neg_eq]

/-- **The triple intersection number of the two ends of the bordism with the fixed chains `A`, `B`**,
as a `ZMod 2`-valued function of the slice parameter `e`. -/
def tri3Count (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (e : ℝ) : ZMod 2 :=
  ((wFaceMeet W A B e).ncard : ZMod 2)

/-- **The bordism invariance, in `ZMod 2` form.**  The two ends of the bordism `W` have the same
triple intersection number with the fixed chains `A`, `B`. -/
theorem tri3Count_eq_of_bordism
    (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (A B : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tri3Diff W A B))
    (hreg : ∀ x ∈ unitBox 6, tri3Diff W A B x = 0 →
      Function.Surjective (fderiv ℝ (tri3Diff W A B) x))
    (hface : ∀ x ∈ unitBoxBdry 6, tri3Diff W A B x = 0 → ∃ i : Fin (6 + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb 6 // v i = 0} =>
        fderiv ℝ (tri3Diff W A B) x v.1))
    (haux : ∀ x, x ∈ unitBox 6 → tri3AuxFace x → tri3Diff W A B x ≠ 0) :
    tri3Count W A B 0 = tri3Count W A B 1 :=
  zmod2_eq_of_even_add (even_ncard_wFaceMeet_add_wFaceMeet W A B hF hreg hface haux)


end

end Work.Drive
