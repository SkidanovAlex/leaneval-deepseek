import Mathlib
import ChallengeDeps
import Submission.Box
import Submission.Work.Smooth.Morse.All
import Submission.Work.Topology.SphereSlicing.All
import Submission.Work.BoxShrink.crux

/-!
# `Work.Smooth.BoxGeneric` — general position of the box-norm level sets

Pardon's box norm `boxNorm c σ y = max_i |y (σ i) - c (σ i)| / boxSide i` is the gauge of the box
`Submission.PBox s c σ`, whose level set `{boxNorm c σ · = s}` is the boundary sphere
`Work.Topology.SphereSlicing.BoxSphere s c σ`.  Unlike a smooth function it is only piecewise
smooth: it is the maximum of the six affine functions

`signedFace c σ i y = (y (σ i) - c (σ i)) / boxSide i`,  `± signedFace c σ i y`,

and it fails to be differentiable exactly where two of the face norms tie.  This file provides the
vocabulary of the chapter (the faces, the box norm as their maximum, and the tight/corner/vertex
predicates).  The chapter proves the a.e. general position of the box-norm level sets from the
classification of compact `1`-manifolds and Jordan–Schoenflies alone; the predicates `SardCoord`,
`AeTransverseCorner` and `AeNoVertex` defined below were the inputs of its first version and are
superseded by theorems (see the section "The predicates of the chapter" and the README).

## The vocabulary

* `signedFace c σ i`, `faceNorm c σ i = |signedFace c σ i|`, `faceLin c σ i ε = ε * signedFace c σ i`:
  the three faces and the six signed faces of the box; the box norm is the maximum of the three
  face norms;
* `IsActiveFace c σ s i y` — the face norm `i` attains the value `s` at `y` and is the maximum
  there (the face is *tight*); `IsActiveSignedFace` records which of the two opposite faces of the
  pair is the tight one;
* `IsCornerPoint c σ s y` — two distinct faces are tight at `y` (a point of an edge of the box
  sphere); `IsBoxVertexPoint c σ s y` — three faces are tight at `y` (a vertex of the box sphere);
* the intermediate genericity predicates `SardCoord` (Sard for the coordinate functions on the
  surface), `AeTransverseCorner` (no tangential edge crossings) and `AeNoVertex` (the surface avoids
  the vertices of the box); and the target `AeTransverseBox` (almost every box sphere meets the
  surface in general position).

## Why the box norm needs its own chapter

The box norm is `C^{0,1}` and not `C¹`: on the open set where a fixed face attains the strict
maximum it agrees with the smooth function `faceLin c σ i ε`, and on the tie locus
`faceNorm i = faceNorm j` it is the maximum of two smooth functions with a kink.  A level `s` is
*good* when

* no point of the level set is a critical point of the active face function (this is `SardCoord`),
  and
* no point of the level set is a tangential corner: at a corner the two active face cuts must
  cross transversally for the level set to be locally an arc (`AeTransverseCorner`), and no point
  of the level set is a vertex of the box (`AeNoVertex`).

Given those, the level set is a compact set which is locally an arc, hence — by the classification
of compact `1`-manifolds, carried as the input `Work.Smooth.Morse.CompactOneManifoldInput` — a
finite disjoint union of simple closed curves of the surface: this is `AeTransverseBox`, and it is
the geometric content of `Work.BoxShrink.AeSliced`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped Topology

namespace Work.Smooth.BoxGeneric

noncomputable section

variable {c : R3} {σ : Equiv.Perm (Fin 3)}

/-! ## The faces of Pardon's box -/

/-- The `i`-th **signed face coordinate** of the box of centre `c` and coordinate permutation `σ`:
the affine function `y ↦ (y (σ i) - c (σ i)) / boxSide i`.  Its level sets are the pairs of
opposite faces of the box. -/
def signedFace (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (y : R3) : ℝ :=
  (y (σ i) - c (σ i)) / Submission.boxSide i

/-- The `i`-th **face norm**: the absolute value of the signed face coordinate. -/
def faceNorm (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (y : R3) : ℝ :=
  |y (σ i) - c (σ i)| / Submission.boxSide i

/-- The `i`-th **signed face function** with sign `ε`: `ε * signedFace c σ i`.  For `ε = 1` and
`ε = -1` these are the two faces of the box in the `σ i` direction; the box norm is the maximum of
the six functions `faceLin c σ i ε` over `i` and `ε = ±1`. -/
def faceLin (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (ε : ℝ) (y : R3) : ℝ :=
  ε * signedFace c σ i y

@[simp] theorem signedFace_apply (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (y : R3) :
    signedFace c σ i y = (y (σ i) - c (σ i)) / Submission.boxSide i := rfl

@[simp] theorem faceNorm_apply (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (y : R3) :
    faceNorm c σ i y = |y (σ i) - c (σ i)| / Submission.boxSide i := rfl

@[simp] theorem faceLin_apply (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (ε : ℝ) (y : R3) :
    faceLin c σ i ε y = ε * signedFace c σ i y := rfl

theorem faceLin_one (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (y : R3) :
    faceLin c σ i 1 y = signedFace c σ i y := by simp

theorem faceLin_neg_one (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (y : R3) :
    faceLin c σ i (-1) y = -signedFace c σ i y := by simp

theorem faceNorm_eq_abs_signedFace (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (y : R3) :
    faceNorm c σ i y = |signedFace c σ i y| := by
  rw [faceNorm, signedFace, abs_div, abs_of_pos (Submission.boxSide_pos i)]

/-- The face norm is the maximum of the two opposite signed faces. -/
theorem faceNorm_eq_max_faceLin (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (y : R3) :
    faceNorm c σ i y = max (faceLin c σ i 1 y) (faceLin c σ i (-1) y) := by
  rw [faceNorm_eq_abs_signedFace, faceLin_one, faceLin_neg_one]
  exact (abs_eq_max_neg).symm

/-! ## The box norm is the maximum of the three face norms -/

/-- **The box norm is the maximum of the three face norms.** -/
theorem boxNorm_eq_max_faceNorm (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) :
    Submission.boxNorm c σ y =
      max (max (faceNorm c σ 0 y) (faceNorm c σ 1 y)) (faceNorm c σ 2 y) := rfl

theorem faceNorm_le_boxNorm (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (y : R3) :
    faceNorm c σ i y ≤ Submission.boxNorm c σ y := by
  rw [boxNorm_eq_max_faceNorm]
  fin_cases i
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_max_right _ _

theorem boxNorm_le_iff (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (y : R3) :
    Submission.boxNorm c σ y ≤ s ↔ ∀ i : Fin 3, faceNorm c σ i y ≤ s := by
  rw [boxNorm_eq_max_faceNorm, max_le_iff, max_le_iff]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro h
    exact ⟨⟨h 0, h 1⟩, h 2⟩

theorem lt_boxNorm_iff (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (y : R3) :
    s < Submission.boxNorm c σ y ↔ ∃ i : Fin 3, s < faceNorm c σ i y := by
  rw [boxNorm_eq_max_faceNorm, lt_max_iff, lt_max_iff]
  constructor
  · rintro (⟨h | h⟩ | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi

/-- Some face norm attains the box norm. -/
theorem exists_faceNorm_eq_boxNorm (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) :
    ∃ i : Fin 3, faceNorm c σ i y = Submission.boxNorm c σ y := by
  rw [boxNorm_eq_max_faceNorm]
  rcases le_total (faceNorm c σ 0 y) (faceNorm c σ 1 y) with h | h
  · rcases le_total (faceNorm c σ 1 y) (faceNorm c σ 2 y) with h2 | h2
    · exact ⟨2, by rw [max_eq_right h, max_eq_right h2]⟩
    · exact ⟨1, by rw [max_eq_right h, max_eq_left h2]⟩
  · rcases le_total (faceNorm c σ 0 y) (faceNorm c σ 2 y) with h2 | h2
    · exact ⟨2, by rw [max_eq_left h, max_eq_right h2]⟩
    · exact ⟨0, by rw [max_eq_left h, max_eq_left h2]⟩

theorem faceNorm_nonneg (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (y : R3) :
    0 ≤ faceNorm c σ i y := div_nonneg (abs_nonneg _) (le_of_lt (Submission.boxSide_pos i))

/-- The box norm vanishes exactly at the centre. -/
theorem boxNorm_eq_zero_iff (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) :
    Submission.boxNorm c σ y = 0 ↔ y = c := by
  constructor
  · intro h
    have hle : ∀ i : Fin 3, faceNorm c σ i y ≤ 0 := (boxNorm_le_iff c σ 0 y).mp (le_of_eq h)
    have h0 : ∀ i : Fin 3, y (σ i) - c (σ i) = 0 := fun i => by
      have hi : |y (σ i) - c (σ i)| / Submission.boxSide i ≤ 0 := hle i
      rw [div_le_iff₀ (Submission.boxSide_pos i)] at hi
      have h2 : |y (σ i) - c (σ i)| = 0 :=
        le_antisymm (by simpa using hi) (abs_nonneg _)
      have h3 : y (σ i) - c (σ i) = 0 := abs_eq_zero.mp h2
      linarith
    ext j
    have h4 := h0 (σ.symm j)
    simp only [Equiv.apply_symm_apply] at h4
    linarith
  · intro h
    subst h
    rw [boxNorm_eq_max_faceNorm]
    simp [faceNorm, sub_self]

theorem boxNorm_pos_iff (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) :
    0 < Submission.boxNorm c σ y ↔ y ≠ c := by
  refine ⟨fun h hy => ?_, fun h => lt_of_le_of_ne (Submission.boxNorm_nonneg c σ y) ?_⟩
  · rw [hy] at h
    rw [(boxNorm_eq_zero_iff c σ c).mpr rfl] at h
    exact lt_irrefl 0 h
  · intro h0
    exact h ((boxNorm_eq_zero_iff c σ y).mp h0.symm)

/-! ## Tight faces, corners and vertices of the box sphere -/

/-- The face `i` is **tight** (active) at `y` for the level `s`: its face norm equals `s` and is
the maximum of the three face norms. -/
def IsActiveFace (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (i : Fin 3) (y : R3) : Prop :=
  faceNorm c σ i y = s ∧ ∀ j : Fin 3, faceNorm c σ j y ≤ s

/-- The face `i` is tight at `y` for the level `s` *and* the sign of the coordinate is `ε`:
the signed face function `faceLin c σ i ε` equals `s` at `y`. -/
def IsActiveSignedFace (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (i : Fin 3) (ε : ℝ) (y : R3) :
    Prop :=
  faceLin c σ i ε y = s ∧ ∀ j : Fin 3, faceNorm c σ j y ≤ s

/-- `y` is a **corner point** of the box sphere of level `s`: two distinct faces are tight. -/
def IsCornerPoint (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (y : R3) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧ IsActiveFace c σ s i y ∧ IsActiveFace c σ s j y

/-- `y` is a **vertex** of the box sphere of level `s`: all three faces are tight. -/
def IsBoxVertexPoint (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (y : R3) : Prop :=
  ∀ i : Fin 3, faceNorm c σ i y = s

theorem IsActiveFace.boxNorm_eq {s : ℝ} {i : Fin 3} {y : R3} (h : IsActiveFace c σ s i y) :
    Submission.boxNorm c σ y = s :=
  le_antisymm ((boxNorm_le_iff c σ s y).mpr h.2)
    (h.1 ▸ faceNorm_le_boxNorm c σ i y)

theorem isActiveFace_of_boxNorm_eq (c : R3) (σ : Equiv.Perm (Fin 3)) {s : ℝ} {y : R3}
    (h : Submission.boxNorm c σ y = s) : ∃ i : Fin 3, IsActiveFace c σ s i y := by
  obtain ⟨i, hi⟩ := exists_faceNorm_eq_boxNorm c σ y
  exact ⟨i, by rw [hi, h], fun j => by rw [← h]; exact faceNorm_le_boxNorm c σ j y⟩

/-- **The box sphere is the union of its tight faces.** -/
theorem BoxSphere_eq_iUnion_active (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) :
    {y : R3 | Submission.boxNorm c σ y = s} =
      ⋃ i : Fin 3, {y : R3 | IsActiveFace c σ s i y} := by
  ext y
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · intro h
    exact isActiveFace_of_boxNorm_eq c σ h
  · rintro ⟨i, hi⟩
    exact hi.boxNorm_eq

theorem IsActiveFace.faceNorm_le {s : ℝ} {i j : Fin 3} {y : R3}
    (h : IsActiveFace c σ s i y) : faceNorm c σ j y ≤ s := h.2 j

theorem IsActiveFace.nonneg {s : ℝ} {i : Fin 3} {y : R3} (h : IsActiveFace c σ s i y) :
    0 ≤ s := by
  rw [← h.1]
  exact faceNorm_nonneg c σ i y

theorem IsCornerPoint.of_active {s : ℝ} {i j : Fin 3} {y : R3} (hij : i ≠ j)
    (hi : IsActiveFace c σ s i y) (hj : IsActiveFace c σ s j y) : IsCornerPoint c σ s y :=
  ⟨i, j, hij, hi, hj⟩

theorem IsBoxVertexPoint.isActiveFace {s : ℝ} {y : R3} (h : IsBoxVertexPoint c σ s y)
    (i : Fin 3) : IsActiveFace c σ s i y :=
  ⟨h i, fun j => le_of_eq (h j)⟩

theorem IsCornerPoint.boxNorm_eq {s : ℝ} {y : R3} (h : IsCornerPoint c σ s y) :
    Submission.boxNorm c σ y = s := by
  obtain ⟨i, j, -, hi, -⟩ := h
  exact hi.boxNorm_eq

/-! ## Smoothness of the faces -/

theorem contDiff_signedFace (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (signedFace c σ i) := by
  unfold signedFace
  fun_prop

theorem contDiff_faceLin (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (faceLin c σ i ε) := by
  have h := contDiff_signedFace c σ i
  unfold faceLin
  fun_prop

theorem continuous_faceNorm (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    Continuous (faceNorm c σ i) := by
  unfold faceNorm
  fun_prop

theorem pullback_signedFace_contDiff (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (Work.Smooth.Morse.pullback ψ (signedFace c σ i)) :=
  Work.Smooth.Morse.pullback_contDiff ψ (contDiff_signedFace c σ i)

theorem pullback_faceLin_contDiff (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) :=
  Work.Smooth.Morse.pullback_contDiff ψ (contDiff_faceLin c σ i ε)

theorem pullback_signedFace_eq (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) (p : ℝ × ℝ) :
    Work.Smooth.Morse.pullback ψ (signedFace c σ i) p =
      (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i)) p - c (σ i)) / Submission.boxSide i :=
  rfl

/-- The level set of the box norm at `s` is the trace of the box sphere on the surface. -/
theorem levelSet_boxNorm_eq (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) :
    Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s =
      (Work.Smooth.Morse.torus ψ).carrier ∩ Work.Topology.SphereSlicing.BoxSphere s c σ := rfl

theorem levelSet_boxNorm_subset_boxSphere (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (s : ℝ) :
    Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s ⊆
      Work.Topology.SphereSlicing.BoxSphere s c σ :=
  inter_subset_right

/-! ## The predicates of the chapter

The predicates defined in this section were the *inputs* of the first version of the chapter.  They
are all superseded by theorems:

* `SardCoord ψ` is proved for every `ψ` (`Work.Smooth.BoxGeneric.Sard.sardCoord`, from the
  two-dimensional Sard theorem of `Submission/Work/Smooth/BoxGeneric/Sard/`);
* `AeTransverseCorner ψ c σ` is proved for every `ψ, c, σ`
  (`Work.Smooth.BoxGeneric.AeCorner.ae_transverseCorner_of_regularBisector`);
* `AeNoVertex ψ c σ` is *not needed*: the vertex strata are handled by the a.e.-tangency argument of
  `Submission/Work/Smooth/BoxGeneric/AeVertex.lean` (see the README, §5.3).

The definitions are kept because they state the intermediate genericity notions precisely, and
because the earlier interfaces of `AeBox.lean`, `AeMain.lean` and `AeCentre.lean` are phrased with
them.
-/

/-- **The Sard input for the coordinate functions**, in the vocabulary of the sibling chapter
`Submission/Work/Smooth/Morse`: almost every level of the coordinate function `y ↦ y i` restricted
to the surface `F = ψ(standard torus)` is a regular value, i.e. the level set `F ∩ {y i = u}` has
no point at which the derivative of the restriction vanishes.

This is Sard's theorem for a `C^∞` function on a compact surface; Mathlib contains no Sard theorem
(and Sard is false for merely `C¹` maps in this dimension, so the `C^∞` hypothesis matters).  It is
proved for every `ψ` in `Work.Smooth.BoxGeneric.Sard.sardCoord`. -/
def SardCoord (ψ : Submission.Diffeo) : Prop :=
  ∀ i : Fin 3, ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
    Work.Smooth.Morse.IsRegularValue ψ (fun y : R3 => y i) u

/-- The same Sard input for the signed face functions `signedFace c σ i` of the box (an affine
translate and rescale of the coordinate function, so the two inputs are equivalent). -/
def SardFace (ψ : Submission.Diffeo) : Prop :=
  ∀ (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3),
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Smooth.Morse.IsRegularValue ψ (signedFace c σ i) u

/-- `SardCoord` in the form of the sibling chapter's input: the a.e.-regularity of the
coordinate functions (`Work.Smooth.Morse.AERegularValues`). -/
theorem sardCoord_of_aeRegularValues {ψ : Submission.Diffeo}
    (h : ∀ i : Fin 3, Work.Smooth.Morse.AERegularValues ψ (fun y : R3 => y i)) : SardCoord ψ := h

/-- **The two face cuts at a corner cross transversally.**

For a point `y` of the surface at which the faces `(i, ε)` and `(j, ε')` are tight, the cuts
`F ∩ {faceLin i ε = s}` and `F ∩ {faceLin j ε' = s}` are two curves through `y` with tangent
lines `ker dG_i`, `ker dG_j` in the tangent plane of the surface (`G_i`,
`G_j` the pulled-back face functions at a parameter `p` over `y`); they are *tangent* to each
other exactly when these two lines coincide, i.e. exactly when the pair
`(dG_i, dG_j) : ℝ × ℝ → ℝ × ℝ` is **not** invertible.  This predicate records the complementary
(generic) case: the pair of derivatives is invertible, so the map `(G_i - s, G_j - s)` is a local
diffeomorphism at `p`.

(The predicate is independent of the choice of the parameter `p` over `y`, because the parameters
over `y` differ by translations of the parameter plane 2πℤ².) -/
def CornerTransverseAt (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3)
    (ε ε' : ℝ) (y : R3) : Prop :=
  ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧
    ((fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) p).prod
      (fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ j ε')) p)).IsInvertible

/-- **Almost every level of the box norm has only transverse corners.** -/
def AeTransverseCorner (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) : Prop :=
  ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
    ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier, Submission.boxNorm c σ y = s →
      ∀ (i j : Fin 3) (ε ε' : ℝ), i ≠ j →
        IsActiveSignedFace c σ s i ε y → IsActiveSignedFace c σ s j ε' y →
          CornerTransverseAt ψ c σ i j ε ε' y

/-- **Almost every box sphere avoids the vertices of the box.** -/
def AeNoVertex (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) : Prop :=
  ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
    ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier, ¬ IsBoxVertexPoint c σ s y

/-- **Almost every box sphere meets the surface in general position**, in the transversality form
of `Work.Topology.SphereSlicing.TransverseSphere`: the intersection is a finite disjoint union of
simple closed curves of the surface.  This is the geometric content of the target
`Work.BoxShrink.AeSliced`. -/
def AeTransverseBox (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) : Prop :=
  ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
    Work.Topology.SphereSlicing.TransverseSphere (Work.Smooth.Morse.torus ψ)
      {y : R3 | Submission.boxNorm c σ y = s}

end

end Work.Smooth.BoxGeneric
