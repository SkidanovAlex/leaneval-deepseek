import Mathlib
import Submission.Work.Core.Torus

/-!
# Halving a box by a Euclidean isometry

This file provides `Work.Geometry.box_halving`: for every `r > 0` there is an
isometry of `ℝ³` that carries the box

`{p | |p 0| < r, |p 1| < 2^(1/3) * r, 0 ≤ p 2 < 2^(2/3) * r}`

into the box

`{q | |q 0| < 2^(1/3) * r, |q 1| < 2^(2/3) * r, |q 2| < r}`.

The isometry is the coordinate permutation `(p₀, p₁, p₂) ↦ (p₁, p₂ - d, p₀)`
with `d = 2^(2/3) * r / 2`, i.e. a cyclic permutation of the three coordinates
followed by a translation in one coordinate.  This is the elementary geometric
step in Pardon's proof of the torus-knot distortion bound: a fundamental
half-open box of the "thickened" torus can be rigidly moved into the central
box.
-/

namespace Work.Geometry

noncomputable section

/-- The coordinate permutation `(p₀, p₁, p₂) ↦ (p₁, p₂ - d, p₀)` on `ℝ³`. -/
def boxMap (d : ℝ) : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
  fun p => WithLp.toLp 2 ![p 1, p 2 - d, p 0]

/-- The inverse of `boxMap d`, namely `(q₀, q₁, q₂) ↦ (q₂, q₀, q₁ + d)`. -/
def boxMapSymm (d : ℝ) : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
  fun q => WithLp.toLp 2 ![q 2, q 0, q 1 + d]

@[simp] lemma boxMap_apply (d : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    boxMap d p = WithLp.toLp 2 ![p 1, p 2 - d, p 0] := rfl

@[simp] lemma boxMapSymm_apply (d : ℝ) (q : EuclideanSpace ℝ (Fin 3)) :
    boxMapSymm d q = WithLp.toLp 2 ![q 2, q 0, q 1 + d] := rfl

@[simp] lemma boxMap_zero (d : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    (boxMap d p) 0 = p 1 := by simp [boxMap]

@[simp] lemma boxMap_one (d : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    (boxMap d p) 1 = p 2 - d := by simp [boxMap]

@[simp] lemma boxMap_two (d : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    (boxMap d p) 2 = p 0 := by simp [boxMap]

/-- `boxMap d` is a Euclidean isometry: it merely permutes the coordinates and
shifts one of them. -/
lemma boxMap_isometry (d : ℝ) : Isometry (boxMap d) := by
  rw [isometry_iff_dist_eq]
  intro p q
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  congr 1
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [boxMap, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  simp only [Real.dist_eq]
  have hmid : (p.ofLp 2 - d) - (q.ofLp 2 - d) = p.ofLp 2 - q.ofLp 2 := by ring
  rw [hmid]
  ring

/-- `boxMapSymm d` is a right inverse of `boxMap d`. -/
lemma boxMap_symm_boxMap (d : ℝ) (q : EuclideanSpace ℝ (Fin 3)) :
    boxMap d (boxMapSymm d q) = q := by
  ext i
  fin_cases i <;> simp [boxMap, boxMapSymm]

/-- The bijection underlying the halving isometry. -/
def boxMapEquiv (d : ℝ) : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3) :=
  IsometryEquiv.mk' (boxMap d) (boxMapSymm d) (boxMap_symm_boxMap d) (boxMap_isometry d)

/-- The halving isometry of `box_halving`, with `d = 2^(2/3) * r / 2`. -/
def boxHalving (d : ℝ) : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3) :=
  boxMapEquiv d

@[simp] lemma boxHalving_apply (d : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    boxHalving d p = boxMap d p := rfl

/-- **Box halving.**  For every `r > 0` there is an isometry of `ℝ³` carrying the
box `{|p 0| < r, |p 1| < 2^(1/3) * r, 0 ≤ p 2 < 2^(2/3) * r}` into the box
`{|q 0| < 2^(1/3) * r, |q 1| < 2^(2/3) * r, |q 2| < r}`. -/
theorem box_halving (r : ℝ) (hr : 0 < r) :
    ∃ e : EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3),
      e '' {p : EuclideanSpace ℝ (Fin 3) |
          |p 0| < r ∧ |p 1| < 2 ^ (1 / 3 : ℝ) * r ∧ (0 : ℝ) ≤ p 2
            ∧ p 2 < 2 ^ (2 / 3 : ℝ) * r} ⊆
        {q : EuclideanSpace ℝ (Fin 3) |
          |q 0| < 2 ^ (1 / 3 : ℝ) * r ∧ |q 1| < 2 ^ (2 / 3 : ℝ) * r ∧ |q 2| < r} := by
  set d : ℝ := 2 ^ (2 / 3 : ℝ) * r / 2 with hd
  have hdp : 0 < d := by rw [hd]; positivity
  have hd2 : 2 * d = 2 ^ (2 / 3 : ℝ) * r := by rw [hd]; ring
  refine ⟨boxHalving d, ?_⟩
  rintro q ⟨p, hp, rfl⟩
  obtain ⟨h0, h1, h2a, h2b⟩ := hp
  have e0 : (boxHalving d p) 0 = p 1 := by
    change (boxMap d p) 0 = p 1; simp
  have e1 : (boxHalving d p) 1 = p 2 - d := by
    change (boxMap d p) 1 = p 2 - d; simp
  have e2 : (boxHalving d p) 2 = p 0 := by
    change (boxMap d p) 2 = p 0; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [e0]; exact h1
  · rw [e1, abs_lt]; constructor <;> linarith
  · rw [e2]; exact h0

end

end Work.Geometry
