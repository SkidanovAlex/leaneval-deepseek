import Mathlib
import Submission.Work.Drive.N2.HeightBasics

/-!
# Splitting `ℝ⁵` along a pair of coordinate directions

For distinct indices `a b : Fin 5` we split `ℝ⁵` as the direct sum of the two-dimensional space
`D_{ab}` spanned by the standard basis vectors `e_a`, `e_b` (the "dependent" directions) and its
orthogonal complement (the "free" directions).

`depProj` extracts the `a`,`b` coordinates (as an element of `ℝ²`) and `depIns` inserts a pair of
reals into those slots; `freePart = 1 - depIns ∘ depProj` is the projection onto the complement of
`D_{ab}`.

This is the linear algebra used to *parametrise* the critical-point bundle of a chart
representation `F : ℝ² → ℝ⁵`: whenever the `(a,b)`-minor `depProj ∘ DF(y)` is bijective, the
critical directions `v` of `y ↦ ⟪v, F y⟫` are read off from their free part.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff RealInnerProductSpace
open Work.Drive.Morse

/-- The two coordinates of `v ∈ ℝ⁵` in the slots `a`, `b`, as an element of `ℝ²`. -/
noncomputable def depProj (a b : Fin 5) : EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ContinuousLinearMap.comp
    ((EuclideanSpace.equiv (Fin 2) ℝ).symm).toContinuousLinearMap
    (ContinuousLinearMap.pi (fun i : Fin 2 =>
      if (i : ℕ) = 0 then EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 5) a
        else EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 5) b))

@[simp] lemma depProj_apply_zero (a b : Fin 5) (v : EuclideanSpace ℝ (Fin 5)) :
    depProj a b v 0 = v a := rfl

@[simp] lemma depProj_apply_one (a b : Fin 5) (v : EuclideanSpace ℝ (Fin 5)) :
    depProj a b v 1 = v b := rfl

/-- The insertion of a pair of reals into the slots `a`, `b`, with zeros elsewhere. -/
noncomputable def depIns (a b : Fin 5) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 5) :=
  ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).smulRight (EuclideanSpace.single a (1 : ℝ))) +
    ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).smulRight (EuclideanSpace.single b (1 : ℝ)))

lemma depIns_apply (a b : Fin 5) (u : EuclideanSpace ℝ (Fin 2)) :
    depIns a b u = u 0 • EuclideanSpace.single a (1 : ℝ) + u 1 • EuclideanSpace.single b (1 : ℝ) := by
  rw [depIns, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply]
  rfl

/-- The projection onto the orthogonal complement of the span of `e_a`, `e_b`. -/
noncomputable def freePart (a b : Fin 5) :
    EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 5) :=
  1 - (depIns a b).comp (depProj a b)

@[simp] lemma depProj_depIns {a b : Fin 5} (hab : a ≠ b) (u : EuclideanSpace ℝ (Fin 2)) :
    depProj a b (depIns a b u) = u := by
  ext i
  fin_cases i <;>
    simp [depIns_apply, PiLp.single_apply, hab, hab.symm]

@[simp] lemma depProj_freePart {a b : Fin 5} (hab : a ≠ b) (v : EuclideanSpace ℝ (Fin 5)) :
    depProj a b (freePart a b v) = 0 := by
  simp [freePart, depProj_depIns hab]

@[simp] lemma freePart_depIns {a b : Fin 5} (hab : a ≠ b) (u : EuclideanSpace ℝ (Fin 2)) :
    freePart a b (depIns a b u) = 0 := by
  simp only [freePart, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply, depProj_depIns hab, sub_self]

/-- The decomposition of `v` into its free part and its `(a,b)`-part. -/
lemma freePart_add_depIns (a b : Fin 5) (v : EuclideanSpace ℝ (Fin 5)) :
    freePart a b v + depIns a b (depProj a b v) = v := by
  simp only [freePart, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply]
  abel

/-- The inner product pairing with the inserted vector `depIns a b u`. -/
lemma inner_depIns (a b : Fin 5) (u : EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 5)) :
    ⟪depIns a b u, z⟫ = u 0 * z a + u 1 * z b := by
  rw [depIns_apply, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
  simp only [map_one, one_mul, mul_comm]

/-! ### The `(a,b)`-minor of a chart representation, and the bad set of a chart -/

/-- The `(a,b)`-minor of the derivative at `y` of a chart representation `F`. -/
noncomputable def minor (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5)) (a b : Fin 5)
    (y : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (depProj a b).comp (fderiv ℝ F y)

/-- A direction `v` is *bad* for the chart representation `F` on the set `T` if the function
`y ↦ ⟪v, F y⟫` has a critical point in `T` at which it is degenerate. -/
def BadSet (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5))
    (T : Set (EuclideanSpace ℝ (Fin 2))) (v : EuclideanSpace ℝ (Fin 5)) : Prop :=
  ∃ y ∈ T, fderiv ℝ (chartHeight F v) y = 0 ∧
    ¬ Function.Injective (fderiv ℝ (fderiv ℝ (chartHeight F v)) y)

/-- The set of bad directions, as a set. -/
def badSet (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5))
    (T : Set (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 5)) :=
  {v | BadSet F T v}

theorem mem_badSet {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 5)}
    {T : Set (EuclideanSpace ℝ (Fin 2))}
    {v : EuclideanSpace ℝ (Fin 5)} : v ∈ badSet F T ↔ BadSet F T v := Iff.rfl

end Work.Drive.N2
