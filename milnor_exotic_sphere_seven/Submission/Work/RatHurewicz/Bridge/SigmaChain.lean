import Mathlib
import Submission.Work.RatHurewicz.Bridge.SimChainMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The chain carried by a simplex which is constant on the simplicial boundary is a cycle

If `s : Δⁿ → X` is constant on the boundary `{z | ∃ j, z j = 0}` of the standard simplex, then
`simpChain n s - simpChain n (const y)` is a cycle.
-/

open scoped unitInterval Topology Simplicial
open CategoryTheory AlgebraicTopology
open Work.Stems.Cubical

namespace Work.RatHurewicz.Bridge

noncomputable section

/-- The `y`-coordinate of `stdSimplex.map f z` vanishes when no `x` is mapped to `y`. -/
theorem stdSimplex_map_eq_zero_of_ne {a b : ℕ} (f : Fin a → Fin b)
    (z : stdSimplex ℝ (Fin a)) (y : Fin b) (hy : ∀ x, f x ≠ y) :
    (stdSimplex.map f z) y = 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [if_neg]
  exact fun h => hy x h

/-- The `i`-th coordinate of the `i`-th coface vanishes. -/
theorem coface_apply_self (m : ℕ) (i : Fin (m + 2)) (z : stdSimplex ℝ (Fin (m + 1))) :
    coface m i z i = 0 := by
  rw [coface_apply]
  exact stdSimplex_map_eq_zero_of_ne _ _ _ fun k => Fin.succAbove_ne i k

/-- The `i`-th face of the singular simplex attached to `s`. -/
theorem toSSetObjEquiv_delta_simplexOf {X : Type} [TopologicalSpace X] (m : ℕ)
    (s : C(stdSimplex ℝ (Fin (m + 2)), X)) (i : Fin (m + 2)) :
    (((TopCat.of X).toSSetObjEquivOld (Opposite.op (SimplexCategory.mk m)))
        (((TopCat.toSSet.obj (TopCat.of X)).δ i) (simplexOf (m + 1) s)))
      = s.comp (coface m i) := by
  ext z
  rw [ContinuousMap.comp_apply, TopCat.toSSetObjEquivOld_δ_apply, toSSetObjEquiv_simplexOf]
  rfl

/-- The `i`-th face of the singular simplex attached to the constant map. -/
theorem toSSetObjEquiv_delta_simplexOf_const {X : Type} [TopologicalSpace X] (m : ℕ)
    (y : X) (i : Fin (m + 2)) :
    (((TopCat.of X).toSSetObjEquivOld (Opposite.op (SimplexCategory.mk m)))
        (((TopCat.toSSet.obj (TopCat.of X)).δ i)
          (simplexOf (m + 1) (ContinuousMap.const (stdSimplex ℝ (Fin (m + 2))) y))))
      = ContinuousMap.const (stdSimplex ℝ (Fin (m + 1))) y := by
  ext z
  rw [TopCat.toSSetObjEquivOld_δ_apply, toSSetObjEquiv_simplexOf]
  rfl

/-- **The reduced chain of a simplex constant on the boundary is a cycle** (successor form). -/
theorem sigmaChain_cycle_succ (m : ℕ) {X : Type} [TopologicalSpace X]
    (s : C(stdSimplex ℝ (Fin (m + 2)), X)) (y : X)
    (hy : ∀ z : stdSimplex ℝ (Fin (m + 2)),
        (∃ j : Fin (m + 2), z j = 0) → s z = y) :
    (Work.Cohomology.singularChains ℤ (TopCat.of X)).d (m + 1) m
      (simpChain (m + 1) s
        - simpChain (m + 1) (ContinuousMap.const (stdSimplex ℝ (Fin (m + 2))) y)) = 0 := by
  have hA : ∀ i : Fin (m + 2),
      (((TopCat.of X).toSSetObjEquivOld (Opposite.op (SimplexCategory.mk m)))
        (((TopCat.toSSet.obj (TopCat.of X)).δ i) (simplexOf (m + 1) s)))
      = s.comp (coface m i) := fun i => toSSetObjEquiv_delta_simplexOf m s i
  have hB : ∀ i : Fin (m + 2),
      (((TopCat.of X).toSSetObjEquivOld (Opposite.op (SimplexCategory.mk m)))
        (((TopCat.toSSet.obj (TopCat.of X)).δ i)
          (simplexOf (m + 1) (ContinuousMap.const (stdSimplex ℝ (Fin (m + 2))) y))))
      = ContinuousMap.const (stdSimplex ℝ (Fin (m + 1))) y :=
    fun i => toSSetObjEquiv_delta_simplexOf_const m y i
  have hS : (Work.Cohomology.singularChains ℤ (TopCat.of X)).d (m + 1) m (simpChain (m + 1) s)
      = ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • simpChain m (s.comp (coface m i)) := by
    have h := d_simpChain m (TopCat.of X) (simplexOf (m + 1) s)
    rw [toSSetObjEquiv_simplexOf (m + 1) s] at h
    refine h.trans ?_
    exact Finset.sum_congr rfl fun i _ => by rw [hA i]
  have hC : (Work.Cohomology.singularChains ℤ (TopCat.of X)).d (m + 1) m
        (simpChain (m + 1) (ContinuousMap.const (stdSimplex ℝ (Fin (m + 2))) y))
      = ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) •
          simpChain m (ContinuousMap.const (stdSimplex ℝ (Fin (m + 1))) y) := by
    have h := d_simpChain m (TopCat.of X)
      (simplexOf (m + 1) (ContinuousMap.const (stdSimplex ℝ (Fin (m + 2))) y))
    rw [toSSetObjEquiv_simplexOf (m + 1) (ContinuousMap.const (stdSimplex ℝ (Fin (m + 2))) y)]
      at h
    refine h.trans ?_
    exact Finset.sum_congr rfl fun i _ => by rw [hB i]
  have hEq : ∀ i : Fin (m + 2),
      s.comp (coface m i) = ContinuousMap.const (stdSimplex ℝ (Fin (m + 1))) y := by
    intro i
    ext z
    rw [ContinuousMap.comp_apply, coface_apply]
    exact hy (stdSimplex.map (Fin.succAbove i) z) ⟨i, coface_apply_self m i z⟩
  have hsame : (∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) • simpChain m (s.comp (coface m i)))
      = (∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) •
          simpChain m (ContinuousMap.const (stdSimplex ℝ (Fin (m + 1))) y)) :=
    Finset.sum_congr rfl fun i _ => by rw [hEq i]
  have hsub : (Work.Cohomology.singularChains ℤ (TopCat.of X)).d (m + 1) m
        (simpChain (m + 1) s
          - simpChain (m + 1) (ContinuousMap.const (stdSimplex ℝ (Fin (m + 2))) y))
      = (Work.Cohomology.singularChains ℤ (TopCat.of X)).d (m + 1) m (simpChain (m + 1) s)
        - (Work.Cohomology.singularChains ℤ (TopCat.of X)).d (m + 1) m
            (simpChain (m + 1) (ContinuousMap.const (stdSimplex ℝ (Fin (m + 2))) y)) :=
    map_sub _ _ _
  rw [hsub, hS, hC, hsame, sub_self]

/-- **The reduced chain of a simplex constant on the boundary is a cycle.** -/
theorem sigmaChain_cycle (n : ℕ) {X : Type} [TopologicalSpace X]
    (s : C(stdSimplex ℝ (Fin (n + 1)), X)) (y : X)
    (hy : ∀ z : stdSimplex ℝ (Fin (n + 1)),
        (∃ j : Fin (n + 1), z j = 0) → s z = y) :
    (Work.Cohomology.singularChains ℤ (TopCat.of X)).d n (n - 1)
      (simpChain n s - simpChain n (ContinuousMap.const (stdSimplex ℝ (Fin (n + 1))) y))
      = 0 := by
  rcases n with _ | m
  · rw [show (0 : ℕ) - 1 = 0 from rfl]
    rw [HomologicalComplex.shape]
    · simp
    · simp [ComplexShape.down]
  · exact sigmaChain_cycle_succ m s y hy

end

end Work.RatHurewicz.Bridge
