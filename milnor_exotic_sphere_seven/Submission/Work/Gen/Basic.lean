import Mathlib
import Submission.Work.Projective.CP4Concrete
import Submission.Work.Thom.chernClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# AREA GEN — the tautological line bundle on `ℂPⁿ` as gluing data

This module starts the *Gen* area (`Submission/Work/Gen/`): the computation of the Pontryagin
numbers of the **defined** tangent-bundle classes (`Work.Thom.p1Tangent'`, `p2Tangent'`) of the
projective spaces, which is what `Work.Drive.Generators8` needs.

The classical route (as recorded in the area's guidance) is

* the Euler sequence `TℂPⁿ ⊕ ℂ ≅ (n+1)·O(1)` in the gluing model,
* `c₁(O(1)) = ±` the generator `x ∈ H²(ℂPⁿ)`, `H^*(ℂPⁿ) = ℤ[x]/(xⁿ⁺¹)`, `⟨x⁴,[ℂP⁴]⟩ = ±1`,
* the Whitney formula `c(E ⊕ F) = c(E)c(F)` (the sibling area `Submission/Work/Whitney/`).

Here we build the *bundle-theoretic* half: the tautological line bundles `O(-1) ⊂ O^{n+1}` and its
dual `O(1)`, as gluing data over the standard `(n+1)`-chart cover of `ℂPⁿ`, together with the
explicit transition functions (the ratios of homogeneous coordinates).
-/

open Work.Projective

namespace Work.Gen

noncomputable section

/-- **The ratio `z_j/z_i` of homogeneous coordinates**, read in the chart at `i`: it is `1` when
`j = i` and the `j`-th coordinate of the chart `i` otherwise (that coordinate being `z_j/z_i`).
For `x ∈ chartSet i` it is the transition function of the tautological line bundle from the chart
`i` to the chart `j`. -/
def homCoord (n : ℕ) (i j : Fin (n + 1)) (x : CP n) : ℂ :=
  if h : j = i then 1 else chartFun i x (removeAbove i j h)

variable {n : ℕ}

@[simp] theorem homCoord_self (i : Fin (n + 1)) (x : CP n) : homCoord n i i x = 1 := by
  simp [homCoord]

theorem homCoord_of_ne {i j : Fin (n + 1)} (h : j ≠ i) (x : CP n) :
    homCoord n i j x = chartFun i x (removeAbove i j h) := by
  simp only [homCoord, dif_neg h]

/-- `homCoord n i j` is continuous on `chartSet i`. -/
theorem continuousOn_homCoord (i j : Fin (n + 1)) :
    ContinuousOn (homCoord n i j) (chartSet i) := by
  by_cases h : j = i
  · rw [show homCoord n i j = fun _ : CP n => (1 : ℂ) from
      funext fun x => by rw [h]; simp]
    exact continuousOn_const
  · have hfun : homCoord n i j = fun x => chartFun i x (removeAbove i j h) := by
      funext x
      exact homCoord_of_ne h x
    rw [hfun]
    exact (continuous_apply (removeAbove i j h)).comp_continuousOn (continuousOn_chartFun i)

/-- **The cocycle identity of the homogeneous coordinates**: on `chartSet i ∩ chartSet j`,
`z_k/z_i = (z_k/z_j)·(z_j/z_i)`. -/
theorem homCoord_mul (i j k : Fin (n + 1)) {x : CP n}
    (hi : x ∈ chartSet i) (hj : x ∈ chartSet j) (hk : x ∈ chartSet k) :
    homCoord n i k x = homCoord n j k x * homCoord n i j x := by
  obtain ⟨w, rfl⟩ := hi
  have hj' : cpMk n ⟨Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w,
      insertNth_one_ne_zero i w⟩ ∈ chartSet j := by
    rw [← chartInv_apply i w]
    exact hj
  have hj0 : (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) j ≠ 0 :=
    (mem_chartSet_iff j _).mp hj'
  have hA : (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) i = 1 :=
    Fin.insertNth_apply_same (α := fun _ => ℂ) i 1 w
  have key : ∀ {m l : Fin (n + 1)}, l ≠ m → homCoord n m l (chartInv i w) =
      (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) l /
      (Fin.insertNth (α := fun _ => ℂ) i (1 : ℂ) w) m := by
    intro m l hl
    rw [homCoord_of_ne hl, chartInv_apply, chartFun_cpMk, chartFunAux, succAbove_removeAbove]
  by_cases hji : j = i
  · rw [hji, homCoord_self, mul_one]
  · by_cases hki : k = i
    · rw [hki, homCoord_self, key (show i ≠ j from Ne.symm hji), key hji, hA, div_one, one_div]
      exact (inv_mul_cancel₀ hj0).symm
    · by_cases hkj : k = j
      · rw [hkj, homCoord_self, one_mul]
      · rw [key hki, key hkj, key hji, hA]
        field_simp

/-! ## The tautological line bundle and its dual, as gluing data -/

section Bundles

open Work.TangentClasses

/-- **The tautological sub-line bundle `O(-1) ⊂ O^{n+1}`** of `ℂPⁿ`, as gluing data over the
standard `(n+1)`-chart cover: over the chart `i` the fibre is trivialised by the normalised
representative (the section with `i`-th homogeneous coordinate `1`), so that the transition
function from the chart `i` to the chart `j` is multiplication by `z_j/z_i`. -/
def tautLine (n : ℕ) :
    VectorBundleCore ℂ (CP n) (EuclideanSpace ℂ (Fin 1)) (Fin (n + 1)) where
  baseSet i := chartSet i
  isOpen_baseSet i := isOpen_chartSet i
  indexAt x := Classical.choose (exists_mem_chartSet x)
  mem_baseSet_at x := Classical.choose_spec (exists_mem_chartSet x)
  coordChange i j x := homCoord n i j x •
    ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))
  coordChange_self i x _ v := by simp
  continuousOn_coordChange i j := by
    refine ((continuousOn_homCoord (n := n) i j).smul
      (continuousOn_const : ContinuousOn
        (fun _ : CP n => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) _)).mono ?_
    intro x hx
    exact hx.1
  coordChange_comp i j k x hx v := by
    simp only [ContinuousLinearMap.smul_apply, map_smul, smul_smul]
    rw [homCoord_mul i j k hx.1.1 hx.1.2 hx.2, mul_comm]
    simp

/-- **The dual `O(1)` of the tautological line bundle** of `ℂPⁿ`, as gluing data over the standard
`(n+1)`-chart cover: the transition function from the chart `i` to the chart `j` is multiplication
by `z_i/z_j`, i.e. `homCoord n j i`. -/
def tautDual (n : ℕ) :
    VectorBundleCore ℂ (CP n) (EuclideanSpace ℂ (Fin 1)) (Fin (n + 1)) where
  baseSet i := chartSet i
  isOpen_baseSet i := isOpen_chartSet i
  indexAt x := Classical.choose (exists_mem_chartSet x)
  mem_baseSet_at x := Classical.choose_spec (exists_mem_chartSet x)
  coordChange i j x := homCoord n j i x •
    ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))
  coordChange_self i x _ v := by simp
  continuousOn_coordChange i j := by
    refine ((continuousOn_homCoord (n := n) j i).smul
      (continuousOn_const : ContinuousOn
        (fun _ : CP n => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) _)).mono ?_
    intro x hx
    exact hx.2
  coordChange_comp i j k x hx v := by
    simp only [ContinuousLinearMap.smul_apply, map_smul, smul_smul]
    rw [homCoord_mul k j i hx.2 hx.1.2 hx.1.1, mul_comm]
    simp

@[simp] theorem tautLine_baseSet (n : ℕ) (i : Fin (n + 1)) :
    (tautLine n).baseSet i = chartSet i := rfl

@[simp] theorem tautLine_indexAt (n : ℕ) (x : CP n) :
    (tautLine n).indexAt x = Classical.choose (exists_mem_chartSet x) := rfl

@[simp] theorem tautLine_coordChange (n : ℕ) (i j : Fin (n + 1)) (x : CP n) :
    (tautLine n).coordChange i j x = homCoord n i j x •
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := rfl

@[simp] theorem tautDual_baseSet (n : ℕ) (i : Fin (n + 1)) :
    (tautDual n).baseSet i = chartSet i := rfl

@[simp] theorem tautDual_indexAt (n : ℕ) (x : CP n) :
    (tautDual n).indexAt x = Classical.choose (exists_mem_chartSet x) := rfl

@[simp] theorem tautDual_coordChange (n : ℕ) (i j : Fin (n + 1)) (x : CP n) :
    (tautDual n).coordChange i j x = homCoord n j i x •
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := rfl

end Bundles

end

end Work.Gen
