/-
  Area E6: the fibrewise closure of a set contained in the closed cube stays in the cube.

  `WilkiesDesign.E.fiberClosure X` is the set of points `z` whose second coordinate lies in the
  topological closure of the fibre `X_{projFirst z}`.  The elementary reason the result holds is

  * `fiberClosure X ⊆ closure X`: a point of the fibrewise closure is approximated by points of
    `X` (the map `y ↦ Fin.append x y` is continuous, so a neighbourhood of `z` pulls back to a
    neighbourhood of `projSnd z`, and the fibre closure provides a point of `X` there), and
  * `closure X ⊆ cubeC (p+q)` because `cubeC` is closed and `X ⊆ cubeC`.

  Both pieces are proved below as separate lemmas, so that other parts of the development can use
  the general inclusion `fiberClosure X ⊆ closure X` and the closedness of the cube.
-/
import Mathlib
import Submission.Work.WilE4.CAD.fiberClosure_eq_sq

set_option autoImplicit false
noncomputable section

namespace Work.WilE6.E6Frontier

open WilkiesDesign.E

/-- The closed cube `[-1,1]^k` is closed. -/
theorem isClosed_cubeC (k : ℕ) : IsClosed (cubeC k) := by
  have h : cubeC k = ⋂ i, {x : Fin k → ℝ | x i ∈ Set.Icc (-1 : ℝ) 1} := by
    ext x
    simp only [cubeC, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_Icc, abs_le]
  rw [h]
  exact isClosed_iInter fun i => isClosed_Icc.preimage (continuous_apply i)

/-- The fibrewise closure of `X` is contained in the ordinary closure of `X`.

Indeed, if `y ∈ closure (fiber X x)` then for every neighbourhood `U` of `z = Fin.append x y` the
preimage of `U` under the continuous map `y' ↦ Fin.append x y'` is a neighbourhood of `y`, hence
meets `fiber X x`; the image of a point of that intersection is a point of `U ∩ X`. -/
theorem fiberClosure_subset_closure {p q : ℕ} (X : Set (Fin (p + q) → ℝ)) :
    fiberClosure X ⊆ closure X := by
  intro z hz
  have hz' : projSnd p q z ∈ closure (fiber X (projFirst p q z)) := hz
  rw [mem_closure_iff_nhds] at hz'
  rw [mem_closure_iff_nhds]
  intro U hU
  have hcont : Continuous fun y : Fin q → ℝ => Fin.append (projFirst p q z) y := by fun_prop
  have happ : Fin.append (projFirst p q z) (projSnd p q z) = z := Fin.append_castAdd_natAdd
  have hU' : U ∈ nhds (Fin.append (projFirst p q z) (projSnd p q z)) := by rw [happ]; exact hU
  have hpre : (fun y : Fin q → ℝ => Fin.append (projFirst p q z) y) ⁻¹' U
      ∈ nhds (projSnd p q z) := hcont.continuousAt.preimage_mem_nhds hU'
  obtain ⟨y', hy'pre, hy'fib⟩ := hz' _ hpre
  exact ⟨Fin.append (projFirst p q z) y', hy'pre, hy'fib⟩

/-- A set contained in the closed cube has its fibrewise closure inside the cube. -/
theorem fiberClosure_subset_cubeC {p q : ℕ} {X : Set (Fin (p + q) → ℝ)}
    (hX : X ⊆ WilkiesDesign.E.cubeC (p + q)) :
    WilkiesDesign.E.fiberClosure X ⊆ WilkiesDesign.E.cubeC (p + q) :=
  (fiberClosure_subset_closure X).trans
    (closure_minimal hX (isClosed_cubeC (p + q)))

end Work.WilE6.E6Frontier
