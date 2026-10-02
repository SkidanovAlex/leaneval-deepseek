import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Whitney.tcmModelMul_of_point

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Auxiliary facts for the `q = 1` case of the point model formula

Toolkit shared by the statement and proof of `Work.Whitney.tcmModelMul_point_succ_one`.

* `Work.Whitney.tcmA_union_tcmC` : `A ∪ C = {x | x.2 ≠ 0}` for `tcmX B p q`.
* `Work.Whitney.tcmF_inv_mem` : the inverse `Work.Whitney.Fib.tcmF_inv` of the coordinate
  identification maps the sphere bundle of rank `p+1` into `A ∪ C`; this is the pair condition
  needed to pull a class of `H^*(tcmX, A ∪ C)` back to `H^*(Y × ℝ^{p+1}, Sph)`.
-/

namespace Work.Whitney

open Work.Thom

noncomputable section

/-- `A ∪ C` is the complement of the zero section, in the coordinates of `tcmX`. -/
theorem tcmA_union_tcmC (B : Type) [TopologicalSpace B] (p q : ℕ) :
    tcmA B p q ∪ tcmC B p q = {x : tcmX B p q | x.2 ≠ 0} := by
  ext x
  simp only [Set.mem_union, tcmA, tcmC, Set.mem_ofPred_eq]
  constructor
  · rintro (h | h)
    · intro h0; exact h (congrArg Prod.fst h0)
    · intro h0; exact h (congrArg Prod.snd h0)
  · intro h
    by_cases h1 : x.2.1 = 0
    · right
      intro h2
      exact h (Prod.ext h1 h2)
    · exact Or.inl h1

/-- **The pair condition of the inverse identification**: every point of the sphere bundle of rank
`p+1` lies in `A ∪ C` after applying `Work.Whitney.Fib.tcmF_inv`.  (The fibre coordinates of `Sph`
are nonzero and `tcmF_inv` is the coordinate reassociation, which preserves nonvanishing.) -/
theorem tcmF_inv_mem (Y : Type) [TopologicalSpace Y] (p : ℕ) :
    ∀ x ∈ Sph Y (p + 1), Fib.tcmF_inv Y p 1 x ∈ tcmA Y p 1 ∪ tcmC Y p 1 := by
  intro x hx
  rw [tcmA_union_tcmC]
  simp only [Set.mem_ofPred_eq, Fib.tcmF_inv_apply]
  intro h0
  have h1 : x.2 = 0 := by
    have h2 := congrArg (tcmSumLin p 1) h0
    simpa only [ContinuousLinearEquiv.apply_symm_apply, map_zero] using h2
  have h3 : ‖x.2‖ = 1 := hx
  rw [h1, norm_zero] at h3
  exact one_ne_zero h3.symm

/-- **The pair condition of the inverse identification on the punctured part**: `Punct` is
carried into `A ∪ C` by `Fib.tcmF_inv`. -/
theorem tcmF_inv_mem_punct (Y : Type) [TopologicalSpace Y] (p : ℕ) :
    ∀ x ∈ Punct Y (p + 1), Fib.tcmF_inv Y p 1 x ∈ tcmA Y p 1 ∪ tcmC Y p 1 := by
  intro x hx
  rw [tcmA_union_tcmC]
  simp only [Set.mem_ofPred_eq, Fib.tcmF_inv_apply]
  intro h0
  exact hx (by
    have h2 := congrArg (tcmSumLin p 1) h0
    simpa only [ContinuousLinearEquiv.apply_symm_apply, map_zero] using h2)

/-- The preimage form of the pair condition: `Sph ⊆ tcmF_inv ⁻¹' (A ∪ C)`. -/
theorem tcmF_inv_preimage (Y : Type) [TopologicalSpace Y] (p : ℕ) :
    Sph Y (p + 1) ⊆ (Fib.tcmF_inv Y p 1) ⁻¹' (tcmA Y p 1 ∪ tcmC Y p 1) :=
  tcmF_inv_mem Y p

end

end Work.Whitney
