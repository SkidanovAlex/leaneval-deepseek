import Submission.Work.TorusCover.Basic
import Submission.Work.TorusCover.hasWinding_unique
import Submission.Work.TorusCover.exists_torusParam_torusMap
import Submission.Work.TorusCover.Lifting

/-!
# The standard torus: winding vector of the standard `(p,q)` curve

For the standard torus of revolution `psi = Work.Core.torusMap`, the standard `(p,q)` curve
`standardTorusCurve p q : t ↦ torusMap (p t) (q t)` has the obvious lift `t ↦ (p t, q t)`,
whose period displacement is `(2πp, 2πq)`; hence its winding vector is `(p, q)`.  Since the
standard parametrisation satisfies the hypotheses of `TorusParam` (with `c = 1`), the winding
vector is unique (`Work.TorusCover.hasWinding_unique`), so this identifies *the* winding vector
of the standard curve.

Main results:

* `Work.TorusCover.standardTorusCurveLift`, `isLift_standardTorusCurve`,
  `isPeriodicLift_standardTorusCurve`, `hasWinding_standardTorusCurve`;
* `Work.TorusCover.hasWinding_standardTorusCurve_iff`: the standard `(p,q)` curve has winding
  vector exactly `(p, q)`.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.TorusCover

noncomputable section

/-- The explicit lift `t ↦ (p t, q t)` of the standard `(p,q)` curve. -/
def standardTorusCurveLift (p q : ℕ) : ℝ → ℝ × ℝ := fun t => ((p : ℝ) * t, (q : ℝ) * t)

@[simp] lemma standardTorusCurveLift_apply (p q : ℕ) (t : ℝ) :
    standardTorusCurveLift p q t = ((p : ℝ) * t, (q : ℝ) * t) := rfl

lemma continuous_standardTorusCurveLift (p q : ℕ) :
    Continuous (standardTorusCurveLift p q) := by
  unfold standardTorusCurveLift
  fun_prop

/-- The explicit lift is indeed a lift of the standard `(p,q)` curve. -/
theorem isLift_standardTorusCurve (p q : ℕ) :
    IsLift Work.Core.torusMap (standardTorusCurve p q) (standardTorusCurveLift p q) := by
  refine ⟨continuous_standardTorusCurveLift p q, fun t => ?_⟩
  simp only [standardTorusCurveLift_apply]
  exact (Work.Core.standardTorusCurve_eq_torusMap p q t).symm

/-- The explicit lift advances by `(2πp, 2πq)` over one period. -/
theorem isPeriodicLift_standardTorusCurve (p q : ℕ) :
    IsPeriodicLift Work.Core.torusMap (standardTorusCurve p q) ((p : ℤ), (q : ℤ))
      (standardTorusCurveLift p q) := by
  refine ⟨isLift_standardTorusCurve p q, fun t => ?_⟩
  ext <;> simp only [standardTorusCurveLift_apply, periodShift, Prod.fst_add, Prod.snd_add]
  · push_cast; ring
  · push_cast; ring

/-- The standard `(p,q)` curve has winding vector `(p, q)` (with respect to the standard
parametrisation `Work.Core.torusMap`). -/
theorem hasWinding_standardTorusCurve (p q : ℕ) :
    HasWinding Work.Core.torusMap (standardTorusCurve p q) ((p : ℤ), (q : ℤ)) :=
  ⟨standardTorusCurveLift p q, isPeriodicLift_standardTorusCurve p q⟩

/-- **The winding vector of the standard `(p,q)` curve is exactly `(p, q)`**: any lift-based
witness of the winding vector of `standardTorusCurve p q` equals `(p, q)`.  (Uniqueness of the
winding vector is applied to the standard torus, which is a `TorusParam` with `c = 1`.) -/
theorem hasWinding_standardTorusCurve_iff (p q : ℕ) {v : ℤ × ℤ} :
    HasWinding Work.Core.torusMap (standardTorusCurve p q) v ↔ v = ((p : ℤ), (q : ℤ)) := by
  obtain ⟨P, hpsi, -⟩ := exists_torusParam_torusMap
  constructor
  · intro hv
    have h1 : HasWinding P.psi (standardTorusCurve p q) ((p : ℤ), (q : ℤ)) := by
      rw [hpsi]; exact hasWinding_standardTorusCurve p q
    have h2 : HasWinding P.psi (standardTorusCurve p q) v := by rw [hpsi]; exact hv
    rw [hasWinding_unique P h2 h1]
  · rintro rfl; exact hasWinding_standardTorusCurve p q

/-! ### Regularity and essentiality of the standard curve -/

/-- The standard `(p,q)` curve is continuous. -/
lemma continuous_standardTorusCurve (p q : ℕ) : Continuous (standardTorusCurve p q) := by
  refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp ?_
  rw [continuous_pi_iff]
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- The standard `(p,q)` curve is `2π`-periodic. -/
lemma standardTorusCurve_periodic (p q : ℕ) (t : ℝ) :
    standardTorusCurve p q (t + 2 * Real.pi) = standardTorusCurve p q t := by
  rw [Work.Core.standardTorusCurve_eq_torusMap, Work.Core.standardTorusCurve_eq_torusMap]
  refine (Work.Core.torusMap_eq_iff _ _ _ _).mpr ⟨⟨(p : ℤ), ?_⟩, ⟨(q : ℤ), ?_⟩⟩ <;>
    push_cast <;> ring

/-- The standard `(p,q)` curve is essential as soon as `(p, q) ≠ (0, 0)`. -/
theorem isEssential_standardTorusCurve (p q : ℕ) (h : ¬ (p = 0 ∧ q = 0)) :
    IsEssential Work.Core.torusMap (standardTorusCurve p q) := by
  refine ⟨((p : ℤ), (q : ℤ)), ?_, hasWinding_standardTorusCurve p q⟩
  rintro hp
  have h1 : (p : ℤ) = 0 := by simpa using congrArg Prod.fst hp
  have h2 : (q : ℤ) = 0 := by simpa using congrArg Prod.snd hp
  exact h ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- **The winding vector of the standard `(p,q)` curve is `(p, q)`**, in the `windingVector`
form. -/
theorem windingVector_standardTorusCurve (p q : ℕ) :
    windingVector torusParamModel (standardTorusCurve p q)
        (continuous_standardTorusCurve p q) (standardTorusCurve_periodic p q)
        (fun t => ⟨((p : ℝ) * t, (q : ℝ) * t), by
          simp [psiMap, Work.Core.standardTorusCurve_eq_torusMap, torusParamModel]⟩) =
      ((p : ℤ), (q : ℤ)) := by
  refine (windingVector_eq torusParamModel (continuous_standardTorusCurve p q)
    (standardTorusCurve_periodic p q) _ ?_).symm
  rw [show torusParamModel.psi = Work.Core.torusMap from rfl]
  exact hasWinding_standardTorusCurve p q

end

end Work.TorusCover
