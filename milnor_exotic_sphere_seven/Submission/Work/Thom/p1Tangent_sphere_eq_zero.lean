import Mathlib
import Submission.Work.Thom.manifoldP1
import Submission.Work.Thom.trivialChern
import Submission.Work.Thom.chernClass_eq_zero_of_lt
import Submission.Work.Thom.p1Tangent_eq_zero_of_finrank_le_one

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

/-- **`p₁(TM)` of the sphere `Sⁿ` vanishes for `n ≠ 4`.**

The first Pontryagin class is the *defined* class `p₁(TM) = - c₂(TM ⊗_ℝ ℂ)`, a class in `H⁴(M;ℤ)`.
For `M = Sⁿ` the cohomology group `H⁴(Sⁿ;ℤ)` is trivial as soon as `n ≠ 4` — the vanishing
`Work.Thom.subsingleton_cohomology_sphere` of `Work.Cohomology.sphereCohomologyZero` for `n ≥ 1`
and the total disconnectedness of `S⁰` for `n = 0` — and any class in the trivial module is `0`, by
`Work.Thom.chernClass_eq_zero_of_subsingleton`.  Hence `p₁(TSⁿ) = 0` for every `n ≠ 4`.

(The statement excludes `n = 4` only because `H⁴(S⁴;ℤ) ≅ ℤ` is not a trivial module; the
mathematical vanishing `p₁(TSⁿ) = 0` in fact holds for all `n`, by stability `TSⁿ ⊕ ε¹ ≅ ε^{n+1}`,
which is a separate — and not needed here — computation.) -/
theorem p1Tangent_sphere_eq_zero (n : ℕ) (hn : n ≠ 4) :
    Work.Thom.p1Tangent' (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) = 0 := by
  rcases n with _ | n
  · -- `n = 0`: the sphere `S⁰` is finite, hence totally disconnected, so `H⁴(S⁰;ℤ) = 0`.
    rw [p1Tangent'_def]
    haveI : Finite ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
      Work.Cohomology.finite_metricSphere_fin_one.to_subtype
    haveI : TotallyDisconnectedSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
      inferInstance
    have h : Subsingleton (Coh ℤ (2 * 2) ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)) :=
      ModuleCat.subsingleton_of_isZero (Work.Cohomology.totallyDisconnected ℤ _ 3)
    rw [chernClass_eq_zero_of_subsingleton _ h, neg_zero]
  · -- `n = m + 1 ≥ 1`: `H⁴(Sⁿ;ℤ) = 0` off the degrees `0` and `n`, and `4 ≠ n`.
    rw [p1Tangent'_def]
    have h : Subsingleton (Coh ℤ (2 * 2)
        ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (Nat.succ n + 1))) 1)) :=
      subsingleton_cohomology_sphere (n := Nat.succ n) (k := 2 * 2)
        (by omega) (by norm_num) (by omega)
    rw [chernClass_eq_zero_of_subsingleton _ h, neg_zero]

end Work.Thom
