import Mathlib
import Submission.Work.PTGeometric.RieszProj.SmoothPhi
import Submission.Work.PTGeometric.RieszProj.CountRank

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.PTGeometric

open scoped ContDiff

/-- **G1 of the PTGEOMETRIC blueprint: the smooth retraction onto the Grassmannian of projection
matrices.**

`Gr_k(ℝⁿ)` is the set of orthogonal projections of rank `k`, i.e. the continuous linear maps
`P : ℝⁿ →L[ℝ] ℝⁿ` with `P† = P` (adjoint/self-adjointness), `P * P = P` and `trace P = k`.  There is
an open neighbourhood `U` of `Gr_k(ℝⁿ)` and a `C^∞` map `r` on `U` which fixes `Gr_k(ℝⁿ)` pointwise
and takes all of `U` into `Gr_k(ℝⁿ)`, and the `1/4`-neighbourhood of `Gr_k(ℝⁿ)` in the operator norm
is contained in `U`.  This is the analytic input of the smoothing step G2 of the blueprint.

Two routes (both acceptable; only the existence is asserted, not the formula):

* the *Riesz/spectral* route: for `A` with `‖A - P‖ < 1/4` and `P` an orthogonal projection, the
  spectrum of `A` lies in `D(0,1/4) ∪ D(1,1/4)`, at distance `≥ 1/4` from the contour `|z - 1| = 1/2`,
  so the Riesz projection `Q A = (2πi)⁻¹ ∮_{|z-1|=1/2} (z - A)⁻¹ dz` is defined and smooth in `A`;
  then take `r A` = the orthogonal projection onto `range (Q A)`.  (Note: `Q A` itself is *not*
  self-adjoint for non-normal `A` — e.g. `A = [[1,t],[0,0]]` — so the orthogonal projection onto its
  range must be taken, and its smoothness near the orthogonal projections needs an argument.)
* the *tubular/nearest-point* route: `Gr_k(ℝⁿ)` is a compact smooth submanifold of the finite
  dimensional space of operators with reach `≥ 1/4` (the bound `dist(λ, σ(P)) ≤ ‖A - P‖` for the
  *normal* operator `P`, plus the spectral-gap/rank-counting argument, gives the uniqueness of the
  nearest point in the `1/4`-ball); the nearest-point map of a submanifold of reach `> 0` is smooth on
  its `1/4`-neighbourhood and fixes the submanifold.

Only the second assertion (the `1/4`-ball is inside `U`) needs the spectral bound; if a route
produces a retraction only on a smaller explicit neighbourhood, say so and I will weaken the radius. -/
theorem grassmannianRetraction (n k : ℕ) (hk : k ≤ n) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
      (r : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))),
      IsOpen U ∧
      (∀ P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        ContinuousLinearMap.adjoint P = P → P * P = P →
        LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) P = (k : ℝ) → P ∈ U) ∧
      ContDiffOn ℝ ∞ r U ∧
      (∀ P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        ContinuousLinearMap.adjoint P = P → P * P = P →
        LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) P = (k : ℝ) → r P = P) ∧
      (∀ A ∈ U, ContinuousLinearMap.adjoint (r A) = r A ∧ r A * r A = r A ∧
        LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (r A) = (k : ℝ)) ∧
      (∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        (∃ P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
          ContinuousLinearMap.adjoint P = P ∧ P * P = P ∧
          LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) P = (k : ℝ) ∧ ‖A - P‖ < 1/4) →
        A ∈ U) := by
  refine ⟨good n k, Rmap, isOpen_good n k, ?_, ?_, ?_, ?_, ?_⟩
  · -- every orthogonal projection of trace `k` lies in `U`
    rintro P h1 h2 h3
    exact Gr_subset_good ⟨h1, h2, h3⟩
  · -- the retraction is smooth on `U`
    exact contDiffOn_Rmap n k
  · -- the retraction fixes `Gr n k` pointwise
    rintro P h1 h2 h3
    change Phi (symm P) = P
    rw [symm_eq_self_of_mem_Gr (⟨h1, h2, h3⟩ : P ∈ Gr n k)]
    exact Phi_eq_self_of_mem_Gr ⟨h1, h2, h3⟩ (finrank_amb n)
  · -- the retraction maps `U` into `Gr n k`
    rintro A hA
    rw [mem_good_iff] at hA
    obtain ⟨P, hP, hAP⟩ := hA
    exact Phi_mem_Gr_of_topCard (symm_isSymmetric A) (finrank_amb n) hP hAP
      (topCard_eq (symm_isSymmetric A) (finrank_amb n) hP hAP)
  · -- the `1/4`-neighbourhood of `Gr n k` is inside `U`
    rintro A ⟨P, h1, h2, h3, hAP⟩
    exact good_of_dist ⟨h1, h2, h3⟩ hAP

end Work.PTGeometric
