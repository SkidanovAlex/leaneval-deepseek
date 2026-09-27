import Mathlib
import Submission.Work.Mostow.gapA.screwDefs
import Submission.Work.Mostow.gapA.geodFacts

/-!
# `screwGeod`: the geometry of the normal vector to the axis `geodSet a b`

For two distinct boundary points `a ≠ b` of `Sph 3` and any `u : E 3` we compute, in the
hyperboloid (Minkowski) model, the normal component `prjN a b (hlift u)` of the lift of `u` with
respect to the plane spanned by the two null vectors `nullA a = (a,1)`, `nullB b = (b,1)`:

* `mink (hlift u) (nullA a) = - lev a u`;
* `prjN a b (hlift u) = 0` exactly on the geodesic `geodSet a b`;
* `mink (prjN a b (hlift u)) (prjN a b (hlift u)) = 2 (lev a u)(lev b u)/mmB a b - 1`,
  which is the squared hyperbolic sine of the distance to the geodesic;
* `cosh (distGeod a b u) = sqrt (1 + mink (prjN …) (prjN …))` and
  `sinh (distGeod a b u)^2 = mink (prjN …) (prjN …)`.

The work is done by `gapA.geodFacts`: the normal vector is the vector `gcN a b u` of that file,
because the two scalar coefficients agree (`smB a b = inner a b - 1 = -(2 gcL a b)`), and
`geodFacts` already computes the Minkowski square of `gcN`, characterises `gcN = 0` and the
hyperbolic functions of `distGeod`.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- The normal component `prjN a b (hlift u)` of the lift of `u` equals the vector `gcN a b u`:
both are `hlift u` minus the multiples of the null vectors `(a,1)`, `(b,1)` making it orthogonal
to them.  The two scalar coefficients are `-lev b u/(inner a b - 1)` and `lev b u/(2 gcL a b)`,
which agree because `inner a b - 1 = -(2 gcL a b)`. -/
lemma prjN_hlift_eq_gcN (a b u : E 3) : prjN a b (hlift u) = gcN a b u := by
  have hA : mink (hlift u) (nvec a) = -lev a u := by
    rw [Work.Mostow.minkSeg_comm]
    exact Work.Mostow.mink_nvec_hlift 3 a u
  have hB : mink (hlift u) (nvec b) = -lev b u := by
    rw [Work.Mostow.minkSeg_comm]
    exact Work.Mostow.mink_nvec_hlift 3 b u
  simp only [prjN, gcN, gcA, gcB, gcL, smB, nullA, nullB]
  rw [hA, hB, mink_nvec_nvec']
  have h1 : (-lev b u) / (inner ℝ a b - 1) = lev b u / (2 * ((1 - inner ℝ a b) / 2)) := by
    rw [show inner ℝ a b - 1 = -(1 - inner ℝ a b) from by ring,
      show 2 * ((1 - inner ℝ a b) / 2) = (1 - inner ℝ a b) from by ring,
      neg_div_neg_eq]
  have h2 : (-lev a u) / (inner ℝ a b - 1) = lev a u / (2 * ((1 - inner ℝ a b) / 2)) := by
    rw [show inner ℝ a b - 1 = -(1 - inner ℝ a b) from by ring,
      show 2 * ((1 - inner ℝ a b) / 2) = (1 - inner ℝ a b) from by ring,
      neg_div_neg_eq]
  rw [h1, h2]

theorem screwGeod {a b : Submission.Mostow.E 3} (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b) (u : Submission.Mostow.E 3) :
    (Work.Mostow.mink (Submission.Mostow.hlift u) (Work.Mostow.gapA.nullA a) = -Work.Mostow.lev a u) ∧
    (Work.Mostow.gapA.prjN a b (Submission.Mostow.hlift u) = 0 ↔ u ∈ Work.Mostow.geodSet a b) ∧
    (Work.Mostow.mink (Work.Mostow.gapA.prjN a b (Submission.Mostow.hlift u)) (Work.Mostow.gapA.prjN a b (Submission.Mostow.hlift u)) = 2 * (Work.Mostow.lev a u * Work.Mostow.lev b u) / Work.Mostow.gapA.mmB a b - 1) ∧
    (Real.cosh (Work.Mostow.distGeod a b u) = Real.sqrt (1 + Work.Mostow.mink (Work.Mostow.gapA.prjN a b (Submission.Mostow.hlift u)) (Work.Mostow.gapA.prjN a b (Submission.Mostow.hlift u)))) ∧
    (Real.sinh (Work.Mostow.distGeod a b u) ^ 2 = Work.Mostow.mink (Work.Mostow.gapA.prjN a b (Submission.Mostow.hlift u)) (Work.Mostow.gapA.prjN a b (Submission.Mostow.hlift u))) := by
  have hN : prjN a b (hlift u) = gcN a b u := prjN_hlift_eq_gcN a b u
  have hself : mink (gcN a b u) (gcN a b u) = lev a u * lev b u / gcL a b - 1 :=
    gcN_self_mink a b ha hb hab u
  have hlevpos : 0 ≤ lev a u * lev b u / gcL a b :=
    div_nonneg (mul_nonneg (le_of_lt (lev_pos a ha u)) (le_of_lt (lev_pos b hb u)))
      (le_of_lt (gcL_pos a b ha hb hab))
  have hcosh : Real.cosh (distGeod a b u) = Real.sqrt (lev a u * lev b u / gcL a b) := by
    rw [distGeod_eq a b ha hb u]
    exact Real.cosh_arcosh (sqrt_levdiv_ge_one a b ha hb hab u)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Work.Mostow.minkSeg_comm]
    exact Work.Mostow.mink_nvec_hlift 3 a u
  · rw [hN]
    exact gcN_eq_zero_iff a b ha hb hab u
  · rw [hN, hself]
    have hmm : mmB a b = 2 * gcL a b := by rw [mmB, gcL]; ring
    rw [hmm]
    have hratio : 2 * (lev a u * lev b u) / (2 * gcL a b) = lev a u * lev b u / gcL a b := by
      rw [show 2 * (lev a u * lev b u) = (lev a u * lev b u) * 2 from by ring,
        show 2 * gcL a b = gcL a b * 2 from by ring]
      exact mul_div_mul_right _ _ (by norm_num)
    rw [hratio]
  · rw [hN, hself, hcosh]
    congr 1
    ring
  · rw [hN, hself, Real.sinh_sq, hcosh, Real.sq_sqrt hlevpos]

end

end Work.Mostow.gapA
