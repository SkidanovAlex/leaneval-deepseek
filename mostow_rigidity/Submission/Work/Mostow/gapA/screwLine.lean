import Mathlib
import Submission.Work.Mostow.gapA.screwDefs
import Submission.Work.Mostow.pairStabDefs
import Submission.Work.Mostow.gapA.mem_geodSet_iff_span

/-!
# The geodesic `axisV a b` through two distinct boundary points

For distinct `a b ∈ Sph 3` (so that `m = mmB a b = 1 - ⟪a,b⟫ > 0`), the curve

`axisV a b s = κ (e^s · nvec a + e^{-s} · nvec b)`, `κ = kkB a b = (2m)^{-1/2}`,

is a unit-speed parametrisation of the hyperboloid geodesic with endpoints `a`, `b`:

* it lies on the hyperboloid (`⟨axisV s, axisV s⟩ = -1`) with positive time coordinate;
* the Minkowski pairing of two parameters is `-cosh (s - t)`;
* `axisPt a b s` is its chart point (`hlift (axisPt a b s) = axisV a b s`);
* consequently `hdist (axisPt a b s) (axisPt a b t) = |s - t|`.

All the content is the bilinear computation `minkAxisCompute` together with
`eq_hlift_of_upper` (a point of the upper sheet is the lift of its spatial part).
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

set_option maxHeartbeats 800000 in
theorem screwLine {a b : Submission.Mostow.E 3} (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b) :
    (Work.Mostow.gapA.kkB a b ^ 2 * (2 * Work.Mostow.gapA.mmB a b) = 1) ∧ (0 < Work.Mostow.gapA.kkB a b) ∧
    (∀ s : ℝ, Work.Mostow.mink (Work.Mostow.gapA.axisV a b s) (Work.Mostow.gapA.axisV a b s) = -1) ∧
    (∀ s : ℝ, 0 < Work.Mostow.gapA.axisV a b s (Sum.inr 0)) ∧
    (∀ s t : ℝ, Work.Mostow.mink (Work.Mostow.gapA.axisV a b s) (Work.Mostow.gapA.axisV a b t) = -Real.cosh (s - t)) ∧
    (∀ s : ℝ, Submission.Mostow.hlift (Work.Mostow.gapA.axisPt a b s) = Work.Mostow.gapA.axisV a b s) ∧
    (∀ s t : ℝ, Submission.Mostow.hdist (Work.Mostow.gapA.axisPt a b s) (Work.Mostow.gapA.axisPt a b t) = |s - t|) := by
  have hmm : 0 < mmB a b := by
    rw [mmB]
    have h := inner_lt_one_of_ne_unit ((mem_Sph_iff a).mp ha) ((mem_Sph_iff b).mp hb) hab
    linarith
  have hkk : 0 < kkB a b := by
    rw [kkB]
    exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have hkk2 : kkB a b ^ 2 * (2 * mmB a b) = 1 := by
    rw [kkB, inv_pow, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2 * mmB a b)]
    exact inv_mul_cancel₀ (by linarith : (2 * mmB a b) ≠ 0)
  have hA0 : mink (nullA a) (nullA a) = 0 := by
    rw [mink_eq_mform]; exact mform_nvec_self (n := 3) ha
  have hB0 : mink (nullB b) (nullB b) = 0 := by
    rw [mink_eq_mform]; exact mform_nvec_self (n := 3) hb
  have hAB : mink (nullA a) (nullB b) = - mmB a b := by
    rw [mink_eq_mform]
    change mform (Work.Mostow.nvec a) (Work.Mostow.nvec b) = -mmB a b
    rw [mform_nvec_nvec, mmB]; ring
  have haux := minkAxisCompute 3 (nullA a) (nullB b) hA0 hB0 (kkB a b)
  -- The Minkowski pairing of two parameters of the axis.
  have hcross : ∀ s t : ℝ, mink (axisV a b s) (axisV a b t) = -Real.cosh (s - t) := by
    intro s t
    have h := haux s t
    rw [hAB] at h
    change mink (kkB a b • (Real.exp s • nullA a + Real.exp (-s) • nullB b))
      (kkB a b • (Real.exp t • nullA a + Real.exp (-t) • nullB b)) = -Real.cosh (s - t)
    rw [h]
    have h2c : Real.exp (s - t) + Real.exp (t - s) = 2 * Real.cosh (s - t) := by
      rw [Real.cosh_eq, show -(s - t) = t - s by ring]
      ring
    rw [h2c]
    have hk : kkB a b ^ 2 * mmB a b = 1/2 := by linarith [hkk2]
    linear_combination (-2 * Real.cosh (s - t)) * hk
  have hself : ∀ s : ℝ, mink (axisV a b s) (axisV a b s) = -1 := by
    intro s
    have h := hcross s s
    rw [sub_self, Real.cosh_zero] at h
    simpa using h
  have htime : ∀ s : ℝ, 0 < axisV a b s (Sum.inr 0) := by
    intro s
    have hv : axisV a b s (Sum.inr 0) = kkB a b * (Real.exp s + Real.exp (-s)) := by
      show (kkB a b • (Real.exp s • nullA a + Real.exp (-s) • nullB b)) (Sum.inr 0) = _
      simp only [Pi.smul_apply, Pi.add_apply, nullA, nullB, Work.Mostow.nvec, Sum.elim_inr,
        smul_eq_mul, mul_one]
    rw [hv]
    positivity
  have hlift_axis : ∀ s : ℝ, hlift (axisPt a b s) = axisV a b s := by
    intro s
    have h1 : mform (axisV a b s) (axisV a b s) = -1 := by
      rw [← mink_eq_mform]; exact hself s
    have h2 : 0 < axisV a b s (Sum.inr 0) := htime s
    have h := eq_hlift_of_upper (axisV a b s) h1 h2
    exact h.symm
  have hdist_axis : ∀ s t : ℝ, hdist (axisPt a b s) (axisPt a b t) = |s - t| := by
    intro s t
    rw [hdist_eq_arcosh_mink, hlift_axis s, hlift_axis t, hcross s t]
    rw [neg_neg, ← Real.cosh_abs (s - t)]
    exact Real.arcosh_cosh (abs_nonneg (s - t))
  exact ⟨hkk2, hkk, hself, htime, hcross, hlift_axis, hdist_axis⟩

end

end Work.Mostow.gapA
