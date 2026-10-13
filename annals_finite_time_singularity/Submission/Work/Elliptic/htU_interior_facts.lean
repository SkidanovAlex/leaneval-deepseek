import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.HardyTwoDefs
import Submission.Work.Elliptic.htU_contDiffAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- On the open interval `(0, π/2)` the denominator `sin (2θ)` of `htU f` does not vanish. -/
private lemma sin_two_ne_zero {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) : Real.sin (2 * x) ≠ 0 := by
  have h1 : 0 < 2 * x := by linarith [hx.1]
  have h2 : 2 * x < π := by linarith [hx.2]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)

/-- `htU f x * sin (2x) = f x` on `(0, π/2)`. -/
private lemma htU_mul_sin (f : ℝ → ℝ) {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) :
    (htU f) x * Real.sin (2 * x) = f x := by
  simp only [htU]
  exact div_mul_cancel₀ _ (sin_two_ne_zero hx)

/-- `f` is `C²` at every interior point of `[0, π/2]`. -/
private lemma contDiffAt_Ioo (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) : ContDiffAt ℝ 2 f x :=
  hf.contDiffAt (mem_of_superset (isOpen_Ioo.mem_nhds hx) Ioo_subset_Icc_self)

/-- `HasDerivAt` for `sin (2·)`. -/
private lemma hasDerivAt_sin_two (x : ℝ) :
    HasDerivAt (fun z : ℝ => Real.sin (2 * z)) (2 * Real.cos (2 * x)) x := by
  have h1 : HasDerivAt (fun z : ℝ => 2 * z) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun z : ℝ => Real.sin (2 * z)) (Real.cos (2 * x) * 2) x := h1.sin
  rw [show Real.cos (2 * x) * 2 = 2 * Real.cos (2 * x) by ring] at h2
  exact h2

/-- `HasDerivAt` for `cos (2·)`. -/
private lemma hasDerivAt_cos_two (x : ℝ) :
    HasDerivAt (fun z : ℝ => Real.cos (2 * z)) (-2 * Real.sin (2 * x)) x := by
  have h1 : HasDerivAt (fun z : ℝ => 2 * z) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun z : ℝ => Real.cos (2 * z)) (-Real.sin (2 * x) * 2) x := h1.cos
  rw [show -Real.sin (2 * x) * 2 = -2 * Real.sin (2 * x) by ring] at h2
  exact h2

/-- First-derivative identity: `u' sin(2x) + 2 u cos(2x) = f'` on `(0, π/2)`, obtained by
differentiating `u · sin(2·) = f`. -/
private lemma htU_deriv_one (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) :
    deriv (htU f) x * Real.sin (2 * x) + 2 * (htU f) x * Real.cos (2 * x) = deriv f x := by
  have hUS : Set.EqOn ((htU f) * fun z : ℝ => Real.sin (2 * z)) f (Set.Ioo 0 (π / 2)) := by
    intro z hz
    simp only [Pi.mul_apply, htU]
    exact div_mul_cancel₀ _ (sin_two_ne_zero hz)
  have hEv : ((htU f) * fun z : ℝ => Real.sin (2 * z)) =ᶠ[𝓝 x] f :=
    Set.EqOn.eventuallyEq_of_mem hUS (isOpen_Ioo.mem_nhds hx)
  have hu : HasDerivAt (htU f) (deriv (htU f) x) x :=
    ((htU_contDiffAt f hf x hx).differentiableAt (by norm_num)).hasDerivAt
  have hS : HasDerivAt (fun z : ℝ => Real.sin (2 * z)) (2 * Real.cos (2 * x)) x :=
    hasDerivAt_sin_two x
  have key : deriv ((htU f) * fun z : ℝ => Real.sin (2 * z)) x = deriv f x := hEv.deriv_eq
  rw [(hu.mul hS).deriv] at key
  convert key using 1
  ring

/-- Second-derivative identity: `u'' sin(2x) + 4 u' cos(2x) - 4 u sin(2x) = f''` on `(0, π/2)`,
obtained by differentiating the first-derivative identity. -/
private lemma htU_deriv_two (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    {x : ℝ} (hx : x ∈ Set.Ioo 0 (π / 2)) :
    deriv (deriv (htU f)) x * Real.sin (2 * x) + 4 * Real.cos (2 * x) * deriv (htU f) x
      - 4 * Real.sin (2 * x) * (htU f) x = deriv (deriv f) x := by
  have hzero : (fun z : ℝ => deriv (htU f) z * Real.sin (2 * z) + 2 * (htU f) z * Real.cos (2 * z)
      - deriv f z) =ᶠ[𝓝 x] (0 : ℝ → ℝ) := by
    apply Set.EqOn.eventuallyEq_of_mem _ (isOpen_Ioo.mem_nhds hx)
    intro z hz
    have h := htU_deriv_one f hf hz
    simp only [Pi.zero_apply]
    linarith [h]
  have hzerod : deriv (fun z : ℝ => deriv (htU f) z * Real.sin (2 * z)
      + 2 * (htU f) z * Real.cos (2 * z) - deriv f z) x = 0 := by
    have h := hzero.deriv_eq
    simpa using h
  have hu : HasDerivAt (htU f) (deriv (htU f) x) x :=
    ((htU_contDiffAt f hf x hx).differentiableAt (by norm_num)).hasDerivAt
  have hdu : HasDerivAt (deriv (htU f)) (deriv (deriv (htU f)) x) x :=
    (((htU_contDiffAt f hf x hx).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have hdf : HasDerivAt (deriv f) (deriv (deriv f) x) x :=
    (((contDiffAt_Ioo f hf hx).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have hS : HasDerivAt (fun z : ℝ => Real.sin (2 * z)) (2 * Real.cos (2 * x)) x :=
    hasDerivAt_sin_two x
  have hC : HasDerivAt (fun z : ℝ => Real.cos (2 * z)) (-2 * Real.sin (2 * x)) x :=
    hasDerivAt_cos_two x
  have hA : HasDerivAt (fun z : ℝ => deriv (htU f) z * Real.sin (2 * z))
      (deriv (deriv (htU f)) x * Real.sin (2 * x)
        + deriv (htU f) x * (2 * Real.cos (2 * x))) x :=
    hdu.mul hS
  have hB : HasDerivAt (fun z : ℝ => 2 * (htU f) z * Real.cos (2 * z))
      ((2 * deriv (htU f) x) * Real.cos (2 * x)
        + (2 * (htU f) x) * (-2 * Real.sin (2 * x))) x :=
    (hu.const_mul 2).mul hC
  have hF : HasDerivAt (fun z : ℝ => deriv (htU f) z * Real.sin (2 * z)
      + 2 * (htU f) z * Real.cos (2 * z) - deriv f z)
      ((deriv (deriv (htU f)) x * Real.sin (2 * x)
          + deriv (htU f) x * (2 * Real.cos (2 * x)))
        + ((2 * deriv (htU f) x) * Real.cos (2 * x)
          + (2 * (htU f) x) * (-2 * Real.sin (2 * x)))
        - deriv (deriv f) x) x :=
    (hA.add hB).sub hdf
  rw [hF.deriv] at hzerod
  nlinarith [hzerod]

theorem htU_interior_facts (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2))) :
    ContDiffOn ℝ 2 (Work.Elliptic.htU f) (Set.Ioo 0 (π / 2)) ∧
    (∀ x ∈ Set.Ioo 0 (π / 2), deriv f x = iteratedDerivWithin 1 f (Set.Icc 0 (π / 2)) x) ∧
    (∀ x ∈ Set.Ioo 0 (π / 2),
        deriv (deriv f) x = iteratedDerivWithin 2 f (Set.Icc 0 (π / 2)) x) ∧
    (∀ x ∈ Set.Ioo 0 (π / 2),
        (Real.sin (2 * x)) ^ 2 * deriv (Work.Elliptic.htU f) x
          = deriv f x * Real.sin (2 * x) - 2 * Real.cos (2 * x) * f x) ∧
    (∀ x ∈ Set.Ioo 0 (π / 2),
        Real.sin (2 * x) * deriv (deriv (Work.Elliptic.htU f)) x
          = deriv (deriv f) x + 4 * f x - 4 * Real.cos (2 * x) * deriv (Work.Elliptic.htU f) x) ∧
    ContinuousOn (Work.Elliptic.htU f) (Set.Ioo 0 (π / 2)) ∧
    ContinuousOn (fun x => deriv (Work.Elliptic.htU f) x) (Set.Ioo 0 (π / 2)) ∧
    ContinuousOn (fun x => deriv (deriv (Work.Elliptic.htU f)) x) (Set.Ioo 0 (π / 2)) ∧
    ContinuousOn (fun x => deriv (deriv f) x) (Set.Ioo 0 (π / 2)) := by
  have hpi : (0 : ℝ) < π / 2 := by linarith [Real.pi_pos]
  have hCU : ContDiffOn ℝ 2 (htU f) (Set.Ioo 0 (π / 2)) :=
    fun x hx => (htU_contDiffAt f hf x hx).contDiffWithinAt
  refine ⟨hCU, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := 1) (uniqueDiffOn_Icc hpi)
        ((contDiffAt_Ioo f hf hx).of_le (by norm_num)) (Ioo_subset_Icc_self hx),
      iteratedDeriv_one]
  · intro x hx
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := 2) (uniqueDiffOn_Icc hpi)
        ((contDiffAt_Ioo f hf hx).of_le (by norm_num)) (Ioo_subset_Icc_self hx),
      show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
  · intro x hx
    have h1 := htU_deriv_one f hf hx
    have h2 := htU_mul_sin f hx
    linear_combination h1 * Real.sin (2 * x) - (2 * Real.cos (2 * x)) * h2
  · intro x hx
    have h1 := htU_deriv_two f hf hx
    have h2 := htU_mul_sin f hx
    nlinarith [h1, h2]
  · exact hCU.continuousOn
  · exact hCU.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  · have h1 : ContDiffOn ℝ 1 (deriv (htU f)) (Set.Ioo 0 (π / 2)) :=
      hCU.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
    exact h1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  · have h1 : ContDiffOn ℝ 2 f (Set.Ioo 0 (π / 2)) := hf.mono Ioo_subset_Icc_self
    have h2 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (π / 2)) :=
      h1.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
    exact h2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)

end Work.Elliptic
