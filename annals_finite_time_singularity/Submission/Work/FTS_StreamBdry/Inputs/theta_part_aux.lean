import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.Inputs

noncomputable section

open MeasureTheory Set Filter

/-! ## Auxiliary facts about the angular moment `Qang` and the radial operator `DzdIter` -/

/-- `Qang X 0 z = 𝔽K X z`: the two angular moments agree at level `0`. -/
theorem Qang_zero_eq_FK (X : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Qang X 0 z = Work.Construction.FK X z := by
  rw [Work.Elliptic.Qang, Work.Construction.FK]
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [Work.Spaces.DzIter_zero]
  exact mul_comm _ _

/-- `DzdIter (j+1) u = DzdIter j (DzdIter 1 u)`. -/
theorem DzdIter_succ_eq (j : ℕ) (u : ℝ → ℝ) :
    Work.Elliptic.DzdIter (j + 1) u = Work.Elliptic.DzdIter j (Work.Elliptic.DzdIter 1 u) := by
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter (j + 1) u,
    Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j (Work.Elliptic.DzdIter 1 u),
    Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter 1 u,
    Function.iterate_one, Function.iterate_succ_apply]

/-- `DzdIter` commutes with multiplication by a constant. -/
theorem DzdIter_const_mul (j : ℕ) (c : ℝ) (u : ℝ → ℝ) :
    Work.Elliptic.DzdIter j (fun z => c * u z) = fun z => c * Work.Elliptic.DzdIter j u z := by
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j (fun z => c * u z),
    Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j u,
    Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul]

/-- The radial operator applied to a linear combination of two functions. -/
theorem DzdIter_const_mul_add {c d : ℝ} {u v : ℝ → ℝ} {j : ℕ}
    (hu : ∀ b < j, ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (Work.Elliptic.DzdIter b u) z)
    (hv : ∀ b < j, ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (Work.Elliptic.DzdIter b v) z)
    {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.DzdIter j (fun w => c * u w + d * v w) z
      = c * Work.Elliptic.DzdIter j u z + d * Work.Elliptic.DzdIter j v z := by
  have hsum : (fun w => c * u w + d * v w) = (fun w => c * u w) + (fun w => d * v w) := rfl
  rw [hsum, Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff j _ _ ?_ ?_ z hz,
    DzdIter_const_mul j c u, DzdIter_const_mul j d v]
  · intro b hb z' hz'
    rw [DzdIter_const_mul b c u]
    exact (hu b hb z' hz').const_mul c
  · intro b hb z' hz'
    rw [DzdIter_const_mul b d v]
    exact (hv b hb z' hz').const_mul d

/-- `Qd` is open. -/
theorem isOpen_Qd : IsOpen Work.Construction.Qd := Work.FTS.EllipticEst.isOpen_Q0

/-- `DzdIter` of a negated function. -/
theorem DzdIter_neg (j : ℕ) (u : ℝ → ℝ) :
    Work.Elliptic.DzdIter j (fun z => -u z) = fun z => -Work.Elliptic.DzdIter j u z := by
  have h : (fun z : ℝ => -u z) = fun z => (-1 : ℝ) * u z := by funext z; ring
  rw [h, DzdIter_const_mul j (-1) u]
  funext z; ring

/-- The derivative of `w ↦ c/(1+w)`. -/
theorem deriv_const_div_one_add (c z : ℝ) (hz : z ≠ -1) :
    deriv (fun w : ℝ => c / (1 + w)) z = -c / (1 + z) ^ 2 := by
  have h1 : HasDerivAt (fun w : ℝ => 1 + w) 1 z := (hasDerivAt_id z).const_add 1
  have h0 : HasDerivAt (fun _ : ℝ => c) 0 z := hasDerivAt_const z c
  have h := h0.div h1 (by intro hc; exact hz (by linarith))
  rw [show deriv (fun w : ℝ => c / (1 + w)) z
    = (0 * (1 + z) - c * 1) / (1 + z) ^ 2 from h.deriv]
  ring

/-- `D_θ` kills the zero function. -/
theorem Dth_zero : Work.Spaces.Dth (0 : ℝ → ℝ → ℝ) = 0 := by
  funext z θ
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => (0 : ℝ)) θ = 0
  rw [deriv_const]
  ring

/-- `D_z` kills the zero function. -/
theorem Dz_zero : Work.Spaces.Dz (0 : ℝ → ℝ → ℝ) = 0 := by
  funext z θ
  show z * deriv (fun z' : ℝ => (0 : ℝ)) z = 0
  rw [deriv_const]
  ring

/-- `D_θ` kills a function that does not depend on `θ`. -/
theorem Dth_radial (r : ℝ → ℝ) : Work.Spaces.Dth (fun z _ => r z) = 0 := by
  funext z θ
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => r z) θ = 0
  rw [deriv_const]
  ring

/-- The iterated `D_θ` of a radial function vanishes from order one on. -/
theorem DthIter_radial_eq_zero (r : ℝ → ℝ) : ∀ i : ℕ, 1 ≤ i →
    Work.Spaces.DthIter i (fun z _ => r z) = 0 := by
  intro i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  clear hi
  induction k with
  | zero => simpa using Dth_radial r
  | succ k ih =>
      rw [Work.Spaces.DthIter_succ (k + 1) (fun z _ => r z), ih, Dth_zero]

/-- The iterated `D_z` of the zero function vanishes. -/
theorem DzIter_zero_fun : ∀ j : ℕ, Work.Spaces.DzIter j (0 : ℝ → ℝ → ℝ) = 0 := by
  intro j
  induction j with
  | zero => rfl
  | succ k ih => rw [Work.Spaces.DzIter_succ, ih, Dz_zero]

end

end Work.FTS_StreamBdry.Inputs
