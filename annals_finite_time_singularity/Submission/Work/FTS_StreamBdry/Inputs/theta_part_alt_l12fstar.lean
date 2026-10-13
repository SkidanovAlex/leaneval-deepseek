import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one
import Submission.Work.FTS.Nonlinear.FstarPkg.c2mInv_points
import Submission.Work.FTS_RegExport.RXT.SysAux.PieceCalc
import Submission.Work.Spaces.DzIter_le_of_pzIter

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.Inputs

noncomputable section

open MeasureTheory Set Filter

open scoped Topology

set_option maxHeartbeats 1000000

/-! ## The `D_z`-jets of `L₁₂(F_*) = 2α/(1+z)`

Self-contained version of the (private) `NonlinRows.NRow7.DzdIter_L12Fstar_le`, in the
two-variable `Spaces.DzIter` form needed by the `theta_part_jets` assembly. -/

/-- `∂_z^k` of a radial function. -/
theorem pzIter_radial' (r : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => r z) z θ = deriv^[k] r z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
      have hfun : (fun z' => Work.Spaces.pzIter k (fun z _ => r z) z' θ) = deriv^[k] r :=
        funext fun z' => ih z'
      show deriv (fun z' => Work.Spaces.pzIter k (fun z _ => r z) z' θ) z = deriv^[k + 1] r z
      rw [hfun, Function.iterate_succ_apply']

/-- `2α/(1+z)` is `C^∞` on `(-1,∞)`. -/
theorem contDiffOn_invH' (α : ℝ) :
    ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi (-1)) := by
  have h : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z)⁻¹) (Set.Ioi (-1)) := by
    refine ContDiffOn.inv (by fun_prop) ?_
    intro z hz
    simp only [Set.mem_Ioi] at hz
    linarith
  have h2 : ContDiffOn ℝ ⊤ (fun z : ℝ => (2 * α) * (1 + z)⁻¹) (Set.Ioi (-1)) :=
    contDiffOn_const.mul h
  refine h2.congr ?_
  intro z _
  simp only [div_eq_mul_inv]

/-- `|z^j ∂_z^j (2α/(1+z))| ≤ 48α` for `z ≥ 0`, `j ≤ 4`. -/
theorem pzIter_invH_bound' (α : ℝ) (hα : 0 < α) (j : ℕ) (hj : j ≤ 4) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |z ^ j * Work.Spaces.pzIter j (fun z _ => 2 * α / (1 + z)) z θ| ≤ 48 * α := by
  intro z hzIz θ _
  have hz0 : (0 : ℝ) ≤ z := hzIz
  rw [pzIter_radial' (fun z => 2 * α / (1 + z)) j z θ]
  rw [show (fun z : ℝ => 2 * α / (1 + z)) = fun z => (2 * α) * (1 + z)⁻¹ from by
    funext z; rw [div_eq_mul_inv]]
  rw [Work.FTS.Nonlinear.FstarPkg.deriv_iter_const_mul (2 * α) (fun z : ℝ => (1 + z)⁻¹) j]
  simp only
  rw [Work.FTS.Nonlinear.FstarPkg.iter_deriv_nInvClosed j z (by linarith)]
  have hw := Work.FTS.Nonlinear.FstarPkg.nInvClosed_weighted j z hz0
  have habs : z ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z|
      ≤ |(z + 1) ^ j * Work.FTS.Nonlinear.FstarPkg.nInvClosed j z| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ z + 1) j)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz0 (by linarith) j) (abs_nonneg _)
  have hkey : z ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z| ≤ (j.factorial : ℝ) :=
    le_trans habs hw
  have hfact : (j.factorial : ℝ) ≤ 24 := by interval_cases j <;> norm_num
  have h2α : (0 : ℝ) < 2 * α := by linarith
  rw [show z ^ j * ((2 * α) * Work.FTS.Nonlinear.FstarPkg.nInvClosed j z)
      = (2 * α) * (z ^ j * Work.FTS.Nonlinear.FstarPkg.nInvClosed j z) from by ring]
  rw [abs_mul, abs_of_nonneg h2α.le]
  calc (2 * α) * |z ^ j * Work.FTS.Nonlinear.FstarPkg.nInvClosed j z|
      = (2 * α) * (z ^ j * |Work.FTS.Nonlinear.FstarPkg.nInvClosed j z|) := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hz0 j)]
    _ ≤ (2 * α) * (j.factorial : ℝ) := mul_le_mul_of_nonneg_left hkey h2α.le
    _ ≤ (2 * α) * 24 := mul_le_mul_of_nonneg_left hfact h2α.le
    _ = 48 * α := by ring

/-- **The `D_z`-jets of `L₁₂(F_*)` are bounded by `4800α`.** -/
theorem L12Fstar_jets' : ∃ C : ℝ, 0 < C ∧
    ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      |Work.Spaces.DzIter k (fun z _ => Work.Construction.L12 (Work.Construction.Fstar α) z)
        z 0| ≤ C * α := by
  refine ⟨4800, by norm_num, ?_⟩
  intro α hα hα1 k hk z hz
  have hcongr : ∀ w ∈ Set.Ioi (0 : ℝ),
      Work.Construction.L12 (Work.Construction.Fstar α) w = 2 * α / (1 + w) :=
    fun w hw => Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1
      (by have hw' : (0 : ℝ) < w := hw; linarith)
  have h1 : Work.Spaces.DzIter k (fun z _ => Work.Construction.L12 (Work.Construction.Fstar α) z)
        z 0 = Work.Spaces.DzIter k (fun z _ => 2 * α / (1 + z)) z 0 :=
    Work.FTS_RegExport.RXT.SysAux.DzIter_congr_of_isOpen (isOpen_Ioi.prod isOpen_univ)
      (by rintro ⟨a, b⟩ ⟨ha, -⟩; exact hcongr a ha) k z 0 ⟨hz, trivial⟩
  rw [h1]
  have hmain := Work.Spaces.DzIter_le_of_pzIter (h := fun z _ => 2 * α / (1 + z)) (M := 48 * α)
    (by positivity)
    (fun θ _ => contDiffOn_invH' α)
    (fun j hj z' hz' θ hθ => pzIter_invH_bound' α hα j hj z' hz' θ hθ)
    k (by omega) z (le_of_lt hz) 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩
  linarith [hmain]

end

end Work.FTS_StreamBdry.Inputs
