import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row24

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Open.Row24Aux

theorem angMulScaledOpen {α₂ Ci α c B : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hB : 0 < B) (hcB : c * B = Ci)
    (hSmoothInt : Work.Spaces.SmoothInt (fun _ (θ : ℝ) => -((Real.sin θ)^2)))
    (hbound : ∀ θ ∈ Work.Spaces.Iθ, |(-((Real.sin θ)^2))| ≤ B)
    (hdth : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ : ℝ) => -((Real.sin θ)^2)) 0 θ| ≤ B * Real.sin (2*θ))
    {g : Work.FTS.Galerkin.Fn} (hsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g) (hIoc : α ∈ Set.Ioc 0 α₂) :
    Work.Spaces.HkMem α 4 (fun z θ => c * (-((Real.sin θ)^2)) * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => c * (-((Real.sin θ)^2)) * g z θ) ≤ Ci * Ci * Work.FTS.Nonlin.Xn α g := by
  have hci : 0 < Ci := hN.pos.1
  -- `c` is positive because `c * B = Ci > 0` and `B > 0`
  have hc : 0 < c := by
    by_contra hc
    push_neg at hc
    nlinarith [hci, hB]
  -- the scaled angular profile is still `SmoothInt`, hence `SmoothOpen`
  have hSI : Work.Spaces.SmoothInt (fun _ (θ : ℝ) => c * (-((Real.sin θ)^2))) := by
    constructor
    · change ContDiffOn ℝ ⊤ (fun x : ℝ × ℝ => c * -Real.sin x.2 ^ 2)
        (Set.Ioi (-1) ×ˢ Set.Ioo 0 (Real.pi / 2))
      exact (contDiffOn_const (𝕜 := ℝ) (c := c)).mul hSmoothInt.1
    · intro θ hθ
      simpa only [Pi.mul_apply] using
        (contDiffOn_const (𝕜 := ℝ) (c := c)).mul (hSmoothInt.2 θ hθ)
  have hSO : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => c * (-((Real.sin θ)^2))) :=
    Work.FTS.EllipticEst.smoothOpen_of_smoothInt hSI
  -- boundedness of the scaled profile
  have hb1 : ∀ θ ∈ Work.Spaces.Iθ, |c * (-((Real.sin θ)^2))| ≤ Ci := by
    intro θ hθ
    rw [abs_mul, abs_of_pos hc]
    calc c * |(-((Real.sin θ)^2))| ≤ c * B := mul_le_mul_of_nonneg_left (hbound θ hθ) hc.le
      _ = Ci := hcB
  -- the `D_θ`-iterates of the scaled profile vanish like `sin 2θ`
  have hb2 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ : ℝ) => c * (-((Real.sin θ)^2))) 0 θ|
        ≤ Ci * Real.sin (2*θ) := by
    intro i hi1 hi4 θ hθ
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.DthIter_const_mul i c
      (fun _ (θ : ℝ) => -((Real.sin θ)^2))]
    rw [abs_mul, abs_of_pos hc]
    calc c * |Work.Spaces.DthIter i (fun _ (θ : ℝ) => -((Real.sin θ)^2)) 0 θ|
        ≤ c * (B * Real.sin (2*θ)) := mul_le_mul_of_nonneg_left (hdth i hi1 hi4 θ hθ) hc.le
      _ = Ci * Real.sin (2*θ) := by rw [← hcB]; ring
  exact hN.angmul α hIoc (fun θ => c * (-((Real.sin θ)^2))) g hSO hb1 hb2 hsm hmem

end Work.FTS.Nonlinear.Open.Row24Aux
