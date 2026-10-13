import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS_RegExport.RXT.Sys.FBZhat

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.FBGamma` — `mixed`-jets of functions of `θ` alone
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false

/-- `D_θ^a` of a function of `θ` alone does not depend on `z`. -/
theorem DthIter_z_indep (G : ℝ → ℝ) :
    ∀ (i : ℕ) (z z' θ : ℝ),
      Work.Spaces.DthIter i (fun _ θ' => G θ') z θ
        = Work.Spaces.DthIter i (fun _ θ' => G θ') z' θ := by
  intro i
  induction i with
  | zero => intro z z' θ; rfl
  | succ i ih =>
      intro z z' θ
      show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') z θ') θ
        = Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') z' θ') θ
      rw [show (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') z θ')
          = (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') z' θ')
          from funext (fun θ' => ih z z' θ')]

/-- `D_θ^a` of a function of `θ` alone is again a function of `θ` alone. -/
theorem DthIter_theta_form (G : ℝ → ℝ) (a : ℕ) :
    Work.Spaces.DthIter a (fun _ θ : ℝ => G θ)
      = fun _ θ => Work.Spaces.DthIter a (fun _ θ' => G θ') 0 θ := by
  funext z θ
  exact DthIter_z_indep G a z 0 θ

/-- `D_z^b` of a function of `θ` alone vanishes for `b ≥ 1`. -/
theorem DzIter_theta_only (G : ℝ → ℝ) (b : ℕ) (hb : 1 ≤ b) :
    Work.Spaces.DzIter b (fun _ θ : ℝ => G θ) = fun _ _ => 0 := by
  induction b with
  | zero => omega
  | succ b ih =>
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · subst hb0
        rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
        funext z θ
        simp only [Work.Spaces.Dz, Work.Spaces.pz]
        rw [show (fun z' : ℝ => (fun _ θ : ℝ => G θ) z' θ) = (fun _ : ℝ => G θ) from rfl,
          deriv_const]
        ring
      · rw [Work.Spaces.DzIter_succ, ih hbpos]
        funext z θ
        simp only [Work.Spaces.Dz, Work.Spaces.pz]
        rw [show (fun z' : ℝ => (fun _ _ : ℝ => (0 : ℝ)) z' θ) = (fun _ : ℝ => (0 : ℝ)) from rfl,
          deriv_const]
        ring

/-- Every `mixed`-jet with a `z`-derivative of a function of `θ` alone vanishes. -/
theorem mixed_theta_only (G : ℝ → ℝ) {a b : ℕ} (hb : 1 ≤ b) (z θ : ℝ) :
    Work.Spaces.mixed b a (fun _ θ => G θ) z θ = 0 := by
  rw [Work.Spaces.mixed, DthIter_theta_form G a]
  exact congrFun (congrFun (DzIter_theta_only
    (fun θ => Work.Spaces.DthIter a (fun _ θ' => G θ') 0 θ) b hb) z) θ

/-- With no `z`-derivative, the `mixed`-jet of a function of `θ` alone is its `θ`-jet at `0`. -/
theorem mixed_theta_only_zero (G : ℝ → ℝ) (a : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed 0 a (fun _ θ => G θ) z θ
      = Work.Spaces.DthIter a (fun _ θ' => G θ') 0 θ := by
  rw [Work.Spaces.mixed, Work.Spaces.DzIter_zero]
  exact DthIter_z_indep G a z 0 θ

end Work.FTS_RegExport.RXT.Sys
