import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.FTS.Nonlinear.FstarPkg.DthFstar_W
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.AngProfAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular jet `θ ↦ D_θ^i (a · Γ(θ) · q(θ))` is continuous on `(0, π/2)`

`Γ(θ) = (sin θ · cos²θ)^{α/3}` and `q(θ) = cos 2θ - 1/3` are both smooth on the open
interval `(0, π/2)` (`contDiffOn_Gam_Ioo` for `Γ`, elementary for `q`), and the operator
`dthU φ = sin(2θ)·φ'` preserves `C^∞`-regularity on an open set
(`contDiffOn_dthU_iter_open`).  Hence every iterate `dthU^[i]` of the product is continuous
on `(0, π/2)`, with no restriction on `i` (in particular for `i ≤ 6`).
-/

open scoped Real Topology ContDiff

namespace Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux

/-- The angular factor `q(θ) = cos 2θ - 1/3` is smooth on the open interval. -/
lemma contDiffOn_qfun :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ : ℝ => Work.Spaces.qfun θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have h : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun θ : ℝ => Real.cos (2 * θ) - 1 / 3) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  refine h.congr (fun θ _ => ?_)
  simp only [Work.Spaces.qfun_apply]

/-- The profile `θ ↦ a · Γ(θ) · q(θ)` is smooth on the open interval. -/
lemma contDiffOn_gamQfun (α a : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun θ : ℝ => a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
  contDiffOn_const.mul
    ((Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_Gam_Ioo α).mul contDiffOn_qfun)

theorem gamQfun_jet_continuousOn : ∀ α ∈ Set.Ioc 0 1, ∀ a : ℝ, |a| ≤ 20 →
    ∀ i : ℕ, i ≤ 6 →
      ContinuousOn (fun θ => Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ)
        (Set.Ioo 0 (Real.pi / 2)) := by
  intro α _ a _ i _
  exact (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_dthU_iter_open isOpen_Ioo
    (contDiffOn_gamQfun α a) i).continuousOn

end Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux
