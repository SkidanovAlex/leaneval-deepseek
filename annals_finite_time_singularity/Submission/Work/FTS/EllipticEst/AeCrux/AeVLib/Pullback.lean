import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.AeCrux.AeVLib.Meas
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.EllipticEst.AeCrux

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz

set_option linter.unusedSimpArgs false

theorem contOn_expComp {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => f (Real.exp p.1) p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hφ : Continuous (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) := by fun_prop
  have hmap : Set.MapsTo (fun p : ℝ × ℝ => (Real.exp p.1, p.2))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun p hp => ⟨Real.exp_pos p.1, hp.2⟩
  exact hf.comp (hφ.continuousOn (s := (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))) hmap

/-! ## 7. The pull-back datum and its mixed-derivative identities -/

def pb (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t θ => u (Real.exp t) θ

theorem pb_contDiff {u : ℝ → ℝ → ℝ}
    (h : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (pb u)) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hφ : ContDiff ℝ n (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) := by fun_prop
  have hmap : Set.MapsTo (fun p : ℝ × ℝ => (Real.exp p.1, p.2))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
      ((Set.Ioi (0:ℝ)) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun p hp => ⟨Real.exp_pos p.1, hp.2⟩
  exact (h n).comp hφ.contDiffOn hmap

theorem pb_pz {u : ℝ → ℝ → ℝ} (hSm : Work.FTS.EllipticEst.SmoothOpen u) {t θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (pb u) t θ = Real.exp t * Work.Spaces.pz u (Real.exp t) θ := by
  have hd1 : DifferentiableAt ℝ (fun z : ℝ => u z θ) (Real.exp t) :=
    (hSm.hasDerivAt_slice hθ (Real.exp_pos t)).differentiableAt
  have hd2 : DifferentiableAt ℝ Real.exp t := (Real.hasDerivAt_exp t).differentiableAt
  rw [show Work.Spaces.pz (pb u) t θ
      = deriv ((fun z : ℝ => u z θ) ∘ Real.exp) t from rfl,
    deriv_comp t hd1 hd2, Real.deriv_exp, mul_comm]
  rfl

theorem pb_pth {u : ℝ → ℝ → ℝ} (t θ : ℝ) :
    Work.Spaces.pth (pb u) t θ = Work.Spaces.pth u (Real.exp t) θ := rfl

theorem pb_pthIter {u : ℝ → ℝ → ℝ} (t θ : ℝ) :
    Work.Spaces.pthIter 2 (pb u) t θ = Work.Spaces.pthIter 2 u (Real.exp t) θ := rfl

theorem pb_DzDz {u : ℝ → ℝ → ℝ} (hSm : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.Dz (Work.Spaces.Dz u) z θ
      = Work.Spaces.Dz u z θ + z ^ 2 * Work.Spaces.pzIter 2 u z θ := by
  have hd : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pz u t θ) z :=
    (hSm.pz.hasDerivAt_slice hθ hz).differentiableAt
  rw [Work.Spaces.Dz, Work.Spaces.pz_Dz_eq (G := u) hd]
  simp only [Work.Spaces.Dz, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
  ring

theorem pb_pz2 {u : ℝ → ℝ → ℝ} (hSm : Work.FTS.EllipticEst.SmoothOpen u) {t θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (Work.Spaces.pz (pb u)) t θ
      = Work.Spaces.Dz (Work.Spaces.Dz u) (Real.exp t) θ := by
  have hid : ∀ s : ℝ, Work.Spaces.pz (pb u) s θ = Work.Spaces.Dz u (Real.exp s) θ := by
    intro s
    rw [pb_pz hSm hθ, Work.Spaces.Dz]
  have hfun : (fun s : ℝ => Work.Spaces.pz (pb u) s θ)
      = (fun s : ℝ => Work.Spaces.Dz u (Real.exp s) θ) := funext hid
  have h1 : deriv (fun s : ℝ => Work.Spaces.Dz u (Real.exp s) θ) t
      = Real.exp t * Work.Spaces.pz (Work.Spaces.Dz u) (Real.exp t) θ := by
    rw [show (fun s : ℝ => Work.Spaces.Dz u (Real.exp s) θ)
        = ((fun z : ℝ => Work.Spaces.Dz u z θ) ∘ Real.exp) from rfl,
      deriv_comp t (hSm.Dz.hasDerivAt_slice hθ (Real.exp_pos t)).differentiableAt
        ((Real.hasDerivAt_exp t).differentiableAt), Real.deriv_exp]
    exact mul_comm _ _
  rw [show Work.Spaces.pz (Work.Spaces.pz (pb u)) t θ
      = deriv (fun s : ℝ => Work.Spaces.pz (pb u) s θ) t from rfl, hfun, h1]
  rfl

theorem pb_pth_pz {u : ℝ → ℝ → ℝ} (hSm : Work.FTS.EllipticEst.SmoothOpen u) {t θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pth (Work.Spaces.pz (pb u)) t θ
      = Work.Spaces.Dz (Work.Spaces.pth u) (Real.exp t) θ := by
  have hev : (fun θ' : ℝ => Work.Spaces.pz (pb u) t θ')
      =ᶠ[𝓝 θ] (fun θ' : ℝ => Real.exp t * Work.Spaces.pz u (Real.exp t) θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    rw [pb_pz hSm hθ']
  have hcd : ContDiffAt ℝ 2 (Function.uncurry u) (Real.exp t, θ) :=
    (hSm.forall 2).contDiffAt (IsOpen.mem_nhds Work.FTS.EllipticEst.isOpen_Q0
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos t, hθ.1, hθ.2⟩))
  rw [show Work.Spaces.pth (Work.Spaces.pz (pb u)) t θ
      = deriv (fun θ' : ℝ => Work.Spaces.pz (pb u) t θ') θ from rfl, hev.deriv_eq,
    deriv_const_mul_field]
  rw [show deriv (fun θ' : ℝ => Work.Spaces.pz u (Real.exp t) θ') θ
      = Work.Spaces.pth (Work.Spaces.pz u) (Real.exp t) θ from rfl,
    ← Work.Spaces.pz_pth_comm hcd]
  rfl




end Work.FTS.EllipticEst.AeCrux
