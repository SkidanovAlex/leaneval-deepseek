/-
# `PhiStarE5` — `SmoothOpen` bookkeeping and the smoothness of `φ` and `Γ`, `Γ̄`

Helper lemmas for `PhiStarE5.PhiStar_existence`. -/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.PhiStarE5

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst (SmoothOpen Q0 mem_Q0 smoothOpen_of_forall)

set_option autoImplicit false
noncomputable section

/-! ## 1. `SmoothOpen` bookkeeping -/

/-- `SmoothOpen` is closed under pointwise subtraction. -/
theorem smoothOpen_sub {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ - g z θ) := by
  have hfun : Function.uncurry (fun z θ => f z θ - g z θ)
      = Function.uncurry f - Function.uncurry g := by
    funext p; rfl
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ - g z θ)) Q0
  rw [hfun]
  exact ContDiffOn.sub hf hg

/-- `SmoothOpen` is closed under pointwise multiplication. -/
theorem smoothOpen_mul {f g : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (hg : SmoothOpen g) :
    SmoothOpen (fun z θ => f z θ * g z θ) := by
  have hfun : Function.uncurry (fun z θ => f z θ * g z θ)
      = Function.uncurry f * Function.uncurry g := by
    funext p; rfl
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ * g z θ)) Q0
  rw [hfun]
  exact ContDiffOn.mul hf hg

/-- A radial function is `SmoothOpen`. -/
theorem smoothOpen_radial {r : ℝ → ℝ} (hr : ∀ n : ℕ, ContDiffOn ℝ n r (Set.Ioi 0)) :
    SmoothOpen (fun z _ => r z) := by
  refine smoothOpen_of_forall (fun n => ?_)
  exact (hr n).comp contDiffOn_fst (fun p hp => (mem_Q0.mp hp).1)

/-- An angular function is `SmoothOpen`. -/
theorem smoothOpen_angular {b : ℝ → ℝ}
    (hb : ∀ n : ℕ, ContDiffOn ℝ n b (Set.Ioo 0 (π / 2))) :
    SmoothOpen (fun _ θ => b θ) := by
  refine smoothOpen_of_forall (fun n => ?_)
  exact (hb n).comp contDiffOn_snd (fun p hp => (mem_Q0.mp hp).2)

/-! ## 2. Smoothness of the two factors `φ` and `Γ` -/

/-- `φ = 2z/(1+z)²` is `C^∞` on `(0,∞)`. -/
theorem contDiffOn_phiR (n : ℕ) :
    ContDiffOn ℝ n (fun z : ℝ => Work.FTS.VocabO.phiR z) (Set.Ioi 0) := by
  rw [show Work.FTS.VocabO.phiR = fun z : ℝ => 2 * z / (1 + z) ^ 2 from by
    funext z; simp only [Work.FTS.VocabO.phiR]]
  refine ContDiffOn.div (by fun_prop) (by fun_prop) ?_
  intro z hz
  have hz' : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
  positivity

/-- `Γ(θ) = (sinθcos²θ)^{α/3}` is `C^∞` on `(0,π/2)`. -/
theorem contDiffOn_Gam (α : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun θ : ℝ => Work.Spaces.Gam α θ) (Set.Ioo 0 (π / 2)) := by
  have hbase : ContDiffOn ℝ n (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo 0 (π / 2)) := by fun_prop
  have hpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by
    intro θ hθ
    have h1 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have h := hbase.rpow_const_of_ne (p := α / 3) hpos
  refine h.congr (fun θ _ => ?_)
  simp only [Work.Spaces.Gam]

/-- `Γ̄ = Γ/c - (5/4) sin 2θ` is `C^∞` on `(0,π/2)`. -/
theorem contDiffOn_GamBar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) :
    ContDiffOn ℝ n (fun θ : ℝ => Work.FTS.VocabO.GamBar α θ) (Set.Ioo 0 (π / 2)) := by
  have hc : (0 : ℝ) < Work.Spaces.c α := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have hGam := contDiffOn_Gam α n
  have hsin : ContDiffOn ℝ n (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (π / 2)) := by
    fun_prop
  have h1 : ContDiffOn ℝ n (fun θ : ℝ => Work.Spaces.Gam α θ / Work.Spaces.c α)
      (Set.Ioo 0 (π / 2)) :=
    ContDiffOn.div hGam contDiffOn_const (fun θ _ => ne_of_gt hc)
  have h2 : ContDiffOn ℝ n (fun θ : ℝ => (5 / 4 : ℝ) * Real.sin (2 * θ))
      (Set.Ioo 0 (π / 2)) :=
    ContDiffOn.mul contDiffOn_const hsin
  exact (ContDiffOn.sub h1 h2).congr (fun θ _ => by
    simp only [Work.FTS.VocabO.GamBar])
end

end Work.FTS.H2.PhiStarE5
