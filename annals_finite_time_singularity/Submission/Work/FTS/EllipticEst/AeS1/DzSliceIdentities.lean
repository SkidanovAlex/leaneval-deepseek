import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.EllipticEst.AeS1.ZsqMixedOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-! ## The two slice identities

The first identity is the `m = 1`, `i = 0` instance of
`Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open` (i.e. `z²∂_z²` commutes with
`D_z = z∂_z`).  The second is the commutation of `∂_z` with the iterated `∂_θ`, which is
Clairaut's theorem iterated, together with the trivial commutation of `∂_θ` with the
`z`-multiplication. -/

/-- `SmoothOpen` is closed under the iterated `∂_θ`. -/
theorem SmoothOpen_pthIter_local {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (i : ℕ) : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i F) := by
  induction i with
  | zero => simpa using hF
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- Multiplication by the first variable commutes with `∂_θ` (the factor is constant in the
differentiated variable). -/
theorem pth_mul_fst (g : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => z * g z θ) = fun z θ => z * Work.Spaces.pth g z θ := by
  funext z θ
  simpa only [Work.Spaces.pth] using
    deriv_const_mul_field (v := fun θ' => g z θ') (x := θ) z

/-- Multiplication by the first variable commutes with the iterates of `∂_θ`. -/
theorem pthIter_mul_fst (g : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.pthIter n (fun z θ => z * g z θ)
      = fun z θ => z * Work.Spaces.pthIter n g z θ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]
      exact pth_mul_fst (Work.Spaces.pthIter n g)

/-- **`∂_z` commutes with the iterates of `∂_θ`** on the open quadrant, for data which are
`C^∞` there.  Iterated Clairaut: the induction step moves `∂_z` across the outermost
`∂_θ`, and the inner derivative is identified by locality of `∂_θ` on the open quadrant
(`Work.Spaces.pth_congr_of_isOpen`). -/
theorem pz_pthIter_comm_open (f : ℝ → ℝ → ℝ) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (n : ℕ) : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pz (Work.Spaces.pthIter n f) z θ
        = Work.Spaces.pthIter n (Work.Spaces.pz f) z θ := by
  induction n with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h1, h2⟩
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pthIter n f)) (z, θ) :=
        ((SmoothOpen_pthIter_local hf n).contDiffAt
          (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).of_le (by norm_num)
      rw [Work.Spaces.pthIter_succ, Work.Spaces.pz_pth_comm hcd, Work.Spaces.pthIter_succ]
      exact Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
        (fun p hp => by
          obtain ⟨hz', h1', h2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
          exact ih p.1 p.2 hz' h1' h2') hmem

theorem Dz_slice_identities (Ψ : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
    ∧ (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ
        = Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) := by
  have hf : ∀ n : ℕ, ContDiffOn ℝ (↑n) (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hsm
  constructor
  · -- `z²∂_z²` commutes with `D_z = z∂_z`: the instance `m = 1`, `i = 0` of
    -- `zsq_pzIter2_mixed_open`.
    intro z θ hz h1 h2
    have h := Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open Ψ hf 1 0 hz ⟨h1, h2⟩
    simp only [Work.Spaces.mixed_zero_right] at h
    exact h.symm
  · -- `∂_z` commutes with `∂_θ²`, and `z` is constant in `θ`.
    intro z θ hz h1 h2
    have hA := pz_pthIter_comm_open Ψ hsm 2 z θ hz h1 h2
    have hB := congrFun (congrFun (pthIter_mul_fst (Work.Spaces.pz Ψ) 2) z) θ
    show z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (fun z θ => z * Work.Spaces.pz Ψ z θ) z θ
    rw [hA]
    exact hB.symm

end Work.FTS.EllipticEst.remov
