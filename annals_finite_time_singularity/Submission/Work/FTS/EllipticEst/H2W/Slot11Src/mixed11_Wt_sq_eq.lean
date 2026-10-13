import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Slot11Src

/-- The first mixed derivative `D_z¹D_θ¹f = D_z(D_θf)` equals `sin(2θ)·∂_θ(D_z f)` on the open
quadrant.  This is the `j = 1` case of the Clairaut identity
`∂_θ(D_z^j f) = D_z^j(∂_θ f)` (`Work.EllipticEst.H2W.pth_DzIter_eqOn_Q0`), transported through
the definition of `D_z`: `D_z(D_θ f) = D_z(sin(2θ)·∂_θf) = sin(2θ)·D_z(∂_θf)` because the
factor `sin(2θ)` does not depend on `z`. -/
lemma mixed_one_one_eq_sin_mul_pth {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.mixed 1 1 f z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ := by
  have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have heq : Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ
      = Work.Spaces.Dz (Work.Spaces.pth f) z θ := by
    have h := Work.EllipticEst.H2W.pth_DzIter_eqOn_Q0 hf 1 hQ
    simpa [Function.uncurry] using h
  rw [heq]
  show Work.Spaces.Dz (Work.Spaces.Dth f) z θ
      = Real.sin (2 * θ) * Work.Spaces.Dz (Work.Spaces.pth f) z θ
  show z * deriv (fun z' => Work.Spaces.Dth f z' θ) z
      = Real.sin (2 * θ) * (z * deriv (fun z' => Work.Spaces.pth f z' θ) z)
  rw [show (fun z' : ℝ => Work.Spaces.Dth f z' θ)
        = (fun z' : ℝ => Real.sin (2 * θ) * Work.Spaces.pth f z' θ) from rfl,
      deriv_const_mul_field]
  ring

/-- Pure monomial algebra of the `γ`-weight: for `s > 0` and real `γ`,
`(s·A·(w·s^{-γ/2}))² = w²·A²·s^{2-γ}`.  This is the pointwise content of the identity
`(D_zD_θf · W)² = w²·(∂_θD_zf)²·sin(2θ)^{2-γ}`, the two `rpow` exponents `-γ/2` (from the
angular weight `w_θ = sin(2θ)^{-γ/2}`) combining to `-γ`, and the two powers of `sin(2θ)`
combining to `2 - γ`. -/
lemma mul_Wt_sq_key {s A w γ : ℝ} (hs : 0 < s) :
    (s * A * (w * s ^ (-(γ / 2)))) ^ 2 = w ^ 2 * A ^ 2 * s ^ (2 - γ) := by
  have harith1 : -(γ / 2) + -(γ / 2) = -γ := by ring
  have h1 : (s ^ (-(γ / 2))) ^ 2 = s ^ (-γ) := by
    have h : s ^ (-(γ / 2)) * s ^ (-(γ / 2)) = s ^ (-(γ / 2) + -(γ / 2)) :=
      (Real.rpow_add hs _ _).symm
    rw [pow_two, h, harith1]
  have harith2 : (2 : ℝ) - γ = 1 + (1 + -γ) := by ring
  have h2 : s ^ (2 - γ) = s * s * s ^ (-γ) := by
    rw [harith2, Real.rpow_add hs 1 (1 + -γ), Real.rpow_add hs 1 (-γ), Real.rpow_one]
    ring
  have hL : (s * A * (w * s ^ (-(γ / 2)))) ^ 2 = s ^ 2 * A ^ 2 * w ^ 2 * (s ^ (-(γ / 2))) ^ 2 :=
    by ring
  rw [hL, h1, h2]
  ring

theorem mixed11_Wt_sq_eq {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed 1 1 f z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * (Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α) := by
  intro z θ hz hθ0 hθ1
  have hs : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith [Real.pi_pos]
  have hmix := mixed_one_one_eq_sin_mul_pth hf hz hθ0 hθ1
  rw [hmix, Work.Spaces.Wt, Work.Spaces.wTheta]
  exact mul_Wt_sq_key (s := Real.sin (2 * θ))
    (A := Work.Spaces.pth (Work.Spaces.DzIter 1 f) z θ) (w := Work.Spaces.w z)
    (γ := Work.Spaces.gam α) hs

end Work.FTS.EllipticEst.H2W.Slot11Src
