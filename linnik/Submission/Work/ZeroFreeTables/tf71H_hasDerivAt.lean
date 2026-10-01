import Mathlib
import Submission.Work.ZeroFreeTables.tf71H_defs

noncomputable section
open scoped Real
namespace Work.ZeroFreeTables

/-- The elementary calculus fact underlying `tf71H_hasDerivAt`: for constants
`a b e c d f` with `d ≠ 0`, the function displayed is an antiderivative of the
displayed `tf71cf`-shaped closed form. -/
lemma tf71H_hasDerivAt_gen (a b e c d f : ℝ) (hd : d ≠ 0) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => a * ( b * ((c - y/2) * Real.sin (d*y)/d - Real.cos (d*y)/(2*d^2))
          + e * (2*c*y - y^2/2)
          + Real.cos (2*f - d*y)/(d * Real.sin (2*f))
          - 2*y
          - 2*Real.cos (f - d*y)/(d * Real.sin f)))
      (a * ( b*(c - x/2)*Real.cos (d*x) + e*(2*c - x)
          + Real.sin (2*f - d*x)/Real.sin (2*f)
          - 2*(1 + Real.sin (f - d*x)/Real.sin f))) x := by
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (d*y)) (Real.cos (d*x) * d) x :=
    (hasDerivAt_const_mul (x := x) d).sin
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (d*y)) (-Real.sin (d*x) * d) x :=
    (hasDerivAt_const_mul (x := x) d).cos
  -- first piece
  have hP1 : HasDerivAt
      (fun y : ℝ => (c - y/2) * Real.sin (d*y)/d - Real.cos (d*y)/(2*d^2))
      ((c - x/2) * Real.cos (d*x)) x := by
    have hlin : HasDerivAt (fun y : ℝ => c - y/2) (-(1/2)) x :=
      ((hasDerivAt_id x).div_const 2).const_sub c
    have hmul : HasDerivAt (fun y : ℝ => (c - y/2) * Real.sin (d*y))
        ((-(1/2)) * Real.sin (d*x) + (c - x/2) * (Real.cos (d*x) * d)) x := hlin.mul hsin
    have h1raw : HasDerivAt (fun y : ℝ => (c - y/2) * Real.sin (d*y) / d)
        (((-(1/2)) * Real.sin (d*x) + (c - x/2) * (Real.cos (d*x) * d)) / d) x :=
      hmul.div_const d
    have h2raw : HasDerivAt (fun y : ℝ => Real.cos (d*y) / (2*d^2))
        ((-Real.sin (d*x) * d) / (2*d^2)) x := hcos.div_const (2*d^2)
    refine (h1raw.sub h2raw).congr_deriv ?_
    field_simp
    ring
  -- the `lam (2 gamma x - x^2/2)` piece
  have hP3 : HasDerivAt (fun y : ℝ => 2*c*y - y^2/2) (2*c - x) x := by
    have h1 : HasDerivAt (fun y : ℝ => (2*c)*y) (2*c) x := hasDerivAt_const_mul (x := x) (2*c)
    have h2 : HasDerivAt (fun y : ℝ => y^2/2) (x) x := by
      have hh : HasDerivAt (fun y : ℝ => y^2) (((2:ℕ):ℝ) * x^(2-1)) x := hasDerivAt_pow 2 x
      refine (hh.div_const (2:ℝ)).congr_deriv ?_
      rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]
      norm_num
    refine (h1.sub h2).congr_deriv ?_
    ring
  -- the `cos (2θ - ζx)/(ζ sin 2θ)` piece
  have hP4 : HasDerivAt (fun y : ℝ => Real.cos (2*f - d*y)/(d * Real.sin (2*f)))
      (Real.sin (2*f - d*x)/Real.sin (2*f)) x := by
    have h2t : HasDerivAt (fun y : ℝ => 2*f - d*y) (-d) x :=
      (hasDerivAt_const_mul (x := x) d).const_sub (2*f)
    refine (h2t.cos.div_const (d * Real.sin (2*f))).congr_deriv ?_
    rw [neg_mul_neg, mul_comm (Real.sin (2*f - d*x)) d, mul_div_mul_left _ _ hd]
  -- the `-2 cos (θ - ζx)/(ζ sin θ)` piece, with the factor `2` kept in the numerator
  have hP6 : HasDerivAt (fun y : ℝ => (2*Real.cos (f - d*y))/(d * Real.sin f))
      (2*(Real.sin (f - d*x)/Real.sin f)) x := by
    have h2t : HasDerivAt (fun y : ℝ => f - d*y) (-d) x :=
      (hasDerivAt_const_mul (x := x) d).const_sub f
    have h2c : HasDerivAt (fun y : ℝ => 2*Real.cos (f - d*y))
        (2 * (-Real.sin (f - d*x) * (-d))) x := h2t.cos.const_mul 2
    refine (h2c.div_const (d * Real.sin f)).congr_deriv ?_
    rw [neg_mul_neg, mul_div_assoc, mul_comm (Real.sin (f - d*x)) d, mul_div_mul_left _ _ hd]
  have hP5 : HasDerivAt (fun y : ℝ => 2*y) (2:ℝ) x := hasDerivAt_const_mul (x := x) (2:ℝ)
  -- combine the five pieces
  have hJ : HasDerivAt
      (fun y : ℝ => b * ((c - y/2) * Real.sin (d*y)/d - Real.cos (d*y)/(2*d^2))
          + e * (2*c*y - y^2/2)
          + Real.cos (2*f - d*y)/(d * Real.sin (2*f))
          - 2*y
          - 2*Real.cos (f - d*y)/(d * Real.sin f))
      (b * ((c - x/2) * Real.cos (d*x)) + e * (2*c - x)
          + Real.sin (2*f - d*x)/Real.sin (2*f)
          - 2 - 2 * (Real.sin (f - d*x)/Real.sin f)) x :=
    ((((hP1.const_mul b).add (hP3.const_mul e)).add hP4).sub hP5).sub hP6
  refine (hJ.const_mul a).congr_deriv ?_
  ring

theorem tf71H_hasDerivAt (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    ∀ x : ℝ, HasDerivAt (Work.ZeroFreeTables.tf71H θ lam) (Work.ZeroFreeTables.tf71cf θ lam x) x := by
  intro x
  have hd : tf71ζ θ lam ≠ 0 := ne_of_gt (tf71ζ_pos hθ0 hθ1 hlam)
  exact tf71H_hasDerivAt_gen (lam * (1 + Real.tan θ ^ 2)) (lam * (1 + Real.tan θ ^ 2))
    lam (tf71γ θ lam) (tf71ζ θ lam) θ hd x

end Work.ZeroFreeTables
