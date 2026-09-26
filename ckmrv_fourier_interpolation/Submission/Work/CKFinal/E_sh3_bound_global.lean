import Mathlib
import Submission.Work.Asymptotics.E_TailClosed
import Submission.Work.Asymptotics.psi1_iteratedDeriv_bound
import Submission.Work.Asymptotics.highPartDefs

/-!
# The global `E_sh3` shape bound (all `x ≥ 0`, not only `x ≥ 2π`)

`Work.Asymptotics.E_sh3 B = fun x => tcF3 x * exp (-((x - 2π) B))` is the `(1,0)` corner of the
closed form of the tail: it is the *shifted* shape `tcF1` regularised by the exponential
`exp (-((x - 2π) B))`.  `E_TailClosed` proves the bound only on the region `x ≥ 2π`, where the
shifted exponential decays; on the remaining bounded window `0 ≤ x ≤ 2π` the exponential actually
*grows* like `exp (2π B)`, and the global bound therefore carries the extra factor
`Real.exp (2π B)`.

Everything reduces to the observation that the shifted exponential is a *constant* multiple of the
unshifted one:

  `exp (-((y - x₀) B)) = exp (x₀ B) · exp (-(y B))`  (`E_exp_sub_factor`).

Consequently the iterated derivative of `f y * exp (-((y - x₀) B))` is the constant
`exp (x₀ B)` times the iterated derivative of `f y * exp (-(y B))`, and the shape bound
`E_shape_bound_exp` of `E_TailClosed` applies to the latter without any hypothesis on `y`
(`E_shape_bound_exp_shift`).  For `x₀ = 2π` this is exactly the requested global bound for
`E_sh3`; the same lemma covers the `(1,1)` corner `E_sh4` with `x₀ = 2π`.

## Main results

* `Work.CKFinal.E_exp_sub_factor` — the shift factorisation of the exponential;
* `Work.CKFinal.E_shape_bound_exp_shift` — the shape bound for a shifted exponential;
* `Work.CKFinal.E_sh3_bound_global` — the requested global bound for `E_sh3`.
-/

open Work.Asymptotics

namespace Work.CKFinal

/-- The exponential factor of a shifted shape is the constant `exp (x₀ B)` times the unshifted
exponential `exp (-(y B))`.  Stated for arbitrary real `x₀`, `B`: no sign hypothesis is needed
because the factorisation is an identity. -/
lemma E_exp_sub_factor (x₀ B y : ℝ) :
    Complex.exp (-(((y - x₀ : ℝ) : ℂ) * (B : ℂ)))
      = ((Real.exp (x₀ * B) : ℝ) : ℂ) * Complex.exp (-((y : ℂ) * (B : ℂ))) := by
  rw [show (-(((y - x₀ : ℝ) : ℂ) * (B : ℂ)))
        = ((x₀ * B : ℝ) : ℂ) + (-((y : ℂ) * (B : ℂ))) from by push_cast; ring]
  rw [Complex.exp_add, Complex.ofReal_exp]

/-- **Shape bound with a shifted exponential.**  If `f` is smooth and its `m`-th iterated
derivative is at most `cf m * (1 + |x|)`, then the same holds for the shifted-regularised shape
`f y * exp (-((y - x₀) B))`, with the extra constant factor `exp (x₀ B)` (the maximal growth of the
shifted exponential relative to the unshifted one).  No hypothesis on `x₀` is needed.

This is the global form of `Work.Asymptotics.E_shape_bound_exp`, which only covers the case in
which the shifted exponential decays. -/
theorem E_shape_bound_exp_shift (f : ℝ → ℂ) (hfc : ContDiff ℝ ⊤ f) (cf : ℕ → ℝ)
    (hf : ∀ (m : ℕ) (x : ℝ), ‖iteratedDeriv m f x‖ ≤ cf m * (1 + |x|))
    (x₀ : ℝ) (B : ℝ) (hB1 : 1 ≤ B) (m : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ‖iteratedDeriv m (fun y : ℝ => f y * Complex.exp (-(((y - x₀ : ℝ) : ℂ) * (B : ℂ)))) x‖
      ≤ (∑ p ∈ Finset.range (m + 1), (m.choose p : ℝ) * cf p * B ^ (m - p))
          * Real.exp (x₀ * B) * ((1 + |x|) * Real.exp (-x)) := by
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hfun : (fun y : ℝ => f y * Complex.exp (-(((y - x₀ : ℝ) : ℂ) * (B : ℂ))))
      = fun y : ℝ => ((Real.exp (x₀ * B) : ℝ) : ℂ)
          * (f y * Complex.exp (-((y : ℂ) * (B : ℂ)))) := by
    funext y
    rw [E_exp_sub_factor x₀ B y]
    ring
  have hshape := E_shape_bound_exp f hfc cf hf B hB0 hB1 m x hx
  have hderiv : iteratedDeriv m (fun y : ℝ => f y * Complex.exp (-(((y - x₀ : ℝ) : ℂ) * (B : ℂ)))) x
      = ((Real.exp (x₀ * B) : ℝ) : ℂ)
        * iteratedDeriv m (fun y : ℝ => f y * Complex.exp (-((y : ℂ) * (B : ℂ)))) x := by
    rw [hfun, iteratedDeriv_const_mul_field]
  rw [hderiv, norm_mul]
  have hc : ‖((Real.exp (x₀ * B) : ℝ) : ℂ)‖ = Real.exp (x₀ * B) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  rw [hc]
  exact le_trans (mul_le_mul_of_nonneg_left hshape (Real.exp_nonneg _)) (le_of_eq (by ring))

/-- **Global bound for the `(1,0)` corner of the tail.**  For every `x ≥ 0` (in particular on the
bounded window `0 ≤ x ≤ 2π`, where the shifted exponential grows), the `l`-th derivative of
`E_sh3 B` is bounded by the Leibniz sum for `tcF3` — whose `p`-th derivative is at most
`2 ^ (p+1) (1 + 2π) (1 + |x|)` — multiplied by the shift factor `exp (2π B)`. -/
theorem E_sh3_bound_global (B : ℝ) (hB1 : 1 ≤ B) (l : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ‖iteratedDeriv l (Work.Asymptotics.E_sh3 B) x‖
      ≤ (∑ p ∈ Finset.range (l + 1), (l.choose p : ℝ) * (2 ^ (p + 1) * (1 + 2 * Real.pi)) * B ^ (l - p))
          * Real.exp (2 * Real.pi * B) * ((1 + |x|) * Real.exp (-x)) := by
  rw [show Work.Asymptotics.E_sh3 B
      = (fun y : ℝ => Work.Asymptotics.tcF3 y * Complex.exp (-(((y - 2 * Real.pi : ℝ) : ℂ) * (B : ℂ))))
      from rfl]
  exact E_shape_bound_exp_shift tcF3 contDiff_tcF3 (fun p => 2 ^ (p + 1) * (1 + 2 * Real.pi))
      (fun m y => E_tcF3_bound m y) (2 * Real.pi) B hB1 l x hx

end Work.CKFinal
