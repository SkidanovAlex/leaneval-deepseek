import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `H^k`-integrand vanishes at the two angular endpoints

`HkIntegrand α n u z θ` is a sum of squares of weighted derivatives of `u`.
Every summand carries a factor that vanishes when `sin (2θ) = 0`:

* the first sum carries `1 / sin(2θ)^{η/2}`, hence is `0` at a zero of `sin(2θ)`
  (the positive power `0^{η/2}` is `0`, and `x / 0 = 0` in `ℝ`);
* in the second sum the only non-trivial summands have `1 ≤ i`, so they involve
  `mixed j i u = D_z^j D_θ^i u`; the outermost operation `D_θ` carries a factor
  `sin (2θ)`, and any `D_z`-iterate of a function vanishing on the line
  `{θ = θ₀}` still vanishes there.

Consequently the integrand is `0` at `θ = 0` and at `θ = π/2` for **every**
`α`, `n`, `u` and `z` (in particular without any regularity assumption on `u`).
This is the endpoint boundary condition needed so that integrating
`HkIntegrand` over `[0, π/2]` sees no contribution from the angular boundary.
-/

noncomputable section

open Work.Spaces

namespace Work.Coercivity

/-- At an angle where `sin (2θ) = 0`, every `D_θ`-iterate `D_θ^i u` with `i ≥ 1`
vanishes: the outermost `D_θ` is `sin (2θ) · ∂_θ`. -/
lemma DthIter_eq_zero_of_sin_eq_zero (u : ℝ → ℝ → ℝ) (i : ℕ) (hi : 1 ≤ i) (θ : ℝ)
    (h : Real.sin (2 * θ) = 0) (z : ℝ) : Work.Spaces.DthIter i u z θ = 0 := by
  cases i with
  | zero => omega
  | succ m => simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, h, zero_mul]

/-- If `g (·) θ` vanishes identically, then so does every `D_z`-iterate
`D_z^j g (·) θ`: `D_z = z ∂_z` is a derivation, and the derivative of the zero
function is zero. -/
lemma DzIter_eq_zero_of_forall_eq_zero (g : ℝ → ℝ → ℝ) (θ : ℝ) (hg : ∀ z, g z θ = 0)
    (j : ℕ) (z : ℝ) : Work.Spaces.DzIter j g z θ = 0 := by
  induction j generalizing z with
  | zero => simpa using hg z
  | succ m ih =>
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    have hfun : (fun z' => Work.Spaces.DzIter m g z' θ) = fun _ => (0 : ℝ) :=
      funext fun z' => ih z'
    simp only [Work.Spaces.pz, hfun, deriv_const, mul_zero]

/-- At an angle where `sin (2θ) = 0`, every mixed derivative `mixed j i u` with
`i ≥ 1` vanishes.  This is the summand of the second sum of `HkIntegrand`. -/
lemma mixed_eq_zero_of_sin_eq_zero (u : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) (θ : ℝ)
    (h : Real.sin (2 * θ) = 0) (z : ℝ) : Work.Spaces.mixed j i u z θ = 0 := by
  rw [Work.Spaces.mixed]
  exact DzIter_eq_zero_of_forall_eq_zero (Work.Spaces.DthIter i u) θ
    (fun z' => DthIter_eq_zero_of_sin_eq_zero u i hi θ h z') j z

/-- The `H^k`-integrand vanishes at any angle `θ` with `sin (2θ) = 0`. -/
lemma HkIntegrand_eq_zero_of_sin_eq_zero (α : ℝ) (n : ℕ) (u : ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α n u z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hden : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [h, Real.zero_rpow (by norm_num [Work.Spaces.eta]), div_zero]
  rw [Finset.sum_eq_zero (fun i _ => by rw [hden, mul_zero, sq, mul_zero]),
      Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_)), add_zero]
  split_ifs with hc
  · rw [mixed_eq_zero_of_sin_eq_zero u j i hc.1 θ h z, zero_mul, sq, mul_zero]
  · rfl

theorem HkIntegrand_endpoint_zero (α : ℝ) (n : ℕ) (u : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α n u z 0 = 0
      ∧ Work.Spaces.HkIntegrand α n u z (Real.pi / 2) = 0 := by
  have h0 : Real.sin (2 * 0) = 0 := by norm_num
  have hpi : Real.sin (2 * (Real.pi / 2)) = 0 := by
    rw [show 2 * (Real.pi / 2) = Real.pi by ring]; exact Real.sin_pi
  exact ⟨HkIntegrand_eq_zero_of_sin_eq_zero α n u z 0 h0,
    HkIntegrand_eq_zero_of_sin_eq_zero α n u z (Real.pi / 2) hpi⟩

end Work.Coercivity
