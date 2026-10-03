/-
# Area A8 — the three-lines assembly for the linearised `V^r` bound

This module contains the Hadamard-three-lines step of area A8 (`VarBilinInterp`): given

* a bilinear operator `T` (additive/homogeneous on finitely supported inputs),
* a test object `ψ : ℤ → (ℕ →₀ ℂ)` whose pairing against `T u v (·) (x)` is pointwise dominated
  by the variational norm of the sequence `n ↦ T u v n x`,
* two *endpoint* bounds for the trilinear form `lam T ψ` at the exponent pairs
  `(p₀,q₀)`/`(p₁,q₁)` for the first two variables and `r₀`/`r₁` for the third,
* a third-slot family `analyticFamily h t₀ t₁` whose boundary seminorms are bounded by
  `W^{t₀}`, `W^{t₁}` with `(1-θ)t₀ + θt₁ = 1`,

we obtain the interpolated bound for finitely supported `f, g, h`:

`‖lam T ψ f g h‖ ≤ M₀^{1-θ}M₁^θ ‖f‖_p ‖g‖_q W`.

The analyticity/boundedness inputs of the three-lines argument are hypotheses here (they are
supplied by `Work.KMTAreas.A8.lam_family`); the boundary estimates are derived from the endpoint
bounds via the `L^p`-seminorm identities for the analytic family.  The statement is phrased with
an `ℝ≥0∞` third-slot endpoint exponent, so that it covers both the finite case (`rᵢ = qᵢ'`) and
the `L¹` endpoint (`qᵢ = 1`, where the third-slot endpoint is `⊤` with family exponent `tᵢ = 0`).
-/
import Mathlib
import Submission.Work.KMTAreas.A8Trilinear

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.InverseTheory (FinSupp)
open Work.Analysis.Interpolation

section Arith

/-- Four-factor `rpow` interpolation arithmetic: for `m₀, m₁ ≥ 0` and `x, y, z > 0`,
`(m₀ x^{α₀} y^{β₀} z^{γ₀})^{1-θ} (m₁ x^{α₁} y^{β₁} z^{γ₁})^{θ}
  = m₀^{1-θ} m₁^θ x y z`
whenever `(1-θ)α₀ + θα₁ = 1`, `(1-θ)β₀ + θβ₁ = 1`, `(1-θ)γ₀ + θγ₁ = 1`. -/
lemma rpow_interp_arith4 {m₀ m₁ x y z α₀ α₁ β₀ β₁ γ₀ γ₁ θ : ℝ} (hm₀ : 0 ≤ m₀) (hm₁ : 0 ≤ m₁)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hα : (1 - θ) * α₀ + θ * α₁ = 1) (hβ : (1 - θ) * β₀ + θ * β₁ = 1)
    (hγ : (1 - θ) * γ₀ + θ * γ₁ = 1) :
    (m₀ * x ^ α₀ * y ^ β₀ * z ^ γ₀) ^ (1 - θ) * (m₁ * x ^ α₁ * y ^ β₁ * z ^ γ₁) ^ θ
      = m₀ ^ (1 - θ) * m₁ ^ θ * x * y * z := by
  have hxp : ∀ a : ℝ, 0 < x ^ a := fun a => Real.rpow_pos_of_pos hx a
  have hyp : ∀ a : ℝ, 0 < y ^ a := fun a => Real.rpow_pos_of_pos hy a
  have hzp : ∀ a : ℝ, 0 < z ^ a := fun a => Real.rpow_pos_of_pos hz a
  have key : ∀ (m a b c d : ℝ), 0 ≤ m →
      (m * x ^ a * y ^ b * z ^ c) ^ d = m ^ d * x ^ (a * d) * y ^ (b * d) * z ^ (c * d) := by
    intro m a b c d hm
    rw [Real.mul_rpow (mul_nonneg (mul_nonneg hm (hxp a).le) (hyp b).le) (hzp c).le,
      Real.mul_rpow (mul_nonneg hm (hxp a).le) (hyp b).le,
      Real.mul_rpow hm (hxp a).le,
      ← Real.rpow_mul hx.le a d, ← Real.rpow_mul hy.le b d, ← Real.rpow_mul hz.le c d]
  have hxx : x ^ (α₀ * (1 - θ)) * x ^ (α₁ * θ) = x := by
    rw [← Real.rpow_add hx]
    have h : α₀ * (1 - θ) + α₁ * θ = 1 := by nlinarith [hα]
    rw [h, Real.rpow_one]
  have hyy : y ^ (β₀ * (1 - θ)) * y ^ (β₁ * θ) = y := by
    rw [← Real.rpow_add hy]
    have h : β₀ * (1 - θ) + β₁ * θ = 1 := by nlinarith [hβ]
    rw [h, Real.rpow_one]
  have hzz : z ^ (γ₀ * (1 - θ)) * z ^ (γ₁ * θ) = z := by
    rw [← Real.rpow_add hz]
    have h : γ₀ * (1 - θ) + γ₁ * θ = 1 := by nlinarith [hγ]
    rw [h, Real.rpow_one]
  have rearr : m₀ ^ (1 - θ) * x ^ (α₀ * (1 - θ)) * y ^ (β₀ * (1 - θ)) * z ^ (γ₀ * (1 - θ)) *
        (m₁ ^ θ * x ^ (α₁ * θ) * y ^ (β₁ * θ) * z ^ (γ₁ * θ))
      = m₀ ^ (1 - θ) * m₁ ^ θ * (x ^ (α₀ * (1 - θ)) * x ^ (α₁ * θ)) *
        (y ^ (β₀ * (1 - θ)) * y ^ (β₁ * θ)) * (z ^ (γ₀ * (1 - θ)) * z ^ (γ₁ * θ)) := by ring
  rw [key m₀ α₀ β₀ γ₀ (1 - θ) hm₀, key m₁ α₁ β₁ γ₁ θ hm₁, rearr, hxx, hyy, hzz]

/-- The `ofReal`/`toReal` conversion of a three-factor real monomial with finite factors. -/
lemma ofReal_toReal_three (m : ℝ) (hm : 0 ≤ m) (U V W : ENNReal) (hU : U < ⊤) (hV : V < ⊤)
    (hW : W < ⊤) (α β γ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    ENNReal.ofReal (m * U.toReal ^ α * V.toReal ^ β * W.toReal ^ γ)
      = ENNReal.ofReal m * U ^ α * V ^ β * W ^ γ := by
  have h1 : ENNReal.ofReal (U.toReal ^ α) = U ^ α := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hα,
      ENNReal.ofReal_toReal (ne_top_of_lt hU)]
  have h2 : ENNReal.ofReal (V.toReal ^ β) = V ^ β := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hβ,
      ENNReal.ofReal_toReal (ne_top_of_lt hV)]
  have h3 : ENNReal.ofReal (W.toReal ^ γ) = W ^ γ := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hγ,
      ENNReal.ofReal_toReal (ne_top_of_lt hW)]
  rw [show m * U.toReal ^ α * V.toReal ^ β * W.toReal ^ γ
      = m * (U.toReal ^ α * (V.toReal ^ β * W.toReal ^ γ)) by ring,
    ENNReal.ofReal_mul hm, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    h1, h2, h3]
  ring

end Arith

section Assembly

variable {T : (ℤ → ℂ) → (ℤ → ℂ) → ℕ → ℤ → ℂ}
variable {psi : ℤ → (ℕ →₀ ℂ)}

/-- **The three-lines bound for the linearised `V^r` inequality.**  See the module docstring. -/
theorem lam_three_lines (f g h : ℤ → ℂ)
    {p₀ p₁ q₀ q₁ p q : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁)
    (hp : 0 < p) (hq : 0 < q)
    {θ' : ℝ} (hθ₀ : 0 < θ') (hθ₁ : θ' < 1)
    (hpθ : 1 / p = (1 - θ') / p₀ + θ' / p₁) (hqθ : 1 / q = (1 - θ') / q₀ + θ' / q₁)
    {r₀ r₁ : ENNReal} (hr₀ : 1 ≤ r₀) (hr₁ : 1 ≤ r₁)
    {M₀ M₁ : ℝ≥0}
    {t₀ t₁ : ℝ} (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁) (ht : (1 - θ') * t₀ + θ' * t₁ = 1)
    {W : ENNReal} (hW : W < ⊤)
    (hbd₀ : ∀ z : ℂ, z.re = 0 →
      eLpNorm (analyticFamily h (t₀ : ℂ) (t₁ : ℂ) z) r₀ Measure.count ≤ W ^ t₀)
    (hbd₁ : ∀ z : ℂ, z.re = 1 →
      eLpNorm (analyticFamily h (t₀ : ℂ) (t₁ : ℂ) z) r₁ Measure.count ≤ W ^ t₁)
    (hdiff : Differentiable ℂ (fun z : ℂ => lam T psi
      (analyticFamily f ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
      (analyticFamily g ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
      (analyticFamily h (t₀ : ℂ) (t₁ : ℂ) z)))
    (hbdd : BddAbove ((norm ∘ fun z : ℂ => lam T psi
      (analyticFamily f ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
      (analyticFamily g ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
      (analyticFamily h (t₀ : ℂ) (t₁ : ℂ) z))
      '' Complex.HadamardThreeLines.verticalClosedStrip 0 1))
    (h₀ : ∀ u v w : ℤ → ℂ, ‖lam T psi u v w‖ₑ
      ≤ (M₀ : ENNReal) * eLpNorm u (ENNReal.ofReal p₀) Measure.count
        * eLpNorm v (ENNReal.ofReal q₀) Measure.count * eLpNorm w r₀ Measure.count)
    (h₁ : ∀ u v w : ℤ → ℂ, ‖lam T psi u v w‖ₑ
      ≤ (M₁ : ENNReal) * eLpNorm u (ENNReal.ofReal p₁) Measure.count
        * eLpNorm v (ENNReal.ofReal q₁) Measure.count * eLpNorm w r₁ Measure.count)
    (hU : eLpNorm f (ENNReal.ofReal p) Measure.count < ⊤)
    (hV : eLpNorm g (ENNReal.ofReal q) Measure.count < ⊤)
    (hU0 : eLpNorm f (ENNReal.ofReal p) Measure.count ≠ 0)
    (hV0 : eLpNorm g (ENNReal.ofReal q) Measure.count ≠ 0)
    (hW0 : W ≠ 0) :
    ‖lam T psi f g h‖ₑ ≤ (M₀ : ENNReal) ^ (1 - θ') * (M₁ : ENNReal) ^ θ'
      * eLpNorm f (ENNReal.ofReal p) Measure.count
      * eLpNorm g (ENNReal.ofReal q) Measure.count * W := by
  classical
  set U : ENNReal := eLpNorm f (ENNReal.ofReal p) Measure.count with hUdef
  set V : ENNReal := eLpNorm g (ENNReal.ofReal q) Measure.count with hVdef
  set F : ℂ → ℂ := fun z : ℂ => lam T psi
      (analyticFamily f ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
      (analyticFamily g ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
      (analyticFamily h (t₀ : ℂ) (t₁ : ℂ) z) with hFdef
  have hdiff' : Differentiable ℂ F := hdiff
  have hbdd' : BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := hbdd
  -- boundary estimates, in real form
  have hbou₀ : ∀ z ∈ Complex.re ⁻¹' {0},
      ‖F z‖ ≤ (M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀) * W.toReal ^ t₀ := by
    intro z hz
    have hz' : z.re = 0 := hz
    have h1 : ‖F z‖ₑ ≤ (M₀ : ENNReal) * U ^ (p / p₀) * V ^ (q / q₀) * W ^ t₀ := by
      rw [hFdef]
      refine le_trans (h₀ _ _ _) ?_
      rw [eLpNorm_analyticFamily_re_zero hp₀ hp₁ hp hz',
        eLpNorm_analyticFamily_re_zero hq₀ hq₁ hq hz', ← hUdef, ← hVdef]
      exact mul_le_mul_of_nonneg_left (hbd₀ z hz') (zero_le)
    have hconv : (M₀ : ENNReal) * U ^ (p / p₀) * V ^ (q / q₀) * W ^ t₀
        = ENNReal.ofReal ((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀)
            * W.toReal ^ t₀) :=
      (by rw [← ENNReal.ofReal_coe_nnreal,
        ofReal_toReal_three (M₀ : ℝ) (by positivity) U V W hU hV hW (p / p₀) (q / q₀) t₀
          (by positivity) (by positivity) ht₀])
    rw [hconv, ← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have hbou₁ : ∀ z ∈ Complex.re ⁻¹' {1},
      ‖F z‖ ≤ (M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁) * W.toReal ^ t₁ := by
    intro z hz
    have hz' : z.re = 1 := hz
    have h1 : ‖F z‖ₑ ≤ (M₁ : ENNReal) * U ^ (p / p₁) * V ^ (q / q₁) * W ^ t₁ := by
      rw [hFdef]
      refine le_trans (h₁ _ _ _) ?_
      rw [eLpNorm_analyticFamily_re_one hp₀ hp₁ hp hz',
        eLpNorm_analyticFamily_re_one hq₀ hq₁ hq hz', ← hUdef, ← hVdef]
      exact mul_le_mul_of_nonneg_left (hbd₁ z hz') (zero_le)
    have hconv : (M₁ : ENNReal) * U ^ (p / p₁) * V ^ (q / q₁) * W ^ t₁
        = ENNReal.ofReal ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁)
            * W.toReal ^ t₁) :=
      (by rw [← ENNReal.ofReal_coe_nnreal,
        ofReal_toReal_three (M₁ : ℝ) (by positivity) U V W hU hV hW (p / p₁) (q / q₁) t₁
          (by positivity) (by positivity) ht₁])
    rw [hconv, ← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have hhad := norm_le_interp_of_strip_edges hθ₀.le hθ₁.le hdiff' hbdd' hbou₀ hbou₁
  -- the value at `θ'`
  have hselfp : (1 - (θ' : ℂ)) * ((p / p₀ : ℝ) : ℂ) + (θ' : ℂ) * ((p / p₁ : ℝ) : ℂ) = 1 :=
    expFamily_interp_self (show p ≠ 0 by positivity) hpθ
  have hselfq : (1 - (θ' : ℂ)) * ((q / q₀ : ℝ) : ℂ) + (θ' : ℂ) * ((q / q₁ : ℝ) : ℂ) = 1 :=
    expFamily_interp_self (show q ≠ 0 by positivity) hqθ
  have hselfh : (1 - (θ' : ℂ)) * (t₀ : ℂ) + (θ' : ℂ) * (t₁ : ℂ) = 1 := by
    have hh := congrArg (fun r : ℝ => (r : ℂ)) ht
    push_cast at hh
    simpa using hh
  have hFθ : F (θ' : ℂ) = lam T psi f g h := by
    rw [hFdef]
    simp only [analyticFamily_self hselfp, analyticFamily_self hselfq, analyticFamily_self hselfh]
  -- the arithmetic
  have hUpos : 0 < U.toReal := ENNReal.toReal_pos hU0 (ne_of_lt hU)
  have hVpos : 0 < V.toReal := ENNReal.toReal_pos hV0 (ne_of_lt hV)
  have hWpos : 0 < W.toReal := ENNReal.toReal_pos hW0 (ne_of_lt hW)
  have hα : (1 - θ') * (p / p₀) + θ' * (p / p₁) = 1 := interp_self (show p ≠ 0 by positivity) hpθ
  have hβ : (1 - θ') * (q / q₀) + θ' * (q / q₁) = 1 := interp_self (show q ≠ 0 by positivity) hqθ
  have harith : ((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀) * W.toReal ^ t₀) ^ (1 - θ')
      * ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁) * W.toReal ^ t₁) ^ θ'
      = (M₀ : ℝ) ^ (1 - θ') * (M₁ : ℝ) ^ θ' * U.toReal * V.toReal * W.toReal :=
    rpow_interp_arith4 (by positivity) (by positivity) hUpos hVpos hWpos hα hβ ht
  have hconv : ENNReal.ofReal ((M₀ : ℝ) ^ (1 - θ') * (M₁ : ℝ) ^ θ' * U.toReal * V.toReal
        * W.toReal)
      = (M₀ : ENNReal) ^ (1 - θ') * (M₁ : ENNReal) ^ θ' * U * V * W := by
    have h1 : ENNReal.ofReal ((M₀ : ℝ) ^ (1 - θ') * (M₁ : ℝ) ^ θ' * U.toReal * V.toReal
          * W.toReal)
        = ENNReal.ofReal ((M₀ : ℝ) ^ (1 - θ') * (M₁ : ℝ) ^ θ') * U * V * W := by
      have := ofReal_toReal_three ((M₀ : ℝ) ^ (1 - θ') * (M₁ : ℝ) ^ θ') (by positivity) U V W hU hV
        hW 1 1 1 (by norm_num) (by norm_num) (by norm_num)
      simpa using this
    have h2 : ENNReal.ofReal ((M₀ : ℝ) ^ (1 - θ') * (M₁ : ℝ) ^ θ')
        = (M₀ : ENNReal) ^ (1 - θ') * (M₁ : ENNReal) ^ θ' := by
      rw [ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_rpow_of_nonneg (show (0 : ℝ) ≤ (M₀ : ℝ) by positivity)
          (show (0 : ℝ) ≤ 1 - θ' by linarith),
        ← ENNReal.ofReal_rpow_of_nonneg (show (0 : ℝ) ≤ (M₁ : ℝ) by positivity)
          (show (0 : ℝ) ≤ θ' by linarith),
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
    rw [h1, h2]
  calc ‖lam T psi f g h‖ₑ = ENNReal.ofReal ‖F (θ' : ℂ)‖ := by rw [hFθ, ofReal_norm]
    _ ≤ ENNReal.ofReal (((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀) * W.toReal ^ t₀)
          ^ (1 - θ') * ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁)
            * W.toReal ^ t₁) ^ θ') := ENNReal.ofReal_le_ofReal hhad
    _ = ENNReal.ofReal ((M₀ : ℝ) ^ (1 - θ') * (M₁ : ℝ) ^ θ' * U.toReal * V.toReal * W.toReal) := by
        rw [harith]
    _ = (M₀ : ENNReal) ^ (1 - θ') * (M₁ : ENNReal) ^ θ' * U * V * W := hconv

end Assembly

end Work.KMTAreas
