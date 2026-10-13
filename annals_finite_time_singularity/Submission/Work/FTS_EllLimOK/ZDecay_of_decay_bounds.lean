/-
Copyright: work module for the Elgindi finite-time singularity project.

# `ZDecay` from the uniform bounds on the jet components `F j i`

The boundary decay `Work.FTS.EllipticEst.ZDecay Ψ` is the statement that at every angle
`θ ∈ Iθ = [0, π/2]` the *plain* jet

`z ^ 2 * (Ψ ^ 2 + (∂_zΨ) ^ 2 + (∂_z²Ψ) ^ 2 + (∂_θΨ) ^ 2 + (∂_θ²Ψ) ^ 2)`

tends to `0` as `z → +∞`.  The elliptic estimates of the chapter produce the limit `Ψ` only
together with the *bounds*

`(1+z)^{3/2} * |F j i z θ| ≤ C`   (`j + i ≤ 2`)

on the components of its jet (`Ψ = F 0 0`, `∂_zΨ = F 1 0 / z`, `∂_z²Ψ = (F 2 0 - F 1 0)/z²`,
`∂_θΨ = F 0 1 / sin 2θ`, `∂_θ²Ψ = (F 0 2 - 2cos2θ·F 0 1)/sin²2θ` on the open quadrant `Q0`), and
`0` at every angle outside the open strip `(0, π/2)`; this module derives `ZDecay` from exactly
that data.

The proof is pointwise.  In the interior `θ ∈ (0, π/2)` the factor `sin 2θ > 0` is a constant and
every one of the five slots is of the form `a(z)` with `|a(z)| ≤ D/(1+z)^{3/2}`; the elementary
bound `z^2 a(z)^2 ≤ D^2/(1+z)` (`Work.FTS.EllLimOK.zsq_mul_sq_le_inv_of_abs_le`) then gives a
squeeze `|·| ≤ D₀/(1+z)`, whence the limit `0`.  At the two endpoints `θ = 0, π/2` the whole
slice vanishes by hypothesis, so every one of the five terms is `0` (the two `θ`-derivatives
because the slice vanishes on one full side of the endpoint — `deriv` is the two-sided derivative
or the junk value `0`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_EllLimOK.DecayAux
import Submission.Work.FTS_EllLimOK.ZDecayAux
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

/-! ## The interior of the quadrant: the squeeze -/

/-- **The interior part of the decay estimate.**  For an angle `θ` strictly inside `(0, π/2)`,
the `z ^ 2`-weighted jet built out of the five `F`-slots decays like `1/z`, hence tends to `0`.

The bound `hdec` is the only input; the constants `sin 2θ` are absorbed into the (finite) limit
constant, and every slot loses the extra `z ^ 2` because the decay hypothesis carries the exponent
`3/2`. -/
private theorem tendsto_interior {θ C : ℝ} (hC : 0 ≤ C) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hdec : ∀ (j i : ℕ), j + i ≤ 2 → ∀ z : ℝ, 0 < z →
      (1 + z) ^ ((3 : ℝ) / 2) * |F j i z θ| ≤ C) :
    Tendsto (fun z : ℝ => z ^ 2 * ((F 0 0 z θ) ^ 2 + (F 1 0 z θ / z) ^ 2
      + ((F 2 0 z θ - F 1 0 z θ) / z ^ 2) ^ 2 + (F 0 1 z θ / Real.sin (2 * θ)) ^ 2
      + ((F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2) ^ 2))
      atTop (𝓝 0) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hD : 0 ≤ C ^ 2 + C ^ 2 + (2 * C) ^ 2 + (C / Real.sin (2 * θ)) ^ 2
      + (3 * C / (Real.sin (2 * θ)) ^ 2) ^ 2 := by positivity
  have key : ∀ z : ℝ, 1 ≤ z →
      z ^ 2 * ((F 0 0 z θ) ^ 2 + (F 1 0 z θ / z) ^ 2
        + ((F 2 0 z θ - F 1 0 z θ) / z ^ 2) ^ 2 + (F 0 1 z θ / Real.sin (2 * θ)) ^ 2
        + ((F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2) ^ 2)
      ≤ (C ^ 2 + C ^ 2 + (2 * C) ^ 2 + (C / Real.sin (2 * θ)) ^ 2
        + (3 * C / (Real.sin (2 * θ)) ^ 2) ^ 2) / (1 + z) := by
    intro z hz
    have hzpos : 0 < z := by linarith
    have hxpos : 0 < 1 + z := by linarith
    have h00 : |F 0 0 z θ| ≤ C / (1 + z) ^ ((3 : ℝ) / 2) :=
      abs_le_div_rpow32_of_mul_le hzpos (hdec 0 0 (by norm_num) z hzpos)
    have h10 : |F 1 0 z θ| ≤ C / (1 + z) ^ ((3 : ℝ) / 2) :=
      abs_le_div_rpow32_of_mul_le hzpos (hdec 1 0 (by norm_num) z hzpos)
    have h20 : |F 2 0 z θ| ≤ C / (1 + z) ^ ((3 : ℝ) / 2) :=
      abs_le_div_rpow32_of_mul_le hzpos (hdec 2 0 (by norm_num) z hzpos)
    have h01 : |F 0 1 z θ| ≤ C / (1 + z) ^ ((3 : ℝ) / 2) :=
      abs_le_div_rpow32_of_mul_le hzpos (hdec 0 1 (by norm_num) z hzpos)
    have h02 : |F 0 2 z θ| ≤ C / (1 + z) ^ ((3 : ℝ) / 2) :=
      abs_le_div_rpow32_of_mul_le hzpos (hdec 0 2 (by norm_num) z hzpos)
    -- slot `(0,0)`
    have s0 : z ^ 2 * (F 0 0 z θ) ^ 2 ≤ C ^ 2 / (1 + z) :=
      zsq_mul_sq_le_inv_of_abs_le hC hz h00
    -- slot `(1,0)`: the factor `1/z` is a gain
    have h10' : |F 1 0 z θ / z| ≤ C / (1 + z) ^ ((3 : ℝ) / 2) := by
      rw [abs_div, abs_of_pos hzpos]
      calc |F 1 0 z θ| / z ≤ |F 1 0 z θ| := div_le_self (abs_nonneg _) hz
        _ ≤ C / (1 + z) ^ ((3 : ℝ) / 2) := h10
    have s1 : z ^ 2 * (F 1 0 z θ / z) ^ 2 ≤ C ^ 2 / (1 + z) :=
      zsq_mul_sq_le_inv_of_abs_le hC hz h10'
    -- slot `(2,0)`: the factor `1/z ^ 2` absorbs the difference
    have h20' : |(F 2 0 z θ - F 1 0 z θ) / z ^ 2| ≤ 2 * C / (1 + z) ^ ((3 : ℝ) / 2) := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < z ^ 2)]
      have htri : |F 2 0 z θ - F 1 0 z θ| ≤ |F 2 0 z θ| + |F 1 0 z θ| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (F 2 0 z θ) (-(F 1 0 z θ))
      have hdiv : |F 2 0 z θ - F 1 0 z θ| / z ^ 2 ≤ |F 2 0 z θ| + |F 1 0 z θ| :=
        le_trans (div_le_self (abs_nonneg _) (by nlinarith [hz])) htri
      have hsum : |F 2 0 z θ| + |F 1 0 z θ| ≤ 2 * C / (1 + z) ^ ((3 : ℝ) / 2) := by
        have hsplit : 2 * C / (1 + z) ^ ((3 : ℝ) / 2)
            = C / (1 + z) ^ ((3 : ℝ) / 2) + C / (1 + z) ^ ((3 : ℝ) / 2) := by ring
        linarith [h20, h10, hsplit]
      linarith
    have s2 : z ^ 2 * ((F 2 0 z θ - F 1 0 z θ) / z ^ 2) ^ 2 ≤ (2 * C) ^ 2 / (1 + z) :=
      zsq_mul_sq_le_inv_of_abs_le (by positivity) hz h20'
    -- slot `(0,1)`: `sin 2θ > 0` is a constant
    have h01' : |F 0 1 z θ / Real.sin (2 * θ)|
        ≤ (C / Real.sin (2 * θ)) / (1 + z) ^ ((3 : ℝ) / 2) := by
      rw [abs_div, abs_of_pos hs, div_eq_mul_inv, div_eq_mul_inv]
      calc |F 0 1 z θ| * (Real.sin (2 * θ))⁻¹
          ≤ (C / (1 + z) ^ ((3 : ℝ) / 2)) * (Real.sin (2 * θ))⁻¹ :=
            mul_le_mul_of_nonneg_right h01 (by positivity)
        _ = (C * (Real.sin (2 * θ))⁻¹) * ((1 + z) ^ ((3 : ℝ) / 2))⁻¹ := by ring
    have s3 : z ^ 2 * (F 0 1 z θ / Real.sin (2 * θ)) ^ 2
        ≤ (C / Real.sin (2 * θ)) ^ 2 / (1 + z) :=
      zsq_mul_sq_le_inv_of_abs_le (by positivity) hz h01'
    -- slot `(0,2)`: the angular weight `sin 2θ) ^ 2` is a constant, `|cos 2θ| ≤ 1`
    have h02c : |2 * Real.cos (2 * θ)| ≤ 2 := by
      have hc : |Real.cos (2 * θ)| ≤ 1 :=
        abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
      calc |2 * Real.cos (2 * θ)| = 2 * |Real.cos (2 * θ)| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ 2 * 1 := by linarith
        _ = 2 := by norm_num
    have h02' : |(F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2|
        ≤ (3 * C / (Real.sin (2 * θ)) ^ 2) / (1 + z) ^ ((3 : ℝ) / 2) := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (Real.sin (2 * θ)) ^ 2),
        div_eq_mul_inv, div_eq_mul_inv]
      have htri : |F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ|
          ≤ |F 0 2 z θ| + |2 * Real.cos (2 * θ)| * |F 0 1 z θ| := by
        calc |F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ|
            ≤ |F 0 2 z θ| + |2 * Real.cos (2 * θ) * F 0 1 z θ| := by
              simpa [sub_eq_add_neg, abs_neg] using
                abs_add_le (F 0 2 z θ) (-(2 * Real.cos (2 * θ) * F 0 1 z θ))
          _ = |F 0 2 z θ| + |2 * Real.cos (2 * θ)| * |F 0 1 z θ| := by rw [abs_mul]
      have hnum : |F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ|
          ≤ 3 * C / (1 + z) ^ ((3 : ℝ) / 2) := by
        have hprod : |2 * Real.cos (2 * θ)| * |F 0 1 z θ|
            ≤ 2 * (C / (1 + z) ^ ((3 : ℝ) / 2)) :=
          mul_le_mul h02c h01 (abs_nonneg _) (by norm_num)
        have hsplit : 3 * C / (1 + z) ^ ((3 : ℝ) / 2)
            = C / (1 + z) ^ ((3 : ℝ) / 2) + 2 * (C / (1 + z) ^ ((3 : ℝ) / 2)) := by ring
        linarith [htri, hprod, hsplit]
      calc |F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ| * ((Real.sin (2 * θ)) ^ 2)⁻¹
          ≤ (3 * C / (1 + z) ^ ((3 : ℝ) / 2)) * ((Real.sin (2 * θ)) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hnum (by positivity)
        _ = (3 * C * ((Real.sin (2 * θ)) ^ 2)⁻¹) * ((1 + z) ^ ((3 : ℝ) / 2))⁻¹ := by ring
    have s4 : z ^ 2 * ((F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2) ^ 2
        ≤ (3 * C / (Real.sin (2 * θ)) ^ 2) ^ 2 / (1 + z) :=
      zsq_mul_sq_le_inv_of_abs_le (by positivity) hz h02'
    -- collect the five slots
    have hsum : (C ^ 2 + C ^ 2 + (2 * C) ^ 2 + (C / Real.sin (2 * θ)) ^ 2
        + (3 * C / (Real.sin (2 * θ)) ^ 2) ^ 2) / (1 + z)
        = C ^ 2 / (1 + z) + C ^ 2 / (1 + z) + (2 * C) ^ 2 / (1 + z)
          + (C / Real.sin (2 * θ)) ^ 2 / (1 + z)
          + (3 * C / (Real.sin (2 * θ)) ^ 2) ^ 2 / (1 + z) := by ring
    rw [mul_add, mul_add, mul_add, mul_add, hsum]
    linarith [s0, s1, s2, s3, s4]
  refine tendsto_zero_of_abs_le_inv hD ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
  rw [abs_of_nonneg (by positivity)]
  exact key z hz

/-! ## The main statement -/

theorem ZDecay_of_decay_bounds {Ψ : ℝ → ℝ → ℝ} {F : ℕ → ℕ → ℝ → ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hΨ : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → Ψ z θ = F 0 0 z θ)
    (hid : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz Ψ z θ = F 1 0 z θ / z ∧
      Work.Spaces.pth Ψ z θ = F 0 1 z θ / Real.sin (2 * θ) ∧
      Work.Spaces.pzIter 2 Ψ z θ = (F 2 0 z θ - F 1 0 z θ) / z ^ 2 ∧
      Work.Spaces.pthIter 2 Ψ z θ
        = (F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2)
    (hvan : ∀ z θ : ℝ, θ ∉ Set.Ioo (0 : ℝ) (π / 2) → Ψ z θ = 0)
    (hdec : ∀ (j i : ℕ), j + i ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      (1 + z) ^ ((3 : ℝ) / 2) * |F j i z θ| ≤ C) :
    Work.FTS.EllipticEst.ZDecay Ψ := by
  intro θ hθ
  by_cases hint : θ ∈ Set.Ioo (0 : ℝ) (π / 2)
  · -- interior: substitute the `F`-slots and use the squeeze
    have hmain : Tendsto (fun z : ℝ => z ^ 2 * ((F 0 0 z θ) ^ 2 + (F 1 0 z θ / z) ^ 2
        + ((F 2 0 z θ - F 1 0 z θ) / z ^ 2) ^ 2 + (F 0 1 z θ / Real.sin (2 * θ)) ^ 2
        + ((F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2) ^ 2))
        atTop (𝓝 0) :=
      tendsto_interior hC hint (fun j i hji z hz => hdec j i hji z θ ⟨hz, hint⟩)
    refine Filter.Tendsto.congr' ?_ hmain
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    obtain ⟨h1, h2, h3, h4⟩ := hid z θ ⟨hz, hint⟩
    rw [hΨ z θ ⟨hz, hint⟩, h1, h2, h3, h4]
  · -- endpoint: the whole slice vanishes, so the function is identically zero
    have hcases : θ = 0 ∨ θ = π / 2 := by
      rcases lt_or_eq_of_le hθ.1 with hlt | heq
      · right
        exact le_antisymm hθ.2 (le_of_not_gt fun hlt2 => hint ⟨hlt, hlt2⟩)
      · exact Or.inl heq.symm
    have hzero : (fun z : ℝ => z ^ 2 * ((Ψ z θ) ^ 2 + (Work.Spaces.pz Ψ z θ) ^ 2
        + (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 + (Work.Spaces.pth Ψ z θ) ^ 2
        + (Work.Spaces.pthIter 2 Ψ z θ) ^ 2)) = fun _ : ℝ => (0 : ℝ) := by
      funext z
      have h0 : Ψ z θ = 0 := hvan z θ hint
      have h1 : Work.Spaces.pz Ψ z θ = 0 :=
        pz_eq_zero_of_forall fun z' => hvan z' θ hint
      have h2 : Work.Spaces.pzIter 2 Ψ z θ = 0 :=
        pzIter_two_eq_zero_of_forall fun z' => hvan z' θ hint
      have h3 : Work.Spaces.pth Ψ z θ = 0 := by
        rcases hcases with h | h
        · rw [h]; exact pth_eq_zero_of_vanishing_left hvan z
        · rw [h]; exact pth_eq_zero_of_vanishing_right hvan z
      have h4 : Work.Spaces.pthIter 2 Ψ z θ = 0 := by
        rcases hcases with h | h
        · rw [h]; exact pthIter_two_eq_zero_of_vanishing_left hvan z
        · rw [h]; exact pthIter_two_eq_zero_of_vanishing_right hvan z
      rw [h0, h1, h2, h3, h4]
      ring
    rw [hzero]
    exact tendsto_const_nhds

end Work.FTS_EllLimOK
