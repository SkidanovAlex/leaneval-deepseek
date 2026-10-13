/-
# `primBoundLeft` — the growth rate of `Γ(θ)/sin(2θ)` at `θ = 0⁺`

The angular factor of the route is `Γ(θ) = (sinθ·cos²θ)^α`
(`Work.FTS.Regularity.Gamma α θ = Work.ConstructionInstance.Gamma α θ`).  The density of the
angular measure is `Γ(θ)/sin(2θ)`, which blows up at both endpoints of `Iθ = [0,π/2]`; the two
`R4b` lemmas record the exact rate of that blow-up.  This file is the **left** half:

  `Γ(θ)/sin(2θ) ≤ M · θ^{α-1}`  on `(0, π/4]`,

i.e. the density grows at most like `θ^{α-1}` at `0⁺` (so that its primitive grows like `θ^α`,
which is what turns the class bound `|D_θg| ≤ Cθ·z²·Γ` into the `θ^α`-Hölder modulus of `g`).
The right half, `Γ(θ)/sin(2θ) ≤ N·(π/2-θ)^{2α-1}` near `π/2`, is `R4b/primBoundRight.lean`.

## The computation

For `t ∈ (0, π/4]` both `sin t` and `cos t` are positive and
`sin(2t) = 2 sin t cos t`, so with `σ = sin t / t` and `c = cos t`,

  `Γ(α,t)/sin(2t) = (sin t·cos²t)^α / (2 sin t cos t)
                  = (1/2)·(sin t)^{α-1}·(cos t)^{2α-1}
                  = (1/2)·σ^{α-1}·c^{2α-1}·t^{α-1}`.

It therefore suffices to bound the two dimensionless factors uniformly on `(0, π/4]`:

* `σ ∈ [2/π, 1]` by Jordan's inequality (`Real.mul_le_sin`) and `Real.sin_le`; hence
  `σ^{α-1} = σ^α/σ ≤ 1/(2/π) = π/2` (using `σ^α ≤ 1`, which is `Real.rpow_le_one`).
  Note how the two ends of the range of `σ` are used in the two different directions — no case
  distinction on `α` is needed.
* `c ∈ [√2/2, 1]`; hence `c^{2α-1} = c^{2α}/c ≤ 1/c ≤ 2`.

Thus `Γ(α,t)/sin(2t) ≤ (1/2)·(π/2)·2·t^{α-1} = (π/2)·t^{α-1}`: one may take `M = π/2`, a
constant that is even independent of `α` (only the exponent on `t` depends on `α`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS.Regularity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R4b

theorem primBoundLeft {α : ℝ} (hα : 0 < α) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 < t → t ≤ Real.pi / 4 →
      Work.FTS.Regularity.Gamma α t / Real.sin (2 * t) ≤ M * t ^ (α - 1) := by
  refine ⟨Real.pi / 2, by positivity, ?_⟩
  intro t ht htle
  -- basic sign and range facts on `(0, π/4]`
  have htpi : t < Real.pi := by linarith [Real.pi_pos]
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht htpi
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  -- the closed form of the density: `Γ(α,t)/sin(2t) = (1/2)·(sin t)^{α-1}·(cos t)^{2α-1}`
  have hc2 : (Real.cos t ^ 2) ^ α = Real.cos t ^ (2 * α) := by
    rw [← Real.rpow_natCast (Real.cos t) 2, ← Real.rpow_mul hc.le]
    norm_num
  have hnum : (Real.sin t * Real.cos t ^ 2) ^ α = Real.sin t ^ α * Real.cos t ^ (2 * α) := by
    rw [Real.mul_rpow hs.le (pow_nonneg hc.le 2), hc2]
  have hmain : (Real.sin t * Real.cos t ^ 2) ^ α / Real.sin (2 * t)
      = (1 / 2) * Real.sin t ^ (α - 1) * Real.cos t ^ (2 * α - 1) := by
    rw [Real.sin_two_mul, hnum, Real.rpow_sub hs, Real.rpow_sub hc, Real.rpow_one, Real.rpow_one]
    field_simp
  -- `sin t / t ∈ [2/π, 1]`, hence `(sin t / t)^{α-1} ≤ π/2`
  have hsdiv_pos : 0 < Real.sin t / t := div_pos hs ht
  have hsdiv_le1 : Real.sin t / t ≤ 1 := (div_le_one ht).2 (Real.sin_le ht.le)
  have hsdiv_ge : 2 / Real.pi ≤ Real.sin t / t := by
    rw [le_div_iff₀ ht]
    exact Real.mul_le_sin ht.le (by linarith)
  have hpow_le_one : (Real.sin t / t) ^ α ≤ 1 := Real.rpow_le_one hsdiv_pos.le hsdiv_le1 hα.le
  have hsig : (Real.sin t / t) ^ (α - 1) ≤ Real.pi / 2 := by
    rw [Real.rpow_sub hsdiv_pos, Real.rpow_one]
    calc (Real.sin t / t) ^ α / (Real.sin t / t) ≤ 1 / (Real.sin t / t) :=
          div_le_div_of_nonneg_right hpow_le_one hsdiv_pos.le
      _ ≤ Real.pi / 2 := by
          have h := one_div_le_one_div_of_le (a := 2 / Real.pi) (b := Real.sin t / t)
            (by positivity) hsdiv_ge
          have h2 : (1 : ℝ) / (2 / Real.pi) = Real.pi / 2 := by field_simp
          linarith [h, h2]
  -- peel off the `t^{α-1}`
  have hsin_bound : Real.sin t ^ (α - 1) ≤ Real.pi / 2 * t ^ (α - 1) := by
    have hdiv : Real.sin t ^ (α - 1) / t ^ (α - 1) ≤ Real.pi / 2 := by
      rw [← Real.div_rpow hs.le ht.le (α - 1)]
      exact hsig
    exact (div_le_iff₀ (Real.rpow_pos_of_pos ht (α - 1))).1 hdiv
  -- `cos t ∈ [√2/2, 1]`, hence `(cos t)^{2α-1} ≤ 2`
  have hcos_lb : √2 / 2 ≤ Real.cos t := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := t) (y := Real.pi / 4) ht.le
      (by linarith [Real.pi_pos]) htle
    rwa [Real.cos_pi_div_four] at h
  have hcos2a : Real.cos t ^ (2 * α) ≤ 1 :=
    Real.rpow_le_one hc.le (Real.cos_le_one t) (by linarith)
  have hcos_bound : Real.cos t ^ (2 * α - 1) ≤ 2 := by
    rw [Real.rpow_sub hc, Real.rpow_one]
    calc Real.cos t ^ (2 * α) / Real.cos t ≤ 1 / Real.cos t :=
          div_le_div_of_nonneg_right hcos2a hc.le
      _ ≤ 2 := by
          have hhalf : (1 : ℝ) / 2 ≤ Real.cos t := by
            have h2 : (1 : ℝ) ≤ √2 := by
              nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
            linarith
          have h := one_div_le_one_div_of_le (a := (1 : ℝ) / 2) (b := Real.cos t)
            (by norm_num) hhalf
          have h2 : (1 : ℝ) / (1 / 2) = 2 := by norm_num
          linarith [h, h2]
  -- assembly
  have hB : 0 ≤ Real.cos t ^ (2 * α - 1) := Real.rpow_nonneg hc.le _
  have hC : 0 ≤ Real.pi / 2 * t ^ (α - 1) :=
    mul_nonneg (by linarith [Real.pi_pos]) (Real.rpow_nonneg ht.le _)
  have hprod : Real.sin t ^ (α - 1) * Real.cos t ^ (2 * α - 1)
      ≤ (Real.pi / 2 * t ^ (α - 1)) * 2 :=
    mul_le_mul hsin_bound hcos_bound hB hC
  rw [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma]
  calc (Real.sin t * Real.cos t ^ 2) ^ α / Real.sin (2 * t)
      = (1 / 2) * Real.sin t ^ (α - 1) * Real.cos t ^ (2 * α - 1) := hmain
    _ ≤ (1 / 2) * (Real.pi / 2 * t ^ (α - 1)) * 2 := by
        calc (1 / 2) * Real.sin t ^ (α - 1) * Real.cos t ^ (2 * α - 1)
            = (1 / 2) * (Real.sin t ^ (α - 1) * Real.cos t ^ (2 * α - 1)) := by ring
          _ ≤ (1 / 2) * ((Real.pi / 2 * t ^ (α - 1)) * 2) :=
              mul_le_mul_of_nonneg_left hprod (by norm_num)
          _ = (1 / 2) * (Real.pi / 2 * t ^ (α - 1)) * 2 := by ring
    _ = Real.pi / 2 * t ^ (α - 1) := by ring

end Work.FTS.RegPkgGal.R4b
