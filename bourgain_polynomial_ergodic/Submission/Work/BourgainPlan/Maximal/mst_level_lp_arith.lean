import Mathlib

/-!
# The arithmetic absorption lemma for the Mirek–Stein–Trojan level interpolation

`mst_level_lp_arith` is the pure real-arithmetic step of the level interpolation
`mst_level_lp_glue`: the `L^r` loss `(A_r * (s+1) * log (s+2))^(1-θ)` and the `L²`
gain `(A₂ * (s+1)^e₂)^θ` must be absorbed against the target decay `(s+1)^{-2}`
whenever the `L²` exponent `e₂` is negative enough (`e₂ ≤ -3/θ`).

Writing `t = s+1 ≥ 1`, the left-hand side equals
`A_r^{1-θ} A₂^θ * t^{1-θ+θe₂} * (log (t+1))^{1-θ}`.  Since
`1 - θ + θ e₂ ≤ 1 - θ - 3 = -2 - θ`, it suffices to bound
`t^{-θ} (log (t+1))^{1-θ}` uniformly on `t ≥ 1`; the elementary inequality
`log u ≤ u^θ/θ` together with `t+1 ≤ 2t` gives the uniform bound
`2^{θ(1-θ)} / θ^{1-θ}` (lemma `log_absorb`).
-/

namespace Work.BourgainPlan.Maximal

/-- Uniform bound for the logarithmic factor: for `1 ≤ t` and `0 < θ < 1`,
`t^{-θ} (log (t+1))^{1-θ} ≤ 2^{θ(1-θ)} / θ^{1-θ}`. -/
lemma log_absorb {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {t : ℝ} (ht : 1 ≤ t) :
    t ^ (-θ) * (Real.log (t + 1)) ^ (1 - θ) ≤ 2 ^ (θ * (1 - θ)) / θ ^ (1 - θ) := by
  have ht0 : (0:ℝ) < t := lt_of_lt_of_le one_pos ht
  have hLnn : 0 ≤ Real.log (t + 1) := Real.log_nonneg (by linarith)
  have hlog : Real.log (t + 1) ≤ (t + 1) ^ θ / θ := Real.log_le_rpow_div (by linarith) hθ0
  have h1 : (Real.log (t + 1)) ^ (1 - θ) ≤ ((t + 1) ^ θ / θ) ^ (1 - θ) :=
    Real.rpow_le_rpow hLnn hlog (by linarith)
  have h2 : ((t + 1) ^ θ / θ) ^ (1 - θ) = (t + 1) ^ (θ * (1 - θ)) / θ ^ (1 - θ) := by
    rw [Real.div_rpow (Real.rpow_nonneg (by linarith) θ) (le_of_lt hθ0) (1 - θ),
        Real.rpow_mul (by linarith : (0:ℝ) ≤ t + 1) θ (1 - θ)]
  have h3 : (t + 1) ^ (θ * (1 - θ)) ≤ (2 * t) ^ (θ * (1 - θ)) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by nlinarith)
  have h4 : (2 * t) ^ (θ * (1 - θ)) = 2 ^ (θ * (1 - θ)) * t ^ (θ * (1 - θ)) :=
    Real.mul_rpow (by norm_num) (le_of_lt ht0)
  have hden : (0:ℝ) < θ ^ (1 - θ) := Real.rpow_pos_of_pos hθ0 _
  have h5 : t ^ (-θ) * t ^ (θ * (1 - θ)) = t ^ (-(θ^2)) := by
    rw [← Real.rpow_add ht0]; congr 1; ring
  have h6 : t ^ (-(θ^2)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by nlinarith)
  calc t ^ (-θ) * (Real.log (t + 1)) ^ (1 - θ)
      ≤ t ^ (-θ) * ((t + 1) ^ θ / θ) ^ (1 - θ) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (le_of_lt ht0) _)
    _ = t ^ (-θ) * ((t + 1) ^ (θ * (1 - θ)) / θ ^ (1 - θ)) := by rw [h2]
    _ ≤ t ^ (-θ) * ((2 * t) ^ (θ * (1 - θ)) / θ ^ (1 - θ)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h3 (le_of_lt hden))
          (Real.rpow_nonneg (le_of_lt ht0) _)
    _ = t ^ (-θ) * (2 ^ (θ * (1 - θ)) * t ^ (θ * (1 - θ)) / θ ^ (1 - θ)) := by rw [h4]
    _ = 2 ^ (θ * (1 - θ)) / θ ^ (1 - θ) * (t ^ (-θ) * t ^ (θ * (1 - θ))) := by ring
    _ = 2 ^ (θ * (1 - θ)) / θ ^ (1 - θ) * t ^ (-(θ^2)) := by rw [h5]
    _ ≤ 2 ^ (θ * (1 - θ)) / θ ^ (1 - θ) * 1 :=
        mul_le_mul_of_nonneg_left h6
          (le_of_lt (div_pos (Real.rpow_pos_of_pos (by norm_num) _) hden))
    _ = 2 ^ (θ * (1 - θ)) / θ ^ (1 - θ) := by ring

/-- The `L^r` loss of the level estimate `(A_r (s+1) log (s+2))^{1-θ}` combined with the
`L²` gain `(A₂ (s+1)^{e₂})^θ` decays at least as fast as `(s+1)^{-2}`, uniformly in `s`,
as soon as the `L²` exponent satisfies `e₂ ≤ -3/θ`. -/
theorem mst_level_lp_arith {θ e₂ A₂ A_r : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hA₂ : 0 < A₂) (hA_r : 0 < A_r) (he₂ : e₂ ≤ -3 / θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ,
      (A_r * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2))) ^ (1 - θ)
        * (A₂ * ((s : ℝ) + 1) ^ e₂) ^ θ
      ≤ C * ((s : ℝ) + 1) ^ (-2 : ℝ) := by
  refine ⟨A_r ^ (1 - θ) * A₂ ^ θ * (2 ^ (θ * (1 - θ)) / θ ^ (1 - θ)), by positivity, ?_⟩
  intro s
  have hnns : (0:ℝ) ≤ (s:ℝ) := Nat.cast_nonneg s
  have ht : (1:ℝ) ≤ (s:ℝ) + 1 := by linarith
  have ht0 : (0:ℝ) < (s:ℝ) + 1 := lt_of_lt_of_le one_pos ht
  have harg : (s:ℝ) + 2 = ((s:ℝ) + 1) + 1 := by ring
  have hlog0 : (0:ℝ) ≤ Real.log ((s:ℝ) + 2) := by
    apply Real.log_nonneg; linarith
  have habs : ((s:ℝ)+1) ^ (-θ) * (Real.log ((s:ℝ)+2)) ^ (1-θ)
      ≤ 2^(θ*(1-θ))/θ^(1-θ) := by
    rw [harg]; exact log_absorb hθ0 hθ1 ht
  have he₂θ : e₂ * θ ≤ -3 := by
    have h := mul_le_mul_of_nonneg_right he₂ (le_of_lt hθ0)
    have h' : (-3/θ) * θ = -3 := by field_simp
    linarith
  have h2exp : 1 - θ + e₂ * θ ≤ -2 - θ := by linarith
  have hstep : ((s:ℝ)+1)^(1-θ+e₂*θ) ≤ ((s:ℝ)+1)^(-2-θ) :=
    Real.rpow_le_rpow_of_exponent_le ht h2exp
  have hLnn : 0 ≤ (Real.log ((s:ℝ)+2))^(1-θ) := Real.rpow_nonneg hlog0 _
  have h1 : ((s:ℝ)+1)^(1-θ+e₂*θ) * (Real.log ((s:ℝ)+2))^(1-θ)
      ≤ ((s:ℝ)+1)^(-2-θ) * (Real.log ((s:ℝ)+2))^(1-θ) :=
    mul_le_mul_of_nonneg_right hstep hLnn
  have hcoef : 0 ≤ A_r^(1-θ) * A₂^θ := by positivity
  have hexp : (-2 - θ : ℝ) = -2 + (-θ) := by ring
  have hrp : ((s:ℝ)+1)^(-2-θ) = ((s:ℝ)+1)^((-2:ℝ)) * ((s:ℝ)+1)^(-θ) := by
    rw [hexp]
    exact Real.rpow_add ht0 (-2) (-θ)
  have heq : (A_r * (((s:ℝ)+1) * Real.log ((s:ℝ)+2))) ^ (1 - θ)
        * (A₂ * ((s:ℝ)+1) ^ e₂) ^ θ
      = A_r^(1-θ) * A₂^θ * (((s:ℝ)+1)^(1-θ+e₂*θ) * (Real.log ((s:ℝ)+2))^(1-θ)) := by
    rw [Real.mul_rpow (le_of_lt hA_r) (mul_nonneg (le_of_lt ht0) hlog0),
        Real.mul_rpow (le_of_lt hA₂) (Real.rpow_nonneg (le_of_lt ht0) e₂),
        Real.mul_rpow (le_of_lt ht0) hlog0,
        (Real.rpow_mul (le_of_lt ht0) e₂ θ).symm]
    rw [show A_r^(1-θ) * (((s:ℝ)+1)^(1-θ) * (Real.log ((s:ℝ)+2))^(1-θ))
          * (A₂^θ * ((s:ℝ)+1)^(e₂*θ))
        = A_r^(1-θ) * A₂^θ * (((s:ℝ)+1)^(1-θ) * ((s:ℝ)+1)^(e₂*θ)
          * (Real.log ((s:ℝ)+2))^(1-θ)) from by ring]
    rw [← Real.rpow_add ht0]
  rw [heq]
  calc A_r^(1-θ) * A₂^θ * (((s:ℝ)+1)^(1-θ+e₂*θ) * (Real.log ((s:ℝ)+2))^(1-θ))
      ≤ A_r^(1-θ) * A₂^θ * (((s:ℝ)+1)^(-2-θ) * (Real.log ((s:ℝ)+2))^(1-θ)) :=
        mul_le_mul_of_nonneg_left h1 hcoef
    _ = A_r^(1-θ) * A₂^θ
          * (((s:ℝ)+1)^((-2:ℝ)) * (((s:ℝ)+1)^(-θ) * (Real.log ((s:ℝ)+2))^(1-θ))) := by
        rw [hrp]; ring
    _ ≤ A_r^(1-θ) * A₂^θ * (((s:ℝ)+1)^((-2:ℝ)) * (2^(θ*(1-θ))/θ^(1-θ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left habs (Real.rpow_nonneg (le_of_lt ht0) (-2))) hcoef
    _ = A_r^(1-θ) * A₂^θ * (2^(θ*(1-θ))/θ^(1-θ)) * ((s:ℝ)+1)^((-2:ℝ)) := by ring

end Work.BourgainPlan.Maximal
