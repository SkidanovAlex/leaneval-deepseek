/-
# The weak `L^ε` estimate

The decay lemma (`Submission.decay_contactPt`) says that the complement of the contact set
`contactPt (a M^j) φ` of the iterated opening has measure at most `(1-θ)^j |S|`, while the values
of `φ` at contact points of opening `a M^j` are at most `1 + 2 a M^j`
(`Submission.contactPt_le_value`).  Hence, for the *largest* `j` with `(t-1)/(2a) ≤ M^j`
(so that the opening `a M^j` matches the level `t` in both directions),

  `{φ > t} ∩ S ⊆ S \ contactPt (a M^j) φ`,  so  `|{φ > t} ∩ S| ≤ (1-θ)^j |S|`,  and
  `t ≤ (2 a M + 1) M^j`,  so  `(1-θ)^j = (M^j)^{-κ} ≤ (2 a M + 1)^κ t^{-κ}`

for any exponent `κ > 0` with `1 - θ ≤ M^{-κ}` (such a `κ` exists because `M^{-κ} → 1` as
`κ → 0⁺`, and it plays the role of Fan's `ε`).  This is the weak `L^κ` estimate, the starting point
of the weak Harnack inequality and of the Hölder regularity theory.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Decay

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- The elementary real inequality `(x^j)^{-κ} ≤ C^κ t^{-κ}` used in the weak `L^ε` estimate: it
suffices that `t ≤ C x^j` and `1 ≤ x^j`. -/
theorem rpow_neg_mul_le_of_le_mul {x C t κ : ℝ} {j : ℕ} (hx : 0 < x) (hC : 0 < C) (ht : 0 < t)
    (hx1 : 1 ≤ x ^ j) (htC : t ≤ C * x ^ j) (hκ : 0 < κ) :
    (x ^ j) ^ (-κ) ≤ C ^ κ * t ^ (-κ) := by
  have hxp : 0 < x ^ j := pow_pos hx j
  have h1 : 1 ≤ C * x ^ j / t := (one_le_div ht).mpr htC
  have h2 : (1 : ℝ) ≤ (C * x ^ j / t) ^ κ := Real.one_le_rpow h1 hκ.le
  have h3 : (C * x ^ j / t) ^ κ = C ^ κ * (x ^ j) ^ κ * t ^ (-κ) := by
    rw [Real.div_rpow (by positivity) (le_of_lt ht), Real.mul_rpow (le_of_lt hC) hxp.le,
      div_eq_mul_inv, ← Real.rpow_neg (le_of_lt ht)]
  rw [h3] at h2
  have h4 : (x ^ j) ^ (-κ) = ((x ^ j) ^ κ)⁻¹ := Real.rpow_neg hxp.le κ
  rw [h4]
  calc ((x ^ j) ^ κ)⁻¹ = 1 * ((x ^ j) ^ κ)⁻¹ := by rw [one_mul]
    _ ≤ (C ^ κ * (x ^ j) ^ κ * t ^ (-κ)) * ((x ^ j) ^ κ)⁻¹ :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = C ^ κ * t ^ (-κ) := by
        field_simp

/-- The elementary real inequality `1 ≤ C^κ t^{-κ}` for `0 < t ≤ C`: this is the weak `L^ε`
estimate in the regime of small levels. -/
theorem one_le_rpow_mul_rpow_neg {C t κ : ℝ} (hC : 0 < C) (ht : 0 < t) (hCt : t ≤ C)
    (hκ : 0 < κ) :
    1 ≤ C ^ κ * t ^ (-κ) := by
  have h1 : 1 ≤ C / t := (one_le_div ht).mpr hCt
  have h2 : (1 : ℝ) ≤ (C / t) ^ κ := Real.one_le_rpow h1 hκ.le
  have h3 : (C / t) ^ κ = C ^ κ * t ^ (-κ) := by
    rw [Real.div_rpow hC.le (le_of_lt ht), div_eq_mul_inv, ← Real.rpow_neg (le_of_lt ht)]
  rwa [h3] at h2

theorem weak_Leps {φ : ℝ⁴ → ℝ} (hφ : ContDiffOn ℝ 2 φ (ball 0 (3 / 2)))
    {C : ℝ⁴ →L[ℝ] ℝ⁴} (hC : C.IsSymmetric) {c c' : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪C v, v⟫) (hcq' : ∀ v : ℝ⁴, ⟪C v, v⟫ ≤ c' * ‖v‖ ^ 2)
    {ε : ℝ} (hε : 0 < ε) (heq : ∀ x ∈ ball 0 (3 / 2), Fop C ε (hessOp φ x) = 0)
    {a p M : ℝ} (ha : 0 < a) (hp : 0 < p) (hM1 : 1 < M)
    (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1))) (hpbig : 16 * c' / c + 2 ≤ p)
    {Km : ℕ} (hbig : 48 * ε * (a * M ^ Km) * 2 ^ (2 * p + 4) ≤ c)
    (hbig' : 3 * ε * (a * M ^ Km) ≤ c / 2)
    (hbase : volume (closedBall (0 : ℝ⁴) (1 / 2) \ contactPt a φ) ≤
      ENNReal.ofReal (1 - (((M - 1) / (8 * M)) ^ 4 / (1 + (2 * trOp C / c + 3)) ^ 4))
        * volume (closedBall (0 : ℝ⁴) (1 / 2)))
    (hinf : ∃ x₁ ∈ closedBall 0 (1 / 2), φ x₁ ≤ 1)
    {κ : ℝ} (hκ : 0 < κ)
    (hκM : 1 - (((M - 1) / (8 * M)) ^ 4 / ((1 + (2 * trOp C / c + 3)) ^ 4 * 5 ^ 4))
      ≤ M ^ (-κ))
    {t : ℝ} (ht0 : 0 < t) (htK : t ≤ 1 + 2 * (a * M ^ Km)) :
    volume (closedBall (0 : ℝ⁴) (1 / 2) ∩ {x : ℝ⁴ | t < φ x}) ≤
      ENNReal.ofReal ((2 * a * M + 1) ^ κ * t ^ (-κ)) * volume (closedBall (0 : ℝ⁴) (1 / 2)) := by
  have hMpos : 0 < M := by linarith
  have htrC : 0 ≤ trOp C := by
    rw [trOp_eq_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have h2 := hcq (stdB4 i)
    have h3 : ‖stdB4 i‖ = 1 := stdB4.orthonormal.1 i
    rw [h3] at h2
    nlinarith [h2]
  have hθle1 : 0 ≤ 1 - (((M - 1) / (8 * M)) ^ 4 /
      ((1 + (2 * trOp C / c + 3)) ^ 4 * 5 ^ 4)) := one_sub_theta_nonneg hM1 hc htrC
  have hCpos : 0 < 2 * a * M + 1 := by positivity
  by_cases hsmall : t ≤ 2 * a * M + 1
  · -- small levels: the trivial bound
    calc volume (closedBall (0 : ℝ⁴) (1 / 2) ∩ {x : ℝ⁴ | t < φ x})
        ≤ volume (closedBall (0 : ℝ⁴) (1 / 2)) := measure_mono Set.inter_subset_left
      _ = 1 * volume (closedBall (0 : ℝ⁴) (1 / 2)) := (one_mul _).symm
      _ ≤ ENNReal.ofReal ((2 * a * M + 1) ^ κ * t ^ (-κ))
            * volume (closedBall (0 : ℝ⁴) (1 / 2)) := by
          refine mul_le_mul_left ?_ _
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (one_le_rpow_mul_rpow_neg hCpos ht0 hsmall hκ)
  · -- large levels: the largest opening that still fits below the level
    push_neg at hsmall
    set u : ℝ := (t - 1) / (2 * a) with hudef
    have hu1 : 1 ≤ u := by
      rw [hudef, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * a)]
      nlinarith [hsmall, hM1, ha]
    have huM : u ≤ M ^ Km := by
      rw [hudef, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * a)]
      nlinarith [htK]
    set j : ℕ := Nat.findGreatest (fun n => M ^ n ≤ u) Km with hjdef
    have hjP : M ^ j ≤ u := by
      rw [hjdef]
      exact Nat.findGreatest_spec (P := fun n => M ^ n ≤ u) (Nat.zero_le Km) (by simpa using hu1)
    have hjle : j ≤ Km := by rw [hjdef]; exact Nat.findGreatest_le Km
    have hj1 : 1 ≤ M ^ j := one_le_pow₀ hM1.le
    -- the opening stays in the range where the growth lemma applies
    have hleM : a * M ^ j ≤ a * M ^ Km :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM1.le hjle) ha.le
    have hbigj : 48 * ε * (a * M ^ j) * 2 ^ (2 * p + 4) ≤ c :=
      le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hleM (by positivity))
        (by positivity)) hbig
    have hbigj' : 3 * ε * (a * M ^ j) ≤ c / 2 :=
      le_trans (mul_le_mul_of_nonneg_left hleM (by positivity)) hbig'
    -- the level sits above the opening
    have hlevel : 1 + 2 * (a * M ^ j) ≤ t := by
      rw [hudef, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * a)] at hjP
      have hEq : M ^ j * (2 * a) = 2 * (a * M ^ j) := by ring
      rw [hEq] at hjP
      linarith
    -- but not too far above it
    have hmax : u < M ^ (j + 1) := by
      rcases eq_or_lt_of_le hjle with hjeq | hjlt
      · rw [hjeq]
        calc u ≤ M ^ Km := huM
          _ < M ^ (Km + 1) := by
              have h1 : 1 ≤ M ^ Km := one_le_pow₀ hM1.le
              rw [pow_succ]
              nlinarith [h1, hMpos]
      · have hg : ¬ (M ^ (j + 1) ≤ u) := by
          intro hcon
          have hle : j + 1 ≤ j := by
            rw [hjdef]
            exact Nat.le_findGreatest (P := fun n => M ^ n ≤ u) (by omega) hcon
          omega
        exact not_le.mp hg
    have htC : t ≤ (2 * a * M + 1) * M ^ j := by
      rw [hudef, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * a)] at hmax
      have h1 : t - 1 ≤ 2 * a * M ^ (j + 1) := by
        have hEq : M ^ (j + 1) * (2 * a) = 2 * a * M ^ (j + 1) := by ring
        linarith [hmax, hEq]
      have h2 : 2 * a * M ^ (j + 1) = (2 * a * M) * M ^ j := by rw [pow_succ]; ring
      rw [h2] at h1
      nlinarith [h1, hj1, ha, hMpos]
    -- the measure of the contact set decays
    have hdec := decay_contactPt hφ hC hc hcq hcq' hε heq ha hp hM1 hM hpbig hbigj hbigj' hbase
    have hsub : closedBall (0 : ℝ⁴) (1 / 2) ∩ {x : ℝ⁴ | t < φ x} ⊆
        closedBall (0 : ℝ⁴) (1 / 2) \ contactPt (a * M ^ j) φ := by
      intro x hx
      obtain ⟨hxS, hxt⟩ := hx
      refine ⟨hxS, fun hxcp => ?_⟩
      obtain ⟨x₁, hx₁, hle₁⟩ := hinf
      have hv := contactPt_le_value (a := a * M ^ j) (by positivity)
        (closedBall_subset_closedBall (by norm_num : (1 : ℝ) / 2 ≤ 1) hx₁) hle₁ hxcp
      have hxt' : t < φ x := hxt
      linarith
    -- the geometric decay written as a power of `t`
    have harith : (1 - (((M - 1) / (8 * M)) ^ 4 /
        ((1 + (2 * trOp C / c + 3)) ^ 4 * 5 ^ 4))) ^ j
        ≤ (2 * a * M + 1) ^ κ * t ^ (-κ) := by
      have h1 := pow_le_pow_left₀ hθle1 hκM j
      have h2 : (M ^ (-κ)) ^ j = (M ^ j) ^ (-κ) := by
        have hL : (M ^ (-κ)) ^ j = M ^ ((-κ) * (j : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hMpos)]
        have hR : (M ^ j) ^ (-κ) = M ^ ((j : ℝ) * (-κ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hMpos)]
        rw [hL, hR, mul_comm]
      have h3 : (M ^ j) ^ (-κ) ≤ (2 * a * M + 1) ^ κ * t ^ (-κ) :=
        rpow_neg_mul_le_of_le_mul hMpos hCpos ht0 hj1 htC hκ
      calc (1 - (((M - 1) / (8 * M)) ^ 4 /
              ((1 + (2 * trOp C / c + 3)) ^ 4 * 5 ^ 4))) ^ j
          ≤ (M ^ (-κ)) ^ j := h1
        _ = (M ^ j) ^ (-κ) := h2
        _ ≤ (2 * a * M + 1) ^ κ * t ^ (-κ) := h3
    calc volume (closedBall (0 : ℝ⁴) (1 / 2) ∩ {x : ℝ⁴ | t < φ x})
        ≤ volume (closedBall (0 : ℝ⁴) (1 / 2) \ contactPt (a * M ^ j) φ) := measure_mono hsub
      _ ≤ ENNReal.ofReal ((1 - (((M - 1) / (8 * M)) ^ 4 /
            ((1 + (2 * trOp C / c + 3)) ^ 4 * 5 ^ 4))) ^ j)
            * volume (closedBall (0 : ℝ⁴) (1 / 2)) := hdec
      _ ≤ ENNReal.ofReal ((2 * a * M + 1) ^ κ * t ^ (-κ))
            * volume (closedBall (0 : ℝ⁴) (1 / 2)) :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal harith) _

end

end Submission
