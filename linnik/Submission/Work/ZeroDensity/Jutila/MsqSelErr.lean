import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.LinnikAreas.Density4.selTheta_asymptotic
import Submission.Work.LinnikAreas.Density4.dyadic_decay_sigma_half
import Submission.Work.LinnikAreas.Density4.dyadic_decay_sigma_half_sq

namespace Work.ZeroDensity.Jutila

open scoped BigOperators
open Finset
open Work.LinnikAreas.Density4

noncomputable section

/-- The first bookkeeping summand `μ(δ)²/δ · σ_{-1/2}(δ) · (log(2+W/δ))^{-3}`. -/
private def mselX (W : ℕ) (δ : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (δ : ℝ) * sHalf δ *
    (Real.log (2 + (W : ℝ) / (δ : ℝ))) ^ (-3 : ℝ)

/-- The second bookkeeping summand `μ(δ)²φ(δ)/δ² · σ_{-1/2}(δ)² · (log(2+W/δ))^{-6}`. -/
private def mselY (W : ℕ) (δ : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius δ : ℝ) ^ 2 * (Nat.totient δ : ℝ)) / ((δ : ℝ) ^ 2) *
    sHalf δ ^ 2 * (Real.log (2 + (W : ℝ) / (δ : ℝ))) ^ (-6 : ℝ)

/-- `selTheta_asymptotic` in `rpow`-exponent form, and phrased with `Tsel`. -/
private lemma Tsel_bound_rpow : ∃ C0 : ℝ, 0 < C0 ∧ ∀ (Q : ℝ) (r : ℕ), 1 ≤ Q → 1 ≤ r →
    |Tsel r Q| ≤ C0 * sHalf r * (Real.log (2 + Q)) ^ (-3 : ℝ) := by
  obtain ⟨C, hC, h⟩ := selTheta_asymptotic
  refine ⟨C, hC, fun Q r hQ hr => ?_⟩
  have he : (Real.log (2 + Q)) ^ (-3 : ℝ) = (Real.log (2 + Q)) ^ (-3 : ℤ) := by
    rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num]
    exact Real.rpow_intCast _ (-3)
  have h1 := h Q hQ r hr
  rw [← he] at h1
  unfold Tsel sHalf
  rw [abs_sub_comm]
  exact h1

/-- `dyadic_decay_sigma_half` with `A = 3`, phrased via `mselX`. -/
private lemma dyadic_mselX : ∃ C : ℝ, 0 < C ∧ ∀ W : ℕ,
    (∑ δ ∈ Finset.Icc 1 W, mselX W δ) ≤ C := by
  obtain ⟨C, hC, h⟩ := dyadic_decay_sigma_half
  refine ⟨C, hC, fun W => ?_⟩
  have hh := h W 3 (by norm_num)
  simpa only [mselX, sHalf] using hh

/-- `dyadic_decay_sigma_half_sq` with `A = 3`, phrased via `mselY`. -/
private lemma dyadic_mselY : ∃ C : ℝ, 0 < C ∧ ∀ W : ℕ,
    (∑ δ ∈ Finset.Icc 1 W, mselY W δ) ≤ C := by
  obtain ⟨C, hC, h⟩ := dyadic_decay_sigma_half_sq
  refine ⟨C, hC, fun W => ?_⟩
  have hexp : (-2 : ℝ) * 3 = -6 := by norm_num
  simpa only [mselY, sHalf, hexp] using h W 3 (by norm_num)

/-- The pointwise algebraic identity: writing `Θ_z(δ) = δ/φ(δ) - T_z(δ)`, the difference
between the mixed Selberg summand and the Mertens summand is
`-(μ²(δ)/δ)(T_w+T_y) + (μ²(δ)φ(δ)/δ²) T_w T_y`. -/
private lemma selTerm_sub (w y : ℝ) {δ : ℕ} (hδ : 1 ≤ δ) :
    ((ArithmeticFunction.moebius δ : ℝ) ^ 2 * (Nat.totient δ : ℝ)) / ((δ : ℝ) ^ 2) *
        selTheta (w / (δ : ℝ)) δ * selTheta (y / (δ : ℝ)) δ
      - ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (Nat.totient δ : ℝ)
    = -(((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (δ : ℝ)) *
        (Tsel δ (w / (δ : ℝ)) + Tsel δ (y / (δ : ℝ)))
      + ((ArithmeticFunction.moebius δ : ℝ) ^ 2 * (Nat.totient δ : ℝ)) / ((δ : ℝ) ^ 2) *
        Tsel δ (w / (δ : ℝ)) * Tsel δ (y / (δ : ℝ)) := by
  have hδ0 : (δ : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
    exact ne_of_gt this
  have hφ0 : (Nat.totient δ : ℝ) ≠ 0 := by
    have : 0 < Nat.totient δ := Nat.totient_pos.mpr (by omega)
    exact_mod_cast (ne_of_gt this)
  unfold Tsel
  field_simp
  ring

/-- The pointwise error bound. -/
private lemma selTerm_abs_bound {C0 : ℝ} (hC0 : 0 ≤ C0)
    (hT : ∀ (Q : ℝ) (r : ℕ), 1 ≤ Q → 1 ≤ r →
      |Tsel r Q| ≤ C0 * sHalf r * (Real.log (2 + Q)) ^ (-3 : ℝ))
    {w y : ℝ} (_hw1 : 1 ≤ w) (hwy : w ≤ y) {W : ℕ} (hWw : (W : ℝ) ≤ w)
    {δ : ℕ} (hδ : δ ∈ Finset.Icc 1 W) :
    |((ArithmeticFunction.moebius δ : ℝ) ^ 2 * (Nat.totient δ : ℝ)) / ((δ : ℝ) ^ 2) *
        selTheta (w / (δ : ℝ)) δ * selTheta (y / (δ : ℝ)) δ
      - ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (Nat.totient δ : ℝ)|
    ≤ 2 * C0 * mselX W δ + C0 ^ 2 * mselY W δ := by
  obtain ⟨hδ1, hδW⟩ := Finset.mem_Icc.mp hδ
  have hdR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ1
  have hdW : (δ : ℝ) ≤ (W : ℝ) := by exact_mod_cast hδW
  have hdw : (δ : ℝ) ≤ w := le_trans hdW hWw
  have hdy : (δ : ℝ) ≤ y := le_trans hdw hwy
  have hQw : 1 ≤ w / (δ : ℝ) := (one_le_div hdR).mpr hdw
  have hQy : 1 ≤ y / (δ : ℝ) := (one_le_div hdR).mpr hdy
  have hbase : (1 : ℝ) < 2 + (W : ℝ) / (δ : ℝ) := by
    have : (0 : ℝ) ≤ (W : ℝ) / (δ : ℝ) := by positivity
    linarith
  have hlogW : 0 < Real.log (2 + (W : ℝ) / (δ : ℝ)) := Real.log_pos hbase
  have hlogw : Real.log (2 + (W : ℝ) / (δ : ℝ)) ≤ Real.log (2 + w / (δ : ℝ)) := by
    apply Real.log_le_log (by linarith : (0 : ℝ) < 2 + (W : ℝ) / (δ : ℝ))
    have h := div_le_div_of_nonneg_right hWw hdR.le
    linarith
  have hlogy : Real.log (2 + (W : ℝ) / (δ : ℝ)) ≤ Real.log (2 + y / (δ : ℝ)) := by
    apply Real.log_le_log (by linarith : (0 : ℝ) < 2 + (W : ℝ) / (δ : ℝ))
    have h := div_le_div_of_nonneg_right (le_trans hWw hwy) hdR.le
    linarith
  have hLw : (Real.log (2 + w / (δ : ℝ))) ^ (-3 : ℝ)
      ≤ (Real.log (2 + (W : ℝ) / (δ : ℝ))) ^ (-3 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hlogW hlogw (by norm_num)
  have hLy : (Real.log (2 + y / (δ : ℝ))) ^ (-3 : ℝ)
      ≤ (Real.log (2 + (W : ℝ) / (δ : ℝ))) ^ (-3 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hlogW hlogy (by norm_num)
  have hsHnn : 0 ≤ sHalf δ := sHalf_nonneg δ
  have hLWpos : 0 < (Real.log (2 + (W : ℝ) / (δ : ℝ))) ^ (-3 : ℝ) :=
    Real.rpow_pos_of_pos hlogW _
  have hCLnn : 0 ≤ C0 * sHalf δ * (Real.log (2 + (W : ℝ) / (δ : ℝ))) ^ (-3 : ℝ) :=
    mul_nonneg (mul_nonneg hC0 hsHnn) hLWpos.le
  rw [selTerm_sub w y hδ1]
  set Am : ℝ := ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (δ : ℝ) with hAm
  set Bm : ℝ := ((ArithmeticFunction.moebius δ : ℝ) ^ 2 * (Nat.totient δ : ℝ)) / ((δ : ℝ) ^ 2)
    with hBm
  set Tw : ℝ := Tsel δ (w / (δ : ℝ)) with hTwS
  set Ty : ℝ := Tsel δ (y / (δ : ℝ)) with hTyS
  have hAnn : 0 ≤ Am := by rw [hAm]; positivity
  have hBnn : 0 ≤ Bm := by rw [hBm]; positivity
  have hTwb : |Tw| ≤ C0 * sHalf δ * (Real.log (2 + (W : ℝ) / (δ : ℝ))) ^ (-3 : ℝ) := by
    rw [hTwS]
    refine le_trans (hT (w / (δ : ℝ)) δ hQw hδ1) ?_
    exact mul_le_mul_of_nonneg_left hLw (mul_nonneg hC0 hsHnn)
  have hTyb : |Ty| ≤ C0 * sHalf δ * (Real.log (2 + (W : ℝ) / (δ : ℝ))) ^ (-3 : ℝ) := by
    rw [hTyS]
    refine le_trans (hT (y / (δ : ℝ)) δ hQy hδ1) ?_
    exact mul_le_mul_of_nonneg_left hLy (mul_nonneg hC0 hsHnn)
  have hsum_abs : |Tw| + |Ty|
      ≤ 2 * (C0 * sHalf δ * (Real.log (2 + (W : ℝ) / (δ : ℝ))) ^ (-3 : ℝ)) := by
    linarith
  have hprod_abs : |Tw| * |Ty|
      ≤ (C0 * sHalf δ * (Real.log (2 + (W : ℝ) / (δ : ℝ))) ^ (-3 : ℝ)) *
        (C0 * sHalf δ * (Real.log (2 + (W : ℝ) / (δ : ℝ))) ^ (-3 : ℝ)) :=
    mul_le_mul hTwb hTyb (abs_nonneg _) hCLnn
  have hL3sq : (Real.log (2 + (W : ℝ) / (δ : ℝ))) ^ (-3 : ℝ) *
        (Real.log (2 + (W : ℝ) / (δ : ℝ))) ^ (-3 : ℝ)
      = (Real.log (2 + (W : ℝ) / (δ : ℝ))) ^ (-6 : ℝ) := by
    rw [← Real.rpow_add hlogW, show (-3 : ℝ) + -3 = -6 by norm_num]
  calc |-(Am) * (Tw + Ty) + Bm * Tw * Ty|
      ≤ Am * (|Tw| + |Ty|) + Bm * (|Tw| * |Ty|) := by
        have h2 : |-(Am) * (Tw + Ty)| = Am * |Tw + Ty| := by
          rw [abs_mul, abs_neg, abs_of_nonneg hAnn]
        have h3 : |Bm * Tw * Ty| = Bm * (|Tw| * |Ty|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hBnn]
          ring
        calc |-(Am) * (Tw + Ty) + Bm * Tw * Ty|
            ≤ |-(Am) * (Tw + Ty)| + |Bm * Tw * Ty| := abs_add_le _ _
          _ = Am * |Tw + Ty| + Bm * (|Tw| * |Ty|) := by rw [h2, h3]
          _ ≤ Am * (|Tw| + |Ty|) + Bm * (|Tw| * |Ty|) := by
              have h1 : Am * |Tw + Ty| ≤ Am * (|Tw| + |Ty|) :=
                mul_le_mul_of_nonneg_left (abs_add_le Tw Ty) hAnn
              linarith
    _ ≤ Am * (2 * (C0 * sHalf δ * (Real.log (2 + (W : ℝ) / (δ : ℝ))) ^ (-3 : ℝ)))
          + Bm * ((C0 * sHalf δ * (Real.log (2 + (W : ℝ) / (δ : ℝ))) ^ (-3 : ℝ)) *
                  (C0 * sHalf δ * (Real.log (2 + (W : ℝ) / (δ : ℝ))) ^ (-3 : ℝ))) :=
        add_le_add (mul_le_mul_of_nonneg_left hsum_abs hAnn)
          (mul_le_mul_of_nonneg_left hprod_abs hBnn)
    _ = 2 * C0 * mselX W δ + C0 ^ 2 * mselY W δ := by
        unfold mselX mselY
        rw [← hAm, ← hBm, ← hL3sq]
        ring

/-- **Error bound for the mixed Selberg form against the Mertens sum.**  Uniformly in
`1 ≤ w ≤ y` and `1 ≤ W ≤ w`, the diagonalized mixed Selberg form
`Σ_{δ ≤ W} (μ(δ)²φ(δ)/δ²) Θ_w(δ) Θ_y(δ)` differs from `Σ_{δ ≤ W} μ(δ)²/φ(δ)` by at most an
absolute constant.

Route.  Write `Θ_z(δ) = selTheta (z/δ) δ = δ/φ(δ) + E_z(δ)` and use `selTheta_asymptotic`:
`|E_z(δ)| ≤ C0·σ(δ)·(log (2 + z/δ))^{-3}` with `σ(δ) = Σ_{d ∣ δ} d^{-1/2}` and `1 ≤ z/δ`.  The
difference is `Σ_{δ ≤ W} (μ(δ)²φ(δ)/δ²)·((δ/φ(δ))(E_w(δ) + E_y(δ)) + E_w(δ)E_y(δ))`, so it is
bounded by `2 C0 Σ_{δ≤W} (μ²(δ)/δ) σ(δ) (log (2 + w/δ))^{-3} + C0² Σ_{δ≤W}
(μ²(δ)φ(δ)/δ²) σ(δ)² (log (2 + w/δ))^{-6}` (using `w ≤ y` and `W ≤ w` to replace all logarithms
by the smallest one), and these two sums are bounded by the absolute constants of
`Work.LinnikAreas.Density4.dyadic_decay_sigma_half` (take `V = W`, `A = 3`) and
`Work.LinnikAreas.Density4.dyadic_decay_sigma_half_sq` (take `V = W`, `A = 3`, exponent `-2·3`).
`selTheta_asymptotic` produces a `zpow` exponent `(-3 : ℤ)`; convert to the `rpow` exponent of
the two dyadic estimates with `Real.rpow_intCast`. -/
theorem MsqSelErr : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (W : ℕ),
    1 ≤ w → w ≤ y → (W : ℝ) ≤ w → 1 ≤ W →
      |(Finset.sum (Finset.Icc 1 W) (fun δ => ((ArithmeticFunction.moebius δ : ℝ) ^ 2 *
            (Nat.totient δ : ℝ)) / ((δ : ℝ) ^ 2) *
            Work.LinnikAreas.Density4.selTheta (w / (δ : ℝ)) δ *
            Work.LinnikAreas.Density4.selTheta (y / (δ : ℝ)) δ))
        - (Finset.sum (Finset.Icc 1 W) (fun δ =>
            ((ArithmeticFunction.moebius δ : ℝ) ^ 2) / (Nat.totient δ : ℝ)))| ≤ C := by
  obtain ⟨C0, hC0pos, hT⟩ := Tsel_bound_rpow
  obtain ⟨C1, hC1pos, hD1⟩ := dyadic_mselX
  obtain ⟨C2, hC2pos, hD2⟩ := dyadic_mselY
  refine ⟨2 * C0 * C1 + C0 ^ 2 * C2, by positivity, ?_⟩
  intro w y W hw1 hwy hWw hW1
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun δ hδ => selTerm_abs_bound hC0pos.le hT hw1 hwy hWw hδ)) ?_
  have hX : (∑ δ ∈ Finset.Icc 1 W, mselX W δ) ≤ C1 := hD1 W
  have hY : (∑ δ ∈ Finset.Icc 1 W, mselY W δ) ≤ C2 := hD2 W
  calc (∑ δ ∈ Finset.Icc 1 W, (2 * C0 * mselX W δ + C0 ^ 2 * mselY W δ))
      = (∑ δ ∈ Finset.Icc 1 W, 2 * C0 * mselX W δ)
          + (∑ δ ∈ Finset.Icc 1 W, C0 ^ 2 * mselY W δ) := Finset.sum_add_distrib
    _ = 2 * C0 * (∑ δ ∈ Finset.Icc 1 W, mselX W δ)
          + C0 ^ 2 * (∑ δ ∈ Finset.Icc 1 W, mselY W δ) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * C0 * C1 + C0 ^ 2 * C2 :=
        add_le_add (mul_le_mul_of_nonneg_left hX (by positivity))
          (mul_le_mul_of_nonneg_left hY (by positivity))

end

end Work.ZeroDensity.Jutila
