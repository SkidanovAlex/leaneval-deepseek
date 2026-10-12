import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.chi_boundary_taylor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiScale_image_le`

**The lemma.**  For `0 < ℓ`, `0 ≤ R ≤ ℓ` and every `K : ℕ` there is `C ≥ 0` such that for all
`x y : ℝ³` which are *lattice-close at scale `ℓ`* — i.e. `x − y` is within `R` of `ℓ • m` for some
nonzero integer vector `m` — one has

    chiScale ℓ x * chiScale ℓ y ≤ C (R/ℓ)^K .

**Why it is true.**  `chiScale ℓ = chi(·/ℓ)` is supported in the open ball of radius `ℓ/2`, and
`chi` is *flat to all orders* at the boundary of its support: `Work.BoseFixB1.chi_boundary_taylor`
gives `chi z ≤ C_K (1/2 − ‖z‖)^K` for `‖z‖ ≤ 1/2`.  Writing `z₁ := ℓ⁻¹ • x`, `z₂ := ℓ⁻¹ • y`, the
hypothesis reads `‖z₁ − z₂ − m‖ ≤ R/ℓ` with `‖m‖ ≥ 1` (`m` a *nonzero* integer vector), and the
support condition gives `‖z₁‖, ‖z₂‖ < 1/2` whenever the product is nonzero.  Then

    (1/2 − ‖z₁‖) + (1/2 − ‖z₂‖) ≤ ‖z₁ − z₂‖ + 1 − (‖z₁‖ + ‖z₂‖) ≤ R/ℓ ,

because `‖m‖ − R/ℓ ≤ ‖z₁ − z₂‖ ≤ ‖z₁‖ + ‖z₂‖`.  With `a := 1/2 − ‖z₁‖`, `b := 1/2 − ‖z₂‖` we get
`a + b ≤ R/ℓ ≤ 1`, hence `a b ≤ ((a+b)/2)² ≤ (R/(2ℓ))² ≤ R/ℓ` (as `R/(2ℓ) ≤ 1`), and the flatness
bound turns this into `chi z₁ chi z₂ ≤ C_K² (R/ℓ)^K`.

The proof is elementary; the only ingredient from the corpus is the flatness estimate, and the
only geometric input is `‖m‖ ≥ 1` for a nonzero integer vector.
-/

namespace Work.BoseBoxFock

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A **nonzero integer vector has (Euclidean) norm at least `1`**.  Used to convert the
lattice-closeness hypothesis into the separation estimate
`‖z₁ − z₂‖ ≥ 1 − R/ℓ` on the scaled variables. -/
private lemma chiImage_intVec_norm_ge_one (m : Fin 3 → ℤ) (hm : m ≠ 0) :
    (1 : ℝ) ≤ ‖(WithLp.toLp 2 (fun i : Fin 3 => (m i : ℝ)) : ℝ³)‖ := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (funext fun j => h j)
  have h1 : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
  have h2 : (1 : ℝ) ≤ |((m i : ℤ) : ℝ)| := by exact_mod_cast h1
  have h3 : ((WithLp.toLp 2 (fun i : Fin 3 => (m i : ℝ)) : ℝ³)).ofLp i = ((m i : ℤ) : ℝ) :=
    congrFun (WithLp.ofLp_toLp 2 (fun i : Fin 3 => (m i : ℝ))) i
  have h4 : ‖((WithLp.toLp 2 (fun i : Fin 3 => (m i : ℝ)) : ℝ³)).ofLp i‖ ≤
      ‖(WithLp.toLp 2 (fun i : Fin 3 => (m i : ℝ)) : ℝ³)‖ := PiLp.norm_apply_le _ i
  rw [h3, Real.norm_eq_abs] at h4
  linarith

/-- **Elementary arithmetic of the decay.**  If `a, b ≥ 0` and `a + b ≤ u ≤ 1` then `a b ≤ u`.
(`a b ≤ ((a+b)/2)² ≤ (u/2)² ≤ u/2 ≤ u`.) -/
private lemma chiImage_mul_le_of_add_le {a b u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a + b ≤ u) (hu : u ≤ 1) : a * b ≤ u := by
  have hu0 : 0 ≤ u := le_trans (add_nonneg ha hb) h
  have h1 : a * b ≤ ((a + b) / 2) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have h2 : ((a + b) / 2) ^ 2 ≤ (u / 2) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  have h3 : (u / 2) ^ 2 ≤ u := by nlinarith [hu0, hu]
  linarith

theorem chiScale_image_le {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hRℓ : R ≤ ℓ) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : EuclideanSpace ℝ (Fin 3),
      (∃ m : Fin 3 → ℤ, m ≠ 0 ∧
        ‖x - y - ℓ • WithLp.toLp 2 (fun i : Fin 3 => (m i : ℝ))‖ ≤ R) →
      Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiScale ℓ y
        ≤ C * (R / ℓ) ^ K := by
  obtain ⟨CK, hCKpos, hCK⟩ := Work.BoseFixB1.chi_boundary_taylor K
  have hRl_nn : 0 ≤ R / ℓ := div_nonneg hR hℓ.le
  have hRl_le_one : R / ℓ ≤ 1 := (div_le_one hℓ).mpr hRℓ
  refine ⟨CK ^ 2 + 1, by positivity, ?_⟩
  intro x y hxy
  have hbase : 0 ≤ (R / ℓ) ^ K := pow_nonneg hRl_nn K
  by_cases h1 : ‖(ℓ⁻¹ : ℝ) • x‖ < 1 / 2
  · by_cases h2 : ‖(ℓ⁻¹ : ℝ) • y‖ < 1 / 2
    · -- both scaled points lie in the interior of the support of `chi`
      obtain ⟨m, hm, hmR⟩ := hxy
      set M : ℝ³ := WithLp.toLp 2 (fun i : Fin 3 => (m i : ℝ)) with hM
      set zx : ℝ³ := (ℓ⁻¹ : ℝ) • x with hzx
      set zy : ℝ³ := (ℓ⁻¹ : ℝ) • y with hzy
      have hzx_le : ‖zx‖ ≤ 1 / 2 := by rw [hzx]; exact h1.le
      have hzy_le : ‖zy‖ ≤ 1 / 2 := by rw [hzy]; exact h2.le
      have hM1 : (1 : ℝ) ≤ ‖M‖ := by rw [hM]; exact chiImage_intVec_norm_ge_one m hm
      have hmR' : ‖x - y - ℓ • M‖ ≤ R := by rw [hM]; exact hmR
      -- the scaled separation hypothesis
      have hdist : ‖zx - zy - M‖ ≤ R / ℓ := by
        have hdiff : zx - zy - M = (ℓ⁻¹ : ℝ) • (x - y - ℓ • M) := by
          rw [hzx, hzy, hM, smul_sub, smul_sub, smul_smul]
          rw [inv_mul_cancel₀ (ne_of_gt hℓ), one_smul]
        rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hℓ.le),
          div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left hmR' (inv_nonneg.mpr hℓ.le)
      -- the boundary distances sum to at most `R/ℓ`
      have hsum : (1 / 2 - ‖zx‖) + (1 / 2 - ‖zy‖) ≤ R / ℓ := by
        have h4 : ‖zx - zy‖ ≤ ‖zx‖ + ‖zy‖ := norm_sub_le zx zy
        have h5 : ‖M‖ - ‖zx - zy - M‖ ≤ ‖zx - zy‖ := by
          have h6 := norm_sub_le (zx - zy) (zx - zy - M)
          have hsub : (zx - zy) - (zx - zy - M) = M := by abel
          rw [hsub] at h6
          linarith
        linarith
      have ha_nn : 0 ≤ 1 / 2 - ‖zx‖ := by linarith
      have hb_nn : 0 ≤ 1 / 2 - ‖zy‖ := by linarith
      -- flatness at the boundary
      have hprod : chi zx * chi zy ≤ CK ^ 2 * ((1 / 2 - ‖zx‖) * (1 / 2 - ‖zy‖)) ^ K := by
        have haK : 0 ≤ (1 / 2 - ‖zx‖) ^ K := pow_nonneg ha_nn K
        have hbm := mul_le_mul (hCK zx hzx_le) (hCK zy hzy_le) (chi_nonneg zy)
          (mul_nonneg hCKpos.le haK)
        calc chi zx * chi zy ≤ (CK * (1 / 2 - ‖zx‖) ^ K) * (CK * (1 / 2 - ‖zy‖) ^ K) := hbm
          _ = CK ^ 2 * ((1 / 2 - ‖zx‖) ^ K * (1 / 2 - ‖zy‖) ^ K) := by ring
          _ = CK ^ 2 * ((1 / 2 - ‖zx‖) * (1 / 2 - ‖zy‖)) ^ K := by rw [mul_pow]
      have hab : (1 / 2 - ‖zx‖) * (1 / 2 - ‖zy‖) ≤ R / ℓ :=
        chiImage_mul_le_of_add_le ha_nn hb_nn hsum hRl_le_one
      have hpow : ((1 / 2 - ‖zx‖) * (1 / 2 - ‖zy‖)) ^ K ≤ (R / ℓ) ^ K :=
        pow_le_pow_left₀ (mul_nonneg ha_nn hb_nn) hab K
      have hmain : chi zx * chi zy ≤ CK ^ 2 * (R / ℓ) ^ K :=
        le_trans hprod (mul_le_mul_of_nonneg_left hpow (sq_nonneg CK))
      have hscale : chiScale ℓ x * chiScale ℓ y = chi zx * chi zy := by
        simp only [chiScale, hzx, hzy]
      rw [hscale]
      calc chi zx * chi zy ≤ CK ^ 2 * (R / ℓ) ^ K := hmain
        _ ≤ (CK ^ 2 + 1) * (R / ℓ) ^ K := by nlinarith [hbase]
    · -- `y` lies outside the support of `chiScale ℓ`
      have hy0 : chiScale ℓ y = 0 := by
        simp only [chiScale]
        exact Submission.BoseGases.chi_eq_zero_of_half_le_norm _ (not_lt.mp h2)
      rw [hy0, mul_zero]
      exact mul_nonneg (by positivity) hbase
  · -- `x` lies outside the support of `chiScale ℓ`
    have hx0 : chiScale ℓ x = 0 := by
      simp only [chiScale]
      exact Submission.BoseGases.chi_eq_zero_of_half_le_norm _ (not_lt.mp h1)
    rw [hx0, zero_mul]
    exact mul_nonneg (by positivity) hbase

end Work.BoseBoxFock
