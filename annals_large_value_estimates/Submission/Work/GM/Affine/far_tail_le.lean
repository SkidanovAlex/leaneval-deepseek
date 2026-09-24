import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.WinMass_fejer_defs
import Submission.Work.GM.Affine.winMass_le_fejer
import Submission.Work.GM.Affine.far_mass_le
import Submission.Work.GM.Affine.norm_Bsum_le_decay
import Submission.Work.GM.Affine.sq_integral_le_of_support
import Submission.Work.GM.Affine.far_tail_integral_le_decay

/-!
# GM §9: the far-frequency tail of the `m₂`-sum is dominated by `M₂² M₃ ∫ f²`

The target `Work.GM.Affine.far_tail_le` bounds the `L²`-mass of the `m₂`-sum
`Bsum f M₂ x = Σ_{m₂ ∈ R2 M₂} m₂ f̂(m₂ x)`, weighted by the Fejér kernel, on the *far* set
`|x| > T^{δ/2} T / M₂`.

The route is elementary (no Poisson/Farey input is needed):

* on the far set every term of the sum sits above frequency `T^{δ/2} T`, so the all-orders decay
  hypothesis `‖f̂(ξ)‖ ≤ c j ε · T^ε (T/|ξ|)^j Λ` and the crude count `Σ_{m₂ ∈ R2 M₂} m₂ ≤ 4M₂²`
  give the *pointwise* bound `‖Bsum f M₂ x‖ ≤ 4M₂² (c j ε T^ε Λ) (T/(M₂|x|))^j`
  (`Work.GM.Affine.norm_Bsum_le_decay`);
* `fejerK M₃ ≤ M₃` for `M₃ ≥ 1` (`fejerK_le_of_one_le` below) turns the weighted integral into an
  integral of `(T/(M₂|x|))^{2j}`, whose value is the explicit `integral_abs_div_pow`
  (`Work.GM.Affine.far_tail_integral_le_decay`);
* the remaining steps are arithmetic: `Λ² ≤ (16 c 2 1 T³ ∫f)²`, `(∫f)² ≤ C₀ ∫f²`
  (`Work.GM.Affine.sq_integral_le_of_support`), `M₂³ ≤ M₂² T⁴` and the choice of `j` (a fixed
  function of `δ`), which makes the surviving power of `T` negative.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.GM.Affine

noncomputable section

/-- For `M₃ ≥ 1` the Fejér kernel is bounded by `M₃` (its order `fejerN M₃` is at most `M₃`). -/
lemma fejerK_le_of_one_le {M₃ : ℝ} (hM₃ : 1 ≤ M₃) (x : ℝ) : fejerK M₃ x ≤ M₃ := by
  by_cases h8 : M₃ < 8
  · rw [fejerK_eq_one_of_lt_eight h8]; exact hM₃
  · have h8' : (8:ℝ) ≤ M₃ := not_lt.mp h8
    have h1 : fejerK M₃ x ≤ |fejerK M₃ x| := le_abs_self _
    have h2 : |fejerK M₃ x| ≤ 2 * (fejerN M₃ : ℝ) := fejerK_abs_le M₃ x
    have hN : fejerN M₃ = ⌊M₃ / 8⌋₊ := by
      rw [fejerN]
      exact max_eq_right (Nat.le_floor (by push_cast; linarith))
    have h3 : (fejerN M₃ : ℝ) ≤ M₃ / 8 := by rw [hN]; exact Nat.floor_le (by linarith)
    linarith

theorem far_tail_le {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, 1 ≤ T → 2 * C₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) →
        SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ M₂ : ℝ, 1 ≤ M₂ → M₂ ≤ T ^ 4 → ∀ M₃ : ℝ, 1 ≤ M₃ →
          (∫ x in {x : ℝ | T ^ (δ / 2) * T / M₂ < |x|},
              ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x)
            ≤ C * M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2 := by
  have hC₀pos : 0 < C₀ := by linarith
  -- the two parameters of the argument: `ε = δ/2` and the (large, `δ`-dependent) power `j`
  set ε : ℝ := δ / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  set j : ℕ := Nat.ceil ((11 + 2 * δ) / δ) + 2 with hjdef
  have hj2 : 2 ≤ j := by rw [hjdef]; omega
  have hj1 : 1 ≤ j := by omega
  have hDpos : 0 < 2 * (j : ℝ) - 1 := by
    have : (2:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj2
    linarith
  set X : ℝ := 32 * 256 * C₀ * (c j ε) ^ 2 * (c 2 1) ^ 2 / (2 * (j : ℝ) - 1) with hXdef
  have hXnn : 0 ≤ X := by rw [hXdef]; positivity
  refine ⟨X + 1, by linarith, ?_⟩
  intro T hT h2C₀ f hf hnn hs Λ hΛ hdec hcompat M₂ hM₂ hM₂T M₃ hM₃
  have hTpos : (0:ℝ) < T := by linarith
  have hM₂pos : 0 < M₂ := by linarith
  have hM₃nn : 0 ≤ M₃ := by linarith
  have hΛnn : 0 ≤ Λ := le_of_lt hΛ
  have hTε : 0 < T ^ ε := Real.rpow_pos_of_pos hTpos ε
  -- `c j ε ≥ 0` is forced by the decay hypothesis and `Λ > 0`
  have hcj : 0 ≤ c j ε := by
    have h1 := hdec j ε hεpos 1 one_ne_zero
    have h1' : 0 ≤ c j ε * T ^ ε * (T / |(1:ℝ)|) ^ j * Λ := le_trans (norm_nonneg _) h1
    have hP : 0 < T ^ ε * (T / |(1:ℝ)|) ^ j * Λ := by positivity
    have h2 : 0 ≤ c j ε * (T ^ ε * (T / |(1:ℝ)|) ^ j * Λ) := by
      simpa only [mul_assoc] using h1'
    exact (mul_nonneg_iff_of_pos_right hP).mp h2
  -- the pointwise decay bound on the far set
  have hbound : ∀ x ∈ {x : ℝ | T ^ (δ / 2) * T / M₂ < |x|},
      ‖Bsum f M₂ x‖ ≤ (4 * M₂ ^ 2 * (c j ε * T ^ ε * Λ)) * (T / (M₂ * |x|)) ^ j := by
    intro x hx
    have hxne : x ≠ 0 := by
      intro h0
      have hx' : T ^ (δ / 2) * T / M₂ < |x| := hx
      rw [h0, abs_zero] at hx'
      have hR : 0 < T ^ (δ / 2) * T / M₂ := by positivity
      linarith
    exact norm_Bsum_le_decay hTpos hΛnn hcj hM₂ (fun ξ hξ => hdec j ε hεpos ξ hξ) hxne
  have hfejer : ∀ x : ℝ, fejerK M₃ x ≤ M₃ := fun x => fejerK_le_of_one_le hM₃ x
  have hfar := far_tail_integral_le_decay (A := 4 * M₂ ^ 2 * (c j ε * T ^ ε * Λ))
      hT hδ hM₂pos hM₃nn hj1 (by positivity) hfejer hbound
  -- the size condition that makes the remaining power of `T` non-positive
  have hE1 : 11 + δ ≤ (δ / 2) * (2 * (j : ℝ) - 1) := by
    have hdj : 11 + 2 * δ ≤ δ * (j : ℝ) := by
      rw [hjdef]
      push_cast
      have hc : (11 + 2 * δ) / δ ≤ ((Nat.ceil ((11 + 2 * δ) / δ) : ℕ) : ℝ) := Nat.le_ceil _
      have h1 : (11 + 2 * δ) / δ * δ ≤ ((Nat.ceil ((11 + 2 * δ) / δ) : ℕ) : ℝ) * δ :=
        mul_le_mul_of_nonneg_right hc (le_of_lt hδ)
      rw [div_mul_cancel₀ _ (ne_of_gt hδ)] at h1
      nlinarith [h1, hδ]
    nlinarith [hdj, hδ]
  have hTE : T ^ (2 * ε) * T ^ (1 - (δ / 2) * (2 * (j : ℝ) - 1)) * T ^ (4:ℕ) * T ^ (6:ℕ) ≤ 1 := by
    have hexp : 2 * ε + (1 - (δ / 2) * (2 * (j : ℝ) - 1)) + 10 ≤ 0 := by
      rw [hεdef]; linarith [hE1]
    calc T ^ (2 * ε) * T ^ (1 - (δ / 2) * (2 * (j : ℝ) - 1)) * T ^ (4:ℕ) * T ^ (6:ℕ)
        = T ^ (2 * ε) * T ^ (1 - (δ / 2) * (2 * (j : ℝ) - 1)) * T ^ (10:ℕ) := by
          rw [mul_assoc, ← pow_add]
      _ = T ^ (2 * ε + (1 - (δ / 2) * (2 * (j : ℝ) - 1)) + 10) := by
          rw [← Real.rpow_natCast T 10, ← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
          push_cast
          ring
      _ ≤ T ^ (0:ℝ) := Real.rpow_le_rpow_of_exponent_le hT hexp
      _ = 1 := Real.rpow_zero T
  have hΛ2 : Λ ^ 2 ≤ 256 * (c 2 1) ^ 2 * T ^ (6:ℕ) * (∫ u, f u) ^ 2 := by
    have h1 : Λ ^ 2 ≤ (16 * c 2 1 * T ^ 3 * ∫ u, f u) ^ 2 := by nlinarith [hΛ, hcompat]
    calc Λ ^ 2 ≤ (16 * c 2 1 * T ^ 3 * ∫ u, f u) ^ 2 := h1
      _ = 256 * (c 2 1) ^ 2 * T ^ (6:ℕ) * (∫ u, f u) ^ 2 := by ring
  have hCS : (∫ u, f u) ^ 2 ≤ C₀ * ∫ u, (f u) ^ 2 := by
    have hab : 1 / C₀ ≤ C₀ := by rw [div_le_iff₀ hC₀pos]; nlinarith [hC₀]
    have h1 := sq_integral_le_of_support (a := 1 / C₀) (b := C₀) hab hf hnn hs
    have h2 : 0 < 1 / C₀ := by positivity
    have h3 : C₀ - 1 / C₀ ≤ C₀ := by linarith
    have h4 : 0 ≤ ∫ u, (f u) ^ 2 := integral_nonneg (fun u => sq_nonneg _)
    linarith [mul_le_mul_of_nonneg_right h3 h4]
  have hM₂3 : M₂ ^ 3 ≤ M₂ ^ 2 * T ^ (4:ℕ) := by
    calc M₂ ^ 3 = M₂ ^ 2 * M₂ := by ring
      _ ≤ M₂ ^ 2 * T ^ 4 := mul_le_mul_of_nonneg_left hM₂T (by positivity)
  have hIf2nn : 0 ≤ ∫ u, (f u) ^ 2 := integral_nonneg (fun u => sq_nonneg _)
  -- the purely arithmetic core
  have hNum : 32 * M₂^3 * M₃ * (c j ε)^2 * T^(2*ε) * T^(1 - (δ/2)*(2*(j:ℝ)-1)) * Λ^2
      ≤ 32 * 256 * C₀ * (c j ε)^2 * (c 2 1)^2 * M₂^2 * M₃ * ∫ u, (f u)^2 := by
    have hK1 : (0:ℝ) ≤ 32 * M₃ * (c j ε)^2 * T^(2*ε) * T^(1-(δ/2)*(2*(j:ℝ)-1)) * Λ^2 := by positivity
    have hK2 : (0:ℝ) ≤ 32 * (M₂^2 * T^4) * M₃ * (c j ε)^2 * T^(2*ε) * T^(1-(δ/2)*(2*(j:ℝ)-1)) := by positivity
    have hK3 : (0:ℝ) ≤ 32 * 256 * (c j ε)^2 * (c 2 1)^2 * M₂^2 * M₃ * (∫ u, f u)^2 := by positivity
    have hK4 : (0:ℝ) ≤ 32 * 256 * (c j ε)^2 * (c 2 1)^2 * M₂^2 * M₃ * 1 := by positivity
    have step1 : 32 * M₂^3 * M₃ * (c j ε)^2 * T^(2*ε) * T^(1 - (δ/2)*(2*(j:ℝ)-1)) * Λ^2
        ≤ 32 * (M₂^2 * T^4) * M₃ * (c j ε)^2 * T^(2*ε) * T^(1 - (δ/2)*(2*(j:ℝ)-1)) * Λ^2 := by
      nlinarith [mul_le_mul_of_nonneg_right hM₂3 hK1]
    have step2 : 32 * (M₂^2 * T^4) * M₃ * (c j ε)^2 * T^(2*ε) * T^(1-(δ/2)*(2*(j:ℝ)-1)) * Λ^2
        ≤ 32 * (M₂^2 * T^4) * M₃ * (c j ε)^2 * T^(2*ε) * T^(1-(δ/2)*(2*(j:ℝ)-1))
            * (256 * (c 2 1)^2 * T^(6:ℕ) * (∫ u, f u)^2) := by
      nlinarith [mul_le_mul_of_nonneg_left hΛ2 hK2]
    have stepC : 32 * 256 * (c j ε)^2 * (c 2 1)^2 * M₂^2 * M₃ * (∫ u, f u)^2
            * (T^(2*ε) * T^(1-(δ/2)*(2*(j:ℝ)-1)) * T^4 * T^6)
        ≤ 32 * 256 * (c j ε)^2 * (c 2 1)^2 * M₂^2 * M₃ * (∫ u, f u)^2 * 1 := by
      nlinarith [mul_le_mul_of_nonneg_left hTE hK3]
    have stepD : 32 * 256 * (c j ε)^2 * (c 2 1)^2 * M₂^2 * M₃ * (∫ u, f u)^2 * 1
        ≤ 32 * 256 * (c j ε)^2 * (c 2 1)^2 * M₂^2 * M₃ * (C₀ * ∫ u, (f u)^2) * 1 := by
      nlinarith [mul_le_mul_of_nonneg_right hCS hK4]
    calc 32 * M₂^3 * M₃ * (c j ε)^2 * T^(2*ε) * T^(1 - (δ/2)*(2*(j:ℝ)-1)) * Λ^2
        ≤ 32 * (M₂^2 * T^4) * M₃ * (c j ε)^2 * T^(2*ε) * T^(1 - (δ/2)*(2*(j:ℝ)-1)) * Λ^2 := step1
      _ ≤ 32 * (M₂^2 * T^4) * M₃ * (c j ε)^2 * T^(2*ε) * T^(1-(δ/2)*(2*(j:ℝ)-1))
            * (256 * (c 2 1)^2 * T^(6:ℕ) * (∫ u, f u)^2) := step2
      _ = 32 * 256 * (c j ε)^2 * (c 2 1)^2 * M₂^2 * M₃ * (∫ u, f u)^2
            * (T^(2*ε) * T^(1-(δ/2)*(2*(j:ℝ)-1)) * T^4 * T^6) := by ring
      _ ≤ 32 * 256 * (c j ε)^2 * (c 2 1)^2 * M₂^2 * M₃ * (∫ u, f u)^2 * 1 := stepC
      _ ≤ 32 * 256 * (c j ε)^2 * (c 2 1)^2 * M₂^2 * M₃ * (C₀ * ∫ u, (f u)^2) * 1 := stepD
      _ = 32 * 256 * C₀ * (c j ε)^2 * (c 2 1)^2 * M₂^2 * M₃ * ∫ u, (f u)^2 := by ring
  -- assemble: the explicit `far_tail_integral_le_decay` bound is `≤ X * M₂² M₃ ∫f²`
  have hfin : (4 * M₂ ^ 2 * (c j ε * T ^ ε * Λ)) ^ 2 * M₃
        * (2 * T ^ (1 - (δ / 2) * (2 * (j : ℝ) - 1)) / (2 * (j : ℝ) - 1)) / M₂
      ≤ X * M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2 := by
    have hM₂ne : M₂ ≠ 0 := ne_of_gt hM₂pos
    have hDne : 2 * (j : ℝ) - 1 ≠ 0 := ne_of_gt hDpos
    have hA2 : (4 * M₂ ^ 2 * (c j ε * T ^ ε * Λ)) ^ 2
        = 16 * M₂ ^ 4 * (c j ε) ^ 2 * T ^ (2 * ε) * Λ ^ 2 := by
      have hTε2 : (T ^ ε) ^ 2 = T ^ (2 * ε) := by
        rw [← Real.rpow_natCast (T ^ ε) 2, ← Real.rpow_mul hTpos.le]; ring
      calc (4 * M₂ ^ 2 * (c j ε * T ^ ε * Λ)) ^ 2
          = 16 * M₂ ^ 4 * (c j ε) ^ 2 * (T ^ ε) ^ 2 * Λ ^ 2 := by ring_nf
        _ = 16 * M₂ ^ 4 * (c j ε) ^ 2 * T ^ (2 * ε) * Λ ^ 2 := by rw [hTε2]
    rw [hA2]
    have hLHS : 16 * M₂ ^ 4 * (c j ε) ^ 2 * T ^ (2 * ε) * Λ ^ 2 * M₃
          * (2 * T ^ (1 - (δ/2)*(2*(j:ℝ)-1)) / (2*(j:ℝ)-1)) / M₂
        = 32 * (M₂^3 * M₃ * (c j ε)^2 * T^(2*ε) * T^(1-(δ/2)*(2*(j:ℝ)-1)) * Λ^2)
            / (2*(j:ℝ)-1) := by
      field_simp
      try ring_nf
    rw [hLHS]
    have hRHS : X * M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2
        = (32 * 256 * C₀ * (c j ε)^2 * (c 2 1)^2) * (M₂^2 * M₃ * ∫ u, (f u)^2)
            / (2*(j:ℝ)-1) := by
      rw [hXdef]; field_simp; try ring_nf
    rw [hRHS]
    exact div_le_div_of_nonneg_right (by nlinarith [hNum]) hDpos.le
  have hlast : X * M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2
      ≤ (X + 1) * M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2 := by
    have h1 : X ≤ X + 1 := by linarith
    have h2 : (0:ℝ) ≤ M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2 := by
      have := hIf2nn; positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  exact le_trans (le_trans hfar hfin) hlast

end

end Work.GM.Affine
