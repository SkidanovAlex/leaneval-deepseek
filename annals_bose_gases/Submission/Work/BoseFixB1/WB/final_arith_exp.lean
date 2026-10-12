import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.WB.final_arith_exp` — the `ε`-split arithmetic with the
explicit window constant

This is the last arithmetic step of the particle-window (`windowBridge`, FS
`thm:aprioriHLambda` step 4), in the *explicit-constant* form needed downstream.
The `P/Q`-split bounds the state-averaged density `s` above and below by the
particle number `n`:

  `s ≤ (1+ε)(n − A₀)/ℓ³ + (1+ε⁻¹)(KU/W)A₀`,   `(1−ε)(n − A₀)/ℓ³ − (1+ε⁻¹)(KU/W)A₀ ≤ s`,

where `A₀` is the excited count `n₊` (capped by the a-priori inequality through
`C_A`) and `K := (1+ε⁻¹)(KU/W)A₀` is the split remainder.  From these and
`s = μ(1+O(γε))` the lemma extracts the window `|n − μℓ³| ≤ Cμℓ³ε` with the
*explicit* constant

  `C = 2 + 2C₁ + 4C₂·(2C_A/bValue) + 2C_A/bValue`.

## The bookkeeping

With `c := 2C_A/bValue` (so `A₀ ≤ cμℓ³ε` by the cap and `ε² ≤ ε`), `D := 2C₂c`
(so `ℓ³·max K 0 ≤ Dμℓ³ε` by `KU/W ≤ C₂/ℓ³`, the cap, and
`(1+ε⁻¹)ε² = ε+ε² ≤ 2ε`), and the `s`-window `|s − μ| ≤ C₁με`:

* **lower** (`A := C₁με`, `K₀ := max K 0`): clearing `ℓ³` from
  `s − K₀ ≤ (1+ε)(n−A₀)/ℓ³` and using `A₀ ≥ 0`,
  `(1+ε)(n−μℓ³) ≥ ℓ³(μ−A−K₀) − (1+ε)μℓ³
                 = −C₁μℓ³ε − ℓ³K₀ − εμℓ³ ≥ −(1+C₁+D)μℓ³ε`,
  and `1+C₁+D ≤ C(1+ε)` (as `C ≥ 2+2C₁+2D` and `1+ε ≥ 1`) gives `n−μℓ³ ≥ −Cμℓ³ε`.
* **upper**: clearing `ℓ³` from `(1−ε)(n−A₀)/ℓ³ ≤ s + K₀` and using `s ≤ μ+C₁με`,
  `A₀ ≤ cμℓ³ε`,
  `(1−ε)(n−μℓ³) ≤ ℓ³(μ+C₁με+K₀) + (1−ε)(A₀−μℓ³)
                 ≤ εμℓ³ + C₁μℓ³ε + ℓ³K₀ + (1−ε)cμℓ³ε
                 ≤ (1+C₁+D+(1−ε)c)μℓ³ε`,
  and `1+C₁+D+(1−ε)c ≤ C(1−ε)` because
  `C(1−ε) − (1+C₁+D+(1−ε)c) = (1−2ε)(1+C₁+D) ≥ 0` (here `ε ≤ 1/2` is used),
  giving `n−μℓ³ ≤ Cμℓ³ε`.

The mathematical content is split into a self-contained abstract lemma
`final_arith_exp_aux` (the `ε`-bookkeeping, in terms of the abstract constants
`c`, `D`, `K₀`) and the theorem below (which derives the three input inequalities
from the concrete hypotheses and instantiates `c = 2C_A/bValue`,
`D = 2C₂c`, `K₀ = max ((1+ε⁻¹)(KU/W)A₀) 0`).
-/

namespace Work.BoseFixB1.WB

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-- **The abstract `ε`-bookkeeping of the particle window.**  Given the two
`P/Q`-split inequalities with the split remainder replaced by its positive part
`K₀ = max K 0`, an `s`-window `|s − μ| ≤ C₁με`, a cap `A₀ ≤ cμℓ³ε` on the
excited count and the extraction bound `ℓ³K₀ ≤ Dμℓ³ε`, the particle number is
located within `(2 + 2C₁ + 2D + c)μℓ³ε` of `μℓ³`. -/
lemma final_arith_exp_aux {μ ℓ s ε C₁ D c K0 A₀ : ℝ} {n : ℕ}
    (hμ : 0 < μ) (hℓ : 0 < ℓ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hc : 0 ≤ c) (hC₁ : 0 ≤ C₁) (hDnn : 0 ≤ D) (hA₀ : 0 ≤ A₀)
    (hA₀c : A₀ ≤ c * μ * ℓ ^ 3 * ε)
    (hK0c : ℓ ^ 3 * K0 ≤ D * μ * ℓ ^ 3 * ε)
    (hsge : μ - C₁ * μ * ε ≤ s) (hsle : s ≤ μ + C₁ * μ * ε)
    (h1 : s - K0 ≤ (1 + ε) * ((n : ℝ) - A₀) / ℓ ^ 3)
    (h2 : (1 - ε) * ((n : ℝ) - A₀) / ℓ ^ 3 ≤ s + K0) :
    |(n : ℝ) - μ * ℓ ^ 3| ≤ (2 + 2 * C₁ + 2 * D + c) * μ * ℓ ^ 3 * ε := by
  have hℓ3pos : (0:ℝ) < ℓ^3 := pow_pos hℓ 3
  have hℓ3nn : (0:ℝ) ≤ ℓ^3 := hℓ3pos.le
  have h1pε : (0:ℝ) < 1 + ε := by linarith
  have h1mε : (0:ℝ) < 1 - ε := by linarith
  have hPnn : (0:ℝ) ≤ μ * ℓ^3 * ε := mul_nonneg (mul_nonneg hμ.le hℓ3nn) hε.le
  have hAeq : ℓ^3 * (C₁ * μ * ε) = C₁ * μ * ℓ^3 * ε := by ring
  -- clear the `ℓ³`-denominators in the two split inequalities
  have h1'' : ℓ^3 * (s - K0) ≤ (1 + ε) * ((n:ℝ) - A₀) := by
    have h := mul_le_mul_of_nonneg_right h1 hℓ3nn
    have heq : ((1 + ε) * ((n:ℝ) - A₀) / ℓ^3) * ℓ^3 = (1 + ε) * ((n:ℝ) - A₀) :=
      div_mul_cancel₀ _ (ne_of_gt hℓ3pos)
    linarith [h, heq]
  have h2'' : (1 - ε) * ((n:ℝ) - A₀) ≤ ℓ^3 * (s + K0) := by
    have h := mul_le_mul_of_nonneg_right h2 hℓ3nn
    have heq : ((1 - ε) * ((n:ℝ) - A₀) / ℓ^3) * ℓ^3 = (1 - ε) * ((n:ℝ) - A₀) :=
      div_mul_cancel₀ _ (ne_of_gt hℓ3pos)
    linarith [h, heq]
  -- ---- lower bound: `-(2 + 2C₁ + 2D + c)μℓ³ε ≤ n - μℓ³`
  have hlow : -((2 + 2 * C₁ + 2 * D + c) * μ * ℓ^3 * ε) ≤ (n:ℝ) - μ * ℓ^3 := by
    have hsc : 1 + C₁ + D ≤ (2 + 2 * C₁ + 2 * D + c) * (1 + ε) := by
      have ha : 1 + C₁ + D ≤ 2 + 2 * C₁ + 2 * D + c := by linarith
      have hb : 2 + 2 * C₁ + 2 * D + c ≤ (2 + 2 * C₁ + 2 * D + c) * (1 + ε) := by
        have h := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ 1 + ε by linarith)
          (show (0:ℝ) ≤ 2 + 2 * C₁ + 2 * D + c by linarith)
        simpa using h
      linarith
    have hstep6 : -((2 + 2 * C₁ + 2 * D + c) * (1 + ε) * μ * ℓ^3 * ε)
        ≤ -(1 + C₁ + D) * (μ * ℓ^3 * ε) := by
      have h := mul_le_mul_of_nonneg_right hsc hPnn
      linarith [h]
    have hsK : ℓ^3 * (μ - C₁ * μ * ε - K0) ≤ ℓ^3 * (s - K0) :=
      mul_le_mul_of_nonneg_left (by linarith [hsge]) hℓ3nn
    have hstep : ℓ^3 * (μ - C₁ * μ * ε - K0) ≤ (1 + ε) * ((n:ℝ) - A₀) :=
      le_trans hsK h1''
    have hbig : ℓ^3 * (μ - C₁ * μ * ε - K0) - (1 + ε) * (μ * ℓ^3)
        ≤ (1 + ε) * ((n:ℝ) - μ * ℓ^3) := by
      have heq : (1 + ε) * ((n:ℝ) - μ * ℓ^3)
          = (1 + ε) * ((n:ℝ) - A₀) + (1 + ε) * (A₀ - μ * ℓ^3) := by ring
      have h2b : 0 ≤ (1 + ε) * A₀ := mul_nonneg h1pε.le hA₀
      linarith [heq, hstep, h2b]
    have hmid : -(1 + C₁ + D) * (μ * ℓ^3 * ε)
        ≤ ℓ^3 * (μ - C₁ * μ * ε - K0) - (1 + ε) * (μ * ℓ^3) := by
      have hexp : ℓ^3 * (μ - C₁ * μ * ε - K0) - (1 + ε) * (μ * ℓ^3)
          = -(C₁ * μ * ℓ^3 * ε) - (ℓ^3 * K0) - ε * (μ * ℓ^3) := by
        calc ℓ^3 * (μ - C₁ * μ * ε - K0) - (1 + ε) * (μ * ℓ^3)
            = ℓ^3 * μ - ℓ^3 * (C₁ * μ * ε) - ℓ^3 * K0 - (1 + ε) * (μ * ℓ^3) := by ring
          _ = -(C₁ * μ * ℓ^3 * ε) - (ℓ^3 * K0) - ε * (μ * ℓ^3) := by rw [hAeq]; ring
      have h2c : -(1 + C₁ + D) * (μ * ℓ^3 * ε)
          ≤ -(C₁ * μ * ℓ^3 * ε) - (ℓ^3 * K0) - ε * (μ * ℓ^3) := by
        nlinarith [hK0c]
      linarith [hexp, h2c]
    have hcomb := le_trans hstep6 (le_trans hmid hbig)
    have hfin : (1 + ε) * (-((2 + 2 * C₁ + 2 * D + c) * μ * ℓ^3 * ε))
        ≤ (1 + ε) * ((n:ℝ) - μ * ℓ^3) := by
      have he : (1 + ε) * (-((2 + 2 * C₁ + 2 * D + c) * μ * ℓ^3 * ε))
          = -((2 + 2 * C₁ + 2 * D + c) * (1 + ε) * μ * ℓ^3 * ε) := by ring
      linarith [hcomb, he]
    exact le_of_mul_le_mul_left hfin h1pε
  -- ---- upper bound: `n - μℓ³ ≤ (2 + 2C₁ + 2D + c)μℓ³ε`
  have hup : (n:ℝ) - μ * ℓ^3 ≤ (2 + 2 * C₁ + 2 * D + c) * μ * ℓ^3 * ε := by
    have hsc : 1 + C₁ + D + (1 - ε) * c ≤ (2 + 2 * C₁ + 2 * D + c) * (1 - ε) := by
      have hE : (0:ℝ) ≤ 1 - 2 * ε := by linarith
      have hF : (0:ℝ) ≤ 1 + C₁ + D := by linarith
      nlinarith [mul_nonneg hE hF]
    have hstep6 : (1 + C₁ + D + (1 - ε) * c) * (μ * ℓ^3 * ε)
        ≤ (2 + 2 * C₁ + 2 * D + c) * (1 - ε) * μ * ℓ^3 * ε := by
      have h := mul_le_mul_of_nonneg_right hsc hPnn
      linarith [h]
    have hsK : ℓ^3 * (s + K0) ≤ ℓ^3 * (μ + C₁ * μ * ε + K0) :=
      mul_le_mul_of_nonneg_left (by linarith [hsle]) hℓ3nn
    have hstep : (1 - ε) * ((n:ℝ) - A₀) ≤ ℓ^3 * (μ + C₁ * μ * ε + K0) :=
      le_trans h2'' hsK
    have hbig : (1 - ε) * ((n:ℝ) - μ * ℓ^3)
        ≤ ℓ^3 * (μ + C₁ * μ * ε + K0) + (1 - ε) * (A₀ - μ * ℓ^3) := by
      have heq : (1 - ε) * ((n:ℝ) - μ * ℓ^3)
          = (1 - ε) * ((n:ℝ) - A₀) + (1 - ε) * (A₀ - μ * ℓ^3) := by ring
      linarith [heq, hstep]
    have hmid : ℓ^3 * (μ + C₁ * μ * ε + K0) + (1 - ε) * (A₀ - μ * ℓ^3)
        ≤ (1 + C₁ + D + (1 - ε) * c) * (μ * ℓ^3 * ε) := by
      have hA0part : (1 - ε) * A₀ ≤ (1 - ε) * (c * μ * ℓ^3 * ε) :=
        mul_le_mul_of_nonneg_left hA₀c h1mε.le
      have hexp : ℓ^3 * (μ + C₁ * μ * ε + K0) + (1 - ε) * (A₀ - μ * ℓ^3)
          ≤ ε * (μ * ℓ^3) + C₁ * μ * ℓ^3 * ε + ℓ^3 * K0 + (1 - ε) * (c * μ * ℓ^3 * ε) := by
        nlinarith [hA0part, hAeq]
      have hfinal : ε * (μ * ℓ^3) + C₁ * μ * ℓ^3 * ε + ℓ^3 * K0 + (1 - ε) * (c * μ * ℓ^3 * ε)
          ≤ (1 + C₁ + D + (1 - ε) * c) * (μ * ℓ^3 * ε) := by
        nlinarith [hK0c]
      linarith [hexp, hfinal]
    have hcomb := le_trans hbig (le_trans hmid hstep6)
    have hfin : (1 - ε) * ((n:ℝ) - μ * ℓ^3)
        ≤ (1 - ε) * ((2 + 2 * C₁ + 2 * D + c) * μ * ℓ^3 * ε) := by
      have he : (1 - ε) * ((2 + 2 * C₁ + 2 * D + c) * μ * ℓ^3 * ε)
          = (2 + 2 * C₁ + 2 * D + c) * (1 - ε) * μ * ℓ^3 * ε := by ring
      linarith [hcomb, he]
    exact le_of_mul_le_mul_left hfin h1mε
  exact abs_le.mpr ⟨hlow, hup⟩

theorem final_arith_exp {μ ℓ W s C_A ε γ C₁ C₂ KU A₀ : ℝ}
    (hμ : 0 < μ) (hℓ : 0 < ℓ) (hW : 0 < W) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hγ : 0 ≤ γ)
    (hγε : γ ≤ ε) (hCA : 0 ≤ C_A) (hA₀ : 0 ≤ A₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hA₀cap : A₀ ≤ (2 * C_A / Work.BoseBox.bValue) * μ * ℓ ^ 3 * ε ^ 2)
    (hs : |s - μ| ≤ C₁ * μ * γ)
    (hKUW : KU / W ≤ C₂ / ℓ ^ 3) :
    ∀ {n : ℕ},
      (s ≤ (1 + ε) * ((n : ℝ) - A₀) / ℓ ^ 3 + (1 + ε⁻¹) * (KU / W) * A₀) →
      ((1 - ε) * ((n : ℝ) - A₀) / ℓ ^ 3 - (1 + ε⁻¹) * (KU / W) * A₀ ≤ s) →
      |(n : ℝ) - μ * ℓ ^ 3|
        ≤ (2 + 2 * C₁ + 4 * C₂ * (2 * C_A / Work.BoseBox.bValue)
            + 2 * C_A / Work.BoseBox.bValue) * μ * ℓ ^ 3 * ε := by
  intro n h1 h2
  have hbpos : (0:ℝ) < Work.BoseBox.bValue := by norm_num [Work.BoseBox.bValue]
  have hℓ3pos : (0:ℝ) < ℓ^3 := pow_pos hℓ 3
  have hℓ3nn : (0:ℝ) ≤ ℓ^3 := hℓ3pos.le
  have hc : (0:ℝ) ≤ 2 * C_A / Work.BoseBox.bValue := div_nonneg (by linarith) hbpos.le
  have hDnn : (0:ℝ) ≤ 2 * C₂ * (2 * C_A / Work.BoseBox.bValue) := by
    have h1 : (0:ℝ) ≤ 2 * C₂ := by linarith
    exact mul_nonneg h1 hc
  have hεsq : ε^2 ≤ ε := by nlinarith [mul_nonneg hε.le (by linarith : (0:ℝ) ≤ 1 - ε)]
  -- the `s`-window, with `γ ≤ ε`
  have hCμγ : C₁ * μ * γ ≤ C₁ * μ * ε := by
    have h := mul_le_mul_of_nonneg_left hγε (mul_nonneg hC₁ hμ.le)
    linarith [h]
  have hsle : s ≤ μ + C₁ * μ * ε := by
    have h := (abs_le.mp hs).2
    linarith [h, hCμγ]
  have hsge : μ - C₁ * μ * ε ≤ s := by
    have h := (abs_le.mp hs).1
    linarith [h, hCμγ]
  -- the excited-count cap, in the linear form `A₀ ≤ cμℓ³ε`
  have hA₀c : A₀ ≤ (2 * C_A / Work.BoseBox.bValue) * μ * ℓ ^ 3 * ε := by
    have h0 : (0:ℝ) ≤ (2 * C_A / Work.BoseBox.bValue) * μ * ℓ ^ 3 :=
      mul_nonneg (mul_nonneg hc hμ.le) hℓ3nn
    have hmono := mul_le_mul_of_nonneg_left hεsq h0
    linarith [hA₀cap, hmono]
  -- the split remainder and its extraction bound
  set K0 := max ((1 + ε⁻¹) * (KU / W) * A₀) 0 with hK0def
  have hK0nn : 0 ≤ K0 := by rw [hK0def]; exact le_max_right _ _
  have hKle : (1 + ε⁻¹) * (KU / W) * A₀ ≤ K0 := by rw [hK0def]; exact le_max_left _ _
  have h1' : s - K0 ≤ (1 + ε) * ((n : ℝ) - A₀) / ℓ ^ 3 := by linarith [h1, hKle]
  have h2' : (1 - ε) * ((n : ℝ) - A₀) / ℓ ^ 3 ≤ s + K0 := by linarith [h2, hKle]
  have hK0c : ℓ ^ 3 * K0 ≤ (2 * C₂ * (2 * C_A / Work.BoseBox.bValue)) * μ * ℓ ^ 3 * ε := by
    have hLnn : (0:ℝ) ≤ 1 + ε⁻¹ := by
      have : (0:ℝ) ≤ ε⁻¹ := inv_nonneg.mpr hε.le
      linarith
    have hK0le0 : K0 ≤ (1 + ε⁻¹) * (C₂ / ℓ^3) * A₀ := by
      rw [hK0def]
      refine max_le ?_ ?_
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKUW hLnn) hA₀
      · exact mul_nonneg (mul_nonneg hLnn (div_nonneg hC₂ hℓ3nn)) hA₀
    have step1 : ℓ^3 * K0 ≤ (1 + ε⁻¹) * C₂ * A₀ := by
      have h := mul_le_mul_of_nonneg_left hK0le0 hℓ3nn
      have heq : ℓ^3 * ((1 + ε⁻¹) * (C₂ / ℓ^3) * A₀) = (1 + ε⁻¹) * C₂ * A₀ := by
        calc ℓ^3 * ((1 + ε⁻¹) * (C₂ / ℓ^3) * A₀)
            = (1 + ε⁻¹) * A₀ * (ℓ^3 * (C₂ / ℓ^3)) := by ring
          _ = (1 + ε⁻¹) * A₀ * C₂ := by rw [mul_div_cancel₀ C₂ (ne_of_gt hℓ3pos)]
          _ = (1 + ε⁻¹) * C₂ * A₀ := by ring
      linarith [h, heq]
    have step2 : (1 + ε⁻¹) * C₂ * A₀
        ≤ (1 + ε⁻¹) * C₂ * ((2 * C_A / Work.BoseBox.bValue) * μ * ℓ^3 * ε^2) :=
      mul_le_mul_of_nonneg_left hA₀cap (mul_nonneg hLnn hC₂)
    have hεsq2 : (1 + ε⁻¹) * ε^2 ≤ 2 * ε := by
      have hne : ε ≠ 0 := ne_of_gt hε
      have hsplit : (1 + ε⁻¹) * ε^2 = ε^2 + ε := by
        calc (1 + ε⁻¹) * ε^2 = ε^2 + ε⁻¹ * (ε * ε) := by rw [add_mul, one_mul, sq]
          _ = ε^2 + (ε⁻¹ * ε) * ε := by ring
          _ = ε^2 + ε := by rw [inv_mul_cancel₀ hne, one_mul]
      rw [hsplit]
      nlinarith [hεsq]
    have step3 : (1 + ε⁻¹) * C₂ * ((2 * C_A / Work.BoseBox.bValue) * μ * ℓ^3 * ε^2)
        ≤ (2 * C₂ * (2 * C_A / Work.BoseBox.bValue)) * μ * ℓ^3 * ε := by
      have hfac : (0:ℝ) ≤ C₂ * (2 * C_A / Work.BoseBox.bValue) * (μ * ℓ^3) :=
        mul_nonneg (mul_nonneg hC₂ hc) (mul_nonneg hμ.le hℓ3nn)
      have hmul := mul_le_mul_of_nonneg_left hεsq2 hfac
      linarith [hmul]
    linarith [step1, step2, step3]
  have key := final_arith_exp_aux (μ := μ) (ℓ := ℓ) (s := s) (ε := ε) (C₁ := C₁)
    (D := 2 * C₂ * (2 * C_A / Work.BoseBox.bValue)) (c := 2 * C_A / Work.BoseBox.bValue)
    (K0 := K0) (A₀ := A₀) (n := n)
    hμ hℓ hε hε1 hc hC₁ hDnn hA₀ hA₀c hK0c hsge hsle h1' h2'
  exact le_trans key (le_of_eq (by ring))

end Work.BoseFixB1.WB
