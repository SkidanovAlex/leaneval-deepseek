import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.abs_wSmallScaled_div_convScale_le
import Submission.Work.MGroupInput.newtonianSharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Assembly pieces for `Work.BoseFixB1S.slidingNewtonMassSharpB1`

This module holds the (child-independent) machinery of the sharp sliding Newtonian-mass
bound of FS `eq:appw1sliding` / `eq:I2-integral` for the TWO-factor renormalised kernel

    𝒲 = wSmallScaled M (ℓ·d) (g₀) / convScale ℓ = g₀ / ( (χ_M⋆χ_M)(·/(ℓd)) · (χ⋆χ)(·/ℓ) ) :

* `sharp_factor_arith` — the pure arithmetic converting the squared diluteness factor
  `(1 + A·U + B·V)²` into `1 + K·(V+U)` with `K = (2 + A/256 + B·chiR0²)·max A B`
  (`U = (R/(ℓd))² ≤ 1/256`, `V = (R/ℓ)² ≤ chiR0²`);
* `aestronglyMeasurable_slidingKernel` / `integrable_slidingKernel_of_abs_le` — (a.e.)
  strong measurability and integrability of `𝒲` from an a.e. domination by `g₀`;
* **`slidingNewtonMassSharp_of_pieces`** — the full assembly of the target statement,
  with the four mathematical inputs (the two global quadratic deviations of the
  self-convolutions, the sharp pointwise comparison with `g₀`, and the general
  Newtonian-mass inequality) taken as hypotheses, so that it can be proved and checked
  independently of the children supplying those inputs.
-/

namespace Work.BoseFixB1S

open MeasureTheory Metric
open scoped Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- **Arithmetic of the diluteness factor.**  With `U ≤ (1/16)²`, `V ≤ chiR0²` and
`A, B ≥ 0`, one has `(1 + A·U + B·V)² ≤ 1 + K·(V+U)` for
`K := (2 + A·(1/16)² + B·chiR0²)·max A B`. -/
lemma sharp_factor_arith {A B U V chiR0 : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) (hU : U ≤ (1 / 16) ^ 2) (hV : V ≤ chiR0 ^ 2) :
    (1 + (A * U + B * V)) ^ 2
      ≤ 1 + ((2 + (A * (1 / 16) ^ 2 + B * chiR0 ^ 2)) * max A B) * (V + U) := by
  set δ : ℝ := A * U + B * V with hδdef
  set M₀ : ℝ := A * (1 / 16) ^ 2 + B * chiR0 ^ 2 with hM₀def
  have hδ0 : 0 ≤ δ := by
    rw [hδdef]
    exact add_nonneg (mul_nonneg hA hU0) (mul_nonneg hB hV0)
  have hM00 : 0 ≤ M₀ := by
    rw [hM₀def]
    exact add_nonneg (mul_nonneg hA (by norm_num)) (mul_nonneg hB (sq_nonneg _))
  have hδM : δ ≤ M₀ := by
    rw [hδdef, hM₀def]
    exact add_le_add (mul_le_mul_of_nonneg_left hU hA) (mul_le_mul_of_nonneg_left hV hB)
  have hδsq : δ ^ 2 ≤ M₀ * δ := by
    have h := mul_le_mul_of_nonneg_right hδM hδ0
    simpa [pow_two] using h
  have hmaxA : A ≤ max A B := le_max_left _ _
  have hmaxB : B ≤ max A B := le_max_right _ _
  have h2M0 : 0 ≤ 2 + M₀ := by linarith
  have hstep : δ ≤ max A B * (U + V) := by
    calc δ = A * U + B * V := rfl
      _ ≤ max A B * U + max A B * V :=
          add_le_add (mul_le_mul_of_nonneg_right hmaxA hU0)
            (mul_le_mul_of_nonneg_right hmaxB hV0)
      _ = max A B * (U + V) := by ring
  calc (1 + δ) ^ 2 = 1 + 2 * δ + δ ^ 2 := by ring
    _ ≤ 1 + 2 * δ + M₀ * δ := by linarith
    _ = 1 + (2 + M₀) * δ := by ring
    _ ≤ 1 + (2 + M₀) * (max A B * (U + V)) := by
        have h := mul_le_mul_of_nonneg_left hstep h2M0
        linarith
    _ = 1 + ((2 + M₀) * max A B) * (V + U) := by ring

/-- **Strong measurability of the two-factor renormalised kernel** (a.e. form, which is
all that is needed since `g₀` is only known to be a.e. strongly measurable). -/
lemma aestronglyMeasurable_slidingKernel {g : E3 → ℝ} {ℓ d : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (hGm : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (fun x : E3 =>
        Submission.BoseGases.wSmallScaled M (ℓ * d) g x
          / Submission.BoseGases.convScale ℓ x) volume := by
  have hcont1 : Continuous (fun x : E3 => Submission.BoseGases.convScaleSmall M (ℓ * d) x) :=
    (Submission.BoseGases.conv3Small_continuous hM).comp (continuous_id.const_smul ((ℓ * d)⁻¹))
  have hmeas1 : Measurable (fun x : E3 => (Submission.BoseGases.convScaleSmall M (ℓ * d) x)⁻¹) :=
    hcont1.measurable.inv
  have hWsm : AEStronglyMeasurable (fun x : E3 =>
      Submission.BoseGases.wSmallScaled M (ℓ * d) g x) volume := by
    have hprod : AEStronglyMeasurable (fun x : E3 =>
        g x * (Submission.BoseGases.convScaleSmall M (ℓ * d) x)⁻¹) volume :=
      hGm.mul hmeas1.aestronglyMeasurable
    refine hprod.congr ?_
    filter_upwards with x
    simp [Submission.BoseGases.wSmallScaled, div_eq_mul_inv]
  have hcont2 : Continuous (fun x : E3 => Submission.BoseGases.convScale ℓ x) :=
    (Submission.BoseGases.conv_contDiff.continuous).comp (continuous_id.const_smul ((ℓ)⁻¹))
  have hmeas2 : Measurable (fun x : E3 => (Submission.BoseGases.convScale ℓ x)⁻¹) :=
    hcont2.measurable.inv
  have hdiv : AEStronglyMeasurable (fun x : E3 =>
      Submission.BoseGases.wSmallScaled M (ℓ * d) g x
        * (Submission.BoseGases.convScale ℓ x)⁻¹) volume :=
    hWsm.mul hmeas2.aestronglyMeasurable
  exact hdiv.congr (Filter.Eventually.of_forall (fun x => by simp [div_eq_mul_inv]))

/-- **Integrability of the two-factor renormalised kernel** from an a.e. domination by
`(1+δ)·g` (and the integrability of `g`). -/
lemma integrable_slidingKernel_of_abs_le {g : E3 → ℝ} {ℓ d δ : ℝ} {M : ℕ} (hδ : 0 ≤ δ)
    (hWm : AEStronglyMeasurable (fun x : E3 =>
        Submission.BoseGases.wSmallScaled M (ℓ * d) g x
          / Submission.BoseGases.convScale ℓ x) volume)
    (hGI : Integrable g)
    (hbd : ∀ᵐ x : E3, |Submission.BoseGases.wSmallScaled M (ℓ * d) g x
        / Submission.BoseGases.convScale ℓ x| ≤ (1 + δ) * g x) :
    Integrable (fun x : E3 =>
      Submission.BoseGases.wSmallScaled M (ℓ * d) g x / Submission.BoseGases.convScale ℓ x) := by
  refine Integrable.mono' (hGI.const_mul (1 + δ)) hWm ?_
  filter_upwards [hbd] with x hx
  rwa [Real.norm_eq_abs]

/-- **The sharp sliding Newtonian mass from its four pieces.**  Taking as hypotheses the two
global quadratic deviations of the self-convolutions (`hdevChi`, `hdevSmall`), the sharp
pointwise comparison (`hsharp`) and the general Newtonian-mass inequality (`hnewton`), the
target bound holds with
`K = (2 + (2C₂/smallConvLower M)/256 + (2C₁)·chiR0²)·max (2C₂/smallConvLower M) (2C₁)`. -/
theorem slidingNewtonMassSharp_of_pieces {v : E3 → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M)
    (hdevChi : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : E3,
      |Submission.BoseGases.conv3 Submission.BoseGases.chi
        Submission.BoseGases.chi t - 1| ≤ C * ‖t‖ ^ 2)
    (hdevSmall : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : E3,
      |Submission.BoseGases.conv3Small M t - 1| ≤ C * ‖t‖ ^ 2)
    (hsharp : ∀ {C₁ C₂ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
      (hC₁ : ∀ t : E3, |Submission.BoseGases.conv3 Submission.BoseGases.chi
        Submission.BoseGases.chi t - 1| ≤ C₁ * ‖t‖ ^ 2)
      (hC₂ : ∀ t : E3, |Submission.BoseGases.conv3Small M t - 1| ≤ C₂ * ‖t‖ ^ 2)
      {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R ≤ ℓ * d / 16)
      (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0),
        ∀ᵐ x : E3,
          0 ≤ Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) x
              / Submission.BoseGases.convScale ℓ x
          ∧ Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) x
              / Submission.BoseGases.convScale ℓ x
            ≤ (1 + 2 * C₂ / Work.SmallBoxSliding.smallConvLower M * (R / (ℓ * d)) ^ 2
                + 2 * C₁ * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h x)
    (hnewton : ∀ {δ : ℝ}, 0 ≤ δ → ∀ {W : E3 → ℝ}, MeasureTheory.Integrable W →
      (0 ≤ᵐ[MeasureTheory.volume] W) → (∀ x : E3, R ≤ ‖x‖ → W x = 0) →
      (∀ᵐ x : E3, W x ≤ (1 + δ) * Submission.BoseGases.g0 v h x) →
      ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
          (Submission.BoseGases.pairW W q) ^ 2 / ‖q‖ ^ 2
        ≤ 2 * (1 + δ) ^ 2 * Submission.BoseGases.g0w0Mass (v := v) h) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
      (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0),
      ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
          (Submission.BoseGases.pairW (fun x : E3 =>
              Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) x
                / Submission.BoseGases.convScale ℓ x) q) ^ 2 / ‖q‖ ^ 2
        ≤ 2 * (1 + K * ((R / ℓ) ^ 2 + (R / (ℓ * d)) ^ 2))
            * Submission.BoseGases.g0w0Mass (v := v) h := by
  obtain ⟨C₁, hC₁0, hC₁dev⟩ := hdevChi
  obtain ⟨C₂, hC₂0, hC₂dev⟩ := hdevSmall
  have hsCL : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  refine ⟨(2 + (2 * C₂ / Work.SmallBoxSliding.smallConvLower M * (1 / 16) ^ 2
      + 2 * C₁ * Submission.BoseGases.chiR0 ^ 2))
      * max (2 * C₂ / Work.SmallBoxSliding.smallConvLower M) (2 * C₁), ?_, ?_⟩
  · have hA0 : 0 ≤ 2 * C₂ / Work.SmallBoxSliding.smallConvLower M :=
      div_nonneg (by linarith) (le_of_lt hsCL)
    have hB0 : 0 ≤ 2 * C₁ := by linarith
    have h1 : 0 ≤ 2 * C₂ / Work.SmallBoxSliding.smallConvLower M * (1 / 16) ^ 2 :=
      mul_nonneg hA0 (by norm_num)
    have h2 : 0 ≤ 2 * C₁ * Submission.BoseGases.chiR0 ^ 2 := mul_nonneg hB0 (sq_nonneg _)
    exact mul_nonneg (by linarith) (le_max_of_le_right hB0)
  intro ℓ d hℓ hd hR hRχ
  have hA0 : 0 ≤ 2 * C₂ / Work.SmallBoxSliding.smallConvLower M :=
    div_nonneg (by linarith) (le_of_lt hsCL)
  have hB0 : 0 ≤ 2 * C₁ := by linarith
  -- ambient `g₀`-facts
  have hGint : Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hG0 : ∀ᵐ x : E3, 0 ≤ Submission.BoseGases.g0 v h x :=
    Submission.BoseGases.g0_nonneg_ae hR0 hv hvrad hv_supp h
  have hGsupp : ∀ x : E3, R ≤ ‖x‖ → Submission.BoseGases.g0 v h x = 0 :=
    fun x hx => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h
  -- the diluteness parameters
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hUle : (R / (ℓ * d)) ^ 2 ≤ (1 / 16) ^ 2 := by
    have h1 : R / (ℓ * d) ≤ 1 / 16 := by
      rw [div_le_iff₀ hld]
      linarith
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hVle : (R / ℓ) ^ 2 ≤ Submission.BoseGases.chiR0 ^ 2 := by
    have h1 : R / ℓ ≤ Submission.BoseGases.chiR0 := by
      rw [div_le_iff₀ hℓ]
      linarith
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hU0 : 0 ≤ (R / (ℓ * d)) ^ 2 := sq_nonneg _
  have hV0 : 0 ≤ (R / ℓ) ^ 2 := sq_nonneg _
  -- the two-factor renormalised kernel, as a local definition (definitionally transparent)
  let W : E3 → ℝ := fun x : E3 =>
    Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) x
      / Submission.BoseGases.convScale ℓ x
  -- the sharp pointwise comparison
  have hcmp := hsharp hC₁0 hC₂0 hC₁dev hC₂dev hℓ hd hR hRχ
  have hW0 : 0 ≤ᵐ[MeasureTheory.volume] W := hcmp.mono (fun x hx => hx.1)
  have hδkey : (1 + 2 * C₂ / Work.SmallBoxSliding.smallConvLower M * (R / (ℓ * d)) ^ 2
        + 2 * C₁ * (R / ℓ) ^ 2)
      = 1 + (2 * C₂ / Work.SmallBoxSliding.smallConvLower M * (R / (ℓ * d)) ^ 2
        + 2 * C₁ * (R / ℓ) ^ 2) := by ring
  have hWle : ∀ᵐ x : E3, W x ≤
      (1 + (2 * C₂ / Work.SmallBoxSliding.smallConvLower M * (R / (ℓ * d)) ^ 2
        + 2 * C₁ * (R / ℓ) ^ 2)) * Submission.BoseGases.g0 v h x := by
    filter_upwards [hcmp] with x hx
    rw [← hδkey]
    exact hx.2
  have hWabs : ∀ᵐ x : E3, |W x| ≤
      (1 + (2 * C₂ / Work.SmallBoxSliding.smallConvLower M * (R / (ℓ * d)) ^ 2
        + 2 * C₁ * (R / ℓ) ^ 2)) * Submission.BoseGases.g0 v h x := by
    filter_upwards [hcmp, hG0] with x hx hgx
    rw [abs_of_nonneg hx.1]
    rw [← hδkey]
    exact hx.2
  have hWsupp : ∀ x : E3, R ≤ ‖x‖ → W x = 0 := by
    intro x hx
    simp only [W, Submission.BoseGases.wSmallScaled, hGsupp x hx, zero_div]
  -- integrability of the renormalised kernel
  have hδ0 : 0 ≤ 2 * C₂ / Work.SmallBoxSliding.smallConvLower M * (R / (ℓ * d)) ^ 2
      + 2 * C₁ * (R / ℓ) ^ 2 :=
    add_nonneg (mul_nonneg hA0 hU0) (mul_nonneg hB0 hV0)
  have hWm : AEStronglyMeasurable W :=
    aestronglyMeasurable_slidingKernel (g := Submission.BoseGases.g0 v h) (ℓ := ℓ) (d := d)
      hM hGint.aestronglyMeasurable
  have hWint : Integrable W :=
    integrable_slidingKernel_of_abs_le (g := Submission.BoseGases.g0 v h) (ℓ := ℓ) (d := d)
      hδ0 hWm hGint hWabs
  -- the Newtonian-mass inequality at the sharp factor
  have hnewton' := hnewton (δ := 2 * C₂ / Work.SmallBoxSliding.smallConvLower M
      * (R / (ℓ * d)) ^ 2 + 2 * C₁ * (R / ℓ) ^ 2) hδ0 hWint hW0 hWsupp hWle
  -- the diluteness arithmetic
  have hY0 : 0 ≤ Submission.BoseGases.g0w0Mass (v := v) h :=
    Work.SmallBoxA0.g0w0Mass_nonneg_general hR0 hv_supp h
  have harith := sharp_factor_arith (A := 2 * C₂ / Work.SmallBoxSliding.smallConvLower M)
    (B := 2 * C₁) (U := (R / (ℓ * d)) ^ 2) (V := (R / ℓ) ^ 2)
    (chiR0 := Submission.BoseGases.chiR0) hA0 hB0 hU0 hV0 hUle hVle
  calc ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3, (Submission.BoseGases.pairW W q) ^ 2 / ‖q‖ ^ 2
      ≤ 2 * (1 + (2 * C₂ / Work.SmallBoxSliding.smallConvLower M * (R / (ℓ * d)) ^ 2
            + 2 * C₁ * (R / ℓ) ^ 2)) ^ 2 * Submission.BoseGases.g0w0Mass (v := v) h := hnewton'
    _ ≤ 2 * (1 + ((2 + (2 * C₂ / Work.SmallBoxSliding.smallConvLower M * (1 / 16) ^ 2
            + 2 * C₁ * Submission.BoseGases.chiR0 ^ 2))
            * max (2 * C₂ / Work.SmallBoxSliding.smallConvLower M) (2 * C₁))
            * ((R / ℓ) ^ 2 + (R / (ℓ * d)) ^ 2)) * Submission.BoseGases.g0w0Mass (v := v) h := by
        refine mul_le_mul_of_nonneg_right ?_ hY0
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
        exact harith

end Work.BoseFixB1S
