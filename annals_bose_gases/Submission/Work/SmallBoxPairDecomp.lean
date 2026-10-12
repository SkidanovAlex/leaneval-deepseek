import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.Haar.Unique
import ChallengeDeps
import Submission.KernelMean
import Submission.KernelSym
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-274 — the relative-coordinate (`z = x − y`) decomposition of the
pair kernel `w₁` (the engine of D1 items (c1)/(c2))

FS `lm:appbogolubov` needs two "resolution of identity" identities,

    (c1)  Σ_i Q_iχ[√−Δ−c]₊²χQ_i = (2π)^{-3}∫[|p|−c]₊²·N_p dp
    (c2)  A₂ = ½(2π)^{-3}∫Ŵ₁(p)(b_p†b_{−p}† + h.c.) dp

whose common engine is the **relative-coordinate structure of the pair
kernel** `w₁(x,y) = χ(x)·W₁(x−y)·χ(y)` (`wPairC ℓ h`, `W₁ = wScaled ℓ h`).
This module proves the exact algebraic identity that makes the momentum
resolution possible:

  * **`integral_wPairC_cos`** — the *anti-diagonal Fourier symbol* of `w₁`:

        ∫∫ w₁(x,y)·cos⟨p, x−y⟩ = ℓ³·∫ h(z)·cos⟨p, z⟩ dz .

    Proof route: substitute `z = x − y` in the inner integral
    (`integral_sub_left_eq_self`, free), swap the two integrals, and evaluate
    the resulting `x`-fibre with the corpus volume identity
    `∫_x χ(x)χ(x−y) = ℓ³(χ⋆χ)_ℓ(y)` (`KernelIds.integral_pair_scale`) together
    with the defining cancellation `W₁(y)·(χ⋆χ)_ℓ(y) = h(y)`
    (`wScaled_mul_convScale`).

    This is the exact form of FS's `\widehat{WS_1}(p) ≈ \widehat{g₀}(p)`
    (`WS₁ ≈ g₀`): the symbol of `w₁` at the anti-diagonal `(p,−p)` is
    `ℓ³𝓕g₀(p)`, the `ℓ³` cancelling the `|B|^{-1}` of `b_p†b_{−p}†`.

  * **`pairForm_relComp`** — the bilinear (test-function) form

        ∫∫ w₁(x,y)·ψ(x)·φ(y) = ∫_z W₁(z)·(∫_x χ(x)χ(x−z)ψ(x)φ(x−z) dx) dz ,

    the exact position-space form of the momentum pairing; its Fourier
    transform in `z` is the Plancherel form
    `∫_p 𝓕W₁(p)·\overline{𝓕(χψ)}(p)·𝓕(χφ)(p) dp`.

The hypotheses beyond `0 ≤ h` and the dilute regime `R ≤ ℓ·chiR0` are only
`Measurable h` and `Integrable h` (`g₀ = v(1−ω₀) ∈ L¹` for `v ∈ L¹`); the
kernel integrability is the proved lemma `integrable_chi_wScaled_chi`, and
`integral_wPairC_cos'` is the fully-applicable (hypothesis-free in `hK`) form.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators Convolution

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1 The kernel identity `W₁·(χ⋆χ)_ℓ = h` -/

/-- **The defining cancellation of the χ-renormalised kernel**: on the
support of `h`, `wScaled ℓ h·convScale ℓ = h`, and off it both sides vanish
(Lean's `x/0 = 0`).  Hypothesis: `convScale ℓ` does not vanish on
`tsupport h` (in the application supplied by
`ChiWitness.convScale_ge_half_ball` from the dilute regime `R ≤ ℓ·chiR0`). -/
lemma wScaled_mul_convScale {ℓ : ℝ} {h : ℝ³ → ℝ} {R : ℝ}
    (hsupp : tsupport h ⊆ ball (0 : ℝ³) R)
    (hconv : ∀ z : ℝ³, z ∈ ball (0 : ℝ³) R → convScale ℓ z ≠ 0) (z : ℝ³) :
    wScaled ℓ h z * convScale ℓ z = h z := by
  by_cases hz : z ∈ tsupport h
  · have hz0 := hsupp hz
    rw [wScaled]
    exact div_mul_cancel₀ _ (hconv z hz0)
  · have hz0 : h z = 0 := image_eq_zero_of_notMem_tsupport hz
    rw [wScaled, hz0, zero_div, zero_mul]

/-- the dilute-regime instance of `hconv`: `1/2 ≤ convScale ℓ` on `ball 0 R`
when `R ≤ ℓ·chiR0`. -/
lemma convScale_ne_zero_of_regime {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {z : ℝ³} (hz : z ∈ ball (0 : ℝ³) R) : convScale ℓ z ≠ 0 := by
  have hnorm : ‖z‖ < R := by simpa [mem_ball, dist_eq_norm] using hz
  have hhalf := convScale_ge_half_ball hℓ hR hRℓ hnorm.le
  linarith

/-! ## 2 The pair kernel and its relative-coordinate form -/

/-- unfolding of the pair kernel `w₁(x,y) = χ(x)·W₁(x−y)·χ(y)`. -/
lemma wPairC_apply (ℓ : ℝ) (h : ℝ³ → ℝ) (x y : ℝ³) :
    wPairC ℓ h x y = chiScale ℓ x * wScaled ℓ h (x - y) * chiScale ℓ y := rfl

/-- `(χ⋆χ)_ℓ` is even (used to align the sign of the substitution
`z = x − y`). -/
lemma convScale_neg (ℓ : ℝ) (z : ℝ³) : convScale ℓ (-z) = convScale ℓ z := by
  dsimp [convScale]
  rw [show (ℓ⁻¹) • (-z) = -((ℓ⁻¹) • z) by rw [smul_neg]]
  exact conv3chi_even ((ℓ⁻¹) • z)

/-- `wScaled ℓ h` is nonnegative when `h` is. -/
lemma wScaled_nonneg {ℓ : ℝ} {h : ℝ³ → ℝ} (hh : 0 ≤ h) (z : ℝ³) :
    0 ≤ wScaled ℓ h z :=
  div_nonneg (hh z) (convScale_nonneg ℓ z)

/-! ## 3 Integrability of the pair kernel (the swap hypothesis) -/

/-- The pair-kernel integrand `χ(x)·W₁(y)·χ(x−y)` factors pointwise as
`χ(x)·χ(x−y)·W₁(y)`. -/
lemma chi_wScaled_chi_eq (ℓ : ℝ) (h : ℝ³ → ℝ) (x y : ℝ³) :
    chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y)
      = chiScale ℓ x * chiScale ℓ (x - y) * wScaled ℓ h y := by ring

/-- **The natural discharge route for the kernel-integrability hypothesis.**
`hK` of `integral_wPairC_cos` is the statement that the pair kernel
`χ(x)·W₁(y)·χ(x−y)` is `L¹` on `ℝ³ × ℝ³`.  It is *automatic* as soon as
`W₁` is locally bounded, because the two `χ`-factors confine `x` to
`ball (ℓ/2)` and `y` to `x − ball (ℓ/2)`; the cleanest Lean route is the
iterated-integrability criterion
`MeasureTheory.integrable_prod_iff`, whose two obligations are
  * `∀ᵐ x, Integrable (fun y => χ(x)·W₁(y)·χ(x−y))` — the fibre bound
    `KernelMean.kernel_fibre_integrable` (with `y ↦ x − y`),
  * `Integrable (fun x => ∫ y, ‖χ(x)·W₁(y)·χ(x−y)‖)`,
    dominated by `‖χ‖_∞·(2‖h‖_1)`.
For `h ≥ 0` integrable compactly supported supported in `ball 0 R` (the D1
case, `h = g₀`) both hold; the explicit construction is the next step and is
recorded in `SmallBoxDesignNote.md`. -/
lemma integrable_chi_wScaled_chi_iff (ℓ : ℝ) {h : ℝ³ → ℝ} (hm : Measurable h) :
    Integrable (fun q : ℝ³ × ℝ³ => chiScale ℓ q.1 * wScaled ℓ h q.2 * chiScale ℓ (q.1 - q.2))
        (volume.prod volume)
      ↔ (∀ᵐ x : ℝ³ ∂(volume : Measure ℝ³),
            Integrable (fun y : ℝ³ => chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y)))
          ∧ Integrable (fun x : ℝ³ =>
              ∫ y : ℝ³, ‖chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y)‖) := by
  refine (integrable_prod_iff ?_).trans ?_
  · have h1 : Measurable (fun q : ℝ³ × ℝ³ =>
        chiScale ℓ q.1 * wScaled ℓ h q.2 * chiScale ℓ (q.1 - q.2)) := by
      refine (((chiScale_continuous ℓ).measurable.comp measurable_fst).mul
        ((hm.div (convScale_continuous ℓ).measurable).comp measurable_snd)).mul
        ((chiScale_continuous ℓ).measurable.comp (measurable_fst.sub measurable_snd))
    exact h1.aestronglyMeasurable
  · constructor
    · intro ⟨h1, h2⟩
      exact ⟨h1, by simpa only [Real.norm_eq_abs] using h2⟩
    · intro ⟨h1, h2⟩
      exact ⟨h1, by simpa only [Real.norm_eq_abs] using h2⟩

/-- **Discharge of the kernel-integrability hypothesis `hK`** (the exact
analogue of `KernelIds.kernel_integrable_prod` for the renormalised kernel
`W₁ = wScaled ℓ h`): for `h` integrable, supported in `ball 0 R` and in the
dilute regime, the product `χ(x)·W₁(y)·χ(x−y)` is `L¹` on `ℝ³ × ℝ³`, dominated
by `(2S)·χ(x)·|h(y)|` with `S := (∫χ²)^{-1/2}` (`wScaled_abs_le_two`,
`abs_chiScale_le`), an `L¹` product. -/
lemma integrable_chi_wScaled_chi {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {h : ℝ³ → ℝ} (hm : Measurable h) (hi : Integrable h)
    (hsuppball : tsupport h ⊆ ball (0 : ℝ³) R) :
    Integrable (fun p : ℝ³ × ℝ³ => chiScale ℓ p.1 * wScaled ℓ h p.2 * chiScale ℓ (p.1 - p.2))
      (volume.prod volume) := by
  let S : ℝ := (Real.sqrt chiNormSq)⁻¹
  have hsup : ∀ x : ℝ³, |chiScale ℓ x| ≤ S := by
    intro x
    dsimp [S]
    exact abs_chiScale_le ℓ x
  have hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0 := by
    intro z hz
    by_contra hne
    have hmem : z ∈ tsupport h := subset_tsupport h (by simpa [Function.mem_support] using hne)
    have hlt : ‖z‖ < R := by
      have := hsuppball hmem
      rw [mem_ball, dist_eq_norm, sub_zero] at this
      exact this
    linarith
  have hkbound : ∀ z : ℝ³, |wScaled ℓ h z| ≤ 2 * |h z| :=
    wScaled_abs_le_two hℓ hR hRℓ hsupp
  have hSpos : 0 < S := by
    dsimp [S]
    exact inv_pos.mpr (Real.sqrt_pos.mpr chiNormSq_pos)
  have hdom : ∀ p : ℝ³ × ℝ³,
      |chiScale ℓ p.1 * wScaled ℓ h p.2 * chiScale ℓ (p.1 - p.2)|
        ≤ ((2 * S) * chiScale ℓ p.1) * |h p.2| := by
    intro p
    calc
      |chiScale ℓ p.1 * wScaled ℓ h p.2 * chiScale ℓ (p.1 - p.2)|
          = (|chiScale ℓ p.1| * |wScaled ℓ h p.2|) * |chiScale ℓ (p.1 - p.2)| := by
            rw [abs_mul, abs_mul]
      _ ≤ (chiScale ℓ p.1 * (2 * |h p.2|)) * S := by
            refine mul_le_mul
              (mul_le_mul (by rw [abs_of_nonneg (chiScale_nonneg ℓ p.1)]) (hkbound p.2)
                (abs_nonneg _) (chiScale_nonneg ℓ p.1))
              (hsup (p.1 - p.2)) (abs_nonneg _)
              (mul_nonneg (chiScale_nonneg ℓ p.1) (by positivity))
      _ = ((2 * S) * chiScale ℓ p.1) * |h p.2| := by ring
  have hfg : Integrable (fun p : ℝ³ × ℝ³ => ((2 * S) * chiScale ℓ p.1) * |h p.2|)
      (volume.prod volume) := by
    have hχint : Integrable (chiScale ℓ) (volume : Measure ℝ³) :=
      Continuous.integrable_of_hasCompactSupport (chiScale_continuous ℓ)
        (chiScale_hasCompactSupport (ne_of_gt hℓ))
    have hf : Integrable (fun x : ℝ³ => (2 * S) * chiScale ℓ x) (volume : Measure ℝ³) :=
      hχint.const_mul (2 * S)
    exact hf.mul_prod hi.abs
  have haesm : AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => chiScale ℓ p.1 * wScaled ℓ h p.2 * chiScale ℓ (p.1 - p.2))
      (volume.prod volume) := by
    have h1 : Measurable (fun p : ℝ³ × ℝ³ =>
        chiScale ℓ p.1 * wScaled ℓ h p.2 * chiScale ℓ (p.1 - p.2)) :=
      (((chiScale_continuous ℓ).measurable.comp measurable_fst).mul
        ((hm.div (convScale_continuous ℓ).measurable).comp measurable_snd)).mul
        ((chiScale_continuous ℓ).measurable.comp (measurable_fst.sub measurable_snd))
    exact h1.aestronglyMeasurable
  refine Integrable.mono hfg haesm ?_
  filter_upwards with p
  have hgnn : 0 ≤ ((2 * S) * chiScale ℓ p.1) * |h p.2| :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (le_of_lt hSpos)) (chiScale_nonneg ℓ p.1))
      (abs_nonneg _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hgnn] using hdom p

/-! ## 4 The anti-diagonal Fourier symbol -/

/-- **The anti-diagonal Fourier symbol of the pair kernel.**  Substituting
`z = x − y` in the inner integral (`integral_sub_left_eq_self`) and using the
corpus volume identity `∫_x χ(x)χ(x−z) = ℓ³(χ⋆χ)_ℓ(z)`
(`KernelIds.integral_pair_scale`) plus the defining cancellation
`W₁(z)·(χ⋆χ)_ℓ(z) = h(z)` (`wScaled_mul_convScale`), the double integral
collapses to `ℓ³∫h(z)cos⟨p,z⟩`.

This is the exact form of FS's `\widehat{WS_1}(p) ≈ \widehat{g₀}(p)`: the
Fourier symbol of `w₁` at the anti-diagonal `(p,−p)` is `ℓ³𝓕g₀(p)`, the `ℓ³`
cancelling the `|B|^{-1}` of `b_p†b_{−p}†`. -/
theorem integral_wPairC_cos {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {h : ℝ³ → ℝ} (hnn : 0 ≤ h) (hm : Measurable h)
    (hsuppball : tsupport h ⊆ ball (0 : ℝ³) R)
    (hK : Integrable (fun q : ℝ³ × ℝ³ => chiScale ℓ q.1 * wScaled ℓ h q.2 * chiScale ℓ (q.1 - q.2))
      (volume.prod volume))
    (p : ℝ³) :
    (∫ x, ∫ y, wPairC ℓ h x y * Real.cos (inner ℝ p (x - y)))
      = ℓ ^ 3 * ∫ z, h z * Real.cos (inner ℝ p z) := by
  have hconv : ∀ z : ℝ³, z ∈ ball (0 : ℝ³) R → convScale ℓ z ≠ 0 :=
    fun z hz => convScale_ne_zero_of_regime hℓ hR hRℓ hz
  -- (A) for each `x`, substitute `y ↦ x − y` in the inner integral
  have hA : ∀ x : ℝ³,
      (∫ y, wPairC ℓ h x y * Real.cos (inner ℝ p (x - y)))
        = ∫ y, chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y) * Real.cos (inner ℝ p y) := by
    intro x
    have hG := integral_sub_left_eq_self
      (fun w : ℝ³ => chiScale ℓ x * wScaled ℓ h w * chiScale ℓ (x - w) * Real.cos (inner ℝ p w))
      volume x
    have hcongr : (∫ y, chiScale ℓ x * wScaled ℓ h (x - y) * chiScale ℓ y
          * Real.cos (inner ℝ p (x - y)))
        = ∫ y, chiScale ℓ x * wScaled ℓ h (x - y) * chiScale ℓ (x - (x - y))
            * Real.cos (inner ℝ p (x - y)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [show x - (x - y) = y from by abel]
    simp only [wPairC, wPair]
    exact hcongr.trans hG
  -- (B) integrability of the uncurried (substituted) kernel
  have hWm : Measurable (wScaled ℓ h) := hm.div (convScale_continuous ℓ).measurable
  have hInt : Integrable (Function.uncurry (fun x y : ℝ³ =>
      chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y) * Real.cos (inner ℝ p y)))
      (volume.prod volume) := by
    refine Integrable.mono' hK ?_ ?_
    · change AEStronglyMeasurable (fun q : ℝ³ × ℝ³ =>
          chiScale ℓ q.1 * wScaled ℓ h q.2 * chiScale ℓ (q.1 - q.2) * Real.cos (inner ℝ p q.2))
          (volume.prod volume)
      have hmeasm : Measurable (fun q : ℝ³ × ℝ³ =>
          chiScale ℓ q.1 * wScaled ℓ h q.2 * chiScale ℓ (q.1 - q.2) * Real.cos (inner ℝ p q.2)) :=
        ((((chiScale_continuous ℓ).measurable.comp measurable_fst).mul
            (hWm.comp measurable_snd)).mul
          ((chiScale_continuous ℓ).measurable.comp (measurable_fst.sub measurable_snd))).mul
          (by fun_prop : Measurable (fun q : ℝ³ × ℝ³ => Real.cos (inner ℝ p q.2)))
      exact hmeasm.aestronglyMeasurable
    · filter_upwards with q
      change ‖chiScale ℓ q.1 * wScaled ℓ h q.2 * chiScale ℓ (q.1 - q.2)
          * Real.cos (inner ℝ p q.2)‖ ≤ chiScale ℓ q.1 * wScaled ℓ h q.2 * chiScale ℓ (q.1 - q.2)
      have hχ1 : 0 ≤ chiScale ℓ q.1 := chiScale_nonneg ℓ q.1
      have hχ2 : 0 ≤ chiScale ℓ (q.1 - q.2) := chiScale_nonneg ℓ _
      have hW0 : 0 ≤ wScaled ℓ h q.2 := wScaled_nonneg hnn q.2
      have hcos : |Real.cos (inner ℝ p q.2)| ≤ 1 := Real.abs_cos_le_one _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (mul_nonneg hχ1 hW0) hχ2)]
      exact mul_le_of_le_one_right (mul_nonneg (mul_nonneg hχ1 hW0) hχ2) hcos
  -- (C) the fibre computation
  have hD : ∀ y : ℝ³,
      (∫ x, chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y) * Real.cos (inner ℝ p y))
        = ℓ ^ 3 * (h y * Real.cos (inner ℝ p y)) := by
    intro y
    have h1 : (∫ x, chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y) * Real.cos (inner ℝ p y))
        = ∫ x, (chiScale ℓ x * chiScale ℓ (x - y)) * (wScaled ℓ h y * Real.cos (inner ℝ p y)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    rw [h1, integral_mul_const, integral_pair_scale hℓ y]
    have h2 : (ℓ ^ 3 * convScale ℓ y) * (wScaled ℓ h y * Real.cos (inner ℝ p y))
        = ℓ ^ 3 * ((wScaled ℓ h y * convScale ℓ y) * Real.cos (inner ℝ p y)) := by ring
    rw [h2, wScaled_mul_convScale hsuppball hconv y]
  have hstep1 : (∫ x, ∫ y, wPairC ℓ h x y * Real.cos (inner ℝ p (x - y)))
      = ∫ x, ∫ y, chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y)
          * Real.cos (inner ℝ p y) :=
    integral_congr_ae (Filter.Eventually.of_forall hA)
  rw [hstep1, integral_integral_swap hInt]
  rw [show (∫ y, ∫ x, chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y)
        * Real.cos (inner ℝ p y))
      = ∫ y, ℓ ^ 3 * (h y * Real.cos (inner ℝ p y)) from
    integral_congr_ae (Filter.Eventually.of_forall hD)]
  rw [integral_const_mul]

/-- **`integral_wPairC_cos` with the kernel-`L¹` hypothesis discharged**: for
`h ≥ 0` measurable, integrable, supported in `ball 0 R`, the anti-diagonal
Fourier symbol identity holds with NO further hypothesis (the integrability of
`χ(x)·W₁(y)·χ(x−y)` is `integrable_chi_wScaled_chi`).  This is the form in
which the D1 body consumes it, with `h = g₀ v h`. -/
theorem integral_wPairC_cos' {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {h : ℝ³ → ℝ} (hnn : 0 ≤ h) (hm : Measurable h)
    (hi : Integrable h) (hsuppball : tsupport h ⊆ ball (0 : ℝ³) R) (p : ℝ³) :
    (∫ x, ∫ y, wPairC ℓ h x y * Real.cos (inner ℝ p (x - y)))
      = ℓ ^ 3 * ∫ z, h z * Real.cos (inner ℝ p z) :=
  integral_wPairC_cos hℓ hR hRℓ hnn hm hsuppball
    (integrable_chi_wScaled_chi hℓ hR hRℓ hm hi hsuppball) p

/-! ## 5 The bilinear relative-coordinate decomposition -/

/-- **The bilinear relative-coordinate decomposition of the pair kernel**
(the exact position-space form of FS's momentum pairing).  For arbitrary test
functions `ψ, φ`,

    ∫∫ w₁(x,y)·ψ(x)·φ(y) = ∫_z W₁(z)·(∫_x χ(x)χ(x−z)·ψ(x)·φ(x−z) dx) dz .

The right-hand side is the position-space form of
`∫_p 𝓕W₁(p)·\overline{𝓕(χψ)}(p)·𝓕(χφ)(p) dp` (Plancherel in `z`): the
relative coordinate `z = x_i − x_j` carries the kernel `W₁`, while the
"condensate density" `∫_x χ(x)χ(x−z)ψ(x)φ(x−z)` is the mode-pair amplitude of
the A₂ word.  This is the engine of D1 item (c2). -/
theorem pairForm_relComp {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hRℓ : R ≤ ℓ * chiR0)
    {h : ℝ³ → ℝ} {ψ φ : ℝ³ → ℝ}
    (hInt : Integrable (Function.uncurry (fun x y : ℝ³ =>
      chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y) * ψ x * φ (x - y)))
      (volume.prod volume)) :
    (∫ x, ∫ y, wPairC ℓ h x y * ψ x * φ y)
      = ∫ y, wScaled ℓ h y *
          (∫ x, chiScale ℓ x * chiScale ℓ (x - y) * ψ x * φ (x - y)) := by
  have hconv : ∀ z : ℝ³, z ∈ ball (0 : ℝ³) R → convScale ℓ z ≠ 0 :=
    fun z hz => convScale_ne_zero_of_regime hℓ hR hRℓ hz
  have hA : ∀ x : ℝ³,
      (∫ y, wPairC ℓ h x y * ψ x * φ y)
        = ∫ y, chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y) * ψ x * φ (x - y) := by
    intro x
    have hG := integral_sub_left_eq_self
      (fun w : ℝ³ => chiScale ℓ x * wScaled ℓ h w * chiScale ℓ (x - w) * ψ x * φ (x - w))
      volume x
    have hcongr : (∫ y, chiScale ℓ x * wScaled ℓ h (x - y) * chiScale ℓ y * ψ x * φ y)
        = ∫ y, chiScale ℓ x * wScaled ℓ h (x - y) * chiScale ℓ (x - (x - y)) * ψ x
            * φ (x - (x - y)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [show x - (x - y) = y from by abel]
    simp only [wPairC, wPair]
    exact hcongr.trans hG
  have hstep1 : (∫ x, ∫ y, wPairC ℓ h x y * ψ x * φ y)
      = ∫ x, ∫ y, chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y) * ψ x * φ (x - y) :=
    integral_congr_ae (Filter.Eventually.of_forall hA)
  have hD : ∀ y : ℝ³,
      (∫ x, chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y) * ψ x * φ (x - y))
        = wScaled ℓ h y * (∫ x, chiScale ℓ x * chiScale ℓ (x - y) * ψ x * φ (x - y)) := by
    intro y
    have h1 : (∫ x, chiScale ℓ x * wScaled ℓ h y * chiScale ℓ (x - y) * ψ x * φ (x - y))
        = ∫ x, wScaled ℓ h y
            * (chiScale ℓ x * chiScale ℓ (x - y) * ψ x * φ (x - y)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    rw [h1, integral_const_mul]
  rw [hstep1, integral_integral_swap hInt]
  exact integral_congr_ae (Filter.Eventually.of_forall hD)


end BoseGases

end Submission
