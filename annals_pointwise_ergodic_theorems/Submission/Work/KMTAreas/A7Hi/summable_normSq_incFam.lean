/-
# Square summability of the low-pass increments `lpf (k+1) − lpf k`

`lpf ρ l m₀ m = kmtProj ρ l (-(m₀ + m))` is the Ionescu--Wainger projection
`Π_{≤ l, ≤ -(m₀+m)}`, i.e. the convolution on `ℤ` with the Fourier coefficients of the symbol
`iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta (-(m₀+m))))`.

The lemma proved here (`summable_normSq_incFam`) is the elementary fact that the *increments* of
this family stay in `ℓ²(ℤ)` when the input does:

  `h ∈ ℓ²(ℤ) ⟹ (x ↦ lpf ρ l m₀ (k+1) h x − lpf ρ l m₀ k h x) ∈ ℓ²(ℤ)`.

The proof does not use any arithmetic hypothesis on `ρ` (in particular no non-aliasing /
good-major-arc condition).  Two ingredients suffice:

* **the kernel of `kmtProj ρ l k` is in `ℓ¹(ℤ)` for *every* `ρ : ℝ`** — this is the `j^{-2}` decay
  of `Work.KMTContract.kmtKernel_decay` (which holds for arbitrary `ρ`, `l`, `k`), turned into
  absolute summability by `Work.KMTContract.kernel_l1_of_decay`;
* **Young's inequality at the endpoint `ℓ¹ ∗ ℓ² → ℓ²`** (Mathlib/`Commons`:
  `eLpNorm_convolution_le_ennreal`), which makes the convolution with an `ℓ¹` kernel an
  `ℓ²`-bounded operator.

The bridge between `Summable (fun x => ‖u x‖ ^ 2)` and `eLpNorm u 2 Measure.count`
(`Work.KMTAreas.A4.eLpNorm_two_count_eq_ofReal` and
`Work.KMTAreas.A4.summable_norm_sq_of_eLpNorm_le`) closes the argument.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Hi.LowpassDefs
import Submission.Work.KMTPlan.A6.eLpNorm_iwConv_two_le_of_symbol_bound
import Submission.Work.KMTAreas.A4.sivPairingCS
import Submission.Port.Aesm

namespace Work.KMTAreas.A7Hi

open MeasureTheory ENNReal
open scoped ENNReal NNReal BigOperators

/-! ## The `ℓ¹` kernel of the IW projection -/

/-- The convolution kernel of `kmtProj ρ l k` — the Fourier coefficients of the IW symbol — is
absolutely summable on `ℤ`, for **every** `ρ : ℝ` (no restriction to `ρ ∈ (0,1]`). -/
lemma summable_iwKernel_kmtProj (ρ : ℝ) (l : ℕ) (k : ℤ) :
    Summable (fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j‖) := by
  obtain ⟨C, _hC, hdec⟩ := Work.KMTContract.kmtKernel_decay ρ l k
  exact Work.KMTContract.kernel_l1_of_decay hdec

/-! ## The `ℓ²` bound for the IW projection -/

/-- **The IW projection is bounded on `ℓ²(ℤ)`**, for every `ρ : ℝ`.  The operator `kmtProj ρ l k`
is the convolution with the `ℓ¹` kernel `iwKernel` of its symbol, so Young's inequality at the
endpoint `ℓ¹ ∗ ℓ² → ℓ²` gives `‖kmtProj ρ l k f‖₂ ≤ (‖kernel‖₁ + 1) ‖f‖₂`.

(The mirror of this proof with a `ρ`-uniform kernel bound is
`Work.KMTAreas.A7.KmtProjUniform`, which assumes `0 < ρ ≤ 1`; here `ρ` is arbitrary and the
constant is allowed to depend on `ρ`, `l`, `k`.) -/
theorem eLpNorm_kmtProj_two_le (ρ : ℝ) (l : ℕ) (k : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℤ → ℂ),
      eLpNorm (Work.KMTContract.kmtProj ρ l k f) (2 : ℝ≥0∞) (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal C * eLpNorm f (2 : ℝ≥0∞) (Measure.count : Measure ℤ) := by
  set kern : ℤ → ℂ := fun j => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j with hkernDef
  have hsumm : Summable (fun j : ℤ => ‖kern j‖) := by
    rw [hkernDef]; exact summable_iwKernel_kmtProj ρ l k
  have hS0 : 0 ≤ ∑' j : ℤ, ‖kern j‖ := tsum_nonneg (fun j => norm_nonneg _)
  refine ⟨(∑' j : ℤ, ‖kern j‖) + 1, by linarith, fun f => ?_⟩
  set K : ℤ → ℝ≥0∞ := fun j => ‖kern j‖ₑ with hK
  set Φ : ℤ → ℝ≥0∞ := fun j => ‖f j‖ₑ with hΦ
  have hKae : AEMeasurable K (Measure.count : Measure ℤ) :=
    (measurable_of_countable K).aemeasurable
  have hΦae : AEMeasurable Φ (Measure.count : Measure ℤ) :=
    (measurable_of_countable Φ).aemeasurable
  -- The projection is pointwise dominated by the (nonnegative) convolution integral.
  have hpoint : ∀ n : ℤ, ‖Work.KMTContract.kmtProj ρ l k f n‖ₑ
      ≤ ∫⁻ y, K (n - y) * Φ y ∂(Measure.count : Measure ℤ) := by
    intro n
    have h1 : ‖Work.KMTContract.kmtProj ρ l k f n‖ₑ ≤ ∑' j : ℤ, K j * Φ (n - j) := by
      rw [Work.KMTContract.kmtProj_apply]
      refine (enorm_tsum_le_tsum_enorm).trans (le_of_eq (tsum_congr (fun j => ?_)))
      simp only [hK, hΦ]
      exact enorm_mul _ _
    have h2 : (∑' j : ℤ, K j * Φ (n - j)) = ∑' y : ℤ, K (n - y) * Φ y := by
      simpa using (Equiv.tsum_eq (Equiv.subLeft n) (fun j : ℤ => K j * Φ (n - j))).symm
    rw [lintegral_count, ← h2]
    exact h1
  -- Monotonicity of `eLpNorm` turns the pointwise bound into an `ℓ²` bound.
  have hstep2 : eLpNorm (Work.KMTContract.kmtProj ρ l k f) (2 : ℝ≥0∞)
        (Measure.count : Measure ℤ)
      ≤ eLpNorm (fun n : ℤ => ∫⁻ y, K (n - y) * Φ y ∂(Measure.count : Measure ℤ))
          (2 : ℝ≥0∞) (Measure.count : Measure ℤ) :=
    eLpNorm_mono_enorm (hf := by pw_aesm) hpoint
  -- Young's convolution inequality at the endpoint `p = 1`: `ℓ¹ ∗ ℓ² → ℓ²`.
  have hconv : eLpNorm (fun n : ℤ => ∫⁻ y, K (n - y) * Φ y ∂(Measure.count : Measure ℤ))
        (2 : ℝ≥0∞) (Measure.count : Measure ℤ)
      ≤ eLpNorm K (ENNReal.ofReal (1 : ℝ)) (Measure.count : Measure ℤ)
        * eLpNorm Φ (2 : ℝ≥0∞) (Measure.count : Measure ℤ) := by
    have h := Commons.Analysis.Convolution.eLpNorm_convolution_le_ennreal
      (K := K) (Φ := Φ) (p := (2 : ℝ)) (q := (2 : ℝ)) (r := (1 : ℝ))
      (by norm_num) le_rfl (by norm_num) hKae hΦae
    simpa only [ENNReal.ofReal_ofNat] using h
  -- `‖K‖_{ℓ¹}` is `∑' j, ‖kern j‖`.
  have hKnorm : eLpNorm K (ENNReal.ofReal (1 : ℝ)) (Measure.count : Measure ℤ)
      = ENNReal.ofReal (∑' j : ℤ, ‖kern j‖) := by
    rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), lintegral_count]
    rw [ENNReal.ofReal_tsum_of_nonneg (f := fun j : ℤ => ‖kern j‖)
      (fun j => norm_nonneg _) hsumm]
    exact tsum_congr (fun j => by simp [hK])
  have hΦnorm : eLpNorm Φ (2 : ℝ≥0∞) (Measure.count : Measure ℤ)
      = eLpNorm f (2 : ℝ≥0∞) (Measure.count : Measure ℤ) := by
    rw [hΦ]
    exact eLpNorm_enorm (hf := by pw_aesm) f
  calc eLpNorm (Work.KMTContract.kmtProj ρ l k f) (2 : ℝ≥0∞) (Measure.count : Measure ℤ)
      ≤ eLpNorm (fun n : ℤ => ∫⁻ y, K (n - y) * Φ y ∂(Measure.count : Measure ℤ))
          (2 : ℝ≥0∞) (Measure.count : Measure ℤ) := hstep2
    _ ≤ eLpNorm K (ENNReal.ofReal (1 : ℝ)) (Measure.count : Measure ℤ)
          * eLpNorm Φ (2 : ℝ≥0∞) (Measure.count : Measure ℤ) := hconv
    _ = ENNReal.ofReal (∑' j : ℤ, ‖kern j‖) * eLpNorm f (2 : ℝ≥0∞)
          (Measure.count : Measure ℤ) := by rw [hKnorm, hΦnorm]
    _ ≤ ENNReal.ofReal ((∑' j : ℤ, ‖kern j‖) + 1) * eLpNorm f (2 : ℝ≥0∞)
          (Measure.count : Measure ℤ) := by
        gcongr
        linarith

/-! ## From `ℓ²` inputs to square summability -/

/-- An `ℓ²` sequence stays square summable under an IW projection: `kmtProj ρ l k` maps
`ℓ²(ℤ)` into itself (for every `ρ : ℝ`). -/
lemma summable_normSq_kmtProj (ρ : ℝ) (l : ℕ) (k : ℤ) (h : ℤ → ℂ)
    (hh : Summable (fun x : ℤ => ‖h x‖ ^ (2 : ℝ))) :
    Summable (fun x : ℤ => ‖Work.KMTContract.kmtProj ρ l k h x‖ ^ (2 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := eLpNorm_kmtProj_two_le ρ l k
  -- `hh` in the natural-number-power form expected by the `ℓ²`-dictionary.
  have hsumm2 : Summable (fun x : ℤ => ‖h x‖ ^ 2) :=
    hh.congr (fun x => Real.rpow_two (‖h x‖))
  have hh2 : eLpNorm h (2 : ℝ≥0∞) (Measure.count : Measure ℤ)
      = ENNReal.ofReal ((∑' x : ℤ, ‖h x‖ ^ 2) ^ (1 / 2 : ℝ)) :=
    Work.KMTAreas.A4.eLpNorm_two_count_eq_ofReal hsumm2
  have hb := hC h
  rw [hh2] at hb
  -- The `ℓ²` seminorm of the projection is finite.
  have hfin : eLpNorm (Work.KMTContract.kmtProj ρ l k h) (2 : ℝ≥0∞) (Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal (C * (∑' x : ℤ, ‖h x‖ ^ 2) ^ (1 / 2 : ℝ)) := by
    rw [ENNReal.ofReal_mul hC0]
    exact hb
  -- Finiteness of the `ℓ²` seminorm on the counting measure is square summability.
  have hs := Work.KMTAreas.A4.summable_norm_sq_of_eLpNorm_le hfin
  exact hs.congr (fun x => (Real.rpow_two (‖Work.KMTContract.kmtProj ρ l k h x‖)).symm)

/-- `‖a - b‖² ≤ 2 (‖a‖² + ‖b‖²)` for complex numbers (in the `ℝ`-power notation). -/
lemma normSq_sub_le_two_mul (a b : ℂ) :
    ‖a - b‖ ^ (2 : ℝ) ≤ 2 * (‖a‖ ^ (2 : ℝ) + ‖b‖ ^ (2 : ℝ)) := by
  rw [Real.rpow_two, Real.rpow_two, Real.rpow_two]
  have h1 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
  have h2 : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  linarith

/-! ## The target -/

/-- **The increments of the low-pass family `lpf ρ l m₀ · = kmtProj ρ l (-(m₀+·))` are square
summable for `ℓ²` inputs.**

This is the size estimate behind the convergence of the low-pass (IW) approximation: the
increment `lpf ρ l m₀ (k+1) h − lpf ρ l m₀ k h` lies in `ℓ²(ℤ)` whenever `h` does.  It is proved
by bounding each increment by the two terms separately (`‖a-b‖² ≤ 2(‖a‖²+‖b‖²)`) and using the
`ℓ²`-boundedness of the two IW projections.

No hypothesis on `ρ` beyond `ρ : ℝ` is used. -/
theorem summable_normSq_incFam (ρ : ℝ) (l m₀ k : ℕ) (h : ℤ → ℂ)
    (hh : Summable (fun x : ℤ => ‖h x‖ ^ (2 : ℝ))) :
    Summable (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (k + 1) h x
        - Work.KMTAreas.A7Hi.lpf ρ l m₀ k h x‖ ^ (2 : ℝ)) := by
  have h1 := summable_normSq_kmtProj ρ l (-((m₀ : ℤ) + ((k + 1 : ℕ) : ℤ))) h hh
  have h2 := summable_normSq_kmtProj ρ l (-((m₀ : ℤ) + ((k : ℕ) : ℤ))) h hh
  have h1' : Summable (fun x : ℤ => ‖lpf ρ l m₀ (k + 1) h x‖ ^ (2 : ℝ)) := by
    simpa only [lpf] using h1
  have h2' : Summable (fun x : ℤ => ‖lpf ρ l m₀ k h x‖ ^ (2 : ℝ)) := by
    simpa only [lpf] using h2
  have hmaj : Summable (fun x : ℤ =>
      2 * (‖lpf ρ l m₀ (k + 1) h x‖ ^ (2 : ℝ) + ‖lpf ρ l m₀ k h x‖ ^ (2 : ℝ))) :=
    (h1'.add h2').mul_left 2
  refine Summable.of_nonneg_of_le (fun x => Real.rpow_nonneg (norm_nonneg _) 2)
    (fun x => normSq_sub_le_two_mul _ _) hmaj

end Work.KMTAreas.A7Hi
