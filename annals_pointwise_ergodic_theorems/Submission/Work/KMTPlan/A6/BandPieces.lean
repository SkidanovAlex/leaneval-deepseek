/-
# The frequency-band pieces of the twisted bilinear multiplier `BtwistEx`

`Work.KMTPlan.A6.BtwistEx` is a bilinear convolution whose arithmetic kernel is the *finite*
double sum

  `arithKernelEx j₁ j₂ = ∑_{α ∈ diffFreqs ρ l₁} ∑_{β ∈ diffFreqs ρ l₂}
        mZ P q α β · fourier (-j₁) α · fourier (-j₂) β`.

Because the frequency sums are finite, the whole `tsum` defining `BtwistEx` may be rearranged,
and `BtwistEx` becomes a *sum of products of two linear pieces*:

  `BtwistEx ρ P l₁ l₂ m₁ m₂ h k x
     = ∑_{α,β} mZ P q α β · bandPiece m₁ α h x · bandPiece m₂ β k x`,

where the **band piece** of `h` at the window `m` and the arithmetic frequency `α` is

  `bandPiece m α h x = ∑'_j cw m j · fourier (-j) α · h (x - j)`.

This is the unconditional algebraic reduction on which every subsequent step of the proof of the
paper's Lemma `ssu` rests (see `NOTES_A6_ssuBtwistEx_SESSION3.md`, §1.1).  It requires no
hypothesis on `m` beyond the summability of its `cw`-coefficients and no hypothesis at all on `h`,
`k` beyond `ℓ²`.

The second content of this file is the `ℓ¹`-kernel (Young) bound

  `eLpNorm (bandPiece m α h) 2 count ≤ (∑'_j ‖cw m j‖) · eLpNorm h 2 count`,

which is the correct replacement for the *false* `ℓ²`-bound `‖cw m‖₂‖h‖₂` (the latter only
bounds the sup norm, see `NOTES_A6_ssuBtwistEx_SESSION3.md`, §1.2).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallDefs
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.KMTAreas.A7

/-- **The band piece of `h` at the arithmetic frequency `α` for the window `m`**:
`bandPiece m α h x = ∑'_j cw m j · fourier (-j) α · h (x - j)`.

This is the "`α`-th band" of the linear multiplier with symbol `m(·+α)`, inserted into the
bilinear kernel of `BtwistEx`. -/
noncomputable def bandPiece (m : ℝ → ℂ) (α : Work.Analysis.IonescuWainger.Circle)
    (h : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j : ℤ, cw m j * fourier (T := 1) (-j) α * h (x - j)

theorem bandPiece_apply (m : ℝ → ℂ) (α : Work.Analysis.IonescuWainger.Circle) (h : ℤ → ℂ)
    (x : ℤ) :
    bandPiece m α h x = ∑' j : ℤ, cw m j * fourier (T := 1) (-j) α * h (x - j) := rfl

/-! ## Elementary manipulations of the pieces -/

theorem bandPiece_zero_fun (m : ℝ → ℂ) (α : Work.Analysis.IonescuWainger.Circle) :
    bandPiece m α (fun _ : ℤ => 0) = fun _ : ℤ => 0 := by
  funext x
  simp [bandPiece]

/-! ## The `ℓ¹`-Young bound -/

/-- The characters have `enorm` one. -/
private theorem enorm_fourier_char (j : ℤ) (α : Work.Analysis.IonescuWainger.Circle) :
    ‖(fourier (T := 1) (-j)) α‖ₑ = 1 := by
  have h1 : ‖(fourier (T := 1) (-j)) α‖ = 1 := Circle.norm_coe _
  rw [← enorm_norm, h1]
  simp

/-- `eLpNorm` of a constant multiple of a translate, for `ℂ`-valued functions. -/
private theorem eLpNorm_const_mul_sub_right (c : ℂ) (h : ℤ → ℂ) (j : ℤ) :
    eLpNorm (fun x : ℤ => c * h (x - j)) 2 Measure.count
      = ‖c‖ₑ * eLpNorm h 2 Measure.count := by
  have key : eLpNorm (fun x : ℤ => c * h (x - j)) (ENNReal.ofReal 2) Measure.count
      = ‖c‖ₑ * eLpNorm h (ENNReal.ofReal 2) Measure.count := by
    rw [← MeasureTheory.eLpNorm_enorm (hf := by pw_aesm) (f := fun x : ℤ => c * h (x - j))
      (p := ENNReal.ofReal 2) (μ := Measure.count)]
    have hpt : (fun x : ℤ => ‖c * h (x - j)‖ₑ)
        = fun x : ℤ => ‖c‖ₑ * ‖h (x - j)‖ₑ := by
      funext x; rw [enorm_mul]
    rw [hpt, Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
      (by simp) (by simp) (by simp)]
    congr 1
    exact (Commons.Analysis.Convolution.eLpNorm_sub_right_ennreal
      (μ := Measure.count) (fun w : ℤ => ‖h w‖ₑ) j (s := 2) (by norm_num : (0:ℝ) < 2)).trans
      (MeasureTheory.eLpNorm_enorm (hf := by pw_aesm) (f := h)
        (p := ENNReal.ofReal 2) (μ := Measure.count))
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num]
  exact key

/-- The `c`-multiple of a character has the same `enorm` as `c`. -/
private theorem enorm_mul_char (c : ℂ) (j : ℤ)
    (α : Work.Analysis.IonescuWainger.Circle) :
    ‖c * fourier (T := 1) (-j) α‖ₑ = ‖c‖ₑ := by
  rw [enorm_mul, enorm_fourier_char, mul_one]

/-- **Young / `ℓ¹`-kernel bound for a band piece.**  The `ℓ²` norm of the band piece is
controlled by the `ℓ¹` mass of the window's `cw`-coefficients times the `ℓ²` norm of `h`:
this is the correct bound (the `ℓ²` analogue is false). -/
theorem eLpNorm_bandPiece_le (m : ℝ → ℂ) (α : Work.Analysis.IonescuWainger.Circle)
    (h : ℤ → ℂ) :
    eLpNorm (bandPiece m α h) 2 Measure.count
      ≤ (∑' j : ℤ, ‖cw m j‖ₑ) * eLpNorm h 2 Measure.count := by
  have hmeas : ∀ j : ℤ, AEMeasurable
      (fun x : ℤ => ‖cw m j * fourier (T := 1) (-j) α * h (x - j)‖ₑ) Measure.count :=
    fun j => (measurable_of_countable (fun x : ℤ =>
      ‖cw m j * fourier (T := 1) (-j) α * h (x - j)‖ₑ)).aemeasurable
  have hpt : ∀ x : ℤ, ‖bandPiece m α h x‖ₑ
      ≤ ∑' j : ℤ, ‖cw m j * fourier (T := 1) (-j) α * h (x - j)‖ₑ :=
    fun x => enorm_tsum_le_tsum_enorm
  have hterm : ∀ j : ℤ, eLpNorm
      (fun x : ℤ => ‖cw m j * fourier (T := 1) (-j) α * h (x - j)‖ₑ) 2 Measure.count
        = ‖cw m j‖ₑ * eLpNorm h 2 Measure.count := by
    intro j
    rw [MeasureTheory.eLpNorm_enorm (hf := by pw_aesm), eLpNorm_const_mul_sub_right, enorm_mul_char]
  calc eLpNorm (bandPiece m α h) 2 Measure.count
      ≤ eLpNorm (fun x : ℤ => ∑' j : ℤ,
          ‖cw m j * fourier (T := 1) (-j) α * h (x - j)‖ₑ) 2 Measure.count :=
        MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hpt
    _ ≤ ∑' j : ℤ, eLpNorm (fun x : ℤ =>
          ‖cw m j * fourier (T := 1) (-j) α * h (x - j)‖ₑ) 2 Measure.count :=
        Submission.PointwiseErgodicTheorems.eLpNorm_tsum_le_tsum_eLpNorm
          (μ := Measure.count) (p := 2) (by norm_num) hmeas
    _ = ∑' j : ℤ, ‖cw m j‖ₑ * eLpNorm h 2 Measure.count := tsum_congr hterm
    _ = (∑' j : ℤ, ‖cw m j‖ₑ) * eLpNorm h 2 Measure.count :=
        ENNReal.tsum_mul_right

/-! ## The `ℓ¹`-coefficient Fourier series: continuous and bounded

If the coefficient sequence is summable, the Fourier series converges **uniformly** (Weierstrass
M-test, since `‖fourier j ξ‖ = 1`), so its sum is continuous and bounded by the `ℓ¹` mass of the
coefficients.  These two lemmas are the reusable core of "Plancherel for `L¹` functions with
summable Fourier coefficients" (`KMTPlan/A6/eq_tsum_fourierCoeff_of_summable`, session-4 notes
§16), and hence of the R2 reduction `cw φ ∈ ℓ¹ ⟹ MemLp (periodize φ) ⊤`. -/

/-- **The Fourier series with summable coefficients is continuous.** -/
theorem continuous_tsum_fourier_mul (c : ℤ → ℂ) (hs : Summable (fun j : ℤ => ‖c j‖)) :
    Continuous (fun ξ : Work.Analysis.IonescuWainger.Circle =>
      ∑' j : ℤ, c j * fourier (T := 1) j ξ) := by
  refine continuous_tsum (fun j : ℤ => ?_) (u := fun j : ℤ => ‖c j‖) hs (fun n x => ?_)
  · continuity
  · have h1 : ‖(fourier (T := 1) n) x‖ = 1 := Circle.norm_coe _
    rw [norm_mul, h1, mul_one]

/-- **The Fourier series with summable coefficients is bounded by the `ℓ¹` mass of the
coefficients.** -/
theorem norm_tsum_fourier_mul_le (c : ℤ → ℂ) (hs : Summable (fun j : ℤ => ‖c j‖))
    (ξ : Work.Analysis.IonescuWainger.Circle) :
    ‖∑' j : ℤ, c j * fourier (T := 1) j ξ‖ ≤ ∑' j : ℤ, ‖c j‖ := by
  have hb : (fun j : ℤ => ‖c j * fourier (T := 1) j ξ‖) = fun j : ℤ => ‖c j‖ := by
    funext j
    have h1 : ‖(fourier (T := 1) j) ξ‖ = 1 := Circle.norm_coe _
    rw [norm_mul, h1, mul_one]
  calc ‖∑' j : ℤ, c j * fourier (T := 1) j ξ‖
      ≤ ∑' j : ℤ, ‖c j * fourier (T := 1) j ξ‖ :=
        norm_tsum_le_tsum_norm (f := fun j : ℤ => c j * fourier (T := 1) j ξ)
          (by rw [hb]; exact hs)
    _ = ∑' j : ℤ, ‖c j‖ := by rw [hb]

/-- **The Fourier series with summable coefficients is `L^∞`.**  Immediate from
`continuous_tsum_fourier_mul` and `norm_tsum_fourier_mul_le` via
`MeasureTheory.memLp_top_of_bound`. -/
theorem memLp_top_tsum_fourier_mul (c : ℤ → ℂ) (hs : Summable (fun j : ℤ => ‖c j‖)) :
    MeasureTheory.MemLp (fun ξ : Work.Analysis.IonescuWainger.Circle =>
      ∑' j : ℤ, c j * fourier (T := 1) j ξ) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
  MeasureTheory.memLp_top_of_bound (continuous_tsum_fourier_mul c hs).aestronglyMeasurable _
    (Filter.Eventually.of_forall (norm_tsum_fourier_mul_le c hs))

end

end Work.KMTPlan.A6
