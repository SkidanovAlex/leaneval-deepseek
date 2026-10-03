/-
# The `L²` (Plancherel) fibre estimate: definitions and elementary lemmas

This module gathers the vocabulary and the elementary (Fourier-analytic and `Lp`-bookkeeping)
lemmas on which the `p = 2` fibre estimate `Work.KMTAreas.A7.fiberOp_residueLp_two` rests:

* `Work.KMTAreas.A7.twistSymSet` — the *twisted* Ionescu–Wainger symbol attached to a finite set
  `A ⊆ ℝ/ℤ` of arithmetic frequencies and a symbol `M` on the circle,
  `Σ_{n₀}(ξ) = ∑_{α ∈ A} e(α n₀) M(ξ - α)`;
  `Work.KMTAreas.A7.twistSym ρ l M n₀` is the instance `A = (ℚ/ℤ)_l = iwArithFreqsNew ρ l` that
  matches the fibre `fiberOp ρ l m n₀` of the arithmetic averaging operator
  (`Work.KMTAreas.A7.fiberOp`, which convolves with the kernel
  `j ↦ (∑_{α ∈ (ℚ/ℤ)_l} e(α (n₀-j))) · cw m j`);

* `memLp_twistSym(Set)` — the twisted symbol of an `L^∞` symbol is `L^∞`;

* `variationalNorm_const` — the variational norm of a *constant* family is the norm of its
  value; this is what collapses the variational norm in the `p = 2` statement
  (`fiberOp ρ l m n₀ u` does not depend on the summation index `n`);

* `multiplierOf_apply_eq` — the `n`-th value of a Fourier multiplier is the `n`-th Fourier
  coefficient of `symbol · 𝓕_ℤ F` (the `multiplierOf` form of `iwOpSet_apply_eq`);

* `fourierCoeff_comp_sub` — translating the argument of a symbol by `α` multiplies its Fourier
  coefficients by `fourier (-j) α`; `fourierCoeff_twistSym(Set)` — the Fourier coefficients of
  the twisted symbol are the twisted arithmetic characters times `fourierCoeff M`;

* `arithQ_nsmul_eq_zero(_new)` — the modulus `arithQ ρ l` kills every frequency of
  `(ℚ/ℤ)_{≤l}` as well as every frequency of `(ℚ/ℤ)_l`, the orthogonality needed by
  `arithChar_orthogonality`;

* `eLpNorm_two_count_sq_tsum` — `(‖F‖_{ℓ²})²` for `F ∈ ℓ²(ℤ)` is the series of `‖F x‖²`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.multiplierOfPlancherel
import Submission.Work.KMTPlan.A6.iwConvEqIwOpSetMemlp
import Submission.Work.KMTAreas.A7.variationalNorm_two_step_le

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open PointwiseErgodicTheorems

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- `fourier n` is additive in the point of the circle. -/
theorem fourier_add_point (n : ℤ) (x y : Circ) :
    fourier (T := 1) n (x + y) = fourier (T := 1) n x * fourier (T := 1) n y := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

/-- The **twisted Ionescu–Wainger symbol** attached to a finite set `A` of arithmetic
frequencies: the translates of the symbol `M` at the frequencies of `A`, weighted by the
arithmetic characters `e(α n₀)`,

  `twistSymSet A M n₀ ξ = ∑_{α ∈ A} e(α n₀) · M (ξ - α)`.

Its multiplier is the twist `∑_{α ∈ A} e(α n₀) M_α` of `M` by the characters on `ℤ/q`. -/
noncomputable def twistSymSet (A : Finset Circ) (M : Circ → ℂ) (n₀ : ℤ) : Circ → ℂ :=
  fun ξ => ∑ α ∈ A, fourier (T := 1) n₀ α * M (ξ - α)

/-- The twisted symbol of the fibre `fiberOp ρ l m n₀`, over the *exact*-height arithmetic
frequencies `(ℚ/ℤ)_l = (ℚ/ℤ)_{≤l} \ (ℚ/ℤ)_{≤l-1}` (this is the frequency set appearing in the
definition of `fiberOp`). -/
noncomputable def twistSym (ρ : ℝ) (l : ℕ) (M : Circ → ℂ) (n₀ : ℤ) : Circ → ℂ :=
  twistSymSet (iwArithFreqsNew ρ l) M n₀

/-- The twisted symbol of an `L^∞` symbol is `L^∞` (a finite sum of translates of `M`). -/
theorem memLp_twistSymSet {A : Finset Circ} {M : Circ → ℂ} (hM : MemLp M ⊤ circleMeasure)
    (n₀ : ℤ) : MemLp (twistSymSet A M n₀) ⊤ circleMeasure := by
  have hterm : ∀ α : Circ,
      MemLp (fun ξ : Circ => fourier (T := 1) n₀ α * M (ξ - α)) ⊤ circleMeasure := by
    intro α
    have hcomp : MemLp (fun ξ : Circ => M (ξ - α)) ⊤ circleMeasure := by
      have hmp : MeasurePreserving (fun ξ : Circ => ξ + (-α)) circleMeasure circleMeasure :=
        measurePreserving_add_right circleMeasure (-α)
      have h := hM.comp_measurePreserving hmp
      simpa only [Function.comp_def, sub_eq_add_neg] using h
    exact hcomp.const_mul _
  have heq : twistSymSet A M n₀
      = ∑ α ∈ A, (fun ξ : Circ => fourier (T := 1) n₀ α * M (ξ - α)) := by
    funext ξ
    simp only [twistSymSet, Finset.sum_apply]
  rw [heq]
  exact memLp_finsetSum' _ (fun α _ => hterm α)

/-- The twisted symbol of the fibre is `L^∞`. -/
theorem memLp_twistSym {ρ : ℝ} {l : ℕ} {M : Circ → ℂ} (hM : MemLp M ⊤ circleMeasure)
    (n₀ : ℤ) : MemLp (twistSym ρ l M n₀) ⊤ circleMeasure :=
  memLp_twistSymSet hM n₀

/-- **The variational norm of a constant family.**  For a sequence which is constant in `n`, the
variation part vanishes and only the supremum of the norms survives. -/
theorem variationalNorm_const {r : ℝ≥0} (hr : 1 ≤ r) (c : ℂ) :
    variationalNorm r (fun _ : ℕ => c) = ‖c‖ₑ := by
  refine le_antisymm (variationalNorm_const_le hr c) ?_
  have h := iSup_enorm_le_variationalNorm r (fun _ : ℕ => c) 0
  simpa using h

/-- The `n`-th value of a Fourier multiplier is the `n`-th Fourier coefficient of the product of
its symbol with the Fourier transform of the input (`fourierZ_multiplierOf` on the coefficient
side; the `multiplierOf` form of `Work.KMTPlan.A6.iwOpSet_apply_eq`). -/
theorem multiplierOf_apply_eq (Ψ : Circ → ℂ) (hΨ : MemLp Ψ ⊤ circleMeasure) (F : L2Z)
    (n : ℤ) :
    ⇑(multiplierOf Ψ hΨ F) n = fourierCoeff (⇑(hΨ.toLp Ψ • fourierZ F)) n := by
  have hsymm : fourierZ.symm = (fourierBasis (T := 1)).repr := rfl
  have h1 : ⇑(multiplierOf Ψ hΨ F) n
      = (fourierZ.symm (hΨ.toLp Ψ • fourierZ F)) n := rfl
  rw [h1, hsymm]
  exact fourierBasis_repr _ n

/-- Translating the argument of a symbol by `α ∈ ℝ/ℤ` multiplies its Fourier coefficients by the
character `fourier (-j) α`. -/
theorem fourierCoeff_comp_sub (M : Circ → ℂ) (α : Circ) (j : ℤ) :
    fourierCoeff (fun ξ : Circ => M (ξ - α)) j
      = fourier (T := 1) (-j) α * fourierCoeff M j := by
  have hL : (∫ t : Circ, fourier (T := 1) (-j) t • M (t - α) ∂circleMeasure)
      = ∫ s : Circ, fourier (T := 1) (-j) (s + α) • M s ∂circleMeasure := by
    rw [← MeasureTheory.integral_add_right_eq_self
      (fun t : Circ => fourier (T := 1) (-j) t • M (t - α)) α]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [add_sub_cancel_right]
  have hpt : ∀ s : Circ, fourier (T := 1) (-j) (s + α) • M s
      = fourier (T := 1) (-j) α • (fourier (T := 1) (-j) s • M s) := by
    intro s
    rw [fourier_add_point, mul_smul, smul_comm]
  have hR : (∫ s : Circ, fourier (T := 1) (-j) (s + α) • M s ∂circleMeasure)
      = fourier (T := 1) (-j) α * (∫ s : Circ, fourier (T := 1) (-j) s • M s
          ∂circleMeasure) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_smul, smul_eq_mul]
  show (∫ t : Circ, fourier (T := 1) (-j) t • M (t - α) ∂circleMeasure)
      = fourier (T := 1) (-j) α * (∫ t : Circ, fourier (T := 1) (-j) t • M t
          ∂circleMeasure)
  rw [hL, hR]

/-- `(ℚ/ℤ)_l ⊆ (ℚ/ℤ)_{≤l}`. -/
theorem mem_iwArithFreqsNew_le {ρ : ℝ} {l : ℕ} {α : Circ} (h : α ∈ iwArithFreqsNew ρ l) :
    α ∈ iwArithFreqs ρ l :=
  (Finset.mem_sdiff.mp h).1

/-- The common denominator `arithQ ρ l = max 1 (lcm P_{≤l})` is the lcm `iwQl ρ l` itself. -/
theorem arithQ_eq_iwQl' (ρ : ℝ) (l : ℕ) : arithQ ρ l = iwQl ρ l :=
  max_eq_right (Nat.succ_le_of_lt (iwQl_pos (ρ := ρ) (l := l)))

/-- The modulus `arithQ ρ l` kills every frequency of `(ℚ/ℤ)_{≤l}`; this is the orthogonality
hypothesis of `arithChar_orthogonality`. -/
theorem arithQ_nsmul_eq_zero {ρ : ℝ} {l : ℕ} {α : Circ} (h : α ∈ iwArithFreqs ρ l) :
    arithQ ρ l • α = 0 := by
  rw [arithQ_eq_iwQl']
  exact iwQl_nsmul_eq_zero h

/-- The modulus `arithQ ρ l` kills every *exact*-height frequency `α ∈ (ℚ/ℤ)_l`. -/
theorem arithQ_nsmul_eq_zero_new {ρ : ℝ} {l : ℕ} {α : Circ} (h : α ∈ iwArithFreqsNew ρ l) :
    arithQ ρ l • α = 0 :=
  arithQ_nsmul_eq_zero (mem_iwArithFreqsNew_le h)

/-- **The Fourier coefficients of the twisted symbol.**  The `j`-th Fourier coefficient of
`twistSymSet A M n₀` is the twisted arithmetic character sum times `fourierCoeff M j`:

  `fourierCoeff (twistSymSet A M n₀) j = (∑_{α ∈ A} e(α (n₀ - j))) · fourierCoeff M j`. -/
theorem fourierCoeff_twistSymSet (A : Finset Circ) {M : Circ → ℂ} (hM : MemLp M ⊤ circleMeasure)
    (n₀ j : ℤ) :
    fourierCoeff (twistSymSet A M n₀) j
      = (∑ α ∈ A, fourier (T := 1) (n₀ - j) α) * fourierCoeff M j := by
  haveI : IsFiniteMeasure circleMeasure := inferInstance
  have hMint : Integrable M circleMeasure := hM.integrable le_top
  have hterm : ∀ α ∈ A, Integrable (fun ξ : Circ => fourier (T := 1) n₀ α * M (ξ - α))
      circleMeasure := by
    intro α _
    have h1 : Integrable (fun ξ : Circ => M (ξ - α)) circleMeasure := by
      have h := hMint.comp_add_right (-α)
      simpa only [sub_eq_add_neg] using h
    exact h1.const_mul _
  calc fourierCoeff (twistSymSet A M n₀) j
      = fourierCoeff (∑ α ∈ A, fun ξ : Circ => fourier (T := 1) n₀ α * M (ξ - α)) j := by
        rw [show twistSymSet A M n₀
            = ∑ α ∈ A, (fun ξ : Circ => fourier (T := 1) n₀ α * M (ξ - α)) from by
          funext ξ; simp only [twistSymSet, Finset.sum_apply]]
    _ = ∑ α ∈ A, fourierCoeff (fun ξ : Circ => fourier (T := 1) n₀ α * M (ξ - α)) j :=
        by simpa only [Finset.sum_apply] using congrFun (fourierCoeff.sum A _ hterm) j
    _ = ∑ α ∈ A, fourier (T := 1) n₀ α * (fourier (T := 1) (-j) α * fourierCoeff M j) := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [fourierCoeff.const_mul, fourierCoeff_comp_sub]
    _ = (∑ α ∈ A, fourier (T := 1) (n₀ - j) α) * fourierCoeff M j := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [show n₀ - j = n₀ + (-j) by ring, fourier_add]
        ring

/-- The Fourier coefficients of the twisted symbol of the fibre. -/
theorem fourierCoeff_twistSym {ρ : ℝ} {l : ℕ} {M : Circ → ℂ} (hM : MemLp M ⊤ circleMeasure)
    (n₀ j : ℤ) :
    fourierCoeff (twistSym ρ l M n₀) j
      = (∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (n₀ - j) α) * fourierCoeff M j :=
  fourierCoeff_twistSymSet _ hM n₀ j

/-- The unfolding of `fiberOp` as the convolution with the kernel
`j ↦ (∑_{α ∈ (ℚ/ℤ)_l} e(α (n₀-j))) · cw m j`. -/
theorem fiberOp_eq_kernel_conv (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (n₀ : ℤ) (u : ℤ → ℂ) :
    fiberOp ρ l m n₀ u
      = fun x => ∑' j : ℤ,
          (∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (n₀ - j) α) * cw m j * u (x - j) :=
  rfl

/-- For `F ∈ ℓ²(ℤ)`, the square of its `ℓ²`-seminorm is the series of the squares of its values. -/
theorem eLpNorm_two_count_sq_tsum (F : L2Z) :
    (eLpNorm (⇑F) (2 : ℝ≥0∞) Measure.count) ^ (2 : ℕ)
      = ∑' x : ℤ, ‖F x‖ₑ ^ (2 : ℕ) := by
  rw [Work.KMTPlan.A6.eLpNorm_two_sq (⇑F), lintegral_count]

end

end Work.KMTAreas.A7
