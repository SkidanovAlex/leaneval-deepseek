/-
# The fibre decomposition of the twisted bilinear multiplier, for arbitrary arithmetic
# frequency sets

The model tuple of `Work.KMTAreas.A7.Large/Defs.lean` is the `t`-integral of the twisted bilinear
multiplier `Btwist ρ P l₁ l₂ m₁ m₂` applied to the two Ionescu--Wainger projections of the bumps
`φ_{N,t}`, `φ̃_{N,t}`.  The relevant portion of the arithmetic frequency set depends on which
projection is used:

* the *height-`≤ l`* multipliers `Tle ρ l φ` use `iwArithFreqs ρ l = (ℚ/ℤ)_{≤l}` (and the
  corresponding `arithChar`, `fiberOp`, `Hcl`, `Gcl` of `LargeInterface.lean`);
* the *exact-height* multipliers `Tex ρ l φ` use `iwArithFreqsNew ρ l = (ℚ/ℤ)_l`, the exact
  height-`2^l` frequencies of the paper (KMT, (2.7): `(ℚ/ℤ)_l = (ℚ/ℤ)_{≤l} \ (ℚ/ℤ)_{≤l-1}`,
  `T^l_φ = T_{Proj(φ ⊗ 1_{(ℚ/ℤ)_l})}`).

Since the paper's §6 model operator uses the *exact-height* multipliers (the §5 pieces of the
contract are the exact-height projections `Π_{l,≤m} = Π_{≤l,≤m} - Π_{≤l-1,≤m}`), the fibre
decomposition and the fibre estimates are needed for both choices.  This file provides the objects
and the fibre decomposition for an **arbitrary** finite set `A` of circle frequencies, so that both
readings are instances.

## Main definitions

* `arithCharSet A y = ∑_{α ∈ A} e(α y)`;
* `arithKernelSet P q A₁ A₂ j₁ j₂ = ∑_{α₁∈A₁}∑_{α₂∈A₂} mZ P q α₁ α₂ e(-j₁α₁) e(-j₂α₂)`;
* `fiberOpSet A m n₀ u`, `fiberOpPSet P A m n₀ v` — the fibres at the residue `n₀`;
* `BtwistSet ρ P l₁ l₂ A₁ A₂ m₁ m₂ h k` — the twisted bilinear multiplier with the pair of
  frequency sets `(A₁,A₂)`.

The identification lemmas at the end show that `arithChar`/`arithKernel`/`fiberOp`/`Btwist` and
`arithKernelExact`/`BtwistExact` are the instances `Aᵢ = iwArithFreqs ρ lᵢ` and
`Aᵢ = iwArithFreqsNew ρ lᵢ` respectively (definitionally).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-- The arithmetic character sum of an arbitrary finite set of circle frequencies:
`∑_{α ∈ A} e(α y)`. -/
noncomputable def arithCharSet (A : Finset Work.Analysis.IonescuWainger.Circle) (y : ℤ) : ℂ :=
  ∑ α ∈ A, fourier (T := 1) y α

/-- The arithmetic kernel of the twisted bilinear multiplier at an arbitrary pair of frequency
sets: the double Fourier coefficient `∑_{α₁∈A₁}∑_{α₂∈A₂} m_Ẑ(α₁,α₂) e(-j₁α₁-j₂α₂)`. -/
noncomputable def arithKernelSet (P : ℤ[X]) (q : ℕ) (A₁ A₂ : Finset Work.Analysis.IonescuWainger.Circle) (j₁ j₂ : ℤ) : ℂ :=
  ∑ α₁ ∈ A₁, ∑ α₂ ∈ A₂,
    mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂

/-- The fibre of the twisted projection at the residue `n₀` (first variable), for an arbitrary
frequency set: the convolution with the kernel `j ↦ e(α(n₀-j)) · 𝓕⁻m_j`. -/
noncomputable def fiberOpSet (A : Finset Work.Analysis.IonescuWainger.Circle) (m : ℝ → ℂ) (n₀ : ℤ) (u : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j : ℤ, arithCharSet A (n₀ - j) * cw m j * u (x - j)

/-- The fibre of the twisted projection at the residue `n₀` (second variable), with the
polynomial twist `P`, for an arbitrary frequency set. -/
noncomputable def fiberOpPSet (P : ℤ[X]) (A : Finset Work.Analysis.IonescuWainger.Circle) (m : ℝ → ℂ) (n₀ : ℤ)
    (v : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j : ℤ, arithCharSet A (P.eval n₀ - j) * cw m j * v (x - j)

/-- The twisted bilinear multiplier with a product symbol, at an arbitrary pair of arithmetic
frequency sets, in kernel form. -/
noncomputable def BtwistSet (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (A₁ A₂ : Finset Work.Analysis.IonescuWainger.Circle)
    (m₁ m₂ : ℝ → ℂ) (h k : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j₁ : ℤ, ∑' j₂ : ℤ,
    arithKernelSet P (arithQ ρ (max l₁ l₂)) A₁ A₂ j₁ j₂ * cw m₁ j₁ * cw m₂ j₂
      * h (x - j₁) * k (x - j₂)

/-! ## The height-`≤ l` and exact-height objects as instances -/

@[simp] theorem arithCharSet_iwArithFreqs (ρ : ℝ) (l : ℕ) :
    arithCharSet (iwArithFreqs ρ l) = arithChar ρ l := rfl

@[simp] theorem arithCharSet_iwArithFreqsNew (ρ : ℝ) (l : ℕ) (y : ℤ) :
    arithCharSet (iwArithFreqsNew ρ l) y = ∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) y α := rfl

@[simp] theorem arithKernelSet_iwArithFreqs (ρ : ℝ) (P : ℤ[X]) (q l₁ l₂ : ℕ) :
    arithKernelSet P q (iwArithFreqs ρ l₁) (iwArithFreqs ρ l₂) = arithKernel ρ P q l₁ l₂ := rfl

@[simp] theorem arithKernelSet_iwArithFreqsNew (ρ : ℝ) (P : ℤ[X]) (q l₁ l₂ : ℕ) :
    arithKernelSet P q (iwArithFreqsNew ρ l₁) (iwArithFreqsNew ρ l₂)
      = arithKernelExact ρ P q l₁ l₂ := rfl

/-- After the (correct) switch of `modelTuple` to the exact-height multipliers, `fiberOp` is the
**exact-height** fibre, so the name `fiberOp` is definitionally `fiberOpSet (iwArithFreqsNew ρ l)`.
(The height-`≤ l` fibre is, and remains, available as `fiberOpSet (iwArithFreqs ρ l)`.) -/
@[simp] theorem fiberOp_eq_fiberOpSet_iwArithFreqsNew (ρ : ℝ) (l : ℕ) :
    fiberOp ρ l = fiberOpSet (iwArithFreqsNew ρ l) := rfl

@[simp] theorem fiberOpP_eq_fiberOpPSet_iwArithFreqsNew (ρ : ℝ) (P : ℤ[X]) (l : ℕ) :
    fiberOpP ρ P l = fiberOpPSet P (iwArithFreqsNew ρ l) := rfl

@[simp] theorem BtwistSet_iwArithFreqs (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) :
    BtwistSet ρ P l₁ l₂ (iwArithFreqs ρ l₁) (iwArithFreqs ρ l₂) = Btwist ρ P l₁ l₂ := rfl

@[simp] theorem BtwistSet_iwArithFreqsNew (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) :
    BtwistSet ρ P l₁ l₂ (iwArithFreqsNew ρ l₁) (iwArithFreqsNew ρ l₂)
      = BtwistExact ρ P l₁ l₂ := rfl

/-! ## Elementary bounds -/

/-- `fourier y α` has modulus one. -/
lemma norm_fourier_apply_ (y : ℤ) (α : Work.Analysis.IonescuWainger.Circle) :
    ‖fourier (T := 1) y α‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- The arithmetic character sum of a finite frequency set is bounded by its cardinality. -/
lemma norm_arithCharSet_le (A : Finset Work.Analysis.IonescuWainger.Circle) (y : ℤ) :
    ‖arithCharSet A y‖ ≤ (A.card : ℝ) := by
  rw [arithCharSet]
  calc ‖∑ α ∈ A, fourier (T := 1) y α‖ ≤ ∑ α ∈ A, ‖fourier (T := 1) y α‖ := norm_sum_le _ _
    _ = ∑ _α ∈ A, (1 : ℝ) := Finset.sum_congr rfl fun α _ => norm_fourier_apply_ y α
    _ = (A.card : ℝ) := by simp

/-- `mZ` is bounded by `1`. -/
lemma norm_mZ_le_ (P : ℤ[X]) (q : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) :
    ‖mZ P q α₁ α₂‖ ≤ 1 := by
  rw [mZ]
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq; simp
  · have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have h1 : ‖((q : ℂ))⁻¹‖ = ((q : ℝ))⁻¹ := by
      rw [norm_inv, norm_natCast, inv_eq_one_div]
    calc ‖((q : ℂ))⁻¹ * ∑ n ∈ Finset.range q,
            fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
        = ((q : ℝ))⁻¹ * ‖∑ n ∈ Finset.range q,
            fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ := by
          rw [norm_mul, h1]
      _ ≤ ((q : ℝ))⁻¹ * ∑ n ∈ Finset.range q,
            ‖fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ := by
          refine mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = ((q : ℝ))⁻¹ * ∑ _n ∈ Finset.range q, (1 : ℝ) := by
          refine congrArg _ (Finset.sum_congr rfl fun n _ => ?_)
          rw [norm_mul, norm_fourier_apply_, norm_fourier_apply_, mul_one]
      _ = ((q : ℝ))⁻¹ * (q : ℝ) := by simp
      _ = 1 := by field_simp

/-- The arithmetic kernel is bounded by the product of the cardinalities. -/
lemma norm_arithKernelSet_le (P : ℤ[X]) (q : ℕ)
    (A₁ A₂ : Finset Work.Analysis.IonescuWainger.Circle) (j₁ j₂ : ℤ) :
    ‖arithKernelSet P q A₁ A₂ j₁ j₂‖ ≤ (A₁.card : ℝ) * (A₂.card : ℝ) := by
  rw [arithKernelSet]
  calc ‖∑ α₁ ∈ A₁, ∑ α₂ ∈ A₂,
          mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖
      ≤ ∑ α₁ ∈ A₁, ‖∑ α₂ ∈ A₂,
          mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖ :=
        norm_sum_le _ _
    _ ≤ ∑ α₁ ∈ A₁, ∑ α₂ ∈ A₂,
          ‖mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖ :=
        Finset.sum_le_sum fun α₁ _ => norm_sum_le _ _
    _ ≤ ∑ _α₁ ∈ A₁, ∑ _α₂ ∈ A₂, (1 : ℝ) := by
        refine Finset.sum_le_sum fun α₁ _ => Finset.sum_le_sum fun α₂ _ => ?_
        calc ‖mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖
            = ‖mZ P q α₁ α₂‖ := by
              rw [norm_mul, norm_mul, norm_fourier_apply_, norm_fourier_apply_]
              ring
          _ ≤ 1 := norm_mZ_le_ P q α₁ α₂
    _ = (A₁.card : ℝ) * (A₂.card : ℝ) := by simp

end

end Work.KMTAreas.A7
