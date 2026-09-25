import Mathlib
import Submission.Work.BourgainPlan.Thm52.largeScaleBound_of_sampling
import Submission.Work.BourgainPlan.IonescuWainger.sampling_principle_variation_decimated
import Submission.Work.BourgainPlan.IonescuWainger.sampling_principle_variation_kernel_lp

/-!
# The decimated (periodised) sampling principle in kernel form, and on all of `ℓᵖ(ℤ)`

`Work.BourgainPlan.IonescuWainger.sampling_principle_variation_decimated` (KMSZ Definition 5.1(3),
the Magyar–Stein–Wainger sampling principle in the form used by §6.3, i.e. MST Theorem 3.1) states
the `ℓᵖ(ℤ)`-variation bound for the **decimated kernel** `j ↦ Q·[Q ∣ j]·∫ m ξ e^{2πi j ξ} dξ`,
for **finitely supported** inputs.

Two packaging steps are needed before it can be *composed* with the Ionescu–Wainger input for the
weight factor of the major-arc model (KMSZ (6.22)):

* `decimatedKernel` names that kernel, and
  **`sampling_principle_variation_decimated_kernel`** restates the sampling principle in the
  kernel form `∫⁻_k (V²(Σ_{j ∈ a.support} K n (k-j) a j))^p ≤ ofReal ((C A)^p) · lpPow p a` which is
  the hypothesis consumed by the extension lemma
  `Work.BourgainPlan.IonescuWainger.sampling_principle_variation_kernel_lp`;
* **`sampling_principle_variation_decimated_lp`** is the resulting *operator-norm* form (the input
  an arbitrary `h ∈ ℓᵖ(ℤ)`, the family defined by the absolutely convergent kernel sum), which is
  the shape in which KMSZ use the sampling principle — as a bound `ℓᵖ → S` on the *whole* space, so
  that it composes with the Theorem 1.9 bound for the weight factor.

Together with `Work.BourgainPlan.Thm52.largeScaleBoundF_comp`-type bookkeeping this produces the
`LargeScaleBound` input of KMSZ Theorem 5.2 for the §6.3 model family; see `Thm52/STATUS.md`.
-/

open MeasureTheory
open scoped ENNReal BigOperators Interval

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.BourgainPlan.Thm52

noncomputable section

/-- **The decimated (periodised) kernel** of a symbol supported in the ball of radius `1/(2Q)`:
`j ↦ Q · [Q ∣ j] · ∫_{-1/2}^{1/2} m ξ e^{2πi j ξ} dξ`.  It is the kernel of the periodisation
`ξ ↦ Σ_{a < Q} m (ξ - a/Q)` of `m` (equivalently: of the `ℤ`-side multiplier
`T_ℤ[J_1 | m K_{Q}]` of KMSZ (5.5)). -/
def decimatedKernel (Q : ℕ) (m : ℝ → ℂ) (j : ℤ) : ℂ :=
  (Q : ℂ) * (if (Q : ℤ) ∣ j then
    (∫ ξ in (-(1/2):ℝ)..(1/2), m ξ *
      Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (ξ : ℂ)))) else 0)

/-- **The sampling principle in kernel form.**  Under the continuous bound `hOp` for the rescaled
symbols `ξ ↦ m n (ξ / Q)`, the decimated kernels `decimatedKernel Q (m n)` obey, for every finitely
supported input `a`, the `ℓᵖ(ℤ)`-variation bound with constant `C·A`, `C = C(p)` independent of
`Q`, `κ`, `m` and `A`.  This is
`Work.BourgainPlan.IonescuWainger.sampling_principle_variation_decimated` with the kernel named and
the right-hand side written as `lpPow`. -/
theorem sampling_principle_variation_decimated_kernel {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ Q : ℕ) (hQ : 1 ≤ Q) (m : ℕ → ℝ → ℂ)
      (hm : ∀ n, MeasureTheory.Integrable (m n))
      (hsupp : ∀ (n : ℕ) (ξ : ℝ),
        ξ ∉ Set.Icc (-(1 / (2 * (Q : ℝ)))) (1 / (2 * (Q : ℝ))) → m n ξ = 0)
      (A : ℝ) (hA : 0 ≤ A)
      (hOp : ∀ (g : ℝ → ℂ), MeasureTheory.Integrable g →
        (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → FourierTransform.fourier g ξ = 0) →
        ∫⁻ x : ℝ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
            (fun n => FourierTransformInv.fourierInv
              (fun ξ : ℝ => m n (ξ / (Q : ℝ)) * FourierTransform.fourier g ξ) x)) ^ p
          ∂MeasureTheory.volume
        ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ p ∂MeasureTheory.volume),
      ∀ a : ℤ →₀ ℂ,
      ∫⁻ k : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
        (fun n : ℕ => ∑ j ∈ a.support, decimatedKernel Q (m n) (k - j) * a j)) ^ p
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((C * A) ^ p) * lpPow p (⇑a) := by
  obtain ⟨C, hCpos, hC⟩ :=
    Work.BourgainPlan.IonescuWainger.sampling_principle_variation_decimated (p := p) hp
  refine ⟨C, hCpos, ?_⟩
  intro κ Q hQ m hm hsupp A hA hOp a
  have ha : ∀ k, k ∉ a.support → (⇑a : ℤ → ℂ) k = 0 := by
    intro k hk
    by_contra hne
    exact hk (Finsupp.mem_support_iff.mpr hne)
  have h := hC κ Q hQ m hm hsupp A hA hOp a.support (⇑a) ha
  rw [lpPow_finsupp_eq_sum (lt_trans zero_lt_one hp) a]
  refine le_of_eq_of_le ?_ h
  simp only [decimatedKernel]

/-- **The sampling principle for the decimated kernel as an operator bound on `ℓᵖ(ℤ)`** — the shape
in which KMSZ use it (a bound `ℓᵖ → S` on the whole space, so that it composes with the
Ionescu–Wainger bound for the weight factor of the major-arc model).

For the decimated kernels of symbols `m n` supported in the ball of radius `1/(2Q)`, obeying the
continuous variation bound `hOp` with constant `A`, and satisfying the Hölder summability
`hKsum` (automatic for a smooth symbol with rapidly decaying Fourier coefficients), the family
`h ↦ (k ↦ Σ'_j K n (k-j) h j)` obeys the variational bound with constant `C·A` *on every* `h ∈ ℓᵖ`:
this is `sampling_principle_variation_decimated_kernel` (finitely supported inputs) extended by
`Work.BourgainPlan.IonescuWainger.sampling_principle_variation_kernel_lp`. -/
theorem sampling_principle_variation_decimated_lp {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ Q : ℕ) (hQ : 1 ≤ Q) (m : ℕ → ℝ → ℂ)
      (hm : ∀ n, MeasureTheory.Integrable (m n))
      (hsupp : ∀ (n : ℕ) (ξ : ℝ),
        ξ ∉ Set.Icc (-(1 / (2 * (Q : ℝ)))) (1 / (2 * (Q : ℝ))) → m n ξ = 0)
      (A : ℝ) (hA : 0 ≤ A)
      (hOp : ∀ (g : ℝ → ℂ), MeasureTheory.Integrable g →
        (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → FourierTransform.fourier g ξ = 0) →
        ∫⁻ x : ℝ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
            (fun n => FourierTransformInv.fourierInv
              (fun ξ : ℝ => m n (ξ / (Q : ℝ)) * FourierTransform.fourier g ξ) x)) ^ p
          ∂MeasureTheory.volume
        ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ p ∂MeasureTheory.volume)
      (hKsum : ∀ n : ℕ, Summable (fun j : ℤ => ‖decimatedKernel Q (m n) j‖ ^ (p / (p - 1))))
      (h : ℤ → ℂ) (hh : Memℓp h (ENNReal.ofReal p)),
      MeasureTheory.eLpNorm (fun k : ℤ => Work.BourgainPlan.Maximal.varRhoFrom 2 κ
          (fun n : ℕ => ∑' j : ℤ, decimatedKernel Q (m n) (k - j) * h j))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C * A)
          * MeasureTheory.eLpNorm h (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hC⟩ := sampling_principle_variation_decimated_kernel (p := p) hp
  exact ⟨C, hCpos, fun κ Q hQ m hm hsupp A hA hOp hKsum h hh =>
    Work.BourgainPlan.IonescuWainger.sampling_principle_variation_kernel_lp (p := p) hp
      (κ := κ) (B := C * A) (mul_nonneg hCpos.le hA) (fun n j => decimatedKernel Q (m n) j) hKsum
      (hC κ Q hQ m hm hsupp A hA hOp) h hh⟩

/-- **`LargeScaleBound` for the §6.3 model family, in the decimated-kernel picture.**  This is the
end-to-end assembly of the sampling-principle half of KMSZ Theorem 5.2: the family
`n ↦ (h ↦ Σ'_j decimatedKernel Q (m n) (k-j) h j)` obeys the `ℓᵖ → V²` bound with constant `C·A`
(by `sampling_principle_variation_decimated_lp`), and composing it with the fixed weight factor `U`
— whose `ℓᵖ` bound `B₂` is the Ionescu–Wainger (Theorem 1.9) input for the weighted flat profile of
the factorisation (6.22) — gives `LargeScaleBoundF` with constant `C·A·B₂` for the composed family.

The remaining object-level step for the §6.3 application is only the identification of the model
operator `opArcW θ w S (m φ)` with this composed family, i.e.
`Thm52.opArcW_eq_decimatedKernel_comp` plus the multi-scale bookkeeping (`kmszMajorData`). -/
theorem LargeScaleBoundF_model_of_sampling {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ Q : ℕ) (hQ : 1 ≤ Q) (m : ℕ → ℝ → ℂ)
      (hm : ∀ n, MeasureTheory.Integrable (m n))
      (hsupp : ∀ (n : ℕ) (ξ : ℝ),
        ξ ∉ Set.Icc (-(1 / (2 * (Q : ℝ)))) (1 / (2 * (Q : ℝ))) → m n ξ = 0)
      (A : ℝ) (hA : 0 ≤ A)
      (hOp : ∀ (g : ℝ → ℂ), MeasureTheory.Integrable g →
        (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → FourierTransform.fourier g ξ = 0) →
        ∫⁻ x : ℝ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
            (fun n => FourierTransformInv.fourierInv
              (fun ξ : ℝ => m n (ξ / (Q : ℝ)) * FourierTransform.fourier g ξ) x)) ^ p
          ∂MeasureTheory.volume
        ≤ ENNReal.ofReal (A ^ p) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ p ∂MeasureTheory.volume)
      (hKsum : ∀ n : ℕ, Summable (fun j : ℤ => ‖decimatedKernel Q (m n) j‖ ^ (p / (p - 1))))
      (U : (ℤ →₀ ℂ) → (ℤ → ℂ)) (B₂ : ℝ) (hB₂ : 0 ≤ B₂)
      (hU : ∀ g : ℤ →₀ ℂ, MeasureTheory.eLpNorm (U g) (ENNReal.ofReal p)
        MeasureTheory.Measure.count ≤ ENNReal.ofReal B₂ * lpNorm p (⇑g))
      (hUmem : ∀ g : ℤ →₀ ℂ, Memℓp (U g) (ENNReal.ofReal p)),
      LargeScaleBoundF p (fun n g => fun k : ℤ =>
        ∑' j : ℤ, decimatedKernel Q (m n) (k - j) * (U g) j) κ (C * A * B₂) := by
  obtain ⟨C, hCpos, hC⟩ := sampling_principle_variation_decimated_lp (p := p) hp
  refine ⟨C, hCpos, ?_⟩
  intro κ Q hQ m hm hsupp A hA hOp hKsum U B₂ hB₂ hU hUmem g
  have h1 := hC κ Q hQ m hm hsupp A hA hOp hKsum (U g) (hUmem g)
  have hCA : (0:ℝ) ≤ C * A := mul_nonneg hCpos.le hA
  calc MeasureTheory.eLpNorm
        (fun k : ℤ => Work.BourgainPlan.Maximal.varRhoFrom 2 κ
          (fun n : ℕ => ∑' j : ℤ, decimatedKernel Q (m n) (k - j) * (U g) j))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C * A) * MeasureTheory.eLpNorm (U g) (ENNReal.ofReal p)
          MeasureTheory.Measure.count := h1
    _ ≤ ENNReal.ofReal (C * A) * (ENNReal.ofReal B₂ * lpNorm p (⇑g)) :=
        mul_le_mul_right (hU g) _
    _ = ENNReal.ofReal (C * A * B₂) * lpNorm p (⇑g) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCA]

/-- **The composition of the sampling principle with a fixed factor** (the `(5.5)` mechanism of
KMSZ): if the family `T` obeys the `ℓᵖ → V²` bound of the sampling principle with constant `B₁` on
*all* of `ℤ → ℂ` (the operator-norm form, produced by `sampling_principle_variation_decimated_lp`)
and a fixed operator `U` — here always a multiplier applied to a finitely supported input, e.g. the
Ionescu–Wainger weight factor of the major-arc model — is `ℓᵖ`-bounded with constant `B₂`, then the
composed family `n ↦ T n (U ·)` obeys `LargeScaleBoundF` with constant `B₁ * B₂`.

This is the packaging that turns the factorisation (6.22) of the §6.3 model into the
`LargeScaleBound` input of `Work.BourgainPlan.Thm52.exists_thm52_finsupp`. -/
theorem largeScaleBoundF_comp_lp {p : ℝ} {κ : ℕ} {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁)
    {T : ℕ → (ℤ → ℂ) → (ℤ → ℂ)} {U : (ℤ →₀ ℂ) → (ℤ → ℂ)}
    (hT : ∀ h : ℤ → ℂ, MeasureTheory.eLpNorm
        (fun k : ℤ => Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n : ℕ => T n h k))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal B₁ * MeasureTheory.eLpNorm h (ENNReal.ofReal p) MeasureTheory.Measure.count)
    (hU : ∀ g : ℤ →₀ ℂ, MeasureTheory.eLpNorm (U g) (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal B₂ * lpNorm p (⇑g)) :
    LargeScaleBoundF p (fun n g => T n (U g)) κ (B₁ * B₂) := by
  intro g
  calc MeasureTheory.eLpNorm
        (fun k : ℤ => Work.BourgainPlan.Maximal.varRhoFrom 2 κ
          (fun n : ℕ => T n (U g) k))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal B₁ * MeasureTheory.eLpNorm (U g) (ENNReal.ofReal p)
          MeasureTheory.Measure.count := hT (U g)
    _ ≤ ENNReal.ofReal B₁ * (ENNReal.ofReal B₂ * lpNorm p (⇑g)) :=
        mul_le_mul_right (hU g) _
    _ = ENNReal.ofReal (B₁ * B₂) * lpNorm p (⇑g) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hB₁]

end

end Work.BourgainPlan.Thm52
