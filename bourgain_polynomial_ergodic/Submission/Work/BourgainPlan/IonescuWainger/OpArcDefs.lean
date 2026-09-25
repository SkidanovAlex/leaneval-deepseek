import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Defs
import Submission.Work.BourgainPlan.IonescuWainger.ftLp_coeff
import Submission.Work.BourgainPlan.IonescuWainger.ftLp_coeff_integral

/-!
# The multiplier operators `Op_{φ;E}` of Tao's `ortho-apply`(ii)

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4
(Theorem `ortho-apply`(ii), the Rubio de Francia type estimate); see `ARC_ARITH_STATUS.md`
Addendum 4 §4 for the decomposition of the (A4)-upper into this chapter.

Tao's second inequality in `ortho-apply` bounded the `ℓ^p` square function of the modulated
multipliers `Op_{φ; α + Σ_{A₀}} f`, `α ∈ Σ_{(A₀)}`, `A₀ ∈ binom(S,≤k)`, where `φ` is the bump
`∏_j φ₀(ξ_j/ε)` and `Op_{φ;Σ} f` is the Fourier multiplier with symbol `Σ_{β ∈ Σ} φ(· - β)`.

This file builds the vocabulary in the `ℓ²(ℤ) ≅ L²(𝕋)` picture of `FourierL2Defs.lean`:

* `arcTranslate β φ` — the translate `ξ ↦ φ (ξ - β)` of a circle function;
* `arcSymbol φ E` — Tao's symbol `Σ_{β ∈ E} φ(· - β)`;
* `arcSymbolLp φ hφ E` — its class in `L^∞(𝕋)`;
* `opMul Φ f hf` — the multiplier with symbol `Φ ∈ L^∞(𝕋)` acting on the `ℓ²(ℤ)`-sequence `f`,
  defined through its Fourier transform `Φ • 𝓕f` (the `HSMul` of `Lp ℂ ⊤` with `Lp ℂ 2`), whose
  coefficients are recovered with the Hilbert basis `fourierBasis`;
* `opArc φ hφ E f hf` — the special case `Φ = arcSymbol φ E`.

The two structural lemmas are `ftLp_opMul` (the definition is compatible with the `ℓ² ≅ L²`
dictionary) and `hasFreqSupport_opMul` (the frequency support of the multiplier is contained in the
support of the symbol).  The `ℓ^p` estimates themselves are in the companion files
(`opArc_l2`, `opArc_sup`); the `p = 2` endpoint is Plancherel plus the arc-counting bound, the
`p = ∞` endpoint is the `ℓ¹` bound on the convolution kernel.
-/

open MeasureTheory
open scoped lp BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-- The translate `ξ ↦ φ (ξ - β)` of a function on the circle `𝕋 = ℝ/ℤ`. -/
def arcTranslate (β : Circle) (φ : Circle → ℂ) : Circle → ℂ := fun ξ => φ (ξ - β)

/-- Tao's arc symbol `Σ_{β ∈ E} φ(· - β)`. -/
def arcSymbol (φ : Circle → ℂ) (E : Finset Circle) : Circle → ℂ :=
  fun ξ => ∑ β ∈ E, arcTranslate β φ ξ

@[simp] theorem arcTranslate_apply (β : Circle) (φ : Circle → ℂ) (ξ : Circle) :
    arcTranslate β φ ξ = φ (ξ - β) := rfl

@[simp] theorem arcSymbol_apply (φ : Circle → ℂ) (E : Finset Circle) (ξ : Circle) :
    arcSymbol φ E ξ = ∑ β ∈ E, φ (ξ - β) := rfl

theorem arcSymbol_empty (φ : Circle → ℂ) : arcSymbol φ ∅ = 0 := by
  funext ξ; simp [arcSymbol]

theorem arcSymbol_congr {φ ψ : Circle → ℂ} (h : φ = ψ) (E : Finset Circle) :
    arcSymbol φ E = arcSymbol ψ E := by rw [h]

/-- A translate of an a.e.-bounded function is a.e.-bounded (the Haar measure of the circle is
invariant under translation). -/
theorem memLp_arcTranslate {φ : Circle → ℂ} (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (β : Circle) : MemLp (arcTranslate β φ) ⊤ (AddCircle.haarAddCircle (T := 1)) := by
  have hmp : MeasurePreserving (fun ξ : Circle => ξ + (-β)) (AddCircle.haarAddCircle (T := 1))
      (AddCircle.haarAddCircle (T := 1)) := measurePreserving_add_right _ _
  have h := hφ.comp_measurePreserving hmp
  have hf : arcTranslate β φ = fun ξ : Circle => φ (ξ + (-β)) := by
    funext ξ; simp [arcTranslate, sub_eq_add_neg]
  rw [hf]
  exact h

/-- A finite sum of translates of an a.e.-bounded function is a.e.-bounded. -/
theorem memLp_arcSymbol {φ : Circle → ℂ} (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (E : Finset Circle) : MemLp (arcSymbol φ E) ⊤ (AddCircle.haarAddCircle (T := 1)) := by
  have h : arcSymbol φ E = fun ξ => ∑ β ∈ E, arcTranslate β φ ξ := rfl
  rw [h]
  exact memLp_finsetSum E (fun β _ => memLp_arcTranslate hφ β)

/-- The `L^∞(𝕋)`-class of the arc symbol `Σ_{β ∈ E} φ(· - β)`. -/
def arcSymbolLp (φ : Circle → ℂ) (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (E : Finset Circle) : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)) :=
  (memLp_arcSymbol hφ E).toLp (arcSymbol φ E)

theorem arcSymbolLp_coeFn (φ : Circle → ℂ) (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (E : Finset Circle) :
    (arcSymbolLp φ hφ E : Circle → ℂ) =ᵐ[AddCircle.haarAddCircle (T := 1)] arcSymbol φ E :=
  MemLp.coeFn_toLp _

/-- The multiplier on `ℓ²(ℤ)` with symbol `Φ ∈ L^∞(𝕋)`, defined through its Fourier transform. -/
def opMulLp (Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) (f : ℤ → ℂ) (hf : Memℓp f 2) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) :=
  Φ • ftLp f hf

/-- The multiplier on `ℓ²(ℤ)` with symbol `Φ ∈ L^∞(𝕋)`, as a sequence: `𝓕(Op f) = Φ · 𝓕f`. -/
def opMul (Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) (f : ℤ → ℂ) (hf : Memℓp f 2) :
    ℤ → ℂ :=
  fun n => ((fourierBasis (T := 1)).repr (opMulLp Φ f hf) : ℤ → ℂ) n

/-- Tao's operator `Op_{φ;E} f`, the multiplier with symbol `Σ_{β ∈ E} φ(· - β)`. -/
def opArc (φ : Circle → ℂ) (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (E : Finset Circle) (f : ℤ → ℂ) (hf : Memℓp f 2) : ℤ → ℂ :=
  opMul (arcSymbolLp φ hφ E) f hf

/-- The multiplier of a `𝓛²`-sequence is a `ℓ²`-sequence. -/
theorem opMul_memℓp (Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) (f : ℤ → ℂ)
    (hf : Memℓp f 2) : Memℓp (opMul Φ f hf) 2 :=
  ((fourierBasis (T := 1)).repr (opMulLp Φ f hf)).2

/-- **The definition is compatible with the `ℓ²(ℤ) ≅ L²(𝕋)` dictionary**: the Fourier transform of
`opMul Φ f` is the product of the symbol with `𝓕f`. -/
theorem ftLp_opMul (Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) (f : ℤ → ℂ)
    (hf : Memℓp f 2) : ftLp (opMul Φ f hf) (opMul_memℓp Φ f hf) = opMulLp Φ f hf := by
  have hsub : (⟨opMul Φ f hf, opMul_memℓp Φ f hf⟩ : ℓ²(ℤ, ℂ))
      = (fourierBasis (T := 1)).repr (opMulLp Φ f hf) := by
    refine Subtype.ext ?_
    funext n
    rfl
  simp only [ftLp]
  rw [hsub]
  exact LinearIsometryEquiv.symm_apply_apply _ _

/-- The coefficients of `opMul Φ f` are the `L²`-inner products of `e_n` with `Φ · 𝓕f`. -/
theorem opMul_apply (Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) (f : ℤ → ℂ)
    (hf : Memℓp f 2) (n : ℤ) :
    opMul Φ f hf n = inner ℂ (fourierBasis (T := 1) n) (opMulLp Φ f hf) := by
  rw [opMul, opMulLp]
  exact HilbertBasis.repr_apply_apply _ _ n

/-- **The frequency support of a multiplier is contained in the support of its symbol.** -/
theorem hasFreqSupport_opMul (Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) (f : ℤ → ℂ)
    (hf : Memℓp f 2) {E : Set Circle}
    (hΦ : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)), ξ ∉ E → (Φ : Circle → ℂ) ξ = 0) :
    HasFreqSupport (opMul Φ f hf) (opMul_memℓp Φ f hf) E := by
  have hcoe : (ftLp (opMul Φ f hf) (opMul_memℓp Φ f hf) : Circle → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] fun ξ => (Φ : Circle → ℂ) ξ
        * (ftLp f hf : Circle → ℂ) ξ := by
    rw [ftLp_opMul]
    exact Lp.coeFn_lpSMul Φ (ftLp f hf)
  simp only [HasFreqSupport]
  filter_upwards [hcoe, hΦ] with ξ hξ hΦξ
  intro hmem
  rw [hξ, hΦξ hmem, zero_mul]

/-- The frequency support of `opArc φ E f` is contained in the union of the translated supports
`β + supp φ`, `β ∈ E`. -/
theorem hasFreqSupport_opArc (φ : Circle → ℂ)
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) (E : Finset Circle) (f : ℤ → ℂ)
    (hf : Memℓp f 2) {D : Set Circle} (hD : ∀ ξ, ξ ∉ D → φ ξ = 0) :
    HasFreqSupport (opArc φ hφ E f hf) (opMul_memℓp (arcSymbolLp φ hφ E) f hf)
      {ξ | ∃ β ∈ E, ξ - β ∈ D} := by
  refine hasFreqSupport_opMul _ _ _ ?_
  have hsym : (arcSymbolLp φ hφ E : Circle → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] arcSymbol φ E := arcSymbolLp_coeFn φ hφ E
  filter_upwards [hsym] with ξ hξ hmem
  rw [hξ, arcSymbol_apply]
  by_contra hne
  obtain ⟨β, hβ, hβne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact hmem ⟨β, hβ, by
    by_contra hd
    exact hβne (hD (ξ - β) hd)⟩


/-! ## Translating the arc set, and the pointwise bound on the symbol -/

/-- The translate `E + α` of a finite set of circle points.  The symbol of Tao's modulated operator
`Op_{φ;α+Σ}` (`ortho-apply`(ii)) is `arcSymbol φ (arcShift Σ α)`. -/
def arcShift (E : Finset Circle) (α : Circle) : Finset Circle := E.image (fun β => β + α)

theorem mem_arcShift {E : Finset Circle} {α x : Circle} :
    x ∈ arcShift E α ↔ ∃ β ∈ E, β + α = x := by
  rw [arcShift, Finset.mem_image]

theorem arcShift_empty (α : Circle) : arcShift ∅ α = ∅ := by simp [arcShift]

/-- The symbol of a translated arc set is the sum of the translates of `φ` by the shifted points. -/
theorem arcSymbol_arcShift (φ : Circle → ℂ) (E : Finset Circle) (α : Circle) :
    arcSymbol φ (arcShift E α) = fun ξ => ∑ β ∈ E, φ (ξ - (β + α)) := by
  funext ξ
  rw [arcSymbol_apply, arcShift,
    Finset.sum_image (fun x _ y _ h => add_right_cancel h)]

/-- **The pointwise bound on the arc symbol.**  If `φ` vanishes off the ball of radius `ε` and is
bounded by `M`, and if the arc points of `E` are `δ`-separated with `2ε < δ`, then at most one of
the translates `φ(· - β)`, `β ∈ E`, is non-zero, so `‖Σ_{β ∈ E} φ(· - β)‖ ≤ M` pointwise. -/
theorem norm_arcSymbol_le {φ : Circle → ℂ} {E : Finset Circle} {ε δ M : ℝ}
    (hφbd : ∀ ξ, ‖φ ξ‖ ≤ M) (hφsupp : ∀ ξ, ε < ‖ξ‖ → φ ξ = 0)
    (hsep : ∀ β ∈ E, ∀ β' ∈ E, β ≠ β' → δ ≤ ‖β - β'‖) (hδε : 2 * ε < δ) (ξ : Circle) :
    ‖arcSymbol φ E ξ‖ ≤ M := by
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hφbd 0)
  have key : ∀ β ∈ E, ∀ β' ∈ E, φ (ξ - β) ≠ 0 → φ (ξ - β') ≠ 0 → β = β' := by
    intro β hβ β' hβ' h1 h2
    by_contra hne
    have hle1 : ‖ξ - β‖ ≤ ε := le_of_not_gt fun h => h1 (hφsupp _ h)
    have hle2 : ‖ξ - β'‖ ≤ ε := le_of_not_gt fun h => h2 (hφsupp _ h)
    have hsub : β - β' = (ξ - β') - (ξ - β) := by abel
    have : ‖β - β'‖ ≤ 2 * ε := by
      rw [hsub]
      linarith [norm_sub_le (ξ - β') (ξ - β)]
    linarith [hsep β hβ β' hβ' hne]
  by_cases hex : ∃ β ∈ E, φ (ξ - β) ≠ 0
  · obtain ⟨β₀, hβ₀, hne₀⟩ := hex
    have hsingle : ∀ β ∈ E, φ (ξ - β) = if β = β₀ then φ (ξ - β₀) else 0 := by
      intro β hβ
      by_cases h : β = β₀
      · simp [h]
      · rw [if_neg h]
        by_contra hφ
        exact h (key β hβ β₀ hβ₀ hφ hne₀)
    calc ‖arcSymbol φ E ξ‖ = ‖φ (ξ - β₀)‖ := by
          congr 1
          rw [arcSymbol_apply]
          refine Finset.sum_eq_single β₀ ?_ ?_
          · intro β hβ hne
            rw [hsingle β hβ, if_neg hne]
          · intro h; exact absurd hβ₀ h
      _ ≤ M := hφbd _
  · rw [arcSymbol_apply, Finset.sum_eq_zero (fun β hβ => by
      by_contra h
      exact hex ⟨β, hβ, h⟩), norm_zero]
    exact hM

end

end Work.BourgainPlan.IonescuWainger
