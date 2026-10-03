import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.weighted_kernels_orthogonal
import Submission.Work.BourgainPlan.IonescuWainger.l1_le_weight_on_support
import Submission.Work.BourgainPlan.IonescuWainger.finset_sup_le_of_kernel_l1

namespace Work.BourgainPlan.IonescuWainger

/-- **The `p = ∞` endpoint of Tao's `ortho-apply`(ii) for a family of torsion-arc multipliers**
(arXiv:2008.05066, §4, the `p = ∞` paragraph): the `ℓ²`-valued square function of the family
`Op_{φ;α_i+Σ_{⊆A}}` is bounded at every point by `C₁C₂‖f‖_∞`, where `C₁` is the restricted
`ℓ²`-norm of the inverse polynomial weight (over the annihilator `Q_Aℤ`) and `C₂` bounds the
weighted `ℓ²`-norms of the kernels.  This is the `ℓ^∞(ℓ²)` endpoint needed by the vector-valued
interpolation of `ortho-apply`(ii); the proof combines `weighted_kernels_orthogonal` (orthogonality
of the weighted kernels), `l1_le_weight_on_support` (the weighted `ℓ¹` bound), the torsion kernel
computation `kernel_arcSymbol_torsion` and the duality step `finset_sup_le_of_kernel_l1`. -/
theorem opArc_sup_torsion_family {A : Finset ℕ} {ι : Type*} [Fintype ι]
    (αs : ι → Circle) (φ : Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {K : ℤ → ℂ}
    (hK : ∀ m : ℤ, ∫ ξ, φ ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1)) = K m)
    {ε C₁ C₂ : ℝ} (hε : 0 < ε) (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hφsupp : ∀ ξ : Circle, ε < ‖ξ‖ → φ ξ = 0)
    (hdisj : ∀ i j : ι, i ≠ j →
      Disjoint (closure {ξ : Circle | ∃ β ∈ sigmaSubAFinset A,
          ξ - (β + αs i) ∈ Metric.closedBall (0 : Circle) ε})
               (closure {ξ : Circle | ∃ β ∈ sigmaSubAFinset A,
          ξ - (β + αs j) ∈ Metric.closedBall (0 : Circle) ε}))
    (hC₁ : ∑' n : ℤ, ‖(if (QA A : ℤ) ∣ n then ((1 : ℂ) + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2)⁻¹
        else 0)‖ ^ 2 ≤ C₁ ^ 2)
    (hWmem : Memℓp (fun n : ℤ => (if (QA A : ℤ) ∣ n then ((1 : ℂ) + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2)⁻¹
        else 0)) 2)
    (hC₂ : ∀ i, ∑' n : ℤ, ‖(1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2)
        * (star (fourier n (αs i)) * (if (QA A : ℤ) ∣ n then (QA A : ℂ) else 0) * K n)‖ ^ 2
        ≤ C₂ ^ 2)
    (hKv : ∀ i, Memℓp (fun n : ℤ => (1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2)
        * (star (fourier n (αs i)) * (if (QA A : ℤ) ∣ n then (QA A : ℂ) else 0) * K n)) 2)
    (hKi : ∀ i, Summable fun n : ℤ =>
        ‖star (fourier n (αs i)) * (if (QA A : ℤ) ∣ n then (QA A : ℂ) else 0) * K n‖)
    (f : ℤ → ℂ) (hf : Memℓp f 2) {C' : ℝ} (hC' : ∀ m : ℤ, ‖f m‖ ≤ C') (n : ℤ) :
    (∑ i, ‖opArc φ hφ (arcShift (sigmaSubAFinset A) (αs i)) f hf n‖ ^ 2) ^ ((1 : ℝ) / 2)
      ≤ (C₁ * C₂) * C' := by
  classical
  -- The polynomial weight `w n = 1 + ε²n²` and its `ℓ²`-inverse `W`, together with the (unweighted)
  -- torsion kernels `Ki` of the shifted torsion arcs.
  let v : ℤ → ℂ := fun n => 1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2
  let W : ℤ → ℂ := fun n =>
    if (QA A : ℤ) ∣ n then (1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2)⁻¹ else 0
  let Ki : ι → ℤ → ℂ := fun i n =>
    star (fourier n (αs i)) * (if (QA A : ℤ) ∣ n then (QA A : ℂ) else 0) * K n
  -- The weight `w` never vanishes (`w n = 1 + (εn)²` is a strictly positive real).
  have hw_ne : ∀ n : ℤ, (1 : ℂ) + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2 ≠ 0 := by
    intro n
    have hcast : (1 : ℂ) + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2
        = ((1 + ε ^ 2 * (n : ℝ) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  -- The unweighted kernels vanish off the multiples of `Q_A`, and there `W` inverts `w`.
  have hKS : ∀ (i : ι) (n : ℤ), n ∉ {m : ℤ | (QA A : ℤ) ∣ m} → Ki i n = 0 := by
    intro i n hn
    have hn' : ¬ (QA A : ℤ) ∣ n := hn
    show star (fourier n (αs i)) * (if (QA A : ℤ) ∣ n then (QA A : ℂ) else 0) * K n = 0
    rw [if_neg hn']; ring
  have hvW : ∀ n : ℤ, n ∈ {m : ℤ | (QA A : ℤ) ∣ m} → W n * v n = 1 := by
    intro n hn
    have hn' : (QA A : ℤ) ∣ n := hn
    show (if (QA A : ℤ) ∣ n then (1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2)⁻¹ else 0)
        * (1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2) = 1
    rw [if_pos hn']
    exact inv_mul_cancel₀ (hw_ne n)
  -- Pairwise orthogonality of the weighted kernels (`weighted_kernels_orthogonal`).
  have horth : ∀ i j : ι, i ≠ j → ∑' m : ℤ, (v m * Ki i m) * star (v m * Ki j m) = 0 := by
    intro i j hij
    exact weighted_kernels_orthogonal (A := A) αs φ hφ hK (le_of_lt hε) hφsupp hdisj hKv i j hij
  -- The weighted `ℓ¹` bound on every combination of the kernels.
  have hL1 : ∀ c : ι → ℂ, ∑' m : ℤ, ‖∑ i, c i * Ki i m‖
      ≤ (C₁ * C₂) * (∑ i, ‖c i‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    intro c
    exact l1_le_weight_on_support (K := Ki) (v := v) (W := W) (S := {m : ℤ | (QA A : ℤ) ∣ m})
      hKS hvW hKv horth hWmem hC₁ hC₂ hC₁0 hC₂0 c
  -- The kernels `Ki` are the Fourier coefficients of the shifted torsion-arc symbols.
  have hker : ∀ (i : ι) (m : ℤ),
      ∫ ξ, (arcSymbolLp φ hφ (arcShift (sigmaSubAFinset A) (αs i)) : Circle → ℂ) ξ
          * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1)) = Ki i m := by
    intro i m
    refine (MeasureTheory.integral_congr_ae ?_).trans
      (kernel_arcSymbol_torsion (A := A) (αs i) φ hφ hK m)
    filter_upwards [arcSymbolLp_coeFn φ hφ (arcShift (sigmaSubAFinset A) (αs i))] with ξ hξ
    rw [hξ]
  -- Duality: the `ℓ²`-valued square function is bounded by the `ℓ¹` bound times `‖f‖_∞`.
  have hmain := finset_sup_le_of_kernel_l1
    (Φ := fun i => arcSymbolLp φ hφ (arcShift (sigmaSubAFinset A) (αs i)))
    hKi hker (mul_nonneg hC₁0 hC₂0) hL1 f hf hC' n
  simpa only [opArc] using hmain

end Work.BourgainPlan.IonescuWainger
