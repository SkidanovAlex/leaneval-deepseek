import Mathlib
import Submission.Work.Residues.ThetaExpansion
import Submission.Work.Kernels.TildeFacts.theta_quartic

/-!
# The limits of the cusp atoms

This file proves the six cusp limits of the atoms occurring in the CKMRV interpolation
formulas, all along `Im → ∞` (`UpperHalfPlane.atImInfty`).  With `E = Work.Residues.Ept`
(`E(z) = e^{πiz}`, so `‖E(z)‖ = e^{-π Im z} → 0`) and the second order cusp expansions of
`Work.Residues.ThetaExpansion` (`U = 1 + 8E + O(‖E‖²)`, `V = 16E + O(‖E‖³)`,
`Δ = E² + O(‖E‖⁴)`, `𝓛_S = -16E + O(‖E‖³)`) and `Work.Residues.E4FunSecondOrder`,
`Work.Residues.E6FunSecondOrder` (`E₄ = 1 + 240q + O(‖q‖²)`, `E₆ = 1 - 504q + O(‖q‖²)`,
`q = E²`), we obtain

* `E² E₁₄/Δ → 1`, `E² E₁₀/Δ → 1`, `E² j → 1` (the cusp forms `E₁₀/Δ`, `E₁₄/Δ` and `j`
  have a simple pole at the cusp with residue `1` in the `E` parameter),
* `𝓛_S/E → -16`, `V/E → 16`,
* `(U² - W²)/E → 32`, using Jacobi's quartic identity `U = W + V`
  (`Work.Kernels.TildeFacts.theta_quartic`), which turns `U² - W²` into `V(U + W)`.

The elementary convergence facts are packaged in `tendsto_of_norm_sub_le`: a bound
`‖f - l‖ ≤ C ‖E‖^k` with `k ≥ 1` on a cusp neighbourhood forces `f → l`.
-/

namespace Work.Asymptotics

open Filter Topology UpperHalfPlane

noncomputable section

/-! ## Elementary convergence facts -/

/-- `‖E(z)‖ = e^{-π Im z} → 0` at the cusp `i∞`. -/
lemma tendsto_norm_Ept : Tendsto (fun z : ℍ => ‖Work.Residues.Ept z‖) atImInfty (𝓝 0) := by
  have him : Tendsto (fun z : ℍ => z.im) atImInfty atTop := Filter.tendsto_comap
  have h1 : Tendsto (fun z : ℍ => Real.pi * z.im) atImInfty atTop :=
    Filter.Tendsto.const_mul_atTop Real.pi_pos him
  have h2 : Tendsto (fun z : ℍ => -(Real.pi * z.im)) atImInfty atBot := by
    have h := Filter.tendsto_neg_atTop_atBot.comp h1
    simpa only [Function.comp_def] using h
  have h3 : Tendsto (fun z : ℍ => Real.exp (-(Real.pi * z.im))) atImInfty (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp h2
    simpa only [Function.comp_def] using h
  simpa only [Work.Residues.norm_Ept] using h3

/-- A statement holding for all `τ` with `A ≤ Im τ` holds eventually at the cusp. -/
lemma eventually_of_forall_im_ge {p : ℍ → Prop} {A : ℝ} (h : ∀ τ : ℍ, A ≤ τ.im → p τ) :
    ∀ᶠ τ in atImInfty, p τ :=
  Filter.eventually_iff.mpr
    ((UpperHalfPlane.atImInfty_mem {τ | p τ}).mpr ⟨A, fun τ hτ => h τ hτ⟩)

/-- **Squeezing against the cusp parameter.**  If `‖f z - l‖ ≤ C ‖E(z)‖ ^ k` eventually,
with `k ≥ 1`, then `f → l` at the cusp. -/
lemma tendsto_of_norm_sub_le {f : ℍ → ℂ} {l : ℂ} {C : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (h : ∀ᶠ z in atImInfty, ‖f z - l‖ ≤ C * ‖Work.Residues.Ept z‖ ^ k) :
    Tendsto f atImInfty (𝓝 l) := by
  have hk0 : k ≠ 0 := by omega
  have hC : Tendsto (fun z : ℍ => C * ‖Work.Residues.Ept z‖ ^ k) atImInfty (𝓝 0) := by
    have h1 : Tendsto (fun z : ℍ => ‖Work.Residues.Ept z‖ ^ k) atImInfty (𝓝 ((0 : ℝ) ^ k)) :=
      tendsto_norm_Ept.pow k
    rw [zero_pow hk0] at h1
    simpa using h1.const_mul C
  have h2 : Tendsto (fun z : ℍ => ‖f z - l‖) atImInfty (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun z => norm_nonneg _) h hC
  have h3 : Tendsto (fun z : ℍ => f z - l) atImInfty (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr h2
  have h4 : Tendsto (fun z : ℍ => (f z - l) + l) atImInfty (𝓝 (0 + l)) :=
    h3.add tendsto_const_nhds
  rw [zero_add] at h4
  exact Filter.Tendsto.congr' (Eventually.of_forall fun z => by simp) h4

/-- If `f = 1 + c q + O(‖q‖²)` at the cusp, where `q = E²`, then `f → 1`. -/
lemma tendsto_one_of_qExpansion {f : ℍ → ℂ} {c : ℂ} {C : ℝ} (hC : 0 < C)
    (h : ∀ τ : ℍ, 1 ≤ τ.im →
      ‖f τ - 1 - c * Work.Kernels.qParamFun τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 2) :
    Tendsto f atImInfty (𝓝 1) := by
  refine tendsto_of_norm_sub_le (k := 2) (C := C + ‖c‖) (by norm_num) ?_
  refine eventually_of_forall_im_ge (A := 1) fun τ hτ => ?_
  have hb := h τ hτ
  have hqE : Work.Kernels.qParamFun τ = Work.Residues.Ept τ ^ 2 := by
    rw [Work.Residues.Ept, Work.Kernels.qParamFun, sq, ← Complex.exp_add]
    congr 1; ring
  have hqn : ‖Work.Kernels.qParamFun τ‖ = ‖Work.Residues.Ept τ‖ ^ 2 := by rw [hqE, norm_pow]
  have he1 : ‖Work.Residues.Ept τ‖ ≤ 1 := le_of_lt (Work.Residues.norm_Ept_lt_one τ)
  have he4 : ‖Work.Residues.Ept τ‖ ^ 4 ≤ ‖Work.Residues.Ept τ‖ ^ 2 :=
    pow_le_pow_of_le_one (norm_nonneg _) he1 (by norm_num)
  rw [hqn] at hb
  rw [show (‖Work.Residues.Ept τ‖ ^ 2) ^ 2 = ‖Work.Residues.Ept τ‖ ^ 4 by ring] at hb
  have hcn : ‖c * Work.Kernels.qParamFun τ‖ = ‖c‖ * ‖Work.Residues.Ept τ‖ ^ 2 := by
    rw [norm_mul, hqn]
  calc ‖f τ - 1‖
      = ‖(f τ - 1 - c * Work.Kernels.qParamFun τ) + c * Work.Kernels.qParamFun τ‖ := by
        congr 1; ring
    _ ≤ ‖f τ - 1 - c * Work.Kernels.qParamFun τ‖ + ‖c * Work.Kernels.qParamFun τ‖ :=
        norm_add_le _ _
    _ ≤ C * ‖Work.Residues.Ept τ‖ ^ 4 + ‖c‖ * ‖Work.Residues.Ept τ‖ ^ 2 := by
        rw [hcn]; exact add_le_add hb le_rfl
    _ ≤ (C + ‖c‖) * ‖Work.Residues.Ept τ‖ ^ 2 := by
        have h1 : C * ‖Work.Residues.Ept τ‖ ^ 4 ≤ C * ‖Work.Residues.Ept τ‖ ^ 2 :=
          mul_le_mul_of_nonneg_left he4 (le_of_lt hC)
        nlinarith [h1, hC.le, norm_nonneg c, pow_nonneg (norm_nonneg (Work.Residues.Ept τ)) 2]

/-! ## The individual limits -/

/-- `E₄ → 1` at the cusp (from its `q`-expansion). -/
lemma tendsto_E4Fun_atImInfty : Tendsto Work.Kernels.E4Fun atImInfty (𝓝 1) := by
  obtain ⟨C, hC, h⟩ := Work.Residues.E4FunSecondOrder
  exact tendsto_one_of_qExpansion (c := 240) hC h

/-- `E₆ → 1` at the cusp (from its `q`-expansion). -/
lemma tendsto_E6Fun_atImInfty : Tendsto Work.Kernels.E6Fun atImInfty (𝓝 1) := by
  obtain ⟨C, hC, h⟩ := Work.Residues.E6FunSecondOrder
  refine tendsto_one_of_qExpansion (c := -504) hC fun τ hτ => ?_
  have hb := h τ hτ
  rw [show Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ
      = Work.Kernels.E6Fun τ - 1 - (-504) * Work.Kernels.qParamFun τ by ring] at hb
  exact hb

/-- `Δ/E² → 1` at the cusp. -/
lemma tendsto_Delta_div_EptSq {C : ℝ}
    (h : ∀ τ : ℍ, 1 ≤ τ.im → ‖Work.Kernels.DeltaFun τ - Work.Residues.Ept τ ^ 2‖ ≤
      C * ‖Work.Residues.Ept τ‖ ^ 4) :
    Tendsto (fun τ : ℍ => Work.Kernels.DeltaFun τ / Work.Residues.Ept τ ^ 2) atImInfty (𝓝 1) := by
  refine tendsto_of_norm_sub_le (k := 2) (C := C) (by norm_num) ?_
  refine eventually_of_forall_im_ge (A := 1) fun τ hτ => ?_
  have hb := h τ hτ
  have hne : Work.Residues.Ept τ ≠ 0 := Work.Residues.Ept_ne_zero τ
  have hsplit : Work.Kernels.DeltaFun τ / Work.Residues.Ept τ ^ 2 - 1
      = (Work.Kernels.DeltaFun τ - Work.Residues.Ept τ ^ 2) / Work.Residues.Ept τ ^ 2 := by
    field_simp
  rw [hsplit, norm_div, norm_pow]
  calc ‖Work.Kernels.DeltaFun τ - Work.Residues.Ept τ ^ 2‖ / ‖Work.Residues.Ept τ‖ ^ 2
      ≤ (C * ‖Work.Residues.Ept τ‖ ^ 4) / ‖Work.Residues.Ept τ‖ ^ 2 :=
        div_le_div_of_nonneg_right hb (by positivity)
    _ = C * ‖Work.Residues.Ept τ‖ ^ 2 := by
        by_cases h0 : ‖Work.Residues.Ept τ‖ = 0
        · rw [h0]; simp
        · field_simp [h0]

/-- `V/E → 16` at the cusp. -/
lemma tendsto_VFun_div_Ept {C : ℝ}
    (h : ∀ τ : ℍ, 1 ≤ τ.im → ‖Work.Kernels.VFun τ - 16 * Work.Residues.Ept τ‖ ≤
      C * ‖Work.Residues.Ept τ‖ ^ 3) :
    Tendsto (fun τ : ℍ => Work.Kernels.VFun τ / Work.Residues.Ept τ) atImInfty (𝓝 16) := by
  refine tendsto_of_norm_sub_le (k := 2) (C := C) (by norm_num) ?_
  refine eventually_of_forall_im_ge (A := 1) fun τ hτ => ?_
  have hb := h τ hτ
  have hne : Work.Residues.Ept τ ≠ 0 := Work.Residues.Ept_ne_zero τ
  have hsplit : Work.Kernels.VFun τ / Work.Residues.Ept τ - 16
      = (Work.Kernels.VFun τ - 16 * Work.Residues.Ept τ) / Work.Residues.Ept τ := by
    field_simp
  rw [hsplit, norm_div]
  calc ‖Work.Kernels.VFun τ - 16 * Work.Residues.Ept τ‖ / ‖Work.Residues.Ept τ‖
      ≤ (C * ‖Work.Residues.Ept τ‖ ^ 3) / ‖Work.Residues.Ept τ‖ :=
        div_le_div_of_nonneg_right hb (norm_nonneg _)
    _ = C * ‖Work.Residues.Ept τ‖ ^ 2 := by
        by_cases h0 : ‖Work.Residues.Ept τ‖ = 0
        · rw [h0]; simp
        · field_simp [h0]

/-- `𝓛_S/E → -16` at the cusp. -/
lemma tendsto_LS_div_Ept (ℓ : Work.Kernels.LogLambdaData) {C : ℝ}
    (h : ∀ τ : ℍ, 1 ≤ τ.im → ‖ℓ.L_S τ + 16 * Work.Residues.Ept τ‖ ≤
      C * ‖Work.Residues.Ept τ‖ ^ 3) :
    Tendsto (fun τ : ℍ => ℓ.L_S τ / Work.Residues.Ept τ) atImInfty (𝓝 (-16)) := by
  refine tendsto_of_norm_sub_le (k := 2) (C := C) (by norm_num) ?_
  refine eventually_of_forall_im_ge (A := 1) fun τ hτ => ?_
  have hb := h τ hτ
  have hne : Work.Residues.Ept τ ≠ 0 := Work.Residues.Ept_ne_zero τ
  have hsplit : ℓ.L_S τ / Work.Residues.Ept τ - (-16)
      = (ℓ.L_S τ + 16 * Work.Residues.Ept τ) / Work.Residues.Ept τ := by
    field_simp
    ring
  rw [hsplit, norm_div]
  calc ‖ℓ.L_S τ + 16 * Work.Residues.Ept τ‖ / ‖Work.Residues.Ept τ‖
      ≤ (C * ‖Work.Residues.Ept τ‖ ^ 3) / ‖Work.Residues.Ept τ‖ :=
        div_le_div_of_nonneg_right hb (norm_nonneg _)
    _ = C * ‖Work.Residues.Ept τ‖ ^ 2 := by
        by_cases h0 : ‖Work.Residues.Ept τ‖ = 0
        · rw [h0]; simp
        · field_simp [h0]

/-- `U + W → 2` at the cusp, using Jacobi's quartic identity `U = W + V`. -/
lemma tendsto_UFun_add_WFun {CU CV : ℝ} (hCV : 0 ≤ CV)
    (hU : ∀ τ : ℍ, 1 ≤ τ.im → ‖Work.Kernels.UFun τ - 1 - 8 * Work.Residues.Ept τ‖ ≤
      CU * ‖Work.Residues.Ept τ‖ ^ 2)
    (hV : ∀ τ : ℍ, 1 ≤ τ.im → ‖Work.Kernels.VFun τ - 16 * Work.Residues.Ept τ‖ ≤
      CV * ‖Work.Residues.Ept τ‖ ^ 3) :
    Tendsto (fun τ : ℍ => Work.Kernels.UFun τ + Work.Kernels.WFun τ) atImInfty (𝓝 2) := by
  refine tendsto_of_norm_sub_le (k := 2) (C := 2 * CU + CV + 1) (by norm_num) ?_
  refine eventually_of_forall_im_ge (A := 1) fun τ hτ => ?_
  have hu := hU τ hτ
  have hv := hV τ hτ
  have hq := Work.Kernels.TildeFacts.theta_quartic τ
  have he1 : ‖Work.Residues.Ept τ‖ ≤ 1 := le_of_lt (Work.Residues.norm_Ept_lt_one τ)
  have h3 : ‖Work.Residues.Ept τ‖ ^ 3 ≤ ‖Work.Residues.Ept τ‖ ^ 2 :=
    pow_le_pow_of_le_one (norm_nonneg _) he1 (by norm_num)
  have hsplit : Work.Kernels.UFun τ + Work.Kernels.WFun τ - 2
      = 2 * (Work.Kernels.UFun τ - 1 - 8 * Work.Residues.Ept τ)
        - (Work.Kernels.VFun τ - 16 * Work.Residues.Ept τ) := by
    rw [hq]; ring
  rw [hsplit]
  calc ‖2 * (Work.Kernels.UFun τ - 1 - 8 * Work.Residues.Ept τ)
        - (Work.Kernels.VFun τ - 16 * Work.Residues.Ept τ)‖
      ≤ ‖2 * (Work.Kernels.UFun τ - 1 - 8 * Work.Residues.Ept τ)‖
        + ‖Work.Kernels.VFun τ - 16 * Work.Residues.Ept τ‖ := norm_sub_le _ _
    _ = 2 * ‖Work.Kernels.UFun τ - 1 - 8 * Work.Residues.Ept τ‖
        + ‖Work.Kernels.VFun τ - 16 * Work.Residues.Ept τ‖ := by
        rw [norm_mul, Complex.norm_ofNat]
    _ ≤ 2 * (CU * ‖Work.Residues.Ept τ‖ ^ 2) + CV * ‖Work.Residues.Ept τ‖ ^ 3 := by
        have h1 : 2 * ‖Work.Kernels.UFun τ - 1 - 8 * Work.Residues.Ept τ‖
            ≤ 2 * (CU * ‖Work.Residues.Ept τ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hu (by norm_num)
        linarith [h1, hv]
    _ ≤ (2 * CU + CV + 1) * ‖Work.Residues.Ept τ‖ ^ 2 := by
        have h1 : CV * ‖Work.Residues.Ept τ‖ ^ 3 ≤ CV * ‖Work.Residues.Ept τ‖ ^ 2 :=
          mul_le_mul_of_nonneg_left h3 hCV
        have h2 : (0 : ℝ) ≤ ‖Work.Residues.Ept τ‖ ^ 2 := pow_nonneg (norm_nonneg _) 2
        nlinarith [h1, h2]

/-! ## The six limits -/

theorem cuspAtomLimits (ℓ : Work.Kernels.LogLambdaData) :
    Filter.Tendsto (fun z : UpperHalfPlane => (Work.Residues.Ept z) ^ 2 * Work.Kernels.E14Fun z /
        Work.Kernels.DeltaFun z) UpperHalfPlane.atImInfty (nhds 1) ∧
    Filter.Tendsto (fun z : UpperHalfPlane => (Work.Residues.Ept z) ^ 2 * Work.Kernels.E10Fun z /
        Work.Kernels.DeltaFun z) UpperHalfPlane.atImInfty (nhds 1) ∧
    Filter.Tendsto (fun z : UpperHalfPlane => ℓ.L_S z / Work.Residues.Ept z)
        UpperHalfPlane.atImInfty (nhds (-16)) ∧
    Filter.Tendsto (fun z : UpperHalfPlane => Work.Kernels.VFun z / Work.Residues.Ept z)
        UpperHalfPlane.atImInfty (nhds 16) ∧
    Filter.Tendsto (fun z : UpperHalfPlane => (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2) /
        Work.Residues.Ept z) UpperHalfPlane.atImInfty (nhds 32) ∧
    Filter.Tendsto (fun z : UpperHalfPlane => (Work.Residues.Ept z) ^ 2 * Work.Kernels.jInvariantFun z)
        UpperHalfPlane.atImInfty (nhds 1) := by
  obtain ⟨hUexp, hVexp, hDexp, hLSexp⟩ := Work.Residues.ThetaExpansion
  obtain ⟨CU, hCU, hU⟩ := hUexp
  obtain ⟨CV, hCV, hV⟩ := hVexp
  obtain ⟨CD, _, hD⟩ := hDexp
  obtain ⟨CL, _, hLS⟩ := hLSexp ℓ
  -- the limits of the elementary blocks
  have hE4 : Tendsto Work.Kernels.E4Fun atImInfty (𝓝 1) := tendsto_E4Fun_atImInfty
  have hE6 : Tendsto Work.Kernels.E6Fun atImInfty (𝓝 1) := tendsto_E6Fun_atImInfty
  have hDeltaDiv : Tendsto (fun τ : ℍ => Work.Kernels.DeltaFun τ / Work.Residues.Ept τ ^ 2)
      atImInfty (𝓝 1) := tendsto_Delta_div_EptSq (C := CD) hD
  have hEptSqDivDelta : Tendsto (fun τ : ℍ => Work.Residues.Ept τ ^ 2 / Work.Kernels.DeltaFun τ)
      atImInfty (𝓝 1) := by
    have h := hDeltaDiv.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
    simpa only [inv_one, inv_div] using h
  have hVdiv : Tendsto (fun τ : ℍ => Work.Kernels.VFun τ / Work.Residues.Ept τ)
      atImInfty (𝓝 16) := tendsto_VFun_div_Ept (C := CV) hV
  have hLSdiv : Tendsto (fun τ : ℍ => ℓ.L_S τ / Work.Residues.Ept τ)
      atImInfty (𝓝 (-16)) := tendsto_LS_div_Ept ℓ (C := CL) hLS
  have hUW : Tendsto (fun τ : ℍ => Work.Kernels.UFun τ + Work.Kernels.WFun τ)
      atImInfty (𝓝 2) := tendsto_UFun_add_WFun hCV.le hU hV
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `E² E₁₄/Δ → 1`
    have h1 : Tendsto (fun z : ℍ => (Work.Residues.Ept z ^ 2 / Work.Kernels.DeltaFun z)
        * (Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z)) atImInfty (𝓝 1) := by
      have h := hEptSqDivDelta.mul ((hE4.pow 2).mul hE6)
      simpa using h
    refine Filter.Tendsto.congr' (Eventually.of_forall fun z => ?_) h1
    show (Work.Residues.Ept z ^ 2 / Work.Kernels.DeltaFun z)
        * (Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z)
      = Work.Residues.Ept z ^ 2
          * (Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z) / Work.Kernels.DeltaFun z
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  · -- `E² E₁₀/Δ → 1`
    have h1 : Tendsto (fun z : ℍ => (Work.Residues.Ept z ^ 2 / Work.Kernels.DeltaFun z)
        * (Work.Kernels.E4Fun z * Work.Kernels.E6Fun z)) atImInfty (𝓝 1) := by
      have h := hEptSqDivDelta.mul (hE4.mul hE6)
      simpa using h
    refine Filter.Tendsto.congr' (Eventually.of_forall fun z => ?_) h1
    show (Work.Residues.Ept z ^ 2 / Work.Kernels.DeltaFun z)
        * (Work.Kernels.E4Fun z * Work.Kernels.E6Fun z)
      = Work.Residues.Ept z ^ 2
          * (Work.Kernels.E4Fun z * Work.Kernels.E6Fun z) / Work.Kernels.DeltaFun z
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  · exact hLSdiv
  · exact hVdiv
  · -- `(U² - W²)/E → 32`
    have h1 : Tendsto (fun z : ℍ => (Work.Kernels.VFun z / Work.Residues.Ept z)
        * (Work.Kernels.UFun z + Work.Kernels.WFun z)) atImInfty (𝓝 32) := by
      have h := hVdiv.mul hUW
      simpa only [show (16 : ℂ) * 2 = 32 by norm_num] using h
    refine Filter.Tendsto.congr' (Eventually.of_forall fun z => ?_) h1
    have hq := Work.Kernels.TildeFacts.theta_quartic z
    show (Work.Kernels.VFun z / Work.Residues.Ept z)
        * (Work.Kernels.UFun z + Work.Kernels.WFun z)
      = (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2) / Work.Residues.Ept z
    rw [div_eq_mul_inv, div_eq_mul_inv, hq]
    ring
  · -- `E² j → 1`
    have h1 : Tendsto (fun z : ℍ => (Work.Residues.Ept z ^ 2 / Work.Kernels.DeltaFun z)
        * Work.Kernels.E4Fun z ^ 3) atImInfty (𝓝 1) := by
      have h := hEptSqDivDelta.mul (hE4.pow 3)
      simpa using h
    refine Filter.Tendsto.congr' (Eventually.of_forall fun z => ?_) h1
    show (Work.Residues.Ept z ^ 2 / Work.Kernels.DeltaFun z) * Work.Kernels.E4Fun z ^ 3
      = Work.Residues.Ept z ^ 2 * (Work.Kernels.E4Fun z ^ 3 / Work.Kernels.DeltaFun z)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring

end

end Work.Asymptotics
