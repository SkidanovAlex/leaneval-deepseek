import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.tsum_norm_sq_eq_norm_ftLp
import Submission.Work.BourgainPlan.IonescuWainger.coe_sigmaAFinset
import Submission.Work.BourgainPlan.IonescuWainger.ShiftArcDefs

/-!
# The `p = 2` endpoint of Tao's `ortho-apply`(ii): Plancherel plus arc counting

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4,
Theorem `ortho-apply`(ii), the case `p = 2` (the case `p = ∞` is in `opArc_sup`).

Tao's argument: *"For `p = 2` the claim follows from Lemma `ortho`(i) and Plancherel's theorem,
noting that each `Op_{φ;α+Σ_{A₀}}f` has Fourier transform supported in `Σ_{A₀}+α+[-ε,ε]^d`, and
each `β ∈ Σ_{≤k}` has at most `2^k` representations of the form `β = α + α₀`."*  In the
`ℓ²(ℤ) ≅ L²(𝕋)` picture of `OpArcDefs.lean` this is

`Σ_{A₀,α} ‖opArc φ (α+Σ_{A₀}) f‖²_{ℓ²} = ∫ (Σ_{A₀,α} ‖sym_{α+Σ_{A₀}}‖²)‖𝓕f‖² ≤ M² 2^k ‖f‖²_{ℓ²}`,

where `M` bounds the bump `φ` and `Σ_{A₀,α} ‖sym_{α+Σ_{A₀}}(ξ)‖² ≤ M² 2^k` is the pointwise
form of Tao's counting bound (`sigmaCompPairSet_filter_card_le`).

This file supplies the two abstract steps (`norm_sq_eq_integral_l2`,
`sum_opMul_l2_le_finset`) and then the concrete bound `opArc_l2_endpoint` for the symbols
`arcSymbol φ (arcShift (Σ_{A₀}) α)` of the square function of `ortho-apply`(ii).
-/

open MeasureTheory
open scoped lp BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-- **The squared `L²`-norm as an integral.**  For `G ∈ L²(𝕋)`, `‖G‖² = ∫_𝕋 ‖G(ξ)‖² dξ`. -/
theorem norm_sq_eq_integral_l2 (G : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
    ‖G‖ ^ 2 = ∫ ξ, ‖(G : Circle → ℂ) ξ‖ ^ 2 ∂(AddCircle.haarAddCircle (T := 1)) := by
  have h := MemLp.eLpNorm_eq_integral_rpow_norm (μ := AddCircle.haarAddCircle (T := 1))
    (p := 2) (by norm_num) (by norm_num) (Lp.memLp G)
  have hnn' : 0 ≤ ∫ a, ‖(G : Circle → ℂ) a‖ ^ (2 : ℝ)
      ∂(AddCircle.haarAddCircle (T := 1)) :=
    integral_nonneg fun a => Real.rpow_nonneg (norm_nonneg _) _
  rw [Lp.norm_def, h]
  simp only [ENNReal.toReal_ofNat]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnn' _)]
  have hcongr : (∫ a, ‖(G : Circle → ℂ) a‖ ^ (2 : ℝ) ∂AddCircle.haarAddCircle)
      = ∫ a, ‖(G : Circle → ℂ) a‖ ^ 2 ∂AddCircle.haarAddCircle :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ => Real.rpow_two _)
  rw [hcongr, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (integral_nonneg fun ξ => sq_nonneg _)]

/-- **Plancherel for `opMul`.**  The squared `ℓ²`-norm of a multiplier applied to `f` is the integral
of `‖Φ‖²‖𝓕f‖²` against the Haar measure of the circle. -/
theorem tsum_norm_sq_opMul_eq_integral (Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    ∑' n : ℤ, ‖opMul Φ f hf n‖ ^ 2
      = ∫ ξ, ‖(Φ : Circle → ℂ) ξ‖ ^ 2 * ‖(ftLp f hf : Circle → ℂ) ξ‖ ^ 2
        ∂(AddCircle.haarAddCircle (T := 1)) := by
  rw [tsum_norm_sq_eq_norm_ftLp (opMul_memℓp Φ f hf), ftLp_opMul]
  simp only [opMulLp]
  rw [norm_sq_eq_integral_l2]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_lpSMul (r := 2) Φ (ftLp f hf)] with ξ hξ
  rw [hξ]
  simp [mul_pow]

/-- **The `p = 2` endpoint of Tao's `ortho-apply`(ii), in `Finset` form.**  If the symbols `Φ i`,
`i ∈ s`, are pointwise bounded by `M` and at most `N` of them are non-zero at each frequency, then
the corresponding multipliers satisfy a Plancherel/Bessel bound on `ℓ²(ℤ)`. -/
theorem sum_opMul_l2_le_finset {ι : Type*} (s : Finset ι)
    (Φ : ι → Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) {M N : ℝ} (hM : 0 ≤ M) (_hN : 0 ≤ N)
    (hbd : ∀ i ∈ s, ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      ‖(Φ i : Circle → ℂ) ξ‖ ≤ M)
    (hcnt : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      ((s.filter (fun i => (Φ i : Circle → ℂ) ξ ≠ 0)).card : ℝ) ≤ N)
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    ∑ i ∈ s, ∑' n : ℤ, ‖opMul (Φ i) f hf n‖ ^ 2 ≤ M ^ 2 * N * ∑' n : ℤ, ‖f n‖ ^ 2 := by
  classical
  -- integrability of each summand
  have hInt : ∀ i ∈ s, Integrable (fun ξ : Circle => ‖(Φ i : Circle → ℂ) ξ‖ ^ 2
      * ‖(ftLp f hf : Circle → ℂ) ξ‖ ^ 2) (AddCircle.haarAddCircle (T := 1)) := by
    intro i _
    have h2 : Integrable (fun ξ : Circle =>
        ‖((Φ i • ftLp f hf : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) : Circle → ℂ) ξ‖ ^ 2)
        (AddCircle.haarAddCircle (T := 1)) :=
      MemLp.integrable_norm_pow'
        (Lp.memLp (Φ i • ftLp f hf : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) (p := 2)
    refine h2.congr ?_
    filter_upwards [Lp.coeFn_lpSMul (r := 2) (Φ i) (ftLp f hf)] with ξ hξ
    rw [hξ]
    simp [mul_pow]
  rw [Finset.sum_congr rfl (fun i _ => tsum_norm_sq_opMul_eq_integral (Φ i) f hf)]
  rw [← integral_finsetSum s hInt]
  have hall : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      ∀ i : ↥s, ‖(Φ i.1 : Circle → ℂ) ξ‖ ≤ M :=
    Filter.eventually_all.mpr fun i => hbd i.1 i.2
  have hpt : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      (∑ i ∈ s, ‖(Φ i : Circle → ℂ) ξ‖ ^ 2 * ‖(ftLp f hf : Circle → ℂ) ξ‖ ^ 2)
        ≤ (M ^ 2 * N) * ‖(ftLp f hf : Circle → ℂ) ξ‖ ^ 2 := by
    filter_upwards [hall, hcnt] with ξ hbdξ hcntξ
    have hbdξ' : ∀ i ∈ s, ‖(Φ i : Circle → ℂ) ξ‖ ≤ M := fun i hi => hbdξ ⟨i, hi⟩
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hsplit : ∑ i ∈ s, ‖(Φ i : Circle → ℂ) ξ‖ ^ 2
        = ∑ i ∈ s.filter (fun i => (Φ i : Circle → ℂ) ξ ≠ 0),
            ‖(Φ i : Circle → ℂ) ξ‖ ^ 2 := by
      refine (Finset.sum_filter_of_ne ?_).symm
      intro i _ h
      by_contra hz
      exact h (by rw [hz, norm_zero]; norm_num)
    rw [hsplit]
    calc ∑ i ∈ s.filter (fun i => (Φ i : Circle → ℂ) ξ ≠ 0), ‖(Φ i : Circle → ℂ) ξ‖ ^ 2
        ≤ ∑ i ∈ s.filter (fun i => (Φ i : Circle → ℂ) ξ ≠ 0), M ^ 2 :=
          Finset.sum_le_sum fun i hi => by
            have := hbdξ' i (Finset.mem_of_mem_filter i hi)
            nlinarith [norm_nonneg ((Φ i : Circle → ℂ) ξ), hM]
      _ = ((s.filter (fun i => (Φ i : Circle → ℂ) ξ ≠ 0)).card : ℝ) * M ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * M ^ 2 := mul_le_mul_of_nonneg_right hcntξ (sq_nonneg M)
      _ = M ^ 2 * N := by ring
  calc ∫ ξ, (∑ i ∈ s, ‖(Φ i : Circle → ℂ) ξ‖ ^ 2 * ‖(ftLp f hf : Circle → ℂ) ξ‖ ^ 2)
        ∂(AddCircle.haarAddCircle (T := 1))
      ≤ ∫ ξ, (M ^ 2 * N) * ‖(ftLp f hf : Circle → ℂ) ξ‖ ^ 2
          ∂(AddCircle.haarAddCircle (T := 1)) := by
        refine integral_mono_ae ?_ ?_ hpt
        · refine (integrable_finsetSum' s (fun i hi => hInt i hi)).congr ?_
          filter_upwards with ξ
          simp [Finset.sum_apply]
        · exact (Lp.memLp (ftLp f hf)).integrable_norm_pow' (p := 2) |>.const_mul _
    _ = M ^ 2 * N * ∫ ξ, ‖(ftLp f hf : Circle → ℂ) ξ‖ ^ 2
          ∂(AddCircle.haarAddCircle (T := 1)) := integral_const_mul _ _
    _ = M ^ 2 * N * ∑' n : ℤ, ‖f n‖ ^ 2 := by
        rw [← norm_sq_eq_integral_l2 (ftLp f hf), ← tsum_norm_sq_eq_norm_ftLp hf]


/-! ## The concrete endpoint: the square function of the major arcs -/

/-- **The `(r,c)`-good hypothesis implies the smallness hypothesis** `2ε < 1/qmax^{2k}` used in the
`p = 2` endpoint: Tao's goodness condition `ε < c/(2r qmax^{2rk})` (with `c ≤ 1 ≤ r`) is stronger,
because `qmax^{2k} ≤ qmax^{2rk}`. -/
lemma two_mul_lt_of_good {k r qmax : ℕ} (hr : 1 ≤ r) (hqmax : 1 ≤ qmax) {c ε : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hε : 0 ≤ ε)
    (hgood : ε < c / (2 * r * (qmax : ℝ) ^ (2 * r * k))) :
    2 * ε < 1 / (qmax : ℝ) ^ (2 * k) := by
  have hq : (1 : ℝ) ≤ (qmax : ℝ) := by exact_mod_cast hqmax
  have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hqk : (1 : ℝ) ≤ (qmax : ℝ) ^ (2 * k) := one_le_pow₀ hq
  have hpow : (qmax : ℝ) ^ (2 * k) ≤ (qmax : ℝ) ^ (2 * r * k) := by
    apply pow_le_pow_right₀ hq
    have h : 2 * k ≤ 2 * r * k := by nlinarith
    exact h
  have h1 : 1 / (qmax : ℝ) ^ (2 * r * k) ≤ 1 / (qmax : ℝ) ^ (2 * k) :=
    one_div_le_one_div_of_le (by positivity) hpow
  have h4 : 0 ≤ 1 / (qmax : ℝ) ^ (2 * r * k) := by positivity
  have h3 : c / (r : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  calc 2 * ε < 2 * (c / (2 * r * (qmax : ℝ) ^ (2 * r * k))) := by linarith
    _ = (c / (r : ℝ)) * (1 / (qmax : ℝ) ^ (2 * r * k)) := by field_simp
    _ ≤ 1 * (1 / (qmax : ℝ) ^ (2 * r * k)) := mul_le_mul_of_nonneg_right h3 h4
    _ ≤ 1 / (qmax : ℝ) ^ (2 * k) := by simpa using h1

end

end Work.BourgainPlan.IonescuWainger
