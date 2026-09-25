import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSquareLp
import Submission.Work.BourgainPlan.Maximal.mzSquareFunctionLpDomain
import Submission.Work.BourgainPlan.Maximal.convolutionLpLinear

open MeasureTheory
open scoped ENNReal BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.BourgainPlan.Maximal

/-- **MST's `(eq:52)` in its vector-valued form, for finite scale sets.**  The scalar
`annulusSquareLp` bounds `∫⁻ (Σ'_n ‖(K_{j+n}*f)(x)‖²)^{p/2}`; the vector-valued version needed by the
applications bounds `∫⁻ (Σ_t Σ_{n∈F} ‖(K_{j+n}*f_t)(x)‖²)^{p/2}` by the `L^p(ℓ²)` norm of the
family `(f_t)`, with a constant uniform in the number `κ` of components, the finite scale set
`F ⊆ ℤ` and the base scale `j`.

Route: apply the `Lp`-domain Marcinkiewicz–Zygmund theorem
`Work.BourgainPlan.Maximal.mzSquareFunctionLpDomain` with `ι := ↥F` to the `ℂ`-linear operators
`T_i : Lp ℂ (ofReal p) →ₗ[ℂ] Lp ℂ (ofReal p)` that realise convolution with the integrable kernel
`annulusK b (j+i)` (`Work.BourgainPlan.Maximal.convolutionLpLinear` +
`Work.BourgainPlan.Maximal.integrable_annulusK`); its representative is a.e.
`annulusConv b (j+i)`.  The uniform-in-signs hypothesis is the `L^p` bound for the multiplier with
symbol `Σ_{i∈F} ε_i b (j+i)`, i.e.
`Work.BourgainPlan.Maximal.annulusSymbolSum_convolution_le` (Mikhlin from `annulusSymbolSum_mikhlin`
via `mikhlinConvolutionLp`), together with the identification `annulusConv_finsetSum_eq` (the signed
sum of the convolutions *is* the convolution with the signed symbol), and the a.e. identification of
the `Lp` representative of `Σ_i ε_i T_i g` with the pointwise convolution.  Choose the MZ constant
`A` so that `A^p` is the Mikhlin constant (uniform in `j`, `F` and the signs).  The passage from
finite `F` to the full `Σ'_n` is the same monotone-convergence argument as in
`annulusSquareLp_of_finset` and is *not* part of this statement. -/
theorem annulusSquareLpVec (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {κ : Type*} [Fintype κ] (j : ℤ) (F : Finset ℤ) (f : κ → ℝ → ℂ),
      (∀ t : κ, MeasureTheory.MemLp (f t) (ENNReal.ofReal p)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) →
      ∫⁻ x, (∑ t : κ, ∑ n ∈ F,
          ‖annulusConv b (j + n) (f t) x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
        ≤ ENNReal.ofReal (C ^ p)
          * ∫⁻ x, (∑ t : κ, ‖f t x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
  obtain ⟨Cd, hCd, hMz⟩ := mzSquareFunctionLpDomain (p := p) (le_of_lt hp)
  obtain ⟨Cm, hCm, hMik⟩ := annulusSymbolSum_convolution_le b hb hsmooth hp
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  -- choose the exponent `A` with `A ^ p = Cm`, the Mikhlin constant of the signed symbol sums
  have hAp : (Cm ^ (1 / p)) ^ p = Cm := by
    rw [← Real.rpow_mul hCm.le, one_div, inv_mul_cancel₀ (ne_of_gt hp0), Real.rpow_one]
  have hCp : ((Cd * Cm) ^ (1 / p)) ^ p = Cd * Cm := by
    rw [← Real.rpow_mul (mul_nonneg hCd.le hCm.le), one_div, inv_mul_cancel₀ (ne_of_gt hp0),
      Real.rpow_one]
  refine ⟨(Cd * Cm) ^ (1 / p), Real.rpow_pos_of_pos (mul_pos hCd hCm) _, ?_⟩
  intro κ _ j F f hf
  classical
  set A : ℝ := Cm ^ (1 / p) with hAdef
  have hAp' : A ^ p = Cm := by rw [hAdef]; exact hAp
  have hA0 : 0 ≤ A := by rw [hAdef]; exact Real.rpow_nonneg hCm.le _
  -- the `ℂ`-linear operators realising convolution with `K_{j+i}` for `i ∈ F`
  have hTex : ∀ i : ↥F,
      ∃ T : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)
          →ₗ[ℂ] Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ),
        ∀ g : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ),
          ((T g : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) : ℝ → ℂ)
            =ᵐ[(volume : Measure ℝ)]
              fun x : ℝ => ∫ y : ℝ, annulusK b (j + (i : ℤ)) (x - y) * (g : ℝ → ℂ) y := by
    intro i
    exact convolutionLpLinear (K := annulusK b (j + (i : ℤ))) (p := p)
      (integrable_annulusK b hb hsmooth (j + (i : ℤ))) (le_of_lt hp)
  choose T hTint using hTex
  have hTcoe : ∀ (i : ↥F) (g : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)),
      ((T i g : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[(volume : Measure ℝ)] annulusConv b (j + (i : ℤ)) (g : ℝ → ℂ) := by
    intro i g
    refine (hTint i g).trans ?_
    exact Filter.EventuallyEq.of_eq (show
      (fun x : ℝ => ∫ y : ℝ, annulusK b (j + (i : ℤ)) (x - y) * (g : ℝ → ℂ) y)
        = annulusConv b (j + (i : ℤ)) (g : ℝ → ℂ) from rfl)
  -- the uniform-in-signs `L^p` bound, from the Mikhlin bound on the signed symbol sums
  have hHyp : ∀ (ε : ↥F → Bool) (g : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)),
      ∫⁻ y, ‖(((∑ i : ↥F, (if ε i then (1 : ℂ) else -1) • T i g :
            Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) : ℝ → ℂ) y)‖ₑ ^ p
        ≤ ENNReal.ofReal (A ^ p)
            * ∫⁻ x, ‖(((g : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) : ℝ → ℂ) x)‖ₑ ^ p := by
    intro ε g
    set coeff : ℤ → ℂ := fun n => if h : n ∈ F then (if ε ⟨n, h⟩ then (1 : ℂ) else -1) else 1
      with hcoeff
    have hcoeff_le : ∀ n : ℤ, ‖coeff n‖ ≤ 1 := by
      intro n
      simp only [hcoeff]
      split_ifs <;> simp
    have hg : MemLp ((g : ℝ → ℂ)) (ENNReal.ofReal p) (volume : Measure ℝ) := Lp.memLp g
    -- the pointwise identification of the signed sum of convolutions with the signed symbol
    have hident : ∀ y : ℝ,
        (∑ i : ↥F, (if ε i then (1 : ℂ) else -1)
            * annulusConv b (j + (i : ℤ)) (g : ℝ → ℂ) y)
          = ∫ z : ℝ, FourierTransformInv.fourierInv (annulusSymbolSum b j F coeff) (y - z)
              * (g : ℝ → ℂ) z := by
      intro y
      have hstep : (∑ i : ↥F, (if ε i then (1 : ℂ) else -1)
            * annulusConv b (j + (i : ℤ)) (g : ℝ → ℂ) y)
          = ∑ n ∈ F, coeff n * annulusConv b (j + n) (g : ℝ → ℂ) y := by
        rw [Finset.univ_eq_attach,
          ← Finset.sum_attach F (fun n : ℤ => coeff n * annulusConv b (j + n) (g : ℝ → ℂ) y)]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp [hcoeff]
      rw [hstep]
      exact annulusConv_finsetSum_eq b hb hsmooth (le_of_lt hp) j F coeff (g : ℝ → ℂ) hg y
    -- the `Lp` representative of the signed combination is a.e. the pointwise convolution
    have hsum_ae : (fun y => ∑ i : ↥F, (if ε i then (1 : ℂ) else -1)
          * (((T i g : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) : ℝ → ℂ) y))
        =ᵐ[(volume : Measure ℝ)]
          (fun y => ∑ i : ↥F, (if ε i then (1 : ℂ) else -1)
            * annulusConv b (j + (i : ℤ)) (g : ℝ → ℂ) y) := by
      filter_upwards [Filter.eventually_all.2 (fun i : ↥F => hTcoe i g)] with y hy
      exact Finset.sum_congr rfl (fun i _ => by rw [hy i])
    have hpoint : ((∑ i : ↥F, (if ε i then (1 : ℂ) else -1) • T i g :
          Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[(volume : Measure ℝ)]
          fun y => ∫ z : ℝ, FourierTransformInv.fourierInv (annulusSymbolSum b j F coeff) (y - z)
            * (g : ℝ → ℂ) z :=
      (mzLp_coeFn_finset_smul_sum (α := ℝ) (μ := (volume : Measure ℝ)) (β := ↥F)
        (Finset.univ : Finset ↥F) (fun i => (if ε i then (1 : ℂ) else -1))
        (fun i => T i g)).trans
        (hsum_ae.trans (Filter.Eventually.of_forall hident))
    calc ∫⁻ y, ‖(((∑ i : ↥F, (if ε i then (1 : ℂ) else -1) • T i g :
            Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) : ℝ → ℂ) y)‖ₑ ^ p
        = ∫⁻ y, ‖(∫ z : ℝ, FourierTransformInv.fourierInv (annulusSymbolSum b j F coeff) (y - z)
              * (g : ℝ → ℂ) z)‖ₑ ^ p := by
          refine lintegral_congr_ae ?_
          filter_upwards [hpoint] with y hy
          rw [hy]
      _ ≤ ENNReal.ofReal Cm * ∫⁻ x, ‖(((g : Lp ℂ (ENNReal.ofReal p)
              (volume : Measure ℝ)) : ℝ → ℂ) x)‖ₑ ^ p :=
          hMik j F coeff hcoeff_le (g : ℝ → ℂ) hg
      _ = ENNReal.ofReal (A ^ p) * ∫⁻ x, ‖(((g : Lp ℂ (ENNReal.ofReal p)
              (volume : Measure ℝ)) : ℝ → ℂ) x)‖ₑ ^ p := by rw [hAp']
  -- the `Lp` lifts of the pointwise family `f`
  set fl : κ → Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) :=
    fun t => (hf t).toLp (f t) with hfl
  have hfl_coe : ∀ t : κ,
      ((fl t : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[(volume : Measure ℝ)] f t := by
    intro t
    rw [hfl]
    exact MemLp.coeFn_toLp (hf t)
  -- Marcinkiewicz–Zygmund
  have hmain := hMz (ι := ↥F) (κ := κ) T A hA0 hHyp fl
  -- the two a.e. rewritings relating the MZ output to the statement
  have hterm : ∀ (i : ↥F) (t : κ),
      (fun y => ‖(((T i (fl t) : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) : ℝ → ℂ) y)‖ₑ
          ^ (2 : ℝ))
        =ᵐ[(volume : Measure ℝ)]
        (fun y => ‖annulusConv b (j + (i : ℤ)) (f t) y‖ₑ ^ (2 : ℝ)) := by
    intro i t
    have h1 : ((T i (fl t) : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[(volume : Measure ℝ)] annulusConv b (j + (i : ℤ)) (fl t) := hTcoe i (fl t)
    have h2 : annulusConv b (j + (i : ℤ)) (fl t) = annulusConv b (j + (i : ℤ)) (f t) :=
      lpConv_congr (hfl_coe t)
    filter_upwards [h1] with y hy
    rw [hy, h2]
  have hL : ∫⁻ x, (∑ t : κ, ∑ n ∈ F,
        ‖annulusConv b (j + n) (f t) x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
      = ∫⁻ y, (∑ i : ↥F, ∑ t : κ,
          ‖(((T i (fl t) : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) : ℝ → ℂ) y)‖ₑ
            ^ (2 : ℝ)) ^ (p / 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [Filter.eventually_all.2 (fun i : ↥F =>
      Filter.eventually_all.2 (fun t : κ => hterm i t))] with x hx
    have hsum : (∑ t : κ, ∑ n ∈ F, ‖annulusConv b (j + n) (f t) x‖ₑ ^ (2 : ℝ))
        = ∑ i : ↥F, ∑ t : κ,
            ‖(((T i (fl t) : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) : ℝ → ℂ) x)‖ₑ
              ^ (2 : ℝ) := by
      rw [show (∑ t : κ, ∑ n ∈ F, ‖annulusConv b (j + n) (f t) x‖ₑ ^ (2 : ℝ))
            = ∑ t : κ, ∑ i : ↥F, ‖annulusConv b (j + (i : ℤ)) (f t) x‖ₑ ^ (2 : ℝ) from
          Finset.sum_congr rfl (fun t _ => by
            rw [Finset.univ_eq_attach,
              ← Finset.sum_attach F
                (fun n : ℤ => ‖annulusConv b (j + n) (f t) x‖ₑ ^ (2 : ℝ))])]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun t _ => ?_))
      rw [← hx i t]
    rw [hsum]
  have hR : ∫⁻ x, (∑ t : κ,
        ‖(((fl t : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) : ℝ → ℂ) x)‖ₑ ^ (2 : ℝ))
          ^ (p / 2)
      = ∫⁻ x, (∑ t : κ, ‖f t x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
    refine lintegral_congr_ae ?_
    have hbase : ∀ t : κ,
        (fun x => ‖(((fl t : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) : ℝ → ℂ) x)‖ₑ)
          =ᵐ[(volume : Measure ℝ)] fun x => ‖f t x‖ₑ := by
      intro t
      filter_upwards [hfl_coe t] with x hx
      rw [hx]
    filter_upwards [Filter.eventually_all.2 hbase] with x hx
    rw [Finset.sum_congr rfl (fun t _ => by rw [hx t])]
  calc ∫⁻ x, (∑ t : κ, ∑ n ∈ F,
        ‖annulusConv b (j + n) (f t) x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
      = ∫⁻ y, (∑ i : ↥F, ∑ t : κ,
          ‖(((T i (fl t) : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) : ℝ → ℂ) y)‖ₑ
            ^ (2 : ℝ)) ^ (p / 2) := hL
    _ ≤ ENNReal.ofReal (Cd * A ^ p)
          * ∫⁻ x, (∑ t : κ,
              ‖(((fl t : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) : ℝ → ℂ) x)‖ₑ
                ^ (2 : ℝ)) ^ (p / 2) := hmain
    _ = ENNReal.ofReal (Cd * A ^ p) * ∫⁻ x, (∑ t : κ, ‖f t x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
          rw [hR]
    _ = ENNReal.ofReal (((Cd * Cm) ^ (1 / p)) ^ p)
          * ∫⁻ x, (∑ t : κ, ‖f t x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by rw [hAp', hCp]

end Work.BourgainPlan.Maximal
