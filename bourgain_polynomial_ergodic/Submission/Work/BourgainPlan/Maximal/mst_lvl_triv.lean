import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_lvl_defs
import Submission.Work.BourgainPlan.Maximal.mstProfBumpS_coeff
import Submission.Work.BourgainPlan.Maximal.mst_err1_opmul_coeff
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mst_minor_per_n
import Submission.Work.BourgainPlan.Maximal.mikhlin_conditions_scaled_bump
import Submission.Work.BourgainPlan.Maximal.mstModelFn_kernel_l1_of_coeff

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset Filter
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))
local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-! ## The trivial `ℓʳ` bound for the level model `ν^s_{2^k}`

The level-`s` piece of the major-arc model is a finite sum of translates of the single
profile-times-bump `star (Φ_{2^k}) · η_s`, weighted by the (bounded) Gauss factors:

`mstNuS P l d χ η k s = Σ_{β ∈ 𝒰(s+1)∖𝒰(s)} star (G β) · (star (Φ_{2^k}) η_s)(· - β)`,  `‖G β‖ ≤ 1`.

Hence its Fourier coefficient kernel is the sum of `#(𝒰(s+1)∖𝒰(s))` translates of the coefficient
kernel of `star (Φ_{2^k}) η_s`, whose total mass is bounded by `K` uniformly in `k` and `s`
(`mstProfBumpS_coeff`, MST §4.2 eq. (78)).  The discrete Young inequality
(`mst_err1_opmul_coeff`) then gives the `ℓʳ → ℓʳ` bound with constant `#(𝒰(s+1)∖𝒰(s)) · K` for every
`r ≥ 1`.  This is the trivial endpoint of MST Theorem 7. -/

/-- **The support of the MST bump is closed.**  A `C²` bump vanishing strictly outside `[-1/2,1/2]`
(`|x| > 1/2 → η x = 0`) also vanishes at the two boundary points `|x| = 1/2`: continuity at `±1/2`
and the one-sided limits (`𝓝[>]` at `1/2`, `𝓝[<]` at `-1/2`) give `η (±1/2) = 0`.  This is the
hypothesis shape (`1/2 ≤ |x|`) required by `mikhlin_conditions_scaled_bump`. -/
lemma mst_lvl_eta_zero_of_half_le_abs {η : ℝ → ℂ} (hηc : ContDiff ℝ 2 η)
    (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0 := by
  intro x hx
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact hη0 x hlt
  · have hx2 : x = 1 / 2 ∨ x = -(1 / 2) := (abs_eq (by norm_num)).mp heq.symm
    rcases hx2 with h | h
    · rw [h]
      have hev : η =ᶠ[𝓝[>] (1 / 2)] fun _ : ℝ => (0 : ℂ) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy' : (1 : ℝ) / 2 < y := hy
        exact hη0 y (by rw [abs_of_pos (by linarith : (0 : ℝ) < y)]; exact hy')
      have h1 : Filter.Tendsto η (𝓝[>] (1 / 2)) (𝓝 (η (1 / 2))) :=
        hηc.continuous.continuousAt.mono_left nhdsWithin_le_nhds
      have h2 : Filter.Tendsto η (𝓝[>] (1 / 2)) (𝓝 0) :=
        Filter.Tendsto.congr' hev.symm tendsto_const_nhds
      exact tendsto_nhds_unique h1 h2
    · rw [h]
      have hev : η =ᶠ[𝓝[<] (-(1 / 2))] fun _ : ℝ => (0 : ℂ) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy' : y < (-(1 / 2) : ℝ) := hy
        exact hη0 y (by rw [abs_of_neg (by linarith : y < 0)]; linarith)
      have h1 : Filter.Tendsto η (𝓝[<] (-(1 / 2))) (𝓝 (η (-(1 / 2)))) :=
        hηc.continuous.continuousAt.mono_left nhdsWithin_le_nhds
      have h2 : Filter.Tendsto η (𝓝[<] (-(1 / 2))) (𝓝 0) :=
        Filter.Tendsto.congr' hev.symm tendsto_const_nhds
      exact tendsto_nhds_unique h1 h2

/-- **The trivial `ℓʳ` bound for the level model `ν^s_{2^k}`**, in the form in which the main
theorem uses it: a summable coefficient kernel of total mass `K` (uniform in the scale and the
level) gives `‖F⁻¹(ν^s_{2^k} ĝ)‖_{ℓʳ} ≤ #(𝒰(s+1)∖𝒰(s)) · K · ‖g‖_{ℓʳ}` for every `r ≥ 1`. -/
lemma mst_lvl_triv_of_kernel {P : Polynomial ℤ} {l : ℕ} {χ : ℝ} {η : ℝ → ℂ} {K : ℝ}
    (hd : 1 ≤ P.natDegree) (hχ0 : 0 ≤ χ) (hχd : χ ≤ (P.natDegree : ℝ))
    (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hcd : ∀ s : ℕ, ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η s)))
    (hterm : ∀ (N s : ℕ), 1 ≤ N →
      Summable (fun m : ℤ => ‖∫ ξ : Circ,
          (star (mstProf P N ξ) * mstEta P.natDegree χ η s ξ) * star (fourier m ξ) ∂haarT‖) ∧
      (∑' m : ℤ, ‖∫ ξ : Circ,
          (star (mstProf P N ξ) * mstEta P.natDegree χ η s ξ) * star (fourier m ξ) ∂haarT‖) ≤ K)
    (hML : ∀ n s : ℕ, MeasureTheory.MemLp (mstNuS P l P.natDegree χ η n s) ⊤ haarT)
    (s k : ℕ) (g : ℤ →₀ ℂ) {r : ℝ} (hr : 1 ≤ r) :
    MeasureTheory.eLpNorm (opMulFinsuppLM (mstNuSCls P l P.natDegree χ η k s (hML k s)) g)
        (ENNReal.ofReal r) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (((mstLevel l (s + 1) \ mstLevel l s).card : ℝ) * K)
        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  classical
  -- the `ℓ¹` kernel bound for the model symbol, uniform in `E`
  obtain ⟨hksum, hkbnd⟩ :=
    mstModelFn_kernel_l1_of_coeff P P.natDegree χ η hd hχ0 hχd hη0 hcd hterm
      (2 ^ k) s (by exact Nat.one_le_two_pow) (mstLevel l (s + 1) \ mstLevel l s)
  -- the model symbol *is* `mstNuS`
  have hnuS : ∀ p : ℤ, (∫ ξ : Circ, mstModelFn (fun β => star (mstG P β))
        (fun ζ => star (mstProf P (2 ^ k) ζ)) (mstEta P.natDegree χ η s)
        (mstLevel l (s + 1) \ mstLevel l s) ξ * star (fourier p ξ) ∂haarT)
      = ∫ ξ : Circ, mstNuS P l P.natDegree χ η k s ξ * star (fourier p ξ) ∂haarT := by
    intro p
    simp only [mstNuS]
  have hksum' : Summable (fun m : ℤ => ‖∫ ξ : Circ,
      mstNuS P l P.natDegree χ η k s ξ * star (fourier m ξ) ∂haarT‖) :=
    hksum.congr (fun m => by rw [hnuS m])
  have hkbnd' : (∑' m : ℤ, ‖∫ ξ : Circ,
      mstNuS P l P.natDegree χ η k s ξ * star (fourier m ξ) ∂haarT‖)
      ≤ K * ((mstLevel l (s + 1) \ mstLevel l s).card : ℝ) := by
    have h1 : (∑' m : ℤ, ‖∫ ξ : Circ,
        mstNuS P l P.natDegree χ η k s ξ * star (fourier m ξ) ∂haarT‖)
        = ∑' m : ℤ, ‖∫ ξ : Circ, mstModelFn (fun β => star (mstG P β))
            (fun ζ => star (mstProf P (2 ^ k) ζ)) (mstEta P.natDegree χ η s)
            (mstLevel l (s + 1) \ mstLevel l s) ξ * star (fourier m ξ) ∂haarT‖ :=
      tsum_congr (fun m => by rw [hnuS m])
    rw [h1]
    exact hkbnd
  -- the coefficient kernel of the `L^∞`-class of `mstNuS`
  let c : ℤ → ℂ := fun m => ∫ ξ : Circ,
    (mstNuSCls P l P.natDegree χ η k s (hML k s) : Circ → ℂ) ξ * star (fourier m ξ) ∂haarT
  have hcbridge : ∀ m : ℤ, c m = ∫ ξ : Circ,
      mstNuS P l P.natDegree χ η k s ξ * star (fourier m ξ) ∂haarT := by
    intro m
    dsimp only [c]
    refine integral_congr_ae ?_
    filter_upwards [mstNuSCls_coeFn P l P.natDegree χ η k s (hML k s)] with ξ hξ
    rw [hξ]
  have hcsum : Summable fun m : ℤ => ‖c m‖ := by
    have h1 : (fun m : ℤ => ‖c m‖) = fun m : ℤ => ‖∫ ξ : Circ,
        mstNuS P l P.natDegree χ η k s ξ * star (fourier m ξ) ∂haarT‖ := by
      funext m; rw [hcbridge m]
    rw [h1]
    exact hksum'
  have hcK : (∑' m : ℤ, ‖c m‖) ≤ K * ((mstLevel l (s + 1) \ mstLevel l s).card : ℝ) := by
    have h1 : (∑' m : ℤ, ‖c m‖) = ∑' m : ℤ, ‖∫ ξ : Circ,
        mstNuS P l P.natDegree χ η k s ξ * star (fourier m ξ) ∂haarT‖ :=
      tsum_congr (fun m => by rw [hcbridge m])
    rw [h1]
    exact hkbnd'
  -- Young's inequality for the multiplier with the summable kernel `c`
  have hmain := mst_err1_opmul_coeff (p := r)
    (Φ := mstNuSCls P l P.natDegree χ η k s (hML k s)) (c := c) hr hcsum
    (fun m => rfl) hcK (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g)
  calc MeasureTheory.eLpNorm (opMulFinsuppLM (mstNuSCls P l P.natDegree χ η k s (hML k s)) g)
        (ENNReal.ofReal r) MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul
          (mstNuSCls P l P.natDegree χ η k s (hML k s)) (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g))
          (ENNReal.ofReal r) MeasureTheory.Measure.count := by
        rw [opMulFinsuppLM_apply]
    _ ≤ ENNReal.ofReal (K * ((mstLevel l (s + 1) \ mstLevel l s).card : ℝ))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := hmain
    _ = ENNReal.ofReal (((mstLevel l (s + 1) \ mstLevel l s).card : ℝ) * K)
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
        rw [show K * ((mstLevel l (s + 1) \ mstLevel l s).card : ℝ)
              = ((mstLevel l (s + 1) \ mstLevel l s).card : ℝ) * K from mul_comm _ _]

/-- The trivial `ℓʳ` bound for the level model `ν^s_{2^k}` (MST Theorem 7, trivial endpoint): a summable coefficient kernel gives `‖F⁻¹(ν^s_{2^k} ĝ)‖_{ℓʳ} ≤ #(𝒰(s+1) ∖ 𝒰(s)) · K · ‖g‖_{ℓʳ}` for every `r ≥ 1`, uniformly in the scale `k` and in the level `s`. -/
theorem mst_lvl_triv (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    (hML : ∀ n s : ℕ, MeasureTheory.MemLp (Work.BourgainPlan.Maximal.mstNuS P l P.natDegree χ η n s) ⊤
      (AddCircle.haarAddCircle (T := 1))) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : ℕ) (k : ℕ) (g : ℤ →₀ ℂ) {r : ℝ}, 1 ≤ r →
      MeasureTheory.eLpNorm (Work.BourgainPlan.Maximal.opMulFinsuppLM
          (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hML k s)) g)
          (ENNReal.ofReal r) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((((Work.BourgainPlan.Maximal.mstLevel l (s + 1) \ Work.BourgainPlan.Maximal.mstLevel l s).card : ℝ)) * K)
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  have hM0 : (0 : ℝ) ≤ M := hM.le
  have hχd : χ + 1 ≤ (P.natDegree : ℝ) := by
    have h2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    linarith
  -- the strict-to-closed support of the bump
  have hsupp : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0 :=
    mst_lvl_eta_zero_of_half_le_abs hηc hη0
  -- the Mikhlin data of the level bumps: `mikhlin_conditions_scaled_bump` at `c = 2^{s(d−χ)}`
  have hcd : ∀ s : ℕ,
      ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η s)) := by
    intro s
    have hexp : (0 : ℝ) ≤ (s : ℝ) * ((P.natDegree : ℝ) - χ) :=
      mul_nonneg (Nat.cast_nonneg s) (by linarith)
    have hc1 : (1 : ℝ) ≤ |(2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ))| := by
      rw [abs_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]
      exact Real.one_le_rpow (by norm_num) hexp
    have h := mikhlin_conditions_scaled_bump (η := η) (M := M)
      (c := (2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ))) hM0 hc1
      hηc hηbd hder1 hder2 hsupp
    have hEq : mstEta P.natDegree χ η s
        = fun ξ => η ((2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) * iwRep ξ) := by
      funext ξ; rw [mstEta_apply]
    rw [hEq]
    exact h.1
  -- the uniform per-term `ℓ¹` kernel bound (MST §4.2, eq. (78))
  obtain ⟨K, hKpos, hK⟩ :=
    mstProfBumpS_coeff P P.natDegree χ η M hM0 hχd hηbd hη0 (hcd 0)
  refine ⟨K, hKpos, fun s k g r hr => ?_⟩
  exact mst_lvl_triv_of_kernel (P := P) (l := l) (χ := χ) (η := η) (K := K)
    (by omega) hχ0.le (by linarith) hη0 hcd hK hML s k g hr

end

end Work.BourgainPlan.Maximal
