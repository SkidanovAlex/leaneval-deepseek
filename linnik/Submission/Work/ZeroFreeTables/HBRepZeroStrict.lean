/-
# ZeroFreeTables — HBRepZeroStrict

Target: `HBRepZeroStrict` — a *multiple* zero `ρ₁` (multiplicity `≥ 2`) of a non-principal
character `χ₁` which is **not** a real–real pair (`¬ (χ₁² = 1 ∧ Im ρ₁ = 0)`) and which realises
HB's §6 minimum over the strip `|Im| ≤ 10` satisfies `696/1000 < λ₁` for all large `q`.

Route (HB §6 "repeated zero", in general position): HB's §6 machinery does *not* need `χ₁` real
or `ρ₁` real — the pointwise positivity `1 + Re(χ(n)n^{-iγ}) ≥ 0` holds for every character, and
the *multiplicity* of `ρ₁` supplies the doubling that HB obtains in the real–real case from the
two factors `1 + χ₁(n)`.  Concretely, for a test function `f` of HB's Conditions 1–2:

* positivity (`Ksum_positivity` with the second character chosen principal):
  `0 ≤ K(β₁, χ₀) + K(β₁+iγ₁, χ₁)`, `β₁ = Re ρ₁`, `γ₁ = Im ρ₁`;
* the principal-character bound (HB Lemma 5.3, `Ksum_principal_le_complex`):
  `K(β₁,χ₀) ≤ L·F(−λ₁) + f(0)(ε/2)L`;
* the window bound (HB Lemma 5.2) at the point `s = ρ₁`, where the window
  `‖1 + i·Im s − u‖ ≤ δ` contains `ρ₁` with multiplicity `m = zeroMult χ₁ ρ₁ ≥ 2` and every
  other window zero is to the left of `ρ₁` by the §6 minimality:
  `K(ρ₁,χ₁) ≤ −L·m·F(0) + f(0)(c+ε)L`;

whence `F(−λ₁) − m F(0) + f(0)(c + 3ε/2) ≥ 0`, and with `m ≥ 2`:

  `F(−λ₁) − 2F(0) + f(0)(c + 3ε/2) ≥ 0`.

With HB Lemma 7.1's optimal test function (`testFn7_1`) at `θ = π/3` and scale `λ = 7/10` and
the convexity constant `c = 1/4 + 10⁻⁶` (no Burgess input needed), this contradicts `λ₁ ≤ 7/10`:
`F(−λ₁) ≤ F(−7/10) = 9 − (4/3)π√3 ≈ 1.7448`, while
`2F(0) − f(0)(c+3ε/2) ≈ 2.5010 − 1.7573·0.2515 ≈ 2.0617`.  Hence `λ₁ > 7/10 > 696/1000`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.TestFn_F_antitone
import Submission.Work.ZeroFreeTables.testFn7_1
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Work.ZeroFreeTables.HB6RepeatedGeneral
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.NumberTheory.Linnik.scratch_kprinc_c
import Submission.Commons.NumberTheory.Linnik.Ksum_positivity
import Submission.Commons.NumberTheory.Linnik.le_windowSum_of_mem
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen
import Submission.Work.LinnikAreas.l31free.LFunction_bound_half_of_convexity
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## 1. The `L52Hyp` input with the convexity constant `c = 1/4 + 10⁻⁶`

HB Lemma 3.1/Lemma 5.2 in window form, with the constant coming from the *convexity* bound
(HB Lemma 2.5 with `φ = 1/2`, `LFunction_bound_half_of_convexity`) — no Burgess input is
needed, so this is `sorry`-free with a light dependency closure.  The transport from
`lemma3_1_free_gen` to `L52Hyp` is the same as in `Work.LinnikAreas.DhCapped.l52HypExplicit`
(which uses `φ = 1/3` and the Burgess input instead). -/

theorem l52Hyp_general_fixed : ∃ c δ : ℝ, 0 < c ∧ c ≤ 1/4 + 1/100 ∧ 0 < δ ∧ δ < 1 ∧
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        Commons.NumberTheory.Linnik.L52Hyp χ c ε δ := by
  have hbound : ∀ k : ℕ, 3 ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ Cb : ℝ, 0 < Cb ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
        ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) →
          ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖
            ≤ Cb * (N:ℝ) ^ (((1:ℝ)/2) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') * (1 + |t|) :=
    fun k hk ε' hε' => Work.LinnikAreas.l31free.LFunction_bound_half_of_convexity hε' k hk
  obtain ⟨L₀, δ, hδpos, hδ1, hmain⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen (φ := (1 : ℝ)/2) (by norm_num)
      (ε := 1/1000000) (by norm_num) hbound
  refine ⟨1/4 + 1/1000000, δ, by norm_num, by norm_num, hδpos, hδ1, ⌈Real.exp L₀⌉₊ + 3, ?_⟩
  intro q hq _inst χ _instc hχ ε hε _hε1 s hsre1 hsre2 hsim
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hexp_le : Real.exp L₀ ≤ (q : ℝ) := by
    have h1 : Real.exp L₀ ≤ (⌈Real.exp L₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp L₀⌉₊ : ℝ) ≤ ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) := by
      push_cast; linarith
    have h3 : ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hL₀le : L₀ ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos L₀) hexp_le
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hcon : 3 ≤ χ.conductor := by
    have h := Work.LinnikAreas.l31free.three_le_of_char_ne_one χ.primitiveCharacter hχ'
    exact_mod_cast h
  have hconle : χ.conductor ≤ q := Nat.le_of_dvd hqpos χ.conductor_dvd_level
  have hNL : Real.log ((χ.conductor : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
    · exact_mod_cast hconle
  have h1 := hmain (N := χ.conductor) hcon χ.primitiveCharacter hχ'
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) (L := Real.log (q : ℝ))
    hL₀le hNL s hsre1 hsre2 hsim
  have hlogq : 0 ≤ Real.log (q : ℝ) := by
    refine Real.log_nonneg ?_
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast hq1
  refine le_trans h1 ?_
  have hc : (1 : ℝ)/2/2 + 1/1000000 ≤ (1/4 + 1/1000000) + ε/4 := by
    have h : (1 : ℝ)/2/2 = 1/4 := by norm_num
    rw [h]; linarith only [hε]
  exact mul_le_mul_of_nonneg_right hc hlogq

/-! ## 2. The multiplicity-weighted window-sum lower bound

HB's Lemma 5.2 retains the *divisor-weighted* term `div(ρ)·Re F((s−ρ)L)` of the window; the
single-term bound therefore carries the multiplicity of `ρ`.  This is
`Work.ZeroFreeTables.HBSecondAux.windowSum_ge_div_mul_kernel`, re-proved here (that module's
import closure currently contains an unfinished colleague file, so it cannot be imported); the
proof is the one of `Commons.NumberTheory.Linnik.le_windowSum_of_mem` with the factor
`div(ρ)` kept. -/

theorem div_mul_kernel_le_windowSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {f : ℝ → ℝ} {x₀ L : ℝ} {s ρ : ℂ} {δ : ℝ} (hL : 0 ≤ L)
    (hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
    (hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) ρ ≠ 0)
    (hwin : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ)
    (hzero : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ s.re) :
    (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|s.im| + 2))) ρ : ℤ) : ℝ) *
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      ≤ ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
          ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
          else 0) := by
  classical
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (|s.im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hDnn : ∀ u : ℂ, (0:ℤ) ≤ MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|s.im| + 2)) u := fun u =>
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg han) u
  let T : ℂ → ℝ := fun u =>
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
        else 0)
  have hzshift : ∀ u : ℂ, u.re ≤ s.re → 0 ≤ (((s - u) * L : ℂ)).re := by
    intro u hu
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have : 0 ≤ (s - u).re := by rw [Complex.sub_re]; linarith
    exact mul_nonneg this hL
  have hTnn : ∀ u : ℂ, 0 ≤ T u := by
    intro u
    simp only [T]
    by_cases hdu : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) u = 0
    · rw [hdu]; norm_num
    · by_cases hw : ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
      · rw [if_pos hw]
        refine mul_nonneg ?_ ?_
        · exact_mod_cast hDnn u
        · exact hF ((s - u) * L) (hzshift u (hzero u hdu hw))
      · rw [if_neg hw, mul_zero]
  have hTρ : (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2))) ρ : ℤ) : ℝ) *
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * L) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      = T ρ := by
    simp only [T]
    rw [if_pos hwin]
  have hDfin : (Function.support (fun u : ℂ => MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 (|s.im| + 2)) u)).Finite := by
    have hmer : MeromorphicOn (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0:ℂ) (|s.im| + 2)) :=
      fun z _ => ((DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z).meromorphicAt
    exact MeromorphicOn.divisor_support_finite_of_subset
      (f := DirichletCharacter.completedLFunction χ)
      (U := Metric.closedBall (0:ℂ) (|s.im| + 2))
      (V := Metric.closedBall (0:ℂ) (|s.im| + 2))
      hmer (isCompact_closedBall 0 (|s.im| + 2)) (subset_refl _)
  have hTfin : (Function.support T).Finite := by
    refine hDfin.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    apply hu
    simp only [T]
    rw [h0]
    norm_num
  rcases eq_or_lt_of_le (hTnn ρ) with h0 | h0
  · rw [hTρ, ← h0]
    exact finsum_nonneg hTnn
  · have hmem : ρ ∈ Function.support T := Function.mem_support.mpr (ne_of_gt h0)
    have heq := finsum_eq_sum_of_support_subset T (s := hTfin.toFinset)
      (fun x hx => hTfin.mem_toFinset.mpr hx)
    rw [heq, hTρ]
    exact Finset.single_le_sum (fun i _ => hTnn i) (hTfin.mem_toFinset.mpr hmem)


/-! ## 3. The arithmetic of HB Lemma 7.1's test function at `θ = π/3`, `λ = 7/10`

With `θ = π/3` (`tan θ = √3`) and `λ = 7/10`, HB's Lemma 7.1 test function has

`f(0) = (7/10)·4·(2π√3/3 − 3) ≈ 1.7573`,  `F(0) = 8(1 − π√3/9)² ≈ 1.2507`,
`F(−7/10) = 9 − 4π√3/3 ≈ 1.7448`,

and the §6 repeated-zero inequality `F(−λ₁) ≥ 2F(0) − f(0)(c + 3ε/2)` (below) together with the
antitonicity `F(−λ₁) ≤ F(−7/10)` for `λ₁ ≤ 7/10` is contradictory as soon as
`c + 3ε/2 ≤ 1/4 + 1/100 + 3/2000`, since
`2F(0) − f(0)·0.2615 ≈ 2.0419 > 1.7448 ≈ F(−7/10)`. -/

theorem tf71_arith_false (T : Work.ZeroFreeTables.TestFn) {lam₁ c ε : ℝ}
    (hf0 : T.f 0 = (7/10) * (1 + Real.tan (Real.pi/3)^2) *
        ((Real.pi/3) * Real.tan (Real.pi/3) + 3 * (Real.pi/3) * (Real.tan (Real.pi/3))⁻¹ - 3))
    (hF0 : T.F 0 = 2 * (1 + Real.tan (Real.pi/3)^2) * (1 - (Real.pi/3) * (Real.tan (Real.pi/3))⁻¹)^2)
    (hF7 : T.F (-(7/10)) = 2 * Real.tan (Real.pi/3)^2 + 3
        - 3 * (Real.pi/3) * Real.tan (Real.pi/3) - 3 * (Real.pi/3) * (Real.tan (Real.pi/3))⁻¹)
    (hlam : lam₁ ≤ 7/10) (hc : c ≤ 1/4 + 1/100) (hε : ε ≤ 1/1000)
    (hineq : 0 ≤ T.F (-lam₁) - 2 * T.F 0 + T.f 0 * (c + 3*ε/2)) : False := by
  have hmono : T.F (-lam₁) ≤ T.F (-(7/10)) := by
    refine TestFn_F_antitone T ?_
    linarith
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := by
    rw [← sq, Real.sq_sqrt (by norm_num)]
  have hs1 : (1.7320508 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt 3 < (1.7320509 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hps_lo : (5.441 : ℝ) < Real.pi * Real.sqrt 3 := by
    nlinarith [Real.pi_gt_d20, hs1]
  have hps_hi : Real.pi * Real.sqrt 3 < 5.442 := by
    nlinarith [Real.pi_lt_d20, hs2]
  have hp2_lo : (9.869 : ℝ) < Real.pi^2 := by nlinarith [Real.pi_gt_d20]
  have hp2_hi : Real.pi^2 < 9.870 := by nlinarith [Real.pi_lt_d20]
  have hinv : (Real.sqrt 3)⁻¹ = Real.sqrt 3 / 3 := by
    have hne : Real.sqrt 3 ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  have hf0pos : 0 < (7/10) * (1 + (Real.sqrt 3)^2) *
      ((Real.pi/3) * (Real.sqrt 3) + 3 * (Real.pi/3) * ((Real.sqrt 3) / 3) - 3) := by
    have hinner : 0 < (Real.pi/3) * (Real.sqrt 3) + 3 * (Real.pi/3) * ((Real.sqrt 3) / 3) - 3 := by
      nlinarith [hps_lo]
    have hsq3 : (0:ℝ) < 1 + (Real.sqrt 3)^2 := by nlinarith [hsq]
    positivity
  have hcoef : c + 3 * ε / 2 ≤ 1/4 + 1/100 + 3 * (1/1000) / 2 := by linarith
  have hkey : T.F (-(7/10)) < 2 * T.F 0 - T.f 0 * (c + 3 * ε / 2) := by
    rw [hF7, hF0, hf0, Real.tan_pi_div_three, hinv]
    have hmain : 2 * 3 + 3 - 3 * (Real.pi/3) * (Real.sqrt 3) - 3 * (Real.pi/3) * (Real.sqrt 3 / 3)
        < 2 * (2 * (1 + (Real.sqrt 3)^2) * (1 - (Real.pi/3) * (Real.sqrt 3 / 3))^2)
          - ((7/10) * (1 + (Real.sqrt 3)^2) *
              ((Real.pi/3) * (Real.sqrt 3) + 3 * (Real.pi/3) * (Real.sqrt 3 / 3) - 3))
            * (1/4 + 1/100 + 3 * (1/1000) / 2) := by
      nlinarith [hsq, hps_lo, hps_hi, hp2_lo, hp2_hi]
    have hstep := mul_le_mul_of_nonneg_left hcoef (le_of_lt hf0pos)
    nlinarith [hmain, hstep]
  linarith [hineq, hmono, hkey]


/-! ## 4. The target

`HBRepZeroStrict`: a multiple zero `ρ₁` of `χ₁` which is not a real–real pair has `λ₁ > 7/10`.

Proof.  Take HB Lemma 7.1's test function `T` at `θ = π/3`, `λ = 7/10` (`testFn7_1`), the
`L52Hyp` input `l52Hyp_general_fixed` with `c ≤ 1/4 + 1/100` and `ε = 1/1000`, and the §6
repeated-zero inequality `HB6RepeatedGeneral` at the doubled zero `ρ₁`.  Assume `λ₁ ≤ 696/1000`;
then `λ₁ ≤ 7/10`, so `F(−λ₁) ≤ F(−7/10)` (antitone) and the §6 inequality gives
`F(−λ₁) − 2F(0) + f(0)(c+3/2000) ≥ 0`, which is impossible by `tf71_arith_false`. -/
theorem HBRepZeroStrict :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ →
      (696 : ℝ)/1000 < Work.LinnikContract.lamOf q ρ₁ := by
  obtain ⟨c, δ, _hcpos, hcle, hδ0, hδ1, q₀L, hL⟩ := l52Hyp_general_fixed
  have hθ0 : (0:ℝ) < Real.pi/3 := by positivity
  have hθ1 : Real.pi/3 < Real.pi/2 := by linarith [Real.pi_pos]
  obtain ⟨T, _hTx₀, hTf₀, hTF₀, hTF7⟩ := testFn7_1 (Real.pi/3) (7/10) hθ0 hθ1 (by norm_num)
  obtain ⟨B, hBnn, hBnd⟩ := T.f_bound
  obtain ⟨q₀R, hR⟩ := HB6RepeatedGeneral (x₀ := T.x₀) (B := B) (c := c) (ε := 1/1000) (δ := δ)
    T.x₀_pos hBnn (by norm_num) hδ0 hδ1 T.f_cont T.f_supp T.f_diff hBnd T.f0_pos T.f_nonneg
    (fun z hz => by rw [← T.Fc_spec z]; exact T.Fc_re_nonneg z hz)
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp ((696:ℝ)/1000 / δ))
  refine ⟨max (max q₀R q₀L) (max N 2187), ?_⟩
  intro q hq _inst χ₁ ρ₁ hm _hnr hmult
  have hqR : q₀R ≤ q := by omega
  have hqL : q₀L ≤ q := by omega
  have hqN : N ≤ q := by omega
  have hq3 : 2187 ≤ q := by omega
  haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hlogq : (0:ℝ) < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hmem : IsZ χ₁ ρ₁ := isMin1_isZ hm.1
  have hχ1 : χ₁ ≠ 1 := isZ_ne_one hmem
  have him1 : |ρ₁.im| ≤ 1 := hmem.2.2
  by_contra hcon
  push_neg at hcon
  have hlam7 : lamOf q ρ₁ ≤ 7/10 := by linarith
  have hstrip : ρ₁.re < 1 := by
    haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
    have hχ' : χ₁.primitiveCharacter ≠ 1 := by
      intro h
      apply hχ1
      rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, h]
      exact DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level
    have hz : DirichletCharacter.completedLFunction χ₁.primitiveCharacter ρ₁ = 0 := by
      have h := apply_eq_zero_of_analyticOrderNatAt_ne_zero hmem.2.1
      simpa [Work.LinnikContract.zeroMult] using h
    exact (Commons.NumberTheory.Linnik.completedL_zero_strip χ₁.primitiveCharacter hχ'
      (DirichletCharacter.primitiveCharacter_isPrimitive χ₁) hz).2
  have hre1 : ρ₁.re ≤ 1 := le_of_lt hstrip
  have hlam0 : 0 ≤ lamOf q ρ₁ := by
    rw [lamOf]
    exact mul_nonneg (by linarith) (le_of_lt hlogq)
  have hsqrt : (7/10 : ℝ) ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
    have hlog7 : (7:ℝ) < Real.log (2187:ℝ) := by
      have h3 : (1:ℝ) < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 3)]
        exact Real.exp_one_lt_three
      have hcast : (2187:ℝ) = (3:ℝ)^7 := by norm_num
      rw [hcast, Real.log_pow]
      push_cast
      nlinarith [h3]
    have h2187 : Real.log (2187:ℝ) ≤ Real.log (q:ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hq3)
    have h2 : Real.log 7 < Real.log (Real.log (q:ℝ)) := by
      apply Real.log_lt_log
      · norm_num
      · linarith
    have h3 : (49:ℝ)/100 < Real.log 7 := by
      have hexp : Real.exp (49/100) < 7 := by
        have h4 : Real.exp (49/100) < Real.exp 1 := (Real.exp_lt_exp).mpr (by norm_num)
        linarith [Real.exp_one_lt_three]
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 7)]
      exact hexp
    have h6 : (7/10:ℝ)^2 ≤ Real.log (Real.log (q:ℝ)) := by nlinarith [h2, h3]
    exact Real.le_sqrt_of_sq_le h6
  have hpt : |ρ₁.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    have habs : |ρ₁.re - 1| = 1 - ρ₁.re := by
      rw [abs_of_nonpos (by linarith : ρ₁.re - 1 ≤ 0)]; ring
    rw [habs, le_div_iff₀ hlogq]
    have h2 : (1 - ρ₁.re) * Real.log (q:ℝ) = lamOf q ρ₁ := by rw [lamOf]
    rw [h2]
    linarith only [hlam7, hsqrt]
  have hw : |1 - ρ₁.re| ≤ δ := by
    have habs : |1 - ρ₁.re| = 1 - ρ₁.re := abs_of_nonneg (by linarith)
    have hexp_lt : Real.exp ((696:ℝ)/1000 / δ) < (q:ℝ) :=
      lt_of_lt_of_le hN (by exact_mod_cast hqN)
    have hlog : (696:ℝ)/1000 / δ < Real.log (q:ℝ) := by
      have h := Real.log_lt_log (Real.exp_pos _) hexp_lt
      rwa [Real.log_exp] at h
    have h3 : (696:ℝ)/1000 < δ * Real.log (q:ℝ) := by
      rw [div_lt_iff₀ hδ0] at hlog; linarith
    rw [habs]
    have h2 : (1 - ρ₁.re) * Real.log (q:ℝ) = lamOf q ρ₁ := by rw [lamOf]
    have h4 : (1 - ρ₁.re) * Real.log (q:ℝ) ≤ (696:ℝ)/1000 := by rw [h2]; linarith
    have h5 : (1 - ρ₁.re) * Real.log (q:ℝ) < δ * Real.log (q:ℝ) := by linarith
    exact le_of_lt ((mul_lt_mul_iff_of_pos_right hlogq).mp h5)
  have hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u ≠ 0 → |u.im| ≤ 10 → u.re ≤ ρ₁.re := by
    intro u hzu himu
    have h1 := hm.2 χ₁ u hχ1 hzu himu
    rw [lamOf, lamOf] at h1
    have h2 := (mul_le_mul_iff_of_pos_right hlogq).mp h1
    linarith
  have H : Commons.NumberTheory.Linnik.L52Hyp χ₁ c (1/1000) δ :=
    hL q hqL χ₁ hχ1 (1/1000) (by norm_num) (by norm_num)
  have h6 := hR (q := q) hqR χ₁ hχ1 hmult him1 hpt hw hmin H
  have hA : (∫ t in (0:ℝ)..T.x₀, Real.exp ((Real.log (q:ℝ) * (1 - ρ₁.re)) * t) * T.f t)
      = T.F (-(lamOf q ρ₁)) := by
    rw [TestFn_F_eq_integral T (-(lamOf q ρ₁))]
    apply intervalIntegral.integral_congr
    intro t _
    show Real.exp ((Real.log (q:ℝ) * (1 - ρ₁.re)) * t) * T.f t
      = Real.exp (-(-(lamOf q ρ₁) * t)) * T.f t
    have harg : -(-(lamOf q ρ₁) * t) = (Real.log (q:ℝ) * (1 - ρ₁.re)) * t := by
      rw [lamOf]; ring
    rw [harg]
  have hB : (∫ t in (0:ℝ)..T.x₀, T.f t) = T.F 0 := by
    rw [TestFn_F_eq_integral T 0]; simp
  have h6' : 0 ≤ T.F (-(lamOf q ρ₁)) - 2 * T.F 0 + T.f 0 * (c + 3 * (1/1000) / 2) := by
    rw [hA, hB] at h6
    linarith only [h6]
  exact tf71_arith_false T hTf₀ hTF₀ hTF7 hlam7 hcle (le_refl _) h6'


end Work.ZeroFreeTables
