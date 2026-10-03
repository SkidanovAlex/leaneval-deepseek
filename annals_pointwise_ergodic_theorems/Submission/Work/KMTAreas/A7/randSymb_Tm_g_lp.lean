/-
# `Work.KMTAreas.A7.randSymb_Tm_g_lp`

The `g`-side linear single-scale estimate for the randomised cut-off in the *exact-height*
(`Tm`) convention: for every `C₀ ≥ 1` there are `A ≥ 0`, `ρ₀ > 0` and, for every `ρ ∈ (0,ρ₀]`, a
`C : NNReal → NNReal` with

  `‖Tm ρ l₂ (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε' K) g‖_{ℓ^{p₂}}
     ≤ (C Λ) · ofReal ((1+L)^A 2^{AρL}) · ‖g‖_{ℓ^{p₂}}`,   `L = lmaxR l₁ l₂ k₁ k₂`.

This is the paper's §8 (lin-2)-type bound `‖T^{l₂}_{φ̃_*}‖_{ℓ^q→ℓ^q} ≲ ⟨max(l,s₁,s₂)⟩^{O(1)}`
(Krause–Mirek–Tao, §`small-sec`) for the randomised cutoff
`φ̃_* = ∑_k ε_k (φ̃_{N_k,t} - φ̃_{N_{k-1},t})`, with the contract's loss weight.

## The route

Write `Φ := randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε' K : ℝ → ℂ`.

1. **The continuous multiplier bound** (`tmglp_randSymbG_mult`): for every `q > 1` there is
   `C > 0` with `IsLqMultiplierBound (ofReal q) Φ (C * (1 + k₂))`.  This is the paper's own
   scale split on `k₂`, and it is the *reason* the loss weight suffices:
   * `k₂ = 0`: the Mikhlin route (`randSymbG_mikhlin` gives the constant
     `C·(1+2^{d·0})² = 4C`, an absolute constant, and `isLqMultiplierBound_of_mikhlin` converts
     it into `IsLqMultiplierBound`);
   * `k₂ ≥ 1`: the shifted Calderón–Zygmund route
     (`varphitildeNt_mult_bound_k2pos_hi`, the `g`-side Appendix B estimate), whose constant is
     `C(1 + d k₂)`, i.e. *linear* in `k₂`.  The Mikhlin constant `(1+2^{d k₂})²` is exponential
     in `k₂` and is **not** absorbable by the weight `(1+L)^A 2^{AρL}` with `A` fixed before `ρ`
     (take `ρ → 0`), which is exactly why the case split is needed.
   The telescoped coefficient bound `‖randSymbGCoef‖ ≤ 2` turns the randomised symbol into
   `2 · ∑_{m ≤ K} c m φ̃_{m}` with `‖c m‖ ≤ 1`, to which the CZ estimate applies.
2. **Support and major arcs** (`gSupport_threshold` + `randSymbG_support_le`): if the
   major-arc threshold `k₂ + Cρ 2^{ρl₂} + 2 ≤ 2^{L/C₀-2}` holds, then `Φ` is supported in the
   single arc `ℝ_{≤⌊-Cρ 2^{ρl₂}⌋}`, which has good major arcs.
3. **The discrete estimate** (`narrow_IWLqBound` at the two levels `l₂` and `l₂ - 1`, then
   `IWLqBound_diffFreqs_of_arithFreqs`): area `A1` supplies the `IWLqBound`s over
   `iwArithFreqs ρ l₂` and `iwArithFreqs ρ (l₂-1)`; their difference is `diffFreqs ρ l₂`, and
   `eLpNorm_iwConv_le_of_IWLqBound` (Fatou along the truncations) passes from finitely supported
   inputs to all of `ℓ^{p₂}`.  Since the multiplier constant is `C'(1+k₂) ≤ C'(1+L)` and
   `⟨l⟩ ≤ 1 + L`, the resulting constant is `O((1+L)^3)`, absorbed by the weight with `A = 3`.
4. **The bounded case** (`Tm_randSymbG_crude_bound`): if the threshold fails, then
   `L ≤ L₀(ρ,C₀,Cρ)` is bounded (`L_le_of_threshold_fail`) and the crude kernel estimate gives a
   constant, which the weight (≥ 1) absorbs.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Tm_randSymbG_crude_bound
import Submission.Work.KMTAreas.A7.IWLqBound_diffFreqs_of_arithFreqs
import Submission.Work.KMTAreas.A7.randSymb_Tle_g_bound
import Submission.Work.KMTAreas.A7Hi.varphitildeNtMultBound

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## §1.  Elementary bounds for the telescoping coefficients -/

/-- The telescoping coefficient of an interval is a difference of two terms of modulus `≤ 1`. -/
lemma tmglp_teleCoef_norm_le_two (ε : ℕ → ℂ) (hε : ∀ n, ‖ε n‖ ≤ 1) (K m : ℕ) :
    ‖teleCoef ε K m‖ ≤ 2 := by
  have h1 : ‖(if 1 ≤ m ∧ m ≤ K then ε (m - 1) else 0 : ℂ)‖ ≤ 1 := by
    by_cases h : 1 ≤ m ∧ m ≤ K
    · rw [if_pos h]; exact hε _
    · rw [if_neg h]; simp
  have h2 : ‖(if m < K then ε m else 0 : ℂ)‖ ≤ 1 := by
    by_cases h : m < K
    · rw [if_pos h]; exact hε _
    · rw [if_neg h]; simp
  have h := norm_sub_le (if 1 ≤ m ∧ m ≤ K then ε (m - 1) else 0 : ℂ)
    (if m < K then ε m else 0 : ℂ)
  unfold teleCoef
  linarith

/-- **The coefficients of the telescoped `g`-side symbol are bounded by `2`.** -/
lemma tmglp_randSymbGCoef_norm_le_two (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (ε : ℕ → ℂ) (hε : ∀ n, ‖ε n‖ ≤ 1) (K m : ℕ) :
    ‖randSymbGCoef ρ C₀ a l₁ l₂ k₁ k₂ ε K m‖ ≤ 2 := by
  unfold randSymbGCoef
  by_cases h : randAct ρ C₀ a l₁ l₂ k₁ k₂ m
  · rw [if_pos h]; exact tmglp_teleCoef_norm_le_two ε hε K m
  · rw [if_neg h]; simp

/-! ## §2.  Scaling a continuous multiplier bound -/

/-- **`IsLqMultiplierBound` is stable under multiplication of the symbol by a natural number.** -/
lemma tmglp_lq_const_mul_nat {q : ENNReal} (m : ℕ) {φ : ℝ → ℂ} {M : NNReal}
    (h : IsLqMultiplierBound q φ M) :
    IsLqMultiplierBound q (fun x : ℝ => (m : ℂ) * φ x) ((m : NNReal) * M) := by
  intro G
  have h1 : contMulOp (fun x : ℝ => (m : ℂ) * φ x) (G : ℝ → ℂ)
      = (m : ℂ) • contMulOp φ (G : ℝ → ℂ) := by
    funext x
    rw [contMulOp, contMulOp]
    have h2 : (fun ξ : ℝ => ((m : ℂ) * φ ξ) * 𝓕 (G : ℝ → ℂ) ξ)
        = fun ξ : ℝ => (m : ℂ) * (φ ξ * 𝓕 (G : ℝ → ℂ) ξ) := by
      funext ξ; ring
    rw [h2, lacBump_fourierInv_const_mul]
    rfl
  rw [h1]
  calc eLpNorm ((m : ℂ) • contMulOp φ (G : ℝ → ℂ)) q (volume : Measure ℝ)
      = ‖(m : ℂ)‖ₑ * eLpNorm (contMulOp φ (G : ℝ → ℂ)) q (volume : Measure ℝ) :=
        eLpNorm_const_smul (m : ℂ) (contMulOp φ (G : ℝ → ℂ)) q (volume : Measure ℝ)
    _ ≤ ‖(m : ℂ)‖ₑ * (ENNReal.ofReal (M : ℝ) * eLpNorm (G : ℝ → ℂ) q (volume : Measure ℝ)) :=
        mul_le_mul_of_nonneg_left (h G) zero_le
    _ = ENNReal.ofReal (((m : NNReal) * M : NNReal) : ℝ) *
          eLpNorm (G : ℝ → ℂ) q (volume : Measure ℝ) := by
        have hm : ‖(m : ℂ)‖ₑ = (m : ENNReal) := by
          rw [← ofReal_norm, Complex.norm_natCast, ENNReal.ofReal_natCast]
        have hco : ENNReal.ofReal (((m : NNReal) * M : NNReal) : ℝ)
            = (m : ENNReal) * (M : ENNReal) := by
          rw [NNReal.coe_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
            ENNReal.ofReal_coe_nnreal, ENNReal.coe_natCast]
        rw [hm, hco, ENNReal.ofReal_coe_nnreal]
        ring

/-! ## §3.  The continuous multiplier bound for the randomised `g`-side symbol -/

/-- **The randomised `g`-side symbol is a bounded `L^q(ℝ)` Fourier multiplier, with a constant
*linear* in the height `k₂`.**  The two cases are the paper's scale split: `k₂ = 0` is the
Mikhlin (low frequency) regime, and `k₂ ≥ 1` is the shifted Calderón–Zygmund regime. -/
theorem tmglp_randSymbG_mult (P : Polynomial ℤ) (Λ : NNReal) (hΛ : 1 < Λ) (q : ℝ) (hq : 1 < q) :
    ∃ C : NNReal, 0 < C ∧
      ∀ (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1/2 : ℝ) 1 → (∀ n, ‖ε n‖ ≤ 1) →
        IsLqMultiplierBound (ENNReal.ofReal q)
          (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K) (C * (1 + (k₂ : NNReal))) := by
  obtain ⟨Cm, hCmpos, hCm⟩ := isLqMultiplierBound_of_mikhlin q hq
  obtain ⟨Kg, hKg0, hKg⟩ := randSymbG_mikhlin P P.natDegree le_rfl Λ hΛ
  obtain ⟨Ccz, hCczpos, hCcz⟩ := varphitildeNt_mult_bound_k2pos_hi P P.natDegree le_rfl q hq Λ hΛ
  refine ⟨max (Real.toNNReal (Cm * (Kg * 4)))
      (2 * Ccz * (((P.natDegree + 1 : ℕ)) : NNReal)), ?_, ?_⟩
  · refine lt_of_lt_of_le ?_ (le_max_right _ _)
    exact_mod_cast (show (0:ℝ) < 2 * ((Ccz:ℝ)) * (((P.natDegree + 1 : ℕ)) : ℝ) by positivity)
  intro ρ C₀ a l₁ l₂ k₁ k₂ K t ε ha ha1 ht hε
  rcases Nat.eq_zero_or_pos k₂ with hk0 | hkpos
  · -- ## the case `k₂ = 0`: the Mikhlin route
    obtain ⟨Φ, hΦcoe⟩ := gRandSymb_schwartz ρ P C₀ a l₁ l₂ k₁ k₂ t ε K
    obtain ⟨hcoeff, hIcc⟩ :=
      randSymbG_telescope ρ P C₀ a l₁ l₂ k₁ k₂ t ε hε (gMonotone_of_lacunary hΛ ha ha1) K
    have hmikh := hKg k₂ t ht a ha ha1 K (randSymbGCoef ρ C₀ a l₁ l₂ k₁ k₂ ε K) hIcc
    have hmikh' : MikhlinBound (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K)
        (Kg * (1 + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2) := by
      rw [hcoeff]; exact hmikh
    have hcd : ContDiff ℝ 2 (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K) := by
      rw [← hΦcoe]; exact Φ.smooth 2
    obtain ⟨hM, -⟩ := hCm hcd hmikh'
    rw [hk0] at hM ⊢
    refine IsLqMultiplierBound.mono hM ?_
    have h4 : (Cm * (Kg * (1 + (2:ℝ) ^ (P.natDegree * 0)) ^ 2)) = Cm * (Kg * 4) := by norm_num
    rw [h4]
    simp only [Nat.cast_zero, add_zero, mul_one]
    exact le_max_left _ _
  · -- ## the case `k₂ ≥ 1`: the shifted Calderón–Zygmund route
    obtain ⟨hcoeff, hIcc⟩ :=
      randSymbG_telescope ρ P C₀ a l₁ l₂ k₁ k₂ t ε hε (gMonotone_of_lacunary hΛ ha ha1) K
    have hc2 : ∀ m, ‖randSymbGCoef ρ C₀ a l₁ l₂ k₁ k₂ ε K m‖ ≤ 2 :=
      fun m => tmglp_randSymbGCoef_norm_le_two ρ C₀ a l₁ l₂ k₁ k₂ ε hε K m
    have hcε : ∀ m, ‖(randSymbGCoef ρ C₀ a l₁ l₂ k₁ k₂ ε K m) / 2‖ ≤ 1 := by
      intro m
      rw [norm_div]
      have h4 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      rw [h4]
      linarith [hc2 m]
    have hcz := hCcz k₂ hkpos t ht a ha ha1 (Finset.range (K + 1))
      (fun m => randSymbGCoef ρ C₀ a l₁ l₂ k₁ k₂ ε K m / 2) hcε
    have hsym : randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K
        = fun ξ : ℝ => (2 : ℂ) * ∑ m ∈ Finset.range (K + 1),
            (randSymbGCoef ρ C₀ a l₁ l₂ k₁ k₂ ε K m / 2) *
              varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t ξ := by
      rw [hcoeff]
      funext ξ
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => by ring)
    rw [hsym]
    refine IsLqMultiplierBound.mono (tmglp_lq_const_mul_nat 2 hcz) ?_
    refine le_trans (by rw [← NNReal.coe_le_coe]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) P.natDegree, NNReal.coe_nonneg k₂]) (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-! ## §4.  The single-scale estimate -/

theorem randSymb_Tm_g_lp (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    ∀ (C₀ : ℕ), 1 ≤ C₀ →
      ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε' : ℕ → ℂ) (g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          (∀ n, ‖ε' n‖ ≤ 1) → t ∈ Set.Icc ((1:ℝ)/2) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.KMTAreas.A7.Tm ρ l₂
                (Work.KMTAreas.A7.randSymb (Work.KMTAreas.A7.smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε' K) g x)
            p₂ MeasureTheory.Measure.count
          ≤ (C Λ : ENNReal) *
              ENNReal.ofReal ((1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ A *
                (2 : ℝ) ^ (A * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)) *
              MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  intro C₀ hC₀
  set p : ℝ := p₂.toReal with hpdef
  have hp : 1 < p := by
    rw [hpdef]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top htp₂.ne).mpr hp₂
  have hp2eq : p₂ = ENNReal.ofReal p := by
    rw [hpdef]; exact (ENNReal.ofReal_toReal htp₂.ne).symm
  obtain ⟨k₀, hk₀, hpk, hpk'⟩ := exists_endpoint_exponent p hp
  have hk₀max : max p (p / (p - 1)) ≤ 2 * (k₀ : ℝ) := max_le hpk hpk'
  have hq2 : 1 < 2 * (k₀ : ℝ) := by
    have h : 1 < 2 * k₀ := by omega
    exact_mod_cast h
  have hexp : ((2 * k₀ : ℕ) : ℝ≥0∞) = ENNReal.ofReal (2 * (k₀ : ℝ)) := by
    rw [← ENNReal.ofReal_natCast (2 * k₀)]; congr 1; push_cast; ring
  have hex_q : ∀ (Λ : NNReal), 1 < Λ → ∃ C : NNReal, 0 < C ∧
      ∀ (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1/2 : ℝ) 1 → (∀ n, ‖ε n‖ ≤ 1) →
        IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
          (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K) (C * (1 + (k₂ : NNReal))) :=
    fun Λ hΛ => tmglp_randSymbG_mult P Λ hΛ (2 * (k₀ : ℝ)) hq2
  set Cmf : NNReal → NNReal :=
    (fun Λ => if h : 1 < Λ then Classical.choose (hex_q Λ h) else 1) with hCmfdef
  have hCmfpos : ∀ Λ, 0 < Cmf Λ := by
    intro Λ
    by_cases h : 1 < Λ
    · rw [hCmfdef]; simp only [dif_pos h]
      exact (Classical.choose_spec (hex_q Λ h)).1
    · rw [hCmfdef]; simp only [dif_neg h]; norm_num
  have hCmfspec : ∀ (Λ : NNReal) (hΛ : 1 < Λ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
      (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      t ∈ Set.Icc (1/2 : ℝ) 1 → (∀ n, ‖ε n‖ ≤ 1) →
      IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
        (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K) (Cmf Λ * (1 + (k₂ : NNReal))) := by
    intro Λ hΛ
    have hval : Cmf Λ = Classical.choose (hex_q Λ hΛ) := by rw [hCmfdef]; simp only [dif_pos hΛ]
    rw [hval]
    exact (Classical.choose_spec (hex_q Λ hΛ)).2
  refine ⟨3, by norm_num, ?_⟩
  refine ⟨min (1/2) (1/(2 * (C₀ : ℝ))), lt_min (by norm_num) (by positivity), ?_⟩
  intro ρ hρ hρρ₀
  have hρ1 : ρ ≤ 1 := le_trans hρρ₀ (le_trans (min_le_left _ _) (by norm_num))
  have hρC₀ : ρ * (C₀ : ℝ) ≤ 1/2 := by
    have h1 : ρ ≤ 1/(2 * (C₀:ℝ)) := le_trans hρρ₀ (min_le_right _ _)
    have h2 : (0:ℝ) < (C₀:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC₀)
    have h3 : ρ * (C₀:ℝ) ≤ (1/(2 * (C₀:ℝ))) * (C₀:ℝ) := mul_le_mul_of_nonneg_right h1 h2.le
    have h4 : (1/(2*(C₀:ℝ))) * (C₀:ℝ) = 1/2 := by field_simp
    linarith
  obtain ⟨Cρ₀, hCρ₀pos, hNA₀, hEven₀⟩ := hA1 ρ hρ hρ1
  obtain ⟨Cev, hCevpos, hEvenRaw⟩ := hEven₀ k₀ hk₀
  set Cρ : ℝ := max Cρ₀ 2 with hCρdef
  have hCρ2 : 2 ≤ Cρ := by rw [hCρdef]; exact le_max_right _ _
  have hCρpos : 0 < Cρ := lt_of_lt_of_le (by norm_num) hCρ2
  have hCρ₀le : Cρ₀ ≤ Cρ := by rw [hCρdef]; exact le_max_left _ _
  set Cbar : ℝ := max 1 (Cρ / (P.natDegree : ℝ)) with hCbardef
  have hCbar1 : 1 ≤ Cbar := by rw [hCbardef]; exact le_max_left _ _
  obtain ⟨L₀, hL₀⟩ := Work.KMTPlan.A6.L_le_of_threshold_fail ρ hρ C₀ hC₀ Cbar hCbar1 hρC₀
  set Mcr : ℕ := max L₀ (2 ^ (2 ^ (2 * L₀ + 1))) with hMcrdef
  obtain ⟨Ccrude, hCcrude⟩ := Tm_randSymbG_crude_bound P p hp ρ hρ C₀ Mcr
  set C : NNReal → NNReal :=
    (fun Λ => 2 * max 1 (Cev : NNReal) * Cmf Λ + 1 + Ccrude Λ) with hCdef
  refine ⟨C, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ K t ε g hΛ hLac ha1 hε ht
  let L : ℝ := lmaxR l₁ l₂ k₁ k₂
  let Wr : ℝ := (1 + L) ^ (3:ℝ) * (2:ℝ) ^ (3 * ρ * L)
  have hWrcoe : Wr = (1 + L) ^ (3:ℝ) * (2:ℝ) ^ (3 * ρ * L) := rfl
  have hLnat : L = ((Lnat l₁ l₂ k₁ k₂ : ℕ) : ℝ) := by
    show lmaxR l₁ l₂ k₁ k₂ = ((Lnat l₁ l₂ k₁ k₂ : ℕ) : ℝ)
    exact gLmaxR_eq_Lnat l₁ l₂ k₁ k₂
  have hLnn : 0 ≤ L := by rw [hLnat]; positivity
  have hk₂L : (k₂ : ℝ) ≤ L := by
    rw [hLnat]; exact_mod_cast (le_trans (le_max_right k₁ k₂) (le_max_right _ _))
  have hl₂L : (l₂ : ℝ) ≤ L := by
    rw [hLnat]; exact_mod_cast (le_trans (le_max_right l₁ l₂) (le_max_left _ _))
  have hWr1 : (1:ℝ) ≤ Wr := by
    rw [hWrcoe]
    have h1 : (1:ℝ) ≤ 1 + L := by linarith
    have h2 : (1:ℝ) ≤ (1 + L) ^ (3:ℝ) := Real.one_le_rpow h1 (by norm_num)
    have h3 : (1:ℝ) ≤ (2:ℝ) ^ (3 * ρ * L) := Real.one_le_rpow (by norm_num) (by positivity)
    calc (1:ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ (1 + L) ^ (3:ℝ) * (2:ℝ) ^ (3 * ρ * L) :=
          mul_le_mul h2 h3 (by norm_num) (le_trans zero_le_one h2)
  have hWrpos : 0 < Wr := lt_of_lt_of_le (by norm_num) hWr1
  by_cases hthr : (k₂ : ℝ) + Cbar * (2:ℝ) ^ (ρ * (l₂ : ℝ)) + 2 ≤
      (2:ℝ) ^ (((Lnat l₁ l₂ k₁ k₂ : ℕ) : ℝ) / (C₀ : ℝ) - 2)
  · -- ## the narrow (good major arcs) case
    have hgood : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₂ ⌊-Cρ * 2 ^ (ρ * (l₂ : ℝ))⌋ := by
      show ((⌊-Cρ * 2 ^ (ρ * (l₂ : ℝ))⌋ : ℤ) : ℝ) ≤ -Cρ * 2 ^ (ρ * (l₂ : ℝ))
      exact_mod_cast Int.floor_le _
    have hNA : ∀ (l : ℕ) (k : ℤ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k →
        Work.Analysis.IonescuWainger.NonAliasing k (iwArithFreqs ρ l) :=
      fun l k hg => hNA₀ l k (gGoodMajorArcs_mono_const hCρ₀le hg)
    have hEven : ∀ (l : ℕ) (k : ℤ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k →
        ∀ (φ : SchwartzMap ℝ ℂ), (∀ x, φ x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k) →
        ∀ (Mv : NNReal), IsLqMultiplierBound ((2 * k₀ : ℕ) : ENNReal) (⇑φ) Mv →
        IWLqBound (iwArithFreqs ρ l) (periodize (⇑φ)) ((2 * k₀ : ℕ) : ENNReal)
          (Cev * angleBracket l * Mv) :=
      fun l k hg φ hφ Mv hM => hEvenRaw l k (gGoodMajorArcs_mono_const hCρ₀le hg) φ hφ Mv hM
    obtain ⟨Φ, hΦcoe⟩ := gRandSymb_schwartz ρ P C₀ a l₁ l₂ k₁ k₂ t ε K
    have hsupp : ∀ n : ℕ, smallCond ρ C₀ a l₁ l₂ k₁ k₂ n →
        (2 : ℝ) ^ ((P.natDegree : ℤ) * ((k₂ : ℤ) - logN (Nat.floor (a n)))) ≤
          (2 : ℝ) ^ (⌊-Cρ * 2 ^ (ρ * (l₂ : ℝ))⌋) := by
      intro n hn
      exact gSupport_threshold ρ Cρ Cbar P C₀ hC₀ (by omega) (le_max_right _ _) hn.1 hthr
    have hΦsupp : ∀ x : ℝ, Φ x ≠ 0 →
        x ∈ Work.Analysis.IonescuWainger.realArc ⌊-Cρ * 2 ^ (ρ * (l₂ : ℝ))⌋ := by
      intro x hx
      rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
      have hx' : randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K x ≠ 0 := by
        rw [← congrFun hΦcoe x]; exact hx
      exact abs_le.mp (randSymbG_support_le ρ P C₀ a l₁ l₂ k₁ k₂ t ε K _ hsupp x hx')
    set S : NNReal := ⟨1 + L, by positivity⟩ with hSdef
    have hScoe : (S : ℝ) = 1 + L := rfl
    set Mv : NNReal := Cmf Λ * S with hMvdef
    have hMvpos : 0 < Mv := by
      rw [hMvdef]
      refine mul_pos (hCmfpos Λ) ?_
      rw [← NNReal.coe_pos, hScoe]; linarith
    have hMvle : Cmf Λ * (1 + (k₂ : NNReal)) ≤ Mv := by
      rw [hMvdef]
      refine mul_le_mul_of_nonneg_left ?_ (zero_le)
      rw [← NNReal.coe_le_coe, hScoe]
      push_cast
      linarith [hk₂L, hLnn]
    have hMm : IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
        (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K) (Cmf Λ * (1 + (k₂ : NNReal))) :=
      hCmfspec Λ hΛ ρ C₀ a l₁ l₂ k₁ k₂ K t ε hLac ha1 ht hε
    have hM : IsLqMultiplierBound ((2 * k₀ : ℕ) : ENNReal) (⇑Φ) Mv := by
      rw [hexp, hΦcoe]
      exact IsLqMultiplierBound.mono hMm hMvle
    have hMst : IsLqMultiplierBound ((2 * k₀ : ℕ) : ENNReal) (fun x => star (Φ x)) Mv := by
      rw [hexp, hΦcoe]
      exact IsLqMultiplierBound.mono (IsLqMultiplierBound_star hMm) hMvle
    have hb₁ := narrow_IWLqBound hA1 hp hρ hCρ2 hNA hk₀ hpk hpk' hEven hgood hΦsupp hMvpos hM hMst
    have hgood' : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ (l₂ - 1)
        ⌊-Cρ * 2 ^ (ρ * (l₂ : ℝ))⌋ := by
      show ((⌊-Cρ * 2 ^ (ρ * (l₂ : ℝ))⌋ : ℤ) : ℝ) ≤ -Cρ * 2 ^ (ρ * ((l₂ - 1 : ℕ) : ℝ))
      have h1 : ((⌊-Cρ * 2 ^ (ρ * (l₂ : ℝ))⌋ : ℤ) : ℝ) ≤ -Cρ * 2 ^ (ρ * (l₂ : ℝ)) :=
        Int.floor_le _
      have h2 : ((l₂ - 1 : ℕ) : ℝ) ≤ (l₂ : ℝ) := by
        have := Nat.sub_le l₂ 1
        exact_mod_cast this
      have h3 : (2:ℝ) ^ (ρ * ((l₂ - 1 : ℕ) : ℝ)) ≤ (2:ℝ) ^ (ρ * (l₂ : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hρ, h2])
      nlinarith [h1, h3, hCρpos]
    have hb₂ := narrow_IWLqBound hA1 hp hρ hCρ2 hNA hk₀ hpk hpk' hEven hgood' hΦsupp hMvpos hM hMst
    have hq1 : (1 : ENNReal) < ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : (0:ℝ) < p)).mpr hp
    have hb := IWLqBound_diffFreqs_of_arithFreqs ρ hρ hρ1 l₂ Φ hq1 hb₁ hb₂
    have hCpos : (0 : NNReal) < max (angleBracket l₂ * Mv) (Cev * angleBracket l₂ * Mv) +
        max (angleBracket (l₂ - 1) * Mv) (Cev * angleBracket (l₂ - 1) * Mv) := by
      have h1 : (0:NNReal) < angleBracket l₂ * Mv := mul_pos (angleBracket_pos l₂) hMvpos
      exact lt_of_lt_of_le (lt_of_lt_of_le h1 (le_max_left _ _))
        (le_add_of_nonneg_right (zero_le))
    have hfin := eLpNorm_iwConv_le_of_IWLqBound (diffFreqs ρ l₂) Φ hp hCpos hb g
    have hTm : Tm ρ l₂ (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K) g
        = iwConv (diffFreqs ρ l₂) (periodize (⇑Φ)) g := by
      rw [← hΦcoe]; rfl
    rw [hp2eq, hTm]
    -- the constant bookkeeping
    set Wn : NNReal := Real.toNNReal Wr with hWnset
    have hWncoe : (Wn : ℝ) = Wr := by rw [hWnset, Real.coe_toNNReal Wr (le_of_lt hWrpos)]
    have hbR : ((angleBracket l₂ : NNReal) : ℝ) ≤ (S : ℝ) := by
      rw [hScoe]
      have h : ((angleBracket l₂ : NNReal) : ℝ) = max 1 (l₂ : ℝ) := by
        simp only [angleBracket, NNReal.coe_max, NNReal.coe_one, NNReal.coe_natCast]
      rw [h]
      exact max_le (by linarith) (by linarith [hl₂L])
    have hbR1 : ((angleBracket (l₂ - 1) : NNReal) : ℝ) ≤ (S : ℝ) := by
      rw [hScoe]
      have h : ((angleBracket (l₂ - 1) : NNReal) : ℝ) = max 1 ((l₂ - 1 : ℕ) : ℝ) := by
        simp only [angleBracket, NNReal.coe_max, NNReal.coe_one, NNReal.coe_natCast]
      rw [h]
      refine max_le (by linarith) ?_
      have h2 : ((l₂ - 1 : ℕ) : ℝ) ≤ (l₂ : ℝ) := by
        have := Nat.sub_le l₂ 1
        exact_mod_cast this
      linarith
    have hS2W : S * S ≤ Wn := by
      rw [← NNReal.coe_le_coe, NNReal.coe_mul, hScoe, hWncoe, hWrcoe]
      have hL1 : (1:ℝ) ≤ 1 + L := by linarith
      have h4 : (1 + L) * (1 + L) ≤ (1 + L) ^ (3:ℝ) := by
        have h5 : (1 + L) ^ (3:ℝ) = (1 + L) * (1 + L) * (1 + L) := by
          rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
          ring
        rw [h5]
        nlinarith [hL1]
      have h3 : (1:ℝ) ≤ (2:ℝ) ^ (3 * ρ * L) := Real.one_le_rpow (by norm_num) (by positivity)
      have hp3 : (0:ℝ) ≤ (1 + L) ^ (3:ℝ) := Real.rpow_nonneg (by linarith) _
      calc (1 + L) * (1 + L) ≤ (1 + L) ^ (3:ℝ) := h4
        _ = (1 + L) ^ (3:ℝ) * 1 := (mul_one _).symm
        _ ≤ (1 + L) ^ (3:ℝ) * (2:ℝ) ^ (3 * ρ * L) := mul_le_mul_of_nonneg_left h3 hp3
    have hbS : angleBracket l₂ ≤ S := by
      rw [← NNReal.coe_le_coe]; simpa using hbR
    have hbS1 : angleBracket (l₂ - 1) ≤ S := by
      rw [← NNReal.coe_le_coe]; simpa using hbR1
    have hSM : S * Mv ≤ Cmf Λ * Wn := by
      rw [hMvdef]
      calc S * (Cmf Λ * S) = Cmf Λ * (S * S) := by ring
        _ ≤ Cmf Λ * Wn := mul_le_mul_of_nonneg_left hS2W (zero_le)
    have hmulS : ∀ a : NNReal, a ≤ S → a * Mv ≤ max 1 Cev * (Cmf Λ * Wn) := by
      intro a ha
      calc a * Mv ≤ S * Mv := mul_le_mul_of_nonneg_right ha (zero_le)
        _ ≤ Cmf Λ * Wn := hSM
        _ ≤ max 1 Cev * (Cmf Λ * Wn) := by
            calc Cmf Λ * Wn = 1 * (Cmf Λ * Wn) := (one_mul _).symm
              _ ≤ max 1 Cev * (Cmf Λ * Wn) :=
                  mul_le_mul_of_nonneg_right (le_max_left (1 : NNReal) Cev) zero_le
    have hmulC : ∀ a : NNReal, a ≤ S → Cev * (a * Mv) ≤ max 1 Cev * (Cmf Λ * Wn) := by
      intro a ha
      have h1 : a * Mv ≤ Cmf Λ * Wn :=
        le_trans (mul_le_mul_of_nonneg_right ha (zero_le)) hSM
      calc Cev * (a * Mv) ≤ Cev * (Cmf Λ * Wn) := mul_le_mul_of_nonneg_left h1 (zero_le)
        _ ≤ max 1 Cev * (Cmf Λ * Wn) :=
            mul_le_mul_of_nonneg_right (le_max_right (1 : NNReal) Cev) zero_le
    have hstep : max (angleBracket l₂ * Mv) (Cev * angleBracket l₂ * Mv) +
        max (angleBracket (l₂ - 1) * Mv) (Cev * angleBracket (l₂ - 1) * Mv) ≤ C Λ * Wn := by
      have h1 : max (angleBracket l₂ * Mv) (Cev * angleBracket l₂ * Mv) ≤
          max 1 Cev * (Cmf Λ * Wn) := by
        refine max_le (hmulS _ hbS) ?_
        rw [mul_assoc]
        exact hmulC _ hbS
      have h2 : max (angleBracket (l₂ - 1) * Mv) (Cev * angleBracket (l₂ - 1) * Mv) ≤
          max 1 Cev * (Cmf Λ * Wn) := by
        refine max_le (hmulS _ hbS1) ?_
        rw [mul_assoc]
        exact hmulC _ hbS1
      calc max (angleBracket l₂ * Mv) (Cev * angleBracket l₂ * Mv) +
            max (angleBracket (l₂ - 1) * Mv) (Cev * angleBracket (l₂ - 1) * Mv)
          ≤ max 1 Cev * (Cmf Λ * Wn) + max 1 Cev * (Cmf Λ * Wn) := add_le_add h1 h2
        _ = 2 * (max 1 Cev * (Cmf Λ * Wn)) := by ring
        _ = 2 * max 1 Cev * Cmf Λ * Wn := by ring
        _ ≤ (2 * max 1 Cev * Cmf Λ + 1) * Wn := by
            rw [add_mul, one_mul]
            exact le_add_of_nonneg_right (zero_le)
        _ ≤ C Λ * Wn := by
            refine mul_le_mul_of_nonneg_right ?_ (zero_le)
            rw [hCdef]
            exact le_add_of_nonneg_right (zero_le)
    refine hfin.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    have hreal : (((max (angleBracket l₂ * Mv) (Cev * angleBracket l₂ * Mv) +
        max (angleBracket (l₂ - 1) * Mv) (Cev * angleBracket (l₂ - 1) * Mv)) : NNReal) : ℝ)
        ≤ ((C Λ : NNReal) : ℝ) * Wr := by
      have h := NNReal.coe_le_coe.mpr hstep
      rw [NNReal.coe_mul, hWncoe] at h
      exact h
    calc ENNReal.ofReal (((max (angleBracket l₂ * Mv) (Cev * angleBracket l₂ * Mv) +
            max (angleBracket (l₂ - 1) * Mv) (Cev * angleBracket (l₂ - 1) * Mv)) : NNReal) : ℝ)
        ≤ ENNReal.ofReal (((C Λ : NNReal) : ℝ) * Wr) := ENNReal.ofReal_le_ofReal hreal
      _ = (C Λ : ENNReal) * ENNReal.ofReal Wr := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
  · -- ## the crude case: the threshold fails
    have hk : k₂ ≤ Lnat l₁ l₂ k₁ k₂ := le_trans (le_max_right k₁ k₂) (le_max_right _ _)
    have hl : l₂ ≤ Lnat l₁ l₂ k₁ k₂ := le_trans (le_max_right l₁ l₂) (le_max_left _ _)
    have hL0 : Lnat l₁ l₂ k₁ k₂ ≤ L₀ := by
      refine hL₀ (Lnat l₁ l₂ k₁ k₂) k₂ l₂ hk hl ?_
      intro hcon
      exact hthr hcon
    have hMax : smallL l₁ l₂ k₁ k₂ ≤ Mcr := by
      have hsm : smallL l₁ l₂ k₁ k₂ = Lnat l₁ l₂ k₁ k₂ := by simp only [smallL, Lnat]
      rw [hsm]
      exact le_trans hL0 (le_max_left _ _)
    have hcr := hCcrude Λ a l₁ l₂ k₁ k₂ K t ε g hΛ hLac ha1 hMax ht hε
    rw [hp2eq]
    refine hcr.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    have h1 : (Ccrude Λ : ENNReal) ≤ (C Λ : ENNReal) := by
      refine ENNReal.coe_le_coe.mpr ?_
      rw [hCdef]
      exact le_add_of_nonneg_left (zero_le)
    have h2 : (1:ENNReal) ≤ ENNReal.ofReal Wr := ENNReal.one_le_ofReal.mpr hWr1
    calc (Ccrude Λ : ENNReal) = (Ccrude Λ : ENNReal) * 1 := (mul_one _).symm
      _ ≤ (C Λ : ENNReal) * ENNReal.ofReal Wr := mul_le_mul h1 h2 (zero_le) (zero_le)

end

end Work.KMTAreas.A7
