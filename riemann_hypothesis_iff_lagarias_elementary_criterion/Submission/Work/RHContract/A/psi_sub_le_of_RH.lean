import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.zeta1Order_triv
import Submission.Work.RHContract.A.zeroSumBeta_le
import Submission.Work.RHContract.A.psi_sub_arith_up
import Submission.Work.RHContract.A.psi_sub_arith_down

/-!
# `Work.RHContract.A.psi_sub_le_of_RH`

Under the Riemann hypothesis, `|ψ x − x| ≤ 0.45 x^{3/4} + 2` for every `x ≥ 200`.

The proof uses the integrated ("tilted") explicit formula of the corpus
(`Commons.NumberTheory.Zeta.psiIntegral_tilted_explicit`):

  `∫_0^y ψ = y²/2 − y log(2π) + C − Σ'_ρ m_ρ y^{ρ+1}/(ρ(ρ+1))`   for `y ≥ 1`,

the sharp zero-sum bound `Σ_ρ m_ρ/|ρ|² ≤ β = 2 + γ − log 4π` of
`Commons.NumberTheory.Zeta.zeroSum_finset_le_beta`, and the monotonicity of `ψ`: averaging
the formula over `[x, x+h]` and over `[x−h, x]`, with `h = (43/100) x^{3/4}`, gives the
claim.  The trivial zeros `ρ = −2(k+1)` are separated out; they contribute a nonnegative
amount at most `1/y`.
-/

namespace Work.RHContract.A

open scoped BigOperators
open MeasureTheory

noncomputable section

/-! ## Inputs from the fleet

* `Work.RHContract.A.zeta1Order_triv` : the trivial zeros `−2(k+1)` of `ζ₁` are simple;
* `Work.RHContract.A.zeroSumBeta_le` : `β = 2 + γ − log(4π) ≤ 48/1000`;
* `Work.RHContract.A.psi_sub_arith_up`, `…_down` : the two explicit real inequalities
  consumed at the very end of the proof.
-/

/-- The constant `β = 2 + γ − log(4π)` of the sharp zero-sum bound. -/
def zeroSumBeta : ℝ := 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

/-! ## The zeros of `ζ₁`

`ζ₁ = (s−1)·ζ` away from `s = 1`, so its zeros are the nontrivial zeros of `ζ` (which lie on
the critical line under RH) together with the trivial zeros `−2(k+1)`.
-/

lemma zeta1_eq_sub_mul_zeta {s : ℂ} (hs : s ≠ 1) :
    riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta₁, riemannZeta_eq_inv_sub_add hs]
  field_simp

lemma zeta_eq_zero_of_zeta1_eq_zero {s : ℂ} (hs : s ≠ 1) (h : riemannZeta₁ s = 0) :
    riemannZeta s = 0 := by
  rw [zeta1_eq_sub_mul_zeta hs] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hs)

lemma zeta1Order_eq_zero_of_ne_zero {ρ : ℂ} (h : riemannZeta₁ ρ ≠ 0) :
    Commons.NumberTheory.Zeta.zeta1Order ρ = 0 := by
  unfold Commons.NumberTheory.Zeta.zeta1Order
  rw [dif_neg h]

/-- Under RH, a zero of `ζ₁` is either trivial (`−2(k+1)`) or on the critical line. -/
lemma re_eq_half_of_zeta1_zero_of_not_triv (h : RiemannHypothesis) {ρ : ℂ}
    (hρ : riemannZeta₁ ρ = 0) (hnt : ¬ ∃ k : ℕ, ρ = -2 * ((k : ℂ) + 1)) : ρ.re = 1 / 2 := by
  have hρ1 : ρ ≠ 1 := by
    intro h1
    rw [h1, riemannZeta₁_one] at hρ
    exact one_ne_zero hρ
  exact h ρ (zeta_eq_zero_of_zeta1_eq_zero hρ1 hρ) hnt hρ1

/-- For a zero `ρ` of `ζ₁` on the critical line, `zeta1Order ρ` is the multiplicity of `ρ`
as a zero of the completed `ξ`, i.e. the divisor of `Ξ` on the ball of radius `R`. -/
lemma zeta1Order_eq_divisor {R : ℝ} (hR : 0 ≤ R) {ρ : ℂ}
    (hρ : riemannZeta₁ ρ = 0) (hρR : ‖ρ‖ ≤ R) (h1 : 1 / 4 < ρ.re) (h2 : ρ.re < 2) :
    (Commons.NumberTheory.Zeta.zeta1Order ρ : ℤ) =
      MeromorphicOn.divisor (fun z : ℂ => (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) *
        completedRiemannZeta₀ z) (Metric.closedBall 0 R) ρ := by
  have hspec := Classical.choose_spec
    (Commons.NumberTheory.Zeta.zeta1_logDeriv_pole_removal ρ hρ)
  unfold Commons.NumberTheory.Zeta.zeta1Order
  rw [dif_pos hρ]
  exact Commons.NumberTheory.Zeta.divisor_xi_eq_logDeriv_pole_order
    hR hρ hρR h1 h2 hspec.1 hspec.2

/-- The sharp zero-sum bound for finite sets of critical-line zeros: `Σ_ρ m_ρ/‖ρ‖² ≤ β`. -/
lemma sum_zeta1Order_div_sq_le (h : RiemannHypothesis) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, riemannZeta₁ ρ = 0 ∧ 1 / 4 < ρ.re ∧ ρ.re < 2) :
    S.sum (fun ρ => (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2)
      ≤ zeroSumBeta := by
  set R : ℝ := S.sum (fun ρ => ‖ρ‖) + 1 with hRdef
  have hR0 : 0 ≤ R := by
    have : 0 ≤ S.sum (fun ρ => ‖ρ‖) := Finset.sum_nonneg (fun i _ => norm_nonneg i)
    rw [hRdef]; linarith
  have hSR : ∀ ρ ∈ S, riemannZeta₁ ρ = 0 ∧ ‖ρ‖ ≤ R ∧ 1 / 4 < ρ.re ∧ ρ.re < 2 := by
    intro ρ hρ
    obtain ⟨h1, h2, h3⟩ := hS ρ hρ
    refine ⟨h1, ?_, h2, h3⟩
    have hle : ‖ρ‖ ≤ S.sum (fun i => ‖i‖) :=
      Finset.single_le_sum (fun i _ => norm_nonneg i) hρ
    rw [hRdef]; linarith
  have hb := Commons.NumberTheory.Zeta.zeroSum_finset_le_beta h R hR0 S hSR
  refine le_trans (le_of_eq ?_) hb
  refine Finset.sum_congr rfl (fun ρ hρ => ?_)
  have h1 := (hSR ρ hρ).1
  have h2 := (hSR ρ hρ).2.1
  have h3 := (hSR ρ hρ).2.2.1
  have h4 := (hSR ρ hρ).2.2.2
  have key := zeta1Order_eq_divisor hR0 h1 h2 h3 h4
  have keyR : (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) =
      ((MeromorphicOn.divisor (fun z : ℂ => (1 / 2 : ℂ) + (1 / 2 : ℂ) * z * (z - 1) *
        completedRiemannZeta₀ z) (Metric.closedBall 0 R) ρ : ℤ) : ℝ) := by
    rw [← key]
    norm_num
  rw [keyR]

/-! ## The tilted summand and its pointwise bounds -/

/-- The tilted summand `m_ρ y^{ρ+1}/(ρ(ρ+1))`. -/
def tiltTerm (y : ℝ) (ρ : ℂ) : ℂ :=
  (Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ) * (y : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))

/-- Trivial zero: `ρ = −2(k+1)`. -/
def isTriv (ρ : ℂ) : Prop := ∃ k : ℕ, ρ = -2 * ((k : ℂ) + 1)

instance : DecidablePred isTriv := fun _ => Classical.propDecidable _

/-- On the critical line, `‖ρ+1‖² = ‖ρ‖² + 2`. -/
lemma norm_add_one_sq_of_re_half {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ‖ρ + 1‖ ^ 2 = ‖ρ‖ ^ 2 + 2 := by
  have hh := Complex.normSq_add ρ 1
  have h1 : Complex.normSq (ρ + 1) = Complex.normSq ρ + 1 + 2 * ρ.re := by
    rw [hh]
    simp
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hre] at h1
  linarith

lemma norm_le_norm_add_one_of_re_half {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ‖ρ‖ ≤ ‖ρ + 1‖ := by
  have h := norm_add_one_sq_of_re_half hre
  nlinarith [norm_nonneg ρ, norm_nonneg (ρ + 1)]

/-- For a zero `ρ` of `ζ₁` on the critical line, the tilted summand at `ρ` is bounded by
`y^{3/2}·m_ρ/‖ρ‖²`. -/
lemma norm_tilt_le_of_re_half {y : ℝ} (hy : 1 ≤ y) {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ‖tiltTerm y ρ‖ ≤ y ^ (3 / 2 : ℝ) * ((Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2) := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    norm_num at hre
  have hρ1 : ρ + 1 ≠ 0 := by
    intro h
    have h2 : ρ = -1 := by linear_combination h
    rw [h2] at hre
    norm_num at hre
  have hle : ‖ρ‖ ≤ ‖ρ + 1‖ := norm_le_norm_add_one_of_re_half hre
  have hm : (0 : ℝ) ≤ (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) := Nat.cast_nonneg _
  have hyle : (0 : ℝ) ≤ y ^ (3 / 2 : ℝ) := Real.rpow_nonneg hypos.le _
  have hρn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  unfold tiltTerm
  rw [norm_div, norm_mul, norm_mul, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hypos, Complex.add_re, Complex.one_re, hre]
  have h32 : (1 / 2 : ℝ) + 1 = 3 / 2 := by norm_num
  rw [h32]
  have hstep : (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)
      ≤ (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2 := by
    apply div_le_div_of_nonneg_left hm (by positivity)
    nlinarith [hle, hρn]
  calc (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) * y ^ (3 / 2 : ℝ) / (‖ρ‖ * ‖ρ + 1‖)
      = y ^ (3 / 2 : ℝ) * ((Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / (‖ρ‖ * ‖ρ + 1‖)) := by
        ring
    _ ≤ y ^ (3 / 2 : ℝ) * ((Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hstep hyle

/-- The trivial zero `−2(k+1)` contributes the real number `y^{−(2k+1)}/((2k+2)(2k+1))`. -/
lemma tiltTerm_triv {y : ℝ} (hy : 1 ≤ y) (k : ℕ) :
    tiltTerm y (-2 * ((k : ℂ) + 1))
      = ((y ^ (-(2 * (k : ℝ) + 1)) / ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1)) : ℝ) : ℂ) := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hρ1 : ((-2 : ℂ) * ((k : ℂ) + 1)) + 1 = -(((2 * k + 1 : ℕ)) : ℂ) := by
    push_cast; ring
  have hρ : (-2 : ℂ) * ((k : ℂ) + 1) = -(((2 * (k + 1) : ℕ)) : ℂ) := by push_cast; ring
  have h1 : (((-2 : ℂ) * ((k : ℂ) + 1)) + 1).re = -(2 * (k : ℝ) + 1) := by
    rw [hρ1, Complex.neg_re, Complex.natCast_re]
    push_cast
    ring
  have hexp : (((-2 : ℂ) * ((k : ℂ) + 1)) + 1) = ((-(2 * (k : ℝ) + 1) : ℝ) : ℂ) := by
    push_cast
    ring
  have hcpp : (y : ℂ) ^ (((-2 : ℂ) * ((k : ℂ) + 1)) + 1)
      = ((y ^ (-(2 * (k : ℝ) + 1)) : ℝ) : ℂ) := by
    rw [hexp, ← Complex.ofReal_cpow hypos.le]
  have hcc : ((-2 : ℂ) * ((k : ℂ) + 1)) * (((-2 : ℂ) * ((k : ℂ) + 1)) + 1)
      = (((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) : ℝ) : ℂ) := by
    rw [hρ]
    push_cast
    ring
  unfold tiltTerm
  rw [zeta1Order_triv k, hcpp, hcc, show ((1 : ℕ) : ℂ) = 1 by norm_num, one_mul,
    ← Complex.ofReal_div]

/-- The trivial zero `−2(k+1)` contributes at most `1/(y·(k+1)(k+2))` in norm. -/
lemma norm_triv_term_le {y : ℝ} (hy : 1 ≤ y) (k : ℕ) :
    ‖tiltTerm y (-2 * ((k : ℂ) + 1))‖ ≤ 1 / (y * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hval := tiltTerm_triv hy k
  rw [hval, Complex.norm_real, Real.norm_eq_abs]
  have hdenpos : 0 < (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) := by positivity
  have hpos1 : 0 < y * ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
  have hle1 : y ^ (-(2 * (k : ℝ) + 1)) ≤ y ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hy (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hkle : ((k : ℝ) + 1) * ((k : ℝ) + 2) ≤ (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hnn : (0 : ℝ) ≤ y ^ (-(2 * (k : ℝ) + 1)) / ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1)) :=
    div_nonneg (Real.rpow_nonneg hypos.le _) hdenpos.le
  rw [abs_of_nonneg hnn, div_le_div_iff₀ hdenpos hpos1]
  have h1 : y ^ (-(2 * (k : ℝ) + 1)) * (y * ((k : ℝ) + 1) * ((k : ℝ) + 2))
      ≤ y ^ (-1 : ℝ) * (y * ((k : ℝ) + 1) * ((k : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_right hle1 (by positivity)
  have h2 : y ^ (-1 : ℝ) * (y * ((k : ℝ) + 1) * ((k : ℝ) + 2))
      = ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
    rw [Real.rpow_neg_one]
    field_simp
  linarith [h1, h2, hkle]

/-- `Σ_k 1/((k+1)(k+2)) ≤ 1` over a finite set of indices. -/
lemma sum_one_div_mul_succ_le_one (s : Finset ℕ) :
    s.sum (fun k => 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) ≤ 1 := by
  classical
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range s
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hN (fun i _ _ => by positivity)) ?_
  have htel : ∀ i : ℕ,
      (1 : ℝ) / (((i : ℝ) + 1) * ((i : ℝ) + 2)) = 1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2) := by
    intro i
    have h1 : ((i : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((i : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun i _ => htel i)]
  have htel2 : ∀ M : ℕ,
      (∑ i ∈ Finset.range M, (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)))
        = 1 - 1 / ((M : ℝ) + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
        have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
        field_simp
        ring
  rw [htel2]
  have hpos : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  linarith

/-- The total contribution of the trivial zeros `−2(k+1)` inside a finite set of zeros. -/
lemma triv_sum_le {y : ℝ} (hy : 1 ≤ y) (T : Finset ℂ) (hT : ∀ ρ ∈ T, isTriv ρ) :
    T.sum (fun ρ => ‖tiltTerm y ρ‖) ≤ 1 / y := by
  classical
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  set nn : ℂ → ℕ := fun ρ => if h : isTriv ρ then Classical.choose h else 0 with hnn
  have hnn_spec : ∀ ρ ∈ T, ρ = -2 * ((nn ρ : ℂ) + 1) := by
    intro ρ hρ
    have h : isTriv ρ := hT ρ hρ
    have hc : nn ρ = Classical.choose h := by rw [hnn]; exact dif_pos h
    rw [hc]
    exact Classical.choose_spec h
  have hinj : Set.InjOn nn ↑T := by
    intro a ha b hb hab
    have ha' := hnn_spec a (by simpa using ha)
    have hb' := hnn_spec b (by simpa using hb)
    rw [ha', hb', hab]
  have hle : T.sum (fun ρ => ‖tiltTerm y ρ‖)
      ≤ T.sum (fun ρ => 1 / (y * ((nn ρ : ℝ) + 1) * ((nn ρ : ℝ) + 2))) := by
    refine Finset.sum_le_sum (fun ρ hρ => ?_)
    have hb := norm_triv_term_le hy (nn ρ)
    conv_lhs => rw [hnn_spec ρ hρ]
    exact hb
  refine le_trans hle ?_
  rw [← Finset.sum_image (s := T) (g := nn)
    (f := fun k : ℕ => 1 / (y * ((k : ℝ) + 1) * ((k : ℝ) + 2))) hinj]
  have h2 : (T.image nn).sum (fun k => 1 / (y * ((k : ℝ) + 1) * ((k : ℝ) + 2)))
      = (1 / y) * (T.image nn).sum (fun k => 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    field_simp
  rw [h2]
  have h3 := sum_one_div_mul_succ_le_one (T.image nn)
  have h4 : (0 : ℝ) ≤ 1 / y := by positivity
  calc (1 / y) * (T.image nn).sum (fun k => 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)))
      ≤ (1 / y) * 1 := mul_le_mul_of_nonneg_left h3 h4
    _ = 1 / y := by ring

/-! ## The two pieces of the tilted zero sum -/

/-- The nontrivial part of the tilted zero sum. -/
def Tnontriv (y : ℝ) : ℂ := ∑' ρ : ℂ, if isTriv ρ then 0 else tiltTerm y ρ

/-- The trivial part of the tilted zero sum. -/
def Ttriv (y : ℝ) : ℂ := ∑' ρ : ℂ, if isTriv ρ then tiltTerm y ρ else 0

/-- The whole tilted zero sum. -/
def Zsum (y : ℝ) : ℂ := ∑' ρ : ℂ, tiltTerm y ρ

/-- Its real part, the term of the integrated explicit formula. -/
def Zreal (y : ℝ) : ℝ := (Zsum y).re

lemma finset_nontriv_le (h : RiemannHypothesis) {y : ℝ} (hy : 1 ≤ y) (T : Finset ℂ) :
    T.sum (fun ρ => ‖if isTriv ρ then 0 else tiltTerm y ρ‖)
      ≤ zeroSumBeta * y ^ (3 / 2 : ℝ) := by
  classical
  have hcongr : T.sum (fun ρ => ‖if isTriv ρ then 0 else tiltTerm y ρ‖)
      = (T.filter (fun ρ => ¬ isTriv ρ)).sum (fun ρ => ‖tiltTerm y ρ‖) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    by_cases htr : isTriv ρ <;> simp [htr]
  rw [hcongr]
  set S : Finset ℂ := (T.filter (fun ρ => ¬ isTriv ρ)).filter (fun ρ => riemannZeta₁ ρ = 0)
    with hS
  have hpt : (T.filter (fun ρ => ¬ isTriv ρ)).sum (fun ρ => ‖tiltTerm y ρ‖)
      ≤ (T.filter (fun ρ => ¬ isTriv ρ)).sum
        (fun ρ => y ^ (3 / 2 : ℝ)
          * ((Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2)) := by
    apply Finset.sum_le_sum
    intro ρ hρ
    by_cases hz : riemannZeta₁ ρ = 0
    · exact norm_tilt_le_of_re_half hy
        (re_eq_half_of_zeta1_zero_of_not_triv h hz (Finset.mem_filter.mp hρ).2)
    · have hzero : tiltTerm y ρ = 0 := by
        unfold tiltTerm
        rw [zeta1Order_eq_zero_of_ne_zero hz]
        ring
      rw [hzero, zeta1Order_eq_zero_of_ne_zero hz]
      simp
  refine le_trans hpt ?_
  rw [← Finset.mul_sum]
  have hSS : (T.filter (fun ρ => ¬ isTriv ρ)).sum
      (fun ρ => (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2)
      = S.sum (fun ρ => (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2) := by
    rw [hS]
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    by_cases hz : riemannZeta₁ ρ = 0
    · simp [hz]
    · simp [hz, zeta1Order_eq_zero_of_ne_zero hz]
  rw [hSS]
  have hSbound : S.sum (fun ρ => (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2)
      ≤ zeroSumBeta := by
    apply sum_zeta1Order_div_sq_le h S
    intro ρ hρ
    obtain ⟨hρT, hz⟩ := Finset.mem_filter.mp hρ
    have hnt : ¬ isTriv ρ := (Finset.mem_filter.mp hρT).2
    have hhalf := re_eq_half_of_zeta1_zero_of_not_triv h hz hnt
    exact ⟨hz, by rw [hhalf]; norm_num, by rw [hhalf]; norm_num⟩
  calc y ^ (3 / 2 : ℝ) * S.sum (fun ρ => (Commons.NumberTheory.Zeta.zeta1Order ρ : ℝ) / ‖ρ‖ ^ 2)
      ≤ y ^ (3 / 2 : ℝ) * zeroSumBeta :=
        mul_le_mul_of_nonneg_left hSbound (Real.rpow_nonneg (by positivity) _)
    _ = zeroSumBeta * y ^ (3 / 2 : ℝ) := by ring

lemma finset_triv_le {y : ℝ} (hy : 1 ≤ y) (T : Finset ℂ) :
    T.sum (fun ρ => ‖if isTriv ρ then tiltTerm y ρ else 0‖) ≤ 1 / y := by
  classical
  have hcongr : T.sum (fun ρ => ‖if isTriv ρ then tiltTerm y ρ else 0‖)
      = (T.filter (fun ρ => isTriv ρ)).sum (fun ρ => ‖tiltTerm y ρ‖) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    by_cases htr : isTriv ρ <;> simp [htr]
  rw [hcongr]
  exact triv_sum_le hy _ (fun ρ hρ => (Finset.mem_filter.mp hρ).2)

lemma summable_Tnontriv (h : RiemannHypothesis) {y : ℝ} (hy : 1 ≤ y) :
    Summable (fun ρ : ℂ => if isTriv ρ then 0 else tiltTerm y ρ) :=
  Summable.of_norm (summable_of_sum_le (fun _ => norm_nonneg _)
    (fun T => finset_nontriv_le h hy T))

lemma summable_Ttriv {y : ℝ} (hy : 1 ≤ y) :
    Summable (fun ρ : ℂ => if isTriv ρ then tiltTerm y ρ else 0) :=
  Summable.of_norm (summable_of_sum_le (fun _ => norm_nonneg _)
    (fun T => finset_triv_le hy T))

lemma norm_Tnontriv_le (h : RiemannHypothesis) {y : ℝ} (hy : 1 ≤ y) :
    ‖Tnontriv y‖ ≤ zeroSumBeta * y ^ (3 / 2 : ℝ) := by
  have hsumm := summable_Tnontriv h hy
  have hmem : ∀ᶠ T : Finset ℂ in Filter.atTop,
      (∑ ρ ∈ T, if isTriv ρ then 0 else tiltTerm y ρ)
        ∈ Metric.closedBall (0 : ℂ) (zeroSumBeta * y ^ (3 / 2 : ℝ)) :=
    Filter.Eventually.of_forall (fun T => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_trans (norm_sum_le T _) (finset_nontriv_le h hy T))
  have hcl := Metric.isClosed_closedBall.mem_of_tendsto hsumm.hasSum hmem
  rw [Tnontriv]
  simpa [Metric.mem_closedBall, dist_zero_right] using hcl

lemma Ttriv_re_bounds {y : ℝ} (hy : 1 ≤ y) :
    0 ≤ (Ttriv y).re ∧ (Ttriv y).re ≤ 1 / y := by
  have hsumm := summable_Ttriv hy
  have hresum : Summable (fun ρ : ℂ => (if isTriv ρ then tiltTerm y ρ else 0).re) :=
    Summable.of_norm ((hsumm.norm).of_nonneg_of_le (fun _ => abs_nonneg _)
      (fun ρ => Complex.abs_re_le_norm _))
  have hre : (Ttriv y).re = ∑' ρ : ℂ, (if isTriv ρ then tiltTerm y ρ else 0).re := by
    rw [Ttriv, Complex.re_tsum hsumm]
  constructor
  · rw [hre]
    refine tsum_nonneg (fun ρ => ?_)
    by_cases htr : isTriv ρ
    · rw [if_pos htr]
      obtain ⟨k, hk⟩ := htr
      rw [hk, tiltTerm_triv hy k, Complex.ofReal_re]
      positivity
    · rw [if_neg htr]
      norm_num
  · rw [hre]
    refine Summable.tsum_le_of_sum_le hresum (fun T => ?_)
    have h1 : T.sum (fun ρ : ℂ => (if isTriv ρ then tiltTerm y ρ else 0).re)
        ≤ T.sum (fun ρ : ℂ => ‖if isTriv ρ then tiltTerm y ρ else 0‖) := by
      have key : ∀ z : ℂ, z.re ≤ ‖z‖ := fun z => le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
      refine Finset.sum_le_sum (fun ρ _ => ?_)
      by_cases htr : isTriv ρ
      · simpa [if_pos htr] using key (tiltTerm y ρ)
      · simp [if_neg htr, Complex.zero_re]
    exact le_trans h1 (finset_triv_le hy T)

lemma Zsum_eq_Tnontriv_add (h : RiemannHypothesis) {y : ℝ} (hy : 1 ≤ y) :
    Zsum y = Tnontriv y + Ttriv y := by
  rw [Zsum, Tnontriv, Ttriv, ← Summable.tsum_add (summable_Tnontriv h hy) (summable_Ttriv hy)]
  exact tsum_congr (fun ρ => by by_cases htr : isTriv ρ <;> simp [htr])

/-- The constant of the integrated explicit formula. -/
def psiIntC : ℝ := Real.log (2 * Real.pi) - 1 + Real.eulerMascheroniConstant
  + (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) ^ 2).re

lemma Zreal_eq (h : RiemannHypothesis) {y : ℝ} (hy : 1 ≤ y) :
    Zreal y = (Tnontriv y).re + (Ttriv y).re := by
  rw [Zreal, Zsum_eq_Tnontriv_add h hy, Complex.add_re]

/-- The integrated explicit formula of the corpus, in real form. -/
lemma integral_psi_eq (h : RiemannHypothesis) {y : ℝ} (hy : 1 ≤ y) :
    (∫ t in (0 : ℝ)..y, Chebyshev.psi t)
      = y ^ 2 / 2 - y * Real.log (2 * Real.pi) + psiIntC - Zreal y := by
  have hc := Commons.NumberTheory.Zeta.psiIntegral_tilted_explicit h y hy
  have hiff : (∫ t in (0 : ℝ)..y, (Chebyshev.psi t : ℂ))
      = ((∫ t in (0 : ℝ)..y, Chebyshev.psi t : ℝ) : ℂ) := intervalIntegral.integral_ofReal
  have hre := congrArg Complex.re ((hc.symm.trans hiff).symm)
  rw [Complex.ofReal_re] at hre
  rw [Complex.sub_re, Complex.add_re, Complex.add_re, Complex.sub_re] at hre
  have e1 : (((y : ℂ) ^ 2 / 2)).re = y ^ 2 / 2 := by
    have h : ((y : ℂ) ^ 2 / 2) = ((y ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.ofReal_re]
  have e2 : (((y : ℂ) * ((Real.log (2 * Real.pi) : ℝ) : ℂ))).re = y * Real.log (2 * Real.pi) := by
    have h : ((y : ℂ) * ((Real.log (2 * Real.pi) : ℝ) : ℂ))
        = ((y * Real.log (2 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.ofReal_re]
  have e3 : ((((Real.log (2 * Real.pi) - 1 + Real.eulerMascheroniConstant : ℝ)) : ℂ)).re
      = Real.log (2 * Real.pi) - 1 + Real.eulerMascheroniConstant := Complex.ofReal_re _
  rw [e1, e2, e3] at hre
  rw [show (∑' ρ : ℂ, (Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ) * (y : ℂ) ^ (ρ + 1)
      / (ρ * (ρ + 1))).re = Zreal y from rfl] at hre
  rw [psiIntC]
  linarith [hre]

/-! ## Averages of `ψ` -/

lemma psi_le_avg {a b : ℝ} (hab : a < b) :
    Chebyshev.psi a ≤ (1 / (b - a)) * ∫ t in a..b, Chebyshev.psi t := by
  have hne : (0 : ℝ) < b - a := by linarith
  have hint : IntervalIntegrable Chebyshev.psi MeasureTheory.volume a b :=
    Chebyshev.psi_mono.intervalIntegrable
  have hconst : IntervalIntegrable (fun _ : ℝ => Chebyshev.psi a) volume a b :=
    intervalIntegrable_const
  have hmono : (∫ t in a..b, (fun _ : ℝ => Chebyshev.psi a) t)
      ≤ ∫ t in a..b, Chebyshev.psi t :=
    intervalIntegral.integral_mono_on hab.le hconst hint (fun t ht => Chebyshev.psi_mono ht.1)
  rw [intervalIntegral.integral_const] at hmono
  have hkey : (b - a) * Chebyshev.psi a ≤ ∫ t in a..b, Chebyshev.psi t := by
    simpa [smul_eq_mul] using hmono
  calc Chebyshev.psi a = (1 / (b - a)) * ((b - a) * Chebyshev.psi a) := by
        field_simp
    _ ≤ (1 / (b - a)) * ∫ t in a..b, Chebyshev.psi t :=
        mul_le_mul_of_nonneg_left hkey (by positivity)

lemma avg_le_psi {a b : ℝ} (hab : a < b) :
    (1 / (b - a)) * ∫ t in a..b, Chebyshev.psi t ≤ Chebyshev.psi b := by
  have hne : (0 : ℝ) < b - a := by linarith
  have hint : IntervalIntegrable Chebyshev.psi MeasureTheory.volume a b :=
    Chebyshev.psi_mono.intervalIntegrable
  have hconst : IntervalIntegrable (fun _ : ℝ => Chebyshev.psi b) volume a b :=
    intervalIntegrable_const
  have hmono : (∫ t in a..b, Chebyshev.psi t)
      ≤ ∫ t in a..b, (fun _ : ℝ => Chebyshev.psi b) t :=
    intervalIntegral.integral_mono_on hab.le hint hconst (fun t ht => Chebyshev.psi_mono ht.2)
  rw [intervalIntegral.integral_const] at hmono
  have hkey : (∫ t in a..b, Chebyshev.psi t) ≤ (b - a) * Chebyshev.psi b := by
    simpa [smul_eq_mul] using hmono
  calc (1 / (b - a)) * ∫ t in a..b, Chebyshev.psi t
      ≤ (1 / (b - a)) * ((b - a) * Chebyshev.psi b) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = Chebyshev.psi b := by field_simp

/-! ## The main theorem -/

theorem psi_sub_le_of_RH (h : RiemannHypothesis) (x : ℝ) (hx : 200 ≤ x) :
    |Chebyshev.psi x - x| ≤ 0.45 * x ^ (3 / 4 : ℝ) + 2 := by
  set hh : ℝ := 43 / 100 * x ^ (3 / 4 : ℝ) with hhdef
  have hxpos : 0 < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hhpos : 0 < hh := by rw [hhdef]; positivity
  have hhhalf : hh ≤ x / 2 := by
    rw [hhdef]
    have h1 : x ^ (3 / 4 : ℝ) ≤ x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [Real.rpow_one] at h1
    linarith
  have hxmm : (1 : ℝ) ≤ x - hh := by linarith
  have hxnh : (1 : ℝ) ≤ x + hh := by linarith
  have hPx := integral_psi_eq h hx1
  have hPxh := integral_psi_eq h hxnh
  have hPxmh := integral_psi_eq h hxmm
  have hdx : (∫ t in x..(x + hh), Chebyshev.psi t)
      = (∫ t in (0 : ℝ)..(x + hh), Chebyshev.psi t) - ∫ t in (0 : ℝ)..x, Chebyshev.psi t := by
    rw [← intervalIntegral.integral_interval_sub_left
      (Chebyshev.psi_mono.intervalIntegrable) (Chebyshev.psi_mono.intervalIntegrable)]
  have hdxm : (∫ t in (x - hh)..x, Chebyshev.psi t)
      = (∫ t in (0 : ℝ)..x, Chebyshev.psi t) - ∫ t in (0 : ℝ)..(x - hh), Chebyshev.psi t := by
    rw [← intervalIntegral.integral_interval_sub_left
      (Chebyshev.psi_mono.intervalIntegrable) (Chebyshev.psi_mono.intervalIntegrable)]
  -- upper estimate
  have hup : Chebyshev.psi x - x ≤ hh / 2 - Real.log (2 * Real.pi)
      + (zeroSumBeta * ((x + hh) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) + 1 / x) / hh := by
    have h1 := psi_le_avg (a := x) (b := x + hh) (by linarith)
    rw [show x + hh - x = hh by ring] at h1
    rw [hdx, hPxh, hPx] at h1
    have hkey : -(Zreal (x + hh) - Zreal x)
        ≤ zeroSumBeta * ((x + hh) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) + 1 / x := by
      rw [Zreal_eq h hxnh, Zreal_eq h hx1]
      have e1 : -((Tnontriv (x + hh)).re) ≤ zeroSumBeta * (x + hh) ^ (3 / 2 : ℝ) :=
        le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm _) (norm_Tnontriv_le h hxnh))
      have e2 : (Tnontriv x).re ≤ zeroSumBeta * x ^ (3 / 2 : ℝ) :=
        le_trans (le_abs_self _) (le_trans (Complex.abs_re_le_norm _) (norm_Tnontriv_le h hx1))
      have e3 : 0 ≤ (Ttriv (x + hh)).re := (Ttriv_re_bounds hxnh).1
      have e4 : (Ttriv x).re ≤ 1 / x := (Ttriv_re_bounds hx1).2
      linarith
    have h2 : (1 / hh) * (((x + hh) ^ 2 / 2 - (x + hh) * Real.log (2 * Real.pi) + psiIntC
          - Zreal (x + hh)) - (x ^ 2 / 2 - x * Real.log (2 * Real.pi) + psiIntC - Zreal x))
        = x + hh / 2 - Real.log (2 * Real.pi) - (Zreal (x + hh) - Zreal x) / hh := by
      field_simp
      ring
    rw [h2] at h1
    have hdiv : -((Zreal (x + hh) - Zreal x) / hh)
        ≤ (zeroSumBeta * ((x + hh) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) + 1 / x) / hh := by
      rw [← neg_div]
      exact div_le_div_of_nonneg_right hkey hhpos.le
    linarith
  -- lower estimate
  have hlow : x - Chebyshev.psi x ≤ hh / 2 + Real.log (2 * Real.pi)
      + (zeroSumBeta * (x ^ (3 / 2 : ℝ) + (x - hh) ^ (3 / 2 : ℝ)) + 1 / x) / hh := by
    have h1 := avg_le_psi (a := x - hh) (b := x) (by linarith)
    rw [show x - (x - hh) = hh by ring] at h1
    rw [hdxm, hPx, hPxmh] at h1
    have hkey : Zreal x - Zreal (x - hh)
        ≤ zeroSumBeta * (x ^ (3 / 2 : ℝ) + (x - hh) ^ (3 / 2 : ℝ)) + 1 / x := by
      rw [Zreal_eq h hx1, Zreal_eq h hxmm]
      have e1 : (Tnontriv x).re ≤ zeroSumBeta * x ^ (3 / 2 : ℝ) :=
        le_trans (le_abs_self _) (le_trans (Complex.abs_re_le_norm _) (norm_Tnontriv_le h hx1))
      have e2 : -((Tnontriv (x - hh)).re) ≤ zeroSumBeta * (x - hh) ^ (3 / 2 : ℝ) :=
        le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm _) (norm_Tnontriv_le h hxmm))
      have e3 : (Ttriv x).re ≤ 1 / x := (Ttriv_re_bounds hx1).2
      have e4 : 0 ≤ (Ttriv (x - hh)).re := (Ttriv_re_bounds hxmm).1
      linarith
    have h2 : (1 / hh) * ((x ^ 2 / 2 - x * Real.log (2 * Real.pi) + psiIntC - Zreal x)
          - ((x - hh) ^ 2 / 2 - (x - hh) * Real.log (2 * Real.pi) + psiIntC - Zreal (x - hh)))
        = x - hh / 2 - Real.log (2 * Real.pi) - (Zreal x - Zreal (x - hh)) / hh := by
      field_simp
      ring
    rw [h2] at h1
    have hdiv : (Zreal x - Zreal (x - hh)) / hh
        ≤ (zeroSumBeta * (x ^ (3 / 2 : ℝ) + (x - hh) ^ (3 / 2 : ℝ)) + 1 / x) / hh :=
      div_le_div_of_nonneg_right hkey hhpos.le
    linarith
  have hβ : zeroSumBeta ≤ 48 / 1000 := zeroSumBeta_le
  have hlog2 : (1 : ℝ) ≤ 2 * Real.log 2 := by
    have h9 := Real.log_two_gt_d9
    linarith
  have hone : 1 / x ≤ 2 * Real.log 2 / x := by
    rw [div_le_div_iff₀ hxpos hxpos]
    nlinarith [hlog2]
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hDpos : 0 < 43 / 100 * x ^ (3 / 4 : ℝ) := by positivity
    have hxmm0 : 0 < x - 43 / 100 * x ^ (3 / 4 : ℝ) := by
      rw [← hhdef]
      linarith [hxmm]
    have hcmp : (zeroSumBeta * (x ^ (3 / 2 : ℝ) + (x - 43 / 100 * x ^ (3 / 4 : ℝ)) ^ (3 / 2 : ℝ))
            + 1 / x) / (43 / 100 * x ^ (3 / 4 : ℝ))
        ≤ (zeroSumBeta * (x ^ (3 / 2 : ℝ) + (x - 43 / 100 * x ^ (3 / 4 : ℝ)) ^ (3 / 2 : ℝ)) + 1 / x
            + 1 / (x - 43 / 100 * x ^ (3 / 4 : ℝ))) / (43 / 100 * x ^ (3 / 4 : ℝ)) := by
      apply div_le_div_of_nonneg_right _ hDpos.le
      have hnn : 0 ≤ 1 / (x - 43 / 100 * x ^ (3 / 4 : ℝ)) := by positivity
      linarith
    rw [hhdef] at hlow
    have harith := psi_sub_arith_down zeroSumBeta x hβ hx
    linarith [hlow, harith, hcmp]
  · have hDpos : 0 < 43 / 100 * x ^ (3 / 4 : ℝ) := by positivity
    have hcmp : (zeroSumBeta * ((x + 43 / 100 * x ^ (3 / 4 : ℝ)) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ))
            + 1 / x) / (43 / 100 * x ^ (3 / 4 : ℝ))
        ≤ (zeroSumBeta * ((x + 43 / 100 * x ^ (3 / 4 : ℝ)) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ))
            + 2 * Real.log 2 / x) / (43 / 100 * x ^ (3 / 4 : ℝ)) := by
      apply div_le_div_of_nonneg_right _ hDpos.le
      linarith [hone]
    rw [hhdef] at hup
    have harith := psi_sub_arith_up zeroSumBeta x hβ hx
    linarith [hup, harith, hcmp]

end

end Work.RHContract.A
