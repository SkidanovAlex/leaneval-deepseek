import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17.lc_defs
import Submission.Work.C17I.subst_eval_abs
import Submission.Work.C17I.sympSym_deriv_coeff_bound
import Submission.Work.C17I.seventeen_subst_eval
import Submission.Work.C17I.hasSum_tsum_of_coeff_growth
import Submission.Work.C17I.xsOf_ge_eight_ninths
import Submission.Work.C17I.sympPhi_series
import Submission.Work.C17I.ball_p0C_bounds

namespace Work.C17I

open PowerSeries

/-!
# `Sym⁺(logP)` as an analytic function of `y = z²/(z-1)`

`Sym⁺H` is defined (`Submission.CDT.sympSym`) by the substitution identity
`(Sym⁺H)∘y = H + H∘φ`, where `y = x²/(x-1)`, `φ = x/(x-1)`
(`Submission.CDT.sympSym_subst`).  The main lemma `sympSym_tsum_eq` evaluates the
`y`-series of `Sym⁺H` at a point `z` with `‖z‖ ≤ 39/100`:

`Σ_k coeff_k(Sym⁺H)·yC z^k = P(z) + P(φ z)`,

where `P(z) = Σ_k coeff_k H · z^k` and `φ z = z/(z-1)`.  The proof is the classical
composition formula for convergent power series (`subst_eval_abs`), applied twice:
once to `(Sym⁺H)∘y` (using `sympSym_subst`) and once to `H∘φ`.

The target `Gfun_repr` then identifies `P` with `Pfun` (by definition) and `P(φ z)`
with `Ψ z` (the continuation hypothesis).
-/

/-- **Evaluation of the symmetrised series.**  Let `H ∈ ℚ⟦X⟧` have coefficients of
exponential type `6/5` (`‖coeff_k H‖ ≤ C₀·(6/5)^k`).  Then for every `z` with
`‖z‖ ≤ 39/100` the `y`-series of `G = Sym⁺H` converges at `yC z = z²/(z-1)` and

`Σ_k coeff_k(G)·(z²/(z-1))^k = Σ_k coeff_k(H)·z^k + Σ_k coeff_k(H)·(z/(z-1))^k.` -/
theorem sympSym_tsum_eq {H : PowerSeries ℚ} {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hP : ∀ k : ℕ, ‖((PowerSeries.coeff k H : ℚ) : ℂ)‖ ≤ C₀ * (6 / 5 : ℝ) ^ k)
    {z : ℂ} (hz : ‖z‖ ≤ 39 / 100) :
    (∑' k : ℕ, ((PowerSeries.coeff k (Submission.CDT.sympSym H) : ℚ) : ℂ) * Work.C17.yC z ^ k)
      = (∑' k : ℕ, ((PowerSeries.coeff k H : ℚ) : ℂ) * z ^ k)
        + (∑' k : ℕ, ((PowerSeries.coeff k H : ℚ) : ℂ) * (z / (z - 1)) ^ k) := by
  have hz1 : ‖z‖ < 1 := by linarith
  -- growth of the coefficients of `G = Sym⁺H`
  obtain ⟨C₁, hC₁, hGb⟩ :
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
        ‖((PowerSeries.coeff n (Submission.CDT.sympSym H) : ℚ) : ℂ)‖ ≤ C * 4 ^ n := by
    simpa only [Function.iterate_zero_apply] using
      Work.C17I.sympSym_deriv_coeff_bound (P := H) hC₀ (by norm_num) (by norm_num) hP 0 (by norm_num)
  -- the `y`-series
  have hYv : (∑' n : ℕ, ((PowerSeries.coeff n Submission.CDT.sympY : ℚ) : ℂ) * z ^ n)
      = Work.C17.yC z := (Work.C17I.sympY_hasSum z hz1).tsum_eq
  have hYS : Summable
      (fun n : ℕ => ‖((PowerSeries.coeff n Submission.CDT.sympY : ℚ) : ℂ)‖ * (39 / 100 : ℝ) ^ n) :=
    (Work.C17I.sympY_norm_hasSum (by norm_num) (by norm_num)).summable
  have hYR : (∑' n : ℕ, ‖((PowerSeries.coeff n Submission.CDT.sympY : ℚ) : ℂ)‖
        * (39 / 100 : ℝ) ^ n) < 1 / 4 := by
    rw [(Work.C17I.sympY_norm_hasSum (by norm_num) (by norm_num)).tsum_eq]
    norm_num
  have hY0 : PowerSeries.constantCoeff Submission.CDT.sympY = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Submission.CDT.coeff_sympY_zero
  have hfG : ∀ n : ℕ,
      ‖((PowerSeries.coeff n (Submission.CDT.sympSym H) : ℚ) : ℂ)‖ * (1 / 4 : ℝ) ^ n ≤ C₁ := by
    intro n
    calc ‖((PowerSeries.coeff n (Submission.CDT.sympSym H) : ℚ) : ℂ)‖ * (1 / 4 : ℝ) ^ n
        ≤ (C₁ * 4 ^ n) * (1 / 4 : ℝ) ^ n := mul_le_mul_of_nonneg_right (hGb n) (by positivity)
      _ = C₁ * ((4 : ℝ) * (1 / 4)) ^ n := by rw [mul_pow]; ring
      _ = C₁ := by rw [show ((4 : ℝ) * (1 / 4)) = 1 by norm_num, one_pow, mul_one]
  -- the composition formula for `(Sym⁺H)∘y`
  have hsA := Work.C17I.subst_eval_abs (f := Submission.CDT.sympSym H) (g := Submission.CDT.sympY)
    (C := C₁) (R := 1 / 4) (ρ := 39 / 100) (z := z)
    hC₁.le (by norm_num) (by norm_num) hY0 hfG hYS hYR hz
  have hLHS : (∑' n : ℕ, ((PowerSeries.coeff n (Submission.CDT.sympSym H) : ℚ) : ℂ)
        * (∑' m : ℕ, ((PowerSeries.coeff m Submission.CDT.sympY : ℚ) : ℂ) * z ^ m) ^ n)
      = ∑' k : ℕ, ((PowerSeries.coeff k (Submission.CDT.sympSym H) : ℚ) : ℂ) * Work.C17.yC z ^ k := by
    rw [hYv]
  have hsA' : HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n ((Submission.CDT.sympSym H).subst Submission.CDT.sympY) : ℚ) : ℂ)
          * z ^ n)
      (∑' k : ℕ, ((PowerSeries.coeff k (Submission.CDT.sympSym H) : ℚ) : ℂ) * Work.C17.yC z ^ k) :=
    hLHS ▸ hsA
  -- the composition formula for `H∘φ`
  have hPhiv : (∑' m : ℕ, ((PowerSeries.coeff m Submission.CDT.sympPhi : ℚ) : ℂ) * z ^ m)
      = z / (z - 1) := (Work.C17I.sympPhi_series.1 z hz1).tsum_eq
  have hPhiS : Summable
      (fun n : ℕ => ‖((PowerSeries.coeff n Submission.CDT.sympPhi : ℚ) : ℂ)‖ * (39 / 100 : ℝ) ^ n) :=
    (Work.C17I.sympPhi_series.2 (39 / 100) (by norm_num) (by norm_num)).summable
  have hPhiR : (∑' n : ℕ, ‖((PowerSeries.coeff n Submission.CDT.sympPhi : ℚ) : ℂ)‖
        * (39 / 100 : ℝ) ^ n) < 5 / 6 := by
    rw [(Work.C17I.sympPhi_series.2 (39 / 100) (by norm_num) (by norm_num)).tsum_eq]
    norm_num
  have hPhi0 : PowerSeries.constantCoeff Submission.CDT.sympPhi = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Submission.CDT.coeff_sympPhi_zero
  have hfH : ∀ n : ℕ, ‖((PowerSeries.coeff n H : ℚ) : ℂ)‖ * (5 / 6 : ℝ) ^ n ≤ C₀ := by
    intro n
    calc ‖((PowerSeries.coeff n H : ℚ) : ℂ)‖ * (5 / 6 : ℝ) ^ n
        ≤ (C₀ * (6 / 5 : ℝ) ^ n) * (5 / 6 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (hP n) (by positivity)
      _ = C₀ * (((6 : ℝ) / 5) * (5 / 6)) ^ n := by rw [mul_pow]; ring
      _ = C₀ := by rw [show (((6 : ℝ) / 5) * (5 / 6)) = 1 by norm_num, one_pow, mul_one]
  have hsPhi := Work.C17I.subst_eval_abs (f := H) (g := Submission.CDT.sympPhi)
    (C := C₀) (R := 5 / 6) (ρ := 39 / 100) (z := z)
    hC₀.le (by norm_num) (by norm_num) hPhi0 hfH hPhiS hPhiR hz
  have hsPhi' : HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n (H.subst Submission.CDT.sympPhi) : ℚ) : ℂ) * z ^ n)
      (∑' n : ℕ, ((PowerSeries.coeff n H : ℚ) : ℂ) * (z / (z - 1)) ^ n) := by
    rw [hPhiv] at hsPhi
    exact hsPhi
  -- the series of `H` itself at `z`
  have hHs : HasSum (fun n : ℕ => ((PowerSeries.coeff n H : ℚ) : ℂ) * z ^ n)
      (∑' n : ℕ, ((PowerSeries.coeff n H : ℚ) : ℂ) * z ^ n) := by
    refine Work.C17I.hasSum_tsum_of_coeff_growth hC₀.le (by norm_num) hP z ?_
    have h56 : (1 : ℝ) / (6 / 5) = 5 / 6 := by norm_num
    rw [h56]; linarith
  have hsum := hHs.add hsPhi'
  have hfun : ∀ n : ℕ,
      ((PowerSeries.coeff n (H + H.subst Submission.CDT.sympPhi) : ℚ) : ℂ) * z ^ n
        = ((PowerSeries.coeff n H : ℚ) : ℂ) * z ^ n
          + ((PowerSeries.coeff n (H.subst Submission.CDT.sympPhi) : ℚ) : ℂ) * z ^ n := by
    intro n
    rw [map_add]
    push_cast
    ring
  have hsB : HasSum
      (fun n : ℕ => ((PowerSeries.coeff n (H + H.subst Submission.CDT.sympPhi) : ℚ) : ℂ) * z ^ n)
      ((∑' n : ℕ, ((PowerSeries.coeff n H : ℚ) : ℂ) * z ^ n)
        + (∑' n : ℕ, ((PowerSeries.coeff n H : ℚ) : ℂ) * (z / (z - 1)) ^ n)) :=
    hsum.congr_fun hfun
  have hsub := Submission.CDT.sympSym_subst H
  have hsA'' : HasSum
      (fun n : ℕ => ((PowerSeries.coeff n (H + H.subst Submission.CDT.sympPhi) : ℚ) : ℂ) * z ^ n)
      (∑' k : ℕ, ((PowerSeries.coeff k (Submission.CDT.sympSym H) : ℚ) : ℂ) * Work.C17.yC z ^ k) := by
    refine hsA'.congr_fun (fun n => ?_)
    rw [hsub]
  exact hsA''.unique hsB

/-! ## The target -/

theorem Gfun_repr (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hlt : m < n)
    (hgap : 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n) (ra rb rab r0 : ℤ) {C : ℝ} (hC : 0 < C)
    (hP : ∀ k : ℕ,
      ‖((PowerSeries.coeff k (Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0) : ℚ) : ℂ)‖
        ≤ C * (6 / 5 : ℝ) ^ k)
    {S : Set ℂ} {Ψ : ℂ → ℂ} (hS : Metric.ball Work.C17.p0C (1 / 20) ⊆ S)
    (hΨd : DifferentiableOn ℂ Ψ S)
    (hΨv : ∀ z ∈ S, ‖z / (z - 1)‖ < Work.C17.xsOf m n →
        Ψ z = Work.C17.Pfun (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 (z / (z - 1))) :
    ∀ z ∈ Metric.ball Work.C17.p0C (1 / 20),
      (∑' k : ℕ,
        ((PowerSeries.coeff k (Submission.CDT.sympSym
            (Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0)) : ℚ) : ℂ)
          * Work.C17.yC z ^ k)
        = Work.C17.Pfun (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 z + Ψ z := by
  intro z hz
  obtain ⟨hsw, hzn⟩ := Work.C17I.ball_p0C_bounds hz
  have hxs := Work.C17I.xsOf_ge_eight_ninths m n hm hlt hgap
  have hswxs : ‖z / (z - 1)‖ < Work.C17.xsOf m n := lt_of_lt_of_le hsw hxs
  have hmain := sympSym_tsum_eq (H := Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0) hC hP hzn
  have hval := hΨv z (hS hz) hswxs
  rw [hval]
  exact hmain

end Work.C17I
