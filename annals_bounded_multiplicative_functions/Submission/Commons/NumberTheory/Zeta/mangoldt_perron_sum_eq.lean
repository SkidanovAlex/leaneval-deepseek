import Mathlib
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_mul_rpow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Complex MeasureTheory intervalIntegral
open scoped BigOperators

namespace Commons.NumberTheory.Zeta

/-! # Perron-series: expanding the Dirichlet series inside the truncated integral
Let Λ(n) = ArithmeticFunction.vonMangoldt n (Λ 0 = 0), s(t) = (σ : ℂ) + Complex.I * (t : ℂ).
For 0 < x and 1 < σ the L-series of Λ converges absolutely on Re s = σ, so inside the
finite interval integral (t ∈ [-T, T]) we may swap the infinite sum and the integral:
    (1/(2π)) ∫_{-T}^{T} LSeries(Λ)(s) · x^s / s dt
        = Σ'_{n:ℕ} Λ(n) · (1/(2π)) ∫_{-T}^{T} exp(s · log(x/n)) / s dt,
using per-term identity  x^s / n^s = (x/n)^s = exp(s·log(x/n))  (bases positive: use
Complex.cpow_def_of_ne_zero, Complex.ofReal_log, div_cpow_of_real or similar), and the theorem
`MeasureTheory.intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm`
(or `MeasureTheory.integral_tsum` via dominated convergence) with the sup-norm summability
`Σ Λ(n) · (x/n)^σ · (1/σ) < ∞` on the compact interval uIcc (-T) T; prove that summability from
Λ(n) ≤ log n and Σ log n / n^σ < ∞ (Mathlib LSeries / PSeries API, e.g.
`LSeriesSummable_of_isBigO_rpow` or direct comparison).
The n = 0 summand is zero (Λ 0 = 0). σ > 1 keeps the denominator (σ + it) nonzero. -/

def vonMangoldtC (n : ℕ) : ℂ := ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)

def sigmaLine (σ : ℝ) (t : ℝ) : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)

def perronLog (x : ℝ) (n : ℕ) : ℂ := Complex.log (((x / (n : ℝ)) : ℝ) : ℂ)

lemma vonMangoldtC_zero : vonMangoldtC 0 = 0 := by
  simp [vonMangoldtC, ArithmeticFunction.map_zero]

lemma sigmaLine_re (σ : ℝ) (t : ℝ) : (sigmaLine σ t).re = σ := by
  simp [sigmaLine]

lemma sigmaLine_im (σ : ℝ) (t : ℝ) : (sigmaLine σ t).im = t := by
  simp [sigmaLine]

lemma sigmaLine_ne_zero (σ : ℝ) (hσ : σ ≠ 0) (t : ℝ) : sigmaLine σ t ≠ 0 := by
  intro hz
  have hre := congrArg Complex.re hz
  have : σ = 0 := by simpa [sigmaLine] using hre
  exact hσ this

lemma sigmaLine_continuous (σ : ℝ) : Continuous (fun t : ℝ => sigmaLine σ t) := by
  unfold sigmaLine
  fun_prop

lemma sigmaLine_norm_ge (σ : ℝ) (hσ : 0 < σ) (t : ℝ) : σ ≤ ‖sigmaLine σ t‖ := by
  have hsq : σ ^ 2 ≤ ‖sigmaLine σ t‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply, sigmaLine_re, sigmaLine_im]
    nlinarith
  have h : |σ| ≤ |‖sigmaLine σ t‖| := (sq_le_sq.mp hsq)
  rwa [abs_of_nonneg (le_of_lt hσ), abs_of_nonneg (norm_nonneg _)] at h

lemma vonMangoldtC_norm (n : ℕ) : ‖vonMangoldtC n‖ = (ArithmeticFunction.vonMangoldt n : ℝ) := by
  dsimp [vonMangoldtC]
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)

lemma perronLog_ofReal_div (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : n ≠ 0) :
    perronLog x n = (Real.log (x / (n : ℝ)) : ℂ) := by
  unfold perronLog
  rw [← Complex.ofReal_log (le_of_lt (div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))))]

lemma exp_cpow_ofReal_pos (z : ℝ) (hz : 0 < z) (s : ℂ) :
    ((z : ℂ) ^ s) = Complex.exp (s * Complex.log (z : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero]
  · congr 1
    rw [mul_comm]
  · exact_mod_cast hz.ne'

lemma div_cpow_ofReal_div (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (s : ℂ) :
    (a : ℂ) ^ s / (b : ℂ) ^ s = ((a / b : ℝ) : ℂ) ^ s := by
  calc
    (a : ℂ) ^ s / (b : ℂ) ^ s = (((a : ℂ) / (b : ℂ)) ^ s) :=
      (Complex.div_cpow_ofReal_nonneg ha hb s).symm
    _ = ((a / b : ℝ) : ℂ) ^ s := by
      congr 1
      rw [← Complex.ofReal_div]

lemma vonMangoldt_term_cpow_eq_exp (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : n ≠ 0) (s : ℂ) :
    LSeries.term vonMangoldtC s n * (x : ℂ) ^ s / s =
      vonMangoldtC n * Complex.exp (s * perronLog x n) / s := by
  have hs : ((x / (n : ℝ)) : ℝ) > 0 := div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  calc
    LSeries.term vonMangoldtC s n * (x : ℂ) ^ s / s
        = (vonMangoldtC n / (n : ℂ) ^ s) * (x : ℂ) ^ s / s := by
          rw [LSeries.term_of_ne_zero hn]
    _ = vonMangoldtC n * (((x : ℂ) ^ s / ((n : ℂ) ^ s))) / s := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
    _ = vonMangoldtC n * (((x : ℂ) ^ s / (((n : ℝ) : ℂ) ^ s))) / s := by rfl
    _ = vonMangoldtC n * ((((x / (n : ℝ)) : ℝ) : ℂ) ^ s) / s := by
          congr 2
          rw [div_cpow_ofReal_div x (n : ℝ) hx.le (by positivity) s]
    _ = vonMangoldtC n * Complex.exp (s * perronLog x n) / s := by
          rw [exp_cpow_ofReal_pos (x / (n : ℝ)) hs]
          rfl

lemma norm_exp_perronLog (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : n ≠ 0) (σ : ℝ) (t : ℝ) :
    ‖Complex.exp (sigmaLine σ t * perronLog x n)‖ = (x / (n : ℝ)) ^ σ := by
  rw [Complex.norm_exp]
  have hL := perronLog_ofReal_div x hx n hn
  have hxdiv : 0 < x / (n : ℝ) := div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  rw [hL]
  have hre : (sigmaLine σ t * ((Real.log (x / (n : ℝ))) : ℂ)).re =
      σ * Real.log (x / (n : ℝ)) := by
    rw [Complex.mul_re, sigmaLine_re, sigmaLine_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre]
  rw [Real.rpow_def_of_pos hxdiv]
  congr 1
  ring

lemma perronSummand_norm_le (x σ : ℝ) (hx : 0 < x) (hσ1 : 1 < σ) (a : ℂ) (n : ℕ)
    (hn : n ≠ 0) (t : ℝ) :
    ‖a * Complex.exp (sigmaLine σ t * perronLog x n) / sigmaLine σ t‖ ≤
      ‖a‖ * ((x / (n : ℝ)) ^ σ) / σ := by
  have hσ : 0 < σ := by linarith
  have hnorm : ‖a * Complex.exp (sigmaLine σ t * perronLog x n) / sigmaLine σ t‖
      = ‖a‖ * ((x / (n : ℝ)) ^ σ) / ‖sigmaLine σ t‖ := by
    rw [norm_div, norm_mul, norm_exp_perronLog x hx n hn σ t]
  rw [hnorm]
  have hle : ‖sigmaLine σ t‖⁻¹ ≤ σ⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le hσ (sigmaLine_norm_ge σ hσ t))
  calc
    ‖a‖ * ((x / (n : ℝ)) ^ σ) / ‖sigmaLine σ t‖
        = ‖a‖ * ((x / (n : ℝ)) ^ σ) * ‖sigmaLine σ t‖⁻¹ := by ring
    _ ≤ ‖a‖ * ((x / (n : ℝ)) ^ σ) * σ⁻¹ := by
          gcongr
    _ = ‖a‖ * ((x / (n : ℝ)) ^ σ) / σ := by ring

lemma perronSummand_continuous (a l : ℂ) {sL : ℝ → ℂ} (hs : Continuous sL)
    (hz : ∀ t : ℝ, sL t ≠ 0) :
    Continuous (fun t : ℝ => a * Complex.exp (sL t * l) / sL t) := by
  have hlin : Continuous (fun t : ℝ => sL t * l) := Continuous.mul hs continuous_const
  have hExp : Continuous (fun t : ℝ => Complex.exp (sL t * l)) :=
    Complex.continuous_exp.comp hlin
  have hnum : Continuous (fun t : ℝ => a * Complex.exp (sL t * l)) :=
    Continuous.mul continuous_const hExp
  exact Continuous.div₀ hnum hs hz

theorem mangoldt_perron_sum_eq (x : ℝ) (hx : 0 < x) (σ T : ℝ) (hσ : 1 < σ) :
    (1 / (2 * Real.pi)) *
        (∫ (t : ℝ) in -T..T,
          (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
              (((σ : ℂ) + Complex.I * (t : ℂ)))) *
            (x : ℂ) ^ (((σ : ℂ) + Complex.I * (t : ℂ))) /
            (((σ : ℂ) + Complex.I * (t : ℂ))))
      = ∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (1 / (2 * Real.pi)) *
            (∫ (t : ℝ) in -T..T,
              Complex.exp ((((σ : ℂ) + Complex.I * (t : ℂ))) *
                (Complex.log (((x / (n : ℝ) : ℝ) : ℂ)))) /
              (((σ : ℂ) + Complex.I * (t : ℂ)))) := by
  let v : ℕ → ℂ := fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
  let c : ℂ := 1 / (2 * (Real.pi : ℂ))
  let s : ℝ → ℂ := fun t => sigmaLine σ t
  change c * (∫ t in -T..T,
        (LSeries v (s t)) * (x : ℂ) ^ (s t) / (s t))
      = ∑' n : ℕ, v n * c * (∫ t in -T..T,
          Complex.exp (s t * (Complex.log (((x / (n : ℝ)) : ℝ) : ℂ))) / (s t))
  have hv : v = vonMangoldtC := by
    ext n
    rfl
  have hσ0 : 0 < σ := by linarith
  have hσn0 : σ ≠ 0 := ne_of_gt hσ0
  have hscont : Continuous s := by
    simpa [s] using (sigmaLine_continuous σ)
  have hsnz : ∀ t : ℝ, s t ≠ 0 := by
    intro t
    simpa [s] using (sigmaLine_ne_zero σ hσn0 t)
  have hσge : ∀ t : ℝ, σ ≤ ‖s t‖ := by
    intro t
    simpa [s] using (sigmaLine_norm_ge σ hσ0 t)
  let logz : ℕ → ℂ := fun n : ℕ => perronLog x n
  let Ffun : ℕ → ℝ → ℂ := fun n t => (c * v n) * Complex.exp (s t * logz n) / s t
  let f : ℝ → ℂ := fun t => LSeries v (s t) * (x : ℂ) ^ (s t) / s t
  -- per-term identity: Dirichlet-series term = Λ n · exp(s·log(x/n)) / s
  have hper : ∀ (n : ℕ) (hn : n ≠ 0) (t : ℝ),
      LSeries.term v (s t) n * (x : ℂ) ^ (s t) / s t = v n * Complex.exp (s t * logz n) / s t := by
    intro n hn t
    simpa [hv, logz] using (vonMangoldt_term_cpow_eq_exp x hx n hn (s t))
  -- multiply the (absolutely summable) series of terms by the constant x^s / s
  have htsum : ∀ t : ℝ,
      (∑' n : ℕ, LSeries.term v (s t) n * (x : ℂ) ^ (s t) / s t) =
        LSeries v (s t) * (x : ℂ) ^ (s t) / s t := by
    intro t
    calc
      (∑' n : ℕ, LSeries.term v (s t) n * (x : ℂ) ^ (s t) / s t)
          = ∑' n : ℕ, LSeries.term v (s t) n * ((x : ℂ) ^ (s t) / s t) := by
              refine tsum_congr ?_
              intro n
              rw [div_eq_mul_inv, div_eq_mul_inv]
              ring
      _ = (∑' n : ℕ, LSeries.term v (s t) n) * ((x : ℂ) ^ (s t) / s t) := tsum_mul_right
      _ = (∑' n : ℕ, LSeries.term v (s t) n) * (x : ℂ) ^ (s t) / s t := by
              rw [div_eq_mul_inv]
              ring
      _ = LSeries v (s t) * (x : ℂ) ^ (s t) / s t := by rfl
  -- the per-term sum equals the L-series times x^s / s
  have hmid : ∀ t : ℝ,
      (∑' n : ℕ, v n * Complex.exp (s t * logz n) / s t) =
        LSeries v (s t) * (x : ℂ) ^ (s t) / s t := by
    intro t
    calc
      (∑' n : ℕ, v n * Complex.exp (s t * logz n) / s t)
          = ∑' n : ℕ, LSeries.term v (s t) n * (x : ℂ) ^ (s t) / s t := by
              refine tsum_congr ?_
              intro n
              by_cases hn : n = 0
              · subst n
                simp [v]
              · exact (hper n hn t).symm
      _ = LSeries v (s t) * (x : ℂ) ^ (s t) / s t := htsum t
  -- pointwise equality of the summed integrands (this is exactly the Dirichlet series)
  have hpt : ∀ t : ℝ, (∑' n : ℕ, Ffun n t) = c * f t := by
    intro t
    calc
      (∑' n : ℕ, Ffun n t) = ∑' n : ℕ, c * (v n * Complex.exp (s t * logz n) / s t) := by
          refine tsum_congr ?_
          intro n
          dsimp [Ffun]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
      _ = c * (∑' n : ℕ, v n * Complex.exp (s t * logz n) / s t) := tsum_mul_left
      _ = c * f t := by
          dsimp [f]
          rw [hmid t]
  -- pointwise upper bound of the summands on the whole real line
  have hpt_bound : ∀ (n : ℕ) (t : ℝ), ‖Ffun n t‖ ≤
      ‖c‖ * (ArithmeticFunction.vonMangoldt n : ℝ) * ((x / (n : ℝ)) ^ σ) / σ := by
    intro n t
    by_cases hn : n = 0
    · subst n
      simp [Ffun, v, ArithmeticFunction.map_zero]
    · calc
        ‖Ffun n t‖ ≤ ‖c * v n‖ * ((x / (n : ℝ)) ^ σ) / σ := by
            dsimp [Ffun]
            exact perronSummand_norm_le x σ hx hσ (c * v n) n hn t
        _ = ‖c‖ * (ArithmeticFunction.vonMangoldt n : ℝ) * ((x / (n : ℝ)) ^ σ) / σ := by
            dsimp [v]
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
  -- build continuous maps
  have hFC_cont : ∀ n : ℕ, Continuous (fun t : ℝ => Ffun n t) := by
    intro n
    dsimp [Ffun]
    exact perronSummand_continuous (c * v n) (logz n) hscont hsnz
  let FC : ℕ → C(ℝ, ℂ) := fun n => ContinuousMap.mk (fun t : ℝ => Ffun n t) (hFC_cont n)
  -- bound on the sup-norm over uIcc (-T) T
  let K : TopologicalSpace.Compacts ℝ := ⟨Set.uIcc (-T) T, isCompact_uIcc⟩
  let b : ℕ → ℝ := fun n : ℕ =>
      ‖c‖ * (ArithmeticFunction.vonMangoldt n : ℝ) * ((x / (n : ℝ)) ^ σ) / σ
  have hb_nonneg : ∀ n : ℕ, 0 ≤ b n := by
    intro n
    dsimp [b]
    have h1 : 0 ≤ (x / (n : ℝ)) ^ σ :=
      Real.rpow_nonneg (div_nonneg (le_of_lt hx) (by positivity : 0 ≤ (n : ℝ))) σ
    have hnum : 0 ≤ ‖c‖ * (ArithmeticFunction.vonMangoldt n : ℝ) * ((x / (n : ℝ)) ^ σ) := by
      positivity
    exact div_nonneg hnum (le_of_lt hσ0)
  have hsum_b : Summable b := by
    have hbmul : Summable (fun n : ℕ =>
        (ArithmeticFunction.vonMangoldt n : ℝ) * ((x / (n : ℝ)) ^ σ)) :=
      summable_vonMangoldt_mul_rpow hx hσ
    have hb' : Summable (fun n : ℕ =>
        (‖c‖ / σ) * ((ArithmeticFunction.vonMangoldt n : ℝ) * ((x / (n : ℝ)) ^ σ))) :=
      Summable.mul_left (‖c‖ / σ) hbmul
    exact (summable_congr (fun n => by dsimp [b]; ring)).mpr hb'
  have hsup : ∀ n : ℕ, ‖(FC n).restrict K‖ ≤ b n := by
    intro n
    rw [ContinuousMap.norm_le (f := (FC n).restrict K) (C := b n) (hb_nonneg n)]
    intro y
    change ‖Ffun n (y : ℝ)‖ ≤ b n
    exact hpt_bound n (y : ℝ)
  have hFC_sum : Summable (fun n : ℕ => ‖(FC n).restrict K‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hsup hsum_b
  -- interchange sum and interval integral
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm (f := FC) hFC_sum
  -- termwise: the integral of the summand equals the RHS summand
  have hterm : ∀ n : ℕ,
      (∫ t in -T..T, Ffun n t) =
        v n * c * (∫ t in -T..T, Complex.exp (s t * logz n) / s t) := by
    intro n
    calc
      (∫ t in -T..T, Ffun n t)
          = ∫ t in -T..T, (c * v n) * (Complex.exp (s t * logz n) / s t) := by
              apply congrArg (fun g : ℝ → ℂ => ∫ t in -T..T, g t)
              funext t
              dsimp [Ffun]
              rw [div_eq_mul_inv, div_eq_mul_inv]
              ring
      _ = (c * v n) * (∫ t in -T..T, Complex.exp (s t * logz n) / s t) := by
              rw [intervalIntegral.integral_const_mul]
      _ = v n * c * (∫ t in -T..T, Complex.exp (s t * logz n) / s t) := by ring
  -- assemble everything
  calc
    c * (∫ t in -T..T, f t) = ∫ t in -T..T, c * f t := by
        exact (intervalIntegral.integral_const_mul c f).symm
    _ = ∫ t in -T..T, (∑' n : ℕ, Ffun n t) := by
        apply congrArg (fun g : ℝ → ℂ => ∫ t in -T..T, g t)
        funext t
        exact (hpt t).symm
    _ = ∫ t in -T..T, (∑' n : ℕ, (FC n) t) := by
        apply congrArg (fun g : ℝ → ℂ => ∫ t in -T..T, g t)
        funext t
        refine tsum_congr ?_
        intro n
        rfl
    _ = ∑' n : ℕ, (∫ t in -T..T, (FC n) t) := hswap.symm
    _ = ∑' n : ℕ, (∫ t in -T..T, Ffun n t) := by
        refine tsum_congr ?_
        intro n
        apply congrArg (fun g : ℝ → ℂ => ∫ t in -T..T, g t)
        funext t
        rfl
    _ = ∑' n : ℕ, v n * c * (∫ t in -T..T, Complex.exp (s t * logz n) / s t) := by
        exact tsum_congr hterm

end Commons.NumberTheory.Zeta
