/-
# Area 5 (HB Lemma 13.3) — assembly

From Area 1 (Burgess) we prove the per-character certificate `PerCharCert`:

  `boxAbs q K R χ ≤ K² (B(λ) + η)`  for every non-principal `χ` mod `q` which has no zero of
  `λ` below `lam`, uniformly in `lam ∈ [0,R]`.

The chain, for a test function `f` with `f(0) = 1`, `‖f‖ ≤ 1`, `‖f''‖ ≤ R²` on `(0,K)`,
supported in `[0,K]`, and with Laplace transform `F`:

* (i)  `hH_provider` (Burgess, Area 1) supplies the log-derivative hypothesis of the §5
       smoothing estimate with a threshold independent of the test function;
* (ii) `l52_uniform_imprim` at the single point `s = 1 - λ/log q` gives
       `∑' Λ(n) Re(χ(n)/n^s) f(log n/log q) ≤ -log q · Z + (1/6+ε) log q`,
       `Z` the δ-window zero sum of `F`;
* (iii) `neg_vonMangoldt_le` (termwise comparison with the principal series) and
       `lambert_principal_uniform` / `lambert_principal_zero` (Chebyshev-ψ) give
       `-log q · (that sum) ≤ (F(-λ)).re + C (M+M')/log q` with `‖f‖ ≤ M`, `‖f'‖ ≤ M'`;
* (iv) `boxAbs_le_deltaSum` converts `boxAbs` into `c⁻¹ Z` using the (13.2) domination
       `c ‖F₂(λ+z)‖ ≤ Re F(z)`, so that `boxAbs ≤ c⁻¹((1/6+ε) + F(-λ) + C(M+M')/log q)`.

The two instantiations are `f = wc K lam = sinh((K-t)λ)/sinh(Kλ)` (cut off at `t = 0`) with
`c = (λ/2)e^{Kλ}/sinh(Kλ)` for `λ > 0`, and the `λ → 0` limit `f = gc K = (K-t)/K` with
`c = 1/(2K)`.  The normalisation `f(0) = 1` is what makes the constants uniform in `λ`.
-/
import Mathlib
import Submission.Work.LinnikContract.Areas
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg
import Submission.Work.LinnikAreas.A5.Basic
import Submission.Work.LinnikAreas.A5.Weights
import Submission.Work.LinnikAreas.A5.f1_data
import Submission.Work.LinnikAreas.A5.g0_data
import Submission.Work.LinnikAreas.A5.Bfun_facts
import Submission.Work.LinnikAreas.A5.F1_neg_lam
import Submission.Work.LinnikAreas.A5.G0_closed
import Submission.Work.LinnikAreas.A5.HProviderFree
import Submission.Work.LinnikAreas.A5.l52_uniform_imprim
import Submission.Work.LinnikAreas.A5.boxAbs_le_deltaSum
import Submission.Work.LinnikAreas.A5.lambert_principal_uniform
import Submission.Work.LinnikAreas.A5.lambert_principal_zero
import Submission.Work.LinnikAreas.A5.lt_weights
import Submission.Work.LinnikAreas.A5.lt_neg_integral
import Submission.Work.LinnikAreas.A5.neg_vonMangoldt_le
import Submission.Work.LinnikAreas.A5.testfun_arith
import Submission.Work.LinnikAreas.A5.gc_data
import Submission.Work.LinnikAreas.A5.wc_data

open Complex DirichletCharacter Metric Filter Set
open scoped Real Topology BigOperators Interval

set_option maxHeartbeats 4000000

noncomputable section

namespace Work.LinnikAreas.A5

open Work.LinnikContract

/-- The zero sum of the §5 estimate, in the shape produced by `boxAbs_le_deltaSum`: the divisor
sum over the δ-window around `1` with the Laplace transform `F` of the weight `f`. -/
private def Zwin (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    (K δ lam : ℝ) (F : ℂ → ℂ) : ℝ :=
  ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 2)) u : ℝ) *
    (if ‖(1 : ℂ) - u‖ ≤ δ then
      (F (((((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ) - u) * (((Real.log (q : ℝ)) : ℝ) : ℂ))).re
     else 0)

/-- Rewriting the zero sum of the §5 estimate (an integral over `(0,K)` of the weight against
`e^{-zt}`) into the form `Zwin` used by `boxAbs_le_deltaSum`, using that `F` is the Laplace
transform of `f`.  The point `s` of the §5 statement is `1 - lam/log q`, hence is real. -/
private theorem zeroSum_congr {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] {K δ lam : ℝ} {f : ℝ → ℝ} {F : ℂ → ℂ}
    (hFT : ∀ z : ℂ, (∫ t in (0 : ℝ)..K, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)) = F z) :
    (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|(((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ).im| + 2))) u : ℤ) *
        (if ‖(1 : ℂ) + (((((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ then
          ((∫ t in (0 : ℝ)..K, Complex.exp
              (-(((((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ) - u) *
                  (((Real.log (q : ℝ)) : ℝ) : ℂ) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
         else 0)) =
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 2)) u : ℝ) *
        (if ‖(1 : ℂ) - u‖ ≤ δ then
          (F (((((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ) - u) * (((Real.log (q : ℝ)) : ℝ) : ℂ))).re
         else 0)) := by
  apply finsum_congr
  intro u
  have him : ((((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ)).im = 0 := Complex.ofReal_im _
  have hball : Metric.closedBall (0 : ℂ)
      (|((((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ)).im| + 2) = Metric.closedBall (0 : ℂ) 2 := by
    rw [him]; norm_num
  rw [hball]
  have hwin : ‖(1 : ℂ) + (((((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ)).im : ℂ) * Complex.I - u‖
      = ‖(1 : ℂ) - u‖ := by
    rw [him]; simp
  by_cases hw : ‖(1 : ℂ) + (((((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ
  · rw [if_pos hw, if_pos (by rwa [hwin] at hw), hFT]
  · rw [if_neg hw, if_neg (by rwa [hwin] at hw)]

/-- The bookkeeping core of HB Lemma 13.3: from the §5 estimate at `s = 1 - λ/log q` and the
Chebyshev-ψ bound for the same weight `f`, deduce the box-sum bound
`boxAbs ≤ c⁻¹((1/6+ε) + F(-λ) + C(M+M')/log q)`. -/
private theorem boxSum_core {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    (hχ : χ ≠ 1) {K R lam δ c C M M' ε : ℝ} {f : ℝ → ℝ} {F : ℂ → ℂ}
    (hK : 0 < K) (hR : 0 < R) (hL : 0 < Real.log (q : ℝ))
    (hσ : 0 < 1 - lam / Real.log (q : ℝ))
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδge : 2 * R ≤ δ * Real.log (q : ℝ)) (hc : 0 < c)
    (hF : ∀ z : ℂ, 0 ≤ z.re → c * ‖F2 K ((lam : ℂ) + z)‖ ≤ (F z).re)
    (hZ : ∀ ρ : ℂ, IsZ χ ρ → lam ≤ lamOf q ρ)
    (hsupp : ∀ t : ℝ, K ≤ t → f t = 0) (hfnn : ∀ t : ℝ, 0 ≤ f t) (hf0 : f 0 = 1)
    (hFT : ∀ z : ℂ, (∫ t in (0 : ℝ)..K, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)) = F z)
    (hFneg : (F (-(lam : ℂ))).re = ∫ u in (0 : ℝ)..K, Real.exp (lam * u) * f u)
    (h5 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ (n : ZMod q) / (n : ℂ) ^ (((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ)).re) *
            f (Real.log n / Real.log (q : ℝ)))
        ≤ -(Real.log (q : ℝ)) * (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
              (completedLFunction χ.primitiveCharacter)
              (Metric.closedBall 0 (|(((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ).im| + 2))) u : ℤ) *
            (if ‖(1 : ℂ) + (((((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ
             then ((∫ t in (0 : ℝ)..K, Complex.exp
                    (-(((((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ) - u) *
                        (((Real.log (q : ℝ)) : ℝ) : ℂ) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
             else 0))
          + f 0 * ((1 / 6 : ℝ) + ε) * Real.log (q : ℝ))
    (hLam : (Real.log (q : ℝ))⁻¹ * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
              (n : ℝ) ^ (-(1 - lam / Real.log (q : ℝ))) * f (Real.log n / Real.log (q : ℝ)))
        ≤ (∫ u in (0 : ℝ)..K, Real.exp (lam * u) * f u) + C * (M + M') / Real.log (q : ℝ)) :
    boxAbs q K R χ ≤ c⁻¹ * ((1 / 6 + ε) + (F (-(lam : ℂ))).re
      + C * (M + M') / Real.log (q : ℝ)) := by
  have hbox : boxAbs q K R χ ≤ c⁻¹ * Zwin q χ K δ lam F := by
    rw [Zwin]
    exact boxAbs_le_deltaSum (F := F) χ hχ hK hR hL hδ0 hδ1 hδge hc hF hZ
  -- the §5 estimate, rewritten with `Zwin`
  have hS5 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ (n : ZMod q) / (n : ℂ) ^ (((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ)).re) *
        f (Real.log n / Real.log (q : ℝ)))
      ≤ -(Real.log (q : ℝ)) * Zwin q χ K δ lam F
        + (1 / 6 + ε) * Real.log (q : ℝ) := by
    have h := h5
    rw [zeroSum_congr χ hFT, hf0] at h
    simp only [one_mul] at h
    rw [Zwin]
    exact h
  -- the principal (untwisted) von Mangoldt sum
  have hneg : -(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ (n : ZMod q) / (n : ℂ) ^ (((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ)).re) *
        f (Real.log n / Real.log (q : ℝ)))
      ≤ ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        (n : ℝ) ^ (-(1 - lam / Real.log (q : ℝ))) * f (Real.log n / Real.log (q : ℝ)) :=
    neg_vonMangoldt_le χ hL hσ hsupp hfnn
  have hLamB : -((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ (n : ZMod q) / (n : ℂ) ^ (((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ)).re) *
        f (Real.log n / Real.log (q : ℝ))) / Real.log (q : ℝ))
      ≤ (F (-(lam : ℂ))).re + C * (M + M') / Real.log (q : ℝ) := by
    have h1 : -(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ (n : ZMod q) / (n : ℂ) ^ (((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ)).re) *
          f (Real.log n / Real.log (q : ℝ))) / Real.log (q : ℝ)
        ≤ (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          (n : ℝ) ^ (-(1 - lam / Real.log (q : ℝ))) * f (Real.log n / Real.log (q : ℝ)))
          / Real.log (q : ℝ) :=
      div_le_div_of_nonneg_right hneg hL.le
    rw [neg_div] at h1
    have h2 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          (n : ℝ) ^ (-(1 - lam / Real.log (q : ℝ))) * f (Real.log n / Real.log (q : ℝ)))
          / Real.log (q : ℝ)
        ≤ (F (-(lam : ℂ))).re + C * (M + M') / Real.log (q : ℝ) := by
      have h := hLam
      rw [← hFneg] at h
      calc (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            (n : ℝ) ^ (-(1 - lam / Real.log (q : ℝ))) * f (Real.log n / Real.log (q : ℝ)))
            / Real.log (q : ℝ)
          = (Real.log (q : ℝ))⁻¹ * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
              (n : ℝ) ^ (-(1 - lam / Real.log (q : ℝ))) * f (Real.log n / Real.log (q : ℝ))) := by
            rw [div_eq_inv_mul]
        _ ≤ _ := h
    linarith [h1, h2]
  have hZcle : Zwin q χ K δ lam F ≤ (1 / 6 + ε) - ((∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n : ℝ) *
        ((χ (n : ZMod q) / (n : ℂ) ^ (((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ)).re) *
        f (Real.log n / Real.log (q : ℝ))) / Real.log (q : ℝ)) := by
    have h1 : ((1 / 6 + ε) - ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ (n : ZMod q) / (n : ℂ) ^ (((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ)).re) *
          f (Real.log n / Real.log (q : ℝ))) / Real.log (q : ℝ))) * Real.log (q : ℝ)
        = (1 / 6 + ε) * Real.log (q : ℝ) - (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ (n : ZMod q) / (n : ℂ) ^ (((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ)).re) *
          f (Real.log n / Real.log (q : ℝ))) := by
      rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hL)]
    have h2 : Zwin q χ K δ lam F * Real.log (q : ℝ) ≤
        ((1 / 6 + ε) - ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((χ (n : ZMod q) / (n : ℂ) ^ (((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ)).re) *
          f (Real.log n / Real.log (q : ℝ))) / Real.log (q : ℝ))) * Real.log (q : ℝ) := by
      rw [h1]
      linarith [hS5]
    exact le_of_mul_le_mul_right h2 hL
  have hZcle' : Zwin q χ K δ lam F ≤ (1 / 6 + ε) +
      ((F (-(lam : ℂ))).re + C * (M + M') / Real.log (q : ℝ)) := by
    linarith [hZcle, hLamB]
  calc boxAbs q K R χ ≤ c⁻¹ * Zwin q χ K δ lam F := hbox
    _ ≤ c⁻¹ * ((1 / 6 + ε) + ((F (-(lam : ℂ))).re + C * (M + M') / Real.log (q : ℝ))) :=
        mul_le_mul_of_nonneg_left hZcle' (inv_nonneg.mpr hc.le)
    _ = c⁻¹ * ((1 / 6 + ε) + (F (-(lam : ℂ))).re + C * (M + M') / Real.log (q : ℝ)) := by ring


/-! ## The main theorem: `Area1 → PerCharCert` -/

/-- **AREA 5** from Area 1 (Burgess): the per-character certificate of HB Lemma 13.3, uniform in
`λ ∈ [0,R]`. -/
theorem perCharCert_of_LBound13 (h13 : Work.LinnikContract.LBound13) :
    Work.LinnikContract.PerCharCert := by
  intro K hK0 hK1 R hR η hη
  -- (i) the §5 log-derivative hypothesis, uniform in the test function
  obtain ⟨q₀H, δ, hδ0, hδ1, hHmain⟩ :=
    hH_provider_free (φ := 1/3) (by norm_num) (by norm_num) (ε := K * η / 16) (by positivity) h13
  -- (ii) the §5 smoothing estimate at the scale `log q`
  obtain ⟨q₀5, h5main⟩ :=
    l52_uniform_imprim K (R ^ 2) hK0 (by positivity) (ε := K * η / 4) (δ := δ)
      (by positivity) hδ0 hδ1
  -- (iii) the two Chebyshev-ψ inputs
  obtain ⟨C₁, hC₁pos, q₀C₁, hC₁⟩ := lambert_principal_uniform K R hK0 hR
  obtain ⟨C₀, hC₀pos, q₀C₀, hC₀⟩ := lambert_principal_zero K R hK0 hR
  set Cε : ℝ := max C₁ C₀ with hCεdef
  have hCεpos : 0 < Cε := by rw [hCεdef]; exact lt_of_lt_of_le hC₁pos (le_max_left _ _)
  have hC₁le : C₁ ≤ Cε := by rw [hCεdef]; exact le_max_left _ _
  have hC₀le : C₀ ≤ Cε := by rw [hCεdef]; exact le_max_right _ _
  set Lneed : ℝ := max 2 (max (2 * R / δ) (max (Real.exp (R ^ 2))
      (4 * Cε * (1 + R + 1 / K) / (K * η)))) with hLneeddef
  refine ⟨q₀H + q₀5 + q₀C₁ + q₀C₀ + ⌈Real.exp Lneed⌉₊ + 7, ?_⟩
  intro q hq hne
  letI : NeZero q := hne
  intro χ hχ lam hlam0 hlamR hZ
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hqH : q₀H ≤ q := by omega
  have hq5 : q₀5 ≤ q := by omega
  have hqC₁ : q₀C₁ ≤ q := by omega
  have hqC₀ : q₀C₀ ≤ q := by omega
  have hq1 : 1 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hL0 : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hexp_le : Real.exp Lneed ≤ (q : ℝ) := by
    have h1 : Real.exp Lneed ≤ (⌈Real.exp Lneed⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp Lneed⌉₊ : ℕ) : ℝ) ≤ (q : ℝ) := by
      have h3 : ⌈Real.exp Lneed⌉₊ ≤ q := by omega
      exact_mod_cast h3
    linarith
  have hLneed_le : Lneed ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp Lneed]
    exact Real.log_le_log (Real.exp_pos Lneed) hexp_le
  have hL2 : 2 ≤ Real.log (q : ℝ) := le_trans (le_max_left _ _) hLneed_le
  have hlogLpos : 0 < Real.log (Real.log (q : ℝ)) := Real.log_pos (by linarith)
  have hLR2 : R ^ 2 ≤ Real.log (Real.log (q : ℝ)) := by
    have h1 : Real.exp (R ^ 2) ≤ Lneed := by
      rw [hLneeddef]
      exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    have h2 : Real.exp (R ^ 2) ≤ Real.log (q : ℝ) := le_trans h1 hLneed_le
    calc R ^ 2 = Real.log (Real.exp (R ^ 2)) := (Real.log_exp _).symm
      _ ≤ Real.log (Real.log (q : ℝ)) := Real.log_le_log (Real.exp_pos _) h2
  have hsqrtR : R ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
    rw [Real.le_sqrt hR.le (by linarith)]
    exact hLR2
  have hδge : 2 * R ≤ δ * Real.log (q : ℝ) := by
    have h1 : 2 * R / δ ≤ Lneed := by
      rw [hLneeddef]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have h2 : 2 * R / δ ≤ Real.log (q : ℝ) := le_trans h1 hLneed_le
    rw [div_le_iff₀ hδ0] at h2
    linarith
  have hR2L : 2 * R ≤ Real.log (q : ℝ) := by
    have h2 := mul_le_mul_of_nonneg_right hδ1.le hL0.le
    linarith
  have hLC : 4 * Cε * (1 + R + 1 / K) / (K * η) ≤ Real.log (q : ℝ) := by
    have h1 : 4 * Cε * (1 + R + 1 / K) / (K * η) ≤ Lneed := by
      rw [hLneeddef]
      exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
    exact le_trans h1 hLneed_le
  -- the §5 log-derivative hypothesis at `(1/6 + (Kη/4)/4) log q`
  have hHhyp : ∀ s : ℂ,
      1 + 1 / (Real.log (q : ℝ) * Real.log (Real.log (q : ℝ))) ≤ s.re →
      s.re ≤ 1 + Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) →
      |s.im| ≤ 10 * Real.log (q : ℝ) →
      (-logDeriv (LFunction χ.primitiveCharacter) s).re
        + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor
              (completedLFunction χ.primitiveCharacter)
              (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
            (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1 / (s - u)).re) else 0))
        ≤ ((1 / 6 : ℝ) + (K * η / 4) / 4) * Real.log (q : ℝ) := by
    intro s hs1 hs2 hs3
    have h := hHmain (q := q) hqH χ hχ s hs1 hs2 hs3
    convert h using 1
    ring
  -- the point `s = 1 - lam/log q` lies in the range of the §5 conclusion
  have hs1 : |(((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ).re - 1| ≤
      Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    have hx : (((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ).re - 1
        = -(lam / Real.log (q : ℝ)) := by
      rw [Complex.ofReal_re]; ring
    rw [hx, abs_neg, abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_right (le_trans hlamR hsqrtR) hL0.le
  have hs2 : |(((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ).im| ≤ 10 * Real.log (q : ℝ) := by
    rw [Complex.ofReal_im, abs_zero]; positivity
  have hs3 : 1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤
      (1 - lam / Real.log (q : ℝ) : ℝ) := by
    have h := div_le_div_of_nonneg_right (le_trans hlamR hsqrtR) hL0.le
    linarith
  rcases eq_or_ne lam 0 with hz | hpos
  · -- ### the endpoint case `lam = 0`: the weight `gc K`
    obtain ⟨hgc0, hgccont, hgcsupp, hgccd, hgc2, hgcbnd, hgcder, hgcpos⟩ :=
      gc_data K R hK0 (by positivity)
    have hcpos : 0 < 1 / (2 * K) := by positivity
    have hFh : ∀ z : ℂ, 0 ≤ z.re → (1 / (2 * K)) * ‖F2 K ((lam : ℂ) + z)‖ ≤ (G0 K z).re := by
      intro z hz'
      have h := (g0_data K hK0).2.2.2.2.2.2 z hz'
      have h2 : (2 * (K : ℂ) * G0 K z).re = 2 * K * (G0 K z).re := by
        rw [show (2 : ℂ) * (K : ℂ) = ((2 * K : ℝ) : ℂ) by push_cast; ring]
        simp [Complex.mul_re]
      rw [h2] at h
      rw [hz, Complex.ofReal_zero, zero_add]
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)]
      linarith
    have hZ0 : ∀ ρ : ℂ, IsZ χ ρ → lam ≤ lamOf q ρ := by
      intro ρ hρ
      rw [hz]
      exact Work.LinnikContract.API.isZ_lambda_nonneg hq2 hρ
    have hσpos : 0 < 1 - lam / Real.log (q : ℝ) := by
      rw [hz, zero_div, sub_zero]; norm_num
    have hgcint : (∫ u in (0 : ℝ)..K, gc K u) = (G0 K 0).re :=
      (lt_neg_integral K 1 hK0 one_pos).2
    have hFneg : (G0 K (-(lam : ℂ))).re
        = ∫ u in (0 : ℝ)..K, Real.exp (lam * u) * gc K u := by
      rw [hz, Complex.ofReal_zero, neg_zero]
      simp only [zero_mul, Real.exp_zero, one_mul]
      exact hgcint.symm
    have h5 := h5main hq5 (f := gc K) hgccont hgcsupp hgccd hgc2 hgc0
      (fun t _ => hgcbnd t) χ hχ hHhyp (((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ) hs1 hs2 hs3
    have hLam := hC₀ hqC₀ (f := gc K) (M := 1) (M' := 1 / K) (by norm_num) (by positivity)
      hgccont hgcsupp (hgccd.of_le (by norm_num)) (fun t => hgcbnd t) hgcder lam hlam0 hlamR
    have hcore := boxSum_core χ hχ hK0 hR hL0 hσpos hδ0 hδ1 hδge hcpos hFh hZ0
      hgcsupp hgcpos hgc0 (fun z => (lt_weights K 1 hK0 one_pos).2 z) hFneg h5 hLam
    have hG00 : (G0 K (0 : ℂ)).re = K / 2 := by
      rw [(G0_closed K hK0).2]; simp
    have hkey0 : (1 / (2 * K))⁻¹ * (1 / 6 + (G0 K (-(lam : ℂ))).re) = K ^ 2 * Bfun K lam := by
      rw [hz, Complex.ofReal_zero, neg_zero, hG00, (Bfun_facts K hK0).2.1]
      field_simp
      ring
    have hmain0 : (1 / (2 * K))⁻¹ *
        ((1 / 6 + K * η / 4) + (G0 K (-(lam : ℂ))).re + C₀ * (1 + 1 / K) / Real.log (q : ℝ))
        ≤ K ^ 2 * (Bfun K lam + η) := by
      have hcinv0 : (1 / (2 * K))⁻¹ = 2 * K := by field_simp
      have herr1 : (1 / (2 * K))⁻¹ * (K * η / 4) ≤ K ^ 2 * η / 2 := by
        rw [hcinv0]; nlinarith [hK0, hη]
      have herr2 : (1 / (2 * K))⁻¹ * (C₀ * (1 + 1 / K) / Real.log (q : ℝ)) ≤ K ^ 2 * η / 2 := by
        rw [hcinv0]
        have hreq : 2 * K * (C₀ * (1 + 1 / K) / Real.log (q : ℝ))
            = (2 * K * C₀ * (1 + 1 / K)) / Real.log (q : ℝ) := by ring
        rw [hreq, div_le_iff₀ hL0]
        have hstep : (K ^ 2 * η / 2) * (4 * Cε * (1 + R + 1 / K) / (K * η))
            ≤ (K ^ 2 * η / 2) * Real.log (q : ℝ) :=
          mul_le_mul_of_nonneg_left hLC (by positivity)
        have heq : (K ^ 2 * η / 2) * (4 * Cε * (1 + R + 1 / K) / (K * η))
            = 2 * K * Cε * (1 + R + 1 / K) := by
          field_simp
          ring
        have hC0le : 2 * K * C₀ * (1 + 1 / K) ≤ 2 * K * Cε * (1 + R + 1 / K) := by
          have h4 : 2 * K * C₀ * (1 + R + 1 / K) ≤ 2 * K * Cε * (1 + R + 1 / K) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC₀le (by positivity))
              (by positivity)
          have h1 : (1 : ℝ) + 1 / K ≤ 1 + R + 1 / K := by linarith [hR.le]
          have h3 : 2 * K * C₀ * (1 + 1 / K) ≤ 2 * K * C₀ * (1 + R + 1 / K) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
          linarith
        linarith
      have hsplit : (1 / (2 * K))⁻¹ *
          ((1 / 6 + K * η / 4) + (G0 K (-(lam : ℂ))).re + C₀ * (1 + 1 / K) / Real.log (q : ℝ))
          = (1 / (2 * K))⁻¹ * (1 / 6 + (G0 K (-(lam : ℂ))).re)
            + (1 / (2 * K))⁻¹ * (K * η / 4)
            + (1 / (2 * K))⁻¹ * (C₀ * (1 + 1 / K) / Real.log (q : ℝ)) := by ring
      rw [hsplit]
      have hfin : K ^ 2 * Bfun K lam + K ^ 2 * η / 2 + K ^ 2 * η / 2
          ≤ K ^ 2 * (Bfun K lam + η) := by ring_nf; norm_num
      linarith [hkey0, herr1, herr2, hfin]
    calc boxAbs q K R χ ≤ (1 / (2 * K))⁻¹ *
          ((1 / 6 + K * η / 4) + (G0 K (-(lam : ℂ))).re + C₀ * (1 + 1 / K) / Real.log (q : ℝ)) :=
        hcore
      _ ≤ K ^ 2 * (Bfun K lam + η) := hmain0
  · -- ### the case `lam > 0`: the normalised weight `wc K lam`
    have hlam_pos : 0 < lam := lt_of_le_of_ne hlam0 (Ne.symm hpos)
    obtain ⟨hwc0, hwccont, hwcsupp, hwccd, hwc2, hwcbnd, hwcder, hwcpos⟩ :=
      wc_data K lam R hK0 hlam_pos hlamR
    have hcpos : 0 < (lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam) :=
      (testfun_arith K lam hK0 hlam_pos).1
    have hFh : ∀ z : ℂ, 0 ≤ z.re →
        ((lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam)) * ‖F2 K ((lam : ℂ) + z)‖
          ≤ (Ftil K lam z).re := by
      intro z hz'
      have h1 := F1_re_ge hK0 hlam_pos z hz'
      have h2 : (Ftil K lam z).re = (Real.sinh (K * lam))⁻¹ * (F1 K lam z).re := by
        simp only [Ftil, Complex.mul_re, ← Complex.ofReal_inv, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
      rw [h2]
      have h3 : ((lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam)) * ‖F2 K ((lam : ℂ) + z)‖
          = (Real.sinh (K * lam))⁻¹ *
            ((lam / 2) * Real.exp (lam * K) * ‖F2 K ((lam : ℂ) + z)‖) := by
        rw [div_eq_mul_inv]; ring
      rw [h3]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have hσpos : 0 < 1 - lam / Real.log (q : ℝ) := by
      rw [sub_pos, div_lt_one hL0]
      linarith [hR2L, hlamR]
    have h5 := h5main hq5 (f := wc K lam) hwccont hwcsupp hwccd hwc2 hwc0
      (fun t _ => hwcbnd t) χ hχ hHhyp (((1 - lam / Real.log (q : ℝ)) : ℝ) : ℂ) hs1 hs2 hs3
    have hLam := hC₁ hqC₁ (f := wc K lam) (M := 1) (M' := 1 / K + R) (by norm_num)
      (by positivity) hwccont hwcsupp (hwccd.of_le (by norm_num)) (fun t => hwcbnd t) hwcder
      lam hlam_pos hlamR
    have hcore := boxSum_core χ hχ hK0 hR hL0 hσpos hδ0 hδ1 hδge hcpos hFh hZ
      hwcsupp hwcpos hwc0 (fun z => (lt_weights K lam hK0 hlam_pos).1 z)
      (lt_neg_integral K lam hK0 hlam_pos).1.symm h5 hLam
    have hFneg_eq : (Ftil K lam (-(lam : ℂ))).re
        = Real.exp (K * lam) * (K / 2 - (1 - Real.exp (-2 * K * lam)) / (4 * lam))
            / Real.sinh (K * lam) := by
      rw [Ftil, (F1_neg_lam K lam hK0 hlam_pos).1, ← Complex.ofReal_inv]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      ring
    have hkey : ((lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam))⁻¹ *
        (1 / 6 + (Ftil K lam (-(lam : ℂ))).re) = K ^ 2 * Bfun K lam := by
      rw [hFneg_eq]
      exact (testfun_arith K lam hK0 hlam_pos).2.1
    have hcinv : ((lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam))⁻¹ ≤ 2 * K :=
      (testfun_arith K lam hK0 hlam_pos).2.2
    have hmain : ((lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam))⁻¹ *
        ((1 / 6 + K * η / 4) + (Ftil K lam (-(lam : ℂ))).re
          + C₁ * (1 + (1 / K + R)) / Real.log (q : ℝ))
        ≤ K ^ 2 * (Bfun K lam + η) := by
      have herr1 : ((lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam))⁻¹ * (K * η / 4)
          ≤ K ^ 2 * η / 2 := by
        have h1 := mul_le_mul_of_nonneg_right hcinv (by positivity : (0 : ℝ) ≤ K * η / 4)
        nlinarith [h1, hK0, hη]
      have herr2 : ((lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam))⁻¹ *
          (C₁ * (1 + (1 / K + R)) / Real.log (q : ℝ)) ≤ K ^ 2 * η / 2 := by
        have h1 := mul_le_mul_of_nonneg_right hcinv
          (by positivity : (0 : ℝ) ≤ C₁ * (1 + (1 / K + R)) / Real.log (q : ℝ))
        have h2 : 2 * K * (C₁ * (1 + (1 / K + R)) / Real.log (q : ℝ)) ≤ K ^ 2 * η / 2 := by
          have hreq : 2 * K * (C₁ * (1 + (1 / K + R)) / Real.log (q : ℝ))
              = (2 * K * C₁ * (1 + (1 / K + R))) / Real.log (q : ℝ) := by ring
          rw [hreq, div_le_iff₀ hL0]
          have hstep : (K ^ 2 * η / 2) * (4 * Cε * (1 + R + 1 / K) / (K * η))
              ≤ (K ^ 2 * η / 2) * Real.log (q : ℝ) :=
            mul_le_mul_of_nonneg_left hLC (by positivity)
          have heq : (K ^ 2 * η / 2) * (4 * Cε * (1 + R + 1 / K) / (K * η))
              = 2 * K * Cε * (1 + R + 1 / K) := by
            field_simp
            ring
          have hcle : 2 * K * C₁ * (1 + (1 / K + R)) ≤ 2 * K * Cε * (1 + R + 1 / K) := by
            have h1' : (2 * K) * C₁ * (1 + (1 / K + R)) = 2 * K * C₁ * (1 + (1 / K + R)) := by
              ring
            rw [h1']
            have h2' : (1 : ℝ) + (1 / K + R) = 1 + R + 1 / K := by ring
            rw [h2']
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC₁le (by positivity))
              (by positivity)
          linarith
        linarith
      have hsplit : ((lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam))⁻¹ *
          ((1 / 6 + K * η / 4) + (Ftil K lam (-(lam : ℂ))).re
            + C₁ * (1 + (1 / K + R)) / Real.log (q : ℝ))
          = ((lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam))⁻¹ *
              (1 / 6 + (Ftil K lam (-(lam : ℂ))).re)
            + ((lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam))⁻¹ * (K * η / 4)
            + ((lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam))⁻¹ *
              (C₁ * (1 + (1 / K + R)) / Real.log (q : ℝ)) := by ring
      rw [hsplit]
      have hfin : K ^ 2 * Bfun K lam + K ^ 2 * η / 2 + K ^ 2 * η / 2
          ≤ K ^ 2 * (Bfun K lam + η) := by ring_nf; norm_num
      linarith [hkey, herr1, herr2, hfin]
    calc boxAbs q K R χ ≤ ((lam / 2) * Real.exp (lam * K) / Real.sinh (K * lam))⁻¹ *
          ((1 / 6 + K * η / 4) + (Ftil K lam (-(lam : ℂ))).re
            + C₁ * (1 + (1 / K + R)) / Real.log (q : ℝ)) := hcore
      _ ≤ K ^ 2 * (Bfun K lam + η) := hmain

end Work.LinnikAreas.A5
