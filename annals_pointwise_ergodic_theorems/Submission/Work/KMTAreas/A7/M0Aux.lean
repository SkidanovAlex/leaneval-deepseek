/-
# Auxiliary lemmas for the symbol-difference estimate `M0DerivBound` (§6 model approximation)

This module collects the self-contained pieces of the proof of

`Work.KMTAreas.A7.M0DerivBound`,

the estimate of the `(ξ₁,ξ₂)`-derivative `M0deriv` of the symbol difference
`M₀ = weylAvg − mZ·mTilde` of Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional
bilinear polynomial averages*, Ann. of Math. **195** (3) 2022, §6 (Proposition `mod-approx`).

The objects are the ones fixed in `Work.KMTAreas.A7.ModelApproxDefs` /
`Work.KMTAreas.A7.ModelApproxM0Deriv` (with the differentiable weight `Work.A7.m0w` and the
arithmetic character `Work.A7.arithW` of `Submission/Work/A7/`):

* `fiberSum_sub_avg` — the regrouping of the discrete average by the residue classes modulo `q`
  and the comparison with the arithmetic average `mZ` (this is the exact algebraic identity
  `∑_n arithW(n) V(n) - mZ·∫V = ∑_{a<q} arithW(a)(∑_{n≡a}V(n) - q⁻¹∫V)`);
* `mTildeDeriv_eq_half` — the substitution `m̃_{N,ℝ}^{deriv} = N⁻¹ ∫_{N/2}^{N} m0w`;
* `m0deriv_decomp` — the resulting decomposition of `M0deriv` into the `q` fibre errors plus one
  boundary integral of length `≤ 1`.

The estimate itself is then
`‖M0deriv‖ ≤ N⁻¹·(∑_{a<q} ‖fibre error a‖) + N⁻¹·‖mZ‖·B`, and each fibre error is bounded by
`3B + N·B₁` (`Work.KMTAreas.A7.FiberFirstOrder`) with `B = C N^{j₁+dj₂}`,
`B₁ = C(X₁+X₂+1) N^{j₁+dj₂-1}` (`Work.KMTAreas.A7.M0WDerivBound`).
-/
import Mathlib
import Submission.Work.A7.M0WBasic
import Submission.Work.A7.sum_arithW_fiber

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

noncomputable section

namespace M0Aux

open Work.A7 (arithW m0w contDiff_two_m0w mTildeDeriv_eq_integral_m0w
  momPhaseDeriv_eq_arithW_m0w sum_arithW_fiber)

/-- The arithmetic character `arithW P α₁ α₂ n = e(α₁n + α₂P(n))` has modulus one. -/
lemma arithW_norm_eq_one (P : Polynomial ℤ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle)
    (n : ℤ) : ‖arithW P α₁ α₂ n‖ = 1 := by
  rw [Work.A7.arithW, norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe]
  norm_num

/-- The arithmetic symbol `mZ` has modulus at most one, for `q ≥ 1`. -/
lemma mZ_norm_le_one (P : Polynomial ℤ) {q : ℕ} (hq : 1 ≤ q)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) : ‖mZ P q α₁ α₂‖ ≤ 1 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [mZ, norm_mul, norm_inv, Complex.norm_natCast]
  rw [inv_mul_le_iff₀ hq0]
  calc ‖∑ n ∈ Finset.range q,
        fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
      ≤ ∑ n ∈ Finset.range q,
          ‖fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ :=
        norm_sum_le _ _
    _ = ∑ n ∈ Finset.range q, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe]
        norm_num
    _ = (q : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    _ = (q : ℝ) * 1 := by ring

/-- **Regrouping by residue classes and comparison with `mZ`.**  For a `q`-periodic arithmetic
character (`q • α₁ = q • α₂ = 0`) and any `V : ℝ → ℂ`,
`∑_{n∈(K,N]} arithW(n) V(n) − mZ·∫_K^N V = ∑_{a<q} arithW(a)·(∑_{n≡a} V(n) − q⁻¹∫_K^N V)`. -/
lemma fiberSum_sub_avg (P : Polynomial ℤ) {q K N : ℕ} (hq : 0 < q)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (h₁ : q • α₁ = 0) (h₂ : q • α₂ = 0)
    (V : ℝ → ℂ) :
    (∑ n ∈ Finset.Ioc K N, arithW P α₁ α₂ (n : ℤ) * V (n : ℝ))
        - mZ P q α₁ α₂ * ∫ u in (K : ℝ)..(N : ℝ), V u
      = ∑ a ∈ Finset.range q, arithW P α₁ α₂ (a : ℤ) *
          ((∑ n ∈ (Finset.Ioc K N).filter (fun n => n % q = a), V (n : ℝ))
            - (q : ℂ)⁻¹ * ∫ u in (K : ℝ)..(N : ℝ), V u) := by
  rw [sum_arithW_fiber P q α₁ α₂ hq h₁ h₂ K N (fun n => V (n : ℝ))]
  have hmZ : mZ P q α₁ α₂ = (q : ℂ)⁻¹ * ∑ a ∈ Finset.range q, arithW P α₁ α₂ (a : ℤ) := rfl
  rw [hmZ, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  ring

/-- **The substitution for the differentiated oscillatory integral**:
`m̃^{deriv}_{N,ℝ} = ∫_{1/2}^1 m0w(Nt)dt = N⁻¹ ∫_{N/2}^{N} m0w`. -/
lemma mTildeDeriv_eq_half (P : Polynomial ℤ) {N : ℕ} (hN : 0 < N) (ξ₁ ξ₂ : ℝ) (j₁ j₂ : ℕ) :
    mTildeDeriv P N ξ₁ ξ₂ j₁ j₂
      = (N : ℂ)⁻¹ * ∫ u in ((N : ℝ) / 2)..(N : ℝ), m0w P ξ₁ ξ₂ j₁ j₂ u := by
  rw [mTildeDeriv_eq_integral_m0w]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h := intervalIntegral.integral_comp_mul_add (a := (1 / 2 : ℝ)) (b := 1)
    (c := (N : ℝ)) (f := fun u : ℝ => m0w P ξ₁ ξ₂ j₁ j₂ u) (ne_of_gt hNpos) 0
  simp only [add_zero, mul_one] at h
  rw [show (N : ℝ) * (1 / 2) = (N : ℝ) / 2 from by ring] at h
  rw [h, Algebra.smul_def, map_inv₀, map_natCast]

/-- **Decomposition of `M0deriv` into the residue-class fibre errors and one boundary integral.**
With `K = N/2` (integer division) and `ρ = N/2`,
`M0deriv = N⁻¹ ∑_{a<q} arithW(a)(∑_{n∈(K,N], n≡a} V(n) − q⁻¹∫_K^N V) + N⁻¹ mZ ∫_K^ρ V`. -/
lemma m0deriv_decomp (P : Polynomial ℤ) {N q : ℕ} (hN : 0 < N) (hq : 0 < q)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (h₁ : q • α₁ = 0) (h₂ : q • α₂ = 0)
    (ξ₁ ξ₂ : ℝ) (j₁ j₂ : ℕ) :
    M0deriv P N q α₁ α₂ ξ₁ ξ₂ j₁ j₂
      = (N : ℂ)⁻¹ * (∑ a ∈ Finset.range q, arithW P α₁ α₂ (a : ℤ) *
            ((∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => n % q = a),
                m0w P ξ₁ ξ₂ j₁ j₂ (n : ℝ))
              - (q : ℂ)⁻¹ * ∫ u in ((N / 2 : ℕ) : ℝ)..(N : ℝ), m0w P ξ₁ ξ₂ j₁ j₂ u))
        + (N : ℂ)⁻¹ * mZ P q α₁ α₂ *
            ∫ u in ((N / 2 : ℕ) : ℝ)..((N : ℝ) / 2), m0w P ξ₁ ξ₂ j₁ j₂ u := by
  have hcont : Continuous (fun u : ℝ => m0w P ξ₁ ξ₂ j₁ j₂ u) :=
    (contDiff_two_m0w P ξ₁ ξ₂ j₁ j₂).continuous
  have hint1 : IntervalIntegrable (fun u : ℝ => m0w P ξ₁ ξ₂ j₁ j₂ u) volume
      (((N / 2 : ℕ)) : ℝ) ((N : ℝ) / 2) := hcont.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun u : ℝ => m0w P ξ₁ ξ₂ j₁ j₂ u) volume
      ((N : ℝ) / 2) (N : ℝ) := hcont.intervalIntegrable _ _
  have hWρ : (∫ u in ((N : ℝ) / 2)..(N : ℝ), m0w P ξ₁ ξ₂ j₁ j₂ u)
      = (∫ u in ((N / 2 : ℕ) : ℝ)..(N : ℝ), m0w P ξ₁ ξ₂ j₁ j₂ u)
        - ∫ u in ((N / 2 : ℕ) : ℝ)..((N : ℝ) / 2), m0w P ξ₁ ξ₂ j₁ j₂ u := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    rw [← hadd]; ring
  have hsum : (∑ n ∈ Finset.Ioc (N / 2) N, momPhaseDeriv P N α₁ α₂ ξ₁ ξ₂ (n : ℤ) j₁ j₂)
      = ∑ n ∈ Finset.Ioc (N / 2) N, arithW P α₁ α₂ (n : ℤ) * m0w P ξ₁ ξ₂ j₁ j₂ (n : ℝ) :=
    Finset.sum_congr rfl (fun n _ => momPhaseDeriv_eq_arithW_m0w P N α₁ α₂ ξ₁ ξ₂ n j₁ j₂)
  have hfib := fiberSum_sub_avg P (K := N / 2) (N := N) hq α₁ α₂ h₁ h₂
    (fun u : ℝ => m0w P ξ₁ ξ₂ j₁ j₂ u)
  rw [M0deriv, hsum, mTildeDeriv_eq_half P hN ξ₁ ξ₂ j₁ j₂, hWρ]
  rw [← hfib]
  ring

end M0Aux

end

end Work.KMTAreas.A7
