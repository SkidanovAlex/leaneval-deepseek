import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep7.flat_pair_transfer_le
import Submission.Work.Diff.STE.B3.flat_diag_pairing_le
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliaries for `flat_pair_transfer_pairing_le`

This file records the `C^∞`-smoothness and `1`-periodicity of the pair operator
`pairOp k ρ ε T T' a b c d g` for smooth periodic `g`, and the **order-`0` endpoint** of the sharp
pairing estimate,

  `|⟨y, pairOp g⟩| ≤ C ‖y‖_{L²} ‖g‖_{H^{2k-1}}`,

which is the `s = 0` case of `flat_pair_transfer_le` combined with the Fourier representation of the
pairing.  For `k = 1` this endpoint *is* the target estimate
`|⟨y, pairOp g⟩| ≤ C ‖y‖_{H^{k-1}} ‖g‖_{H^k}`.
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3.SymCalcStep7

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Smoothness and periodicity of `pairOp` -/

/-- `pairOp … g` is smooth for smooth periodic `g`. -/
lemma pairOp_contDiff (k : ℕ) (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (T T' : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (ε : ℝ) (a b c d : (ι → ℝ) → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hbp : Work.Diff.STE.Periodic1 b) (hdp : Work.Diff.STE.Periodic1 d)
    {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgp : Work.Diff.STE.Periodic1 g) :
    ContDiff ℝ (⊤ : ℕ∞) (pairOp k ρ ε T T' a b c d g) := by
  have hVsm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) :=
    conjCut_contDiff ρ hρ T T' hT hT' hTper ε hg hgp
  have hVp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) :=
    conjCut_periodic ρ T T' hTper hTinv1 hTinv2 ε g hgp
  have hPsm : ContDiff ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g) :=
    Work.Diff.STE.B3.SymCalcStep6.conjLapPow_contDiff T T' hT hT' hTper hTinv1 hTinv2 k hg hgp
  have hPp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g) :=
    Work.Diff.STE.B3.SymCalcStep6.conjLapPow_periodic T T' hTper k g
  have hSsm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hg hgp
  have hSp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε g
  have hbody : pairOp k ρ ε T T' a b c d g
      = fun x : ι → ℝ => a x * (Work.Diff.STE.B3.SymCalcStep5.lapPow k
        (fun y => b y * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g y) x
      - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
        (fun y => b y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g y) x)
    + c x * (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
        (fun y => d y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε g y) x
      - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
        (fun y => d y * Work.Diff.STE.B3.SymCalcStep5.lapPow k g y) x) := rfl
  rw [hbody]
  exact (ha.mul
      ((Work.Diff.STE.B3.contDiff_lapPow k _ (hb.mul hVsm)
          (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hbp hVp)).sub
        (Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε (hb.mul hPsm)
          (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hbp hPp)))).add
    (hc.mul
      ((Work.Diff.STE.B3.SymCalcStep6.conjLapPow_contDiff T T' hT hT' hTper hTinv1 hTinv2 k
          (hd.mul hSsm) (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hdp hSp)).sub
        (conjCut_contDiff ρ hρ T T' hT hT' hTper ε
          (hd.mul (Work.Diff.STE.B3.contDiff_lapPow k g hg hgp))
          (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hdp
            (Work.Diff.STE.B3.periodic1_lapPow k g)))))

/-- `pairOp … g` is `1`-periodic for `1`-periodic `g`. -/
lemma pairOp_periodic (k : ℕ) (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (T T' : (ι → ℝ) → (ι → ℝ))
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (ε : ℝ) (a b c d : (ι → ℝ) → ℂ)
    (hap : Work.Diff.STE.Periodic1 a) (hbp : Work.Diff.STE.Periodic1 b)
    (hcp : Work.Diff.STE.Periodic1 c) (hdp : Work.Diff.STE.Periodic1 d)
    (g : (ι → ℝ) → ℂ) (hgp : Work.Diff.STE.Periodic1 g) :
    Work.Diff.STE.Periodic1 (pairOp k ρ ε T T' a b c d g) := by
  have hVp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) :=
    conjCut_periodic ρ T T' hTper hTinv1 hTinv2 ε g hgp
  have hPp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g) :=
    Work.Diff.STE.B3.SymCalcStep6.conjLapPow_periodic T T' hTper k g
  have hSp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.flatCut ρ ε g) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε g
  have hbody : pairOp k ρ ε T T' a b c d g
      = fun x : ι → ℝ => a x * (Work.Diff.STE.B3.SymCalcStep5.lapPow k
        (fun y => b y * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g y) x
      - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
        (fun y => b y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' g y) x)
    + c x * (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
        (fun y => d y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε g y) x
      - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
        (fun y => d y * Work.Diff.STE.B3.SymCalcStep5.lapPow k g y) x) := rfl
  rw [hbody]
  exact Work.Diff.STE.B3.SymCalcStep1.Periodic1_add'
    (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hap
      (Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
        (Work.Diff.STE.B3.periodic1_lapPow k _)
        (Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε _)))
    (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hcp
      (Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
        (Work.Diff.STE.B3.SymCalcStep6.conjLapPow_periodic T T' hTper k _)
        (conjCut_periodic ρ T T' hTper hTinv1 hTinv2 ε _
          (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hdp
            (Work.Diff.STE.B3.periodic1_lapPow k g)))))

/-! ## The `L² → H^{-(2k-1)}` endpoint -/

/-- **The `s = 0` endpoint of the sharp pairing estimate.**
`|⟨y, pairOp g⟩| ≤ C ‖y‖_{L²} ‖g‖_{H^{2k-1}}`, uniformly in `ε ∈ (0,1]`. -/
theorem pairOp_pairing_le_zero (k : ℕ) (hk : 1 ≤ k)
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (T T' : (ι → ℝ) → (ι → ℝ))
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (a b c d : (ι → ℝ) → ℂ)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hap : Work.Diff.STE.Periodic1 a) (hbp : Work.Diff.STE.Periodic1 b)
    (hcp : Work.Diff.STE.Periodic1 c) (hdp : Work.Diff.STE.Periodic1 d)
    (hrel : ∀ x : ι → ℝ, a x * b x = c x * d x) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ y g : (ι → ℝ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) y → Work.Diff.STE.Periodic1 y →
        ContDiff ℝ (⊤ : ℕ∞) g → Work.Diff.STE.Periodic1 g →
        |Work.Diff.STE.L2re y (pairOp k ρ ε T T' a b c d g)|
          ≤ K * Real.sqrt (Work.Diff.STE.CSq 0 (Work.Diff.STE.fourierCoeff y))
              * Real.sqrt (Work.Diff.STE.CSq (2 * k - 1) (Work.Diff.STE.fourierCoeff g)) := by
  classical
  obtain ⟨K1, hK1nn, hK1b⟩ :=
    flat_pair_transfer_le k hk 0 ρ hρ hρ0 hρs hρ1 T T' hT hT' hTinv1 hTinv2 hTper
      a b c d ha hb hc hd hap hbp hcp hdp hrel
  have hK1b' : ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ g : (ι → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) g → Work.Diff.STE.Periodic1 g →
      Work.Diff.STE.CSq 0 (Work.Diff.STE.fourierCoeff (pairOp k ρ ε T T' a b c d g))
        ≤ K1 * Work.Diff.STE.CSq (2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
    intro ε hε hε1 g hg hgp
    have h := hK1b ε hε hε1 g hg hgp
    simpa using h
  refine ⟨Real.sqrt K1, Real.sqrt_nonneg _, ?_⟩
  intro ε hε hε1 y g hy hyp hg hgp
  set W : (ι → ℝ) → ℂ := pairOp k ρ ε T T' a b c d g with hW
  have hWsm : ContDiff ℝ (⊤ : ℕ∞) W :=
    pairOp_contDiff k ρ hρ T T' hT hT' hTper hTinv1 hTinv2 ε a b c d ha hb hc hd hbp hdp hg hgp
  have hWp : Work.Diff.STE.Periodic1 W :=
    pairOp_periodic k ρ hρ T T' hTper hTinv1 hTinv2 ε a b c d hap hbp hcp hdp g hgp
  have hdW : Summable (fun m : ι → ℤ => ‖Work.Diff.STE.fourierCoeff W m‖) :=
    Work.Diff.STE.B3.summable_norm_fourierCoeff W hWsm hWp
  have hpar : Work.Diff.STE.L2re y W
      = (∑' m : ι → ℤ,
          Work.Diff.STE.fourierCoeff y m * star (Work.Diff.STE.fourierCoeff W m)).re := by
    have h := L2re_seriesFun_eq y hy hyp (Work.Diff.STE.fourierCoeff W) hdW
    rw [show Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff W) = W from
      funext (Work.Diff.STE.flat.seriesFun_fourierCoeff W hWsm hWp)] at h
    exact h
  set Y : (ι → ℤ) → ℝ := fun m => ‖Work.Diff.STE.fourierCoeff y m‖ with hY
  set Z : (ι → ℤ) → ℝ := fun m => ‖Work.Diff.STE.fourierCoeff W m‖ with hZ
  have hYsum : Summable (fun m : ι → ℤ => Y m ^ 2) := by
    have h := Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff y hy hyp 0
    simpa [hY, Work.Diff.STE.CSq] using h
  have hZsum : Summable (fun m : ι → ℤ => Z m ^ 2) := by
    have h := Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff W hWsm hWp 0
    simpa [hZ, Work.Diff.STE.CSq] using h
  have hYeq : (∑' m : ι → ℤ, Y m ^ 2) = Work.Diff.STE.CSq 0 (Work.Diff.STE.fourierCoeff y) := by
    simp [hY, Work.Diff.STE.CSq]
  have hZeq : (∑' m : ι → ℤ, Z m ^ 2) = Work.Diff.STE.CSq 0 (Work.Diff.STE.fourierCoeff W) := by
    simp [hZ, Work.Diff.STE.CSq]
  have hCS : Work.Diff.STE.CSq 0 (Work.Diff.STE.fourierCoeff W)
      ≤ K1 * Work.Diff.STE.CSq (2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
    rw [hW]; exact hK1b' ε hε hε1 g hg hgp
  have hprod : (∑' m : ι → ℤ, Y m * Z m)
      ≤ Real.sqrt (Work.Diff.STE.CSq 0 (Work.Diff.STE.fourierCoeff y))
        * Real.sqrt (Work.Diff.STE.CSq 0 (Work.Diff.STE.fourierCoeff W)) := by
    rw [← hYeq, ← hZeq]
    exact tsum_mul_le_sqrt_mul_sqrt Y Z (fun m => norm_nonneg _) (fun m => norm_nonneg _)
      hYsum hZsum
  have hYZsum : Summable (fun m : ι → ℤ => Y m * Z m) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun m => by nlinarith [sq_nonneg (Y m - Z m)]) ((hYsum.add hZsum).mul_left (1 / 2))
  have hnormsum : Summable (fun m : ι → ℤ =>
      ‖Work.Diff.STE.fourierCoeff y m * star (Work.Diff.STE.fourierCoeff W m)‖) :=
    hYZsum.congr (fun m => by rw [norm_mul, norm_star])
  refine (le_trans ?_ (le_trans hprod ?_))
  · calc |Work.Diff.STE.L2re y W|
        = |(∑' m : ι → ℤ,
            Work.Diff.STE.fourierCoeff y m * star (Work.Diff.STE.fourierCoeff W m)).re| := by
          rw [hpar]
      _ ≤ ‖∑' m : ι → ℤ,
            Work.Diff.STE.fourierCoeff y m * star (Work.Diff.STE.fourierCoeff W m)‖ :=
          Complex.abs_re_le_norm _
      _ ≤ ∑' m : ι → ℤ,
            ‖Work.Diff.STE.fourierCoeff y m * star (Work.Diff.STE.fourierCoeff W m)‖ :=
          norm_tsum_le_tsum_norm hnormsum
      _ = ∑' m : ι → ℤ, Y m * Z m :=
          tsum_congr (fun m => by rw [norm_mul, norm_star])
  · rw [show Real.sqrt K1 * Real.sqrt (Work.Diff.STE.CSq 0 (Work.Diff.STE.fourierCoeff y))
        * Real.sqrt (Work.Diff.STE.CSq (2 * k - 1) (Work.Diff.STE.fourierCoeff g))
        = Real.sqrt (Work.Diff.STE.CSq 0 (Work.Diff.STE.fourierCoeff y))
          * (Real.sqrt K1 * Real.sqrt (Work.Diff.STE.CSq (2 * k - 1)
              (Work.Diff.STE.fourierCoeff g))) from by ring]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    calc Real.sqrt (Work.Diff.STE.CSq 0 (Work.Diff.STE.fourierCoeff W))
        ≤ Real.sqrt (K1 * Work.Diff.STE.CSq (2 * k - 1) (Work.Diff.STE.fourierCoeff g)) :=
          Real.sqrt_le_sqrt hCS
      _ = Real.sqrt K1 * Real.sqrt (Work.Diff.STE.CSq (2 * k - 1)
            (Work.Diff.STE.fourierCoeff g)) := Real.sqrt_mul hK1nn _


/-! ## Additivity of `pairOp` in its argument, and of `L2re` -/

/-- The Friedrichs cutoff is additive on smooth periodic functions. -/
lemma flatCut_add (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    {u v : (ι → ℝ) → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hup : Work.Diff.STE.Periodic1 u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvp : Work.Diff.STE.Periodic1 v) :
    Work.Diff.STE.B3.SymCalc.flatCut ρ ε (u + v)
      = Work.Diff.STE.B3.SymCalc.flatCut ρ ε u + Work.Diff.STE.B3.SymCalc.flatCut ρ ε v := by
  have h := Work.Diff.STE.B3.SymCalcStep1.flatCut_fintype_sum (ι := ι) ρ hρ ε
    (fun p : Fin 2 => (![u, v] : Fin 2 → (ι → ℝ) → ℂ) p)
    (fun p => by fin_cases p <;> simpa) (fun p => by fin_cases p <;> simpa)
  have h1 : (fun x : ι → ℝ => ∑ p : Fin 2, (![u, v] : Fin 2 → (ι → ℝ) → ℂ) p x)
      = u + v := by
    funext x
    rw [Fin.sum_univ_two]
    rfl
  have h2 : (fun x : ι → ℝ => ∑ p : Fin 2,
        Work.Diff.STE.B3.SymCalc.flatCut ρ ε ((![u, v] : Fin 2 → (ι → ℝ) → ℂ) p) x)
      = Work.Diff.STE.B3.SymCalc.flatCut ρ ε u
        + Work.Diff.STE.B3.SymCalc.flatCut ρ ε v := by
    funext x
    rw [Fin.sum_univ_two]
    rfl
  rw [h1, h2] at h
  exact h

/-- The conjugated cutoff `V = conjCut` is additive on smooth periodic functions. -/
lemma conjCut_add (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (T T' : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (ε : ℝ) {u v : (ι → ℝ) → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hup : Work.Diff.STE.Periodic1 u)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvp : Work.Diff.STE.Periodic1 v) :
    Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' (u + v)
      = Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' u
        + Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' v := by
  have hcu : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T u) := hu.comp hT
  have hcv : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T v) := hv.comp hT
  have hcup : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T u) := by
    intro i x
    show u (T (x + Pi.single i 1)) = u (T x)
    rw [hTper i x]
    exact hup i (T x)
  have hcvp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T v) := by
    intro i x
    show v (T (x + Pi.single i 1)) = v (T x)
    rw [hTper i x]
    exact hvp i (T x)
  have h1 : Work.Diff.STE.B3.SymCalc.compMap T (u + v)
      = Work.Diff.STE.B3.SymCalc.compMap T u + Work.Diff.STE.B3.SymCalc.compMap T v :=
    Work.Diff.STE.B3.SymCalcStep6.compMap_add T u v
  have h2 := flatCut_add ρ hρ ε hcu hcup hcv hcvp
  have h3 : Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' (u + v)
      = Work.Diff.STE.B3.SymCalc.compMap T'
          (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
            (Work.Diff.STE.B3.SymCalc.compMap T u
              + Work.Diff.STE.B3.SymCalc.compMap T v)) := by
    unfold Work.Diff.STE.B3.SymCalc.conjCut
    rw [h1]
  rw [h3, h2]
  show Work.Diff.STE.B3.SymCalc.compMap T'
      (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Work.Diff.STE.B3.SymCalc.compMap T u)
        + Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Work.Diff.STE.B3.SymCalc.compMap T v))
    = Work.Diff.STE.B3.SymCalc.compMap T'
        (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Work.Diff.STE.B3.SymCalc.compMap T u))
      + Work.Diff.STE.B3.SymCalc.compMap T'
        (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Work.Diff.STE.B3.SymCalc.compMap T v))
  exact Work.Diff.STE.B3.SymCalcStep6.compMap_add T' _ _

end Work.Diff.STE.B3.SymCalcStep7
