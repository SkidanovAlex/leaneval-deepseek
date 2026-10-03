import Mathlib
import Submission.Work.A7Hi2.RealScaleDefs
import Submission.Commons.Analysis.Hilbert.eLpNorm_le_liminf_of_le_liminf
import Submission.Work.KMTContract.tendsto_sum_Icc_atTop
import Submission.Port.Aesm

/-!
# Removing the finite-support hypothesis from an `ℓᵖ` square-function bound

The theorem `Work.A7Hi2.sqfn_lp_of_finsupp` extends an `ℓᵖ` bound for the square function

  `S k g n = (∑'_l ‖∑'_y k l y · g (n - y)‖ ^ 2)^{1/2}`

from *finitely supported* inputs `g` to *all* functions `g : ℤ → ℂ` (no a priori `ℓᵖ` membership is
assumed: the right-hand side is `⊤` in the cases where it matters).

The proof is a Fatou/truncation argument, in the following shape.  Write
`truncC K g = g · 1_{[-K,K]}` for the finitely supported truncation of `g`.

* **Pointwise liminf inequality** (`sqfn_le_liminf_truncC`): for every `n`,
  `S k g n ≤ liminf_K S k (truncC K g) n`.
  The inner `tsum` over `y` is not assumed to converge, so this is where the content sits: for the
  finitely many `l` where the family `y ↦ k l y · g (n - y)` is summable, the truncated series is
  the symmetric partial sum over `Icc (n - K) (n + K)` and converges to the full `tsum`
  (`Work.KMTContract.tendsto_sum_Icc_atTop`), hence *equals* its own `liminf`; when the family is
  not summable the `tsum` is `0` and there is nothing to prove.  Passing from the individual `l`
  to the sum over `l` is Fatou's lemma for `∑'` over `ℕ` (`lintegral_liminf_le'` for the counting
  measure), and passing to the exponent `1/2` is the order-isomorphism `ENNReal.orderIsoRpow`.
* **Fatou for `eLpNorm`** (`Commons.Analysis.Hilbert.eLpNorm_le_liminf_of_le_liminf`) turns the
  pointwise inequality into `eLpNorm (S k g) ≤ liminf_K eLpNorm (S k (truncC K g))`.
* Each term of that `liminf` is bounded by `ENNReal.ofReal C · ‖g‖_{ℓᵖ}` using the hypothesis `hfin`
  (applied to `truncC K g`, which is finitely supported) and the pointwise bound
  `‖truncC K g x‖ ≤ ‖g x‖`; the `liminf` of a constant sequence is that constant (and if
  `‖g‖_{ℓᵖ} = ⊤` the right-hand side is `⊤` because `C > 0`).
-/

set_option autoImplicit false

namespace Work.A7Hi2

open MeasureTheory Filter Finset
open scoped ENNReal NNReal BigOperators

/-! ## The truncations `g · 1_{[-K,K]}` -/

/-- The truncation of `g : ℤ → ℂ` to the symmetric interval `[-K,K]`. -/
def truncC (K : ℕ) (g : ℤ → ℂ) : ℤ → ℂ := fun x => if |x| ≤ (K : ℤ) then g x else 0

theorem truncC_apply (K : ℕ) (g : ℤ → ℂ) (x : ℤ) :
    truncC K g x = if |x| ≤ (K : ℤ) then g x else 0 := rfl

theorem truncC_eq_of_le {K : ℕ} {g : ℤ → ℂ} {x : ℤ} (h : |x| ≤ (K : ℤ)) :
    truncC K g x = g x := by
  rw [truncC_apply, if_pos h]

theorem truncC_eq_zero_of_gt {K : ℕ} {g : ℤ → ℂ} {x : ℤ} (h : (K : ℤ) < |x|) :
    truncC K g x = 0 := by
  rw [truncC_apply, if_neg (not_le.mpr h)]

/-- The truncation is finitely supported. -/
theorem truncC_finSupp (K : ℕ) (g : ℤ → ℂ) :
    ∃ t : Finset ℤ, ∀ x : ℤ, x ∉ t → truncC K g x = 0 := by
  refine ⟨Finset.Icc (-(K : ℤ)) (K : ℤ), fun x hx => ?_⟩
  rw [truncC_apply, if_neg]
  intro h
  exact hx (Finset.mem_Icc.mpr (abs_le.mp h))

/-- The truncation does not increase the pointwise norm. -/
theorem norm_truncC_le (K : ℕ) (g : ℤ → ℂ) (x : ℤ) : ‖truncC K g x‖ ≤ ‖g x‖ := by
  rw [truncC_apply]
  split
  · exact le_rfl
  · rw [norm_zero]; exact norm_nonneg _

/-- **The truncated convolution series is the symmetric partial sum over `Icc (n-K) (n+K)`.**
The summand `k y · truncC K g (n - y)` vanishes as soon as `|n - y| > K`. -/
theorem tsum_truncC_eq_sum_Icc (k : ℤ → ℂ) (K : ℕ) (g : ℤ → ℂ) (n : ℤ) :
    (∑' y : ℤ, k y * truncC K g (n - y))
      = ∑ j ∈ Finset.Icc (n - (K : ℤ)) (n + (K : ℤ)), k j * g (n - j) := by
  have hiff : ∀ j : ℤ, |n - j| ≤ (K : ℤ) ↔ j ∈ Finset.Icc (n - (K : ℤ)) (n + (K : ℤ)) := by
    intro j
    rw [Finset.mem_Icc, abs_le]
    omega
  rw [tsum_eq_sum (s := Finset.Icc (n - (K : ℤ)) (n + (K : ℤ))) ?_]
  · exact Finset.sum_congr rfl fun b hb => by rw [truncC_eq_of_le ((hiff b).mpr hb)]
  · intro b hb
    rw [truncC_eq_zero_of_gt (K := K) (g := g) (x := n - b) ?_, mul_zero]
    by_contra h
    exact hb ((hiff b).mp (le_of_not_gt h))

/-! ## Symmetric partial sums of an arbitrary series -/

/-- **The `liminf` of the symmetric partial sums bounds the sum.**  If the family `u : ℤ → ℂ` is
summable this is the statement that the partial sums over the intervals `Icc (n-K) (n+K)` (which
are cofinal among the finite subsets of `ℤ`) converge to the full sum; if it is not summable the
`tsum` is `0` by definition and there is nothing to prove. -/
theorem enorm_tsum_le_liminf_sum_Icc (u : ℤ → ℂ) (n : ℤ) :
    ‖∑' y : ℤ, u y‖ₑ
      ≤ liminf (fun K : ℕ =>
          ‖∑ j ∈ Finset.Icc (n - (K : ℤ)) (n + (K : ℤ)), u j‖ₑ) atTop := by
  by_cases hs : Summable u
  · have hconv := Work.KMTContract.tendsto_sum_Icc_atTop (G := ℂ) hs n
    have h3 : Tendsto (fun K : ℕ =>
        ‖∑ j ∈ Finset.Icc (n - (K : ℤ)) (n + (K : ℤ)), u j‖ₑ) atTop (nhds ‖∑' y : ℤ, u y‖ₑ) :=
      (continuous_enorm.tendsto _).comp hconv
    rw [h3.liminf_eq]
  · rw [tsum_eq_zero_of_not_summable hs]
    simp

/-! ## Two `liminf` bookkeeping lemmas -/

/-- Monotonicity of `liminf` for `ℝ≥0∞`-valued sequences (the general `Filter.liminf_le_liminf`
carries coboundedness side conditions that are awkward here). -/
theorem liminf_le_liminf_ennreal_of_sqfn {u v : ℕ → ℝ≥0∞} (h : ∀ᶠ n in atTop, u n ≤ v n) :
    liminf u atTop ≤ liminf v atTop := by
  rw [Filter.liminf_eq, Filter.liminf_eq]
  refine sSup_le fun a ha => le_sSup ((ha.and h).mono fun n hn => le_trans hn.1 hn.2)

/-- **Fatou's lemma for `∑'` over `ℕ`.**  The `∑'` is the integral against the counting measure
(`MeasureTheory.lintegral_count`), so this is `MeasureTheory.lintegral_liminf_le'`. -/
theorem tsum_liminf_le_liminf_tsum (F : ℕ → ℕ → ℝ≥0∞) :
    (∑' l : ℕ, liminf (fun K : ℕ => F K l) atTop)
      ≤ liminf (fun K : ℕ => ∑' l : ℕ, F K l) atTop := by
  have h := MeasureTheory.lintegral_liminf_le'
    (μ := (MeasureTheory.Measure.count : MeasureTheory.Measure ℕ))
    (u := Filter.atTop) (f := fun K l => F K l)
    (fun K => (measurable_of_countable _).aemeasurable)
  simpa only [MeasureTheory.lintegral_count] using h

/-! ## The pointwise `liminf` inequality -/

/-- **The square function of `g` is bounded by the `liminf` of the square functions of the
truncations `truncC K g`.**  This is the pointwise input of the Fatou argument. -/
theorem sqfn_le_liminf_truncC (k : ℕ → ℤ → ℂ) (g : ℤ → ℂ) (n : ℤ) :
    (∑' l : ℕ, ‖∑' y : ℤ, k l y * g (n - y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ liminf (fun K : ℕ =>
          (∑' l : ℕ, ‖∑' y : ℤ, k l y * truncC K g (n - y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) atTop := by
  -- (1) For a single `l`: the square of the norm of the sum is at most the `liminf` of the
  -- squares of the norms of the truncated sums.
  have hstep1 : ∀ l : ℕ, ‖∑' y : ℤ, k l y * g (n - y)‖ₑ ^ (2 : ℝ)
      ≤ liminf (fun K : ℕ => ‖∑' y : ℤ, k l y * truncC K g (n - y)‖ₑ ^ (2 : ℝ)) atTop := by
    intro l
    have hbase : ‖∑' y : ℤ, k l y * g (n - y)‖ₑ
        ≤ liminf (fun K : ℕ => ‖∑' y : ℤ, k l y * truncC K g (n - y)‖ₑ) atTop := by
      have hEq : (fun K : ℕ => ‖∑' y : ℤ, k l y * truncC K g (n - y)‖ₑ)
          = fun K : ℕ =>
              ‖∑ j ∈ Finset.Icc (n - (K : ℤ)) (n + (K : ℤ)), k l j * g (n - j)‖ₑ :=
        funext fun K => by rw [tsum_truncC_eq_sum_Icc]
      rw [hEq]
      exact enorm_tsum_le_liminf_sum_Icc (fun y : ℤ => k l y * g (n - y)) n
    calc ‖∑' y : ℤ, k l y * g (n - y)‖ₑ ^ (2 : ℝ)
        = ENNReal.orderIsoRpow 2 (by norm_num) (‖∑' y : ℤ, k l y * g (n - y)‖ₑ) := by
          rw [ENNReal.orderIsoRpow_apply]
      _ ≤ ENNReal.orderIsoRpow 2 (by norm_num)
            (liminf (fun K : ℕ => ‖∑' y : ℤ, k l y * truncC K g (n - y)‖ₑ) atTop) :=
          (ENNReal.orderIsoRpow 2 (by norm_num)).monotone hbase
      _ = liminf (fun K : ℕ => ENNReal.orderIsoRpow 2 (by norm_num)
            (‖∑' y : ℤ, k l y * truncC K g (n - y)‖ₑ)) atTop := by
          refine (ENNReal.orderIsoRpow 2 (by norm_num)).liminf_apply ?_ ?_ ?_ ?_
          all_goals isBoundedDefault
      _ = liminf (fun K : ℕ => ‖∑' y : ℤ, k l y * truncC K g (n - y)‖ₑ ^ (2 : ℝ)) atTop := by
          simp only [ENNReal.orderIsoRpow_apply]
  -- (2) Fatou in the sum over `l`.
  have hstep2 : (∑' l : ℕ, ‖∑' y : ℤ, k l y * g (n - y)‖ₑ ^ (2 : ℝ))
      ≤ liminf (fun K : ℕ =>
          ∑' l : ℕ, ‖∑' y : ℤ, k l y * truncC K g (n - y)‖ₑ ^ (2 : ℝ)) atTop :=
    (ENNReal.tsum_le_tsum hstep1).trans
      (tsum_liminf_le_liminf_tsum
        (fun K l => ‖∑' y : ℤ, k l y * truncC K g (n - y)‖ₑ ^ (2 : ℝ)))
  -- (3) The exponent `1/2`.
  calc (∑' l : ℕ, ‖∑' y : ℤ, k l y * g (n - y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      = ENNReal.orderIsoRpow (1 / 2) (by norm_num)
          (∑' l : ℕ, ‖∑' y : ℤ, k l y * g (n - y)‖ₑ ^ (2 : ℝ)) := by
        rw [ENNReal.orderIsoRpow_apply]
    _ ≤ ENNReal.orderIsoRpow (1 / 2) (by norm_num)
          (liminf (fun K : ℕ =>
            ∑' l : ℕ, ‖∑' y : ℤ, k l y * truncC K g (n - y)‖ₑ ^ (2 : ℝ)) atTop) :=
        (ENNReal.orderIsoRpow (1 / 2) (by norm_num)).monotone hstep2
    _ = liminf (fun K : ℕ => ENNReal.orderIsoRpow (1 / 2) (by norm_num)
          (∑' l : ℕ, ‖∑' y : ℤ, k l y * truncC K g (n - y)‖ₑ ^ (2 : ℝ))) atTop := by
        refine (ENNReal.orderIsoRpow (1 / 2) (by norm_num)).liminf_apply ?_ ?_ ?_ ?_
        all_goals isBoundedDefault
    _ = liminf (fun K : ℕ =>
          (∑' l : ℕ, ‖∑' y : ℤ, k l y * truncC K g (n - y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) atTop := by
        simp only [ENNReal.orderIsoRpow_apply]

/-! ## The target -/

theorem sqfn_lp_of_finsupp (p : ℝ) (hp : 0 < p) (k : ℕ → ℤ → ℂ) (C : ℝ) (hC : 0 < C)
    (hfin : ∀ g : ℤ → ℂ, (∃ t : Finset ℤ, ∀ x : ℤ, x ∉ t → g x = 0) →
      MeasureTheory.eLpNorm
          (fun n : ℤ => (∑' l : ℕ, ‖∑' y : ℤ, k l y * g (n - y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
          (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm g (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) :
    ∀ g : ℤ → ℂ,
      MeasureTheory.eLpNorm
          (fun n : ℤ => (∑' l : ℕ, ‖∑' y : ℤ, k l y * g (n - y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
          (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm g (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  intro g
  by_cases htop : MeasureTheory.eLpNorm g (ENNReal.ofReal p)
      (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hC)]
    exact le_top
  -- Fatou for `eLpNorm` along the truncations.
  have hFat := Commons.Analysis.Hilbert.eLpNorm_le_liminf_of_le_liminf
    (fun K n => (∑' l : ℕ, ‖∑' y : ℤ, k l y * truncC K g (n - y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
    (fun n => (∑' l : ℕ, ‖∑' y : ℤ, k l y * g (n - y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
    hp (fun n => sqfn_le_liminf_truncC k g n)
  refine hFat.trans ?_
  -- Each truncated square function satisfies the hypothesis.
  have hK : ∀ K : ℕ, MeasureTheory.eLpNorm (fun n : ℤ =>
        (∑' l : ℕ, ‖∑' y : ℤ, k l y * truncC K g (n - y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
        (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm g (ENNReal.ofReal p)
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
    intro K
    have hmono : MeasureTheory.eLpNorm (truncC K g) (ENNReal.ofReal p)
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ MeasureTheory.eLpNorm g (ENNReal.ofReal p)
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
      MeasureTheory.eLpNorm_mono (hf := by pw_aesm) (fun x => norm_truncC_le K g x)
    exact (hfin (truncC K g) (truncC_finSupp K g)).trans
      (mul_le_mul_right hmono (ENNReal.ofReal C))
  calc liminf (fun K : ℕ => MeasureTheory.eLpNorm (fun n : ℤ =>
        (∑' l : ℕ, ‖∑' y : ℤ, k l y * truncC K g (n - y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
        (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) atTop
      ≤ liminf (fun _ : ℕ => ENNReal.ofReal C *
          MeasureTheory.eLpNorm g (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) atTop :=
        liminf_le_liminf_ennreal_of_sqfn (Eventually.of_forall hK)
    _ = ENNReal.ofReal C * MeasureTheory.eLpNorm g (ENNReal.ofReal p)
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := Filter.liminf_const _

end Work.A7Hi2
