import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB2.DvApriori.DvapInputs
import Submission.Work.BoseFixB2.DvApriori.q1word_onebody_diff_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.dvap_numerator_bound`

The *numerator* bound underlying FS §6 `eq:dvapriori`.  For a low box state `Φ` inside the
particle window `n ≤ 2μℓ³` (`ℓ = fsSide v μ`) the potential words `q₁`, `q₃` and the `T₄`
double-cross sum making up the two off-diagonal bands are all `O(μ²ℓ³‖Φ‖²)`:

`|q₁(g₀,v)| + |q₃| + |T₄| ≤ (13 qcrossC ∫v + 4χ²(g0mass + ∫|v|) + 5 potappC a)·μ²ℓ³·‖Φ‖²`.

The proof is the FS chain:

* `qcross_w_d11` bounds the `wPairC v`/`wPairC v` word `q₁`;
* `q1word_onebody_diff_bound` compares it with the `q₁` carrying `wPairC (g₀ v h)` — only the
  one-body line of `q₁` sees the kernel numerator, the two-body line is literally the same — so
  the triangle inequality gives `|q₁(g₀,v)| ≤ |q₁(v,v)| + |q₁(g₀,v) − q₁(v,v)|`;
* `qcross_w_d13_quarter` and `qcross_w_d2_quarter` bound `q₃` and `T₄`, each at the price of
  `¼ Q₄`;
* the a priori `Q₄` bound `q4word_le_of_low` (FS `eq:Q4apriori`) absorbs the two `¼ Q₄` into
  `5 potappC·a·μ²ℓ³‖Φ‖²`;
* the particle window `hn2 : n ≤ 2μℓ³` gives `n²/ℓ³ ≤ 4μ²ℓ³` and `μn ≤ 2μ²ℓ³`, which converts
  the coefficients `3n²/ℓ³ + μ²ℓ³` and `2μn` into `13μ²ℓ³` and `4μ²ℓ³`.
-/

namespace Work.BoseFixB2.DvApriori

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

theorem dvap_numerator_bound {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} {n : ℕ} {R J : ℝ} {Φ : Submission.BoseGases.X n → ℝ}
    (hℓ : 0 < Work.BoseFixB2.fsSide v μ) (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv1 : MeasureTheory.MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ Work.BoseFixB2.fsSide v μ * Submission.BoseGases.chiR0)
    (hJ : J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3)
    (ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1)
    (hn2 : (n : ℝ) ≤ 2 * μ * (Work.BoseFixB2.fsSide v μ) ^ 3)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦs : Submission.BoseGases.PermInvariant n Φ)
    (hΦn : Φ ≠ 0) (hlow : Work.BoseBoxFix.IsLowB v h J μ n Φ) :
    |Submission.BoseGases.q1word (N := n) (Work.BoseFixB2.fsSide v μ) μ
        (Submission.BoseGases.wPairC (Work.BoseFixB2.fsSide v μ) (Submission.BoseGases.g0 v h))
        (Submission.BoseGases.wPairC (Work.BoseFixB2.fsSide v μ) v) Φ|
      + |Submission.BoseGases.q3word (N := n) (Work.BoseFixB2.fsSide v μ)
        (Submission.BoseGases.wPairC (Work.BoseFixB2.fsSide v μ) v) Φ|
      + |(∑ p ∈ Submission.BoseGases.pairSet n,
            ∫ x in Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ),
              Submission.BoseGases.aP (Work.BoseFixB2.fsSide v μ) p.1
                  (Submission.BoseGases.aP (Work.BoseFixB2.fsSide v μ) p.2 Φ) x
                * Submission.BoseGases.aQ (Work.BoseFixB2.fsSide v μ) p.2
                  (Submission.BoseGases.aQ (Work.BoseFixB2.fsSide v μ) p.1 Φ) x
                * Submission.BoseGases.wPairC (Work.BoseFixB2.fsSide v μ) v (x p.1) (x p.2))|
      ≤ (13 * Submission.BoseGases.qcrossC * (∫ z : EuclideanSpace ℝ (Fin 3), v z)
          + 4 * Work.BoseBox.chiSup ^ 2
              * (Work.BoseBox.g0mass v h + ∫ y : EuclideanSpace ℝ (Fin 3), |v y|)
          + 5 * Submission.BoseGases.potappC * (_root_.BoseGases.a v))
        * μ ^ 2 * (Work.BoseFixB2.fsSide v μ) ^ 3 * Work.BoseBoxFix.normB v μ n Φ := by
  classical
  set ℓ : ℝ := Work.BoseFixB2.fsSide v μ with hℓdef
  -- ## nonnegative constants
  have hqc : (0 : ℝ) ≤ Submission.BoseGases.qcrossC := by
    rw [Submission.BoseGases.qcrossC]; positivity
  have hpc : (0 : ℝ) ≤ Submission.BoseGases.potappC := by
    rw [Submission.BoseGases.potappC]; positivity
  have hIv0 : (0 : ℝ) ≤ ∫ y : EuclideanSpace ℝ (Fin 3), |v y| :=
    MeasureTheory.integral_nonneg (fun y => abs_nonneg _)
  have hg0m : (0 : ℝ) ≤ Work.BoseBox.g0mass v h := by
    rw [Work.BoseBox.g0mass]
    exact MeasureTheory.integral_nonneg (fun y => abs_nonneg _)
  have hW0 : (0 : ℝ) ≤ ∫ z : EuclideanSpace ℝ (Fin 3), v z :=
    MeasureTheory.integral_nonneg (fun z => hv z)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hℓ3 : (0 : ℝ) < ℓ ^ 3 := by positivity
  -- ## the word estimates (the atoms)
  have hq1w := Submission.BoseGases.qcross_w_d11 (N := n) (ℓ := ℓ) (μ := μ) hℓ hμ.le hv hvrad
    hv1 hR hv_supp h hRℓ hΦ.continuous
  have hq3w := Submission.BoseGases.qcross_w_d13_quarter (N := n) (ℓ := ℓ) hℓ hv hvrad
    hv1 hR hv_supp h hRℓ hΦ.continuous
  have hT4w := Submission.BoseGases.qcross_w_d2_quarter (N := n) (ℓ := ℓ) hℓ hv hvrad
    hv1 hR hv_supp h hRℓ hΦ.continuous
  have hQ4b := q4word_le_of_low (v := v) (h := h) (μ := μ) (n := n) (R := R) (J := J)
    hΦ hΦs hΦn hℓ hμ ht1 hav hR hRℓ hv hvrad hv1 hv_supp hJ hn2 hlow
  have hdiff := q1word_onebody_diff_bound (v := v) (h := h) (μ := μ) (ℓ := ℓ) (n := n)
    (R := R) hℓ hR hμ hv hvrad hv1 hv_supp hRℓ hΦ
  rw [← hℓdef] at hQ4b
  have hQdef : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
      = Work.BoseBoxFix.normB v μ n Φ := rfl
  rw [hQdef] at hq1w hq3w hT4w hdiff
  -- ## the composite scalars
  set ν : ℝ := Work.BoseBoxFix.normB v μ n Φ with hνdef
  set Wv : ℝ := ∫ z : EuclideanSpace ℝ (Fin 3), v z with hWdef
  set G : ℝ := Work.BoseBox.g0mass v h + ∫ y : EuclideanSpace ℝ (Fin 3), |v y| with hGdef
  set X : ℝ := (n : ℝ) ^ 2 / ℓ ^ 3 with hXdef
  set Q4 : ℝ := Submission.BoseGases.q4word (N := n) ℓ
    (Submission.BoseGases.wPairC ℓ v) (Submission.BoseGases.omC (Classical.choose h)) Φ
    with hQ4def
  have hν0 : (0 : ℝ) ≤ ν := by
    rw [hνdef, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
    exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have hW0' : (0 : ℝ) ≤ Wv := by rw [hWdef]; exact hW0
  have hG0 : (0 : ℝ) ≤ G := by rw [hGdef]; linarith
  have hY0 : (0 : ℝ) ≤ μ ^ 2 * ℓ ^ 3 := by positivity
  -- ## the particle-window consequences
  have hX3 : 3 * X + μ ^ 2 * ℓ ^ 3 ≤ 13 * (μ ^ 2 * ℓ ^ 3) := by
    have h1 : X ≤ 4 * (μ ^ 2 * ℓ ^ 3) := by
      rw [hXdef, div_le_iff₀ hℓ3]
      nlinarith [hn2, hn0, sq_nonneg ((n : ℝ) - 2 * μ * ℓ ^ 3)]
    linarith
  have hμn : μ * (n : ℝ) ≤ 2 * (μ ^ 2 * ℓ ^ 3) := by
    nlinarith [mul_le_mul_of_nonneg_left hn2 hμ.le]
  -- ## the triangle inequality for `q₁` (only its one-body line sees `g₀`)
  have hq1g : |Submission.BoseGases.q1word (N := n) ℓ μ
        (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h))
        (Submission.BoseGases.wPairC ℓ v) Φ|
      ≤ Submission.BoseGases.qcrossC * Wv * (X + μ ^ 2 * ℓ ^ 3) * ν
        + 2 * Work.BoseBox.chiSup ^ 2 * G * μ * (n : ℝ) * ν := by
    calc |Submission.BoseGases.q1word (N := n) ℓ μ
            (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h))
            (Submission.BoseGases.wPairC ℓ v) Φ|
        = |(Submission.BoseGases.q1word (N := n) ℓ μ
              (Submission.BoseGases.wPairC ℓ v) (Submission.BoseGases.wPairC ℓ v) Φ)
            + (Submission.BoseGases.q1word (N := n) ℓ μ
                (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h))
                (Submission.BoseGases.wPairC ℓ v) Φ
              - Submission.BoseGases.q1word (N := n) ℓ μ
                (Submission.BoseGases.wPairC ℓ v) (Submission.BoseGases.wPairC ℓ v) Φ)| := by
          ring_nf
      _ ≤ |Submission.BoseGases.q1word (N := n) ℓ μ
              (Submission.BoseGases.wPairC ℓ v) (Submission.BoseGases.wPairC ℓ v) Φ|
            + |(Submission.BoseGases.q1word (N := n) ℓ μ
                (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h))
                (Submission.BoseGases.wPairC ℓ v) Φ
              - Submission.BoseGases.q1word (N := n) ℓ μ
                (Submission.BoseGases.wPairC ℓ v) (Submission.BoseGases.wPairC ℓ v) Φ)| :=
          abs_add_le _ _
      _ ≤ Submission.BoseGases.qcrossC * Wv * (X + μ ^ 2 * ℓ ^ 3) * ν
            + 2 * Work.BoseBox.chiSup ^ 2 * G * μ * (n : ℝ) * ν := by
          linarith [hq1w, hdiff]
  -- ## assembly
  have hqw : (0 : ℝ) ≤ Submission.BoseGases.qcrossC * Wv * ν :=
    mul_nonneg (mul_nonneg hqc hW0') hν0
  have hcg : (0 : ℝ) ≤ 2 * Work.BoseBox.chiSup ^ 2 * G * ν :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hG0) hν0
  have hmain : |Submission.BoseGases.q1word (N := n) ℓ μ
        (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h))
        (Submission.BoseGases.wPairC ℓ v) Φ|
      + |Submission.BoseGases.q3word (N := n) ℓ (Submission.BoseGases.wPairC ℓ v) Φ|
      + |(∑ p ∈ Submission.BoseGases.pairSet n,
            ∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ p.1
                  (Submission.BoseGases.aP ℓ p.2 Φ) x
                * Submission.BoseGases.aQ ℓ p.2
                  (Submission.BoseGases.aQ ℓ p.1 Φ) x
                * Submission.BoseGases.wPairC ℓ v (x p.1) (x p.2))|
      ≤ (13 * Submission.BoseGases.qcrossC * Wv
          + 4 * Work.BoseBox.chiSup ^ 2 * G
          + 5 * Submission.BoseGases.potappC * (_root_.BoseGases.a v)) * μ ^ 2 * ℓ ^ 3 * ν := by
    nlinarith [hq1g, hq3w, hT4w, hQ4b, hX3, hμn, hqw, hcg, hν0, hY0]
  exact hmain

end

end Work.BoseFixB2.DvApriori
