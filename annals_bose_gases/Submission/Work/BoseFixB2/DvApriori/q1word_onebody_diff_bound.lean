import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseFixB2.DvApriori.BandDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.q1word_onebody_diff_bound`

The one-body (`μ`-)line of `q1word` is the only place where the kernel *numerator* enters
linearly; the two-body (`w₂`-)line carries `w₂ = wPairC ℓ v` in both words compared here and
is therefore **identical**.  Hence the difference of the two `q1word`s is `2μ` times the
difference of the two one-body cross sums `Σᵢ∫(QᵢΦ)(PᵢΦ)·fibre_{h}(xᵢ)`, `h ∈ {g₀, v}`, and
each of those obeys the AM–GM/Parseval estimate

  `|Σᵢ∫(PᵢΦ)(QᵢΦ)·f(xᵢ)| ≤ (sup|f|/2)·(n₊ + S₁) = (sup|f|/2)·N·∫_{abox}Φ²`

(the mechanism of `Submission.Work.OneBodyCross.onebody_cross_sum_abs_le`, here generalised to
an *abstract* fibre `f`), where `sup|fibre_h| ≤ 2·chiSup²·∫|h|` is the fibre bound
`Submission.KernelFibreBound.fibre_acube_abs_le`, and `n₊ + S₁ = N‖Φ‖²` is
`Submission.CentredSector.cnPlus_add_cS1`.  With `∫|g₀| = g0mass` this yields exactly

  `2μ·(chiSup²·(∫|v| + g0mass))·N·∫Φ² = 2·chiSup²·(g0mass + ∫|v|)·μ·N·∫Φ²`.

(Note that no *cancellation* of `g₀` against `v` is used: the triangle inequality
`∫|g₀ − v| ≤ g0mass + ∫|v|` is the reason the statement's constant is a sum.)
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## An abstract-fibre version of the one-body cross estimate -/

/-- Per-slot one-body cross bound with an abstract fibre `f` bounded by `C`:
`|∫_{abox}(QᵢΦ)(PᵢΦ)·f(xᵢ)| ≤ (C/2)·(‖PᵢΦ‖² + ‖QᵢΦ‖²)` (AM–GM pointwise). -/
lemma onebody_cross_per_gen {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f : ℝ³ → ℝ} {C : ℝ}
    (hFm : AEStronglyMeasurable f (volume.restrict (acube ℓ)))
    (hfib : ∀ z : ℝ³, |f z| ≤ C) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    |∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f (x i)|
      ≤ (1 / 2) * C *
          ((∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) := by
  classical
  let μ : Measure (X N) := volume.restrict (abox N ℓ)
  let g : X N → ℝ := fun x => (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f (x i)
  let b : X N → ℝ := fun x => (1 / 2) * ((aP ℓ i Φ x) ^ 2 + (aQ ℓ i Φ x) ^ 2)
  have hPc : Continuous (aP ℓ i Φ) := aP_continuous hℓ i hΦc
  have hQc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
  have hPQc : Continuous (fun x : X N => (aQ ℓ i Φ x) * (aP ℓ i Φ x)) := hQc.mul hPc
  have hgI : Integrable g μ := by
    have hh : IntegrableOn (fun x : X N => (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f (x i))
        (abox N ℓ) volume :=
      integrableOn_slot_fibre hℓ i hFm (fun z _ => hfib z) hPQc
    exact hh
  have hP2i : Integrable (fun x : X N => (aP ℓ i Φ x) ^ 2) μ :=
    integrableOn_abox_of_continuous hℓ (hPc.pow 2)
  have hQ2i : Integrable (fun x : X N => (aQ ℓ i Φ x) ^ 2) μ :=
    integrableOn_abox_of_continuous hℓ (hQc.pow 2)
  have hbI : Integrable b μ := by
    have hsum : Integrable (fun x : X N => (aP ℓ i Φ x) ^ 2 + (aQ ℓ i Φ x) ^ 2) μ :=
      hP2i.add hQ2i
    exact hsum.const_mul (1 / 2)
  have hCbI : Integrable (fun x : X N => C * b x) μ := hbI.const_mul C
  have hgb : ∀ x : X N, |g x| ≤ C * b x := by
    intro x
    have hF : |f (x i)| ≤ C := hfib (x i)
    have ham : |(aQ ℓ i Φ x) * (aP ℓ i Φ x)| ≤ b x := by
      rw [abs_mul]
      calc |aQ ℓ i Φ x| * |aP ℓ i Φ x|
            ≤ (1 / 2) * (aQ ℓ i Φ x) ^ 2 + (1 / 2) * (aP ℓ i Φ x) ^ 2 :=
              abs_mul_le_half_sq_sq (aQ ℓ i Φ x) (aP ℓ i Φ x)
        _ = b x := by simp only [b]; ring
    have hb0 : 0 ≤ b x := by
      simp only [b]
      positivity
    calc
      |g x| = |(aQ ℓ i Φ x) * (aP ℓ i Φ x)| * |f (x i)| := by
        dsimp only [g]
        rw [abs_mul]
      _ ≤ b x * C := mul_le_mul ham hF (abs_nonneg _) hb0
      _ = C * b x := by ring
  have hbE : (∫ x, b x ∂μ)
      = (1 / 2) * ((∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2)
          + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) := by
    calc
      (∫ x, b x ∂μ)
          = ∫ x in abox N ℓ, (1 / 2) * ((aP ℓ i Φ x) ^ 2 + (aQ ℓ i Φ x) ^ 2) := by
              dsimp [b, μ]
      _ = (1 / 2) * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 + (aQ ℓ i Φ x) ^ 2) := by
              rw [integral_const_mul]
      _ = (1 / 2) * ((∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2)
            + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) := by
              congr 1
              calc
                (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 + (aQ ℓ i Φ x) ^ 2)
                    = ∫ x, ((fun x => (aP ℓ i Φ x) ^ 2)
                        + (fun x => (aQ ℓ i Φ x) ^ 2)) x ∂μ := by
                        dsimp [μ]
                _ = (∫ x, (fun x => (aP ℓ i Φ x) ^ 2) x ∂μ)
                    + (∫ x, (fun x => (aQ ℓ i Φ x) ^ 2) x ∂μ) := by
                        exact integral_add hP2i hQ2i
                _ = (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2)
                    + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
                        dsimp [μ]
  have h1 : |∫ x, g x ∂μ| ≤ ∫ x, |g x| ∂μ := abs_integral_le_integral_abs (μ := μ) (f := g)
  have h2 : (∫ x, |g x| ∂μ) ≤ ∫ x, C * b x ∂μ :=
    integral_mono_ae (μ := μ) hgI.abs hCbI (by filter_upwards with x; exact hgb x)
  calc
    |∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f (x i)|
        = |∫ x, g x ∂μ| := by dsimp [g, μ]
    _ ≤ ∫ x, |g x| ∂μ := h1
    _ ≤ ∫ x, C * b x ∂μ := h2
    _ = C * (∫ x, b x ∂μ) := by rw [integral_const_mul]
    _ = C * ((1 / 2) * ((∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2)
          + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2))) := by rw [hbE]
    _ = (1 / 2) * C * ((∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2)
          + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) := by ring

/-- Summed abstract-fibre one-body cross bound:
`|Σᵢ∫_{abox}(QᵢΦ)(PᵢΦ)·f(xᵢ)| ≤ (C/2)·(S₁ + n₊)`. -/
lemma onebody_cross_sum_abs_le_gen {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f : ℝ³ → ℝ} {C : ℝ}
    (hFm : AEStronglyMeasurable f (volume.restrict (acube ℓ)))
    (hfib : ∀ z : ℝ³, |f z| ≤ C) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    |∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f (x i)|
      ≤ (1 / 2) * C * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
  have hper : ∀ i : Fin N,
      |∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f (x i)|
        ≤ (1 / 2) * C *
            ((∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) :=
    fun i => onebody_cross_per_gen hℓ hFm hfib i hΦc
  calc
    |∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f (x i)|
        ≤ ∑ i : Fin N, |∫ x in abox N ℓ,
            (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f (x i)| := by
            simpa using (Finset.abs_sum_le_sum_abs (s := Finset.univ)
              (f := fun i : Fin N => ∫ x in abox N ℓ,
                (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f (x i)))
    _ ≤ ∑ i : Fin N, (1 / 2) * C *
          ((∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)) :=
          Finset.sum_le_sum (fun i _ => hper i)
    _ = (1 / 2) * C * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
          rw [← Finset.mul_sum]
          rw [Finset.sum_add_distrib]
          dsimp [cS1, cnPlus]

/-! ## The `q1word` one-body line and its difference identity -/

/-- The one-body (`μ`-)line of `q1word`: `Σᵢ∫_{abox}(QᵢΦ)(PᵢΦ)·(∫_{acube} w₁(xᵢ,y)dy)`. -/
noncomputable def q1OneBody {N : ℕ} (ℓ : ℝ) (w1 : ℝ³ → ℝ³ → ℝ) (Φ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ w1 (x i))

/-- `q1word` splits into its two-body line and `−2μ` times its one-body line. -/
lemma q1word_eq_pair_sub_onebody {N : ℕ} (ℓ μ : ℝ) (w1 w2 : ℝ³ → ℝ³ → ℝ)
    (Φ : X N → ℝ) :
    q1word (N := N) ℓ μ w1 w2 Φ
      = 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * w2 (x p.1) (x p.2))
        - 2 * μ * q1OneBody ℓ w1 Φ := by
  simp only [q1word, q1OneBody]

/-- The two `q1word`s compared here differ only in their one-body line. -/
lemma q1word_sub_eq {N : ℕ} (ℓ μ : ℝ) (w1 w1' w2 : ℝ³ → ℝ³ → ℝ)
    (Φ : X N → ℝ) :
    q1word (N := N) ℓ μ w1 w2 Φ - q1word (N := N) ℓ μ w1' w2 Φ
      = 2 * μ * (q1OneBody ℓ w1' Φ - q1OneBody ℓ w1 Φ) := by
  simp only [q1word, q1OneBody]
  ring

/-! ## The target -/

theorem q1word_onebody_diff_bound {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ ℓ : ℝ} {n : ℕ} {R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (hμ : 0 < μ)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    |Submission.BoseGases.q1word (N := n) ℓ μ (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h))
        (Submission.BoseGases.wPairC ℓ v) Φ
      - Submission.BoseGases.q1word (N := n) ℓ μ (Submission.BoseGases.wPairC ℓ v)
        (Submission.BoseGases.wPairC ℓ v) Φ|
      ≤ (2 * Work.BoseBox.chiSup ^ 2 * (Work.BoseBox.g0mass v h + ∫ y : EuclideanSpace ℝ (Fin 3), |v y|))
          * μ * (n : ℝ) * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
  classical
  -- convert the two `Work.BoseBox` spellings into the corpus ones
  rw [show Work.BoseBox.chiSup = chiSup from rfl,
      show Work.BoseBox.g0mass v h = ∫ y : ℝ³, |Submission.BoseGases.g0 v h y| from rfl]
  have hΦc : Continuous Φ := hΦ.continuous
  -- the two fibres and their sup bounds
  have hFvb : ∀ z : ℝ³, |∫ y in acube ℓ, wPair ℓ v z y| ≤ chiSup ^ 2 * 2 * (∫ y : ℝ³, |v y|) := by
    intro z
    exact fibre_acube_abs_le hℓ hR.le hRℓ (v_integrable hv1)
      (fun z hz => v_eq_zero_of_norm_ge hv_supp hz) z
  have hFgb : ∀ z : ℝ³, |∫ y in acube ℓ, wPair ℓ (g0 v h) z y|
      ≤ chiSup ^ 2 * 2 * (∫ y : ℝ³, |g0 v h y|) := by
    intro z
    exact fibre_acube_abs_le hℓ hR.le hRℓ (g0_integrable hR hv_supp h)
      (fun z hz => g0_zero_of_norm_ge hv_supp hz h) z
  have hFvm : AEStronglyMeasurable (fun z : ℝ³ => ∫ y in acube ℓ, wPair ℓ v z y)
      (volume.restrict (acube ℓ)) :=
    fibre_acube_aem (ℓ := ℓ) (h := v) (v_integrable hv1)
  have hFgm : AEStronglyMeasurable (fun z : ℝ³ => ∫ y in acube ℓ, wPair ℓ (g0 v h) z y)
      (volume.restrict (acube ℓ)) :=
    fibre_acube_aem (ℓ := ℓ) (h := g0 v h) (g0_integrable hR hv_supp h)
  -- the two one-body bounds
  have hOV : |q1OneBody ℓ (wPairC ℓ v) Φ|
      ≤ (1 / 2) * (chiSup ^ 2 * 2 * (∫ y : ℝ³, |v y|)) * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
    simpa only [q1OneBody, w1Fibre, wPairC] using
      (onebody_cross_sum_abs_le_gen (N := n) hℓ (f := fun z : ℝ³ => ∫ y in acube ℓ, wPair ℓ v z y)
        hFvm hFvb hΦc)
  have hOG : |q1OneBody ℓ (wPairC ℓ (g0 v h)) Φ|
      ≤ (1 / 2) * (chiSup ^ 2 * 2 * (∫ y : ℝ³, |g0 v h y|)) * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
    simpa only [q1OneBody, w1Fibre, wPairC] using
      (onebody_cross_sum_abs_le_gen (N := n) hℓ
        (f := fun z : ℝ³ => ∫ y in acube ℓ, wPair ℓ (g0 v h) z y) hFgm hFgb hΦc)
  have hparse : cS1 ℓ Φ + cnPlus ℓ Φ = (n : ℝ) * (∫ x in abox n ℓ, (Φ x) ^ 2) := by
    rw [add_comm]
    exact cnPlus_add_cS1 hℓ hΦc
  have h2μ : (0 : ℝ) ≤ 2 * μ := by linarith
  -- triangle inequality for the difference of the two one-body lines
  have htri : |q1OneBody ℓ (wPairC ℓ v) Φ - q1OneBody ℓ (wPairC ℓ (g0 v h)) Φ|
      ≤ |q1OneBody ℓ (wPairC ℓ v) Φ| + |q1OneBody ℓ (wPairC ℓ (g0 v h)) Φ| := by
    have h := abs_add_le (q1OneBody ℓ (wPairC ℓ v) Φ)
      (-(q1OneBody ℓ (wPairC ℓ (g0 v h)) Φ))
    rw [sub_eq_add_neg]
    simpa only [abs_neg] using h
  calc
    |Submission.BoseGases.q1word (N := n) ℓ μ (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h))
        (Submission.BoseGases.wPairC ℓ v) Φ
      - Submission.BoseGases.q1word (N := n) ℓ μ (Submission.BoseGases.wPairC ℓ v)
        (Submission.BoseGases.wPairC ℓ v) Φ|
        = |2 * μ * (q1OneBody ℓ (wPairC ℓ v) Φ - q1OneBody ℓ (wPairC ℓ (g0 v h)) Φ)| := by
            rw [q1word_sub_eq]
    _ = 2 * μ * |q1OneBody ℓ (wPairC ℓ v) Φ - q1OneBody ℓ (wPairC ℓ (g0 v h)) Φ| := by
            rw [abs_mul, abs_of_nonneg h2μ]
    _ ≤ 2 * μ * (|q1OneBody ℓ (wPairC ℓ v) Φ| + |q1OneBody ℓ (wPairC ℓ (g0 v h)) Φ|) :=
            mul_le_mul_of_nonneg_left htri h2μ
    _ ≤ 2 * μ * ((1 / 2) * (chiSup ^ 2 * 2 * (∫ y : ℝ³, |v y|)) * (cS1 ℓ Φ + cnPlus ℓ Φ)
          + (1 / 2) * (chiSup ^ 2 * 2 * (∫ y : ℝ³, |g0 v h y|)) * (cS1 ℓ Φ + cnPlus ℓ Φ)) :=
            mul_le_mul_of_nonneg_left (add_le_add hOV hOG) h2μ
    _ = (2 * chiSup ^ 2 * ((∫ y : ℝ³, |g0 v h y|) + (∫ y : ℝ³, |v y|))) * μ * (n : ℝ)
          * (∫ x in abox n ℓ, (Φ x) ^ 2) := by
            rw [hparse]
            ring

end Work.BoseFixB2.DvApriori
