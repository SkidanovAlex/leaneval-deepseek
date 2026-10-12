import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.Assembly
import Submission.Work.BoseFixB3.Conv.abox_peel_pair
import Submission.Work.BoseFixB3.Conv.chi_highpass_decay
import Submission.Work.BoseFixB3.Conv.dilute_consequences
import Submission.Work.BoseFixB3.Conv.num_comparison
import Submission.Work.BoseFixB3.Conv.pair_conv_bound
import Submission.Work.BoseFixB3.Conv.q3om_sub_q3conv_le
import Submission.Work.BoseFixB3.Convolution.convolution_lemma
import Submission.Work.BoseFixB3.Eps.convI_abs_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.Conv.b3ConvRoot_holds`

FS `lem:Convolution`'s application inside FS §7 (`eq:pq'pp-sf` →
`eq:ReduceQ3`, `final_v2.tex` ll. 1518–1524): the `ω`-pairing word is dominated
by the convolution word up to FS's error `a n²ℓ⁻³(R/ℓ)²`.

## The mathematical chain (for one ordered pair `i ≠ j`)

With `ℓ = ellAt μ (a v)`, `f y := wScaled ℓ (g₀ v h) y · w₀ y` (so that
`convI ℓ v h = ∫ f`) and `χ_ℓ := chiScale ℓ`, the pair integrand of
`q3omWord` is

`(1−f_L)_j(aP i Φ) · aP j (aP i Φ) · χ_ℓ(x_i) · f(x_i − x_j) · χ_ℓ(x_j)`.

1. (`abox_peel_pair`) the `x_i`-integral only meets `χ_ℓ·f`, and equals
   `conv3 f χ_ℓ (x_j)`;
2. (`convolution_lemma`) `conv3 f χ_ℓ = χ_ℓ·I + ρ` with `‖ρ‖_∞ ≤ C(R/ℓ)²∫|f|`;
3. (`abox_highSlot_transfer`) `∫ (1−f_L)_j(aP i Φ) · aP j(aP i Φ) · χ_ℓ²`
   `= ∫ aP i Φ · aP j(aP i Φ) · (1−f_L)(χ_ℓ²)`;
4. (`chi_highpass_decay`) `‖(1−f_L)(χ_ℓ²)‖_∞ ≤ C (ℓκ)^{-40}`, while the
   remaining `ρ`-term is bounded crudely by `‖ρ‖_∞ ‖Φ‖²`;
5. summing over `i ≠ j` and comparing with `q3convWord`
   `= I ℓ⁻³ Σ_{i,j} ∫ aP i Φ · aP j Φ · (1−f_L)(χ_ℓ²)` (the `i = j` terms and
   the difference `2 aP j(aP i Φ) − aP j Φ` are controlled by the same
   `(ℓκ)^{-40}` bound), the errors are `≤ K μ² a ℓ³ (R/ℓ)² ‖Φ‖²` for a
   `μ`-independent `K`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3.Conv

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The kernel of `q3omWord` -/

/-- `chiU ℓ 0 = chiScale ℓ`. -/
lemma chiU_zero_eq_chiScale (ℓ : ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    chiU ℓ 0 z = chiScale ℓ z := by
  simp [chiU, chiScale]

/-- The convolution kernel of `lem:Convolution`: `f y = W₁(y) ω(y)`, so that
`convI ℓ v h = ∫ f`. -/
def convK (ℓ : ℝ) (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun y => wScaled ℓ (g0 v h) y * Classical.choose h y

lemma convI_eq_integral_convK (ℓ : ℝ) (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) :
    convI ℓ v h = ∫ y, convK ℓ v h y := rfl

/-- The pair kernel of `q3omWord` read as `χ_ℓ(x)·f(x−y)·χ_ℓ(y)`. -/
lemma w1At_mul_omAt (μ : ℝ) (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    w1At μ (a v) v h x y * omAt h x y
      = chiScale (ellAt μ (a v)) x * convK (ellAt μ (a v)) v h (x - y)
          * chiScale (ellAt μ (a v)) y := by
  simp only [w1At, omAt, omC, wLoc, ellAt, patAt, sideAt, convK, chiU_zero_eq_chiScale]
  ring

/-- `f = convK ℓ v h` is even. -/
lemma convK_even {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    (hvrad : BoseGases.IsRadial v) (ℓ : ℝ) :
    ∀ y, convK ℓ v h (-y) = convK ℓ v h y := by
  intro y
  have hw0 : _root_.BoseGases.IsRadial (Classical.choose h) := (w0_spec h).1
  have hg : ∀ z, g0 v h (-z) = g0 v h z := g0_even hvrad h
  have hcs : ∀ z, convScale ℓ (-z) = convScale ℓ z := convScale_symm ℓ
  simp only [convK, wScaled]
  rw [hg, hcs, radial_neg hw0 y]

/-- `f` vanishes off the ball of radius `R`. -/
lemma convK_eq_zero_of_le_norm {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) {ℓ : ℝ} {y : EuclideanSpace ℝ (Fin 3)}
    (hy : R ≤ ‖y‖) : convK ℓ v h y = 0 := by
  simp only [convK, wScaled, g0_support_of_norm_ge hv_supp hy h]
  ring

/-- The support of the convolution kernel sits in the ball of radius `2R`. -/
lemma tsupport_convK_subset {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {R ℓ : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball 0 R) :
    tsupport (convK ℓ v h) ⊆ Metric.ball 0 (2 * R) := by
  have hsub : Function.support (convK ℓ v h) ⊆ {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ < R} := by
    intro y hy
    by_contra hcon
    exact hy (convK_eq_zero_of_le_norm hv_supp (not_lt.mp hcon))
  have hb : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R
      = {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ < R} := by
    ext y; simp [Metric.mem_ball, dist_eq_norm]
  calc tsupport (convK ℓ v h) ⊆ closure {y : EuclideanSpace ℝ (Fin 3) | ‖y‖ < R} :=
        closure_mono hsub
    _ = Metric.closedBall 0 R := by rw [← hb, closure_ball 0 (ne_of_gt hR)]
    _ ⊆ Metric.ball 0 (2 * R) := Metric.closedBall_subset_ball (by linarith)

/-- `ω = w₀` is bounded by `1` a.e. -/
lemma choose_abs_le_one {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {R : ℝ}
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) :
    ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))), ‖Classical.choose h z‖ ≤ 1 := by
  have hb := chosen_w0_bounds_ae (R := R) hR hv hvrad hv_supp h
  filter_upwards [hb.1, hb.2] with z hz0 hz1
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, hz1⟩

/-- The convolution kernel `f` is integrable in the dilute regime. -/
lemma convK_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {R ℓ : ℝ}
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hℓ : 0 < ℓ)
    (hdil : R ≤ ℓ * Submission.BoseGases.chiR0) :
    MeasureTheory.Integrable (convK ℓ v h) := by
  have hW := wScaled_g0_integrable hR hv_supp h hℓ hdil
  have hωm : AEStronglyMeasurable (Classical.choose h)
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
    ((w0_spec h).2.lhs_integrable).aestronglyMeasurable
  have hωb := choose_abs_le_one (h := h) hv hvrad hR hv_supp
  have hI : MeasureTheory.Integrable
      (fun z => wScaled ℓ (g0 v h) z * Classical.choose h z) :=
    hW.mul_bdd (c := 1) hωm hωb
  rw [show convK ℓ v h = fun z => wScaled ℓ (g0 v h) z * Classical.choose h z from rfl]
  exact hI

/-- `∫ |f| ≤ 16π (a v)`. -/
lemma convK_abs_integral_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {R ℓ : ℝ}
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hℓ : 0 < ℓ)
    (hdil : R ≤ ℓ * Submission.BoseGases.chiR0) :
    (∫ y, |convK ℓ v h y|) ≤ 16 * π * BoseGases.a v := by
  have hW := wScaled_g0_integrable hR hv_supp h hℓ hdil
  have hωb := choose_abs_le_one (h := h) hv hvrad hR hv_supp
  have hbound : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
      ‖convK ℓ v h z‖ ≤ ‖wScaled ℓ (g0 v h) z‖ := by
    filter_upwards [hωb] with z hz
    simp only [convK, norm_mul]
    calc ‖wScaled ℓ (g0 v h) z‖ * ‖Classical.choose h z‖
        ≤ ‖wScaled ℓ (g0 v h) z‖ * 1 :=
          mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ = ‖wScaled ℓ (g0 v h) z‖ := mul_one _
  calc (∫ y, |convK ℓ v h y|) = ∫ y, ‖convK ℓ v h y‖ := by
        simp only [Real.norm_eq_abs]
    _ ≤ ∫ y, ‖wScaled ℓ (g0 v h) y‖ :=
        integral_mono_ae (convK_integrable hv hvrad hR hv_supp hℓ hdil).norm hW.norm hbound
    _ = ∫ y, |wScaled ℓ (g0 v h) y| := by simp only [Real.norm_eq_abs]
    _ ≤ 16 * π * BoseGases.a v :=
        wScaled_g0_abs_integral_le hR hv hvrad hv_supp h hℓ hdil

/-! ## 2. The two words as double sums -/

/-- `q3convWord` in the fibre-collapsed form
`I ℓ⁻³ Σ_{i,j} ∫_{abox} P_iΦ · (P_jΦ · hRes(x_j))`. -/
lemma q3convWord_eq_pairSum {fc : LowCut} {κ ℓ I : ℝ} {n : ℕ}
    {Φ : X n → ℝ} (hℓ : 0 < ℓ) (hΦ : Continuous Φ) :
    q3convWord fc κ ℓ I Φ
      = I * ℓ ^ (-(3 : ℤ)) * ∑ i : Fin n, ∑ j : Fin n,
          (∫ x in abox n ℓ, aP ℓ i Φ x * (aP ℓ j Φ x * Eps.hRes fc κ ℓ (x j))) := by
  unfold q3convWord
  congr 1
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  apply integral_congr_ae
  filter_upwards with x
  rw [Eps.highSlot_chiSq_aP_eq hℓ hΦ x]

/-- `q3omWord` as the double sum of the pair integrals. -/
lemma q3omWord_eq_pairSum {fc : LowCut} {κ : ℝ} {n : ℕ}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ} {Φ : X n → ℝ} :
    q3omWord fc κ (ellAt μ (a v)) (w1At μ (a v) v h) (omAt h) Φ
      = 2 * ∑ i : Fin n, ∑ j : Fin n,
          if i ≠ j then
            (∫ x in abox n (ellAt μ (a v)),
                highSlot fc κ (ellAt μ (a v)) j (aP (ellAt μ (a v)) i Φ) x
                  * aP (ellAt μ (a v)) j (aP (ellAt μ (a v)) i Φ) x
                  * (chiScale (ellAt μ (a v)) (x i) * convK (ellAt μ (a v)) v h (x i - x j)
                      * chiScale (ellAt μ (a v)) (x j)))
          else 0 := by
  have hpt : ∀ p : Fin n × Fin n,
      (∫ x in abox n (ellAt μ (a v)),
          highSlot fc κ (ellAt μ (a v)) p.2 (aP (ellAt μ (a v)) p.1 Φ) x
            * aP (ellAt μ (a v)) p.2 (aP (ellAt μ (a v)) p.1 Φ) x
            * w1At μ (a v) v h (x p.1) (x p.2) * omAt h (x p.1) (x p.2))
        = (∫ x in abox n (ellAt μ (a v)),
            highSlot fc κ (ellAt μ (a v)) p.2 (aP (ellAt μ (a v)) p.1 Φ) x
              * aP (ellAt μ (a v)) p.2 (aP (ellAt μ (a v)) p.1 Φ) x
              * (chiScale (ellAt μ (a v)) (x p.1) * convK (ellAt μ (a v)) v h (x p.1 - x p.2)
                  * chiScale (ellAt μ (a v)) (x p.2))) := by
    intro p
    apply integral_congr_ae
    filter_upwards with x
    calc highSlot fc κ (ellAt μ (a v)) p.2 (aP (ellAt μ (a v)) p.1 Φ) x
            * aP (ellAt μ (a v)) p.2 (aP (ellAt μ (a v)) p.1 Φ) x
            * w1At μ (a v) v h (x p.1) (x p.2) * omAt h (x p.1) (x p.2)
        = highSlot fc κ (ellAt μ (a v)) p.2 (aP (ellAt μ (a v)) p.1 Φ) x
            * aP (ellAt μ (a v)) p.2 (aP (ellAt μ (a v)) p.1 Φ) x
            * (w1At μ (a v) v h (x p.1) (x p.2) * omAt h (x p.1) (x p.2)) := by ring
      _ = highSlot fc κ (ellAt μ (a v)) p.2 (aP (ellAt μ (a v)) p.1 Φ) x
            * aP (ellAt μ (a v)) p.2 (aP (ellAt μ (a v)) p.1 Φ) x
            * (chiScale (ellAt μ (a v)) (x p.1) * convK (ellAt μ (a v)) v h (x p.1 - x p.2)
                * chiScale (ellAt μ (a v)) (x p.2)) := by
          rw [w1At_mul_omAt]
  simp only [q3omWord, hpt]
  congr 1
  rw [pairSet, Finset.sum_filter, Fintype.sum_prod_type]

theorem b3ConvRoot_holds (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (h : Work.UBB.ScatSol v) (R : ℝ) (fc : Work.BoseBoxFix.LowCut)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    (hvrad : BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < BoseGases.a v) :
    Work.BoseFixB3.B3ConvRoot v h R fc := by
  classical
  obtain ⟨Cdec, hCdec0, hCdec⟩ := chi_highpass_decay
  obtain ⟨Ccv, hCcv0, hCcv⟩ := Work.BoseFixB3.Convolution.convolution_lemma
  obtain ⟨ε₁, hε₁0, hε₁⟩ := dilute_consequences v h R hv hvrad hR hv_supp hav
  have hchiM0 : 0 ≤ (Real.sqrt chiNormSq)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  refine ⟨max 1 (max (512 * π * Cdec * (BoseGases.a v) ^ 2 / R ^ 2)
      (1024 * π * Ccv * (Real.sqrt chiNormSq)⁻¹)), min ε₁ 1,
      le_trans zero_le_one (le_max_left 1 _), lt_min hε₁0 one_pos, ?_⟩
  intro μ hAdm n Φ hn
  have hAdm₁ : Adm v ε₁ μ := Work.BoseFixB3.Adm.mono hAdm (min_le_left _ _)
  obtain ⟨hX1, hdil, hDX, hκℓz, hℓpos, hκpos⟩ := hε₁ μ hAdm₁
  have hΦc : Continuous (Φ : X n → ℝ) := Φ.contDiff.continuous
  have hA0 : 0 < BoseGases.a v := hav
  have hμ0 : 0 < μ := hAdm.1
  set D : ℝ := (patAt μ (BoseGases.a v)).d with hDdef
  have hD0 : 0 < D := Eps.patAt_d_pos (mul_pos hμ0 (pow_pos hA0 3))
  -- kernel facts
  have hfint : MeasureTheory.Integrable (convK (ellAt μ (BoseGases.a v)) v h) :=
    convK_integrable (v := v) (h := h) (R := R) hv hvrad hR hv_supp hℓpos hdil
  have hfeven : ∀ y, convK (ellAt μ (BoseGases.a v)) v h (-y)
      = convK (ellAt μ (BoseGases.a v)) v h y := convK_even hvrad (ellAt μ (BoseGases.a v))
  have hfsupp : tsupport (convK (ellAt μ (BoseGases.a v)) v h) ⊆ Metric.ball 0 (2 * R) :=
    tsupport_convK_subset (v := v) (h := h) (R := R) (ℓ := ellAt μ (BoseGases.a v)) hR hv_supp
  have hfabs : (∫ z, |convK (ellAt μ (BoseGases.a v)) v h z|) ≤ 16 * π * BoseGases.a v :=
    convK_abs_integral_le (v := v) (h := h) (R := R) (ℓ := ellAt μ (BoseGases.a v)) hv hvrad hR hv_supp hℓpos hdil
  have hIbound : |convI (ellAt μ (BoseGases.a v)) v h| ≤ 16 * π * BoseGases.a v :=
    Eps.convI_abs_le (v := v) (h := h) (R := R) (ℓ := ellAt μ (BoseGases.a v)) hv hvrad hR hv_supp hℓpos hdil
  have hIeq : convI (ellAt μ (BoseGases.a v)) v h = ∫ y, convK (ellAt μ (BoseGases.a v)) v h y :=
    convI_eq_integral_convK _ _ _
  -- the residual bound
  have hresb : ∀ z : EuclideanSpace ℝ (Fin 3),
      |Eps.hRes fc (kapAt μ (BoseGases.a v)) (ellAt μ (BoseGases.a v)) z| ≤ Cdec * D ^ 80 := by
    intro z
    have h1 := hCdec fc (kapAt μ (BoseGases.a v)) (ellAt μ (BoseGases.a v)) hℓpos hκpos z
    have hkey : Eps.hRes fc (kapAt μ (BoseGases.a v)) (ellAt μ (BoseGases.a v)) z
        = -(Work.BoseBoxFix.lowMult fc (kapAt μ (BoseGases.a v)) (ellAt μ (BoseGases.a v))
              (fun z => chiScale (ellAt μ (BoseGases.a v)) z ^ 2) z
            - chiScale (ellAt μ (BoseGases.a v)) z ^ 2) := by
      simp only [Eps.hRes, chiU_zero_eq_chiScale]
      ring
    have h2 : |Work.BoseBoxFix.lowMult fc (kapAt μ (BoseGases.a v)) (ellAt μ (BoseGases.a v))
          (fun z => chiScale (ellAt μ (BoseGases.a v)) z ^ 2) z
          - chiScale (ellAt μ (BoseGases.a v)) z ^ 2|
        ≤ Cdec / (ellAt μ (BoseGases.a v) * kapAt μ (BoseGases.a v)) ^ 40 := by
      simpa only [chiScale] using h1
    have h5 : (ellAt μ (BoseGases.a v) * kapAt μ (BoseGases.a v)) ^ (-(40 : ℤ)) = D ^ 80 := by
      rw [hDdef]
      exact hκℓz
    have h6 : ((ellAt μ (BoseGases.a v) * kapAt μ (BoseGases.a v)) ^ (40 : ℕ))⁻¹ = D ^ 80 := by
      have h5' := h5
      rw [zpow_neg, zpow_ofNat] at h5'
      exact h5'
    have h4 : Cdec / (ellAt μ (BoseGases.a v) * kapAt μ (BoseGases.a v)) ^ 40 = Cdec * D ^ 80 := by
      rw [div_eq_mul_inv, h6]
    rw [hkey, abs_neg]
    exact h2.trans (le_of_eq h4)
  -- the kernel-error budget
  set ρmax : ℝ := Ccv * (2 * R / ellAt μ (BoseGases.a v)) ^ 2
    * (∫ z, |convK (ellAt μ (BoseGases.a v)) v h z|) with hρmaxdef
  have hρmax0 : 0 ≤ ρmax := by
    rw [hρmaxdef]
    exact mul_nonneg (mul_nonneg hCcv0 (sq_nonneg _)) (integral_nonneg (fun z => abs_nonneg _))
  -- per-pair bound (D7)
  have hper : ∀ i j : Fin n, i ≠ j →
      (∫ x in abox n (ellAt μ (BoseGases.a v)),
          highSlot fc (kapAt μ (BoseGases.a v)) (ellAt μ (BoseGases.a v)) j
              (aP (ellAt μ (BoseGases.a v)) i (Φ : X n → ℝ)) x
            * aP (ellAt μ (BoseGases.a v)) j
                (aP (ellAt μ (BoseGases.a v)) i (Φ : X n → ℝ)) x
            * (chiScale (ellAt μ (BoseGases.a v)) (x i)
                * (Submission.BoseGases.wScaled (ellAt μ (BoseGases.a v)) (g0 v h) (x i - x j)
                    * Classical.choose h (x i - x j))
                * chiScale (ellAt μ (BoseGases.a v)) (x j)))
        ≤ ((ellAt μ (BoseGases.a v)) ^ 3)⁻¹ *
            (convI (ellAt μ (BoseGases.a v)) v h
                * (∫ x in abox n (ellAt μ (BoseGases.a v)),
                    aP (ellAt μ (BoseGases.a v)) i (Φ : X n → ℝ) x
                      * (aP (ellAt μ (BoseGases.a v)) j
                            (aP (ellAt μ (BoseGases.a v)) i (Φ : X n → ℝ)) x
                          * Eps.hRes fc (kapAt μ (BoseGases.a v)) (ellAt μ (BoseGases.a v)) (x j)))
              + ρmax * (Real.sqrt chiNormSq)⁻¹
                  * (∫ x in abox n (ellAt μ (BoseGases.a v)), ((Φ : X n → ℝ) x) ^ 2)) := by
    intro i j hij
    have hρdef : ∀ y, Submission.BoseGases.conv3 (convK (ellAt μ (BoseGases.a v)) v h)
        (fun z => Submission.BoseGases.chi (((ellAt μ (BoseGases.a v))⁻¹) • z)) y
        = Submission.BoseGases.chiScale (ellAt μ (BoseGases.a v)) y * convI (ellAt μ (BoseGases.a v)) v h
          + (Submission.BoseGases.conv3 (convK (ellAt μ (BoseGases.a v)) v h)
              (fun z => Submission.BoseGases.chi (((ellAt μ (BoseGases.a v))⁻¹) • z)) y
              - Submission.BoseGases.chiScale (ellAt μ (BoseGases.a v)) y
                  * convI (ellAt μ (BoseGases.a v)) v h) := by
      intro y; ring
    have hρb : ∀ y, |Submission.BoseGases.conv3 (convK (ellAt μ (BoseGases.a v)) v h)
          (fun z => Submission.BoseGases.chi (((ellAt μ (BoseGases.a v))⁻¹) • z)) y
          - Submission.BoseGases.chiScale (ellAt μ (BoseGases.a v)) y
              * convI (ellAt μ (BoseGases.a v)) v h| ≤ ρmax := by
      intro y
      have hcv2 := hCcv (convK (ellAt μ (BoseGases.a v)) v h) hfint hfeven
        (R := 2 * R) (ℓ := ellAt μ (BoseGases.a v)) (by linarith) hℓpos hfsupp y
      rw [hρmaxdef, hIeq]
      simpa only [chiScale] using hcv2
    have hab := pair_conv_bound (n := n) (ℓ := ellAt μ (BoseGases.a v))
      (κ := kapAt μ (BoseGases.a v)) (fc := fc) (i := i) (j := j)
      (Φ := (Φ : X n → ℝ)) hℓpos hκpos hij hΦc
      hfint hfeven hIeq (ρ := fun y => Submission.BoseGases.conv3 (convK (ellAt μ (BoseGases.a v)) v h)
        (fun z => Submission.BoseGases.chi (((ellAt μ (BoseGases.a v))⁻¹) • z)) y
          - Submission.BoseGases.chiScale (ellAt μ (BoseGases.a v)) y
              * convI (ellAt μ (BoseGases.a v)) v h) hρdef hρmax0 hρb
    simpa only [convK] using hab
  -- the sum-level comparison (D8)
  have hsum := q3om_sub_q3conv_le (n := n) (κ := kapAt μ (BoseGases.a v)) (fc := fc)
    (v := v) (h := h) (μ := μ) (I := convI (ellAt μ (BoseGases.a v)) v h)
    (B := Cdec * D ^ 80) (ρmax := ρmax) (χM := (Real.sqrt chiNormSq)⁻¹)
    (Φ := (Φ : X n → ℝ)) hℓpos (mul_nonneg hCdec0 (pow_nonneg hD0.le 80)) hρmax0 hchiM0 hΦc
    (by simpa only [convK] using hIeq) hresb hper
  -- the numeric comparison
  have hnum : (4 * |convI (ellAt μ (BoseGases.a v)) v h|
          * ((ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ))) * (Cdec * D ^ 80)
        + 2 * ((ellAt μ (BoseGases.a v)) ^ (-(3 : ℤ))) * ρmax * (Real.sqrt chiNormSq)⁻¹)
        * ((n : ℝ) ^ 2 * (∫ x in abox n (ellAt μ (BoseGases.a v)), ((Φ : X n → ℝ) x) ^ 2))
      ≤ max 1 (max (512 * π * Cdec * (BoseGases.a v) ^ 2 / R ^ 2)
          (1024 * π * Ccv * (Real.sqrt chiNormSq)⁻¹))
        * μ ^ 2 * (BoseGases.a v) * (ellAt μ (BoseGases.a v)) ^ 3
        * (R ^ 2 / (ellAt μ (BoseGases.a v)) ^ 2)
        * (∫ x in abox n (ellAt μ (BoseGases.a v)), ((Φ : X n → ℝ) x) ^ 2) := by
    have hρmax_le : ρmax ≤ Ccv * (2 * R / ellAt μ (BoseGases.a v)) ^ 2 * (16 * π * (BoseGases.a v)) := by
      rw [hρmaxdef]
      exact mul_le_mul_of_nonneg_left hfabs (mul_nonneg hCcv0 (sq_nonneg _))
    have hnB : 0 ≤ ∫ x in abox n (ellAt μ (BoseGases.a v)), ((Φ : X n → ℝ) x) ^ 2 :=
      integral_nonneg (fun x => sq_nonneg _)
    have hDℓ : D ^ 80 * (ellAt μ (BoseGases.a v)) ^ 2 ≤ (BoseGases.a v) ^ 2 := by
      nlinarith [hDX, hD0.le, pow_nonneg hD0.le 80, sq_nonneg (ellAt μ (BoseGases.a v))]
    exact num_comparison (n := n) (μ := μ) (R := R) (ℓ := ellAt μ (BoseGases.a v))
      (A := BoseGases.a v) (D := D) (Cdec := Cdec) (Ccv := Ccv)
      (χM := (Real.sqrt chiNormSq)⁻¹) (I := convI (ellAt μ (BoseGases.a v)) v h)
      (ρmax := ρmax) (normB := ∫ x in abox n (ellAt μ (BoseGases.a v)), ((Φ : X n → ℝ) x) ^ 2)
      hμ0 hR hℓpos hA0 hD0.le hCdec0 hCcv0 hchiM0 hn hnB hIbound hρmax_le hDℓ
  have hgoal : -q3omWord fc (kapAt μ (BoseGases.a v)) (ellAt μ (BoseGases.a v))
        (w1At μ (BoseGases.a v) v h) (omAt h) (Φ : X n → ℝ)
      ≥ -q3convWord fc (kapAt μ (BoseGases.a v)) (ellAt μ (BoseGases.a v))
          (convI (ellAt μ (BoseGases.a v)) v h) (Φ : X n → ℝ)
        - max 1 (max (512 * π * Cdec * (BoseGases.a v) ^ 2 / R ^ 2)
            (1024 * π * Ccv * (Real.sqrt chiNormSq)⁻¹))
          * μ ^ 2 * (BoseGases.a v) * (ellAt μ (BoseGases.a v)) ^ 3
          * (R ^ 2 / (ellAt μ (BoseGases.a v)) ^ 2)
          * normB v μ n (Φ : X n → ℝ) := by
    have h1 : q3omWord fc (kapAt μ (BoseGases.a v)) (ellAt μ (BoseGases.a v))
          (w1At μ (BoseGases.a v) v h) (omAt h) (Φ : X n → ℝ)
        - q3convWord fc (kapAt μ (BoseGases.a v)) (ellAt μ (BoseGases.a v))
          (convI (ellAt μ (BoseGases.a v)) v h) (Φ : X n → ℝ)
        ≤ max 1 (max (512 * π * Cdec * (BoseGases.a v) ^ 2 / R ^ 2)
            (1024 * π * Ccv * (Real.sqrt chiNormSq)⁻¹))
          * μ ^ 2 * (BoseGases.a v) * (ellAt μ (BoseGases.a v)) ^ 3
          * (R ^ 2 / (ellAt μ (BoseGases.a v)) ^ 2)
          * normB v μ n (Φ : X n → ℝ) := by
      have h2 : (∫ x in abox n (ellAt μ (BoseGases.a v)), ((Φ : X n → ℝ) x) ^ 2)
          = normB v μ n (Φ : X n → ℝ) := rfl
      rw [h2] at hnum
      exact hsum.trans hnum
    linarith
  exact hgoal

end Work.BoseFixB3.Conv
