import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.chiRowSum_eval
import Submission.Work.BoseBoxFock.chiRow_muCorr_eq
import Submission.Work.BoseBoxFock.chiRow_muForm_decomp
import Submission.Work.BoseBoxFock.doubleSlot_lin
import Submission.Work.BoseBoxFock.doubleSlot_n0Form
import Submission.Work.BoseBoxFock.muLine_abs_le
import Submission.Work.BoseBoxFock.muLine_const
import Submission.Work.BoseBoxFock.muLine_smul_ae
import Submission.Work.BoseBoxFock.muLine_sub_ae
import Submission.Work.BoseBoxFock.pairSlot_twoDouble
import Submission.Work.BoseBoxFock.q1word_sandwich
import Submission.Work.BoseBoxFock.slotWeighted_abs_aQn0_le
import Submission.Work.BoseBoxFock.slotWeighted_abs_n0_le
import Submission.Work.BoseBoxFock.sum_aP_aQn0_eq_zero
import Submission.Work.BoseBoxFock.sum_aP_chiCube_aPn0_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "Sp" => EuclideanSpace ℝ (Fin 3)
open Submission.BoseGases

/-! ## Elementary identities for the two row weights -/

lemma chiScale_sq_eq_one_add_chiCube (ℓ : ℝ) (z : Sp) :
    Submission.BoseGases.chiScale ℓ z ^ 2 = 1 + chiCube ℓ z := by
  rw [show Submission.BoseGases.chiScale ℓ z = Work.BoseK15.corpusBox.chiLam ℓ z from rfl]
  simp only [chiCube]
  ring

lemma chiW_eq_scale (ℓ : ℝ) (N : ℕ) (z : Sp) :
    chiW ℓ N z = Submission.BoseGases.chiScale ℓ z ^ 2 - 1 - (chiTail ℓ N z).re := by
  rw [show Submission.BoseGases.chiScale ℓ z = Work.BoseK15.corpusBox.chiLam ℓ z from rfl]
  simp only [chiW, chiCube]

lemma thW_eq_scale (ℓ : ℝ) (N : ℕ) (z : Sp) :
    thW ℓ N z = Submission.BoseGases.chiScale ℓ z ^ 2 - 1 - (thetaTail ℓ N z).re := by
  rw [show Submission.BoseGases.chiScale ℓ z = Work.BoseK15.corpusBox.chiLam ℓ z from rfl]
  simp only [thW, chiCube]

/-- The pure algebra of the pair-row comparison. -/
lemma pairKeyAlg {W1 W1w c p q f1 f1w t1 t1w χ θ ch : ℝ}
    (hc : c = 1 + ch) (h1 : f1 + t1 = W1 * c) (h2 : f1w + t1w = W1w * c) :
    (W1 * (c - 1 - χ) + W1w * (c - 1 - θ)) * (p + q) - (f1 + f1w) * q
      = (t1 + t1w) * q - (W1 * χ + W1w * θ) * (p + q) + (W1 + W1w) * (ch * p - q) := by
  have h1' : f1 = W1 * (1 + ch) - t1 := by rw [← hc, ← h1]; ring
  have h2' : f1w = W1w * (1 + ch) - t1w := by rw [← hc, ← h2]; ring
  rw [hc, h1', h2']
  ring

/-- A pointwise bound on a weight from a comparison with `W · χ_ℓ²`. -/
lemma weightAbs_le_of_kc {ℓ W A : ℝ} {F : Sp → ℝ}
    (h : ∀ x, |W * Submission.BoseGases.chiScale ℓ x ^ 2 - F x| ≤ A) :
    ∀ x, |F x| ≤ A + |W| * Submission.BoseGases.chiSup ^ 2 := by
  intro x
  have hx := h x
  rw [abs_sub_comm] at hx
  calc |F x| = |(F x - W * Submission.BoseGases.chiScale ℓ x ^ 2) + W * Submission.BoseGases.chiScale ℓ x ^ 2| := by
        ring_nf
    _ ≤ |F x - W * Submission.BoseGases.chiScale ℓ x ^ 2| + |W * Submission.BoseGases.chiScale ℓ x ^ 2| :=
        abs_add_le _ _
    _ ≤ A + |W| * Submission.BoseGases.chiSup ^ 2 := by
        refine add_le_add hx ?_
        have hsq : |Submission.BoseGases.chiScale ℓ x ^ 2| = Submission.BoseGases.chiScale ℓ x ^ 2 :=
          abs_of_nonneg (sq_nonneg _)
        rw [abs_mul, hsq]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg W)
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (Submission.BoseGases.abs_chiScale_le_chiSup ℓ x) 2

/-! ## Integrability helpers for slot weights -/

private lemma integrableOn_slotU {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {A : Submission.BoseGases.X n → ℝ} (hAc : Continuous A) {u : Sp → ℝ} (hum : Measurable u)
    {K : ℝ} (hu : ∀ z, |u z| ≤ K) {B : Submission.BoseGases.X n → ℝ} (hBc : Continuous B) :
    IntegrableOn (fun x : Submission.BoseGases.X n => A x * (u (x i) * B x))
      (Submission.BoseGases.abox n ℓ) volume := by
  refine (integrableOn_cont_slot_bounded (n := n) (ℓ := ℓ) hℓ i (A := A) (B := B)
    hAc hBc hum hu).congr ?_
  filter_upwards with x
  ring

private lemma integrableOn_slotAbs {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) {F : Sp → ℝ}
    (hFm : AEStronglyMeasurable F (volume.restrict (Submission.BoseGases.acube ℓ)))
    {C : ℝ} (hFb : ∀ z ∈ Submission.BoseGases.acube ℓ, |F z| ≤ C)
    {B : Submission.BoseGases.X n → ℝ} (hBc : Continuous B) :
    IntegrableOn (fun x : Submission.BoseGases.X n =>
        |Submission.BoseGases.aP ℓ i Φ x| * F (x i) * B x)
      (Submission.BoseGases.abox n ℓ) volume := by
  have hS : Continuous (fun x : Submission.BoseGases.X n =>
      |Submission.BoseGases.aP ℓ i Φ x| * B x) :=
    ((Submission.BoseGases.aP_continuous hℓ i hΦc).abs).mul hBc
  refine (Submission.BoseGases.integrableOn_slot_fibre (N := n) (ℓ := ℓ) hℓ i hFm hFb hS).congr ?_
  filter_upwards with x
  ring

/-- The absolute value of an a.e. strongly measurable function is a.e. strongly measurable. -/
private lemma aesAbs {ℓ : ℝ} {f : Sp → ℝ}
    (h : AEStronglyMeasurable f (volume.restrict (Submission.BoseGases.acube ℓ))) :
    AEStronglyMeasurable (fun z => |f z|) (volume.restrict (Submission.BoseGases.acube ℓ)) :=
  (h.norm).congr (Filter.Eventually.of_forall (fun z => Real.norm_eq_abs (f z)))

private lemma integrableOn_slotFibre {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) {F : Sp → ℝ}
    (hFm : AEStronglyMeasurable F (volume.restrict (Submission.BoseGases.acube ℓ))) {C : ℝ}
    (hFb : ∀ z ∈ Submission.BoseGases.acube ℓ, |F z| ≤ C)
    {B : Submission.BoseGases.X n → ℝ} (hBc : Continuous B) :
    IntegrableOn (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.aP ℓ i Φ x * (F (x i) * B x)) (Submission.BoseGases.abox n ℓ) volume := by
  have hS : Continuous (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ i Φ x * B x) :=
    (Submission.BoseGases.aP_continuous hℓ i hΦc).mul hBc
  refine (Submission.BoseGases.integrableOn_slot_fibre (N := n) (ℓ := ℓ) hℓ i hFm hFb hS).congr ?_
  filter_upwards with x
  ring

/-! ## The localised fibres as functions of one variable -/

lemma fibre_g0_aem {v : Sp → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : Sp) R) :
    AEStronglyMeasurable
      (fun z => Submission.BoseGases.w1Fibre ℓ
        (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) z)
      (volume.restrict (Submission.BoseGases.acube ℓ)) := by
  have hfac := Submission.BoseGases.fibre_acube_aem (ℓ := ℓ) (h := Submission.BoseGases.g0 v h)
    (Submission.BoseGases.g0_integrable hR hv_supp h)
  have hfun : (fun z => Submission.BoseGases.w1Fibre ℓ
        (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) z)
      = fun z => ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) z y := by
    funext z
    simp only [Submission.BoseGases.w1Fibre]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun y => wLocKC_wLoc_zero_eq_wPair ℓ (Submission.BoseGases.g0 v h) z y))
  rw [hfun]
  exact hfac

lemma fibre_g0w0_aem {v : Sp → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ} (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : Sp) R) :
    AEStronglyMeasurable
      (fun z => Submission.BoseGases.w1Fibre ℓ
        (Submission.BoseGases.wLoc ℓ
          (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z) 0) z)
      (volume.restrict (Submission.BoseGases.acube ℓ)) := by
  have hfac := Submission.BoseGases.fibre_acube_aem (ℓ := ℓ)
    (h := fun z => Submission.BoseGases.g0 v h z * Classical.choose h z)
    (Submission.BoseGases.g0w0_integrable hR hv hvrad hv_supp h)
  have hfun : (fun z => Submission.BoseGases.w1Fibre ℓ
        (Submission.BoseGases.wLoc ℓ
          (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z) 0) z)
      = fun z => ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wPair ℓ
            (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z) z y := by
    funext z
    simp only [Submission.BoseGases.w1Fibre]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun y => wLocKC_wLoc_zero_eq_wPair ℓ
        (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z) z y))
  rw [hfun]
  exact hfac

/-- The fibre of the `g₂`-kernel is the sum of the two fibres. -/
lemma w1Fibre_g2_split_loc {ℓ : ℝ} {v : Sp → ℝ} {R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : Sp) R) (h : Work.UBB.ScatSol v)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (z : Sp) :
    Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0) z
      = Submission.BoseGases.w1Fibre ℓ
          (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) z
        + Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ
            (fun w => Submission.BoseGases.g0 v h w * Classical.choose h w) 0) z := by
  have hloc1 : Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0
      = Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h) := by
    funext x y
    exact wLocKC_wLoc_zero_eq_wPair ℓ (Submission.BoseGases.g2 v h) x y
  have hloc2 : Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0
      = Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) := by
    funext x y
    exact wLocKC_wLoc_zero_eq_wPair ℓ (Submission.BoseGases.g0 v h) x y
  have hloc3 : Submission.BoseGases.wLoc ℓ
        (fun w => Submission.BoseGases.g0 v h w * Classical.choose h w) 0
      = Submission.BoseGases.wPairC ℓ
          (fun w => Submission.BoseGases.g0 v h w * Classical.choose h w) := by
    funext x y
    exact wLocKC_wLoc_zero_eq_wPair ℓ
      (fun w => Submission.BoseGases.g0 v h w * Classical.choose h w) x y
  rw [hloc1, hloc2, hloc3]
  exact Submission.BoseGases.w1Fibre_g2_split hℓ hR hv hvrad hv_supp h hRℓ z

lemma fibre_g2_aem {v : Sp → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ} (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : Sp) R) :
    AEStronglyMeasurable
      (fun z => Submission.BoseGases.w1Fibre ℓ
        (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0) z)
      (volume.restrict (Submission.BoseGases.acube ℓ)) := by
  have hfac := Submission.BoseGases.fibre_acube_aem (ℓ := ℓ) (h := Submission.BoseGases.g2 v h)
    (Submission.BoseGases.g2_integrable hR hv hvrad hv_supp h)
  have hfun : (fun z => Submission.BoseGases.w1Fibre ℓ
        (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0) z)
      = fun z => ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wPair ℓ (Submission.BoseGases.g2 v h) z y := by
    funext z
    simp only [Submission.BoseGases.w1Fibre]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun y => wLocKC_wLoc_zero_eq_wPair ℓ (Submission.BoseGases.g2 v h) z y))
  rw [hfun]
  exact hfac

/-! ## The main comparison -/

theorem chiRow_compareSharp2 {n : ℕ} {ℓ μ R : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {Φ : Submission.BoseGases.X n → ℝ} {N : ℕ} {δ A W1 W1w 𝓜 : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ) (hav : 0 < BoseGases.a v) (hR : 0 < R) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hΦc : Continuous Φ) (hW1 : W1 = Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h)) 0) (hW1w : W1w = Work.BoseFixR.chat (Submission.BoseGases.wScaled ℓ (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z)) 0) (hδχ : ∀ x, ‖Work.BoseBoxFock.chiTail ℓ N x‖ ≤ δ) (hδθ : ∀ x, ‖Work.BoseBoxFock.thetaTail ℓ N x‖ ≤ δ) (hδ0 : 0 ≤ δ) (hA : 0 ≤ A) (hKC : ∀ x, |W1 * Submission.BoseGases.chiScale ℓ x ^ 2 - Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) x| ≤ A) (hKCw : ∀ x, |W1w * Submission.BoseGases.chiScale ℓ x ^ 2 - Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z) 0) x| ≤ A) (hKCm : |(ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.acube ℓ, Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) x) - W1| ≤ A) (hKCmw : |(ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.acube ℓ, Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z) 0) x) - W1w| ≤ A) (hg2 : ∀ z, Submission.BoseGases.g2 v h z = Submission.BoseGases.g0 v h z + Submission.BoseGases.g0 v h z * Classical.choose h z) (hn : (n : ℝ) ≤ 2 * μ * ℓ ^ 3) (hMM : Submission.BoseGases.cnPlus ℓ Φ ≤ 𝓜 * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)) (hMM0 : 0 ≤ 𝓜) : ((ℓ ^ 3)⁻¹ * W1 * Work.BoseBoxFock.pairSlot n ℓ (Work.BoseBoxFock.chiW ℓ N) Φ + (ℓ ^ 3)⁻¹ * W1w * Work.BoseBoxFock.pairSlot n ℓ (Work.BoseBoxFock.thW ℓ N) Φ - μ * W1 * Work.BoseBoxFock.muForm n ℓ (Work.BoseBoxFock.chiW ℓ N) Φ) ≤ (Submission.BoseGases.q1word (N := n) ℓ μ (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0) Φ + (2 * (ℓ ^ 3)⁻¹ * (4 * A + δ * (|W1| + |W1w|)) * (n : ℝ) ^ 2 + 2 * μ * (A + δ * |W1|) * Real.sqrt ((n : ℝ) * 𝓜) + 2 * μ * |W1| * δ * (n : ℝ)) * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)) := by
  classical
  -- ============ 0. the two row weights ============
  obtain ⟨K1, hK10, hK1b⟩ := chiW_abs_bound hℓ N
  obtain ⟨K2, hK20, hK2b⟩ := thW_abs_bound hℓ N
  have hχWm : Measurable (chiW ℓ N) := chiW_measurable ℓ N
  have hθWm : Measurable (thW ℓ N) := thW_measurable_box ℓ N
  -- ============ 1. abbreviations ============
  set H : ℝ := ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 with hH
  have hH0 : 0 ≤ H := by
    rw [hH]
    exact integral_nonneg (fun x => sq_nonneg _)
  let n0 : Submission.BoseGases.X n → ℝ :=
    fun y => ∑ j : Fin n, Submission.BoseGases.aP ℓ j Φ y
  have hn0c : Continuous n0 :=
    continuous_finsetSum _ (fun j _ => Submission.BoseGases.aP_continuous hℓ j hΦc)
  let χT : Sp → ℝ := fun z => (chiTail ℓ N z).re
  let θT : Sp → ℝ := fun z => (thetaTail ℓ N z).re
  let f1 : Sp → ℝ := fun z =>
    Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) z
  let f1w : Sp → ℝ := fun z =>
    Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ
      (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z) 0) z
  let f2 : Sp → ℝ := fun z =>
    Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0) z
  let τ1 : Sp → ℝ := fun z => W1 * Submission.BoseGases.chiScale ℓ z ^ 2 - f1 z
  let τ1w : Sp → ℝ := fun z => W1w * Submission.BoseGases.chiScale ℓ z ^ 2 - f1w z
  let Wf : Sp → ℝ := fun z => W1 * chiW ℓ N z + W1w * thW ℓ N z
  let Af : (Sp → ℝ) → ℝ := fun w => ∑ i : Fin n, ∑ j : Fin n,
    ∫ x in Submission.BoseGases.abox n ℓ,
      Submission.BoseGases.aP ℓ i Φ x * w (x i) * (Submission.BoseGases.aP ℓ j Φ x)
  let AfP : (Sp → ℝ) → ℝ := fun w => ∑ i : Fin n, ∑ j : Fin n,
    ∫ x in Submission.BoseGases.abox n ℓ,
      Submission.BoseGases.aP ℓ i Φ x * (w (x i) * (Submission.BoseGases.aP ℓ j Φ x))
  let Bf : (Sp → ℝ) → ℝ := fun w => ∑ i : Fin n,
    ∫ x in Submission.BoseGases.abox n ℓ,
      Submission.BoseGases.aP ℓ i Φ x * (w (x i) * n0 x)
  let S2 : ℝ := ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
    Submission.BoseGases.aP ℓ i Φ x * (f2 (x i) * (Submission.BoseGases.aQ ℓ i n0 x))
  -- ============ 2. measurability and bounds ============
  have hχTm : Measurable χT :=
    Complex.continuous_re.measurable.comp (chiTail_measurable ℓ N)
  have hθTm : Measurable θT :=
    Complex.continuous_re.measurable.comp (thetaTail_measurable_box ℓ N)
  have hχTaem : AEStronglyMeasurable χT (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    hχTm.aestronglyMeasurable
  have hθTaem : AEStronglyMeasurable θT (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    hθTm.aestronglyMeasurable
  have hf1aem : AEStronglyMeasurable f1 (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    fibre_g0_aem (ℓ := ℓ) hR hv_supp
  have hf1waem : AEStronglyMeasurable f1w (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    fibre_g0w0_aem (ℓ := ℓ) hR hv hvrad hv_supp
  have hf2aem : AEStronglyMeasurable f2 (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    fibre_g2_aem (ℓ := ℓ) hR hv hvrad hv_supp
  have hτ1aem : AEStronglyMeasurable τ1 (volume.restrict (Submission.BoseGases.acube ℓ)) := by
    have hc : Continuous (fun z : Sp => W1 * Submission.BoseGases.chiScale ℓ z ^ 2) :=
      continuous_const.mul ((Submission.BoseGases.chiScale_continuous ℓ).pow 2)
    exact (hc.aestronglyMeasurable).sub hf1aem
  have hτ1waem : AEStronglyMeasurable τ1w (volume.restrict (Submission.BoseGases.acube ℓ)) := by
    have hc : Continuous (fun z : Sp => W1w * Submission.BoseGases.chiScale ℓ z ^ 2) :=
      continuous_const.mul ((Submission.BoseGases.chiScale_continuous ℓ).pow 2)
    exact (hc.aestronglyMeasurable).sub hf1waem
  have hχTb : ∀ z, |χT z| ≤ δ :=
    fun z => le_trans (Complex.abs_re_le_norm _) (hδχ z)
  have hθTb : ∀ z, |θT z| ≤ δ :=
    fun z => le_trans (Complex.abs_re_le_norm _) (hδθ z)
  have hf1b : ∀ z, |f1 z| ≤ A + |W1| * Submission.BoseGases.chiSup ^ 2 :=
    weightAbs_le_of_kc (ℓ := ℓ) (W := W1) (A := A) (F := f1) hKC
  have hf1wb : ∀ z, |f1w z| ≤ A + |W1w| * Submission.BoseGases.chiSup ^ 2 :=
    weightAbs_le_of_kc (ℓ := ℓ) (W := W1w) (A := A) (F := f1w) hKCw
  have hτ1b : ∀ z, |τ1 z| ≤ A := fun z => hKC z
  have hτ1wb : ∀ z, |τ1w z| ≤ A := fun z => hKCw z
  have hf2b : ∀ z ∈ Submission.BoseGases.acube ℓ,
      |f2 z| ≤ Submission.BoseGases.chiSup ^ 2 * 2 * (16 * Real.pi * BoseGases.a v) := by
    intro z _
    have hb := Submission.BoseGases.w2c_fibre_acube_abs_le (v := v) (R := R) (ℓ := ℓ)
      hR hv hvrad hv_supp h hℓ hRℓ z
    simpa only [f2, Submission.BoseGases.w1Fibre, wLocKC_wLoc_zero_eq_wPair] using hb
  have hWm : Measurable Wf := by
    have h1 : Measurable (fun z : Sp => W1 * chiW ℓ N z) := hχWm.const_mul W1
    have h2 : Measurable (fun z : Sp => W1w * thW ℓ N z) := hθWm.const_mul W1w
    exact h1.add h2
  have hWb : ∀ z, |Wf z| ≤ |W1| * K1 + |W1w| * K2 := by
    intro z
    calc |Wf z| = |W1 * chiW ℓ N z + W1w * thW ℓ N z| := rfl
      _ ≤ |W1 * chiW ℓ N z| + |W1w * thW ℓ N z| := abs_add_le _ _
      _ = |W1| * |chiW ℓ N z| + |W1w| * |thW ℓ N z| := by simp only [abs_mul]
      _ ≤ |W1| * K1 + |W1w| * K2 :=
          add_le_add (mul_le_mul_of_nonneg_left (hK1b z) (abs_nonneg W1))
            (mul_le_mul_of_nonneg_left (hK2b z) (abs_nonneg W1w))
  -- ============ 3. integrability ============
  have hQc : ∀ i : Fin n, Continuous (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aQ ℓ i n0 x) := fun i =>
    (hn0c.sub (Submission.BoseGases.aP_continuous hℓ i hn0c))
  have hWint : ∀ i : Fin n, IntegrableOn (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ i Φ x * (Wf (x i) * n0 x))
      (Submission.BoseGases.abox n ℓ) volume := fun i =>
    integrableOn_slotU hℓ i (Submission.BoseGases.aP_continuous hℓ i hΦc) hWm hWb hn0c
  have hf2int : ∀ i : Fin n, IntegrableOn (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ i Φ x * (f2 (x i) * (Submission.BoseGases.aQ ℓ i n0 x)))
      (Submission.BoseGases.abox n ℓ) volume := fun i =>
    integrableOn_slotFibre hℓ i hΦc hf2aem hf2b (hQc i)
  -- ============ 4. the pair-slot and q1 reductions ============
  have hLHSred : ((ℓ ^ 3)⁻¹ * W1 * pairSlot n ℓ (chiW ℓ N) Φ
        + (ℓ ^ 3)⁻¹ * W1w * pairSlot n ℓ (thW ℓ N) Φ
        - μ * W1 * muForm n ℓ (chiW ℓ N) Φ)
      = 2 * (ℓ ^ 3)⁻¹ * Bf Wf
        - μ * (W1 * muLine n ℓ (chiW ℓ N) Φ + W1 * muCorr n ℓ (chiW ℓ N) Φ) := by
    rw [chiRow_muForm_decomp hℓ hΦc hχWm hK1b]
    have h1 : pairSlot n ℓ (chiW ℓ N) Φ = 2 * Af (chiW ℓ N) :=
      pairSlot_twoDouble hℓ hΦc hχWm hK1b
    have h2 : pairSlot n ℓ (thW ℓ N) Φ = 2 * Af (thW ℓ N) :=
      pairSlot_twoDouble hℓ hΦc hθWm hK2b
    have hAfP : ∀ w : Sp → ℝ, Af w = AfP w := fun w => by
      dsimp only [Af, AfP]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
    have hlinP : AfP (fun z : Sp => W1 * chiW ℓ N z + W1w * thW ℓ N z)
        = W1 * AfP (chiW ℓ N) + W1w * AfP (thW ℓ N) := by
      dsimp only [AfP]
      exact doubleSlot_lin (n := n) (ℓ := ℓ) hℓ hΦc (w := chiW ℓ N) (w' := thW ℓ N)
        hχWm hθWm hK1b hK2b W1 W1w
    have hlin : Af (fun z : Sp => W1 * chiW ℓ N z + W1w * thW ℓ N z)
        = W1 * Af (chiW ℓ N) + W1w * Af (thW ℓ N) := by
      rw [hAfP (fun z : Sp => W1 * chiW ℓ N z + W1w * thW ℓ N z), hlinP,
        ← hAfP (chiW ℓ N), ← hAfP (thW ℓ N)]
    have hB : Af (fun z : Sp => W1 * chiW ℓ N z + W1w * thW ℓ N z)
        = Bf (fun z : Sp => W1 * chiW ℓ N z + W1w * thW ℓ N z) := by
      dsimp only [Af, Bf]
      exact doubleSlot_n0Form (n := n) (ℓ := ℓ) hℓ hΦc hWm hWb
    rw [h1, h2]
    have hcat : (ℓ ^ 3)⁻¹ * W1 * (2 * Af (chiW ℓ N)) + (ℓ ^ 3)⁻¹ * W1w * (2 * Af (thW ℓ N))
        = 2 * (ℓ ^ 3)⁻¹ * (W1 * Af (chiW ℓ N) + W1w * Af (thW ℓ N)) := by ring
    rw [hcat, ← hlin, hB]
    ring
  have hq1red : Submission.BoseGases.q1word (N := n) ℓ μ
        (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0)
        (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0) Φ
      = 2 * (ℓ ^ 3)⁻¹ * S2 - μ * muLine n ℓ f1 Φ := by
    have hD := q1word_sandwich (n := n) (ℓ := ℓ) (μ := μ) hℓ hv hvrad hR hv_supp h hRℓ hΦc
    rw [hD]
    have hpair : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i Φ x *
            (Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0) (x i)) *
            (Submission.BoseGases.aQ ℓ i (fun y : Submission.BoseGases.X n =>
              ∑ j : Fin n, Submission.BoseGases.aP ℓ j Φ y) x)) = S2 := by
      dsimp only [S2, f2]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
    have hmuLin : muLine n ℓ f1 Φ = 2 * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.aQ ℓ i Φ x) * (f1 (x i)) * (Submission.BoseGases.aP ℓ i Φ x)) := rfl
    have hswap : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.aQ ℓ i Φ x) * (Submission.BoseGases.aP ℓ i Φ x) * (f1 (x i)))
        = (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.aQ ℓ i Φ x) * (f1 (x i)) * (Submission.BoseGases.aP ℓ i Φ x)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
    rw [hpair, hmuLin, hswap]
    ring
  -- ============ 5. the split of `LHS - q1word` ============
  have hsplit : ((ℓ ^ 3)⁻¹ * W1 * pairSlot n ℓ (chiW ℓ N) Φ
        + (ℓ ^ 3)⁻¹ * W1w * pairSlot n ℓ (thW ℓ N) Φ
        - μ * W1 * muForm n ℓ (chiW ℓ N) Φ)
      - (Submission.BoseGases.q1word (N := n) ℓ μ
          (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0)
          (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0) Φ)
      = 2 * (ℓ ^ 3)⁻¹ * (Bf Wf - S2)
        + (- μ * W1 * muLine n ℓ (chiW ℓ N) Φ - μ * W1 * muCorr n ℓ (chiW ℓ N) Φ
            + μ * muLine n ℓ f1 Φ) := by
    rw [hLHSred, hq1red]
    ring
  -- ============ 6. the pointwise key identity ============
  have hWz : ∀ (i : Fin n) (x : Submission.BoseGases.X n),
      Wf (x i) = W1 * (Submission.BoseGases.chiScale ℓ (x i) ^ 2 - 1 - χT (x i))
        + W1w * (Submission.BoseGases.chiScale ℓ (x i) ^ 2 - 1 - θT (x i)) := by
    intro i x
    simp only [Wf, χT, θT, chiW_eq_scale, thW_eq_scale]
  have hkey : ∀ (i : Fin n) (x : Submission.BoseGases.X n),
      Wf (x i) * n0 x - f2 (x i) * (Submission.BoseGases.aQ ℓ i n0 x)
        = (τ1 (x i) + τ1w (x i)) * (Submission.BoseGases.aQ ℓ i n0 x)
          - (W1 * χT (x i) + W1w * θT (x i)) * n0 x
          + (W1 + W1w) * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
              - Submission.BoseGases.aQ ℓ i n0 x) := by
    intro i x
    have hpq : n0 x = Submission.BoseGases.aP ℓ i n0 x + Submission.BoseGases.aQ ℓ i n0 x := by
      simp only [Submission.BoseGases.aQ]
      ring
    have hf2s : f2 (x i) = f1 (x i) + f1w (x i) :=
      w1Fibre_g2_split_loc (ℓ := ℓ) (v := v) (R := R) hℓ hR hv hvrad hv_supp h hRℓ (x i)
    have h1' : f1 (x i) + τ1 (x i) = W1 * Submission.BoseGases.chiScale ℓ (x i) ^ 2 := by
      simp only [τ1, f1]; ring
    have h2' : f1w (x i) + τ1w (x i) = W1w * Submission.BoseGases.chiScale ℓ (x i) ^ 2 := by
      simp only [τ1w, f1w]; ring
    have hc' : Submission.BoseGases.chiScale ℓ (x i) ^ 2 = 1 + chiCube ℓ (x i) :=
      chiScale_sq_eq_one_add_chiCube ℓ (x i)
    rw [hpq, hWz i x, hf2s]
    exact pairKeyAlg hc' h1' h2'
  -- ============ 7. the middle sum vanishes ============
  have hT3 : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ i Φ x
          * ((W1 + W1w) * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
              - Submission.BoseGases.aQ ℓ i n0 x))) = 0 := by
    have hper : ∀ i : Fin n,
        (∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i Φ x
            * ((W1 + W1w) * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                - Submission.BoseGases.aQ ℓ i n0 x)))
          = (W1 + W1w) * (∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i Φ x
                * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                    - Submission.BoseGases.aQ ℓ i n0 x)) := by
      intro i
      rw [show (fun x : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ i Φ x
            * ((W1 + W1w) * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                - Submission.BoseGases.aQ ℓ i n0 x)))
          = fun x : Submission.BoseGases.X n => (W1 + W1w) *
              (Submission.BoseGases.aP ℓ i Φ x
                * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                    - Submission.BoseGases.aQ ℓ i n0 x)) from
        funext (fun x => by ring)]
      rw [integral_const_mul]
    have hsplit2 : ∀ i : Fin n,
        (∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i Φ x
            * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                - Submission.BoseGases.aQ ℓ i n0 x))
          = (∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i Φ x
                * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)))
            - (∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i Φ x * (Submission.BoseGases.aQ ℓ i n0 x)) := by
      intro i
      rw [show (fun x : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ i Φ x
            * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                - Submission.BoseGases.aQ ℓ i n0 x))
          = fun x : Submission.BoseGases.X n =>
              Submission.BoseGases.aP ℓ i Φ x
                * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x))
              - Submission.BoseGases.aP ℓ i Φ x * (Submission.BoseGases.aQ ℓ i n0 x) from
        funext (fun x => by ring)]
      have h1 : Integrable (fun x : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ i Φ x
            * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)))
          (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
        integrableOn_abox_of_continuous hℓ
          ((Submission.BoseGases.aP_continuous hℓ i hΦc).mul
            (((chiCube_cont ℓ).comp (continuous_apply i)).mul
              (Submission.BoseGases.aP_continuous hℓ i hn0c)))
      have h2 : Integrable (fun x : Submission.BoseGases.X n =>
            Submission.BoseGases.aP ℓ i Φ x * (Submission.BoseGases.aQ ℓ i n0 x))
          (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
        integrableOn_abox_of_continuous hℓ
          ((Submission.BoseGases.aP_continuous hℓ i hΦc).mul (hQc i))
      rw [MeasureTheory.integral_sub h1 h2]
    rw [Finset.sum_congr rfl (fun i _ => hper i)]
    rw [← Finset.mul_sum]
    have : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i Φ x
            * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                - Submission.BoseGases.aQ ℓ i n0 x))
        = (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i Φ x
                * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)))
          - (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i Φ x * (Submission.BoseGases.aQ ℓ i n0 x)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => hsplit2 i)
    rw [this, sum_aP_chiCube_aPn0_eq_zero hℓ hΦc, sum_aP_aQn0_eq_zero hℓ hΦc]
    ring
  -- ============ 8. the two estimates of the pair row ============
  have hE1 : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ i Φ x
          * ((τ1 (x i) + τ1w (x i)) * (Submission.BoseGases.aQ ℓ i n0 x)))
      ≤ 2 * A * ((n : ℝ) ^ 2 * H) := by
    have hBm : AEStronglyMeasurable (fun z : Sp => τ1 z + τ1w z)
        (volume.restrict (Submission.BoseGases.acube ℓ)) := hτ1aem.add hτ1waem
    have hBb : ∀ z ∈ Submission.BoseGases.acube ℓ, |τ1 z + τ1w z| ≤ 2 * A := by
      intro z _
      calc |τ1 z + τ1w z| ≤ |τ1 z| + |τ1w z| := abs_add_le _ _
        _ ≤ A + A := add_le_add (hτ1b z) (hτ1wb z)
        _ = 2 * A := by ring
    have habs := slotWeighted_abs_aQn0_le (n := n) (ℓ := ℓ) (Φ := Φ) hℓ hΦc
      (B := fun z : Sp => τ1 z + τ1w z) hBm (K := 2 * A) (by linarith) hBb
    have hle : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i Φ x
            * ((τ1 (x i) + τ1w (x i)) * (Submission.BoseGases.aQ ℓ i n0 x)))
        ≤ ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            |Submission.BoseGases.aP ℓ i Φ x| * |τ1 (x i) + τ1w (x i)|
              * |Submission.BoseGases.aQ ℓ i n0 x| := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      refine integral_mono ?_ ?_ (fun x => ?_)
      · exact integrableOn_slotFibre hℓ i hΦc (hτ1aem.add hτ1waem) (fun z hz => hBb z hz) (hQc i)
      · exact integrableOn_slotAbs (ℓ := ℓ) hℓ i hΦc (F := fun z : Sp => |τ1 z + τ1w z|)
          (aesAbs hBm) (C := 2 * A) (fun z hz => by rw [abs_abs]; exact hBb z hz) ((hQc i).abs)
      · calc (Submission.BoseGases.aP ℓ i Φ x
              * ((τ1 (x i) + τ1w (x i)) * (Submission.BoseGases.aQ ℓ i n0 x)))
            ≤ |Submission.BoseGases.aP ℓ i Φ x
                * ((τ1 (x i) + τ1w (x i)) * (Submission.BoseGases.aQ ℓ i n0 x))| := le_abs_self _
          _ = |Submission.BoseGases.aP ℓ i Φ x| * |τ1 (x i) + τ1w (x i)|
                * |Submission.BoseGases.aQ ℓ i n0 x| := by rw [abs_mul, abs_mul]; ring
    linarith [hle, habs]
  have hE2 : - (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ i Φ x
          * ((W1 * χT (x i) + W1w * θT (x i)) * n0 x))
      ≤ (δ * (|W1| + |W1w|)) * ((n : ℝ) ^ 2 * H) := by
    have hBm : AEStronglyMeasurable (fun z : Sp => W1 * χT z + W1w * θT z)
        (volume.restrict (Submission.BoseGases.acube ℓ)) :=
      ((hχTm.const_mul W1).add (hθTm.const_mul W1w)).aestronglyMeasurable
    have hBb : ∀ z ∈ Submission.BoseGases.acube ℓ, |W1 * χT z + W1w * θT z| ≤ δ * (|W1| + |W1w|) := by
      intro z _
      calc |W1 * χT z + W1w * θT z| ≤ |W1 * χT z| + |W1w * θT z| := abs_add_le _ _
        _ = |W1| * |χT z| + |W1w| * |θT z| := by simp only [abs_mul]
        _ ≤ |W1| * δ + |W1w| * δ :=
            add_le_add (mul_le_mul_of_nonneg_left (hχTb z) (abs_nonneg W1))
              (mul_le_mul_of_nonneg_left (hθTb z) (abs_nonneg W1w))
        _ = δ * (|W1| + |W1w|) := by ring
    have habs := slotWeighted_abs_n0_le (n := n) (ℓ := ℓ) (Φ := Φ) hℓ hΦc
      (B := fun z : Sp => W1 * χT z + W1w * θT z) hBm
      (K := δ * (|W1| + |W1w|)) (mul_nonneg hδ0 (add_nonneg (abs_nonneg W1) (abs_nonneg W1w))) hBb
    have hlow : - (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i Φ x
            * ((W1 * χT (x i) + W1w * θT (x i)) * n0 x))
        ≤ ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            |Submission.BoseGases.aP ℓ i Φ x| * |W1 * χT (x i) + W1w * θT (x i)| * |n0 x| := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [← integral_neg]
      refine integral_mono ?_ ?_ (fun x => ?_)
      · refine (integrableOn_slotFibre hℓ i hΦc hBm (fun z hz => hBb z hz) hn0c).neg
      · exact integrableOn_slotAbs (ℓ := ℓ) hℓ i hΦc
          (F := fun z : Sp => |W1 * χT z + W1w * θT z|) (aesAbs hBm)
          (C := δ * (|W1| + |W1w|)) (fun z hz => by rw [abs_abs]; exact hBb z hz) hn0c.abs
      · calc - (Submission.BoseGases.aP ℓ i Φ x
              * ((W1 * χT (x i) + W1w * θT (x i)) * n0 x))
            ≤ |Submission.BoseGases.aP ℓ i Φ x
                * ((W1 * χT (x i) + W1w * θT (x i)) * n0 x)| := neg_le_abs _
          _ = |Submission.BoseGases.aP ℓ i Φ x| * |W1 * χT (x i) + W1w * θT (x i)| * |n0 x| := by
              rw [abs_mul, abs_mul]; ring
    linarith [hlow, habs]
  -- ============ 9. the pair-row bound ============
  have hpair : 2 * (ℓ ^ 3)⁻¹ * (Bf Wf - S2)
      ≤ (2 * (ℓ ^ 3)⁻¹ * (4 * A + δ * (|W1| + |W1w|)) * (n : ℝ) ^ 2) * H := by
    have hstep1 : Bf Wf - S2 = ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ i Φ x
          * (Wf (x i) * n0 x - f2 (x i) * (Submission.BoseGases.aQ ℓ i n0 x)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← integral_sub (hWint i) (hf2int i)]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
    have hstep2 : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i Φ x
            * (Wf (x i) * n0 x - f2 (x i) * (Submission.BoseGases.aQ ℓ i n0 x)))
        = (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i Φ x
                * ((τ1 (x i) + τ1w (x i)) * (Submission.BoseGases.aQ ℓ i n0 x)))
          - (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i Φ x
                * ((W1 * χT (x i) + W1w * θT (x i)) * n0 x))
          + (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i Φ x
                * ((W1 + W1w) * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                    - Submission.BoseGases.aQ ℓ i n0 x))) := by
      have hper : ∀ i : Fin n,
          (∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i Φ x
              * (Wf (x i) * n0 x - f2 (x i) * (Submission.BoseGases.aQ ℓ i n0 x)))
            = (∫ x in Submission.BoseGases.abox n ℓ,
                Submission.BoseGases.aP ℓ i Φ x
                  * ((τ1 (x i) + τ1w (x i)) * (Submission.BoseGases.aQ ℓ i n0 x)))
              - (∫ x in Submission.BoseGases.abox n ℓ,
                Submission.BoseGases.aP ℓ i Φ x
                  * ((W1 * χT (x i) + W1w * θT (x i)) * n0 x))
              + (∫ x in Submission.BoseGases.abox n ℓ,
                Submission.BoseGases.aP ℓ i Φ x
                  * ((W1 + W1w) * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                      - Submission.BoseGases.aQ ℓ i n0 x))) := by
        intro i
        have hb1 : ∀ z : Sp, |τ1 z + τ1w z| ≤ 2 * A := fun z =>
          le_trans (abs_add_le _ _) (by linarith [hτ1b z, hτ1wb z])
        have hb2 : ∀ z : Sp, |W1 * χT z + W1w * θT z| ≤ δ * (|W1| + |W1w|) := fun z => by
          have h1 : |W1 * χT z + W1w * θT z| ≤ |W1 * χT z| + |W1w * θT z| := abs_add_le _ _
          rw [abs_mul, abs_mul] at h1
          have h2 := mul_le_mul_of_nonneg_left (hχTb z) (abs_nonneg W1)
          have h3 := mul_le_mul_of_nonneg_left (hθTb z) (abs_nonneg W1w)
          linarith [h1, h2, h3]
        have hm1 : Measurable (fun z : Sp => W1 * χT z + W1w * θT z) :=
          (hχTm.const_mul W1).add (hθTm.const_mul W1w)
        rw [show (fun x : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ i Φ x
              * (Wf (x i) * n0 x - f2 (x i) * (Submission.BoseGases.aQ ℓ i n0 x)))
            = fun x : Submission.BoseGases.X n =>
                (Submission.BoseGases.aP ℓ i Φ x
                  * ((τ1 (x i) + τ1w (x i)) * (Submission.BoseGases.aQ ℓ i n0 x))
                - Submission.BoseGases.aP ℓ i Φ x
                  * ((W1 * χT (x i) + W1w * θT (x i)) * n0 x))
              + Submission.BoseGases.aP ℓ i Φ x
                  * ((W1 + W1w) * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                      - Submission.BoseGases.aQ ℓ i n0 x)) from
          funext (fun x => by rw [hkey i x]; ring)]
        have hf : Integrable (fun x : Submission.BoseGases.X n =>
            Submission.BoseGases.aP ℓ i Φ x
              * ((τ1 (x i) + τ1w (x i)) * (Submission.BoseGases.aQ ℓ i n0 x)))
            (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
          integrableOn_slotFibre hℓ i hΦc (hτ1aem.add hτ1waem) (fun z _ => hb1 z) (hQc i)
        have hg : Integrable (fun x : Submission.BoseGases.X n =>
            Submission.BoseGases.aP ℓ i Φ x
              * ((W1 * χT (x i) + W1w * θT (x i)) * n0 x))
            (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
          integrableOn_slotU hℓ i (Submission.BoseGases.aP_continuous hℓ i hΦc) hm1 hb2 hn0c
        have hk : Integrable (fun x : Submission.BoseGases.X n =>
            Submission.BoseGases.aP ℓ i Φ x
              * ((W1 + W1w) * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                  - Submission.BoseGases.aQ ℓ i n0 x)))
            (volume.restrict (Submission.BoseGases.abox n ℓ)) := by
          refine integrableOn_slotU hℓ i (Submission.BoseGases.aP_continuous hℓ i hΦc)
            measurable_const (fun z => le_rfl) ?_
          exact (((chiCube_cont ℓ).comp (continuous_apply i)).mul
            (Submission.BoseGases.aP_continuous hℓ i hn0c)).sub (hQc i)
        have hAB : (∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i Φ x
                * ((τ1 (x i) + τ1w (x i)) * (Submission.BoseGases.aQ ℓ i n0 x))
              - Submission.BoseGases.aP ℓ i Φ x
                * ((W1 * χT (x i) + W1w * θT (x i)) * n0 x))
            = (∫ x in Submission.BoseGases.abox n ℓ,
                Submission.BoseGases.aP ℓ i Φ x
                  * ((τ1 (x i) + τ1w (x i)) * (Submission.BoseGases.aQ ℓ i n0 x)))
              - (∫ x in Submission.BoseGases.abox n ℓ,
                Submission.BoseGases.aP ℓ i Φ x
                  * ((W1 * χT (x i) + W1w * θT (x i)) * n0 x)) :=
          MeasureTheory.integral_sub hf hg
        have hABC : (∫ x in Submission.BoseGases.abox n ℓ,
              (Submission.BoseGases.aP ℓ i Φ x
                * ((τ1 (x i) + τ1w (x i)) * (Submission.BoseGases.aQ ℓ i n0 x))
              - Submission.BoseGases.aP ℓ i Φ x
                * ((W1 * χT (x i) + W1w * θT (x i)) * n0 x))
              + Submission.BoseGases.aP ℓ i Φ x
                  * ((W1 + W1w) * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                      - Submission.BoseGases.aQ ℓ i n0 x)))
            = (∫ x in Submission.BoseGases.abox n ℓ,
                Submission.BoseGases.aP ℓ i Φ x
                  * ((τ1 (x i) + τ1w (x i)) * (Submission.BoseGases.aQ ℓ i n0 x))
                - Submission.BoseGases.aP ℓ i Φ x
                  * ((W1 * χT (x i) + W1w * θT (x i)) * n0 x))
              + (∫ x in Submission.BoseGases.abox n ℓ,
                Submission.BoseGases.aP ℓ i Φ x
                  * ((W1 + W1w) * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                      - Submission.BoseGases.aQ ℓ i n0 x))) :=
          MeasureTheory.integral_add (f := fun x : Submission.BoseGases.X n =>
              Submission.BoseGases.aP ℓ i Φ x
                * ((τ1 (x i) + τ1w (x i)) * (Submission.BoseGases.aQ ℓ i n0 x))
              - Submission.BoseGases.aP ℓ i Φ x
                * ((W1 * χT (x i) + W1w * θT (x i)) * n0 x))
            (g := fun x : Submission.BoseGases.X n =>
              Submission.BoseGases.aP ℓ i Φ x
                * ((W1 + W1w) * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                    - Submission.BoseGases.aQ ℓ i n0 x))) (hf.sub hg) hk
        rw [hABC, hAB]
      have hsum : (∑ i : Fin n, (∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i Φ x
              * (Wf (x i) * n0 x - f2 (x i) * (Submission.BoseGases.aQ ℓ i n0 x))))
          = (∑ i : Fin n, ((∫ x in Submission.BoseGases.abox n ℓ,
                Submission.BoseGases.aP ℓ i Φ x
                  * ((τ1 (x i) + τ1w (x i)) * (Submission.BoseGases.aQ ℓ i n0 x)))
              - (∫ x in Submission.BoseGases.abox n ℓ,
                Submission.BoseGases.aP ℓ i Φ x
                  * ((W1 * χT (x i) + W1w * θT (x i)) * n0 x))
              + (∫ x in Submission.BoseGases.abox n ℓ,
                Submission.BoseGases.aP ℓ i Φ x
                  * ((W1 + W1w) * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                      - Submission.BoseGases.aQ ℓ i n0 x))))) :=
        Finset.sum_congr rfl (fun i _ => hper i)
      rw [hsum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hstep3 : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i Φ x
            * ((W1 + W1w) * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                - Submission.BoseGases.aQ ℓ i n0 x))) = 0 := by
      -- factor the constant out of the sum
      have hper : ∀ i : Fin n,
          (∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i Φ x
              * ((W1 + W1w) * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                  - Submission.BoseGases.aQ ℓ i n0 x)))
            = (W1 + W1w) * (∫ x in Submission.BoseGases.abox n ℓ,
                Submission.BoseGases.aP ℓ i Φ x
                  * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                      - Submission.BoseGases.aQ ℓ i n0 x)) := by
        intro i
        rw [show (fun x : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ i Φ x
              * ((W1 + W1w) * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                  - Submission.BoseGases.aQ ℓ i n0 x)))
            = fun x : Submission.BoseGases.X n => (W1 + W1w) *
                (Submission.BoseGases.aP ℓ i Φ x
                  * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                      - Submission.BoseGases.aQ ℓ i n0 x)) from
          funext (fun x => by ring)]
        rw [integral_const_mul]
      rw [Finset.sum_congr rfl (fun i _ => hper i), ← Finset.mul_sum]
      -- split
      have hsplit2 : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ i Φ x
              * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                  - Submission.BoseGases.aQ ℓ i n0 x))
          = (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
                Submission.BoseGases.aP ℓ i Φ x
                  * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)))
            - (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
                Submission.BoseGases.aP ℓ i Φ x * (Submission.BoseGases.aQ ℓ i n0 x)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [show (fun x : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ i Φ x
              * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)
                  - Submission.BoseGases.aQ ℓ i n0 x))
            = fun x : Submission.BoseGases.X n =>
                Submission.BoseGases.aP ℓ i Φ x
                  * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x))
                - Submission.BoseGases.aP ℓ i Φ x * (Submission.BoseGases.aQ ℓ i n0 x) from
          funext (fun x => by ring)]
        have h1 : Integrable (fun x : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ i Φ x
              * (chiCube ℓ (x i) * (Submission.BoseGases.aP ℓ i n0 x)))
            (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
          integrableOn_abox_of_continuous hℓ
            ((Submission.BoseGases.aP_continuous hℓ i hΦc).mul
              (((chiCube_cont ℓ).comp (continuous_apply i)).mul
                (Submission.BoseGases.aP_continuous hℓ i hn0c)))
        have h2 : Integrable (fun x : Submission.BoseGases.X n =>
              Submission.BoseGases.aP ℓ i Φ x * (Submission.BoseGases.aQ ℓ i n0 x))
            (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
          integrableOn_abox_of_continuous hℓ
            ((Submission.BoseGases.aP_continuous hℓ i hΦc).mul (hQc i))
        rw [MeasureTheory.integral_sub h1 h2]
      rw [hsplit2, sum_aP_chiCube_aPn0_eq_zero hℓ hΦc, sum_aP_aQn0_eq_zero hℓ hΦc]
      ring
    have hbound : Bf Wf - S2 ≤ (4 * A + δ * (|W1| + |W1w|)) * ((n : ℝ) ^ 2 * H) := by
      rw [hstep1, hstep2, hstep3]
      have h2A : 2 * A * ((n : ℝ) ^ 2 * H) ≤ 4 * A * ((n : ℝ) ^ 2 * H) := by
        have hX : 0 ≤ ((n : ℝ) ^ 2 * H) := mul_nonneg (by positivity) hH0
        exact mul_le_mul_of_nonneg_right (by linarith : 2 * A ≤ 4 * A) hX
      linarith [hE1, hE2, h2A]
    have hcoef : 0 ≤ 2 * (ℓ ^ 3)⁻¹ := by positivity
    calc 2 * (ℓ ^ 3)⁻¹ * (Bf Wf - S2)
        ≤ 2 * (ℓ ^ 3)⁻¹ * ((4 * A + δ * (|W1| + |W1w|)) * ((n : ℝ) ^ 2 * H)) :=
          mul_le_mul_of_nonneg_left hbound hcoef
      _ = (2 * (ℓ ^ 3)⁻¹ * (4 * A + δ * (|W1| + |W1w|)) * (n : ℝ) ^ 2) * H := by ring
  -- ============ 10. the mu-row bound ============
  have hmu_id : - W1 * muLine n ℓ (chiW ℓ N) Φ + muLine n ℓ f1 Φ
      = - muLine n ℓ τ1 Φ + W1 * muLine n ℓ χT Φ := by
    have hs : muLine n ℓ (fun z : Sp => W1 * chiW ℓ N z) Φ
        = W1 * muLine n ℓ (chiW ℓ N) Φ :=
      muLine_smul_ae (n := n) (ℓ := ℓ) hℓ hΦc (w := chiW ℓ N)
        hχWm.aestronglyMeasurable (fun z _ => hK1b z) W1
    have hsub : muLine n ℓ (fun z : Sp => W1 * chiW ℓ N z - f1 z) Φ
        = muLine n ℓ (fun z : Sp => W1 * chiW ℓ N z) Φ - muLine n ℓ f1 Φ :=
      muLine_sub_ae (n := n) (ℓ := ℓ) hℓ hΦc (w := fun z : Sp => W1 * chiW ℓ N z)
        (w' := f1) (hχWm.const_mul W1).aestronglyMeasurable hf1aem
        (fun z _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK1b z) (abs_nonneg W1))
        (fun z _ => hf1b z)
    have hpt : (fun z : Sp => W1 * chiW ℓ N z - f1 z) = fun z : Sp => (τ1 z - W1) - W1 * χT z := by
      funext z
      simp only [τ1, f1, χT, chiW_eq_scale]
      ring
    have hsub2 : muLine n ℓ (fun z : Sp => (τ1 z - W1) - W1 * χT z) Φ
        = muLine n ℓ (fun z : Sp => τ1 z - W1) Φ - muLine n ℓ (fun z : Sp => W1 * χT z) Φ :=
      muLine_sub_ae (n := n) (ℓ := ℓ) hℓ hΦc (w := fun z : Sp => τ1 z - W1)
        (w' := fun z : Sp => W1 * χT z)
        ((hτ1aem.sub aestronglyMeasurable_const)) ((hχTaem.const_mul W1))
        (fun z _ => by
          calc |τ1 z - W1| ≤ |τ1 z| + |W1| := abs_sub_le_iff.mpr
                ⟨by linarith [le_abs_self (τ1 z), neg_le_abs W1],
                 by linarith [le_abs_self W1, neg_le_abs (τ1 z)]⟩
            _ ≤ A + |W1| := add_le_add (hτ1b z) le_rfl)
        (fun z _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hχTb z) (abs_nonneg W1))
    have hsub3 : muLine n ℓ (fun z : Sp => τ1 z - W1) Φ
        = muLine n ℓ τ1 Φ - muLine n ℓ (fun _ : Sp => W1) Φ :=
      muLine_sub_ae (n := n) (ℓ := ℓ) hℓ hΦc (w := τ1) (w' := fun _ : Sp => W1)
        (K := A) (K' := |W1|) hτ1aem aestronglyMeasurable_const (fun z _ => hτ1b z)
        (fun z _ => by simp)
    have hc : muLine n ℓ (fun _ : Sp => W1) Φ = 0 := muLine_const hℓ hΦc W1
    have hs2 : muLine n ℓ (fun z : Sp => W1 * χT z) Φ = W1 * muLine n ℓ χT Φ :=
      muLine_smul_ae (n := n) (ℓ := ℓ) hℓ hΦc (w := χT) hχTaem (fun z _ => hχTb z) W1
    have hkey : muLine n ℓ (fun z : Sp => W1 * chiW ℓ N z - f1 z) Φ
        = muLine n ℓ τ1 Φ - W1 * muLine n ℓ χT Φ := by
      rw [hpt, hsub2, hsub3, hc, hs2]
      ring
    have hkey' : muLine n ℓ (fun z : Sp => W1 * chiW ℓ N z - f1 z) Φ
        = W1 * muLine n ℓ (chiW ℓ N) Φ - muLine n ℓ f1 Φ := by
      rw [hsub, hs]
    linarith [hkey, hkey']
  have hml : - W1 * muLine n ℓ (chiW ℓ N) Φ + muLine n ℓ f1 Φ
      ≤ (2 * A + 2 * |W1| * δ)
        * Real.sqrt (Submission.BoseGases.cS1 ℓ Φ * Submission.BoseGases.cnPlus ℓ Φ) := by
    rw [hmu_id]
    have ha : - muLine n ℓ τ1 Φ
        ≤ 2 * A * Real.sqrt (Submission.BoseGases.cS1 ℓ Φ * Submission.BoseGases.cnPlus ℓ Φ) :=
      le_trans (neg_le_abs _) (muLine_abs_le hℓ hΦc hτ1b hA)
    have hb : W1 * muLine n ℓ χT Φ
        ≤ 2 * |W1| * δ
          * Real.sqrt (Submission.BoseGases.cS1 ℓ Φ * Submission.BoseGases.cnPlus ℓ Φ) := by
      have h1 : W1 * muLine n ℓ χT Φ ≤ |W1| * |muLine n ℓ χT Φ| := by
        rw [← abs_mul]
        exact le_abs_self _
      have h2 : |W1| * |muLine n ℓ χT Φ|
          ≤ |W1| * (2 * δ
            * Real.sqrt (Submission.BoseGases.cS1 ℓ Φ * Submission.BoseGases.cnPlus ℓ Φ)) :=
        mul_le_mul_of_nonneg_left (muLine_abs_le hℓ hΦc hχTb hδ0) (abs_nonneg W1)
      calc W1 * muLine n ℓ χT Φ
          ≤ |W1| * (2 * δ
            * Real.sqrt (Submission.BoseGases.cS1 ℓ Φ * Submission.BoseGases.cnPlus ℓ Φ)) :=
            le_trans h1 h2
        _ = 2 * |W1| * δ
            * Real.sqrt (Submission.BoseGases.cS1 ℓ Φ * Submission.BoseGases.cnPlus ℓ Φ) := by
            ring
    have hdist : 2 * A * Real.sqrt (Submission.BoseGases.cS1 ℓ Φ * Submission.BoseGases.cnPlus ℓ Φ)
          + 2 * |W1| * δ
              * Real.sqrt (Submission.BoseGases.cS1 ℓ Φ * Submission.BoseGases.cnPlus ℓ Φ)
        = (2 * A + 2 * |W1| * δ)
          * Real.sqrt (Submission.BoseGases.cS1 ℓ Φ * Submission.BoseGases.cnPlus ℓ Φ) := by
      ring
    linarith [ha, hb, hdist]
  have hsq : Real.sqrt (Submission.BoseGases.cS1 ℓ Φ * Submission.BoseGases.cnPlus ℓ Φ)
      ≤ Real.sqrt ((n : ℝ) * 𝓜) * H := by
    have hcs := Submission.BoseGases.cS1_le_norm_sq (N := n) (ℓ := ℓ) hℓ hΦc
    have hcn0 : 0 ≤ Submission.BoseGases.cnPlus ℓ Φ := Submission.BoseGases.cnPlus_nonneg
    have hnl : 0 ≤ (n : ℝ) * H := mul_nonneg (Nat.cast_nonneg n) hH0
    have hmul : Submission.BoseGases.cS1 ℓ Φ * Submission.BoseGases.cnPlus ℓ Φ
        ≤ ((n : ℝ) * 𝓜) * H ^ 2 := by
      calc Submission.BoseGases.cS1 ℓ Φ * Submission.BoseGases.cnPlus ℓ Φ
          ≤ ((n : ℝ) * H) * (𝓜 * H) := mul_le_mul hcs hMM hcn0 hnl
        _ = ((n : ℝ) * 𝓜) * H ^ 2 := by ring
    calc Real.sqrt (Submission.BoseGases.cS1 ℓ Φ * Submission.BoseGases.cnPlus ℓ Φ)
        ≤ Real.sqrt (((n : ℝ) * 𝓜) * H ^ 2) := Real.sqrt_le_sqrt hmul
      _ = Real.sqrt ((n : ℝ) * 𝓜) * H := by
          rw [Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg n) hMM0), Real.sqrt_sq hH0]
  have hpint : |∫ z in Submission.BoseGases.acube ℓ, chiW ℓ N z| ≤ δ * ℓ ^ 3 := by
    have hcd : chiW ℓ N = fun z : Sp => chiCube ℓ z - χT z := rfl
    rw [hcd, integral_sub]
    · rw [integral_chiCube_acube hℓ, zero_sub, abs_neg]
      calc |∫ z in Submission.BoseGases.acube ℓ, χT z|
          ≤ ∫ z in Submission.BoseGases.acube ℓ, |χT z| := abs_integral_le_integral_abs
        _ ≤ ∫ z in Submission.BoseGases.acube ℓ, δ := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => abs_nonneg _))
              (integrableOn_const (by rw [Submission.BoseGases.acube_volume ℓ hℓ.le]; simp))
              (Filter.Eventually.of_forall (fun z => hχTb z))
        _ = δ * ℓ ^ 3 := Submission.BoseGases.integral_const_acube ℓ hℓ δ
    · exact Submission.BoseGases.integrableOn_acube_of_continuous hℓ (chiCube_cont ℓ)
    · refine IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
        hχTm.aestronglyMeasurable.restrict δ ?_
      rw [ae_restrict_iff' (Submission.BoseGases.acube_measurable ℓ)]
      exact Filter.Eventually.of_forall (fun z _ => by simpa [Real.norm_eq_abs] using hχTb z)
  have hcorr : |muCorr n ℓ (chiW ℓ N) Φ| ≤ 2 * δ * ((n : ℝ) * H) := by
    have heq := chiRow_muCorr_eq (n := n) (ℓ := ℓ) hℓ hΦc hχWm hK1b
    have hcS : 0 ≤ (ℓ ^ 3)⁻¹ * Submission.BoseGases.cS1 ℓ Φ :=
      mul_nonneg (by positivity) Submission.BoseGases.cS1_nonneg
    have h2 : |(ℓ ^ 3)⁻¹ * Submission.BoseGases.cS1 ℓ Φ|
        = (ℓ ^ 3)⁻¹ * Submission.BoseGases.cS1 ℓ Φ := abs_of_nonneg hcS
    rw [heq, abs_mul, h2]
    have h1 : |2 * ∫ z in Submission.BoseGases.acube ℓ, chiW ℓ N z| ≤ 2 * (δ * ℓ ^ 3) := by
      rw [abs_mul]
      have h2' : |(2 : ℝ)| = 2 := abs_of_nonneg (by norm_num)
      rw [h2']
      linarith [hpint]
    have h3 : 2 * (δ * ℓ ^ 3) * ((ℓ ^ 3)⁻¹ * Submission.BoseGases.cS1 ℓ Φ)
        = 2 * δ * Submission.BoseGases.cS1 ℓ Φ := by
      rw [show 2 * (δ * ℓ ^ 3) * ((ℓ ^ 3)⁻¹ * Submission.BoseGases.cS1 ℓ Φ)
          = (2 * δ) * (ℓ ^ 3 * (ℓ ^ 3)⁻¹) * Submission.BoseGases.cS1 ℓ Φ from by ring]
      rw [mul_inv_cancel₀ (ne_of_gt (by positivity : (0 : ℝ) < ℓ ^ 3))]
      ring
    have hcs' := Submission.BoseGases.cS1_le_norm_sq (N := n) (ℓ := ℓ) hℓ hΦc
    calc |2 * ∫ z in Submission.BoseGases.acube ℓ, chiW ℓ N z|
          * ((ℓ ^ 3)⁻¹ * Submission.BoseGases.cS1 ℓ Φ)
        ≤ (2 * (δ * ℓ ^ 3)) * ((ℓ ^ 3)⁻¹ * Submission.BoseGases.cS1 ℓ Φ) :=
          mul_le_mul_of_nonneg_right h1 hcS
      _ = 2 * δ * Submission.BoseGases.cS1 ℓ Φ := h3
      _ ≤ 2 * δ * ((n : ℝ) * H) := by
          refine mul_le_mul_of_nonneg_left hcs' ?_
          linarith [hδ0]
  have hmu : (- μ * W1 * muLine n ℓ (chiW ℓ N) Φ - μ * W1 * muCorr n ℓ (chiW ℓ N) Φ
        + μ * muLine n ℓ f1 Φ)
      ≤ (2 * μ * (A + δ * |W1|) * Real.sqrt ((n : ℝ) * 𝓜) + 2 * μ * |W1| * δ * (n : ℝ)) * H := by
    have hA1 : μ * (- W1 * muLine n ℓ (chiW ℓ N) Φ + muLine n ℓ f1 Φ)
        ≤ μ * ((2 * A + 2 * |W1| * δ) * (Real.sqrt ((n : ℝ) * 𝓜) * H)) := by
      refine mul_le_mul_of_nonneg_left ?_ hμ.le
      refine le_trans hml ?_
      exact mul_le_mul_of_nonneg_left hsq (by nlinarith [hA, abs_nonneg W1, hδ0])
    have hA2 : - μ * W1 * muCorr n ℓ (chiW ℓ N) Φ ≤ μ * |W1| * (2 * δ * ((n : ℝ) * H)) := by
      have h1 : - μ * W1 * muCorr n ℓ (chiW ℓ N) Φ
          ≤ |μ * W1 * muCorr n ℓ (chiW ℓ N) Φ| := by
        rw [show - μ * W1 * muCorr n ℓ (chiW ℓ N) Φ
            = - (μ * W1 * muCorr n ℓ (chiW ℓ N) Φ) from by ring]
        exact neg_le_abs _
      have h2 : |μ * W1 * muCorr n ℓ (chiW ℓ N) Φ|
          = μ * |W1| * |muCorr n ℓ (chiW ℓ N) Φ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hμ.le]
      rw [h2] at h1
      have h3 := mul_le_mul_of_nonneg_left hcorr (mul_nonneg hμ.le (abs_nonneg W1))
      linarith [h1, h3]
    have hd : (- μ * W1 * muLine n ℓ (chiW ℓ N) Φ - μ * W1 * muCorr n ℓ (chiW ℓ N) Φ
          + μ * muLine n ℓ f1 Φ)
        = μ * (- W1 * muLine n ℓ (chiW ℓ N) Φ + muLine n ℓ f1 Φ)
          - μ * W1 * muCorr n ℓ (chiW ℓ N) Φ := by ring
    have hfac : μ * ((2 * A + 2 * |W1| * δ) * (Real.sqrt ((n : ℝ) * 𝓜) * H))
        + μ * |W1| * (2 * δ * ((n : ℝ) * H))
        = (2 * μ * (A + δ * |W1|) * Real.sqrt ((n : ℝ) * 𝓜) + 2 * μ * |W1| * δ * (n : ℝ)) * H := by
      ring
    rw [hd]
    linarith [hA1, hA2, hfac]
  -- ============ 11. the final assembly ============
  have hmain : ((ℓ ^ 3)⁻¹ * W1 * pairSlot n ℓ (chiW ℓ N) Φ
        + (ℓ ^ 3)⁻¹ * W1w * pairSlot n ℓ (thW ℓ N) Φ
        - μ * W1 * muForm n ℓ (chiW ℓ N) Φ)
      - (Submission.BoseGases.q1word (N := n) ℓ μ
          (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0)
          (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g2 v h) 0) Φ)
      ≤ (2 * (ℓ ^ 3)⁻¹ * (4 * A + δ * (|W1| + |W1w|)) * (n : ℝ) ^ 2
          + 2 * μ * (A + δ * |W1|) * Real.sqrt ((n : ℝ) * 𝓜)
          + 2 * μ * |W1| * δ * (n : ℝ)) * H := by
    rw [hsplit]
    have hsum := add_le_add hpair hmu
    have hfac : (2 * (ℓ ^ 3)⁻¹ * (4 * A + δ * (|W1| + |W1w|)) * (n : ℝ) ^ 2) * H
        + (2 * μ * (A + δ * |W1|) * Real.sqrt ((n : ℝ) * 𝓜)
            + 2 * μ * |W1| * δ * (n : ℝ)) * H
        = (2 * (ℓ ^ 3)⁻¹ * (4 * A + δ * (|W1| + |W1w|)) * (n : ℝ) ^ 2
          + 2 * μ * (A + δ * |W1|) * Real.sqrt ((n : ℝ) * 𝓜)
          + 2 * μ * |W1| * δ * (n : ℝ)) * H := by
      ring
    linarith [hsum, hfac]
  linarith [hmain]

end Work.BoseBoxFock
