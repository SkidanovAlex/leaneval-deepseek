import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.PotChosen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The one-body condensate mass (FS `eq:Q2n0` mass-term content, P-part)

For the fixed-N dictionary the potential's one-body mass
`Σ_i ∫_{abox} Φ²·(∫_{acube} w₁(xᵢ,·))` splits into a condensate part — which
evaluates EXACTLY, since `aP_i Φ` is constant in the `xᵢ`-coordinate and the
cube-pair mass is `∬_{acube²} w₁ = ℓ³·(8πa v)`
(`Q0Chosen.w1c_acube_integral`) — plus excited and cross parts.  This module
proves the exact condensate identity

    Σ_i ∫_abox (aP_i Φ)²·(∫_{acube} w₁(xᵢ,·)) = (8π·a v)·cS1 ℓ Φ,

the first ingredient of the μ-tuning master lemma (the P-part of the
`eq:Q2n0` mass term, replacing the crude `−μ·q2C0·cnPlus` bound of
`q2_onebody_lower`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Per-particle: `∫_{abox} (aP_i Φ)²·fibre(xᵢ) = (8π·a v)·∫_{abox}(aP_iΦ)²`,
because `aP_iΦ` is constant in the `xᵢ`-coordinate and
`∫_{xᵢ∈acube}∫_{y∈acube} w₁(xᵢ,y) = ℓ³·(8π·a v)` (times `ℓ⁻³` for the
`xᵢ`-average normalisation). -/
lemma onebody_mass_per_condensate {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i : Fin N) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ,
        (aP ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
      = (8 * π * a v) * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
  have hv1i : IntegrableOn (wPairU ℓ (g0 v h)) (acube ℓ ×ˢ acube ℓ) volume :=
    integrableOn_w1c_acube hR hv_supp h hℓ hRℓ
  have hk := one_value_ae (N := N) hℓ (i := i) (Φ := Φ) hΦc
    (w1 := wPairU ℓ (g0 v h)) hv1i
  have hcube := w1c_acube_integral hR hv_supp h hℓ hRℓ
  calc
    (∫ x in abox N ℓ,
        (aP ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
        = ∫ x in abox N ℓ,
            (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, wPairU ℓ (g0 v h) (x i, y)) := by
            apply integral_congr_ae
            filter_upwards with x
            simp [w1Fibre, wPairC, wPairU]
    _ = (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g0 v h) p) *
          (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := hk
    _ = (8 * π * a v) * (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := by
            rw [hcube]
            field_simp [pow_ne_zero 3 (ne_of_gt hℓ)]

/-- **Condensate one-body mass (exact)**: the P-part of the one-body mass of
the potential is `(8π·a v)·cS1`. -/
lemma onebody_mass_condensate {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
      = (8 * π * a v) * cS1 ℓ Φ := by
  have hv1i : IntegrableOn (wPairU ℓ (g0 v h)) (acube ℓ ×ˢ acube ℓ) volume :=
    integrableOn_w1c_acube hR hv_supp h hℓ hRℓ
  have hk := sumOne_value_ae (N := N) hℓ (Φ := Φ) hΦc (w1 := wPairU ℓ (g0 v h)) hv1i
  have hcube := w1c_acube_integral hR hv_supp h hℓ hRℓ
  calc
    (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
        = ∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) ^ 2 * (∫ y in acube ℓ, wPairU ℓ (g0 v h) (x i, y)) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply integral_congr_ae
            filter_upwards with x
            simp [w1Fibre, wPairC, wPairU]
    _ = (ℓ ^ 3)⁻¹ * (∫ p in acube ℓ ×ˢ acube ℓ, wPairU ℓ (g0 v h) p) *
          (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2) := hk
    _ = (8 * π * a v) * cS1 ℓ Φ := by
            rw [hcube]
            have hℓ3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
            have hc : (ℓ ^ 3)⁻¹ * (ℓ ^ 3 * (8 * π * a v)) = (8 * π * a v) := by
              rw [← mul_assoc, inv_mul_cancel₀ hℓ3, one_mul]
            rw [hc]
            rfl


/-- **Q²-part of the one-body mass (lower bound)**: the excited square part is
bounded below by `−C₀·cnPlus`, `C₀ := chiSup²·2·8π·a v` (the fibre bound
`w1c_fibre_acube_abs_le`).  Together with `onebody_mass_condensate` and the
cross bound this is the FS `eq:Q2n0` mass-term decomposition. -/
lemma q2part_mass_lower {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    - (chiSup ^ 2 * 2 * (8 * π * a v)) * cnPlus ℓ Φ
      ≤ ∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) := by
  classical
  let C0 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  have hfib : ∀ z : ℝ³, |w1Fibre ℓ (wPairC ℓ (g0 v h)) z| ≤ C0 := by
    intro z
    have hb := w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
    dsimp [C0]
    simpa [w1Fibre, wPairC] using hb
  -- per particle: ∫(QᵢΦ)²·fibre(xᵢ) ≥ −C0·∫(QᵢΦ)²
  have hper : ∀ i : Fin N,
      - C0 * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)
        ≤ ∫ x in abox N ℓ,
            (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) := by
    intro i
    let F : ℝ³ → ℝ := fun z => w1Fibre ℓ (wPairC ℓ (g0 v h)) z
    let S : X N → ℝ := fun x => (aQ ℓ i Φ x) ^ 2
    have hSc : Continuous S := by
      dsimp [S]
      exact (aQ_continuous hℓ i hΦc).pow 2
    have hFm : AEStronglyMeasurable F (volume.restrict (acube ℓ)) := by
      dsimp [F]
      have hfac := fibre_acube_aem (ℓ := ℓ) (h := g0 v h) (g0_integrable hR hv_supp h)
      simpa [w1Fibre, wPairC] using hfac
    have hInt : IntegrableOn (fun x : X N => S x * F (x i)) (abox N ℓ) volume := by
      exact integrableOn_slot_fibre hℓ i hFm (fun z hz => by
        have hb := hfib z
        simpa [F, C0] using hb) hSc
    have hpt : ∀ x : X N, - C0 * S x ≤ S x * F (x i) := by
      intro x
      have hFc : - C0 ≤ F (x i) := by
        dsimp [F]
        exact (abs_le.mp (hfib (x i))).1
      have hS0 : 0 ≤ S x := sq_nonneg _
      have hmul : -C0 * S x ≤ F (x i) * S x := mul_le_mul_of_nonneg_right hFc hS0
      simpa [mul_comm] using hmul
    have hIntL : IntegrableOn (fun x : X N => - C0 * S x) (abox N ℓ) volume := by
      have hEq : (fun x : X N => - C0 * S x) = fun x : X N => (-C0) * (aQ ℓ i Φ x) ^ 2 := by
        funext x
        rfl
      rw [hEq]
      exact (integrableOn_abox_of_continuous hℓ ((aQ_continuous hℓ i hΦc).pow 2)).const_mul (-C0)
    calc
      - C0 * (∫ x in abox N ℓ, S x)
          = ∫ x in abox N ℓ, - C0 * S x := by
              rw [integral_const_mul]
      _ ≤ ∫ x in abox N ℓ, S x * F (x i) := by
              exact integral_mono_ae (μ := (volume : Measure (X N)).restrict (abox N ℓ))
                hIntL hInt (by filter_upwards with x; exact hpt x)
  -- sum over i
  have hsum : ∑ i : Fin N, - C0 * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)
      ≤ ∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) :=
    Finset.sum_le_sum (fun i hi => hper i)
  calc
    - (chiSup ^ 2 * 2 * (8 * π * a v)) * cnPlus ℓ Φ
        = ∑ i : Fin N, - C0 * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
            dsimp [C0]
            simp_rw [← Finset.mul_sum]
            simp [cnPlus]
    _ ≤ ∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) := hsum





/-- **One-body mass expansion (exact)**: `Φ = PᵢΦ + QᵢΦ` per particle gives
`Σᵢ∫Φ²·fibre(xᵢ) = (8π·a v)·cS1 + Σᵢ∫(QᵢΦ)²·fibre(xᵢ) +
2·Σᵢ∫(PᵢΦ)(QᵢΦ)·fibre(xᵢ)` (the identity the master lemma combines with
`q2part_mass_lower` and the cross bound). -/
lemma onebody_mass_expand {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in abox N ℓ, (Φ x) ^ 2 *
        (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
      = (8 * π * a v) * cS1 ℓ Φ
        + (∑ i : Fin N, ∫ x in abox N ℓ,
            (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
        + 2 * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) * (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))) := by
  classical
  let F : ℝ³ → ℝ := fun z => w1Fibre ℓ (wPairC ℓ (g0 v h)) z
  let C0 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  have hfib : ∀ z : ℝ³, |F z| ≤ C0 := by
    intro z
    dsimp [F, C0]
    simpa [w1Fibre, wPairC] using
      (w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z)
  have hFm : AEStronglyMeasurable F (volume.restrict (acube ℓ)) := by
    dsimp [F]
    have hfac := fibre_acube_aem (ℓ := ℓ) (h := g0 v h) (g0_integrable hR hv_supp h)
    simpa [w1Fibre, wPairC] using hfac
  have hint : ∀ i : Fin N, ∀ S : X N → ℝ, Continuous S →
      IntegrableOn (fun x : X N => S x * F (x i)) (abox N ℓ) volume := by
    intro i S hSc
    exact integrableOn_slot_fibre hℓ i hFm (fun z hz => by
      have hb := hfib z
      simpa [C0] using hb) hSc
  -- per particle: Φ² = (PᵢΦ + QᵢΦ)² splits into P² + 2PQ + Q²
  have hpi : ∀ i : Fin N,
      (∫ x in abox N ℓ, (Φ x) ^ 2 * F (x i))
        = (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * F (x i))
          + 2 * (∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * F (x i))
          + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * F (x i)) := by
    intro i
    have hPc : Continuous (aP ℓ i Φ) := aP_continuous hℓ i hΦc
    have hQc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
    let μ : Measure (X N) := volume.restrict (abox N ℓ)
    let f1 : X N → ℝ := fun x => (aP ℓ i Φ x) ^ 2 * F (x i)
    let f2 : X N → ℝ := fun x => (2 * ((aP ℓ i Φ x) * (aQ ℓ i Φ x))) * F (x i)
    let f3 : X N → ℝ := fun x => (aQ ℓ i Φ x) ^ 2 * F (x i)
    have h1 : Integrable f1 μ := by
      have hh := hint i (fun x => (aP ℓ i Φ x) ^ 2) (hPc.pow 2)
      simpa [f1, μ, IntegrableOn] using hh
    have h2 : Integrable f2 μ := by
      have hh := hint i (fun x => (aP ℓ i Φ x) * (aQ ℓ i Φ x)) (hPc.mul hQc)
      simpa [f2, μ, mul_assoc, IntegrableOn] using hh.const_mul 2
    have h3 : Integrable f3 μ := by
      have hh := hint i (fun x => (aQ ℓ i Φ x) ^ 2) (hQc.pow 2)
      simpa [f3, μ, IntegrableOn] using hh
    have h12 : Integrable (f1 + f2) μ := h1.add h2
    have hΦ2 : (fun x : X N => (Φ x) ^ 2 * F (x i))
        = fun x : X N => (f1 x + f2 x + f3 x) := by
      funext x
      dsimp [f1, f2, f3]
      have hPQx : Φ x = aP ℓ i Φ x + aQ ℓ i Φ x := by dsimp [aQ]; ring
      rw [hPQx]
      ring
    have hE1 : (∫ x, f1 x ∂μ) = ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * F (x i) := by
      dsimp [f1, μ]
    have hE2 : (∫ x, f2 x ∂μ)
        = 2 * (∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * F (x i)) := by
      have hm : (fun x : X N => (2 * ((aP ℓ i Φ x) * (aQ ℓ i Φ x))) * F (x i))
          = fun x : X N => 2 * (((aP ℓ i Φ x) * (aQ ℓ i Φ x)) * F (x i)) := by
        funext x
        ring
      calc
        (∫ x, f2 x ∂μ)
            = ∫ x in abox N ℓ, (2 * ((aP ℓ i Φ x) * (aQ ℓ i Φ x))) * F (x i) := by
                dsimp [f2, μ]
        _ = ∫ x in abox N ℓ, 2 * (((aP ℓ i Φ x) * (aQ ℓ i Φ x)) * F (x i)) := by
                rw [hm]
        _ = 2 * (∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * F (x i)) := by
                rw [integral_const_mul]
    have hE3 : (∫ x, f3 x ∂μ) = ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * F (x i) := by
      dsimp [f3, μ]
    calc
      (∫ x in abox N ℓ, (Φ x) ^ 2 * F (x i))
          = (∫ x, (Φ x) ^ 2 * F (x i) ∂μ) := by rfl
      _ = (∫ x, (f1 x + f2 x + f3 x) ∂μ) := by
              rw [hΦ2]
      _ = (∫ x, ((f1 + f2) x + f3 x) ∂μ) := by rfl
      _ = (∫ x, (f1 + f2) x ∂μ) + (∫ x, f3 x ∂μ) := by
              exact integral_add h12 h3
      _ = (∫ x, (f1 x + f2 x) ∂μ) + (∫ x, f3 x ∂μ) := by rfl
      _ = (∫ x, f1 x ∂μ) + (∫ x, f2 x ∂μ) + (∫ x, f3 x ∂μ) := by
              rw [integral_add h1 h2]
      _ = (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * F (x i))
          + 2 * (∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * F (x i))
          + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * F (x i)) := by
          rw [hE1, hE2, hE3]
  -- sum over i; P-part via onebody_mass_condensate
  calc
    (∑ i : Fin N, ∫ x in abox N ℓ, (Φ x) ^ 2 *
        (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
        = ∑ i : Fin N, (∫ x in abox N ℓ, (Φ x) ^ 2 * F (x i)) := by simp [F]
    _ = ∑ i : Fin N,
          ((∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * F (x i))
            + 2 * (∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * F (x i))
            + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * F (x i))) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hpi i
    _ = (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * F (x i))
        + 2 * (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) * (aQ ℓ i Φ x) * F (x i))
        + (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * F (x i)) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (8 * π * a v) * cS1 ℓ Φ
        + (∑ i : Fin N, ∫ x in abox N ℓ,
            (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
        + 2 * (∑ i : Fin N, ∫ x in abox N ℓ,
            (aP ℓ i Φ x) * (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))) := by
            have hP : (∑ i : Fin N, ∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * F (x i))
                = (8 * π * a v) * cS1 ℓ Φ := by
              simpa [F] using (onebody_mass_condensate hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc)
            rw [hP]
            simp [F]
            ring


end BoseGases

end Submission
