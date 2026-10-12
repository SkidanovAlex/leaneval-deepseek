import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FibreLocal
import Submission.Work.QDecompSimpler
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# eq:Q2n0 mass treatment, S2 — T₂-mass identity (execution)

Goal: `q2QQ_slot_identity_statement` (`QDecompSimpler.lean`).  Plan: prove
per-(i,j), i ≠ j, with ψ := aQ_iΦ, fibre₂(z) := w1Fibre(wPairC(g2)) z, the
per-pair identity via the two closed forms

    ∫_x (aP_jψ)²·w₂(x_j,xᵢ) = (ℓ³)⁻¹·∫_x (aP_jψ)²·fibre₂(xᵢ)   (q2QQ_lhs_closed)
    ∫_x ψ·fibre₂(xᵢ)·(aP_jψ)  =       ∫_x (aP_jψ)²·fibre₂(xᵢ)   (q2QQ_rhs_closed)

then the slot identity sums the per-pair identity over j ≠ i
(`q2QQ_slot_identity_p2`).  All peel steps use `abox_integral_peel` +
`kcInsN`, `aP_kcInsN` constancy, `kc_insN_other_indep` y-independence, and
`w2_fibre_first_slot_eq` / `Q0Sector.integral_const_acube`.
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
set_option maxHeartbeats 400000

/-- Integrability over `abox (p+2) ℓ` of the T₂-mass integrand
`(aP_j(aQ_iΦ))²·w₂(x_j,xᵢ)` (w₂ := wPairC(g2)), `i ≠ j`. -/
lemma q2QQ_F_integrable {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X (p + 2) =>
        (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x j) (x i))
      (abox (p + 2) ℓ) volume := by
  classical
  have hψc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
  have hPc : Continuous (fun x : X (p + 2) => (aP ℓ j (aQ ℓ i Φ) x) ^ 2) :=
    (aP_continuous hℓ j hψc).pow 2
  obtain ⟨B, hB⟩ := (abox_compact (p + 2) hℓ).exists_bound_of_continuousOn
    (s := abox (p + 2) ℓ)
    (f := fun x : X (p + 2) => (aP ℓ j (aQ ℓ i Φ) x) ^ 2) hPc.continuousOn
  have hw2i : IntegrableOn (wPairU ℓ (g2 v h)) (acube ℓ ×ˢ acube ℓ) volume :=
    integrableOn_w2c_acube hR hv_nonneg hvrad hv_supp h hℓ hRℓ
  have hwcomp : IntegrableOn (fun x : X (p + 2) => wPairU ℓ (g2 v h) (x j, x i))
      (abox (p + 2) ℓ) volume :=
    integrableOn_pair_comp_ae hℓ j i hij.symm hw2i
  have hwabs : Integrable (fun x : X (p + 2) => |wPairU ℓ (g2 v h) (x j, x i)|)
      (volume.restrict (abox (p + 2) ℓ)) := by
    have hwabs' := hwcomp.abs
    simpa [Real.norm_eq_abs] using hwabs'
  have hbnd : ∀ᵐ x ∂(volume.restrict (abox (p + 2) ℓ)),
      ‖(aP ℓ j (aQ ℓ i Φ) x) ^ 2 * wPairU ℓ (g2 v h) (x j, x i)‖
        ≤ B * |wPairU ℓ (g2 v h) (x j, x i)| := by
    rw [ae_restrict_iff' (abox_measurable (p + 2) ℓ)]
    apply ae_of_all
    intro x hx
    have hle : |(aP ℓ j (aQ ℓ i Φ) x) ^ 2| ≤ B := by
      have hb' := hB x hx
      simpa [Real.norm_eq_abs] using hb'
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
  have hmeas : AEStronglyMeasurable (fun x : X (p + 2) =>
      (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * wPairU ℓ (g2 v h) (x j, x i))
      (volume.restrict (abox (p + 2) ℓ)) := by
    have h1 : Measurable (fun x : X (p + 2) => (aP ℓ j (aQ ℓ i Φ) x) ^ 2) := hPc.measurable
    exact (h1.aestronglyMeasurable.mul hwcomp.aestronglyMeasurable)
  have hdomin : Integrable (fun x : X (p + 2) => B * |wPairU ℓ (g2 v h) (x j, x i)|)
      (volume.restrict (abox (p + 2) ℓ)) := by
    exact hwabs.const_mul B
  have hgoal : Integrable (fun x : X (p + 2) =>
      (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x j) (x i))
      (volume.restrict (abox (p + 2) ℓ)) := by
    change Integrable (fun x : X (p + 2) =>
        (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * wPairU ℓ (g2 v h) (x j, x i))
      (volume.restrict (abox (p + 2) ℓ))
    exact Integrable.mono' hdomin hmeas hbnd
  exact hgoal

/-- Pointwise bound of the `w₂`-fibre over the cube: `|fibre₂ z| ≤
chiSup²·2·(16πa v)` for the chosen `w₂ := wPairC(g2)` (dilute regime). -/
lemma w2c_fibre_acube_abs_le {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (x : ℝ³) :
    |∫ y in acube ℓ, wPair ℓ (g2 v h) x y| ≤ chiSup ^ 2 * 2 * (16 * π * a v) := by
  have hbnd := fibre_acube_abs_le (h := g2 v h) hℓ hR.le hRℓ
    (g2_integrable hR hv_nonneg hvrad hv_supp h)
    (fun z hz => g2_zero_of_norm_ge hv_supp hz h) x
  have hnn : ∀ᵐ z : ℝ³, 0 ≤ g2 v h z := g2_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hEq : (∫ z : ℝ³, |g2 v h z|) = ∫ z : ℝ³, g2 v h z := by
    apply integral_congr_ae
    filter_upwards [hnn] with z hz
    exact abs_of_nonneg hz
  have hleInt : (∫ z : ℝ³, g2 v h z) ≤ 16 * π * a v :=
    (g2_integral_bounds hR hv_nonneg hvrad hv_supp h).2
  have hnnC : 0 ≤ chiSup ^ 2 * 2 := by
    exact mul_nonneg (sq_nonneg chiSup) (by norm_num)
  calc
    |∫ y in acube ℓ, wPair ℓ (g2 v h) x y| ≤ chiSup ^ 2 * 2 * (∫ z : ℝ³, |g2 v h z|) := hbnd
    _ = chiSup ^ 2 * 2 * (∫ z : ℝ³, g2 v h z) := by rw [hEq]
    _ ≤ chiSup ^ 2 * 2 * (16 * π * a v) := by
        exact mul_le_mul_of_nonneg_left hleInt hnnC

/-- Integrability over `abox (p+2) ℓ` of the closed-form integrand
`(aP_j(aQ_iΦ))²·fibre₂(xᵢ)` (`fibre₂ := w1Fibre(wPairC(g2))`, slot `i`). -/
lemma q2QQ_G_integrable {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X (p + 2) =>
        (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)))
      (abox (p + 2) ℓ) volume := by
  classical
  have hψc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
  have hPc : Continuous (fun x : X (p + 2) => (aP ℓ j (aQ ℓ i Φ) x) ^ 2) :=
    (aP_continuous hℓ j hψc).pow 2
  have hFm : AEStronglyMeasurable (fun z : ℝ³ => w1Fibre ℓ (wPairC ℓ (g2 v h)) z)
      (volume.restrict (acube ℓ)) := by
    have hfac := fibre_acube_aem (ℓ := ℓ) (h := g2 v h)
      (g2_integrable hR hv_nonneg hvrad hv_supp h)
    simpa [w1Fibre, wPairC] using hfac
  have hbnd : ∀ z : ℝ³, z ∈ acube ℓ →
      |w1Fibre ℓ (wPairC ℓ (g2 v h)) z| ≤ chiSup ^ 2 * 2 * (16 * π * a v) := by
    intro z hz
    have hb := w2c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
    simpa [w1Fibre, wPairC] using hb
  exact integrableOn_slot_fibre hℓ i hFm hbnd hPc

/-- Integrability over `abox (p+2) ℓ` of `ψ·fibre₂(xᵢ)·(aP_jψ)` (ψ := aQ_iΦ,
fibre₂ := w1Fibre(wPairC(g2))), i ≠ j — the RHS-of-pair integrand. -/
lemma q2QQ_H_integrable {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X (p + 2) =>
        (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) * (aP ℓ j (aQ ℓ i Φ) x))
      (abox (p + 2) ℓ) volume := by
  classical
  have hψc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
  have hFm : AEStronglyMeasurable (fun z : ℝ³ => w1Fibre ℓ (wPairC ℓ (g2 v h)) z)
      (volume.restrict (acube ℓ)) := by
    have hfac := fibre_acube_aem (ℓ := ℓ) (h := g2 v h)
      (g2_integrable hR hv_nonneg hvrad hv_supp h)
    simpa [w1Fibre, wPairC] using hfac
  have hbnd : ∀ z : ℝ³, z ∈ acube ℓ →
      |w1Fibre ℓ (wPairC ℓ (g2 v h)) z| ≤ chiSup ^ 2 * 2 * (16 * π * a v) := by
    intro z hz
    have hb := w2c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
    simpa [w1Fibre, wPairC] using hb
  have hS : Continuous (fun x : X (p + 2) => (aQ ℓ i Φ x) * (aP ℓ j (aQ ℓ i Φ) x)) :=
    (aQ_continuous hℓ i hΦc).mul (aP_continuous hℓ j hψc)
  have hslot := integrableOn_slot_fibre hℓ i hFm hbnd hS
  simpa [mul_assoc, mul_left_comm, mul_comm] using hslot

/-- LHS closed form: `∫_x (P_jψ)²·w₂(x_j,xᵢ) = (ℓ³)⁻¹·∫_x (P_jψ)²·fibre₂(xᵢ)`
(`ψ := aQ_iΦ`, `w₂ := wPairC(g2)`, `fibre₂ := w1Fibre(wPairC(g2))`). -/
lemma q2QQ_lhs_closed {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x j) (x i))
    = (ℓ ^ 3)⁻¹ * (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) := by
  classical
  let ψ : X (p + 2) → ℝ := aQ ℓ i Φ
  let F : X (p + 2) → ℝ := fun x =>
      (aP ℓ j ψ x) ^ 2 * wPairC ℓ (g2 v h) (x j) (x i)
  let G : X (p + 2) → ℝ := fun x =>
      (aP ℓ j ψ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))
  have hF : IntegrableOn F (abox (p + 2) ℓ) volume := by
    simpa [F, ψ] using (q2QQ_F_integrable hℓ hv_nonneg hvrad hR hv_supp h hRℓ i j hij hΦc)
  have hG : IntegrableOn G (abox (p + 2) ℓ) volume := by
    simpa [G, ψ] using (q2QQ_G_integrable hℓ hv_nonneg hvrad hR hv_supp h hRℓ i j hij hΦc)
  have hpeelF : (∫ x in abox (p + 2) ℓ, F x)
      = ∫ r : X (p + 1), (∫ y in acube ℓ, F (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) :=
      abox_integral_peel (n := p + 1) (i := j) (F := F) hF
  have hpeelG : (∫ x in abox (p + 2) ℓ, G x)
      = ∫ r : X (p + 1), (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) :=
      abox_integral_peel (n := p + 1) (i := j) (F := G) hG
  have hPj : ∀ r : X (p + 1), ∀ y : ℝ³,
      (aP ℓ j ψ (kcInsN (p + 1) j (y, r))) ^ 2 =
        ((ℓ ^ 3)⁻¹ * (∫ z in acube ℓ, ψ (kcInsN (p + 1) j (z, r)))) ^ 2 := by
    intro r y
    congr 1
    simpa [ψ] using (aP_kcInsN (i := j) y r)
  have hci : ∀ r : X (p + 1), ∀ y : ℝ³,
      (kcInsN (p + 1) j (y, r)) i = (kcInsN (p + 1) j (0, r)) i := by
    intro r y
    exact kc_insN_other_indep (p + 1) j y 0 r i hij
  have hinner : ∀ r : X (p + 1),
      (∫ y in acube ℓ, F (kcInsN (p + 1) j (y, r)))
        = (ℓ ^ 3)⁻¹ * (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r))) := by
    intro r
    let ci : ℝ³ := (kcInsN (p + 1) j (0, r)) i
    let C : ℝ := (ℓ ^ 3)⁻¹ * (∫ z in acube ℓ, ψ (kcInsN (p + 1) j (z, r)))
    have hFibre : (∫ y in acube ℓ, wPair ℓ (g2 v h) y ci) = w1Fibre ℓ (wPairC ℓ (g2 v h)) ci :=
      w2_fibre_first_slot_eq hvrad h ci
    have hFy : (∫ y in acube ℓ, F (kcInsN (p + 1) j (y, r)))
        = C ^ 2 * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci := by
      calc
        (∫ y in acube ℓ, F (kcInsN (p + 1) j (y, r)))
            = ∫ y in acube ℓ, (aP ℓ j ψ (kcInsN (p + 1) j (y, r))) ^ 2 *
                wPairC ℓ (g2 v h) (kcInsN (p + 1) j (y, r) j) (kcInsN (p + 1) j (y, r) i) := by
                rfl
        _ = ∫ y in acube ℓ, C ^ 2 * wPairC ℓ (g2 v h) y ci := by
                apply integral_congr_ae
                refine ae_of_all _ (fun y => ?_)
                dsimp [F]
                have hyj : (kcInsN (p + 1) j (y, r)) j = y := kc_insN_apply_same (p + 1) j y r
                rw [hPj r y, hyj, hci r y]
        _ = C ^ 2 * (∫ y in acube ℓ, wPairC ℓ (g2 v h) y ci) := by
                rw [integral_const_mul]
        _ = C ^ 2 * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci := by
                rw [← hFibre]
                simp [wPairC]
    have hGy : (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
        = (ℓ ^ 3) * C ^ 2 * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci := by
      calc
        (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
            = ∫ y in acube ℓ, (aP ℓ j ψ (kcInsN (p + 1) j (y, r))) ^ 2 *
                (w1Fibre ℓ (wPairC ℓ (g2 v h)) (kcInsN (p + 1) j (y, r) i)) := by
                rfl
        _ = ∫ y in acube ℓ, C ^ 2 * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci := by
                apply integral_congr_ae
                refine ae_of_all _ (fun y => ?_)
                dsimp [G]
                rw [hPj r y, hci r y]
        _ = (ℓ ^ 3) * C ^ 2 * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci := by
                rw [integral_const_acube ℓ hℓ (C ^ 2 * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci)]
                ring
    rw [hFy, hGy]
    field_simp [ne_of_gt hℓ]
  calc
    (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x j) (x i))
        = ∫ x in abox (p + 2) ℓ, F x := by
            simp [F, ψ]
    _ = ∫ r : X (p + 1), (∫ y in acube ℓ, F (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) := hpeelF
    _ = ∫ r : X (p + 1), (ℓ ^ 3)⁻¹ * (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) := by
            apply integral_congr_ae
            refine ae_of_all _ (fun r => ?_)
            exact hinner r
    _ = (ℓ ^ 3)⁻¹ * ∫ r : X (p + 1), (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) := by
            rw [integral_const_mul]
    _ = (ℓ ^ 3)⁻¹ * ∫ x in abox (p + 2) ℓ, G x := by
            rw [hpeelG]
    _ = (ℓ ^ 3)⁻¹ * (∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))) := by
            simp [G, ψ]

/-- RHS closed form: `∫_x ψ·fibre₂(xᵢ)·(aP_jψ) = ∫_x (aP_jψ)²·fibre₂(xᵢ)`. -/
lemma q2QQ_rhs_closed {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i j : Fin (p + 2)) (hij : i ≠ j)
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox (p + 2) ℓ,
        (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) * (aP ℓ j (aQ ℓ i Φ) x))
    = ∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) := by
  classical
  let ψ : X (p + 2) → ℝ := aQ ℓ i Φ
  let H : X (p + 2) → ℝ := fun x =>
      ψ x * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) * (aP ℓ j ψ x)
  let G : X (p + 2) → ℝ := fun x =>
      (aP ℓ j ψ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i))
  have hψc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
  have hH : IntegrableOn H (abox (p + 2) ℓ) volume := by
    simpa [H, ψ, mul_assoc, mul_left_comm, mul_comm] using
      (q2QQ_H_integrable hℓ hv_nonneg hvrad hR hv_supp h hRℓ i j hij hΦc)
  have hG : IntegrableOn G (abox (p + 2) ℓ) volume := by
    simpa [G, ψ] using (q2QQ_G_integrable hℓ hv_nonneg hvrad hR hv_supp h hRℓ i j hij hΦc)
  have hpeelH : (∫ x in abox (p + 2) ℓ, H x)
      = ∫ r : X (p + 1), (∫ y in acube ℓ, H (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) :=
      abox_integral_peel (n := p + 1) (i := j) (F := H) hH
  have hpeelG : (∫ x in abox (p + 2) ℓ, G x)
      = ∫ r : X (p + 1), (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) :=
      abox_integral_peel (n := p + 1) (i := j) (F := G) hG
  have hPj : ∀ r : X (p + 1), ∀ y : ℝ³,
      (aP ℓ j ψ (kcInsN (p + 1) j (y, r))) ^ 2 =
        ((ℓ ^ 3)⁻¹ * (∫ z in acube ℓ, ψ (kcInsN (p + 1) j (z, r)))) ^ 2 := by
    intro r y
    congr 1
    simpa [ψ] using (aP_kcInsN (i := j) y r)
  have hPjlin : ∀ r : X (p + 1), ∀ y : ℝ³,
      (aP ℓ j ψ (kcInsN (p + 1) j (y, r))) =
        (ℓ ^ 3)⁻¹ * (∫ z in acube ℓ, ψ (kcInsN (p + 1) j (z, r))) := by
    intro r y
    simpa [ψ] using (aP_kcInsN (i := j) y r)
  have hci : ∀ r : X (p + 1), ∀ y : ℝ³,
      (kcInsN (p + 1) j (y, r)) i = (kcInsN (p + 1) j (0, r)) i := by
    intro r y
    exact kc_insN_other_indep (p + 1) j y 0 r i hij
  have hinner : ∀ r : X (p + 1),
      (∫ y in acube ℓ, H (kcInsN (p + 1) j (y, r)))
        = ∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)) := by
    intro r
    let ci : ℝ³ := (kcInsN (p + 1) j (0, r)) i
    let I : ℝ := ∫ z in acube ℓ, ψ (kcInsN (p + 1) j (z, r))
    have hHy : (∫ y in acube ℓ, H (kcInsN (p + 1) j (y, r)))
        = (ℓ ^ 3)⁻¹ * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci * I ^ 2 := by
      calc
        (∫ y in acube ℓ, H (kcInsN (p + 1) j (y, r)))
            = ∫ y in acube ℓ, ψ (kcInsN (p + 1) j (y, r)) *
                (w1Fibre ℓ (wPairC ℓ (g2 v h)) (kcInsN (p + 1) j (y, r) i)) *
                  (aP ℓ j ψ (kcInsN (p + 1) j (y, r))) := by
                rfl
        _ = ∫ y in acube ℓ,
              (w1Fibre ℓ (wPairC ℓ (g2 v h)) ci * (ℓ ^ 3)⁻¹ * I) * ψ (kcInsN (p + 1) j (y, r)) := by
                apply integral_congr_ae
                refine ae_of_all _ (fun y => ?_)
                dsimp [H]
                rw [hci r y, hPjlin r y]
                dsimp [I]
                ring
        _ = (w1Fibre ℓ (wPairC ℓ (g2 v h)) ci * (ℓ ^ 3)⁻¹ * I) * I := by
                rw [integral_const_mul]
        _ = (ℓ ^ 3)⁻¹ * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci * I ^ 2 := by ring
    have hGy : (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
        = (ℓ ^ 3)⁻¹ * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci * I ^ 2 := by
      calc
        (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
            = ∫ y in acube ℓ, (aP ℓ j ψ (kcInsN (p + 1) j (y, r))) ^ 2 *
                (w1Fibre ℓ (wPairC ℓ (g2 v h)) (kcInsN (p + 1) j (y, r) i)) := by
                rfl
        _ = ∫ y in acube ℓ,
              (((ℓ ^ 3)⁻¹ * I) ^ 2 * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci) := by
                apply integral_congr_ae
                refine ae_of_all _ (fun y => ?_)
                dsimp [G]
                rw [hPj r y, hci r y]
        _ = (((ℓ ^ 3)⁻¹ * I) ^ 2 * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci) * ℓ ^ 3 := by
                rw [integral_const_acube ℓ hℓ (((ℓ ^ 3)⁻¹ * I) ^ 2 * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci)]
        _ = (ℓ ^ 3)⁻¹ * w1Fibre ℓ (wPairC ℓ (g2 v h)) ci * I ^ 2 := by
                field_simp [ne_of_gt hℓ]
    rw [hHy, hGy]
  calc
    (∫ x in abox (p + 2) ℓ,
        (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) * (aP ℓ j (aQ ℓ i Φ) x))
        = ∫ x in abox (p + 2) ℓ, H x := by
            simp [H, ψ]
    _ = ∫ r : X (p + 1), (∫ y in acube ℓ, H (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) := hpeelH
    _ = ∫ r : X (p + 1), (∫ y in acube ℓ, G (kcInsN (p + 1) j (y, r)))
          ∂((volume : Measure (X (p + 1))).restrict (abox (p + 1) ℓ)) := by
            apply integral_congr_ae
            refine ae_of_all _ (fun r => ?_)
            exact hinner r
    _ = ∫ x in abox (p + 2) ℓ, G x := hpeelG.symm
    _ = ∫ x in abox (p + 2) ℓ,
        (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) := by
            simp [G, ψ]


/-- **Slot identity over `Fin (p+2)`**: `Σ_{j≠i}` of the per-pair T₂-mass
identity (`Finset.sum_filter` for the `j ≠ i` guards, per-`j` case split,
`integral_finsetSum` for the Σ/∫ swap). -/
lemma q2QQ_slot_identity_p2 {p : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i : Fin (p + 2))
    {Φ : X (p + 2) → ℝ} (hΦc : Continuous Φ) :
    (∑ j : Fin (p + 2), if hj : j ≠ i then
        (∫ x in abox (p + 2) ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x j) (x i)) else 0)
    = (ℓ ^ 3)⁻¹ * (∫ x in abox (p + 2) ℓ,
        (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
          (∑ j : Fin (p + 2), if hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)) := by
  classical
  let ψ : X (p + 2) → ℝ := aQ ℓ i Φ
  let s : Finset (Fin (p + 2)) := Finset.univ.filter (fun j => j ≠ i)
  let lhs_j : Fin (p + 2) → ℝ := fun j =>
      ∫ x in abox (p + 2) ℓ, (aP ℓ j ψ x) ^ 2 * wPairC ℓ (g2 v h) (x j) (x i)
  let rhs_j : Fin (p + 2) → ℝ := fun j =>
      ∫ x in abox (p + 2) ℓ, ψ x * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) * (aP ℓ j ψ x)
  have hpair : ∀ j : Fin (p + 2), j ∈ s → lhs_j j = (ℓ ^ 3)⁻¹ * rhs_j j := by
    intro j hj
    have hji : j ≠ i := by
      simpa [s] using (Finset.mem_filter.mp hj).2
    have h1 := q2QQ_lhs_closed (p := p) hℓ hv_nonneg hvrad hR hv_supp h hRℓ i j hji.symm hΦc
    have h2 := q2QQ_rhs_closed (p := p) hℓ hv_nonneg hvrad hR hv_supp h hRℓ i j hji.symm hΦc
    dsimp [lhs_j, rhs_j, ψ]
    rw [h1]
    congr 1
    exact h2.symm
  have hfint : ∀ j : Fin (p + 2), j ∈ s →
      MeasureTheory.Integrable (fun x : X (p + 2) =>
        ψ x * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) * (aP ℓ j ψ x))
        (volume.restrict (abox (p + 2) ℓ)) := by
    intro j hj
    have hji : j ≠ i := by
      simpa [s] using (Finset.mem_filter.mp hj).2
    exact q2QQ_H_integrable hℓ hv_nonneg hvrad hR hv_supp h hRℓ i j hji.symm hΦc
  have hswap : (∑ j ∈ s, rhs_j j)
      = ∫ x in abox (p + 2) ℓ,
          ψ x * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) * (∑ j ∈ s, aP ℓ j ψ x) := by
    calc
      (∑ j ∈ s, rhs_j j)
          = ∫ x in abox (p + 2) ℓ,
              (∑ j ∈ s, ψ x * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) * (aP ℓ j ψ x)) := by
              rw [← integral_finsetSum s hfint]
      _ = ∫ x in abox (p + 2) ℓ,
          ψ x * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) * (∑ j ∈ s, aP ℓ j ψ x) := by
              apply integral_congr_ae
              filter_upwards with x
              change (∑ j ∈ s, ψ x * w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i) * aP ℓ j ψ x)
                  = ψ x * w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i) * (∑ j ∈ s, aP ℓ j ψ x)
              rw [← Finset.mul_sum]
  calc
    (∑ j : Fin (p + 2), if hj : j ≠ i then
        (∫ x in abox (p + 2) ℓ,
          (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x j) (x i)) else 0)
        = ∑ j ∈ s, lhs_j j := by
            simp [s, lhs_j, ψ, Finset.sum_filter]
    _ = ∑ j ∈ s, (ℓ ^ 3)⁻¹ * rhs_j j := by
            exact Finset.sum_congr rfl (fun j hj => hpair j hj)
    _ = (ℓ ^ 3)⁻¹ * (∑ j ∈ s, rhs_j j) := by
            rw [Finset.mul_sum]
    _ = (ℓ ^ 3)⁻¹ * (∫ x in abox (p + 2) ℓ,
        ψ x * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) * (∑ j ∈ s, aP ℓ j ψ x)) := by
            rw [hswap]
    _ = (ℓ ^ 3)⁻¹ * (∫ x in abox (p + 2) ℓ,
        (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
          (∑ j : Fin (p + 2), if hj : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0)) := by
            congr 1
            apply integral_congr_ae
            refine ae_of_all _ (fun x => ?_)
            simp [ψ, s, Finset.sum_filter]


/-- **Slot identity** (the `q2QQ_slot_identity_statement` target, proven):
`Σ_{j≠i}∫(aP_jψ)²·w₂(x_j,xᵢ) = (ℓ³)⁻¹·∫ ψ·fibre₂(xᵢ)·(Σ_{j≠i} aP_jψ)` for every
`N` (the `Fin (p+2)` case is `q2QQ_slot_identity_p2`; `N = 0` is vacuous and
`N = 1` has empty `j ≠ i` sums). -/
theorem q2QQ_slot_identity {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i : Fin N) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    q2QQ_slot_identity_statement hℓ hv_nonneg hvrad hR hv_supp h hRℓ i hΦc := by
  classical
  cases N with
  | zero =>
      exfalso
      exact Nat.not_lt_zero i.1 i.isLt
  | succ n =>
      cases n with
      | zero =>
          -- N = 1: the only index is i, so both `j ≠ i` sums vanish
          have hall : ∀ j : Fin 1, j = i := by
            intro j
            ext
            fin_cases j <;> fin_cases i <;> rfl
          simp [q2QQ_slot_identity_statement, hall]
      | succ n =>
          simpa [q2QQ_slot_identity_statement] using
            (q2QQ_slot_identity_p2 (p := n) hℓ hv_nonneg hvrad hR hv_supp h hRℓ i hΦc)

end BoseGases

end Submission
