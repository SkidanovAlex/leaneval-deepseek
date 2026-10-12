import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FSGroupQ1Q2
import Submission.Work.QCrossQuarterD2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Q2 in sharp mass form (FS eq:SmallsimpleQs Q2 part, corpus per-sector)

Sub-lemma (b), Q2 side.  The corpus `q2word(N, ℓ, μ, w₁ := wPairC(g₀),
w₂ := wPairC(g₂))` splits as `T1 + T2 + T3 + T4` (PotWords):

  T1 = Σ∫(P₁Q₂Φ)·(P₂Q₁Φ)·w₂          T2 = Σ∫(P₁Q₂Φ)·(Q₂P₁Φ)·w₂
  T3 = −μ·Σ∫(Q_iΦ)²·(w₁-fibre)(x_i)   T4 = Σ∫(P₁P₂Φ)·(Q₂Q₁Φ)·w₁

This module proves the sharp `n₊`/`cS₂`-linear mass bounds of T1, T2, T3 and
the T4-`q4B`-absorption in the quarter form (`qcross_d2_quarter` per-pair,
summed with the sharp `w₁`-mass atoms), giving the assembled lower bound

  q2word ≥ − C₂(ℓ³)⁻¹·(2·N̂·n₊) − C₁(ℓ³)⁻¹·(4·cS2 + 3·N̂·n₊) − μ·C₁·n₊ − (1/4)·q4word

(`q2_sharp_lower`, chosen branch, `Continuous Φ`, `0 ≤ μ`).
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

section ChosenBranch

/-- T3 one-body lower bound: `−μ·Σ∫(Q_iΦ)²·fibre ≥ −μ·C₁·n₊` (fibre ≤ C₁
pointwise, `0 ≤ μ`). -/
lemma q2_T3_lower {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 ≤ μ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    - μ * (fsqC1 (a v)) * cnPlus ℓ Φ ≤
      - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) ^ 2 * w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) := by
  have hfib : ∀ (i : Fin N) (x : XN N),
      w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i) ≤ fsqC1 (a v) := by
    intro i x
    have hb := w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ (x i)
    have hb' : |w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)| ≤ fsqC1 (a v) := by
      simpa [w1Fibre, wPairC, fsqC1] using hb
    exact le_trans (le_abs_self _) hb'
  have hC : 0 ≤ fsqC1 (a v) := by
    have hav0 : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
    dsimp [fsqC1]
    positivity
  have hInt (i : Fin N) :
      (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
        ≤ (fsqC1 (a v)) * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
    let S : XN N → ℝ := fun x => (aQ ℓ i Φ x) ^ 2
    let F : ℝ³ → ℝ := fun z => w1Fibre ℓ (wPairC ℓ (g0 v h)) z
    have hSc : Continuous S := by
      dsimp [S]
      exact (aQ_continuous hℓ i hΦc).pow 2
    have hFm : AEStronglyMeasurable F (volume.restrict (acube ℓ)) := by
      dsimp [F]
      exact (fibre_acube_aem (h := g0 v h) (g0_integrable hR hv_supp h))
    have hC : ∀ z ∈ acube ℓ, |F z| ≤ fsqC1 (a v) := by
      intro z hz
      have hb := w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
      have hb' : |F z| ≤ fsqC1 (a v) := by
        dsimp [F]
        simpa [w1Fibre, wPairC, fsqC1] using hb
      exact hb'
    have hD : IntegrableOn (fun x : XN N => S x * F (x i)) (abox N ℓ) volume :=
      integrableOn_slot_fibre hℓ i hFm hC hSc
    have hD' : IntegrableOn (fun x : XN N => (aQ ℓ i Φ x) ^ 2 *
        w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) (abox N ℓ) volume := by
      simpa [S, F] using hD
    have hCst : IntegrableOn (fun x : XN N => (fsqC1 (a v)) * (aQ ℓ i Φ x) ^ 2)
        (abox N ℓ) volume := by
      exact (integrableOn_sq_aQ hℓ i hΦc).const_mul (fsqC1 (a v))
    have hle : (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 *
          w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
        ≤ ∫ x in abox N ℓ, (fsqC1 (a v)) * (aQ ℓ i Φ x) ^ 2 := by
      refine integral_mono ?_ ?_ ?_
      · exact hD'
      · simpa [IntegrableOn] using hCst
      · intro x
        have hb := hfib i x
        have h1 : (aQ ℓ i Φ x) ^ 2 * w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)
            ≤ (aQ ℓ i Φ x) ^ 2 * fsqC1 (a v) :=
          mul_le_mul_of_nonneg_left hb (sq_nonneg (aQ ℓ i Φ x))
        simpa [mul_comm] using h1
    rw [integral_const_mul] at hle
    simpa [mul_comm] using hle
  have hsum : (∑ i : Fin N, ∫ x in abox N ℓ,
        (aQ ℓ i Φ x) ^ 2 * w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
      ≤ (fsqC1 (a v)) * cnPlus ℓ Φ := by
    calc
      (∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) ^ 2 * w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
          ≤ ∑ i : Fin N, (fsqC1 (a v)) * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
            exact Finset.sum_le_sum (fun i _ => hInt i)
      _ = (fsqC1 (a v)) * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
            rw [← Finset.mul_sum]
      _ = (fsqC1 (a v)) * cnPlus ℓ Φ := by simp [cnPlus]
  have hmu : - μ * (fsqC1 (a v)) * cnPlus ℓ Φ
      ≤ - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) ^ 2 * w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) := by
    have h1 : μ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aQ ℓ i Φ x) ^ 2 * w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
        ≤ μ * ((fsqC1 (a v)) * cnPlus ℓ Φ) :=
      mul_le_mul_of_nonneg_left hsum hμ
    nlinarith
  nlinarith

/-- The swapped `(P Q)`-family for the `w₂`-kernel is `n₊`-linear:
`Σ_p∫(P_{p.2}Q_{p.1}Φ)²·|wPairC(ℓ,g₂)| ≤ C₂·(ℓ³)⁻¹·N̂·n₊`. -/
lemma pq_w2_mass_swap_le_cnPlus {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
      ≤ (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
  classical
  let C2 : ℝ := fsqC2 (a v)
  have hC2nn : 0 ≤ C2 := by
    have hav0 : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
    dsimp [C2, fsqC2]
    positivity
  have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g2 v h) (x p.1) (x p.2)|)
      ≤ C2 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) :=
    masssum_Qsw_abs_le hℓ (le_of_lt hR) hRℓ (g2_integrable hR hv_nonneg hvrad hv_supp h)
      (fun z hz => g2_zero_of_norm_ge hv_supp hz h) (g2_even hvrad h)
      (C := C2) (fun x => w2abs_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ x)
      hΦc
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
        = (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g2 v h) (x p.1) (x p.2)|) := by
          simp [wPairC]
    _ ≤ C2 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) := by
          simpa [C2] using hmm
    _ ≤ C2 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
          exact mul_le_mul_of_nonneg_left (pairSum_Q_swap_le hℓ hΦc) (mul_nonneg hC2nn hLinv)
    _ = (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
          simp [C2]
          ring

/-- **Q2 T1 sharp mass bound** (the first sum-processing lemma of the
`q2_sharp_lower` T1/T2 block): the per-pair AM–GM over the two `w₂`-mass
families gives

    |Σ_p∫(P₁Q₂Φ)·(P₂Q₁Φ)·wPairC(ℓ,g₂)| ≤ C₂·(ℓ³)⁻¹·N̂·n₊ . -/
theorem q2_T1_abs_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g2 v h) (x p.1) (x p.2)|
      ≤ (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
  classical
  let C2 : ℝ := fsqC2 (a v)
  have hP : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
      ≤ C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    simpa [C2] using (pq_w2_mass_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc)
  have hS : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
      ≤ C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    simpa [C2] using (pq_w2_mass_swap_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc)
  calc
    |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g2 v h) (x p.1) (x p.2)|
        ≤ ∑ p ∈ pairSet N, |∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
              wPairC ℓ (g2 v h) (x p.1) (x p.2)| := by
          simpa using (Finset.abs_sum_le_sum_abs (s := pairSet N)
            (f := fun p : Fin N × Fin N => ∫ x in abox N ℓ,
              (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
                wPairC ℓ (g2 v h) (x p.1) (x p.2)))
    _ ≤ ∑ p ∈ pairSet N,
          ((1 / 2) * (∫ x in abox N ℓ,
              (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
          + (1 / 2) * (∫ x in abox N ℓ,
              (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
        have hf : Continuous (aP ℓ p.1 (aQ ℓ p.2 Φ)) :=
          aP_continuous hℓ p.1 (aQ_continuous hℓ p.2 hΦc)
        have hg : Continuous (aP ℓ p.2 (aQ ℓ p.1 Φ)) :=
          aP_continuous hℓ p.2 (aQ_continuous hℓ p.1 hΦc)
        simpa [wPairC, mul_assoc] using (abs_integral_mul_mul_wPair_le_half hℓ
          (g2_integrable hR hv_nonneg hvrad hv_supp h)
          (fun z hz => g2_zero_of_norm_ge hv_supp hz h) hRℓ hne
          (f := aP ℓ p.1 (aQ ℓ p.2 Φ)) (g := aP ℓ p.2 (aQ ℓ p.1 Φ)) hf hg)
    _ = (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
        + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|) := by
        rw [Finset.sum_add_distrib]
        simp_rw [← Finset.mul_sum]
    _ ≤ C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
          nlinarith [hP, hS]

/-- **Q2 T2 sharp mass bound**: slot commutation makes T2 a
`(Q_{p.2}P_{p.1}Φ)²`-sum, so

    |Σ_p∫(P₁Q₂Φ)·(Q₂P₁Φ)·wPairC(ℓ,g₂)| ≤ C₂·(ℓ³)⁻¹·N̂·n₊ . -/
theorem q2_T2_abs_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
          wPairC ℓ (g2 v h) (x p.1) (x p.2)|
      ≤ (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
  classical
  let C2 : ℝ := fsqC2 (a v)
  -- term2 = Σ_p ∫ (Q_{p2} P_{p1} Φ)² · w₂   (P_i Q_j = Q_j P_i pointwise)
  have hsq : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
          wPairC ℓ (g2 v h) (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x p.1) (x p.2) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
    apply integral_congr_ae
    filter_upwards with x
    rw [aP_aQ_comm hℓ hne hΦc x]
    ring
  -- per pair: |∫ s²·w₂| ≤ ∫ s²·|w₂|   (AM–GM with f = g = s)
  have hpair : ∀ p ∈ pairSet N, |∫ x in abox N ℓ,
        (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x p.1) (x p.2)|
      ≤ ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)| := by
    intro p hp
    have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
    let s : XN N → ℝ := fun x => aQ ℓ p.2 (aP ℓ p.1 Φ) x
    have hs : Continuous s := by
      dsimp [s]
      exact aQ_continuous hℓ p.2 (aP_continuous hℓ p.1 hΦc)
    have hb := abs_integral_mul_mul_wPair_le_half hℓ
      (g2_integrable hR hv_nonneg hvrad hv_supp h)
      (fun z hz => g2_zero_of_norm_ge hv_supp hz h) hRℓ hne hs hs
    calc
      |∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 *
          wPairC ℓ (g2 v h) (x p.1) (x p.2)|
          = |∫ x in abox N ℓ, s x * (s x * wPair ℓ (g2 v h) (x p.1) (x p.2))| := by
              dsimp [s]
              simp [wPairC, pow_two, mul_assoc]
      _ ≤ (1 / 2) * (∫ x in abox N ℓ, (s x) ^ 2 * |wPair ℓ (g2 v h) (x p.1) (x p.2)|)
            + (1 / 2) * (∫ x in abox N ℓ, (s x) ^ 2 * |wPair ℓ (g2 v h) (x p.1) (x p.2)|) := by
              simpa using hb
      _ = ∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 *
            |wPairC ℓ (g2 v h) (x p.1) (x p.2)| := by
              dsimp [s]
              simp [wPairC]
              ring
  -- sharp mass: commute s = Q_{p2}(P_{p1}Φ) = P_{p1}(Q_{p2}Φ) and use the
  -- pq-`w₂`-mass atom (sharp, `n₊`-linear)
  have hmass' : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
      ≤ C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    calc
      (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
          = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)| := by
            apply Finset.sum_congr rfl
            intro p hp
            have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
            apply integral_congr_ae
            filter_upwards with x
            rw [aP_aQ_comm hℓ hne hΦc x]
      _ ≤ C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
            simpa [C2] using (pq_w2_mass_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc)
  have hsq' : |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
          wPairC ℓ (g2 v h) (x p.1) (x p.2)|
      = |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x p.1) (x p.2)| := by
    rw [hsq]
  calc
    |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
          wPairC ℓ (g2 v h) (x p.1) (x p.2)|
        = |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x p.1) (x p.2)| := hsq'
    _ ≤ ∑ p ∈ pairSet N, |∫ x in abox N ℓ,
            (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x p.1) (x p.2)| := by
          simpa using (Finset.abs_sum_le_sum_abs (s := pairSet N)
            (f := fun p : Fin N × Fin N => ∫ x in abox N ℓ,
              (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x p.1) (x p.2)))
    _ ≤ ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)| := by
          exact Finset.sum_le_sum hpair
    _ ≤ C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := hmass'
    _ = (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
          simp [C2]

/-- **Q2 T4 quarter-absorption sum lemma**: `|T4| ≤ C₁(ℓ³)⁻¹·(4·cS2+3·N̂·n₊)
+ (1/4)·q4word`.  The family sums are bounded directly (no local mass lets). -/
theorem q2_T4_abs_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g0 v h) (x p.1) (x p.2)|
      ≤ (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
        + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
  classical
  let C1 : ℝ := fsqC1 (a v)
  let mA : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let F1 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let F2 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let F3 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mS : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
        |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mQ : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)
  -- per-pair quarter bound, summed
  have hsum_le : (∑ p ∈ pairSet N,
      |∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ (5 / 2) * mA + (1 / 2) * mS + (1 / 8) * mQ := by
    calc
      (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
          ≤ ∑ p ∈ pairSet N,
              ((5 / 2) * (∫ x in abox N ℓ,
                  (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (1 / 2) * (∫ x in abox N ℓ,
                  ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
                  |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (1 / 8) * (∫ x in abox N ℓ,
                  (q4B ℓ (omC (Classical.choose h)) Φ (p.1, p.2) x) ^ 2 *
                    wPairC ℓ v (x p.1) (x p.2))) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
            simpa [wPairC] using (qcross_d2_pair_quarter hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
              (i := p.1) (j := p.2) hne hΦc)
      _ = (5 / 2) * mA + (1 / 2) * mS + (1 / 8) * mQ := by
            simp [mA, mS, mQ, Finset.sum_add_distrib, Finset.mul_sum]
  have hq4 : (1 / 8) * mQ = (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    dsimp [mQ]
    unfold q4word
    ring
  have hsum : |∑ p ∈ pairSet N,
        ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g0 v h) (x p.1) (x p.2)|
      ≤ (5 / 2) * mA + (1 / 2) * mS + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    rw [← hq4]
    calc
      |∑ p ∈ pairSet N,
          ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
            wPairC ℓ (g0 v h) (x p.1) (x p.2)|
          ≤ ∑ p ∈ pairSet N, |∫ x in abox N ℓ,
              (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
                wPairC ℓ (g0 v h) (x p.1) (x p.2)| := by
              simpa using (Finset.abs_sum_le_sum_abs (s := pairSet N)
                (f := fun p : Fin N × Fin N => ∫ x in abox N ℓ,
                  (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
                    wPairC ℓ (g0 v h) (x p.1) (x p.2)))
      _ ≤ (5 / 2) * mA + (1 / 2) * mS + (1 / 8) * mQ := hsum_le
  -- mS split over the three families (per-pair `sq3_mass_pair_le`, no lets)
  have hpp3 : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
            |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ 3 * ((∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
          + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
          + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)) := by
    calc
      (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
            |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
          ≤ ∑ p ∈ pairSet N, 3 * (
                (∫ x in abox N ℓ, (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
              + (∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
              + (∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
            have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
            have hg0s : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
            simpa [wPairC] using (sq3_mass_pair_le hℓ hg0i hg0s hRℓ
              (a := fun x => aP ℓ p.2 (aP ℓ p.1 Φ) x)
              (hac := aP_continuous hℓ p.2 (aP_continuous hℓ p.1 hΦc))
              (b := fun x => aP ℓ p.2 (aQ ℓ p.1 Φ) x)
              (hbc := aP_continuous hℓ p.2 (aQ_continuous hℓ p.1 hΦc))
              (c := fun x => aQ ℓ p.2 (aP ℓ p.1 Φ) x)
              (hcc := aQ_continuous hℓ p.2 (aP_continuous hℓ p.1 hΦc)) hne)
      _ = 3 * ((∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
            + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
            + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)) := by
          rw [← Finset.mul_sum]
          rw [Finset.sum_add_distrib]
          rw [Finset.sum_add_distrib]
  have hSsplit : mS ≤ 3 * (F1 + F2 + F3) := by
    have hb := hpp3
    have hconv : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
            |wPair ℓ (g0 v h) (x p.1) (x p.2)|) = mS := by
      dsimp [mS]
      simp [wPairC]
    have hconvF : 3 * ((∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
          + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
          + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|))
        = 3 * (F1 + F2 + F3) := by
      dsimp [F1, F2, F3]
      simp [wPairC]
    rwa [hconv, hconvF] at hb
  -- family bounds
  have hC1nn : 0 ≤ C1 := by
    have hav0 : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
    dsimp [C1, fsqC1]
    positivity
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  have hmA : mA ≤ C1 * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ := by
    have hmm := pp_w1_mass_le_cS2 hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
    simpa [mA, C1, wPairC] using hmm
  have hF1 : F1 ≤ C1 * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ := by
    calc
      F1 = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)| := by
            dsimp [F1]
            refine Finset.sum_congr rfl (fun p hp => ?_)
            apply integral_congr_ae
            filter_upwards with x
            congr 1
            rw [aP_comm hℓ p.1 p.2 hΦc x]
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ := by
            simpa [C1] using (pp_w1_mass_le_cS2 hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc)
  have hF2 : F2 ≤ C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    have hmm := pq_w1_mass_swap_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
    simpa [F2, C1, wPairC] using hmm
  have hF3 : F3 ≤ C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    have hmm := q_p_w1_mass_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
    simpa [F3, C1, wPairC] using hmm
  calc
    |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g0 v h) (x p.1) (x p.2)|
        ≤ (5 / 2) * mA + (1 / 2) * mS
            + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := hsum
    _ ≤ (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
          + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          let A : ℝ := C1 * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ
          let P : ℝ := C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ
          have hF1' : F1 ≤ A := by
            dsimp [A]
            exact hF1
          have hF2' : F2 ≤ P := by
            dsimp [P]
            exact hF2
          have hF3' : F3 ≤ P := by
            dsimp [P]
            exact hF3
          have hA' : mA ≤ A := by
            dsimp [A]
            exact hmA
          have hmass : (5 / 2) * mA + (1 / 2) * mS ≤ 4 * A + 3 * P := by
            nlinarith [hSsplit, hA', hF1', hF2', hF3']
          have h4 : 4 * A + 3 * P = C1 * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ)) := by
            dsimp [A, P]
            ring
          rw [← h4]
          nlinarith
    _ = (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
          + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          simp [C1]

/-- **Q2 in sharp mass form (assembled)**: `q2word = T1+T2+T3+T4` with the
four sharp summand bounds,

    q2word(N, ℓ, μ, w₁:=wPairC(g₀), w₂:=wPairC(g₂)) Φ
      ≥ − C₂·(ℓ³)⁻¹·(2·N̂·n₊) − C₁·(ℓ³)⁻¹·(4·cS2 + 3·N̂·n₊)
        − μ·C₁·n₊ − (1/4)·q4word(N,ℓ,wPairC(v),omC w₀)Φ . -/
theorem q2_sharp_lower {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 ≤ μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    - (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (2 * ((N : ℝ) * cnPlus ℓ Φ))
      - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
      - μ * (fsqC1 (a v)) * cnPlus ℓ Φ
      - (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
      ≤ q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ := by
  classical
  let w1 : ℝ³ → ℝ³ → ℝ := wPairC ℓ (g0 v h)
  let w2 : ℝ³ → ℝ³ → ℝ := wPairC ℓ (g2 v h)
  let C1 : ℝ := fsqC1 (a v)
  let C2 : ℝ := fsqC2 (a v)
  let T1 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) * w2 (x p.1) (x p.2)
  let T2 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) * w2 (x p.1) (x p.2)
  let T3 : ℝ := - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
      (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ w1 (x i)))
  let T4 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * w1 (x p.1) (x p.2)
  have hq2eq : q2word (N := N) ℓ μ w1 w2 Φ = T1 + T2 + T3 + T4 := by
    dsimp [q2word, T1, T2, T3, T4, w1, w2]
    ring
  have hT1 : - (C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ) ≤ T1 := by
    have hb := q2_T1_abs_le hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
    have hb' : |T1| ≤ C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
      simpa [C2, T1, w2] using hb
    exact (abs_le.mp hb').1
  have hT2 : - (C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ) ≤ T2 := by
    have hb := q2_T2_abs_le hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
    have hb' : |T2| ≤ C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
      simpa [C2, T2, w2] using hb
    exact (abs_le.mp hb').1
  have hT3 : - (μ * C1 * cnPlus ℓ Φ) ≤ T3 := by
    have hb := q2_T3_lower hℓ hμ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
    have hb' : - (μ * C1 * cnPlus ℓ Φ) ≤ T3 := by
      simpa [C1, T3, w1] using hb
    exact hb'
  have hT4 : - (C1 * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ)))
        - (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ ≤ T4 := by
    have hb := q2_T4_abs_le hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
    have hb' : |T4| ≤ C1 * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ + 3 * ((N : ℝ) * cnPlus ℓ Φ))
        + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
      simpa [C1, T4, w1] using hb
    have hneg := (abs_le.mp hb').1
    nlinarith [hneg]
  rw [hq2eq]
  have hsum : - (2 * C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ)
        - (C1 * (ℓ ^ 3)⁻¹ * (4 * cS2 ℓ Φ))
        - (3 * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ)
        - (μ * C1 * cnPlus ℓ Φ)
        - (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
      ≤ T1 + T2 + T3 + T4 := by
    nlinarith [hT1, hT2, hT3, hT4]
  convert hsum using 1
  dsimp [C1, C2]
  ring

end ChosenBranch

end BoseGases

end Submission
