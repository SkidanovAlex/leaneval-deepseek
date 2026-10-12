import ChallengeDeps
import Submission.Work.QCrossQuarter
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# First FS-precision Q3+Q4 atoms: sharp mass bounds and the sharp q3-bound

(Documentation header continued in the section below.) -/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The sharp `w₁`-mass constant (`g₀`-fibre over the cube, times `a`). -/
noncomputable def fsqC1 (a : ℝ) : ℝ := chiSup ^ 2 * 2 * (8 * π * a)

section ChosenBranch

/- Standing chosen-branch hypotheses. -/

/-- The `|w₁|`-weighted `(P Q)`-pair mass is `n₊`-linear:
`Σ_p∫(P_{p.1}Q_{p.2}Φ)²·|wPairC(ℓ,g₀)| ≤ C₁·(ℓ³)⁻¹·N̂·n₊`
(FS eq:BQwQleq corpus form). -/
lemma pq_w1_mass_le_cnPlus {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
  classical
  let C1 : ℝ := fsqC1 (a v)
  have hC1nn : 0 ≤ C1 := by
    have hav0 : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
    dsimp [C1, fsqC1]
    positivity
  have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) :=
    masssum_PQ_abs_le hℓ (le_of_lt hR) hRℓ (g0_integrable hR hv_supp h)
      (fun z hz => g0_zero_of_norm_ge hv_supp hz h) (g0_even hvrad h)
      (C := C1) (fun x => w1abs_fibre_acube_abs_le_used hR hv_nonneg hvrad hv_supp h hℓ hRℓ x)
      hΦc
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hP : 0 ≤ cnPlus ℓ Φ := cnPlus_nonneg
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
        = (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|) := by
          simp [wPairC]
    _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) := by
          simpa [C1] using hmm
    _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
          exact mul_le_mul_of_nonneg_left (pairSum_B_le hℓ hΦc) (mul_nonneg hC1nn hLinv)
    _ = (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
          simp [C1]
          ring

/-- The swapped `(P Q)`-family: `Σ_p∫(P_{p.2}Q_{p.1}Φ)²·|w₁| ≤ C₁·(ℓ³)⁻¹·N̂·n₊`. -/
lemma pq_w1_mass_swap_le_cnPlus {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
  classical
  let C1 : ℝ := fsqC1 (a v)
  have hC1nn : 0 ≤ C1 := by
    have hav0 : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
    dsimp [C1, fsqC1]
    positivity
  have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) :=
    masssum_Qsw_abs_le hℓ (le_of_lt hR) hRℓ (g0_integrable hR hv_supp h)
      (fun z hz => g0_zero_of_norm_ge hv_supp hz h) (g0_even hvrad h)
      (C := C1) (fun x => w1abs_fibre_acube_abs_le_used hR hv_nonneg hvrad hv_supp h hℓ hRℓ x)
      hΦc
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
        = (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|) := by
          simp [wPairC]
    _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) := by
          simpa [C1] using hmm
    _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
          exact mul_le_mul_of_nonneg_left (pairSum_Q_swap_le hℓ hΦc) (mul_nonneg hC1nn hLinv)
    _ = (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
          simp [C1]
          ring

/-- The `(Q_{p.2}P_{p.1})`-family equals the `(P_{p.1}Q_{p.2})`-family (slot
commutation), so its `|w₁|`-mass is also `≤ C₁·(ℓ³)⁻¹·N̂·n₊`. -/
lemma q_p_w1_mass_le_cnPlus {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
  have hEq : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
      = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)| := by
    apply Finset.sum_congr rfl
    intro p hp
    have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
    apply integral_congr_ae
    filter_upwards with x
    rw [(aP_aQ_comm hℓ hne hΦc x).symm]
  rw [hEq]
  exact pq_w1_mass_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc

/-- The `|w₁|`-weighted condensate-pair mass is `cS₂`-bounded:
`Σ_p∫(P_{p.1}P_{p.2}Φ)²·|wPairC(ℓ,g₀)| ≤ C₁·(ℓ³)⁻¹·cS2 ℓ Φ`
(the FS eq:Q3+Q4CS condensate part, corpus form). -/
lemma pp_w1_mass_le_cS2 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ := by
  classical
  let C1 : ℝ := fsqC1 (a v)
  have hC1nn : 0 ≤ C1 := by
    have hav0 : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
    dsimp [C1, fsqC1]
    positivity
  have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) :=
    masssum_PP_abs_le hℓ (le_of_lt hR) hRℓ (g0_integrable hR hv_supp h)
      (fun z hz => g0_zero_of_norm_ge hv_supp hz h) (g0_even hvrad h)
      (C := C1) (fun x => w1abs_fibre_acube_abs_le_used hR hv_nonneg hvrad hv_supp h hℓ hRℓ x)
      hΦc
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
        = (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|) := by
          simp [wPairC]
    _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := by
          simpa [C1] using hmm
    _ = C1 * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ := by
          rw [pairSum_A_eq]
    _ = (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ := by
          simp [C1]


theorem q3_sharp_mass {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ| ≤
      (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (3 * cS2 ℓ Φ + 9 * ((N : ℝ) * cnPlus ℓ Φ))
      + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
  classical
  let C1 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  let J : ℝ := ∫ x in abox N ℓ, (Φ x) ^ 2
  let mA : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mS : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
        |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mG2 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mG3 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mQ : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)
  let mG : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  have hsum_le : (∑ p ∈ pairSet N,
      |∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ (3 / 2) * mG + (1 / 2) * mS + (1 / 4) * mQ := by
    calc
      (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
          ≤ ∑ p ∈ pairSet N,
              ((3 / 2) * (∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (1 / 2) * (∫ x in abox N ℓ,
                  ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
                  |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (1 / 4) * (∫ x in abox N ℓ,
                  (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
            simpa [wPairC] using (qcross_d13_pair hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
              (i := p.1) (j := p.2) hne hΦc)
      _ = (3 / 2) * mG + (1 / 2) * mS + (1 / 4) * mQ := by
            simp [mG, mS, mQ, Finset.sum_add_distrib, Finset.mul_sum]
  have hq4 : mQ = 2 * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    dsimp [mQ]
    unfold q4word
    ring
  have hD : |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ| ≤
      3 * mG + mS + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    let q4 : ℝ := q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
    have hq4' : (1 / 2) * mQ = q4 := by
      dsimp [q4]
      rw [hq4]
      ring
    have h1 : |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ| ≤ 2 * ((3 / 2) * mG + (1 / 2) * mS + (1 / 4) * mQ) := by
      calc
        |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ|
            = |2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2))| := by
                rfl
        _ ≤ 2 * (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
                (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)|) := by
                have habs := Finset.abs_sum_le_sum_abs (s := pairSet N) (f := fun p : Fin N × Fin N =>
                  ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2))
                have h2 : (0 : ℝ) ≤ 2 := by norm_num
                calc
                  |2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2))|
                      = 2 * |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)| := by
                          rw [abs_mul, abs_of_nonneg h2]
                  _ ≤ 2 * (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
                          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)|) := by
                          exact mul_le_mul_of_nonneg_left habs h2
        _ ≤ 2 * ((3 / 2) * mG + (1 / 2) * mS + (1 / 4) * mQ) := by
                exact mul_le_mul_of_nonneg_left hsum_le (by norm_num)
    calc
      |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ| ≤ 2 * ((3 / 2) * mG + (1 / 2) * mS + (1 / 4) * mQ) := h1
      _ = 3 * mG + mS + (1 / 2) * mQ := by ring
      _ = 3 * mG + mS + q4 := by
            rw [← hq4']
      _ = 3 * mG + mS + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
            rfl
  have hSsplit : mS ≤ 3 * (mA + mG2 + mG3) := by
    calc
      mS = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2) *
          |wPairC ℓ (g0 v h) (x p.1) (x p.2)| := by
            rfl
      _ ≤ ∑ p ∈ pairSet N, 3 * (
            (∫ x in abox N ℓ, (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
          + (∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
          + (∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)) := by
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
      _ = 3 * (mA + mG2 + mG3) := by
          have hX : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|) = mA := by
            dsimp [mA]
            refine Finset.sum_congr rfl (fun p hp => ?_)
            apply integral_congr_ae
            filter_upwards with x
            rw [aP_comm hℓ p.1 p.2 hΦc x]
          have hc : (∑ p ∈ pairSet N, 3 * (
                (∫ x in abox N ℓ, (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)))
              = 3 * ((∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
                + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
                + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)) := by
                rw [← Finset.mul_sum]
                rw [Finset.sum_add_distrib]
                rw [Finset.sum_add_distrib]
          rw [hc]
          rw [hX]

  -- sharp mass tail (FS eq:BQwQleq atoms, Session-104): replace the coarse
  -- qcrossC · N̂²/ℓ³-degradation of the original qcross_d13 proof.
  let A : ℝ := (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ
  let P : ℝ := (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ
  have hmA' : mA ≤ A := by
    dsimp [A]
    dsimp [mA]
    exact pp_w1_mass_le_cS2 hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hmG2' : mG2 ≤ P := by
    dsimp [P]
    dsimp [mG2]
    exact pq_w1_mass_swap_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hmG3' : mG3 ≤ P := by
    dsimp [P]
    dsimp [mG3]
    exact q_p_w1_mass_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hmG' : mG ≤ P := by
    dsimp [P]
    dsimp [mG]
    exact pq_w1_mass_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  calc
    |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ|
        ≤ 3 * mG + mS + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := hD
    _ ≤ 3 * P + 3 * (A + P + P) + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          nlinarith [hSsplit, hmA', hmG2', hmG3', hmG']
    _ = (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (3 * cS2 ℓ Φ + 9 * ((N : ℝ) * cnPlus ℓ Φ))
          + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          dsimp [A, P]
          ring

/-- **Sharp Q3+Q4 C–S absorption** (FS eq:Q3+Q4CS, corpus per-sector mass
form): the `q4word`-square cancels, leaving only the `n₊`/`cS2`-linear sharp
mass term,

    q3word(ℓ, wPairC(g₀))Φ + q4word(ℓ, wPairC(v), omC w₀)Φ ≥
      − C₁·(ℓ³)⁻¹·(3·cS2 ℓ Φ + 9·N̂·n₊),   C₁ := chiSup²·2·(8π·a v). -/
theorem q3_sharp_quarter {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ| ≤
      (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (3 * cS2 ℓ Φ + 15 * ((N : ℝ) * cnPlus ℓ Φ))
      + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
  classical
  let C1 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  let J : ℝ := ∫ x in abox N ℓ, (Φ x) ^ 2
  let mA : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mS : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
        |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mG2 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mG3 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mQ : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)
  let mG : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  have hsum_le : (∑ p ∈ pairSet N,
      |∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ (9 / 2) * mG + (1 / 2) * mS + (1 / 16) * mQ := by
    calc
      (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
          ≤ ∑ p ∈ pairSet N,
              ((9 / 2) * (∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (1 / 2) * (∫ x in abox N ℓ,
                  ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
                  |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (1 / 16) * (∫ x in abox N ℓ,
                  (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
            simpa [wPairC] using (qcross_d13_pair_quarter hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
              (i := p.1) (j := p.2) hne hΦc)
      _ = (9 / 2) * mG + (1 / 2) * mS + (1 / 16) * mQ := by
            simp [mG, mS, mQ, Finset.sum_add_distrib, Finset.mul_sum]
  have hq4 : mQ = 2 * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    dsimp [mQ]
    unfold q4word
    ring
  have hD : |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ| ≤
      9 * mG + mS + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    let q4 : ℝ := q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
    have hq4' : (1 / 8) * mQ = (1 / 4) * q4 := by
      dsimp [q4]
      rw [hq4]
      ring
    have h1 : |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ| ≤ 2 * ((9 / 2) * mG + (1 / 2) * mS + (1 / 16) * mQ) := by
      calc
        |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ|
            = |2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2))| := by
                rfl
        _ ≤ 2 * (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
                (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)|) := by
                have habs := Finset.abs_sum_le_sum_abs (s := pairSet N) (f := fun p : Fin N × Fin N =>
                  ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2))
                have h2 : (0 : ℝ) ≤ 2 := by norm_num
                calc
                  |2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2))|
                      = 2 * |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)| := by
                          rw [abs_mul, abs_of_nonneg h2]
                  _ ≤ 2 * (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
                          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)|) := by
                          exact mul_le_mul_of_nonneg_left habs h2
        _ ≤ 2 * ((9 / 2) * mG + (1 / 2) * mS + (1 / 16) * mQ) := by
                exact mul_le_mul_of_nonneg_left hsum_le (by norm_num)
    calc
      |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ| ≤ 2 * ((9 / 2) * mG + (1 / 2) * mS + (1 / 16) * mQ) := h1
      _ = 9 * mG + mS + (1 / 8) * mQ := by ring
      _ = 9 * mG + mS + (1 / 4) * q4 := by
            rw [← hq4']
      _ = 9 * mG + mS + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
            rfl
  have hSsplit : mS ≤ 3 * (mA + mG2 + mG3) := by
    calc
      mS = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2) *
          |wPairC ℓ (g0 v h) (x p.1) (x p.2)| := by
            rfl
      _ ≤ ∑ p ∈ pairSet N, 3 * (
            (∫ x in abox N ℓ, (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
          + (∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
          + (∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)) := by
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
      _ = 3 * (mA + mG2 + mG3) := by
          have hX : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|) = mA := by
            dsimp [mA]
            refine Finset.sum_congr rfl (fun p hp => ?_)
            apply integral_congr_ae
            filter_upwards with x
            rw [aP_comm hℓ p.1 p.2 hΦc x]
          have hc : (∑ p ∈ pairSet N, 3 * (
                (∫ x in abox N ℓ, (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)))
              = 3 * ((∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
                + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
                + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)) := by
                rw [← Finset.mul_sum]
                rw [Finset.sum_add_distrib]
                rw [Finset.sum_add_distrib]
          rw [hc]
          rw [hX]

  -- sharp mass tail (FS eq:BQwQleq atoms, Session-104): replace the coarse
  -- qcrossC · N̂²/ℓ³-degradation of the original qcross_d13 proof.
  let A : ℝ := (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ
  let P : ℝ := (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ
  have hmA' : mA ≤ A := by
    dsimp [A]
    dsimp [mA]
    exact pp_w1_mass_le_cS2 hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hmG2' : mG2 ≤ P := by
    dsimp [P]
    dsimp [mG2]
    exact pq_w1_mass_swap_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hmG3' : mG3 ≤ P := by
    dsimp [P]
    dsimp [mG3]
    exact q_p_w1_mass_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hmG' : mG ≤ P := by
    dsimp [P]
    dsimp [mG]
    exact pq_w1_mass_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  calc
    |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ|
        ≤ 9 * mG + mS + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := hD
    _ ≤ 9 * P + 3 * (A + P + P) + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          nlinarith [hSsplit, hmA', hmG2', hmG3', hmG']
    _ = (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (3 * cS2 ℓ Φ + 15 * ((N : ℝ) * cnPlus ℓ Φ))
          + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          dsimp [A, P]
          ring

/-- **Sharp Q3+Q4 C–S absorption** (FS eq:Q3+Q4CS, corpus per-sector mass
form): the `q4word`-square cancels, leaving only the `n₊`/`cS2`-linear sharp
mass term,

    q3word(ℓ, wPairC(g₀))Φ + q4word(ℓ, wPairC(v), omC w₀)Φ ≥
      − C₁·(ℓ³)⁻¹·(3·cS2 ℓ Φ + 9·N̂·n₊),   C₁ := chiSup²·2·(8π·a v). -/

theorem q3_q4_sharp_lower {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
      + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
      ≥ - (fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (3 * cS2 ℓ Φ + 9 * ((N : ℝ) * cnPlus ℓ Φ)) := by
  have hb := q3_sharp_mass hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  have hq4nn : 0 ≤ q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ :=
    q4_nonneg hℓ (wPairC_nonneg hv_nonneg ℓ)
  have hneg : -((fsqC1 (a v)) * (ℓ ^ 3)⁻¹ * (3 * cS2 ℓ Φ + 9 * ((N : ℝ) * cnPlus ℓ Φ))
      + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ) ≤
      q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ := by
    nlinarith [abs_le.mp hb]
  nlinarith

end ChosenBranch

end BoseGases

end Submission
