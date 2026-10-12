import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.QCrossD
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Per-state lower bounds for the three open summands of `q2word` (FS eq:Q2n0)

`q2word` (FS `eq:DefQ2`, corpus `PotWords.q2word`) splits, for the chosen
kernels `w1 := wPairC ℓ (g0 v h)`, `w2 := wPairC ℓ (g2 v h)`, into four
summands over `pairSet N` (`p = (i,j)`, `i ≠ j`):

  term1 = Σ_p ∫ (P_i Q_j Φ)·(P_j Q_i Φ)·w₂          (FS P_iQ_j w₂ P_jQ_i)
  term2 = Σ_p ∫ (P_i Q_j Φ)·(Q_j P_i Φ)·w₂          (FS P_iQ_j w₂ Q_jP_i)
  term3 = − μ·Σ_i ∫ (Q_i Φ)²·(∫_{acube} w1(x_i,·))  (one-body excited term)
  term4 = Σ_p ∫ (P_i P_j Φ)·(Q_j Q_i Φ)·w₁          (FS PP·w₁·QQ; |term4|
          bounded by `QCrossD.qcross_d2`)

Bounds here (all per-state, unconditional):

  * `q2massPQ_swap_le` : the swapped `(P Q)`-mass ≤ `q1massPQ_le`-bound;
  * `q2_first_abs_le`  : |term1| ≤ qcrossC·(a v)·N̂²/ℓ³·J
                          (AM–GM per pair + the `(P Q)`-masses);
  * `q2_second_abs_le` : |term2| ≤ qcrossC·(a v)·N̂²/ℓ³·J
                          (commutation `P_iQ_j = Q_jP_i`, one mass);
  * `q2_onebody_lower` : term3 ≥ −μ·(chiSup²·2·(8πa v))·cnPlus;
  * `q2_lower`         : q2word ≥ −2·qcrossC·(a v)·N̂²/ℓ³·J − q4word
                              − μ·q2C0·cnPlus.

Notation: `J = ∫_abox Φ²`, `N̂ = (N : ℝ)`, `cnPlus = Σ_i‖Q_iΦ‖²`.
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

/-- The one-body constant of the `−μΣQ(∫w1)Q` term: `chiSup²·2·(8πa v)`. -/
noncomputable def q2C0 (a : ℝ) : ℝ := chiSup ^ 2 * 2 * (8 * π * a)

/-- The `(P Q)`-mass constant of `q1massPQ_le`: `chiSup²·2·(16πa v)`. -/
noncomputable def q2C2 (a : ℝ) : ℝ := chiSup ^ 2 * 2 * (16 * π * a)

/-- The `(P Q)`-mass sum with the swapped factor is bounded by the
`q1massPQ_le` bound (relabel the pair set; `w₂` is symmetric since `g2` is
even). -/
lemma q2massPQ_swap_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
      ≤ (chiSup ^ 2 * 2 * (16 * π * a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 *
          (∫ x in abox N ℓ, (Φ x) ^ 2) := by
  classical
  -- w₂ is symmetric (g2 even), hence its absolute value is symmetric
  have hsym : ∀ a b : ℝ³,
      |wPairC ℓ (g2 v h) a b| = |wPairC ℓ (g2 v h) b a| := by
    intro a b
    rw [wPairC_sym (g2_even hvrad h) ℓ a b]
  -- relabel: LHS = Σ_p ∫(P_{p1}Q_{p2}Φ)²·|w₂(x_{p2},x_{p1})|
  have hL : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
      = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)| := by
    calc
      (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
          = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.2) (x p.1)| := by
              -- swap the roles of the two coordinates of p
              simpa [Function.comp_def] using
                (sum_pairSet_swap (N := N)
                  (fun p : Fin N × Fin N => ∫ x in abox N ℓ,
                    (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 *
                      |wPairC ℓ (g2 v h) (x p.2) (x p.1)|))
      _ = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)| := by
            apply Finset.sum_congr rfl
            intro p hp
            apply integral_congr_ae
            filter_upwards with x
            rw [hsym (x p.1) (x p.2)]
  rw [hL]
  exact q1massPQ_le (N := N) (ℓ := ℓ) hℓ hv_nonneg hvrad (R := R) hR hv_supp h hRℓ
    (Φ := Φ) hΦc

/-- The term-1 summand of `q2word` (FS `P_iQ_jw₂P_jQ_i`), per-state:
`|term1| ≤ qcrossC·(a v)·N̂²/ℓ³·J`. -/
lemma q2_first_abs_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g2 v h) (x p.1) (x p.2)|
      ≤ qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
  classical
  let M1 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|
  let M2 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|
  let J : ℝ := ∫ x in abox N ℓ, (Φ x) ^ 2
  let C2 : ℝ := chiSup ^ 2 * 2 * (16 * π * a v)
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg (μ := (volume : Measure (XN N)).restrict (abox N ℓ))
      (by intro x; exact sq_nonneg (Φ x))
  have hAv : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hC2nn : 0 ≤ C2 := by
    dsimp [C2]
    have h16 : 0 ≤ 16 * π * a v := by positivity
    exact mul_nonneg (mul_nonneg (sq_nonneg chiSup) (by norm_num : (0 : ℝ) ≤ 2)) h16
  have hM1 : M1 ≤ C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hb := q1massPQ_le (N := N) (ℓ := ℓ) hℓ hv_nonneg hvrad (R := R) hR hv_supp h
      hRℓ (Φ := Φ) hΦc
    simpa [M1, C2, J] using hb
  have hM2 : M2 ≤ C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hb := q2massPQ_swap_le (N := N) (ℓ := ℓ) hℓ hv_nonneg hvrad (R := R) hR hv_supp h
      hRℓ (Φ := Φ) hΦc
    simpa [M2, C2, J] using hb
  have hmain : |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g2 v h) (x p.1) (x p.2)|
      ≤ (1 / 2) * M1 + (1 / 2) * M2 := by
    calc
      |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
            wPairC ℓ (g2 v h) (x p.1) (x p.2)|
          ≤ ∑ p ∈ pairSet N,
              |∫ x in abox N ℓ,
                (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
                  wPair ℓ (g2 v h) (x p.1) (x p.2)| := by
              simpa [wPairC] using (Finset.abs_sum_le_sum_abs (s := pairSet N)
                (f := fun p : Fin N × Fin N => ∫ x in abox N ℓ,
                  (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
                    wPair ℓ (g2 v h) (x p.1) (x p.2)))
      _ ≤ ∑ p ∈ pairSet N,
            ((1 / 2) * (∫ x in abox N ℓ,
                (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g2 v h) (x p.1) (x p.2)|)
              + (1 / 2) * (∫ x in abox N ℓ,
                (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g2 v h) (x p.1) (x p.2)|)) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
          have hf : Continuous (aP ℓ p.1 (aQ ℓ p.2 Φ)) :=
            aP_continuous hℓ p.1 (aQ_continuous hℓ p.2 hΦc)
          have hg : Continuous (aP ℓ p.2 (aQ ℓ p.1 Φ)) :=
            aP_continuous hℓ p.2 (aQ_continuous hℓ p.1 hΦc)
          have hb := abs_integral_mul_mul_wPair_le_half hℓ (g2_integrable hR hv_nonneg hvrad hv_supp h)
            (fun z hz => g2_zero_of_norm_ge hv_supp hz h) hRℓ hne hf hg
          simpa [mul_assoc, wPairC] using hb
      _ = (1 / 2) * M1 + (1 / 2) * M2 := by
          dsimp [M1, M2]
          simp only [wPairC]
          rw [Finset.sum_add_distrib]
          simp_rw [← Finset.mul_sum]
  have hX : (1 / 2) * M1 + (1 / 2) * M2 ≤ C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hX' : C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J = (1 / 2) * (C2 * (ℓ ^ 3)⁻¹ * (N : ℝ)^2 * J)
        + (1 / 2) * (C2 * (ℓ ^ 3)⁻¹ * (N : ℝ)^2 * J) := by ring
    rw [hX']
    linarith
  have hfin : C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
      ≤ qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J := by
    have hq : 0 ≤ qcrossC * (a v) := by
      dsimp [qcrossC]
      positivity
    have hN : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg (N : ℝ)
    have hlinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
    have hc : C2 ≤ qcrossC * (a v) := by
      dsimp [C2, qcrossC]
      have hchi : 0 ≤ chiSup ^ 2 := sq_nonneg chiSup
      calc
        chiSup ^ 2 * 2 * (16 * π * a v)
            = chiSup ^ 2 * (32 * π) * (a v) := by ring
        _ ≤ chiSup ^ 2 * (8 * π * 1000000) * (a v) := by
              have h32 : (32 * π : ℝ) ≤ 8 * π * 1000000 := by
                nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ (8 * 1000000 - 32)) Real.pi_nonneg]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h32 hchi) hAv
        _ = (1000000 * chiSup ^ 2 * (8 * π)) * (a v) := by ring
    calc
      C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
          = (C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2) * J := by ring
      _ ≤ ((qcrossC * (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2) * J := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hc hlinv) hN) hJ
      _ = qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J := by
              rw [div_eq_mul_inv]
              ring
  exact le_trans (le_trans hmain hX) hfin


/-- The term-2 summand of `q2word` (FS `P_iQ_jw₂Q_jP_i`), per-state:
`|term2| ≤ qcrossC·(a v)·N̂²/ℓ³·J`.  (`P_iQ_j = Q_jP_i`, so the summand is a
sum of squares times `w₂`; its absolute value is one `(P Q)`-mass.) -/
lemma q2_second_abs_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
          wPairC ℓ (g2 v h) (x p.1) (x p.2)|
      ≤ qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
  classical
  let J : ℝ := ∫ x in abox N ℓ, (Φ x) ^ 2
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
  -- mass bound: commute s = Q_{p2}(P_{p1}Φ) = P_{p1}(Q_{p2}Φ) and use q1massPQ_le
  have hmass : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
      ≤ (chiSup ^ 2 * 2 * (16 * π * a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
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
      _ ≤ (chiSup ^ 2 * 2 * (16 * π * a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
            have hb := q1massPQ_le (N := N) (ℓ := ℓ) hℓ hv_nonneg hvrad (R := R) hR hv_supp h
              hRℓ (Φ := Φ) hΦc
            simpa [J] using hb
  -- assemble the two-step chain and the constant comparison
  have hmain : |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x p.1) (x p.2)|
      ≤ (chiSup ^ 2 * 2 * (16 * π * a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    calc
      |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x p.1) (x p.2)|
          ≤ ∑ p ∈ pairSet N, |∫ x in abox N ℓ,
              (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x p.1) (x p.2)| := by
              simpa using (Finset.abs_sum_le_sum_abs (s := pairSet N)
                (f := fun p : Fin N × Fin N => ∫ x in abox N ℓ,
                  (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x p.1) (x p.2)))
      _ ≤ ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)| := by
            exact Finset.sum_le_sum hpair
      _ ≤ (chiSup ^ 2 * 2 * (16 * π * a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := hmass
  have hAv : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hJ0 : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg (μ := (volume : Measure (XN N)).restrict (abox N ℓ))
      (by intro x; exact sq_nonneg (Φ x))
  have hC : (chiSup ^ 2 * 2 * (16 * π * a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
      ≤ qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J := by
    let C2 : ℝ := chiSup ^ 2 * 2 * (16 * π * a v)
    have hc : C2 ≤ qcrossC * (a v) := by
      dsimp [C2, qcrossC]
      have hchi : 0 ≤ chiSup ^ 2 := sq_nonneg chiSup
      have h32 : (32 * π : ℝ) ≤ 8 * π * 1000000 := by
        nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ (8 * 1000000 - 32)) Real.pi_nonneg]
      calc
        chiSup ^ 2 * 2 * (16 * π * a v)
            = chiSup ^ 2 * (32 * π) * (a v) := by ring
        _ ≤ chiSup ^ 2 * (8 * π * 1000000) * (a v) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h32 hchi) hAv
        _ = (1000000 * chiSup ^ 2 * (8 * π)) * (a v) := by ring
    have hN0 : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg (N : ℝ)
    have hlinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
    calc
      C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
          = (C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2) * J := by ring
      _ ≤ ((qcrossC * (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2) * J := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hc hlinv) hN0) hJ0
      _ = qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J := by
              rw [div_eq_mul_inv]
              ring
  have hsq' : |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
          wPairC ℓ (g2 v h) (x p.1) (x p.2)|
      = |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * wPairC ℓ (g2 v h) (x p.1) (x p.2)| := by
    rw [hsq]
  rw [hsq']
  exact le_trans hmain hC


/-- The one-body summand of `q2word` (`−μΣᵢQᵢ(∫w₁)Qᵢ`), per-state:
`term3 ≥ −μ·(chiSup²·2·(8πa v))·cnPlus`.  (The `w₁`-fibre is pointwise
`≤ chiSup²·2·8πa v`, `(QᵢΦ)² ≥ 0`, and `μ ≥ 0` flips the sign.) -/
lemma q2_onebody_lower {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 ≤ μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
      ≥ - μ * q2C0 (a v) * cnPlus ℓ Φ := by
  classical
  let C0 : ℝ := q2C0 (a v)
  have hfib : ∀ z : ℝ³, |w1Fibre ℓ (wPairC ℓ (g0 v h)) z| ≤ C0 := by
    intro z
    have hb := w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
    dsimp [C0, q2C0]
    simpa [w1Fibre, wPairC] using hb
  have hper : ∀ i : Fin N,
      (∫ x in abox N ℓ,
          (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
        ≤ C0 * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
    intro i
    let F : ℝ³ → ℝ := fun z => w1Fibre ℓ (wPairC ℓ (g0 v h)) z
    let S : XN N → ℝ := fun x => (aQ ℓ i Φ x) ^ 2
    have hSc : Continuous S := by
      dsimp [S]
      exact (aQ_continuous hℓ i hΦc).pow 2
    have hFm : AEStronglyMeasurable F (volume.restrict (acube ℓ)) := by
      dsimp [F]
      have hfac := fibre_acube_aem (ℓ := ℓ) (h := g0 v h) (g0_integrable hR hv_supp h)
      simpa [w1Fibre, wPairC] using hfac
    have hInt : IntegrableOn (fun x : XN N => S x * F (x i)) (abox N ℓ) volume := by
      exact integrableOn_slot_fibre hℓ i hFm (fun z hz => by
        have hb := hfib z
        simpa [F, C0] using hb) hSc
    have hpt : ∀ x : XN N, S x * F (x i) ≤ S x * C0 := by
      intro x
      have hFc : F (x i) ≤ C0 := by
        dsimp [F]
        exact le_trans (le_abs_self (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))) (hfib (x i))
      exact mul_le_mul_of_nonneg_left hFc (sq_nonneg (aQ ℓ i Φ x))
    have hIntR : IntegrableOn (fun x : XN N => S x * C0) (abox N ℓ) volume := by
      have hEq : (fun x : XN N => S x * C0) = fun x : XN N => C0 * (aQ ℓ i Φ x) ^ 2 := by
        funext x
        dsimp [S]
        ring
      rw [hEq]
      exact (integrableOn_abox_of_continuous hℓ ((aQ_continuous hℓ i hΦc).pow 2)).const_mul C0
    calc
      (∫ x in abox N ℓ, S x * F (x i))
          ≤ ∫ x in abox N ℓ, S x * C0 := by
              exact integral_mono_ae (μ := (volume : Measure (XN N)).restrict (abox N ℓ))
                hInt hIntR (by filter_upwards with x; exact hpt x)
      _ = C0 * (∫ x in abox N ℓ, S x) := by
              rw [← integral_const_mul]
              apply integral_congr_ae
              filter_upwards with x
              ring
  have hsum : (∑ i : Fin N, ∫ x in abox N ℓ,
        (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
      ≤ C0 * cnPlus ℓ Φ := by
    calc
      (∑ i : Fin N, ∫ x in abox N ℓ,
          (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
          ≤ ∑ i : Fin N, C0 * (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
              exact Finset.sum_le_sum (fun i hi => hper i)
      _ = C0 * cnPlus ℓ Φ := by
              simpa [cnPlus] using
                ((Finset.mul_sum (s := Finset.univ) (a := C0)
                  (f := fun i : Fin N => ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)).symm)
  have hmul : μ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
      ≤ μ * (C0 * cnPlus ℓ Φ) := mul_le_mul_of_nonneg_left hsum hμ
  linarith

/-- **Per-state lower bound on the full `q2word`** (FS `eq:Q2n0` rough form):

`q2word ≥ −3·qcrossC·(a v)·N̂²/ℓ³·J − q4word − μ·q2C0(a v)·cnPlus`.  (Terms 1,2
via the mass bounds above, term 3 via the one-body bound, term 4 via
`QCrossD.qcross_d2`.) -/
lemma q2_lower {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 ≤ μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ ≥
      - (3 * qcrossC) * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
          (∫ x in abox N ℓ, (Φ x) ^ 2)
        - q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
        - μ * q2C0 (a v) * cnPlus ℓ Φ := by
  classical
  let T1 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
        wPairC ℓ (g2 v h) (x p.1) (x p.2)
  let T2 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
        wPairC ℓ (g2 v h) (x p.1) (x p.2)
  let T3 : ℝ := - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
      (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)))
  let T4 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
        wPairC ℓ (g0 v h) (x p.1) (x p.2)
  have h1 := q2_first_abs_le (N := N) (ℓ := ℓ) hℓ hv_nonneg hvrad (R := R) hR hv_supp h
    hRℓ (Φ := Φ) hΦc
  have h2 := q2_second_abs_le (N := N) (ℓ := ℓ) hℓ hv_nonneg hvrad (R := R) hR hv_supp h
    hRℓ (Φ := Φ) hΦc
  have h3 := q2_onebody_lower (N := N) (ℓ := ℓ) (μ := μ) hℓ hμ hv_nonneg hvrad (R := R)
    hR hv_supp h hRℓ (Φ := Φ) hΦc
  have h4 := qcross_d2 (N := N) (ℓ := ℓ) hℓ (v := v) hv_nonneg hvrad hv_memL1 (R := R)
    hR hv_supp h hRℓ (Φ := Φ) hΦc
  have h1' : |T1| ≤ qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
      (∫ x in abox N ℓ, (Φ x) ^ 2) := by
    simpa [T1] using h1
  have h2' : |T2| ≤ qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
      (∫ x in abox N ℓ, (Φ x) ^ 2) := by
    simpa [T2] using h2
  have h4' : |T4| ≤ qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
      (∫ x in abox N ℓ, (Φ x) ^ 2)
      + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    simpa [T4] using h4
  have hT1 : - (qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
      (∫ x in abox N ℓ, (Φ x) ^ 2)) ≤ T1 := (abs_le.mp h1').1
  have hT2 : - (qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
      (∫ x in abox N ℓ, (Φ x) ^ 2)) ≤ T2 := (abs_le.mp h2').1
  have hT3 : - μ * q2C0 (a v) * cnPlus ℓ Φ ≤ T3 := by
    simpa [T3] using h3
  have hT4 : - (qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
      (∫ x in abox N ℓ, (Φ x) ^ 2))
      - q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ ≤ T4 := by
    have habs := (abs_le.mp h4').1
    linarith
  have hq : q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ =
      T1 + T2 + T3 + T4 := by
    unfold q2word
    simp only [T1, T2, T3, T4]
    ring
  rw [hq]
  linarith


end BoseGases

end Submission
