import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.PotQ0Lower
import Submission.Work.Q2Lower
import Submission.Work.QCrossQuarter
import Submission.Work.QCrossQuarterD2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The q4-free per-state first bound (FS §10-style assembly)

With the two ¼-variants (`qcross_d13_quarter`, `qcross_d2_quarter`) the
coefficient condition `c₂ + c₃ = ½ ≤ 1` holds, and the assembled per-state
potential bound over the centred box becomes q4-free:

    qLHS ≥ q0RenVal − 5·qcrossC·(a v)·(N̂²/ℓ³ + μ²ℓ³)·J − μ·q2C0(a v)·cnPlus

Ingredients: `pot_q0_lower` (qLHS ≥ q0RenVal + q1+q2+q3+q4, exact q4),
`qcross_d11` (|q1| ≤ qcrossC·(a v)·Xbig·J), `q2_lower_quarter`
(q2 ≥ −3·qcrossC·(a v)·N̂²/ℓ³·J − μ·q2C0·cnPlus − (1/4)·q4word, via the
T1/T2/T3 bounds + `qcross_d2_quarter`), `qcross_d13_quarter`
(q3 ≥ −qcrossC·(a v)·N̂²/ℓ³·J − (1/4)·q4word), and the exact `+q4word` in the
potsplit identity: the q4-word coefficient closes as
`1 − 1/4 − 1/4 = 1/2 ≥ 0`.  `q2_lower_quarter` is the q4-free-friendly
version of `Q2Lower.q2_lower` (T4 bounded by the ¼-variant).
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

/-- q2 lower bound with the ¼-`q4word` (T4 via `qcross_d2_quarter`):
`q2 ≥ −3·qcrossC·(a v)·N̂²/ℓ³·J − μ·q2C0(a v)·cnPlus − (1/4)·q4word`. -/
lemma q2_lower_quarter {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 ≤ μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ ≥
      - (3 * qcrossC) * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
          (∫ x in abox N ℓ, (Φ x) ^ 2)
        - (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
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
  have h4 := qcross_d2_quarter (N := N) (ℓ := ℓ) hℓ (v := v) hv_nonneg hvrad hv_memL1 (R := R)
    hR hv_supp h hRℓ (Φ := Φ) hΦc
  have h1' : |T1| ≤ qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
      (∫ x in abox N ℓ, (Φ x) ^ 2) := by
    simpa [T1] using h1
  have h2' : |T2| ≤ qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
      (∫ x in abox N ℓ, (Φ x) ^ 2) := by
    simpa [T2] using h2
  have h4' : |T4| ≤ qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
      (∫ x in abox N ℓ, (Φ x) ^ 2)
      + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    simpa [T4] using h4
  have hT1 : - (qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
      (∫ x in abox N ℓ, (Φ x) ^ 2)) ≤ T1 := (abs_le.mp h1').1
  have hT2 : - (qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
      (∫ x in abox N ℓ, (Φ x) ^ 2)) ≤ T2 := (abs_le.mp h2').1
  have hT3 : - μ * q2C0 (a v) * cnPlus ℓ Φ ≤ T3 := by
    simpa [T3] using h3
  have hT4 : - (qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
      (∫ x in abox N ℓ, (Φ x) ^ 2))
      - (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ ≤ T4 := by
    have habs := (abs_le.mp h4').1
    linarith
  have hq : q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ =
      T1 + T2 + T3 + T4 := by
    unfold q2word
    simp only [T1, T2, T3, T4]
    ring
  rw [hq]
  linarith

/-- **The q4-free per-state first bound**: the potential word of the box
Hamiltonian is at least the renormalised-Q0 value minus
`5·qcrossC·(a v)·Xbig·J` minus the one-body `μ·q2C0(a v)·cnPlus` term — with
NO `q4word` on the right (the q4 coefficient closes as `1 − ¼ − ¼ = ½ ≥ 0`). -/
theorem pot_first_bound_q4free {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 ≤ μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ ≥
      q0RenVal (N := N) (v := v) ℓ μ Φ
        - (5 * qcrossC) * (a v) * (((N : ℝ) ^ 2 / ℓ ^ 3) + μ ^ 2 * ℓ ^ 3) *
            (∫ x in abox N ℓ, (Φ x) ^ 2)
        - μ * q2C0 (a v) * cnPlus ℓ Φ := by
  classical
  let J : ℝ := ∫ x in abox N ℓ, (Φ x) ^ 2
  have hpot := pot_q0_lower (N := N) (ℓ := ℓ) (μ := μ) hℓ hv_nonneg hvrad hv_memL1
    (R := R) hR hv_supp h hRℓ (Φ := Φ) hΦc
  have hq1 := qcross_d11 (N := N) (ℓ := ℓ) hℓ μ hμ (v := v) hv_nonneg hvrad hv_memL1
    (R := R) hR hv_supp h hRℓ (Φ := Φ) hΦc
  have hq2 := q2_lower_quarter (N := N) (ℓ := ℓ) (μ := μ) hℓ hμ hv_nonneg hvrad hv_memL1
    (R := R) hR hv_supp h hRℓ (Φ := Φ) hΦc
  have hq3 := qcross_d13_quarter (N := N) (ℓ := ℓ) hℓ (v := v) hv_nonneg hvrad hv_memL1
    (R := R) hR hv_supp h hRℓ (Φ := Φ) hΦc
  have hJ0 : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg (μ := (volume : Measure (XN N)).restrict (abox N ℓ))
      (by intro x; exact sq_nonneg (Φ x))
  have hAv : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hqC0 : 0 ≤ qcrossC := by dsimp [qcrossC]; positivity
  have hq4nn : 0 ≤ q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ :=
    q4_nonneg (N := N) hℓ (wPairC_nonneg hv_nonneg ℓ)
  -- lower bounds in the `J`-form
  have h1lo : - (qcrossC * (a v) * (((N : ℝ) ^ 2 / ℓ ^ 3) + μ ^ 2 * ℓ ^ 3) * J)
        ≤ q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ := by
    have hb : |q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ| ≤
        qcrossC * (a v) * (((N : ℝ) ^ 2 / ℓ ^ 3) + μ ^ 2 * ℓ ^ 3) * J := by
      simpa [J] using hq1
    exact (abs_le.mp hb).1
  have h2lo : - (3 * qcrossC) * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J
        - (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
        - μ * q2C0 (a v) * cnPlus ℓ Φ
        ≤ q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ := by
    simpa [J] using hq2
  have h3lo : - (qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J)
        - (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
        ≤ q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ := by
    have hb : |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ| ≤
        qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J
        + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
      simpa [J] using hq3
    have habs := (abs_le.mp hb).1
    have hring : - (qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J)
          - (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
        = - (qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J
            + (1 / 4) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ) := by ring
    rwa [hring]
  -- potsplit with the exact q4 word
  have hpot' : q0RenVal (N := N) (v := v) ℓ μ Φ
        + q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
        + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
      ≤ qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
    simpa using hpot
  -- absorption: 5·Xbig ≥ Xbig + 4·N̂²/ℓ³  (Xbig := N̂²/ℓ³ + μ²ℓ³)
  have hprod : 0 ≤ qcrossC * (a v) * J := by
    exact mul_nonneg (mul_nonneg hqC0 hAv) hJ0
  have h5le : qcrossC * (a v) * (((N : ℝ) ^ 2 / ℓ ^ 3) + μ ^ 2 * ℓ ^ 3 + 4 * ((N : ℝ) ^ 2 / ℓ ^ 3)) * J
      ≤ 5 * (qcrossC * (a v) * (((N : ℝ) ^ 2 / ℓ ^ 3) + μ ^ 2 * ℓ ^ 3) * J) := by
    have hA : ((N : ℝ) ^ 2 / ℓ ^ 3) + μ ^ 2 * ℓ ^ 3 + 4 * ((N : ℝ) ^ 2 / ℓ ^ 3)
        ≤ 5 * (((N : ℝ) ^ 2 / ℓ ^ 3) + μ ^ 2 * ℓ ^ 3) := by
      have hb : 0 ≤ μ ^ 2 * ℓ ^ 3 := by positivity
      nlinarith
    calc
      qcrossC * (a v) * (((N : ℝ) ^ 2 / ℓ ^ 3) + μ ^ 2 * ℓ ^ 3 + 4 * ((N : ℝ) ^ 2 / ℓ ^ 3)) * J
          = (qcrossC * (a v) * J) * (((N : ℝ) ^ 2 / ℓ ^ 3) + μ ^ 2 * ℓ ^ 3 + 4 * ((N : ℝ) ^ 2 / ℓ ^ 3)) := by ring
      _ ≤ (qcrossC * (a v) * J) * (5 * (((N : ℝ) ^ 2 / ℓ ^ 3) + μ ^ 2 * ℓ ^ 3)) := by
              exact mul_le_mul_of_nonneg_left hA hprod
      _ = 5 * (qcrossC * (a v) * (((N : ℝ) ^ 2 / ℓ ^ 3) + μ ^ 2 * ℓ ^ 3) * J) := by ring
  -- assemble (q4-word coefficient: +1 − 1/4 − 1/4 = +1/2 ≥ 0; no q4word remains)
  nlinarith [hpot', h1lo, h2lo, h3lo, hq4nn, h5le]

end BoseGases

end Submission
