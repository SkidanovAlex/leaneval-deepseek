import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1M

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# `Work.BoseFixB1M.boxMuSum` — the `μ`-weighted box words reassemble into `Φ²`

The FS-faithful box projections `Pᵢ = boxPInd volA A i` and `Qᵢ = boxQInd volA A i` of
`Submission/Work/UBBInputs8/Defs.lean` satisfy `Pᵢ + Qᵢ = 1_A(xᵢ)·` *definitionally*.  Hence at
every point `x` the mixed square `(PᵢΦ)² + 2(QᵢΦ)(PᵢΦ) + (QᵢΦ)²` is `(1_A(xᵢ)Φ)²`.  Multiplying
by the one-body fibre `w1Fibre ℓ w1 (xᵢ)` and using that the fibre vanishes whenever `xᵢ ∉ A`
(the hypothesis `hvan`), the extra factor `1_A(xᵢ)` may be dropped:

  `Σᵢ ∫ (PᵢΦ)²·fib + 2 Σᵢ ∫ (QᵢΦ)(PᵢΦ)·fib + Σᵢ ∫ (QᵢΦ)²·fib = Σᵢ ∫ Φ²·fib`.

Unlike `Work.BoseFixB1S.boxMuSumAgree` (which assumes `Φ` and `w1` continuous and derives
integrability from boundedness), here the three integrabilities are *hypotheses*, so the whole
argument is pure integral linearity plus the pointwise identity.
-/

/-- **The pointwise `μ`-identity.**  Writing `P = boxPInd volA A i Φ x`,
`Q = boxQInd volA A i Φ x`, `F = w1Fibre ℓ w1 (x i)`:  since `P + Q = 1_A(xᵢ)·Φ x`, the mixed
square `P² + 2QP + Q²` is the square of `1_A(xᵢ)·Φ x`; multiplying by `F` and using
`1_A(xᵢ)·1_A(xᵢ) = 1_A(xᵢ)` gives `(P² + 2QP + Q²)·F = Φ x²·F`, the correction on the
complement of `A` being that `F = 0` there. -/
theorem boxMu_pointwise {N : ℕ} {ℓ volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))}
    {w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hvan : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ A → w1Fibre ℓ w1 z = 0)
    {Φ : X N → ℝ} (i : Fin N) (x : X N) :
    (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * w1Fibre ℓ w1 (x i)
      + 2 * ((Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x)
          * w1Fibre ℓ w1 (x i))
      + (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * w1Fibre ℓ w1 (x i)
    = (Φ x) ^ 2 * w1Fibre ℓ w1 (x i) := by
  set P := Work.UBBInputs8.boxPInd volA A i Φ x with hP
  set Q := Work.UBBInputs8.boxQInd volA A i Φ x with hQ
  set F := w1Fibre ℓ w1 (x i) with hF
  have hPQ : P + Q = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x := by
    rw [hP, hQ]
    unfold Work.UBBInputs8.boxQInd
    ring
  have hsq : P ^ 2 + 2 * (Q * P) + Q ^ 2
      = (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 := by
    calc P ^ 2 + 2 * (Q * P) + Q ^ 2 = (P + Q) ^ 2 := by ring
      _ = (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 := by rw [hPQ]
  have hind : (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2
      = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x ^ 2 := by
    rw [mul_pow]
    by_cases hx : x i ∈ A
    · rw [Set.indicator_of_mem hx]
      ring
    · rw [Set.indicator_of_notMem hx]
      ring
  have hmul : (P ^ 2 + 2 * (Q * P) + Q ^ 2) * F = (Φ x) ^ 2 * F := by
    rw [hsq, hind]
    by_cases hx : x i ∈ A
    · rw [Set.indicator_of_mem hx, one_mul]
    · rw [Set.indicator_of_notMem hx, zero_mul, zero_mul, hF, hvan _ hx, mul_zero]
  calc P ^ 2 * F + 2 * (Q * P * F) + Q ^ 2 * F
      = (P ^ 2 + 2 * (Q * P) + Q ^ 2) * F := by ring
    _ = (Φ x) ^ 2 * F := hmul

/-- **The per-slot `μ`-identity**:
`boxMuP i + 2·boxMuQP i + boxMuQ i = boxMuPhi i`, from the three integrabilities alone. -/
theorem boxMu_slot {N : ℕ} {ℓ volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))}
    {w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hvan : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ A → w1Fibre ℓ w1 z = 0)
    {Φ : X N → ℝ} (i : Fin N)
    (hIntP : IntegrableOn (fun x : X N =>
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * w1Fibre ℓ w1 (x i))
        (abox N ℓ) volume)
    (hIntQP : IntegrableOn (fun x : X N =>
        (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x) *
          w1Fibre ℓ w1 (x i))
        (abox N ℓ) volume)
    (hIntQ : IntegrableOn (fun x : X N =>
        (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * w1Fibre ℓ w1 (x i))
        (abox N ℓ) volume) :
    Work.BoseFixB1S.boxMuP volA ℓ A w1 Φ i
      + 2 * Work.BoseFixB1S.boxMuQP volA ℓ A w1 Φ i
      + Work.BoseFixB1S.boxMuQ volA ℓ A w1 Φ i
      = Work.BoseFixB1S.boxMuPhi (N := N) ℓ w1 Φ i := by
  classical
  simp only [Work.BoseFixB1S.boxMuP, Work.BoseFixB1S.boxMuQP, Work.BoseFixB1S.boxMuQ,
    Work.BoseFixB1S.boxMuPhi]
  set G : X N → ℝ := fun x => (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * w1Fibre ℓ w1 (x i)
    with hG
  set H : X N → ℝ := fun x => (Work.UBBInputs8.boxQInd volA A i Φ x) *
      (Work.UBBInputs8.boxPInd volA A i Φ x) * w1Fibre ℓ w1 (x i) with hH
  set K : X N → ℝ := fun x => (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * w1Fibre ℓ w1 (x i)
    with hK
  set D : X N → ℝ := fun x => (Φ x) ^ 2 * w1Fibre ℓ w1 (x i) with hD
  have hIntG : IntegrableOn G (abox N ℓ) volume := by rwa [hG]
  have hIntH : IntegrableOn H (abox N ℓ) volume := by rwa [hH]
  have hIntK : IntegrableOn K (abox N ℓ) volume := by rwa [hK]
  have h2 : (2 : ℝ) * (∫ x in abox N ℓ, H x) = ∫ x in abox N ℓ, 2 * H x :=
    (integral_const_mul (2 : ℝ) H).symm
  have hA1 : (∫ x in abox N ℓ, G x) + (∫ x in abox N ℓ, 2 * H x)
      = ∫ x in abox N ℓ, (G x + 2 * H x) :=
    (integral_add hIntG (hIntH.const_mul 2)).symm
  have hA2 : (∫ x in abox N ℓ, (G x + 2 * H x)) + (∫ x in abox N ℓ, K x)
      = ∫ x in abox N ℓ, ((G x + 2 * H x) + K x) :=
    (integral_add (hIntG.add (hIntH.const_mul 2)) hIntK).symm
  have hA3 : (∫ x in abox N ℓ, ((G x + 2 * H x) + K x)) = ∫ x in abox N ℓ, D x := by
    apply setIntegral_congr_fun (abox_measurable N ℓ)
    intro x _
    simp only [hG, hH, hK, hD]
    exact boxMu_pointwise hvan i x
  linarith [h2, hA1, hA2, hA3]

theorem boxMuSum {N : ℕ} {ℓ volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))}
    {w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hvan : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ A →
      Submission.BoseGases.w1Fibre ℓ w1 z = 0)
    {Φ : Submission.BoseGases.X N → ℝ}
    (hIntP : ∀ i : Fin N, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 *
          Submission.BoseGases.w1Fibre ℓ w1 (x i))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hIntQP : ∀ i : Fin N, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A i Φ x) *
          Submission.BoseGases.w1Fibre ℓ w1 (x i))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hIntQ : ∀ i : Fin N, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 *
          Submission.BoseGases.w1Fibre ℓ w1 (x i))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    (∑ i : Fin N, Work.BoseFixB1S.boxMuP volA ℓ A w1 Φ i)
      + 2 * (∑ i : Fin N, Work.BoseFixB1S.boxMuQP volA ℓ A w1 Φ i)
      + (∑ i : Fin N, Work.BoseFixB1S.boxMuQ volA ℓ A w1 Φ i)
      = ∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ w1 Φ i := by
  have hLHS : (∑ i : Fin N, Work.BoseFixB1S.boxMuP volA ℓ A w1 Φ i)
        + 2 * (∑ i : Fin N, Work.BoseFixB1S.boxMuQP volA ℓ A w1 Φ i)
        + (∑ i : Fin N, Work.BoseFixB1S.boxMuQ volA ℓ A w1 Φ i)
      = ∑ i : Fin N, (Work.BoseFixB1S.boxMuP volA ℓ A w1 Φ i
          + 2 * Work.BoseFixB1S.boxMuQP volA ℓ A w1 Φ i
          + Work.BoseFixB1S.boxMuQ volA ℓ A w1 Φ i) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hLHS]
  exact Finset.sum_congr rfl
    (fun i _ => boxMu_slot hvan i (hIntP i) (hIntQP i) (hIntQ i))

end Work.BoseFixB1M
