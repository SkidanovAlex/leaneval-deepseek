import Mathlib
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.assembly_helpers
import Submission.Work.FITop4.Red5.sum_Zint_annM_prim_le
import Submission.Work.FITop4.Red5.wsr_shellW_le

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. Elementary helpers -/

/-- The norm of one cell summand, bounded by the `μγ`-majorant with the `τ`-factor. -/
lemma wsr_norm_pc_Zc_le (Pa : Work.FITop.Params) (φ : ℝ) (q p : ℝ → ℝ) (w z : GaussianInt)
    (hq : 0 ≤ q (Complex.arg z.toComplex - φ)) (hp : 0 ≤ p (Work.FIPlan.gnorm z)) :
    ‖pieceCoeff Pa φ q p z * Work.FITop3.Zc w z‖
      ≤ q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
          * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
          * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
          * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by
  rw [norm_pieceCoeff_mul_Zc, abs_cfVal Pa φ q p z hq hp]
  have h1 : pcInd Pa φ z ≤ 1 := pcInd_one_le Pa φ z
  have h2 : |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|
      ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := Work.FITop3.abs_gammaTrunc_le Pa.C _
  have h2nn : 0 ≤ |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)| := abs_nonneg _
  have step : pcInd Pa φ z * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|
      ≤ 1 * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
    calc pcInd Pa φ z * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|
        ≤ 1 * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)| :=
          mul_le_mul_of_nonneg_right h1 h2nn
      _ ≤ 1 * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
  have h3nn : 0 ≤ q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
      * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)| := by positivity
  have h5nn : 0 ≤ (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := Zint_nonneg _
  calc pcInd Pa φ z
        * (q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|)
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)
      = (pcInd Pa φ z * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|)
          * (q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|)
          * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by ring
    _ ≤ (1 * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
          * (q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|)
          * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right step h3nn) h5nn
    _ = q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
          * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
          * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
          * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by ring

/-- Membership in `primAnn R`. -/
lemma wsr_mem_primAnn_iff {R : ℕ} {z : GaussianInt} :
    z ∈ primAnn R ↔ z ∈ Work.FIPlan.gBox ((R:ℕ):ℤ) ∧ 1 ≤ Work.FIPlan.gnorm z
      ∧ Work.FIPlan.gnorm z ≤ R ∧ Work.FIPlan.IsPrimary z := by
  simp only [primAnn, Finset.mem_filter]
  tauto

lemma wsr_gnorm_le {R : ℕ} {z : GaussianInt} (hz : z ∈ primAnn R) :
    Work.FIPlan.gnorm z ≤ R := (wsr_mem_primAnn_iff.mp hz).2.2.1

/-- Collapsing a `k`-partition of unity times a constant. -/
lemma wsr_collapse_k {K' : ℕ} (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ) (α C S : ℝ)
    (h : (∑ k, q k (α - φ k)) = 1) :
    (∑ k, C * q k (α - φ k) * S) = C * S := by
  rw [← Finset.sum_mul, ← Finset.mul_sum, h]
  ring

/-- Reorder a five-fold sum with the innermost (`z`-) index set independent of everything. -/
lemma wsr_sum_comm_z {K K' : ℕ} (F : Fin K → Finset ℕ) (u : Finset GaussianInt)
    (G : Fin K → Fin K' → ℕ → GaussianInt → GaussianInt → ℝ) :
    (∑ i, ∑ k, ∑ mm ∈ F i, ∑ w ∈ wSph mm, ∑ z ∈ u, G i k mm w z)
      = ∑ z ∈ u, ∑ i, ∑ k, ∑ mm ∈ F i, ∑ w ∈ wSph mm, G i k mm w z := by
  have hA : ∀ i k, (∑ mm ∈ F i, ∑ w ∈ wSph mm, ∑ z ∈ u, G i k mm w z)
      = ∑ z ∈ u, ∑ mm ∈ F i, ∑ w ∈ wSph mm, G i k mm w z := by
    intro i k
    have h1 : (∑ mm ∈ F i, ∑ w ∈ wSph mm, ∑ z ∈ u, G i k mm w z)
        = ∑ mm ∈ F i, ∑ z ∈ u, ∑ w ∈ wSph mm, G i k mm w z := by
      apply Finset.sum_congr rfl; intro mm _
      exact Finset.sum_comm
    rw [h1]
    exact Finset.sum_comm
  have hB : ∀ i, (∑ k, ∑ mm ∈ F i, ∑ w ∈ wSph mm, ∑ z ∈ u, G i k mm w z)
      = ∑ z ∈ u, ∑ k, ∑ mm ∈ F i, ∑ w ∈ wSph mm, G i k mm w z := by
    intro i
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ (Finset.univ : Finset (Fin K'))) => hA i k)]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin K))) => hB i)]
  exact Finset.sum_comm

lemma wsr_sum_p_nonneg {K : ℕ} (p : Fin K → ℝ → ℝ) (hp0 : ∀ i u, 0 ≤ p i u) (u : ℝ) :
    0 ≤ (∑ i, p i u) := Finset.sum_nonneg (fun i _ => hp0 i u)

lemma wsr_sum_p_eq_zero_of_le {K : ℕ} (N : ℕ) (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ)
    (ha : ∀ i, (N:ℝ) ≤ a i) (hpsup : ∀ i u, p i u ≠ 0 → a i < u) (u : ℝ)
    (hu : u ≤ (N:ℝ)) : (∑ i, p i u) = 0 := by
  apply Finset.sum_eq_zero; intro i _
  by_contra h
  have h1 := hpsup i u h
  have h2 := ha i
  linarith

lemma wsr_sum_p_le_one {K : ℕ} (N : ℕ) (θ : ℝ) (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ)
    (ha : ∀ i, (N:ℝ) ≤ a i)
    (hpsup : ∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1+θ)*a i)
    (hsum_le : ∀ u, (N:ℝ) < u → u ≤ 2*(N:ℝ) → (∑ i, p i u) ≤ 1)
    (u : ℝ) (hu : u ≤ 2*(N:ℝ)) : (∑ i, p i u) ≤ 1 := by
  by_cases h : (N:ℝ) < u
  · exact hsum_le u h hu
  · rw [wsr_sum_p_eq_zero_of_le N a p ha (fun i u h => (hpsup i u h).1) u (le_of_not_gt h)]
    norm_num

/-! ## 1. The per-`z` bound -/

lemma wsr_perz_zero (x N Mn : ℕ) (θ : ℝ) (K K' : ℕ)
    (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (ha : ∀ i, (N:ℝ) ≤ a i)
    (hpsup : ∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i)
    (z : GaussianInt) (hu : (Work.FIPlan.gnorm z : ℝ) ≤ (N:ℝ)) :
    (∑ i, ∑ k,
        ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter (fun m : ℕ => (m:ℝ) * a i < (x:ℝ)),
        ∑ w ∈ wSph mm,
          2 * (if (mm:ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x:ℝ) then (1:ℝ) else 0)
            * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
                * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
                * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))) = 0 := by
  apply Finset.sum_eq_zero; intro i _
  apply Finset.sum_eq_zero; intro k _
  apply Finset.sum_eq_zero; intro mm _
  apply Finset.sum_eq_zero; intro w _
  have hpiz : p i (Work.FIPlan.gnorm z : ℝ) = 0 := by
    by_contra h
    have h1 := (hpsup i (Work.FIPlan.gnorm z : ℝ) h).1
    have h2 := ha i
    linarith
  rw [hpiz]; ring

lemma wsr_perz_le (x N Mn : ℕ) (θ : ℝ) (K K' : ℕ)
    (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (hN1 : (1:ℝ) ≤ (N:ℝ)) (hθ : 0 < θ) (ha : ∀ i, (N:ℝ) ≤ a i)
    (hp0 : ∀ i u, 0 ≤ p i u)
    (hpsup : ∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i)
    (hsum_le : ∀ u, (N:ℝ) < u → u ≤ 2*(N:ℝ) → (∑ i, p i u) ≤ 1)
    (hq0 : ∀ k α, 0 ≤ q k α)
    (hang : ∀ α, -Real.pi ≤ α → α ≤ Real.pi → (∑ k, q k (α - φ k)) = 1)
    (z : GaussianInt) (hu2 : (Work.FIPlan.gnorm z : ℝ) ≤ 2*(N:ℝ)) :
    (∑ i, ∑ k,
        ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter (fun m : ℕ => (m:ℝ) * a i < (x:ℝ)),
        ∑ w ∈ wSph mm,
          2 * (if (mm:ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x:ℝ) then (1:ℝ) else 0)
            * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
                * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
                * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)))
      ≤ 2 * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
          * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
          * (∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
              (fun m : ℕ => (x:ℝ) < (m:ℝ) * (Work.FIPlan.gnorm z : ℝ)
                ∧ (m:ℝ) * (Work.FIPlan.gnorm z : ℝ) ≤ (x:ℝ) * (1 + θ)),
              ∑ w ∈ wSph mm, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) := by
  set u : ℝ := (Work.FIPlan.gnorm z : ℝ) with hu
  set Mu : ℝ := |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)| with hMu
  set Tau : ℝ := (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) with hTau
  set s3 : Finset ℕ := Finset.Icc (Mn + 1) (2 * Mn) with hs3
  let S : ℕ → ℝ := fun mm => ∑ w ∈ wSph mm, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)
  have hMu0 : 0 ≤ Mu := by rw [hMu]; exact abs_nonneg _
  have hTau0 : 0 ≤ Tau := by rw [hTau]; exact Nat.cast_nonneg _
  have hS0 : ∀ mm, 0 ≤ S mm := fun mm => Finset.sum_nonneg (fun w _ => Zint_nonneg _)
  have hcollapse : (∑ i, ∑ k, ∑ mm ∈ s3.filter (fun m : ℕ => (m:ℝ) * a i < (x:ℝ)), ∑ w ∈ wSph mm,
        (2 * (if (mm:ℝ) * u > (x:ℝ) then (1:ℝ) else 0)
          * (q k (Complex.arg z.toComplex - φ k) * p i u * Mu * Tau
              * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))))
      = ∑ i, ∑ mm ∈ s3.filter (fun m : ℕ => (m:ℝ) * a i < (x:ℝ)),
          (2 * (if (mm:ℝ) * u > (x:ℝ) then (1:ℝ) else 0) * p i u * Mu * Tau) * S mm := by
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro mm _
    have hk : ∀ k, (∑ w ∈ wSph mm,
          (2 * (if (mm:ℝ) * u > (x:ℝ) then (1:ℝ) else 0)
            * (q k (Complex.arg z.toComplex - φ k) * p i u * Mu * Tau
                * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))))
        = (2 * (if (mm:ℝ) * u > (x:ℝ) then (1:ℝ) else 0) * p i u * Mu * Tau)
            * q k (Complex.arg z.toComplex - φ k) * S mm := by
      intro k
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro w _
      ring
    rw [Finset.sum_congr rfl (fun k _ => hk k)]
    exact wsr_collapse_k φ q (Complex.arg z.toComplex)
      (2 * (if (mm:ℝ) * u > (x:ℝ) then (1:ℝ) else 0) * p i u * Mu * Tau) (S mm)
      (hang _ (le_of_lt (Complex.neg_pi_lt_arg _)) (Complex.arg_le_pi _))
  have hpt : ∀ i (mm : ℕ), (if (mm:ℝ) * a i < (x:ℝ) then (1:ℝ) else 0)
        * ((2 * (if (mm:ℝ) * u > (x:ℝ) then (1:ℝ) else 0) * p i u * Mu * Tau) * S mm)
      ≤ (if (x:ℝ) < (mm:ℝ) * u ∧ (mm:ℝ) * u ≤ (x:ℝ) * (1 + θ) then (1:ℝ) else 0)
        * ((2 * Mu * Tau * p i u) * S mm) := by
    intro i mm
    by_cases hp : p i u = 0
    · rw [hp]; ring_nf; norm_num
    · have hu' : u ≤ (1 + θ) * a i := (hpsup i u hp).2
      have hsw : (if (x:ℝ) < (mm:ℝ) * u then (1:ℝ) else 0)
            * (if (mm:ℝ) * a i < (x:ℝ) then (1:ℝ) else 0) * p i u
          ≤ (if (x:ℝ) < (mm:ℝ) * u ∧ (mm:ℝ) * u ≤ (x:ℝ) * (1 + θ) then (1:ℝ) else 0) * p i u :=
        wsr_shellW_le (hp0 i u) (Nat.cast_nonneg mm)
          (lt_of_lt_of_le (by linarith [hN1]) (ha i)) hθ hu'
      have hc0 : (0:ℝ) ≤ 2 * Mu * Tau * S mm :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hMu0) hTau0) (hS0 mm)
      calc (if (mm:ℝ) * a i < (x:ℝ) then (1:ℝ) else 0)
              * ((2 * (if (mm:ℝ) * u > (x:ℝ) then (1:ℝ) else 0) * p i u * Mu * Tau) * S mm)
          = ((if (x:ℝ) < (mm:ℝ) * u then (1:ℝ) else 0)
              * (if (mm:ℝ) * a i < (x:ℝ) then (1:ℝ) else 0) * p i u) * (2 * Mu * Tau * S mm) := by ring
        _ ≤ ((if (x:ℝ) < (mm:ℝ) * u ∧ (mm:ℝ) * u ≤ (x:ℝ) * (1 + θ) then (1:ℝ) else 0) * p i u)
              * (2 * Mu * Tau * S mm) := mul_le_mul_of_nonneg_right hsw hc0
        _ = (if (x:ℝ) < (mm:ℝ) * u ∧ (mm:ℝ) * u ≤ (x:ℝ) * (1 + θ) then (1:ℝ) else 0)
              * ((2 * Mu * Tau * p i u) * S mm) := by ring
  have hstep2 : (∑ i, ∑ mm ∈ s3.filter (fun m : ℕ => (m:ℝ) * a i < (x:ℝ)),
        (2 * (if (mm:ℝ) * u > (x:ℝ) then (1:ℝ) else 0) * p i u * Mu * Tau) * S mm)
      ≤ ∑ i, ∑ mm ∈ s3.filter (fun m : ℕ => (x:ℝ) < (m:ℝ)*u ∧ (m:ℝ)*u ≤ (x:ℝ)*(1+θ)),
          (2 * Mu * Tau * p i u) * S mm := by
    apply Finset.sum_le_sum; intro i _
    rw [Finset.sum_filter]
    calc (∑ mm ∈ s3, (if (mm:ℝ) * a i < (x:ℝ) then (2 * (if (mm:ℝ) * u > (x:ℝ) then (1:ℝ) else 0) * p i u * Mu * Tau) * S mm else 0))
        = ∑ mm ∈ s3, (if (mm:ℝ) * a i < (x:ℝ) then (1:ℝ) else 0) * ((2 * (if (mm:ℝ) * u > (x:ℝ) then (1:ℝ) else 0) * p i u * Mu * Tau) * S mm) := by
          apply Finset.sum_congr rfl; intro mm _
          by_cases h : (mm:ℝ) * a i < (x:ℝ) <;> simp [h]
      _ ≤ ∑ mm ∈ s3, (if (x:ℝ) < (mm:ℝ)*u ∧ (mm:ℝ)*u ≤ (x:ℝ)*(1+θ) then (1:ℝ) else 0) * ((2 * Mu * Tau * p i u) * S mm) :=
          Finset.sum_le_sum (fun mm _ => hpt i mm)
      _ = ∑ mm ∈ s3.filter (fun m : ℕ => (x:ℝ) < (m:ℝ)*u ∧ (m:ℝ)*u ≤ (x:ℝ)*(1+θ)), (2 * Mu * Tau * p i u) * S mm := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl; intro mm _
          by_cases h : (x:ℝ) < (mm:ℝ)*u ∧ (mm:ℝ)*u ≤ (x:ℝ)*(1+θ) <;> simp [h]
  have hstep3 : (∑ i, ∑ mm ∈ s3.filter (fun m : ℕ => (x:ℝ) < (m:ℝ)*u ∧ (m:ℝ)*u ≤ (x:ℝ)*(1+θ)),
        (2 * Mu * Tau * p i u) * S mm)
      ≤ 2 * Mu * Tau * (∑ mm ∈ s3.filter (fun m : ℕ => (x:ℝ) < (m:ℝ)*u ∧ (m:ℝ)*u ≤ (x:ℝ)*(1+θ)), S mm) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum (fun mm _ => ?_)
    have hp1 : (∑ i, p i u) ≤ 1 := wsr_sum_p_le_one N θ a p ha hpsup hsum_le u hu2
    have hc0 : (0:ℝ) ≤ 2 * Mu * Tau * S mm :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hMu0) hTau0) (hS0 mm)
    calc (∑ i, (2 * Mu * Tau * p i u) * S mm)
        = (2 * Mu * Tau * S mm) * (∑ i, p i u) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
      _ ≤ (2 * Mu * Tau * S mm) * 1 := mul_le_mul_of_nonneg_left hp1 hc0
      _ = 2 * Mu * Tau * S mm := by ring
  rw [hcollapse]
  exact le_trans hstep2 hstep3

/-! ## 2. The full left-hand side, reduced to the per-`z` sums -/

lemma wsr_lhs_le_zsum (x N Mn : ℕ) (θ : ℝ) (K K' : ℕ)
    (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (Pa : Fin K → Fin K' → Work.FITop.Params)
    (hp0 : ∀ i u, 0 ≤ p i u) (hq0 : ∀ k α, 0 ≤ q k α) :
    (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter (fun m : ℕ => (m:ℝ) * a i < (x:ℝ)),
        ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
          2 * (if (mm:ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x:ℝ) then (1:ℝ) else 0)
            * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
      ≤ ∑ z ∈ primAnn (2 * N), ∑ i, ∑ k,
          ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter (fun m : ℕ => (m:ℝ) * a i < (x:ℝ)),
          ∑ w ∈ wSph mm,
            2 * (if (mm:ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x:ℝ) then (1:ℝ) else 0)
              * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
                  * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
                  * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
                  * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) := by
  have h1 : (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter (fun m : ℕ => (m:ℝ) * a i < (x:ℝ)),
        ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
          2 * (if (mm:ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x:ℝ) then (1:ℝ) else 0)
            * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
      ≤ ∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter (fun m : ℕ => (m:ℝ) * a i < (x:ℝ)),
        ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
          2 * (if (mm:ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x:ℝ) then (1:ℝ) else 0)
            * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
                * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
                * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro k _
    apply Finset.sum_le_sum; intro mm _
    apply Finset.sum_le_sum; intro w _
    apply Finset.sum_le_sum; intro z _
    have hnb := wsr_norm_pc_Zc_le (Pa i k) (φ k) (q k) (p i) w z (hq0 k _) (hp0 i _)
    have hsh : (0:ℝ) ≤ 2 * (if (mm:ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x:ℝ) then (1:ℝ) else 0) := by
      split_ifs <;> norm_num
    exact mul_le_mul_of_nonneg_left hnb hsh
  refine le_trans h1 ?_
  exact le_of_eq (wsr_sum_comm_z
    (fun i => (Finset.Icc (Mn + 1) (2 * Mn)).filter (fun m : ℕ => (m:ℝ) * a i < (x:ℝ)))
    (primAnn (2 * N))
    (fun i k mm w z => 2 * (if (mm:ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x:ℝ) then (1:ℝ) else 0)
      * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
          * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
          * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
          * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))))

/-! ## 3. The per-`z` sums, bounded by the shell count -/

lemma wsr_zsum_le (x N Mn : ℕ) (θ : ℝ) (K K' : ℕ)
    (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (hN1 : (1:ℝ) ≤ (N:ℝ)) (hθ : 0 < θ) (ha : ∀ i, (N:ℝ) ≤ a i)
    (hp0 : ∀ i u, 0 ≤ p i u)
    (hpsup : ∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i)
    (hsum_le : ∀ u, (N:ℝ) < u → u ≤ 2*(N:ℝ) → (∑ i, p i u) ≤ 1)
    (hq0 : ∀ k α, 0 ≤ q k α)
    (hang : ∀ α, -Real.pi ≤ α → α ≤ Real.pi → (∑ k, q k (α - φ k)) = 1) :
    (∑ z ∈ primAnn (2 * N), ∑ i, ∑ k,
        ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter (fun m : ℕ => (m:ℝ) * a i < (x:ℝ)),
        ∑ w ∈ wSph mm,
          2 * (if (mm:ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x:ℝ) then (1:ℝ) else 0)
            * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
                * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
                * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)))
      ≤ 2 * (∑ z ∈ (primAnn (2 * N)).filter (fun z => (N:ℝ) < (Work.FIPlan.gnorm z : ℝ)),
          |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
            * (∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
                (fun m : ℕ => (x:ℝ) < (m:ℝ) * (Work.FIPlan.gnorm z : ℝ)
                  ∧ (m:ℝ) * (Work.FIPlan.gnorm z : ℝ) ≤ (x:ℝ) * (1 + θ)),
                ∑ w ∈ wSph mm, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))) := by
  have hper : ∀ z ∈ primAnn (2 * N),
      (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter (fun m : ℕ => (m:ℝ) * a i < (x:ℝ)),
        ∑ w ∈ wSph mm,
          2 * (if (mm:ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x:ℝ) then (1:ℝ) else 0)
            * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
                * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
                * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)))
      ≤ (if (N:ℝ) < (Work.FIPlan.gnorm z : ℝ) then
          2 * (|(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
              * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
              * (∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
                  (fun m : ℕ => (x:ℝ) < (m:ℝ) * (Work.FIPlan.gnorm z : ℝ)
                    ∧ (m:ℝ) * (Work.FIPlan.gnorm z : ℝ) ≤ (x:ℝ) * (1 + θ)),
                  ∑ w ∈ wSph mm, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)))
        else 0) := by
    intro z hz
    by_cases hzu : (N:ℝ) < (Work.FIPlan.gnorm z : ℝ)
    · rw [if_pos hzu]
      have hperz := wsr_perz_le x N Mn θ K K' a p φ q hN1 hθ ha hp0 hpsup hsum_le hq0 hang z
        (by exact_mod_cast wsr_gnorm_le hz)
      refine le_trans hperz ?_
      apply le_of_eq; ring
    · rw [if_neg hzu]
      exact le_of_eq (wsr_perz_zero x N Mn θ K K' a p φ q ha hpsup z (le_of_not_gt hzu))
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [← Finset.sum_filter, Finset.mul_sum]


theorem window_T2_shell_reduce :
    ∀ (x N Mn : ℕ) (τ θ : ℝ) (K K' : ℕ)
      (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
      (Pa : Fin K → Fin K' → Work.FITop.Params),
      (1 ≤ N) → (0 < θ) → (∀ i, (N : ℝ) ≤ a i) →
      (∀ i u, 0 ≤ p i u) →
      (∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i) →
      (∀ u, (N : ℝ) < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) ≤ 1) →
      (∀ k α, 0 ≤ q k α) →
      (∀ α, -Real.pi ≤ α → α ≤ Real.pi → (∑ k, q k (α - φ k)) = 1) →
      (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
          ∑ w ∈ Work.FITop4.Red5.wSph mm, ∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
            2 * (if (mm : ℝ) * (Work.FIPlan.gnorm z : ℝ) > (x : ℝ) then (1 : ℝ) else 0)
              * ‖Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
        ≤ 2 * (∑ z ∈ (Work.FITop4.Red5.primAnn (2 * N)).filter
            (fun z => (N : ℝ) < (Work.FIPlan.gnorm z : ℝ)),
          |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
            * (∑ m ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter
                (fun m : ℕ => (x : ℝ) < (m : ℝ) * (Work.FIPlan.gnorm z : ℝ)
                  ∧ (m : ℝ) * (Work.FIPlan.gnorm z : ℝ) ≤ (x : ℝ) * (1 + θ)),
                ∑ w ∈ Work.FITop4.Red5.wSph m,
                  (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))) := by
  intro x N Mn τ θ K K' a p φ q Pa hN hθ ha hp0 hpsup hsum_le hq0 hang
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  exact le_trans (wsr_lhs_le_zsum x N Mn θ K K' a p φ q Pa hp0 hq0)
    (wsr_zsum_le x N Mn θ K K' a p φ q hN1 hθ ha hp0 hpsup hsum_le hq0 hang)

end

end Work.FITop4.Red5
