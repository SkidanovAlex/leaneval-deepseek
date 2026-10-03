import Mathlib
import Submission.Work.A7.Pev.PevalR_deriv_bounds
import Submission.Work.KMTAreas.A7.KmtKernelL1Uniform
import Submission.Work.KMTAreas.A7.abelPeriodicSum
import Submission.Work.KMTAreas.A7.fourierPeriodSumZero
import Submission.Work.KMTAreas.A7.weylAvgFibreExpansion
import Submission.Work.KMTAreas.A7.diffMassSharp

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-! ## The objects -/

/-- The Fourier transform of the bump `φ_N` at the continuous height `k₁`. -/
private noncomputable def bA (N k : ℕ) : ℝ → ℂ := bumpFT (varphiN N k)

/-- The Fourier transform of the bump `φ̃_N` at the continuous height `k₂`. -/
private noncomputable def bB (P : Polynomial ℤ) (N k : ℕ) : ℝ → ℂ :=
  bumpFT (varphitildeN P.natDegree N k)

/-- The arithmetic character `n ↦ e(n α₁)`. -/
private noncomputable def bC (α : Work.Analysis.IonescuWainger.Circle) : ℤ → ℂ :=
  fun m => fourier (T := 1) m α

/-- The fibre function `t ↦ φ̂_N(t - p₁) φ̃̂_N(P(t) - p₂)`. -/
private noncomputable def bFibreR (P : Polynomial ℤ) (N k₁ k₂ : ℕ) (p : ℤ × ℤ) (t : ℝ) : ℂ :=
  bA N k₁ (t - (p.1 : ℝ)) * bB P N k₂ (PevalR P t - (p.2 : ℝ))

/-- The `p`-th Fourier coefficient of the twisted fibre mass. -/
private noncomputable def bMass (P : Polynomial ℤ) (N k₁ k₂ : ℕ)
    (α₁ : Work.Analysis.IonescuWainger.Circle) (p : ℤ × ℤ) : ℂ :=
  ∫ θ₁ : ℝ, ∫ θ₂ : ℝ, varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
    * weylAvg P N α₁ 0 θ₁ θ₂ * ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))


/-! ## Summability of the lattice masses -/

private lemma summ_cw {m : ℝ → ℂ} (hcd : ContDiff ℝ 2 m) (hcs : HasCompactSupport m) :
    Summable (fun j : ℤ => ‖cw m j‖) := by
  have h := FourierDecayExplicit hcd hcs
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left
      (4 * max (∫ y, ‖m y‖) (∫ y, ‖iteratedDeriv 2 m y‖) + 1))
  rw [cw_eq_fourierTransform, norm_kmtKernWeight, mul_one_div]
  exact h (j : ℝ)

private lemma summ_bT {m : ℝ → ℂ} (hcd : ContDiff ℝ 2 m) (hcs : HasCompactSupport m) :
    Summable (fun j : ℤ => ‖bumpFT m (-(j : ℝ))‖) := by
  have h := summ_cw hcd hcs
  convert h using 1 with j
  simp only [cw, bumpFT, neg_mul]

private lemma summ_bT_shift {m : ℝ → ℂ} (hcd : ContDiff ℝ 2 m) (hcs : HasCompactSupport m)
    (z : ℤ) : Summable (fun p : ℤ => ‖bumpFT m ((z : ℝ) - (p : ℝ))‖) := by
  have h0 := summ_bT hcd hcs
  have h2 : (fun p : ℤ => ‖bumpFT m ((z : ℝ) - (p : ℝ))‖)
      = fun p : ℤ => ‖bumpFT m (-(((p - z : ℤ)) : ℝ))‖ := by
    funext p
    have harg : (z : ℝ) - (p : ℝ) = -(((p - z : ℤ)) : ℝ) := by push_cast; ring
    rw [harg]
  rw [h2]
  exact (Equiv.subRight z).summable_iff.mpr h0

private lemma summ_bA (N k : ℕ) (z : ℤ) :
    Summable (fun p : ℤ => ‖bA N k ((z : ℝ) - (p : ℝ))‖) :=
  summ_bT_shift (contDiff_varphiN N k) (hasCompactSupport_varphiN N k) z

private lemma summ_bB (P : Polynomial ℤ) (N k : ℕ) (z : ℤ) :
    Summable (fun p : ℤ => ‖bB P N k ((z : ℝ) - (p : ℝ))‖) :=
  summ_bT_shift (contDiff_varphitildeN P.natDegree N k)
    (hasCompactSupport_varphitildeN P.natDegree N k) z

private lemma summ_bA_diff (N k : ℕ) (z : ℤ) :
    Summable (fun p : ℤ => ‖bA N k ((z : ℝ) + 1 - (p : ℝ)) - bA N k ((z : ℝ) - (p : ℝ))‖) := by
  have hsum : Summable (fun p : ℤ => ‖bA N k ((((z + 1 : ℤ)) : ℝ) - (p : ℝ))‖
      + ‖bA N k ((z : ℝ) - (p : ℝ))‖) := (summ_bA N k (z + 1)).add (summ_bA N k z)
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hsum
  have harg : (z : ℝ) + 1 - (p : ℝ) = (((z + 1 : ℤ)) : ℝ) - (p : ℝ) := by push_cast; ring
  rw [harg]
  exact norm_sub_le _ _

private lemma summ_bB_diff (P : Polynomial ℤ) (N k : ℕ) (z a : ℤ) :
    Summable (fun p : ℤ => ‖bB P N k ((z : ℝ) + (a : ℝ) - (p : ℝ))
      - bB P N k ((z : ℝ) - (p : ℝ))‖) := by
  have hsum : Summable (fun p : ℤ => ‖bB P N k ((((z + a : ℤ)) : ℝ) - (p : ℝ))‖
      + ‖bB P N k ((z : ℝ) - (p : ℝ))‖) := (summ_bB P N k (z + a)).add (summ_bB P N k z)
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hsum
  have harg : (z : ℝ) + (a : ℝ) - (p : ℝ) = (((z + a : ℤ)) : ℝ) - (p : ℝ) := by push_cast; ring
  rw [harg]
  exact norm_sub_le _ _

/-! ## The fibre expansion and the Abel bound for one fibre -/

private lemma bMass_eq (P : Polynomial ℤ) (N k₁ k₂ : ℕ) (α₁ : Work.Analysis.IonescuWainger.Circle) (p : ℤ × ℤ) :
    bMass P N k₁ k₂ α₁ p
      = (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          bC α₁ (n : ℤ) * bFibreR P N k₁ k₂ p (n : ℝ) := by
  rw [bMass, weylAvgFibreExpansion P N k₁ k₂ α₁ p]
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [bC, bFibreR, bA, bB, mul_assoc]

private lemma bMass_abel (P : Polynomial ℤ) (N q k₁ k₂ : ℕ) (α₁ : Work.Analysis.IonescuWainger.Circle)
    (hN : 1 ≤ N) (hq : 0 < q) (hqα : q • α₁ = 0) (hαne : α₁ ≠ 0) (p : ℤ × ℤ) :
    ‖bMass P N k₁ k₂ α₁ p‖ ≤ (N : ℝ)⁻¹ * (q : ℝ) *
      (‖bFibreR P N k₁ k₂ p (N : ℝ)‖
        + ∑ n ∈ Finset.Ico (N / 2 + 1) N,
            ‖bFibreR P N k₁ k₂ p ((n : ℝ) + 1) - bFibreR P N k₁ k₂ p (n : ℝ)‖) := by
  rw [bMass_eq]
  have hnorm : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  rw [norm_mul, hnorm]
  have h2 : ‖∑ n ∈ Finset.Ioc (N / 2) N, bC α₁ (n : ℤ) * bFibreR P N k₁ k₂ p (n : ℝ)‖
      ≤ (q : ℝ) * (‖bFibreR P N k₁ k₂ p (N : ℝ)‖
        + ∑ n ∈ Finset.Ico (N / 2 + 1) N,
            ‖bFibreR P N k₁ k₂ p ((n : ℝ) + 1) - bFibreR P N k₁ k₂ p (n : ℝ)‖) := by
    have hzero : ∀ n : ℤ, ∑ r ∈ Finset.range q, bC α₁ (n + (r : ℤ)) = 0 := by
      intro n
      have h := fourierPeriodSumZero q hq α₁ hqα hαne n
      simpa only [bC] using h
    have hc : ∀ n : ℤ, ‖bC α₁ n‖ ≤ 1 := by
      intro n
      have h1 : ‖fourier (T := 1) n α₁‖ = 1 := by
        rw [fourier_apply, Circle.norm_coe]
      simpa only [bC] using le_of_eq h1
    have h := abelPeriodicSum q hq (bC α₁) (fun n : ℕ => bFibreR P N k₁ k₂ p (n : ℝ)) hzero hc
      (Nat.div_le_self N 2)
    simpa only [Nat.cast_add, Nat.cast_one] using h
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.Ioc (N / 2) N, bC α₁ (n : ℤ) * bFibreR P N k₁ k₂ p (n : ℝ)‖
      ≤ (N : ℝ)⁻¹ * ((q : ℝ) * (‖bFibreR P N k₁ k₂ p (N : ℝ)‖
        + ∑ n ∈ Finset.Ico (N / 2 + 1) N,
            ‖bFibreR P N k₁ k₂ p ((n : ℝ) + 1) - bFibreR P N k₁ k₂ p (n : ℝ)‖)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (N : ℝ)⁻¹ * (q : ℝ) * (‖bFibreR P N k₁ k₂ p (N : ℝ)‖
        + ∑ n ∈ Finset.Ico (N / 2 + 1) N,
            ‖bFibreR P N k₁ k₂ p ((n : ℝ) + 1) - bFibreR P N k₁ k₂ p (n : ℝ)‖) := by ring

/-! ## Elementary `ℝ≥0∞` tools -/

private lemma ennreal_tsum_prod_mul (f g : ℤ → ℝ≥0∞) :
    (∑' p : ℤ × ℤ, f p.1 * g p.2) = (∑' a : ℤ, f a) * (∑' b : ℤ, g b) := by
  rw [ENNReal.tsum_prod']
  simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

private lemma ennreal_tsum_prod_ofReal (X Y : ℤ → ℝ) (hX : ∀ a, 0 ≤ X a) (hY : ∀ b, 0 ≤ Y b) :
    (∑' p : ℤ × ℤ, ENNReal.ofReal (X p.1 * Y p.2))
      = (∑' a : ℤ, ENNReal.ofReal (X a)) * (∑' b : ℤ, ENNReal.ofReal (Y b)) := by
  have h1 : ∀ p : ℤ × ℤ, ENNReal.ofReal (X p.1 * Y p.2)
      = ENNReal.ofReal (X p.1) * ENNReal.ofReal (Y p.2) :=
    fun p => ENNReal.ofReal_mul (hX p.1)
  simp only [h1]
  exact ennreal_tsum_prod_mul (fun a : ℤ => ENNReal.ofReal (X a)) (fun b : ℤ => ENNReal.ofReal (Y b))

private lemma ennreal_tsum_finset_sum_le {ι α : Type*} (s : Finset ι) (g : ι → α → ℝ≥0∞) :
    (∑' a, ∑ i ∈ s, g i a) ≤ ∑ i ∈ s, ∑' a, g i a := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le (fun F => ?_)
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun i _ => ENNReal.sum_le_tsum F)

private lemma ennreal_sum_const_le (s : Finset ℕ) (n : ℕ) (hcard : s.card ≤ n) (c : ℝ≥0∞) :
    ∑ _i ∈ s, c ≤ (n : ℝ≥0∞) * c := by
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul' (by exact_mod_cast hcard) le_rfl


private lemma ennreal_const_mul_ofReal {n : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (n : ℝ≥0∞) * (ENNReal.ofReal a * ENNReal.ofReal b) = ENNReal.ofReal (n * (a * b)) := by
  rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul ha,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]

private lemma ennreal_sum_const_mul_le (s : Finset ℕ) (n : ℕ) (hcard : s.card ≤ n)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∑ _i ∈ s, (ENNReal.ofReal a * ENNReal.ofReal b) ≤ ENNReal.ofReal (n * (a * b)) :=
  (ennreal_sum_const_le s n hcard _).trans (le_of_eq (ennreal_const_mul_ofReal ha hb))

private lemma pevalR_intCast (P : Polynomial ℤ) (m : ℤ) :
    PevalR P ((m : ℝ)) = ((P.eval m : ℤ) : ℝ) := by
  simp [PevalR]

/-! ## The arithmetic of the constants -/

private lemma arith_bound (d : ℕ) {N q k₁ k₂ : ℕ} {Km Cm Kp C₀ r₁ r₂ s : ℝ}
    (hN : 1 ≤ N) (hq : 1 ≤ q) (hKm : 0 ≤ Km) (hKp : 0 ≤ Kp) (hCm : 0 ≤ Cm)
    (hr₁0 : 0 ≤ r₁) (hr₂0 : 0 ≤ r₂) (hs : 0 ≤ s)
    (hC₀ : C₀ = 4 * Km ^ 2 + 2 * Cm * Km + 2 * Km * Kp * Cm)
    (hr₁ : ((N : ℝ)) * r₁ = (2 : ℝ) ^ k₁)
    (hr₂ : ((N : ℝ) ^ d) * r₂ = (2 : ℝ) ^ (d * k₂)) :
    (N : ℝ)⁻¹ * (q : ℝ) *
        (Km ^ 2 * (1 + r₁) * (1 + r₂) + ((N : ℝ)) * Cm * r₁ * Km * (1 + r₂)
          + Km * (1 + r₁) * ((N : ℝ) ^ d) * (Kp * (Cm * r₂)))
      ≤ (max 1 C₀) * (q : ℝ) ^ 2 * (1 + s) * (2 : ℝ) ^ (k₁ + d * k₂) / (N : ℝ) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h2k₁ : (1 : ℝ) ≤ (2 : ℝ) ^ k₁ := one_le_pow₀ (by norm_num)
  have h2k₂ : (1 : ℝ) ≤ (2 : ℝ) ^ (d * k₂) := one_le_pow₀ (by norm_num)
  have hp : (2 : ℝ) ^ k₁ * (2 : ℝ) ^ (d * k₂) = (2 : ℝ) ^ (k₁ + d * k₂) := by
    rw [← pow_add]
  have hNd1 : (1 : ℝ) ≤ (N : ℝ) ^ d := one_le_pow₀ hN1
  have hr₁le : r₁ ≤ (2 : ℝ) ^ k₁ := by
    have h : r₁ = (2 : ℝ) ^ k₁ / (N : ℝ) := by
      rw [eq_div_iff (by positivity : ((N : ℝ)) ≠ 0)]
      linarith [hr₁]
    rw [h, div_le_iff₀ (by linarith : (0 : ℝ) < (N : ℝ))]
    nlinarith [h2k₁, hN1]
  have hr₂le : r₂ ≤ (2 : ℝ) ^ (d * k₂) := by
    have h : r₂ = (2 : ℝ) ^ (d * k₂) / ((N : ℝ) ^ d) := by
      rw [eq_div_iff (by positivity : ((N : ℝ) ^ d) ≠ 0)]
      linarith [hr₂]
    rw [h, div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) ^ d)]
    nlinarith [h2k₂, hNd1]
  have h1r₁ : 1 + r₁ ≤ 2 * (2 : ℝ) ^ k₁ := by linarith
  have h1r₂ : 1 + r₂ ≤ 2 * (2 : ℝ) ^ (d * k₂) := by linarith
  have hBr : Km ^ 2 * (1 + r₁) * (1 + r₂) + ((N : ℝ)) * Cm * r₁ * Km * (1 + r₂)
        + Km * (1 + r₁) * ((N : ℝ) ^ d) * (Kp * (Cm * r₂))
      ≤ C₀ * (2 : ℝ) ^ (k₁ + d * k₂) := by
    have hA : Km ^ 2 * (1 + r₁) * (1 + r₂) ≤ 4 * Km ^ 2 * (2 : ℝ) ^ (k₁ + d * k₂) := by
      have h11 : (1 + r₁) * (1 + r₂) ≤ (2 * (2 : ℝ) ^ k₁) * (2 * (2 : ℝ) ^ (d * k₂)) :=
        mul_le_mul h1r₁ h1r₂ (by positivity) (by positivity)
      calc Km ^ 2 * (1 + r₁) * (1 + r₂) = Km ^ 2 * ((1 + r₁) * (1 + r₂)) := by ring
        _ ≤ Km ^ 2 * ((2 * (2 : ℝ) ^ k₁) * (2 * (2 : ℝ) ^ (d * k₂))) :=
            mul_le_mul_of_nonneg_left h11 (sq_nonneg Km)
        _ = 4 * Km ^ 2 * (2 : ℝ) ^ (k₁ + d * k₂) := by rw [← hp]; ring
    have hB : ((N : ℝ)) * Cm * r₁ * Km * (1 + r₂) ≤ 2 * Cm * Km * (2 : ℝ) ^ (k₁ + d * k₂) := by
      calc ((N : ℝ)) * Cm * r₁ * Km * (1 + r₂)
          = Cm * Km * ((1 + r₂) * (((N : ℝ)) * r₁)) := by ring
        _ = Cm * Km * ((1 + r₂) * (2 : ℝ) ^ k₁) := by rw [hr₁]
        _ ≤ Cm * Km * ((2 * (2 : ℝ) ^ (d * k₂)) * (2 : ℝ) ^ k₁) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right h1r₂ (by positivity)) (mul_nonneg hCm hKm)
        _ = 2 * Cm * Km * (2 : ℝ) ^ (k₁ + d * k₂) := by rw [← hp]; ring
    have hC : Km * (1 + r₁) * ((N : ℝ) ^ d) * (Kp * (Cm * r₂))
        ≤ 2 * Km * Kp * Cm * (2 : ℝ) ^ (k₁ + d * k₂) := by
      calc Km * (1 + r₁) * ((N : ℝ) ^ d) * (Kp * (Cm * r₂))
          = Km * Kp * Cm * ((1 + r₁) * (((N : ℝ) ^ d) * r₂)) := by ring
        _ = Km * Kp * Cm * ((1 + r₁) * (2 : ℝ) ^ (d * k₂)) := by rw [hr₂]
        _ ≤ Km * Kp * Cm * ((2 * (2 : ℝ) ^ k₁) * (2 : ℝ) ^ (d * k₂)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right h1r₁ (by positivity))
              (mul_nonneg (mul_nonneg hKm hKp) hCm)
        _ = 2 * Km * Kp * Cm * (2 : ℝ) ^ (k₁ + d * k₂) := by rw [← hp]; ring
    calc Km ^ 2 * (1 + r₁) * (1 + r₂) + ((N : ℝ)) * Cm * r₁ * Km * (1 + r₂)
          + Km * (1 + r₁) * ((N : ℝ) ^ d) * (Kp * (Cm * r₂))
        ≤ 4 * Km ^ 2 * (2 : ℝ) ^ (k₁ + d * k₂) + 2 * Cm * Km * (2 : ℝ) ^ (k₁ + d * k₂)
          + 2 * Km * Kp * Cm * (2 : ℝ) ^ (k₁ + d * k₂) := add_le_add (add_le_add hA hB) hC
      _ = C₀ * (2 : ℝ) ^ (k₁ + d * k₂) := by rw [hC₀]; ring
  have hkey : C₀ ≤ (max 1 C₀) * (q : ℝ) * (1 + s) := by
    have hM0 : (0 : ℝ) ≤ max 1 C₀ := le_trans zero_le_one (le_max_left _ _)
    have hCs : C₀ ≤ max 1 C₀ := le_max_right _ _
    have h1s : (1 : ℝ) ≤ 1 + s := by linarith
    calc C₀ ≤ (max 1 C₀) * 1 * 1 := by rw [mul_one, mul_one]; exact hCs
      _ ≤ (max 1 C₀) * (q : ℝ) * (1 + s) :=
          mul_le_mul (mul_le_mul le_rfl hq1 (by norm_num) hM0) h1s (by norm_num) (by positivity)
  calc (N : ℝ)⁻¹ * (q : ℝ) *
        (Km ^ 2 * (1 + r₁) * (1 + r₂) + ((N : ℝ)) * Cm * r₁ * Km * (1 + r₂)
          + Km * (1 + r₁) * ((N : ℝ) ^ d) * (Kp * (Cm * r₂)))
      ≤ (N : ℝ)⁻¹ * (q : ℝ) * (C₀ * (2 : ℝ) ^ (k₁ + d * k₂)) :=
        mul_le_mul_of_nonneg_left hBr (by positivity)
    _ = C₀ * ((q : ℝ) * (2 : ℝ) ^ (k₁ + d * k₂) / (N : ℝ)) := by ring
    _ ≤ ((max 1 C₀) * (q : ℝ) * (1 + s)) * ((q : ℝ) * (2 : ℝ) ^ (k₁ + d * k₂) / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = (max 1 C₀) * (q : ℝ) ^ 2 * (1 + s) * (2 : ℝ) ^ (k₁ + d * k₂) / (N : ℝ) := by ring

/-- The translate of `f` by the integer `y`, evaluated at the integer shift `j`. -/
private noncomputable def trF (f : ℝ → ℂ) (y : ℤ) (p : ℤ) (j : ℕ) : ℂ :=
  f (((((y + ((j : ℕ) : ℤ)) : ℤ)) : ℝ) - (p : ℝ))

private lemma tsum_trF_diff_le (f : ℝ → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (h1 : ∀ u : ℤ, (∑' p : ℤ, ENNReal.ofReal ‖trF f u p 1 - trF f u p 0‖) ≤ ENNReal.ofReal D)
    (y : ℤ) (m : ℕ) :
    (∑' p : ℤ, ENNReal.ofReal ‖trF f y p m - trF f y p 0‖) ≤ ENNReal.ofReal ((m : ℝ) * D) := by
  calc (∑' p : ℤ, ENNReal.ofReal ‖trF f y p m - trF f y p 0‖)
      ≤ ∑' p : ℤ, ∑ j ∈ Finset.range m, ENNReal.ofReal ‖trF f y p (j + 1) - trF f y p j‖ := by
        refine ENNReal.tsum_le_tsum (fun p => ?_)
        rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => norm_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have htel : (∑ j ∈ Finset.range m, (trF f y p (j + 1) - trF f y p j))
            = trF f y p m - trF f y p 0 :=
          Finset.sum_range_sub (fun j : ℕ => trF f y p j) m
        rw [← htel]
        exact norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range m, ∑' p : ℤ, ENNReal.ofReal ‖trF f y p (j + 1) - trF f y p j‖ :=
        ennreal_tsum_finset_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range m, ENNReal.ofReal D := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have h := h1 (y + (j : ℤ))
        have hconv : (∑' p : ℤ, ENNReal.ofReal ‖trF f y p (j + 1) - trF f y p j‖)
            = (∑' p : ℤ, ENNReal.ofReal ‖trF f (y + (j : ℤ)) p 1 - trF f (y + (j : ℤ)) p 0‖) := by
          refine tsum_congr (fun p => ?_)
          have h2 : trF f y p (j + 1) = trF f (y + (j : ℤ)) p 1 := by
            simp only [trF, Nat.cast_add, Nat.cast_one]
            congr 1
            push_cast
            ring
          have h3 : trF f y p j = trF f (y + (j : ℤ)) p 0 := by
            simp only [trF, Nat.cast_zero, add_zero]
          rw [h2, h3]
        rw [hconv]
        exact h
    _ = ENNReal.ofReal ((m : ℝ) * D) := by
        have h1' : (∑ j ∈ Finset.range m, ENNReal.ofReal D) = (m : ℝ≥0∞) * ENNReal.ofReal D := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [h1', ← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]

private lemma tsum_shift_le_int (f : ℝ → ℂ) (D : ℝ) (hD : 0 ≤ D)
    (h1 : ∀ u : ℤ, (∑' p : ℤ, ENNReal.ofReal ‖trF f u p 1 - trF f u p 0‖) ≤ ENNReal.ofReal D)
    (y a : ℤ) :
    (∑' p : ℤ, ENNReal.ofReal ‖trF f (y + a) p 0 - trF f y p 0‖)
      ≤ ENNReal.ofReal (|(a : ℝ)| * D) := by
  rcases le_or_gt 0 a with ha | ha
  · have hm : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha
    have hmR : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by rw [← Int.cast_natCast, hm]
    have hgoal : (∑' p : ℤ, ENNReal.ofReal ‖trF f (y + a) p 0 - trF f y p 0‖)
        = (∑' p : ℤ, ENNReal.ofReal ‖trF f y p a.toNat - trF f y p 0‖) := by
      refine tsum_congr (fun p => ?_)
      have h2 : trF f (y + a) p 0 = trF f y p a.toNat := by
        simp only [trF, Nat.cast_zero, add_zero]
        rw [hm]
      rw [h2, norm_sub_rev]
    rw [hgoal]
    refine (tsum_trF_diff_le f D hD h1 y a.toNat).trans (le_of_eq ?_)
    rw [hmR, abs_of_nonneg (by exact_mod_cast ha)]
  · have hpos : 0 < -a := neg_pos.mpr ha
    have hm : ((((-a).toNat : ℕ)) : ℤ) = -a := Int.toNat_of_nonneg hpos.le
    have hmR : (((-a).toNat : ℕ) : ℝ) = |(a : ℝ)| := by
      rw [← Int.cast_natCast, hm, Int.cast_neg, abs_of_neg (by exact_mod_cast ha)]
    have hgoal : (∑' p : ℤ, ENNReal.ofReal ‖trF f (y + a) p 0 - trF f y p 0‖)
        = (∑' p : ℤ, ENNReal.ofReal
            ‖trF f (y + a) p ((-a).toNat) - trF f (y + a) p 0‖) := by
      refine tsum_congr (fun p => ?_)
      have h2 : trF f y p 0 = trF f (y + a) p ((-a).toNat) := by
        simp only [trF, Nat.cast_zero, add_zero]
        rw [hm]
        ring_nf
      rw [h2, norm_sub_rev]
    rw [hgoal]
    refine (tsum_trF_diff_le f D hD h1 (y + a) ((-a).toNat)).trans (le_of_eq ?_)
    rw [hmR]

/-- The evaluation of `P` at a successor index, as an integer. -/
private lemma pevalR_succ (P : Polynomial ℤ) (n : ℕ) :
    PevalR P ((n : ℝ) + 1) = ((P.eval ((n : ℤ) + 1) : ℤ) : ℝ) := by
  have hcast : (n : ℝ) + 1 = ((((n + 1 : ℕ)) : ℤ) : ℝ) := by push_cast; ring
  rw [hcast, pevalR_intCast]
  push_cast
  ring

/-- The difference of consecutive evaluations of `P`, as an integer. -/
private lemma shift_int (P : Polynomial ℤ) (n : ℕ) :
    PevalR P ((n : ℝ) + 1) - PevalR P (n : ℝ)
      = (((P.eval ((n : ℤ) + 1) - P.eval (n : ℤ) : ℤ)) : ℝ) := by
  rw [pevalR_succ P n]
  have h2 : PevalR P ((n : ℝ)) = ((P.eval ((n : ℤ)) : ℤ) : ℝ) := by
    have hcast : (n : ℝ) = (((n : ℤ)) : ℝ) := by push_cast; ring
    rw [hcast, pevalR_intCast]
  rw [h2]
  push_cast
  ring

theorem LoFibreMass (P : Polynomial ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N q k₁ k₂ : ℕ) (α₁ : Work.Analysis.IonescuWainger.Circle),
      1 ≤ N → 0 < q → q • α₁ = 0 → α₁ ≠ 0 →
      Summable (fun p : ℤ × ℤ => ‖∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
          Work.KMTAreas.A7.varphiN N k₁ θ₁ * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ θ₂
            * Work.KMTAreas.A7.weylAvg P N α₁ 0 θ₁ θ₂
            * Work.KMTAreas.A7.ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))‖)
      ∧ (∑' p : ℤ × ℤ, ‖∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
          Work.KMTAreas.A7.varphiN N k₁ θ₁ * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ θ₂
            * Work.KMTAreas.A7.weylAvg P N α₁ 0 θ₁ θ₂
            * Work.KMTAreas.A7.ee (-((p.1 : ℝ) * θ₁ + (p.2 : ℝ) * θ₂))‖)
        ≤ C * (q : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ) := by
  obtain ⟨Km, hKmpos, hmass1, hmass2⟩ := Work.KMTPlan.A6.bumpFourierMass P
  obtain ⟨Cd, hCdpos, hd1, hd2⟩ := diffMassSharp P
  obtain ⟨Kp, hKppos, hPderiv⟩ := Work.A7.Pev.PevalR_deriv_bounds P
  have hKm0 : (0 : ℝ) ≤ Km := hKmpos.le
  have hCd0 : (0 : ℝ) ≤ Cd := hCdpos.le
  have hKp0 : (0 : ℝ) ≤ Kp := hKppos.le
  set Cm : ℝ := max Cd (4 * Km) with hCmdef
  have hCm0 : (0 : ℝ) ≤ Cm := by
    rw [hCmdef]
    exact le_trans (by linarith) (le_max_right _ _)
  have hCdCm : Cd ≤ Cm := by rw [hCmdef]; exact le_max_left _ _
  have h4KmCm : 4 * Km ≤ Cm := by rw [hCmdef]; exact le_max_right _ _
  set C₀ : ℝ := 4 * Km ^ 2 + 2 * Cm * Km + 2 * Km * Kp * Cm with hC₀def
  refine ⟨max 1 C₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro N q k₁ k₂ α₁ hN hq hqα hαne
  have hq1 : 1 ≤ q := by omega
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  set r₁ : ℝ := (2 : ℝ) ^ k₁ / (N : ℝ) with hr₁def
  set r₂ : ℝ := (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree with hr₂def
  have hr₁0 : (0 : ℝ) ≤ r₁ := by rw [hr₁def]; positivity
  have hr₂0 : (0 : ℝ) ≤ r₂ := by rw [hr₂def]; positivity
  have hr₁mul : ((N : ℝ)) * r₁ = (2 : ℝ) ^ k₁ := by
    rw [hr₁def]; field_simp
  have hr₂mul : ((N : ℝ) ^ P.natDegree) * r₂ = (2 : ℝ) ^ (P.natDegree * k₂) := by
    rw [hr₂def]; field_simp
  -- the mass bounds (at integer shifts, which is all we need)
  have hmA : ∀ u : ℤ, (∑' p : ℤ, ENNReal.ofReal ‖bA N k₁ ((u : ℝ) - (p : ℝ))‖)
      ≤ ENNReal.ofReal (Km * (1 + r₁)) := by
    intro u
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => norm_nonneg _) (summ_bA N k₁ u)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (∑' p : ℤ, ‖bA N k₁ ((u : ℝ) - (p : ℝ))‖)
        = (∑' p : ℤ, ‖∫ θ : ℝ, varphiN N k₁ θ * ee (((u : ℝ) - (p : ℝ)) * θ)‖) := rfl
      _ ≤ Km * (1 + (2 : ℝ) ^ k₁ / (N : ℝ)) := hmass1 N k₁ hN (u : ℝ)
      _ = Km * (1 + r₁) := by rw [hr₁def]
  have hmB : ∀ u : ℤ, (∑' p : ℤ, ENNReal.ofReal ‖bB P N k₂ ((u : ℝ) - (p : ℝ))‖)
      ≤ ENNReal.ofReal (Km * (1 + r₂)) := by
    intro u
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => norm_nonneg _) (summ_bB P N k₂ u)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (∑' p : ℤ, ‖bB P N k₂ ((u : ℝ) - (p : ℝ))‖)
        = (∑' p : ℤ, ‖∫ θ : ℝ, varphitildeN P.natDegree N k₂ θ * ee (((u : ℝ) - (p : ℝ)) * θ)‖) :=
          rfl
      _ ≤ Km * (1 + (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) :=
          hmass2 N k₂ hN (u : ℝ)
      _ = Km * (1 + r₂) := by rw [hr₂def]
  -- the difference-mass bounds
  have hdA : ∀ u : ℤ,
      (∑' p : ℤ, ENNReal.ofReal
        ‖bA N k₁ ((u : ℝ) + 1 - (p : ℝ)) - bA N k₁ ((u : ℝ) - (p : ℝ))‖)
        ≤ ENNReal.ofReal (Cm * r₁) := by
    intro u
    rcases le_or_gt ((2 : ℝ) ^ k₁) (N : ℝ) with hreg | hreg
    · have hsumm : Summable (fun p : ℤ => ‖bA N k₁ ((u : ℝ) + 1 - (p : ℝ))
            - bA N k₁ ((u : ℝ) - (p : ℝ))‖) := by
        have h := summ_bA_diff N k₁ u
        simpa only [Int.cast_one] using h
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => norm_nonneg _) hsumm]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (∑' p : ℤ, ‖bA N k₁ ((u : ℝ) + 1 - (p : ℝ)) - bA N k₁ ((u : ℝ) - (p : ℝ))‖)
          = (∑' p : ℤ, ‖bumpFT (varphiN N k₁) ((u : ℝ) + 1 - (p : ℝ))
              - bumpFT (varphiN N k₁) ((u : ℝ) - (p : ℝ))‖) := rfl
        _ ≤ Cd * ((2 : ℝ) ^ k₁ / (N : ℝ)) := hd1 N k₁ hN hreg (u : ℝ)
        _ = Cd * r₁ := by rw [hr₁def]
        _ ≤ Cm * r₁ := mul_le_mul_of_nonneg_right hCdCm hr₁0
    · have hr₁ge : 1 ≤ r₁ := by
        rw [hr₁def, le_div_iff₀ hNpos]
        linarith [hreg.le]
      have hconv : (∑' p : ℤ, ENNReal.ofReal
            ‖bA N k₁ ((u : ℝ) + 1 - (p : ℝ)) - bA N k₁ ((u : ℝ) - (p : ℝ))‖)
          = (∑' p : ℤ, ENNReal.ofReal
            ‖bA N k₁ ((((u + 1 : ℤ)) : ℝ) - (p : ℝ)) - bA N k₁ ((u : ℝ) - (p : ℝ))‖) := by
        refine tsum_congr (fun p => ?_)
        have h : bA N k₁ ((u : ℝ) + 1 - (p : ℝ)) = bA N k₁ ((((u + 1 : ℤ)) : ℝ) - (p : ℝ)) := by
          congr 1
          push_cast
          ring
        rw [h]
      rw [hconv]
      calc (∑' p : ℤ, ENNReal.ofReal
            ‖bA N k₁ ((((u + 1 : ℤ)) : ℝ) - (p : ℝ)) - bA N k₁ ((u : ℝ) - (p : ℝ))‖)
          ≤ ∑' p : ℤ, (ENNReal.ofReal ‖bA N k₁ ((((u + 1 : ℤ)) : ℝ) - (p : ℝ))‖
              + ENNReal.ofReal ‖bA N k₁ ((u : ℝ) - (p : ℝ))‖) := by
            refine ENNReal.tsum_le_tsum (fun p => ?_)
            rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (norm_sub_le _ _)
        _ = (∑' p : ℤ, ENNReal.ofReal ‖bA N k₁ ((((u + 1 : ℤ)) : ℝ) - (p : ℝ))‖)
            + (∑' p : ℤ, ENNReal.ofReal ‖bA N k₁ ((u : ℝ) - (p : ℝ))‖) := ENNReal.tsum_add
        _ ≤ ENNReal.ofReal (Km * (1 + r₁)) + ENNReal.ofReal (Km * (1 + r₁)) :=
            add_le_add (hmA (u + 1)) (hmA u)
        _ = ENNReal.ofReal (2 * (Km * (1 + r₁))) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            ring_nf
        _ ≤ ENNReal.ofReal (Cm * r₁) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 : 2 * (Km * (1 + r₁)) ≤ 4 * Km * r₁ := by nlinarith [hKm0, hr₁ge]
            exact h1.trans (mul_le_mul_of_nonneg_right h4KmCm hr₁0)
  have hdB : ∀ u : ℤ,
      (∑' p : ℤ, ENNReal.ofReal
        ‖bB P N k₂ ((u : ℝ) + 1 - (p : ℝ)) - bB P N k₂ ((u : ℝ) - (p : ℝ))‖)
        ≤ ENNReal.ofReal (Cm * r₂) := by
    intro u
    rcases le_or_gt ((2 : ℝ) ^ (P.natDegree * k₂)) ((N : ℝ) ^ P.natDegree) with hreg | hreg
    · have hsumm : Summable (fun p : ℤ => ‖bB P N k₂ ((u : ℝ) + 1 - (p : ℝ))
            - bB P N k₂ ((u : ℝ) - (p : ℝ))‖) := by
        simpa only [Int.cast_one, add_assoc] using summ_bB_diff P N k₂ u 1
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => norm_nonneg _) hsumm]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [bB]
      have h := hd2 N k₂ hN hreg (u : ℝ)
      rw [← hr₂def] at h
      exact h.trans (mul_le_mul_of_nonneg_right hCdCm hr₂0)
    · have hr₂ge : 1 ≤ r₂ := by
        rw [hr₂def, le_div_iff₀ (pow_pos hNpos _)]
        linarith [hreg.le]
      have hconv : (∑' p : ℤ, ENNReal.ofReal
            ‖bB P N k₂ ((u : ℝ) + 1 - (p : ℝ)) - bB P N k₂ ((u : ℝ) - (p : ℝ))‖)
          = (∑' p : ℤ, ENNReal.ofReal
            ‖bB P N k₂ ((((u + 1 : ℤ)) : ℝ) - (p : ℝ)) - bB P N k₂ ((u : ℝ) - (p : ℝ))‖) := by
        refine tsum_congr (fun p => ?_)
        have h : bB P N k₂ ((u : ℝ) + 1 - (p : ℝ))
            = bB P N k₂ ((((u + 1 : ℤ)) : ℝ) - (p : ℝ)) := by
          congr 1
          push_cast
          ring
        rw [h]
      rw [hconv]
      calc (∑' p : ℤ, ENNReal.ofReal
            ‖bB P N k₂ ((((u + 1 : ℤ)) : ℝ) - (p : ℝ)) - bB P N k₂ ((u : ℝ) - (p : ℝ))‖)
          ≤ ∑' p : ℤ, (ENNReal.ofReal ‖bB P N k₂ ((((u + 1 : ℤ)) : ℝ) - (p : ℝ))‖
              + ENNReal.ofReal ‖bB P N k₂ ((u : ℝ) - (p : ℝ))‖) := by
            refine ENNReal.tsum_le_tsum (fun p => ?_)
            rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (norm_sub_le _ _)
        _ = (∑' p : ℤ, ENNReal.ofReal ‖bB P N k₂ ((((u + 1 : ℤ)) : ℝ) - (p : ℝ))‖)
            + (∑' p : ℤ, ENNReal.ofReal ‖bB P N k₂ ((u : ℝ) - (p : ℝ))‖) := ENNReal.tsum_add
        _ ≤ ENNReal.ofReal (Km * (1 + r₂)) + ENNReal.ofReal (Km * (1 + r₂)) :=
            add_le_add (hmB (u + 1)) (hmB u)
        _ = ENNReal.ofReal (2 * (Km * (1 + r₂))) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            ring_nf
        _ ≤ ENNReal.ofReal (Cm * r₂) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 : 2 * (Km * (1 + r₂)) ≤ 4 * Km * r₂ := by nlinarith [hKm0, hr₂ge]
            exact h1.trans (mul_le_mul_of_nonneg_right h4KmCm hr₂0)
  have hdB_tr : ∀ u : ℤ, (∑' p : ℤ, ENNReal.ofReal
      ‖trF (bB P N k₂) u p 1 - trF (bB P N k₂) u p 0‖) ≤ ENNReal.ofReal (Cm * r₂) := by
    intro u
    have h := hdB u
    have hconv : (∑' p : ℤ, ENNReal.ofReal
        ‖trF (bB P N k₂) u p 1 - trF (bB P N k₂) u p 0‖)
        = (∑' p : ℤ, ENNReal.ofReal
          ‖bB P N k₂ ((u : ℝ) + 1 - (p : ℝ)) - bB P N k₂ ((u : ℝ) - (p : ℝ))‖) := by
      refine tsum_congr (fun p => ?_)
      have h1 : trF (bB P N k₂) u p 1 = bB P N k₂ ((u : ℝ) + 1 - (p : ℝ)) := by
        simp only [trF, Nat.cast_one]
        congr 1
        push_cast
        ring
      have h0 : trF (bB P N k₂) u p 0 = bB P N k₂ ((u : ℝ) - (p : ℝ)) := by
        simp only [trF, Nat.cast_zero, add_zero]
      rw [h1, h0]
    rw [hconv]
    exact h
  have hshB : ∀ (y a : ℤ), (∑' p : ℤ, ENNReal.ofReal
      ‖bB P N k₂ ((((y + a : ℤ)) : ℝ) - (p : ℝ)) - bB P N k₂ ((((y : ℤ)) : ℝ) - (p : ℝ))‖)
        ≤ ENNReal.ofReal (|(a : ℝ)| * (Cm * r₂)) := by
    intro y a
    have h := tsum_shift_le_int (bB P N k₂) (Cm * r₂) (mul_nonneg hCm0 hr₂0) hdB_tr y a
    have hconv : (∑' p : ℤ, ENNReal.ofReal
        ‖bB P N k₂ ((((y + a : ℤ)) : ℝ) - (p : ℝ)) - bB P N k₂ ((((y : ℤ)) : ℝ) - (p : ℝ))‖)
        = (∑' p : ℤ, ENNReal.ofReal ‖trF (bB P N k₂) (y + a) p 0 - trF (bB P N k₂) y p 0‖) := by
      refine tsum_congr (fun p => ?_)
      have h1 : trF (bB P N k₂) (y + a) p 0 = bB P N k₂ ((((y + a : ℤ)) : ℝ) - (p : ℝ)) := by
        simp only [trF, Nat.cast_zero, add_zero]
      have h0 : trF (bB P N k₂) y p 0 = bB P N k₂ ((((y : ℤ)) : ℝ) - (p : ℝ)) := by
        simp only [trF, Nat.cast_zero, add_zero]
      rw [h1, h0]
    rw [hconv]
    exact h
  -- the polynomial difference bound
  have hPd : ∀ n : ℕ, n + 1 ≤ N →
      |PevalR P ((n : ℝ) + 1) - PevalR P (n : ℝ)| ≤ Kp * (N : ℝ) ^ P.natDegree / (N : ℝ) := by
    intro n hn
    have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => PevalR P y)
        (deriv (fun y : ℝ => PevalR P y) x) x := by
      intro x
      have h2 : HasDerivAt (fun y : ℝ => (P.map (Int.castRingHom ℝ)).eval y)
          (((P.map (Int.castRingHom ℝ)).derivative).eval x) x :=
        Polynomial.hasDerivAt (P.map (Int.castRingHom ℝ)) x
      have h3 : deriv (fun y : ℝ => PevalR P y) x
          = ((P.map (Int.castRingHom ℝ)).derivative).eval x := by
        rw [Work.A7.Pev.deriv_PevalR P x, Polynomial.derivative_map]
      rw [h3]
      exact h2
    have hb := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun x : ℝ => PevalR P x)
      (f' := fun x : ℝ => deriv (fun y : ℝ => PevalR P y) x)
      (a := (n : ℝ)) (b := (n : ℝ) + 1) (C := Kp * (N : ℝ) ^ P.natDegree / (N : ℝ))
      (fun x _ => (hderiv x).hasDerivWithinAt) (fun x hx => ?_) ((n : ℝ) + 1)
      ⟨by linarith [Nat.cast_nonneg (α := ℝ) n], by linarith [Nat.cast_nonneg (α := ℝ) n]⟩
    · have hb1 : ((n : ℝ) + 1 - (n : ℝ)) = 1 := by ring
      rw [hb1, mul_one, Real.norm_eq_abs] at hb
      exact hb
    · rw [Real.norm_eq_abs]
      have hx2 : x < (n : ℝ) + 1 := hx.2
      have hnN : (n : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hn
      exact (hPderiv N hN x ⟨by linarith [hx.1, Nat.cast_nonneg (α := ℝ) n], by linarith⟩).2.1
  -- the finite-set bound
  have hfinite : ∀ F : Finset (ℤ × ℤ),
      ∑ p ∈ F, ENNReal.ofReal ‖bMass P N k₁ k₂ α₁ p‖
        ≤ ENNReal.ofReal ((N : ℝ)⁻¹ * (q : ℝ) *
            (Km ^ 2 * (1 + r₁) * (1 + r₂) + ((N : ℝ)) * Cm * r₁ * Km * (1 + r₂)
              + Km * (1 + r₁) * ((N : ℝ) ^ P.natDegree) * (Kp * (Cm * r₂)))) := by
    intro F
    have hpt : ∀ p : ℤ × ℤ, ENNReal.ofReal ‖bMass P N k₁ k₂ α₁ p‖
        ≤ ENNReal.ofReal ((N : ℝ)⁻¹ * (q : ℝ)) *
          (ENNReal.ofReal ‖bFibreR P N k₁ k₂ p (N : ℝ)‖
            + ∑ n ∈ Finset.Ico (N / 2 + 1) N,
                ENNReal.ofReal ‖bFibreR P N k₁ k₂ p ((n : ℝ) + 1) - bFibreR P N k₁ k₂ p (n : ℝ)‖) := by
      intro p
      have h := bMass_abel P N q k₁ k₂ α₁ hN hq hqα hαne p
      refine (ENNReal.ofReal_le_ofReal h).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [ENNReal.ofReal_add (norm_nonneg _) (by positivity)]
      congr 1
      rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => norm_nonneg _)]
    have h1F : ∑ p ∈ F, ENNReal.ofReal ‖bFibreR P N k₁ k₂ p (N : ℝ)‖
        ≤ ENNReal.ofReal (Km * (1 + r₁)) * ENNReal.ofReal (Km * (1 + r₂)) := by
      have hbridge : PevalR P ((N : ℝ)) = (((P.eval ((N : ℤ)) : ℤ)) : ℝ) := by
        rw [show (N : ℝ) = (((N : ℤ)) : ℝ) by push_cast; ring, pevalR_intCast]
      calc ∑ p ∈ F, ENNReal.ofReal ‖bFibreR P N k₁ k₂ p (N : ℝ)‖
          = ∑ p ∈ F, ENNReal.ofReal (‖bA N k₁ ((N : ℝ) - (p.1 : ℝ))‖
              * ‖bB P N k₂ (PevalR P (N : ℝ) - (p.2 : ℝ))‖) := by
              refine Finset.sum_congr rfl (fun p _ => ?_)
              rw [bFibreR, norm_mul]
        _ ≤ ∑' p : ℤ × ℤ, ENNReal.ofReal (‖bA N k₁ ((N : ℝ) - (p.1 : ℝ))‖
              * ‖bB P N k₂ (PevalR P (N : ℝ) - (p.2 : ℝ))‖) := ENNReal.sum_le_tsum F
        _ = (∑' p₁ : ℤ, ENNReal.ofReal ‖bA N k₁ ((N : ℝ) - (p₁ : ℝ))‖)
              * (∑' p₂ : ℤ, ENNReal.ofReal ‖bB P N k₂ (PevalR P (N : ℝ) - (p₂ : ℝ))‖) :=
              ennreal_tsum_prod_ofReal (fun a : ℤ => ‖bA N k₁ ((N : ℝ) - (a : ℝ))‖)
                (fun b : ℤ => ‖bB P N k₂ (PevalR P (N : ℝ) - (b : ℝ))‖)
                (fun a => norm_nonneg _) (fun b => norm_nonneg _)
        _ ≤ ENNReal.ofReal (Km * (1 + r₁))
              * ENNReal.ofReal (Km * (1 + r₂)) := by
              rw [hbridge]
              exact mul_le_mul' (by simpa only [Int.cast_natCast] using hmA (N : ℤ))
                (hmB (P.eval (N : ℤ)))
    have hn_pt : ∀ (n : ℕ), n + 1 ≤ N → ∀ p : ℤ × ℤ,
        ENNReal.ofReal ‖bFibreR P N k₁ k₂ p ((n : ℝ) + 1) - bFibreR P N k₁ k₂ p (n : ℝ)‖
          ≤ ENNReal.ofReal
              (‖bA N k₁ ((n : ℝ) + 1 - (p.1 : ℝ)) - bA N k₁ ((n : ℝ) - (p.1 : ℝ))‖
                 * ‖bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p.2 : ℝ))‖
               + ‖bA N k₁ ((n : ℝ) - (p.1 : ℝ))‖
                 * ‖bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p.2 : ℝ))
                     - bB P N k₂ (PevalR P (n : ℝ) - (p.2 : ℝ))‖) := by
      intro n hnN p
      refine ENNReal.ofReal_le_ofReal ?_
      have hd : bFibreR P N k₁ k₂ p ((n : ℝ) + 1) - bFibreR P N k₁ k₂ p (n : ℝ)
          = (bA N k₁ ((n : ℝ) + 1 - (p.1 : ℝ)) - bA N k₁ ((n : ℝ) - (p.1 : ℝ)))
              * bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p.2 : ℝ))
            + bA N k₁ ((n : ℝ) - (p.1 : ℝ))
              * (bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p.2 : ℝ))
                  - bB P N k₂ (PevalR P (n : ℝ) - (p.2 : ℝ))) := by
        simp only [bFibreR]; ring
      rw [hd]
      calc ‖(bA N k₁ ((n : ℝ) + 1 - (p.1 : ℝ)) - bA N k₁ ((n : ℝ) - (p.1 : ℝ)))
              * bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p.2 : ℝ))
            + bA N k₁ ((n : ℝ) - (p.1 : ℝ))
              * (bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p.2 : ℝ))
                  - bB P N k₂ (PevalR P (n : ℝ) - (p.2 : ℝ)))‖
          ≤ ‖(bA N k₁ ((n : ℝ) + 1 - (p.1 : ℝ)) - bA N k₁ ((n : ℝ) - (p.1 : ℝ)))
              * bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p.2 : ℝ))‖
            + ‖bA N k₁ ((n : ℝ) - (p.1 : ℝ))
              * (bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p.2 : ℝ))
                  - bB P N k₂ (PevalR P (n : ℝ) - (p.2 : ℝ)))‖ := norm_add_le _ _
        _ = ‖bA N k₁ ((n : ℝ) + 1 - (p.1 : ℝ)) - bA N k₁ ((n : ℝ) - (p.1 : ℝ))‖
              * ‖bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p.2 : ℝ))‖
            + ‖bA N k₁ ((n : ℝ) - (p.1 : ℝ))‖
              * ‖bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p.2 : ℝ))
                  - bB P N k₂ (PevalR P (n : ℝ) - (p.2 : ℝ))‖ := by rw [norm_mul, norm_mul]
    have hn : ∀ n ∈ Finset.Ico (N / 2 + 1) N,
        ∑ p ∈ F, ENNReal.ofReal ‖bFibreR P N k₁ k₂ p ((n : ℝ) + 1) - bFibreR P N k₁ k₂ p (n : ℝ)‖
          ≤ ENNReal.ofReal (Cm * r₁) * ENNReal.ofReal (Km * (1 + r₂))
            + ENNReal.ofReal (Km * (1 + r₁))
              * ENNReal.ofReal ((Kp * (N : ℝ) ^ P.natDegree / (N : ℝ)) * (Cm * r₂)) := by
      intro n hnmem
      have hnN : n + 1 ≤ N := by
        have := (Finset.mem_Ico.mp hnmem).2
        omega
      have hsucc := pevalR_succ P n
      have hA1 : (∑' p : ℤ, ENNReal.ofReal
            ‖bA N k₁ ((n : ℝ) + 1 - (p : ℝ)) - bA N k₁ ((n : ℝ) - (p : ℝ))‖)
          ≤ ENNReal.ofReal (Cm * r₁) := by
        have h := hdA (n : ℤ)
        simpa only [Int.cast_natCast] using h
      have hA2 : (∑' p : ℤ, ENNReal.ofReal ‖bA N k₁ ((n : ℝ) - (p : ℝ))‖)
          ≤ ENNReal.ofReal (Km * (1 + r₁)) := by
        have h := hmA (n : ℤ)
        simpa only [Int.cast_natCast] using h
      have hB1 : (∑' p : ℤ, ENNReal.ofReal ‖bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p : ℝ))‖)
          ≤ ENNReal.ofReal (Km * (1 + r₂)) := by
        rw [hsucc]
        exact hmB (P.eval ((n : ℤ) + 1))
      have hB2 : (∑' p : ℤ, ENNReal.ofReal
            ‖bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p : ℝ))
              - bB P N k₂ (PevalR P (n : ℝ) - (p : ℝ))‖)
          ≤ ENNReal.ofReal ((Kp * (N : ℝ) ^ P.natDegree / (N : ℝ)) * (Cm * r₂)) := by
        have hPn : PevalR P ((n : ℝ)) = (((P.eval (n : ℤ)) : ℤ) : ℝ) := by
          have hcast : (n : ℝ) = (((n : ℤ)) : ℝ) := by push_cast; ring
          rw [hcast, pevalR_intCast]
        have hleft : (∑' p : ℤ, ENNReal.ofReal
              ‖bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p : ℝ))
                - bB P N k₂ (PevalR P (n : ℝ) - (p : ℝ))‖)
            = (∑' p : ℤ, ENNReal.ofReal
              ‖bB P N k₂ (PevalR P (n : ℝ) + ((P.eval ((n : ℤ) + 1) - P.eval (n : ℤ) : ℤ) : ℝ)
                    - (p : ℝ))
                - bB P N k₂ (PevalR P (n : ℝ) - (p : ℝ))‖) := by
          refine tsum_congr (fun p => ?_)
          have harg : PevalR P ((n : ℝ) + 1) - (p : ℝ)
              = PevalR P (n : ℝ) + ((P.eval ((n : ℤ) + 1) - P.eval (n : ℤ) : ℤ) : ℝ) - (p : ℝ) := by
            rw [← shift_int P n]
            ring
          rw [harg]
        have hleft2 : (∑' p : ℤ, ENNReal.ofReal
              ‖bB P N k₂ (PevalR P (n : ℝ) + ((P.eval ((n : ℤ) + 1) - P.eval (n : ℤ) : ℤ) : ℝ)
                    - (p : ℝ))
                - bB P N k₂ (PevalR P (n : ℝ) - (p : ℝ))‖)
            = (∑' p : ℤ, ENNReal.ofReal
              ‖bB P N k₂ ((((P.eval (n : ℤ) + (P.eval ((n : ℤ) + 1) - P.eval (n : ℤ)) : ℤ)) : ℝ)
                    - (p : ℝ))
                - bB P N k₂ ((((P.eval (n : ℤ)) : ℤ) : ℝ) - (p : ℝ))‖) := by
          refine tsum_congr (fun p => ?_)
          have harg : PevalR P (n : ℝ) + ((P.eval ((n : ℤ) + 1) - P.eval (n : ℤ) : ℤ) : ℝ)
              = (((P.eval (n : ℤ) + (P.eval ((n : ℤ) + 1) - P.eval (n : ℤ)) : ℤ)) : ℝ) := by
            rw [hPn]
            push_cast
            ring
          rw [harg, hPn]
        rw [hleft, hleft2]
        have hsh := hshB (P.eval (n : ℤ)) (P.eval ((n : ℤ) + 1) - P.eval (n : ℤ))
        refine hsh.trans ?_
        refine ENNReal.ofReal_le_ofReal ?_
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hCm0 hr₂0)
        have habs : |((P.eval ((n : ℤ) + 1) - P.eval (n : ℤ) : ℤ) : ℝ)|
            = |PevalR P ((n : ℝ) + 1) - PevalR P (n : ℝ)| := by
          rw [shift_int P n]
        rw [habs]
        exact hPd n hnN
      calc ∑ p ∈ F, ENNReal.ofReal
            ‖bFibreR P N k₁ k₂ p ((n : ℝ) + 1) - bFibreR P N k₁ k₂ p (n : ℝ)‖
          ≤ ∑' p : ℤ × ℤ, ENNReal.ofReal
              (‖bA N k₁ ((n : ℝ) + 1 - (p.1 : ℝ)) - bA N k₁ ((n : ℝ) - (p.1 : ℝ))‖
                 * ‖bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p.2 : ℝ))‖
               + ‖bA N k₁ ((n : ℝ) - (p.1 : ℝ))‖
                 * ‖bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p.2 : ℝ))
                     - bB P N k₂ (PevalR P (n : ℝ) - (p.2 : ℝ))‖) :=
              (ENNReal.sum_le_tsum F).trans (ENNReal.tsum_le_tsum (fun p => hn_pt n hnN p))
        _ = (∑' p : ℤ × ℤ, ENNReal.ofReal
              (‖bA N k₁ ((n : ℝ) + 1 - (p.1 : ℝ)) - bA N k₁ ((n : ℝ) - (p.1 : ℝ))‖
                 * ‖bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p.2 : ℝ))‖))
            + (∑' p : ℤ × ℤ, ENNReal.ofReal
              (‖bA N k₁ ((n : ℝ) - (p.1 : ℝ))‖
                 * ‖bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p.2 : ℝ))
                     - bB P N k₂ (PevalR P (n : ℝ) - (p.2 : ℝ))‖)) := by
              rw [← ENNReal.tsum_add]
              exact tsum_congr (fun p => ENNReal.ofReal_add (by positivity) (by positivity))
        _ = (∑' p₁ : ℤ, ENNReal.ofReal
                ‖bA N k₁ ((n : ℝ) + 1 - (p₁ : ℝ)) - bA N k₁ ((n : ℝ) - (p₁ : ℝ))‖)
              * (∑' p₂ : ℤ, ENNReal.ofReal ‖bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p₂ : ℝ))‖)
            + (∑' p₁ : ℤ, ENNReal.ofReal ‖bA N k₁ ((n : ℝ) - (p₁ : ℝ))‖)
              * (∑' p₂ : ℤ, ENNReal.ofReal
                  ‖bB P N k₂ (PevalR P ((n : ℝ) + 1) - (p₂ : ℝ))
                    - bB P N k₂ (PevalR P (n : ℝ) - (p₂ : ℝ))‖) := by
              rw [ennreal_tsum_prod_ofReal (fun a : ℤ => ‖bA N k₁ ((n : ℝ) + 1 - (a : ℝ))
                      - bA N k₁ ((n : ℝ) - (a : ℝ))‖)
                    (fun b : ℤ => ‖bB P N k₂ (PevalR P ((n : ℝ) + 1) - (b : ℝ))‖)
                    (fun a => norm_nonneg _) (fun b => norm_nonneg _),
                  ennreal_tsum_prod_ofReal (fun a : ℤ => ‖bA N k₁ ((n : ℝ) - (a : ℝ))‖)
                    (fun b : ℤ => ‖bB P N k₂ (PevalR P ((n : ℝ) + 1) - (b : ℝ))
                      - bB P N k₂ (PevalR P (n : ℝ) - (b : ℝ))‖)
                    (fun a => norm_nonneg _) (fun b => norm_nonneg _)]
        _ ≤ ENNReal.ofReal (Cm * r₁) * ENNReal.ofReal (Km * (1 + r₂))
            + ENNReal.ofReal (Km * (1 + r₁))
              * ENNReal.ofReal ((Kp * (N : ℝ) ^ P.natDegree / (N : ℝ)) * (Cm * r₂)) :=
              add_le_add (mul_le_mul' hA1 hB1) (mul_le_mul' hA2 hB2)
    have hcard : (Finset.Ico (N / 2 + 1) N).card ≤ N := by
      have hsub : Finset.Ico (N / 2 + 1) N ⊆ Finset.range N := by
        intro x hx
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
      calc (Finset.Ico (N / 2 + 1) N).card ≤ (Finset.range N).card := Finset.card_le_card hsub
        _ = N := Finset.card_range N
    have h2F : ∑ p ∈ F, ∑ n ∈ Finset.Ico (N / 2 + 1) N,
          ENNReal.ofReal ‖bFibreR P N k₁ k₂ p ((n : ℝ) + 1) - bFibreR P N k₁ k₂ p (n : ℝ)‖
        ≤ ENNReal.ofReal (((N : ℝ)) * Cm * r₁ * Km * (1 + r₂)
            + Km * (1 + r₁) * ((N : ℝ) ^ P.natDegree) * (Kp * (Cm * r₂))) := by
      rw [Finset.sum_comm]
      calc ∑ n ∈ Finset.Ico (N / 2 + 1) N,
            ∑ p ∈ F, ENNReal.ofReal
              ‖bFibreR P N k₁ k₂ p ((n : ℝ) + 1) - bFibreR P N k₁ k₂ p (n : ℝ)‖
          ≤ ∑ n ∈ Finset.Ico (N / 2 + 1) N,
              (ENNReal.ofReal (Cm * r₁) * ENNReal.ofReal (Km * (1 + r₂))
                + ENNReal.ofReal (Km * (1 + r₁))
                  * ENNReal.ofReal ((Kp * (N : ℝ) ^ P.natDegree / (N : ℝ)) * (Cm * r₂))) :=
              Finset.sum_le_sum (fun n hnm => hn n hnm)
        _ = (∑ _n ∈ Finset.Ico (N / 2 + 1) N,
                ENNReal.ofReal (Cm * r₁) * ENNReal.ofReal (Km * (1 + r₂)))
            + ∑ _n ∈ Finset.Ico (N / 2 + 1) N,
                ENNReal.ofReal (Km * (1 + r₁))
                  * ENNReal.ofReal ((Kp * (N : ℝ) ^ P.natDegree / (N : ℝ)) * (Cm * r₂)) :=
              Finset.sum_add_distrib
        _ ≤ ENNReal.ofReal ((N : ℝ) * ((Cm * r₁) * (Km * (1 + r₂))))
            + ENNReal.ofReal ((N : ℝ) * (Km * (1 + r₁)
                * ((Kp * (N : ℝ) ^ P.natDegree / (N : ℝ)) * (Cm * r₂)))) :=
              add_le_add
                (ennreal_sum_const_mul_le (Finset.Ico (N / 2 + 1) N) N hcard
                  (by positivity) (by positivity))
                (ennreal_sum_const_mul_le (Finset.Ico (N / 2 + 1) N) N hcard
                  (by positivity) (by positivity))
        _ = ENNReal.ofReal (((N : ℝ)) * Cm * r₁ * Km * (1 + r₂)
            + Km * (1 + r₁) * ((N : ℝ) ^ P.natDegree) * (Kp * (Cm * r₂))) := by
              have h1 : (N : ℝ) * (Km * (1 + r₁)
                    * ((Kp * (N : ℝ) ^ P.natDegree / (N : ℝ)) * (Cm * r₂)))
                  = Km * (1 + r₁) * ((N : ℝ) ^ P.natDegree) * (Kp * (Cm * r₂)) := by
                field_simp <;> ring
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
              refine congrArg ENNReal.ofReal ?_
              rw [h1]
              ring
    calc ∑ p ∈ F, ENNReal.ofReal ‖bMass P N k₁ k₂ α₁ p‖
        ≤ ∑ p ∈ F, ENNReal.ofReal ((N : ℝ)⁻¹ * (q : ℝ)) *
            (ENNReal.ofReal ‖bFibreR P N k₁ k₂ p (N : ℝ)‖
              + ∑ n ∈ Finset.Ico (N / 2 + 1) N,
                  ENNReal.ofReal ‖bFibreR P N k₁ k₂ p ((n : ℝ) + 1) - bFibreR P N k₁ k₂ p (n : ℝ)‖) :=
            Finset.sum_le_sum (fun p _ => hpt p)
      _ = ENNReal.ofReal ((N : ℝ)⁻¹ * (q : ℝ)) *
            ((∑ p ∈ F, ENNReal.ofReal ‖bFibreR P N k₁ k₂ p (N : ℝ)‖)
              + ∑ p ∈ F, ∑ n ∈ Finset.Ico (N / 2 + 1) N,
                  ENNReal.ofReal ‖bFibreR P N k₁ k₂ p ((n : ℝ) + 1) - bFibreR P N k₁ k₂ p (n : ℝ)‖) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ ENNReal.ofReal ((N : ℝ)⁻¹ * (q : ℝ)) *
            (ENNReal.ofReal (Km * (1 + r₁)) * ENNReal.ofReal (Km * (1 + r₂))
              + ENNReal.ofReal (((N : ℝ)) * Cm * r₁ * Km * (1 + r₂)
                  + Km * (1 + r₁) * ((N : ℝ) ^ P.natDegree) * (Kp * (Cm * r₂)))) :=
            mul_le_mul' le_rfl (add_le_add h1F h2F)
      _ = ENNReal.ofReal ((N : ℝ)⁻¹ * (q : ℝ) *
            (Km ^ 2 * (1 + r₁) * (1 + r₂) + ((N : ℝ)) * Cm * r₁ * Km * (1 + r₂)
              + Km * (1 + r₁) * ((N : ℝ) ^ P.natDegree) * (Kp * (Cm * r₂)))) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
                ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
  -- the tsum bound and summability
  have hsum_bound : (∑' p : ℤ × ℤ, ENNReal.ofReal ‖bMass P N k₁ k₂ α₁ p‖)
      ≤ ENNReal.ofReal ((max 1 C₀) * (q : ℝ) ^ 2
          * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
          * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ)) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le (fun F => (hfinite F).trans ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    have hS : (0 : ℝ) ≤ (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ) := by positivity
    have h := arith_bound P.natDegree (N := N) (q := q) (k₁ := k₁) (k₂ := k₂)
      (Km := Km) (Cm := Cm) (Kp := Kp) (C₀ := C₀) (r₁ := r₁) (r₂ := r₂)
      (s := (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
      hN hq1 hKm0 hKp0 hCm0 hr₁0 hr₂0 hS hC₀def hr₁mul hr₂mul
    simpa using h
  constructor
  · have hne : (∑' p : ℤ × ℤ, ENNReal.ofReal ‖bMass P N k₁ k₂ α₁ p‖) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_lt_top.ne hsum_bound
    have h := ENNReal.summable_toReal hne
    have h2 : (fun p : ℤ × ℤ => (ENNReal.ofReal ‖bMass P N k₁ k₂ α₁ p‖).toReal)
        = fun p : ℤ × ℤ => ‖bMass P N k₁ k₂ α₁ p‖ := by
      funext p
      exact ENNReal.toReal_ofReal (norm_nonneg _)
    rwa [h2] at h
  · have h1 : ENNReal.ofReal (∑' p : ℤ × ℤ, ‖bMass P N k₁ k₂ α₁ p‖)
        = ∑' p : ℤ × ℤ, ENNReal.ofReal ‖bMass P N k₁ k₂ α₁ p‖ :=
      ENNReal.ofReal_tsum_of_nonneg (fun p => norm_nonneg _)
        (by
          have h := ENNReal.summable_toReal
            (ne_top_of_le_ne_top ENNReal.ofReal_lt_top.ne hsum_bound)
          have h2 : (fun p : ℤ × ℤ => (ENNReal.ofReal ‖bMass P N k₁ k₂ α₁ p‖).toReal)
              = fun p : ℤ × ℤ => ‖bMass P N k₁ k₂ α₁ p‖ := by
            funext p
            exact ENNReal.toReal_ofReal (norm_nonneg _)
          rwa [h2] at h)
    rw [← h1] at hsum_bound
    have h2 : (0 : ℝ) ≤ (max 1 C₀) * (q : ℝ) ^ 2
        * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
        * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ) := by
      have hM : (0 : ℝ) ≤ max 1 C₀ := le_trans zero_le_one (le_max_left _ _)
      positivity
    exact (ENNReal.ofReal_le_ofReal_iff h2).mp hsum_bound

end

end Work.KMTAreas.A7
