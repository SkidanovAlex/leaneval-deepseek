import Mathlib
import Submission.Work.Analysis.Variation.rademacher_menshov_two_dim
import Submission.Work.Analysis.Variation.eLpNorm_sum_rpow_le
import Submission.Work.Analysis.Variation.bilinear_block_lp
import Submission.Work.Analysis.Variation.bilinear_tiling_sum
import Submission.Work.Analysis.Variation.double_khintchine
import Submission.Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped ENNReal

namespace Work.Analysis.Variation

section Aux

variable {V W X : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [MeasurableSpace X] {μ : Measure X}

lemma aemeasurable_bilinear_sub (B : V → W → X → ℂ)
    (hadd₁ : ∀ (v v' : V) (w : W), B (v + v') w = B v w + B v' w)
    (hsmul₁ : ∀ (c : ℂ) (v : V) (w : W), B (c • v) w = c • B v w)
    (hadd₂ : ∀ (v : V) (w w' : W), B v (w + w') = B v w + B v w')
    (hsmul₂ : ∀ (c : ℂ) (v : V) (w : W), B v (c • w) = c • B v w)
    (f : ℕ → V) (g : ℕ → W)
    (hmeas : ∀ (i j : ℕ), _root_.AEMeasurable (fun x => B (f i) (g j) x) μ)
    (i i' j j' : ℕ) :
    _root_.AEMeasurable (fun x => B (f i - f i') (g j - g j') x) μ := by
  have hfun : (fun x => B (f i - f i') (g j - g j') x)
      = fun x => (B (f i) (g j) x - B (f i) (g j') x)
          - (B (f i') (g j) x - B (f i') (g j') x) := by
    funext x
    rw [bil_sub₁_apply B hadd₁ hsmul₁, bil_sub₂_apply B hadd₂ hsmul₂,
      bil_sub₂_apply B hadd₂ hsmul₂]
  rw [hfun]
  exact ((hmeas i j).sub (hmeas i j')).sub ((hmeas i' j).sub (hmeas i' j'))

lemma div_lt_nb {K M k : ℕ} (hM : 0 < M) (hk : k < K) : k / M < nb K M := by
  have h1 : k / M ≤ (K - 1) / M := Nat.div_le_div_right (by omega)
  have h2 : nb K M = (K - 1) / M + 1 := by
    rw [nb, show K + M - 1 = M * 1 + (K - 1) by omega, Nat.mul_add_div hM]
    omega
  omega

lemma tiling_sum_eq {V : Type*} [AddCommGroup V] [Module ℂ V] (K M : ℕ) (hM : 0 < M)
    (f : ℕ → V) (d : Fin (nb K M) → Bool) :
    (∑ i : Fin (nb K M), sgn (d i) • (f (min (M * ((i : ℕ) + 1)) K) - f (M * (i : ℕ))))
      = ∑ k : Fin K, sgn (d ⟨(k : ℕ) / M, div_lt_nb hM k.isLt⟩) •
          (f ((k : ℕ) + 1) - f (k : ℕ)) := by
  have h := bilinear_tiling_sum K M hM f
    (fun j => if hj : j < nb K M then d ⟨j, hj⟩ else false)
  rw [show (∑ i : Fin (nb K M),
        sgn ((fun j => if hj : j < nb K M then d ⟨j, hj⟩ else false) (i : ℕ)) •
          (f (min (M * ((i : ℕ) + 1)) K) - f (M * (i : ℕ))))
      = ∑ i : Fin (nb K M), sgn (d i) •
          (f (min (M * ((i : ℕ) + 1)) K) - f (M * (i : ℕ))) from
      Finset.sum_congr rfl fun i _ => by
        show sgn (if hj : (i : ℕ) < nb K M then d ⟨(i : ℕ), hj⟩ else false) •
            (f (min (M * ((i : ℕ) + 1)) K) - f (M * (i : ℕ))) = sgn (d i) •
            (f (min (M * ((i : ℕ) + 1)) K) - f (M * (i : ℕ)))
        rw [dif_pos i.isLt]] at h
  rw [show (∑ k : Fin K,
        sgn ((fun j => if hj : j < nb K M then d ⟨j, hj⟩ else false) ((k : ℕ) / M)) •
          (f ((k : ℕ) + 1) - f (k : ℕ)))
      = ∑ k : Fin K, sgn (d ⟨(k : ℕ) / M, div_lt_nb hM k.isLt⟩) •
          (f ((k : ℕ) + 1) - f (k : ℕ)) from
      Finset.sum_congr rfl fun k _ => by
        show sgn (if hj : (k : ℕ) / M < nb K M then d ⟨(k : ℕ) / M, hj⟩ else false) •
            (f ((k : ℕ) + 1) - f (k : ℕ)) = _
        rw [dif_pos (div_lt_nb hM k.isLt)]] at h
  exact h

lemma tiling_bilinear_fun (B : V → W → X → ℂ)
    (K M₁ M₂ : ℕ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (f : ℕ → V) (g : ℕ → W)
    (d₁ : Fin (nb K M₁) → Bool) (d₂ : Fin (nb K M₂) → Bool) :
    (fun x => B (∑ i : Fin (nb K M₁), sgn (d₁ i) •
          (f (min (M₁ * ((i : ℕ) + 1)) K) - f (M₁ * (i : ℕ))))
        (∑ j : Fin (nb K M₂), sgn (d₂ j) •
          (g (min (M₂ * ((j : ℕ) + 1)) K) - g (M₂ * (j : ℕ)))) x)
      = fun x => B (∑ k : Fin K, sgn (d₁ ⟨(k : ℕ) / M₁, div_lt_nb hM₁ k.isLt⟩) •
            (f ((k : ℕ) + 1) - f (k : ℕ)))
          (∑ k : Fin K, sgn (d₂ ⟨(k : ℕ) / M₂, div_lt_nb hM₂ k.isLt⟩) •
            (g ((k : ℕ) + 1) - g (k : ℕ))) x := by
  funext x
  rw [tiling_sum_eq K M₁ hM₁ f d₁, tiling_sum_eq K M₂ hM₂ g d₂]

lemma incLp2_bilinear_eq (B : V → W → X → ℂ)
    (hadd₁ : ∀ (v v' : V) (w : W), B (v + v') w = B v w + B v' w)
    (hsmul₁ : ∀ (c : ℂ) (v : V) (w : W), B (c • v) w = c • B v w)
    (hadd₂ : ∀ (v : V) (w w' : W), B v (w + w') = B v w + B v w')
    (hsmul₂ : ∀ (c : ℂ) (v : V) (w : W), B v (c • w) = c • B v w)
    (K M₁ M₂ : ℕ) (f : ℕ → V) (g : ℕ → W) :
    (fun x => incLp2 2 K M₁ M₂ (fun k₁ k₂ => B (f k₁) (g k₂) x))
      = fun x => (∑ q ∈ (Finset.range (nb K M₁)).product (Finset.range (nb K M₂)),
          ‖B (f (min (M₁ * (q.1 + 1)) K) - f (M₁ * q.1))
             (g (min (M₂ * (q.2 + 1)) K) - g (M₂ * q.2)) x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  funext x
  simp only [incLp2]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [blockDelta2_eq_apply B hadd₁ hsmul₁ hadd₂ hsmul₂ f g K M₁ (M₁ * q.1) M₂ (M₂ * q.2) x]
  have e₁ : min (M₁ * q.1 + M₁) K = min (M₁ * (q.1 + 1)) K := by rw [Nat.mul_add, Nat.mul_one]
  have e₂ : min (M₂ * q.2 + M₂) K = min (M₂ * (q.2 + 1)) K := by rw [Nat.mul_add, Nat.mul_one]
  rw [e₁, e₂]

lemma aemeasurable_incLp2_bilinear (B : V → W → X → ℂ)
    (hadd₁ : ∀ (v v' : V) (w : W), B (v + v') w = B v w + B v' w)
    (hsmul₁ : ∀ (c : ℂ) (v : V) (w : W), B (c • v) w = c • B v w)
    (hadd₂ : ∀ (v : V) (w w' : W), B v (w + w') = B v w + B v w')
    (hsmul₂ : ∀ (c : ℂ) (v : V) (w : W), B v (c • w) = c • B v w)
    (f : ℕ → V) (g : ℕ → W)
    (hmeas : ∀ (i j : ℕ), _root_.AEMeasurable (fun x => B (f i) (g j) x) μ)
    (K M₁ M₂ : ℕ) :
    _root_.AEMeasurable (fun x => incLp2 2 K M₁ M₂ (fun k₁ k₂ => B (f k₁) (g k₂) x)) μ := by
  rw [incLp2_bilinear_eq B hadd₁ hsmul₁ hadd₂ hsmul₂ K M₁ M₂ f g]
  refine (Finset.aemeasurable_fun_sum _ fun q _ => ?_).pow_const _
  exact ((aemeasurable_bilinear_sub B hadd₁ hsmul₁ hadd₂ hsmul₂ f g hmeas
    (min (M₁ * (q.1 + 1)) K) (M₁ * q.1)
    (min (M₂ * (q.2 + 1)) K) (M₂ * q.2)).enorm).pow_const _

lemma log2_sq_le (K : ℕ) (q : ℝ) (hq : 0 < q) :
    ((Nat.log2 K + 1 : ℕ) : ℝ) ^ 2
      ≤ ((Nat.log2 K : ℝ) + 2) ^ (max 2 (2 / q)) := by
  have hcast : ((Nat.log2 K + 1 : ℕ) : ℝ) = (Nat.log2 K : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have h1 : ((Nat.log2 K : ℝ) + 1) ^ (2 : ℝ) ≤ ((Nat.log2 K : ℝ) + 2) ^ (2 : ℝ) := by
    rw [Real.rpow_two, Real.rpow_two]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc ((Nat.log2 K : ℝ) + 1) ^ 2
      = ((Nat.log2 K : ℝ) + 1) ^ (2 : ℝ) := (Real.rpow_two _).symm
    _ ≤ ((Nat.log2 K : ℝ) + 2) ^ (2 : ℝ) := h1
    _ ≤ ((Nat.log2 K : ℝ) + 2) ^ (max 2 (2 / q)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)

lemma log2_rpow_le (K : ℕ) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    ((Nat.log2 K + 1 : ℕ) : ℝ) ^ (2 / q)
      ≤ ((Nat.log2 K : ℝ) + 2) ^ (max 2 (2 / q)) := by
  have hcast : ((Nat.log2 K + 1 : ℕ) : ℝ) = (Nat.log2 K : ℝ) + 1 := by push_cast; ring
  have hmax : max 2 (2 / q) = 2 / q := by
    have : (2:ℝ) ≤ 2 / q := by
      have h1q : (1:ℝ) ≤ 1 / q := one_le_one_div hq hq1
      have h2q : (2:ℝ) / q = 2 * (1 / q) := by ring
      linarith
    exact max_eq_right this
  rw [hcast, hmax]
  exact Real.rpow_le_rpow (by positivity) (by linarith)
    (by positivity : (0:ℝ) ≤ 2 / q)

end Aux

end Work.Analysis.Variation
