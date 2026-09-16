import Mathlib
import Submission.MainSumPairwise
import Submission.SieveSupport

open scoped BigOperators Topology
open Filter MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
# The main term of Polymath8a Theorem 3.6(i)

The window expansion (`Submission/SieveExpansion.lean`) writes the residue-window
product of the Maynard divisor sums as `goodMainSum + goodErrSum`.  The error
half is bounded in `Submission/SieveSupport.lean`; this module evaluates the
main half:

  * `pairWeightDiv_eq_zero_of_gt` — the pairwise divisor weight vanishes once a
    coordinate exceeds the support bound `R^M` of the smooth cutoffs;
  * `goodMainSum_asymptotic` — for the modulus family `N = 1`,
    `goodMainSum (μFᵢ(log_x ·)) (μGᵢ(log_x ·)) = (1/W)·prefactor^k·∏ᵢ∫₀^∞Fᵢ′Gᵢ′`
    up to a relative error `o(1)`, uniformly over truncation parameters
    `D ≥ x^M`.  This is obtained from the algebraic identification
    (`MainSumPairwise.goodMainSum_lamDiv_eq_mul_pairwiseSum`), the finite-to-`tsum`
    exhaustion (`MainSumPairwise.sum_fin_eq_tsum`) and the pairwise P8 Lemma 4.1
    (`PairwiseLemma41.pairwiseLemma41`).

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The norm of a real number inside `ℂ`. -/
lemma norm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ = |r| := RCLike.norm_ofReal r

/-- The pairwise divisor weight vanishes once a coordinate leaves the support. -/
theorem pairWeightDiv_eq_zero_of_gt {k : ℕ} (F G : Fin k → ℝ → ℝ) (R W : ℕ)
    {M : ℝ} (hM : ∀ i : Fin k, ∀ t : ℝ, M < |t| → F i t = 0 ∧ G i t = 0)
    (hR : 1 < R) {D : ℕ} (hD : (R : ℝ) ^ M ≤ (D : ℝ)) (t : Fin k → ℕ × ℕ)
    (h : ∃ i : Fin k, D < (t i).1 ∨ D < (t i).2) : pairWeightDiv F G W R t = 0 := by
  rw [pairWeightDiv]
  by_cases hg : (∀ j : Fin k, ((t j).1.lcm (t j).2).Coprime W) ∧ PairwiseCoprimeK t
  · rw [if_pos hg]
    obtain ⟨i, hi | hi⟩ := h
    · have hd0 : (t i).1 ≠ 0 := by omega
      have hlog : M < logR (t i).1 R := by
        by_contra hcon
        push_neg at hcon
        have h2 : ((t i).1 : ℝ) ≤ (R : ℝ) ^ M := le_rpow_of_logR_le hR hd0 hcon
        have h3 : ((t i).1 : ℝ) ≤ (D : ℝ) := le_trans h2 hD
        have h4 : (t i).1 ≤ D := by exact_mod_cast h3
        omega
      have hF0 : F i (logR (t i).1 R) = 0 :=
        (hM i _ (lt_of_lt_of_le hlog (le_abs_self _))).1
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hF0])
    · have hd0 : (t i).2 ≠ 0 := by omega
      have hlog : M < logR (t i).2 R := by
        by_contra hcon
        push_neg at hcon
        have h2 : ((t i).2 : ℝ) ≤ (R : ℝ) ^ M := le_rpow_of_logR_le hR hd0 hcon
        have h3 : ((t i).2 : ℝ) ≤ (D : ℝ) := le_trans h2 hD
        have h4 : (t i).2 ≤ D := by exact_mod_cast h3
        omega
      have hG0 : G i (logR (t i).2 R) = 0 :=
        (hM i _ (lt_of_lt_of_le hlog (le_abs_self _))).2
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hG0])
  · rw [if_neg hg]

/-- **The main term of Polymath8a Theorem 3.6(i)** (in the form used, with
modulus `N = 1`).  The `goodMainSum` of the window expansion, with the Maynard
divisor weights `μ(d)Fᵢ(log_x d)`, equals `(1/W)·prefactor^k·∏ᵢ∫₀^∞ Fᵢ′Gᵢ′` up to
a relative error `o(1)`, uniformly in the truncation parameter `D ≥ x^M`
(`M` a support bound of the cutoffs). -/
theorem goodMainSum_asymptotic {k : ℕ} (hk : 1 ≤ k)
    (F G : Fin k → ℝ → ℝ) (hcsF : ∀ i, HasCompactSupport (F i))
    (hsmF : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (F i)) (hcsG : ∀ i, HasCompactSupport (G i))
    (hsmG : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (G i))
    (Wf : ℕ → ℕ) (hW : ∀ x, Wf x ≠ 0)
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ Wf x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log ((Wf x : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    {M : ℝ} (hM : ∀ i : Fin k, ∀ t : ℝ, M < |t| → F i t = 0 ∧ G i t = 0)
    (D : ℕ → ℕ) (hD : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ M ≤ (D x : ℝ)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x →
        ‖(((goodMainSum (k := k) (D := D x) (N := 1) (W := Wf x)
              (fun i d => lamDivWeight (F i) x d)
              (fun i d => lamDivWeight (G i) x d) : ℝ)) : ℂ) -
            ((((1 : ℝ) / (Wf x : ℝ) : ℝ) : ℂ) *
              (((prefactor Wf (fun _ => 1) x : ℝ) : ℂ) ^ k *
                ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
                  ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ))))‖ ≤
          ε x * ((1 : ℝ) / (Wf x : ℝ)) * prefactor Wf (fun _ => 1) x ^ k := by
  classical
  obtain ⟨x₀s, εs, hεs, hbd⟩ :=
    pairwiseLemma41 hk F G hcsF hsmF hcsG hsmG Wf (fun _ => 1) hW
      (fun _ => one_ne_zero) (fun x => by simp) w hw
      (fun x p hp hle => by simpa using hsmall x p hp hle) (by simpa using hlq)
  obtain ⟨x₀D, hx₀D⟩ := Filter.eventually_atTop.mp hD
  refine ⟨max (max x₀s x₀D) 2, εs, hεs, fun x hx => ?_⟩
  have hxs : x₀s ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxD : x₀D ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : 1 < x := by omega
  have hc0 : (0 : ℝ) ≤ (1 : ℝ) / (Wf x : ℝ) :=
    div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hsum := sum_fin_eq_tsum (D := D x) (W := Wf x) (R := x) F G
    (fun t ht => pairWeightDiv_eq_zero_of_gt F G x (Wf x) hM hx1 (hx₀D x hxD) t ht)
  have hkey : (((goodMainSum (k := k) (D := D x) (N := 1) (W := Wf x)
        (fun i d => lamDivWeight (F i) x d)
        (fun i d => lamDivWeight (G i) x d) : ℝ)) : ℂ) =
      ((((1 : ℝ) / (Wf x : ℝ) : ℝ) : ℂ) *
        (∑' t : Fin k → ℕ × ℕ, pairWeightDiv F G (Wf x) x t)) := by
    rw [goodMainSum_lamDiv_eq_mul_pairwiseSum (W := Wf x) (N := 1) (D := D x)
      (R := x) (hW x) F G, Complex.ofReal_mul]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    rw [hsum]
    congr 1
    push_cast
    ring
  rw [hkey]
  set S : ℂ := ∑' t : Fin k → ℕ × ℕ, pairWeightDiv F G (Wf x) x t with hSdef
  set Mterm : ℂ := ((prefactor Wf (fun _ => 1) x : ℝ) : ℂ) ^ k *
    ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
      ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ)) with hMterm
  have hbd' : ‖S - Mterm‖ ≤ εs x * prefactor Wf (fun _ => 1) x ^ k := by
    rw [hSdef, hMterm]
    simpa using hbd x hxs
  calc ‖(((1 : ℝ) / (Wf x : ℝ) : ℝ) : ℂ) * S -
        (((1 : ℝ) / (Wf x : ℝ) : ℝ) : ℂ) * Mterm‖
      = ‖(((1 : ℝ) / (Wf x : ℝ) : ℝ) : ℂ) * (S - Mterm)‖ := by
        congr 1
        ring
    _ = ‖(((1 : ℝ) / (Wf x : ℝ) : ℝ) : ℂ)‖ * ‖S - Mterm‖ := norm_mul _ _
    _ ≤ ((1 : ℝ) / (Wf x : ℝ)) * (εs x * prefactor Wf (fun _ => 1) x ^ k) := by
        refine mul_le_mul ?_ hbd' (norm_nonneg _) hc0
        rw [norm_ofReal_complex, abs_of_nonneg hc0]
    _ = εs x * ((1 : ℝ) / (Wf x : ℝ)) * prefactor Wf (fun _ => 1) x ^ k := by ring

