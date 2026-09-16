import Mathlib
import Submission.S2Reduction
import Submission.Theorem36i
import Submission.PhiMainSum
import Submission.Commons.NumberTheory.PrimeNumberTheorem.theta_window_shift_powLog_largeN
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_card_divisors_pow_div_totient_le
import Submission.Commons.NumberTheory.ArithmeticFunction.card_lcm_prod_eq_le_of_ne_zero
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_card_divisors_pow_div_totient_le_uniform
import Submission.Commons.NumberTheory.Totient.totient_finset_prod

open scoped BigOperators Topology FourierTransform SchwartzMap
open Filter Finset MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# Polymath8a Theorem 3.5(i): the main term of the θ-weighted window sum

Polymath8a Theorem 3.5 estimates the *prime* (θ-weighted) window sum

    `Σ_{x ≤ n ≤ 2x, n ≡ b (W)} θ(n + h) · ∏_{i} λ_{Fᵢ}(n + hᵢ)λ_{Gᵢ}(n + hᵢ)`
      `= (c + o(1))·B^{1-k}·x/φ(W)`.

After the expansion of the divisor sums (`Submission.S2Expansion`) and the
good/bad split with the CRT collapse of the `S`-set (`Submission.S2Reduction`)
this sum equals `thetaMainSum + thetaDiscSum`, where

* `thetaMainSum` collects the contributions of the *expected* part
  `(1/φ(q))·Σ_{(n+h,q)=1}θ(n+h)` of the class sum, `q = W·∏ᵢ[dᵢ,eᵢ]`;
* `thetaDiscSum` collects the discrepancy parts.

This module evaluates `thetaMainSum`: it proves the totient identity
`1/φ(W·∏ᵢmᵢ) = (1/φ(W))·∏ᵢ1/φ(mᵢ)` on the good divisor pairs, replaces the
θ-mass of the coprime class by `N` using the prime number theorem (with rate),
controls the resulting error by grouping divisor tuples by `∏ᵢ[dᵢ,eᵢ]` (the
divisor bound `τ(M)^{3k}` and `Σ_{M≤Q}τ(M)^{3k}/φ(M) ≪ (log Q)^{2^{3k}}`), and
finally invokes the φ-denominator Lemma 4.1 (`phiGoodMainSum_asymptotic`).

The upshot (`thetaMainSum_asymptotic`) is

    `‖thetaMainSum − (1/φ(W))·N·prefactor^k·∏ᵢ∫₀^∞Fᵢ′Gᵢ′‖ ≤ ε x·(1/φ(W))·N·prefactor^k`,

i.e. the main term of Polymath8a (26).
-/

namespace Commons.NumberTheory.MaynardSieve

attribute [local instance] Classical.propDecidable

/-! ## The θ-mass of the coprime class -/

/-- The θ-mass of the shifted window in the classes coprime to `q`:
`Σ_{N ≤ n ≤ 2N, (n+h, q) = 1} θ(n + h)`. -/
noncomputable def thetaClassSum (N q h : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => (n + h).Coprime q), thetaNat (n + h)

/-- The θ-mass of the coprime class is the θ-mass of the shifted window. -/
lemma thetaClassSum_eq_shifted (N q h : ℕ) :
    thetaClassSum N q h =
      ∑ m ∈ (Finset.Icc (N + h) (2 * N + h)).filter (fun m => m.Coprime q), thetaNat m := by
  refine Finset.sum_bij (fun n _ => n + h) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨by omega, by omega⟩, hn.2⟩
  · intro n₁ hn₁ n₂ hn₂ hh
    omega
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hm2⟩, hmcop⟩ := hm
    have hle : h ≤ m := by omega
    refine ⟨m - h, ?_, by omega⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, by rwa [Nat.sub_add_cancel hle]⟩
  · intro n hn
    rfl

/-- **The prime number theorem in the form used by the sieve**: the θ-mass of the
coprime part of the window is `N` up to `O(N/log^A N)`, uniformly for
`q ≤ N^{1/2}` and shifts `h ≤ N`. -/
theorem thetaClassSum_bound (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ N q h : ℕ, 2 ≤ N → q ≠ 0 →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) → h ≤ N →
      |thetaClassSum N q h - (N : ℝ)| ≤ C * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  obtain ⟨C, hC, hbd⟩ :=
    Commons.NumberTheory.PrimeNumberTheorem.theta_window_shift_powLog_largeN A hA
  refine ⟨C, hC, fun N q h hN hq hqN hh => ?_⟩
  have hsh := thetaClassSum_eq_shifted N q h
  rw [hsh]
  exact hbd N q h hN hq hqN hh

/-! ## The main and discrepancy parts of the θ-weighted expansion -/

/-- The main part of the θ-weighted window expansion: for each good divisor pair,
the coefficient times `(1/φ(q))·(θ-mass in the class coprime to `q`)`, with
`q = W·∏ᵢ[dᵢ,eᵢ]`. -/
noncomputable def thetaMainSum {k : ℕ} (N W h D : ℕ) (α β : Fin k → ℕ → ℝ) : ℝ :=
  ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
    goodInd W d e *
      (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
        ((1 / (((W * ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ)) *
          thetaClassSum N (W * ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i)) h))

/-- The discrepancy part of the θ-weighted window expansion. -/
noncomputable def thetaDiscSum {k : ℕ} (N W b h D : ℕ) (H : Fin k → ℕ)
    (α β : Fin k → ℕ → ℝ) : ℝ :=
  ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
    goodInd W d e *
      (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
        discShift (fun n => thetaNat n) N
          (W * ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ))
          (classResidue N W b h H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))) h)

/-- **The θ-weighted window sum splits into main part and discrepancy part.** -/
theorem thetaWindowProduct_eq_main_add_disc {k D N W b wd : ℕ} {H : Fin k → ℕ} (h : ℕ)
    (α β : Fin k → ℕ → ℝ) (hW2 : 2 ≤ W)
    (hWdiv : ∀ p : ℕ, p.Prime → p ≤ wd → p ∣ W)
    (hHinj : Function.Injective H) (hbW : ∀ i : Fin k, (b + H i).Coprime W)
    (hsep : ∀ i j : Fin k, i ≠ j → H j - H i < wd) :
    (∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => n % W = b % W),
        thetaNat (n + h) * ∏ i : Fin k,
          (∑ d : Fin (D + 1), α i (d : ℕ) * (if (d : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
          (∑ e : Fin (D + 1), β i (e : ℕ) * (if (e : ℕ) ∣ n + H i then (1 : ℝ) else 0))) =
      thetaMainSum (N := N) (W := W) (h := h) (D := D) α β +
        thetaDiscSum (N := N) (W := W) (b := b) (h := h) (D := D) H α β := by
  rw [thetaWindowProduct_decomposition (k := k) (D := D) (N := N) (W := W) (b := b)
    (wd := wd) (H := H) h α β hW2 hWdiv hHinj hbW hsep]
  simp only [thetaMainSum, thetaDiscSum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [thetaClassSum]
  ring

/-! ## The totient identity on good divisor pairs -/

/-- The `Fin k` form of the totient product identity (commons lemma
`Commons.NumberTheory.Totient.totient_finset_prod`). -/
lemma totient_prod_univ {k : ℕ} (m : Fin k → ℕ) (h0 : ∀ i, m i ≠ 0)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j)) :
    (∏ i : Fin k, m i).totient = ∏ i : Fin k, (m i).totient :=
  Commons.NumberTheory.Totient.totient_finset_prod Finset.univ m (fun i _ => h0 i)
    (fun i _ j _ hij => hcop i j hij)

/-- The totient of `W·∏ᵢmᵢ` on a good divisor tuple. -/
lemma totient_mul_prod_univ {k : ℕ} (W : ℕ) (m : Fin k → ℕ)
    (hW : W ≠ 0) (h0 : ∀ i, m i ≠ 0)
    (hcW : ∀ i, (m i).Coprime W) (hcm : ∀ i j, i ≠ j → (m i).Coprime (m j)) :
    ((W * ∏ i, m i).totient : ℝ) = (W.totient : ℝ) * ∏ i, ((m i).totient : ℝ) := by
  have hcW' : W.Coprime (∏ i, m i) := Nat.Coprime.prod_right fun i _ => (hcW i).symm
  rw [Nat.totient_mul hcW', totient_prod_univ m h0 hcm]
  push_cast
  ring

/-- The reciprocal form of the totient identity on a good divisor tuple. -/
lemma inv_totient_mul_prod_univ {k : ℕ} (W : ℕ) (m : Fin k → ℕ)
    (hW : W ≠ 0) (h0 : ∀ i, m i ≠ 0)
    (hcW : ∀ i, (m i).Coprime W) (hcm : ∀ i j, i ≠ j → (m i).Coprime (m j)) :
    (1 : ℝ) / (((W * ∏ i, m i).totient : ℕ) : ℝ) =
      (1 / ((W.totient : ℕ) : ℝ)) * ∏ i, (1 / (((m i).totient : ℕ) : ℝ)) := by
  have h1 := totient_mul_prod_univ W m hW h0 hcW hcm
  have hWφ : ((W.totient : ℕ) : ℝ) ≠ 0 := by
    have h : 0 < W.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hW)
    exact_mod_cast h.ne'
  have hφ : ∀ i : Fin k, (((m i).totient : ℕ) : ℝ) ≠ 0 := fun i => by
    have h : 0 < (m i).totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (h0 i))
    exact_mod_cast h.ne'
  have hprod : (∏ i : Fin k, (((m i).totient : ℕ) : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hφ i)
  rw [Finset.prod_div_distrib, Finset.prod_const_one]
  simp only [one_div]
  rw [h1]
  field_simp


/-! ## The φ-denominator weights -/

/-- The φ-denominator pairwise weight of a divisor pair:
`goodInd · ∏ᵢ μ(dᵢ)μ(eᵢ)Fᵢ(log dᵢ)Gᵢ(log eᵢ) / φ([dᵢ,eᵢ])`. -/
noncomputable def phiPairWeight {k D : ℕ} (F G : Fin k → ℝ → ℝ) (N W : ℕ)
    (d e : Fin k → Fin (D + 1)) : ℝ :=
  goodInd W d e * ∏ i : Fin k,
    (lamDivWeight (F i) N (d i : ℕ) * lamDivWeight (G i) N (e i : ℕ) /
      (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ))

/-- The box sum of the φ-denominator pairwise weights — the object evaluated by
the φ-denominator Lemma 4.1. -/
noncomputable def phiBoxSum {k D : ℕ} (F G : Fin k → ℝ → ℝ) (N W : ℕ) : ℝ :=
  ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)), phiPairWeight F G N W d e

/-- The `φ`-error term: the φ-weights times the deviation of the θ-mass of the
coprime class from `N`. -/
noncomputable def thetaErrSum {k D : ℕ} (F G : Fin k → ℝ → ℝ) (N W h : ℕ) : ℝ :=
  ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
    phiPairWeight F G N W d e *
      (thetaClassSum N (W * ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ)) h - (N : ℝ))

/-- **Step A.**  On the good divisor pairs the totient identity
`1/φ(W·∏ᵢmᵢ) = (1/φ(W))·∏ᵢ1/φ(mᵢ)` rewrites the main part of the θ-weighted
expansion in terms of the φ-denominator weights. -/
lemma thetaMainSum_eq_inv_totient_mul {k D N W h : ℕ} (F G : Fin k → ℝ → ℝ)
    (hW : W ≠ 0) (hW2 : 2 ≤ W) :
    thetaMainSum (N := N) (W := W) (h := h) (D := D)
        (α := fun i => lamDivWeight (F i) N) (β := fun i => lamDivWeight (G i) N) =
      (1 / ((W.totient : ℕ) : ℝ)) *
        ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
          phiPairWeight F G N W d e *
            thetaClassSum N (W * ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ)) h := by
  simp only [thetaMainSum, phiPairWeight, coefProd]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hg : lcmGood W d e
  · have hgl : lcmGood W d e := hg
    obtain ⟨hcW, hcm⟩ := hgl
    have hm0 : ∀ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) ≠ 0 := by
      intro i hzero
      have hc := hcW i
      rw [hzero] at hc
      simp [Nat.Coprime] at hc
      omega
    have hkey := inv_totient_mul_prod_univ W (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) hW hm0 hcW hcm
    have hdiv : (∏ i : Fin k, (lamDivWeight (F i) N (d i : ℕ) * lamDivWeight (G i) N (e i : ℕ) /
          (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ))) =
        (∏ i : Fin k, (lamDivWeight (F i) N (d i : ℕ) * lamDivWeight (G i) N (e i : ℕ))) *
          ∏ i : Fin k, (1 / (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ)) := by
      rw [Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_const_one]
      ring
    rw [goodInd, if_pos hg, one_mul, hkey, hdiv]
    ring
  · rw [goodInd, if_neg hg]
    ring

/-- **Step B.**  Splitting the θ-mass of the coprime class as `N + (…−N)` gives
the main part `N·phiBoxSum` plus the error `thetaErrSum`. -/
lemma sum_phiWeight_classSum_eq {k D N W h : ℕ} (F G : Fin k → ℝ → ℝ) :
    (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
        phiPairWeight F G N W d e *
          thetaClassSum N (W * ∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ)) h) =
      (N : ℝ) * phiBoxSum (D := D) F G N W + thetaErrSum (D := D) F G N W h := by
  simp only [phiBoxSum, thetaErrSum]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- **The φ-denominator box sum at the sieve's modulus family.**  This is the
asymptotic of the φ-denominator Lemma 4.1, transported to `phiBoxSum`. -/
theorem phiBoxSum_asymptotic {k : ℕ} (hk : 1 ≤ k)
    (F G : Fin k → ℝ → ℝ) (hcsF : ∀ i, HasCompactSupport (F i))
    (hsmF : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (F i)) (hcsG : ∀ i, HasCompactSupport (G i))
    (hsmG : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (G i))
    (Wf : ℕ → ℕ) (hW : ∀ x, Wf x ≠ 0)
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ Wf x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log ((Wf x : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ))) atTop (𝓝 0))
    {M : ℝ} (hM : ∀ i : Fin k, ∀ t : ℝ, M < |t| → F i t = 0 ∧ G i t = 0)
    (D : ℕ → ℕ) (hD : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ M ≤ (D x : ℝ)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x →
        ‖((phiBoxSum (D := D x) F G x (Wf x) : ℝ) : ℂ) -
            (((prefactor Wf (fun _ => 1) x : ℝ) : ℂ) ^ k *
                ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
                  ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ)))‖ ≤
          ε x * prefactor Wf (fun _ => 1) x ^ k := by
  obtain ⟨x₀, ε, hε, hbd⟩ :=
    phiGoodMainSum_asymptotic hk F G hcsF hsmF hcsG hsmG Wf hW w hw hsmall hlq hM D hD
  refine ⟨x₀, ε, hε, fun x hx => ?_⟩
  have h := hbd x hx
  simp only [phiBoxSum, phiPairWeight] at h ⊢
  push_cast at h ⊢
  exact h


/-! ## The divisor-tuple counting bound

The error introduced by replacing the θ-mass of the coprime class by `N` is
controlled by grouping divisor pairs by `M = ∏ᵢ[dᵢ,eᵢ]`: the fibre of `M`
contains at most `τ(M)^{3k}` pairs, and `Σ_{M ≤ Q}τ(M)^{3k}/φ(M) ≪ (log Q)^{2^{3k}}`.
-/

/-- The `Fin k` totient product identity in the form used below. -/
private lemma totient_prod_eq {k : ℕ} (m : Fin k → ℕ) (h0 : ∀ i, m i ≠ 0)
    (hcop : ∀ i j, i ≠ j → (m i).Coprime (m j)) :
    (∏ i : Fin k, ((m i).totient : ℕ)) = (∏ i : Fin k, m i).totient :=
  (totient_prod_univ m h0 hcop).symm

/-- **Fibre count.**  The number of good divisor pairs with `∏ᵢ[dᵢ,eᵢ] = M ≠ 0`
is at most `τ(M)^{2k} ≤ τ(M)^{3k}`: each coordinate is a divisor of `M`, so the
map into `Fin k → M.divisors × M.divisors` is injective. -/
private lemma card_goodFiber_le {k D W M : ℕ} (hM : M ≠ 0) :
    ((Finset.univ : Finset ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)))).filter
      (fun p : (Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)) => lcmGood W p.1 p.2 ∧
        (∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) = M)).card
    ≤ (M.divisors.card) ^ (3 * k) := by
  classical
  set F0 : Finset ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1))) :=
    (Finset.univ : Finset ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)))).filter (fun p : (Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)) => lcmGood W p.1 p.2 ∧
      (∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) = M) with hF0
  have hmem : ∀ p ∈ F0, (∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) = M ∧
      lcmGood W p.1 p.2 := by
    intro p hp
    rw [hF0, Finset.mem_filter] at hp
    exact ⟨hp.2.2, hp.2.1⟩
  have hdvd : ∀ p ∈ F0, ∀ i : Fin k,
      (p.1 i : ℕ) ∣ M ∧ (p.2 i : ℕ) ∣ M := by
    intro p hp i
    obtain ⟨hpM, _⟩ := hmem p hp
    have hlcm : Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ) ∣ M := by
      rw [← hpM]
      exact Finset.dvd_prod_of_mem
        (fun j : Fin k => Nat.lcm (p.1 j : ℕ) (p.2 j : ℕ)) (Finset.mem_univ i)
    exact ⟨Nat.dvd_trans (Nat.dvd_lcm_left _ _) hlcm,
      Nat.dvd_trans (Nat.dvd_lcm_right _ _) hlcm⟩
  let g : ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1))) →
      (Fin k → M.divisors × M.divisors) := fun p i =>
    if h : (p.1 i : ℕ) ∣ M ∧ (p.2 i : ℕ) ∣ M then
      (⟨(p.1 i : ℕ), Nat.mem_divisors.mpr ⟨h.1, hM⟩⟩,
       ⟨(p.2 i : ℕ), Nat.mem_divisors.mpr ⟨h.2, hM⟩⟩)
    else (⟨1, Nat.mem_divisors.mpr ⟨one_dvd M, hM⟩⟩,
          ⟨1, Nat.mem_divisors.mpr ⟨one_dvd M, hM⟩⟩)
  have hgval1 : ∀ p ∈ F0, ∀ i, ((g p i).1 : ℕ) = (p.1 i : ℕ) := by
    intro p hp i
    have hd := hdvd p hp i
    simp only [g]
    rw [dif_pos hd]
  have hgval2 : ∀ p ∈ F0, ∀ i, ((g p i).2 : ℕ) = (p.2 i : ℕ) := by
    intro p hp i
    have hd := hdvd p hp i
    simp only [g]
    rw [dif_pos hd]
  have hginj : Set.InjOn g ↑F0 := by
    intro p hp q hq hpq
    have h1 : p.1 = q.1 := by
      funext i
      have h2 : ((g p i).1 : ℕ) = ((g q i).1 : ℕ) := by rw [hpq]
      rw [hgval1 p hp i, hgval1 q hq i] at h2
      exact Fin.ext h2
    have h2 : p.2 = q.2 := by
      funext i
      have h3 : ((g p i).2 : ℕ) = ((g q i).2 : ℕ) := by rw [hpq]
      rw [hgval2 p hp i, hgval2 q hq i] at h3
      exact Fin.ext h3
    exact Prod.ext h1 h2
  have hcard : F0.card ≤ (Finset.univ : Finset (Fin k → M.divisors × M.divisors)).card :=
    Finset.card_le_card_of_injOn g (fun p _ => Finset.mem_univ _) hginj
  have hτpos : 0 < M.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hM⟩
  calc F0.card ≤ (Finset.univ : Finset (Fin k → M.divisors × M.divisors)).card := hcard
    _ = ((M.divisors.card) ^ 2) ^ k := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_coe, sq]
    _ = (M.divisors.card) ^ (2 * k) := by rw [← pow_mul]
    _ ≤ (M.divisors.card) ^ (3 * k) :=
        Nat.pow_le_pow_right hτpos (by omega)

/-- **Counting bound.**  For `2 ≤ W`, the sum of the dominating weights
`∏ᵢ 1/φ([dᵢ,eᵢ])` over the good divisor pairs with `∏ᵢ[dᵢ,eᵢ] ≤ Q` is
`O((log Q)^{2^{3k}})`. -/
theorem sum_phiDomWeight_le {k D Q W : ℕ} (hW : 2 ≤ W) {C : ℝ}
    (hCb : (∑ M ∈ Finset.Icc 1 Q,
        ((M.divisors.card : ℝ)) ^ (3 * k) / (M.totient : ℝ))
      ≤ C * (Real.log (Q : ℝ) + 1) ^ (2 ^ (3 * k))) :
    (∑ p ∈ (Finset.univ : Finset ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)))).filter
        (fun p : (Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)) => lcmGood W p.1 p.2 ∧
          (∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) ≤ Q),
      ∏ i : Fin k, (1 / (((Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)).totient : ℕ) : ℝ)))
    ≤ C * (Real.log (Q : ℝ) + 1) ^ (2 ^ (3 * k)) := by
  classical
  set T : Finset ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1))) :=
    (Finset.univ : Finset ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)))).filter
      (fun p : (Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)) => lcmGood W p.1 p.2 ∧
        (∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) ≤ Q) with hT
  set Mp : ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1))) → ℕ :=
    fun p => ∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ) with hMp
  have hmaps : ∀ p ∈ T, Mp p ∈ Finset.Icc 1 Q := by
    intro p hp
    rw [hT, Finset.mem_filter] at hp
    obtain ⟨_, hgood, hle⟩ := hp
    rw [Finset.mem_Icc]
    have hm0 : ∀ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ) ≠ 0 := by
      intro i hzero
      have hc := hgood.1 i
      rw [hzero] at hc
      simp [Nat.Coprime] at hc
      omega
    exact ⟨Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (hm0 i), hle⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p : (Fin k → Fin (D + 1)) ×
    (Fin k → Fin (D + 1)) =>
      ∏ i : Fin k, (1 / (((Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)).totient : ℕ) : ℝ)))]
  refine le_trans (Finset.sum_le_sum fun M' hM' => ?_) hCb
  rw [Finset.mem_Icc] at hM'
  have hM'ne : M' ≠ 0 := by omega
  have hconst : ∀ p ∈ T.filter (fun p => Mp p = M'),
      (∏ i : Fin k, (1 / (((Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)).totient : ℕ) : ℝ))) =
        1 / ((M'.totient : ℕ) : ℝ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpT, hpM⟩ := hp
    rw [hT, Finset.mem_filter] at hpT
    obtain ⟨_, hgood, _⟩ := hpT
    have hpM' : (∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) = M' := hpM
    have hm0 : ∀ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ) ≠ 0 := by
      intro i hzero
      have hc := hgood.1 i
      rw [hzero] at hc
      simp [Nat.Coprime] at hc
      omega
    have htotN : (∏ i : Fin k, ((Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)).totient : ℕ)) = M'.totient := by
      rw [totient_prod_eq (fun i => Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) hm0 hgood.2, hpM']
    have htotR : (∏ i : Fin k, (((Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)).totient : ℕ) : ℝ)) =
        ((M'.totient : ℕ) : ℝ) := by
      rw [← Nat.cast_prod, htotN]
    calc (∏ i : Fin k, (1 / (((Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)).totient : ℕ) : ℝ)))
        = 1 / ∏ i : Fin k, (((Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)).totient : ℕ) : ℝ) := by
          rw [Finset.prod_div_distrib, Finset.prod_const_one]
      _ = 1 / ((M'.totient : ℕ) : ℝ) := by rw [htotR]
  have hfiber : ((T.filter (fun p => Mp p = M')).card : ℝ) ≤
      (((M'.divisors.card) ^ (3 * k) : ℕ) : ℝ) := by
    have hsub : T.filter (fun p => Mp p = M') ⊆
        (Finset.univ : Finset ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)))).filter
          (fun p : (Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)) => lcmGood W p.1 p.2 ∧
            (∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) = M') := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpT, hpM⟩ := hp
      rw [hT, Finset.mem_filter] at hpT
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpT.2.1, hpM⟩
    have := le_trans (Finset.card_le_card hsub)
      (card_goodFiber_le (D := D) (W := W) (M := M') hM'ne)
    exact_mod_cast this
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hphi : (0 : ℝ) < ((M'.totient : ℕ) : ℝ) := by
    have h : 0 < M'.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hM'ne)
    exact_mod_cast h
  calc ((T.filter (fun p => Mp p = M')).card : ℝ) * (1 / ((M'.totient : ℕ) : ℝ))
      ≤ (((M'.divisors.card) ^ (3 * k) : ℕ) : ℝ) * (1 / ((M'.totient : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hfiber (by positivity)
    _ = ((M'.divisors.card : ℝ) ^ (3 * k)) / ((M'.totient : ℕ) : ℝ) := by
        rw [Nat.cast_pow]; ring
/-! ## Support restriction, weight bounds and the φ-error bound -/

/-- **Support restriction.**  If the coefficient of a divisor pair does not
vanish, then `∏ᵢ[dᵢ,eᵢ] ≤ N^{Σᵢ(Mfᵢ+Mgᵢ)}`: every coordinate lies in the
support of the corresponding cutoff. -/
lemma lcm_prod_le_of_coefProd_ne_zero {k D : ℕ} (F G : Fin k → ℝ → ℝ) (N : ℕ)
    (hN : 1 < N) {Mf Mg : Fin k → ℝ}
    (hMf : ∀ (i : Fin k) (t : ℝ), Mf i < |t| → F i t = 0)
    (hMg : ∀ (i : Fin k) (t : ℝ), Mg i < |t| → G i t = 0)
    {ϑ Q : ℝ} (hsum : ∑ i, (Mf i + Mg i) ≤ ϑ) (hQ : (N : ℝ) ^ ϑ ≤ Q)
    {d e : Fin k → Fin (D + 1)}
    (hne : coefProd (fun i => lamDivWeight (F i) N) (fun i => lamDivWeight (G i) N)
        (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) ≠ 0) :
    ((∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) : ℕ) : ℝ) ≤ Q := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNr : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hfac := Finset.prod_ne_zero_iff.mp (by simpa only [coefProd] using hne)
  have hne0 : ∀ i : Fin k, (d i : ℕ) ≠ 0 ∧ (e i : ℕ) ≠ 0 := by
    intro i
    have hi := hfac i (Finset.mem_univ i)
    exact ⟨fun h0 => (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hi).1).1 (by simp [moebiusReal, h0]),
      fun h0 => (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hi).2).1 (by simp [moebiusReal, h0])⟩
  have hcoord : ∀ i : Fin k,
      ((d i : ℕ) : ℝ) ≤ (N : ℝ) ^ (Mf i) ∧ ((e i : ℕ) : ℝ) ≤ (N : ℝ) ^ (Mg i) := by
    intro i
    have hi := hfac i (Finset.mem_univ i)
    have h1 : lamDivWeight (F i) N (d i : ℕ) ≠ 0 := (mul_ne_zero_iff.mp hi).1
    have h2 : lamDivWeight (G i) N (e i : ℕ) ≠ 0 := (mul_ne_zero_iff.mp hi).2
    have hd0 : (d i : ℕ) ≠ 0 := (hne0 i).1
    have he0 : (e i : ℕ) ≠ 0 := (hne0 i).2
    constructor
    · have hF : F i (logR (d i : ℕ) N) ≠ 0 := (mul_ne_zero_iff.mp h1).2
      have hlog : logR (d i : ℕ) N ≤ Mf i := by
        by_contra hc
        push_neg at hc
        exact hF (hMf i _ (lt_of_lt_of_le hc (le_abs_self _)))
      exact le_rpow_of_logR_le hN hd0 hlog
    · have hG : G i (logR (e i : ℕ) N) ≠ 0 := (mul_ne_zero_iff.mp h2).2
      have hlog : logR (e i : ℕ) N ≤ Mg i := by
        by_contra hc
        push_neg at hc
        exact hG (hMg i _ (lt_of_lt_of_le hc (le_abs_self _)))
      exact le_rpow_of_logR_le hN he0 hlog
  calc ((∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) : ℕ) : ℝ)
      = ∏ i : Fin k, ((Nat.lcm (d i : ℕ) (e i : ℕ) : ℕ) : ℝ) := Nat.cast_prod _ _
    _ ≤ ∏ i : Fin k, (((d i : ℕ) : ℝ) * ((e i : ℕ) : ℝ)) := by
        refine Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => ?_)
        exact_mod_cast Nat.lcm_le_mul (Nat.pos_of_ne_zero (hne0 i).1) (Nat.pos_of_ne_zero (hne0 i).2)
    _ = (∏ i : Fin k, ((d i : ℕ) : ℝ)) * ∏ i : Fin k, ((e i : ℕ) : ℝ) :=
        Finset.prod_mul_distrib
    _ ≤ (∏ i : Fin k, (N : ℝ) ^ (Mf i)) * ∏ i : Fin k, (N : ℝ) ^ (Mg i) := by
        have h1 : (∏ i : Fin k, ((d i : ℕ) : ℝ)) ≤ ∏ i : Fin k, (N : ℝ) ^ (Mf i) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => (hcoord i).1)
        have h2 : (∏ i : Fin k, ((e i : ℕ) : ℝ)) ≤ ∏ i : Fin k, (N : ℝ) ^ (Mg i) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => (hcoord i).2)
        have h3 : (0 : ℝ) ≤ ∏ i : Fin k, ((e i : ℕ) : ℝ) := by positivity
        have h4 : (0 : ℝ) ≤ ∏ i : Fin k, (N : ℝ) ^ (Mf i) :=
          Finset.prod_nonneg fun i _ => Real.rpow_nonneg hNpos.le _
        exact mul_le_mul h1 h2 h3 h4
    _ = (N : ℝ) ^ (∑ i : Fin k, Mf i) * (N : ℝ) ^ (∑ i : Fin k, Mg i) := by
        rw [Real.rpow_sum_of_pos hNpos, Real.rpow_sum_of_pos hNpos]
    _ = (N : ℝ) ^ (∑ i : Fin k, Mf i + ∑ i : Fin k, Mg i) := by
        rw [Real.rpow_add hNpos]
    _ ≤ (N : ℝ) ^ ϑ := by
        apply (Real.rpow_le_rpow_left_iff hNr).mpr
        rw [← Finset.sum_add_distrib]
        exact hsum
    _ ≤ Q := hQ

/-- **Dominating weight bound.**  The φ-pair weight is bounded by
`∏ᵢ‖Fᵢ‖‖Gᵢ‖·∏ᵢ1/φ([dᵢ,eᵢ])`. -/
lemma abs_phiPairWeight_le {k D : ℕ} (F G : Fin k → ℝ → ℝ) (N W : ℕ) {BF BG : ℝ}
    (hBF : 0 ≤ BF) (hBG : 0 ≤ BG)
    (hF : ∀ (i : Fin k) (t : ℝ), |F i t| ≤ BF) (hG : ∀ (i : Fin k) (t : ℝ), |G i t| ≤ BG)
    (d e : Fin k → Fin (D + 1)) :
    |phiPairWeight F G N W d e| ≤ BF ^ k * BG ^ k *
      ∏ i : Fin k, (1 / (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ)) := by
  classical
  have hgi : |goodInd W d e| ≤ 1 := by
    by_cases h : lcmGood W d e <;> simp [goodInd, h]
  have hterm : ∀ i : Fin k,
      |lamDivWeight (F i) N (d i : ℕ) * lamDivWeight (G i) N (e i : ℕ) /
        (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ)| ≤
      BF * BG * (1 / (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ)) := by
    intro i
    have hL : |lamDivWeight (F i) N (d i : ℕ)| ≤ BF := by
      simp only [lamDivWeight, logR, abs_mul]
      calc |moebiusReal ↑(d i)| * |F i (Real.log ↑(d i) / Real.log ↑N)| ≤ 1 * BF :=
            mul_le_mul (abs_moebiusReal_le_one _) (hF i _) (abs_nonneg _) (by norm_num)
        _ = BF := one_mul BF
    have hR : |lamDivWeight (G i) N (e i : ℕ)| ≤ BG := by
      simp only [lamDivWeight, logR, abs_mul]
      calc |moebiusReal ↑(e i)| * |G i (Real.log ↑(e i) / Real.log ↑N)| ≤ 1 * BG :=
            mul_le_mul (abs_moebiusReal_le_one _) (hG i _) (abs_nonneg _) (by norm_num)
        _ = BG := one_mul BG
    rw [abs_div, abs_mul]
    by_cases h0 : (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ) = 0
    · simp [h0]
    · have hpos : 0 < (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ) :=
        lt_of_le_of_ne (by positivity) (Ne.symm h0)
      rw [abs_of_pos hpos]
      calc |lamDivWeight (F i) N (d i : ℕ)| * |lamDivWeight (G i) N (e i : ℕ)| /
            (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ)
          ≤ BF * BG / (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right (mul_le_mul hL hR (abs_nonneg _) hBF) hpos.le
        _ = BF * BG * (1 / (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ)) := by
            rw [div_eq_mul_inv, one_div]
  have hinner : |∏ i : Fin k, (lamDivWeight (F i) N (d i : ℕ) * lamDivWeight (G i) N (e i : ℕ) /
      (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ))| ≤
      ∏ i : Fin k, (BF * BG * (1 / (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ))) := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hterm i)
  have hnn : 0 ≤ ∏ i : Fin k, (BF * BG * (1 / (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ))) :=
    Finset.prod_nonneg fun i _ => mul_nonneg (mul_nonneg hBF hBG) (by positivity)
  rw [phiPairWeight, abs_mul]
  calc |goodInd W d e| * |∏ i : Fin k, (lamDivWeight (F i) N (d i : ℕ) *
        lamDivWeight (G i) N (e i : ℕ) / (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ))|
      ≤ 1 * ∏ i : Fin k,
          (BF * BG * (1 / (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ))) :=
        mul_le_mul hgi hinner (abs_nonneg _) (by norm_num)
    _ = BF ^ k * BG ^ k *
        ∏ i : Fin k, (1 / (((Nat.lcm (d i : ℕ) (e i : ℕ)).totient : ℕ) : ℝ)) := by
        rw [one_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, mul_pow]

/-- **The φ-error bound.**  If the θ-mass of the coprime class equals `N` up to
`κ` for every modulus `q ≤ W·Q`, and every contributing divisor pair has
`∏ᵢ[dᵢ,eᵢ] ≤ Q`, then the error term is
`O(κ·(log Q)^{2^{3k}}·∏ᵢ‖Fᵢ‖‖Gᵢ‖)`. -/
theorem abs_thetaErrSum_le {k D : ℕ} (F G : Fin k → ℝ → ℝ) (N W h : ℕ) {BF BG κ : ℝ}
    (hW : 2 ≤ W) (hBF : 0 ≤ BF) (hBG : 0 ≤ BG) (hκ : 0 ≤ κ)
    (hFbd : ∀ (i : Fin k) (t : ℝ), |F i t| ≤ BF) (hGbd : ∀ (i : Fin k) (t : ℝ), |G i t| ≤ BG)
    {Q : ℕ} {C : ℝ}
    (hCb : (∑ M ∈ Finset.Icc 1 Q,
        ((M.divisors.card : ℝ)) ^ (3 * k) / (M.totient : ℝ))
      ≤ C * (Real.log (Q : ℝ) + 1) ^ (2 ^ (3 * k)))
    (hQ : ∀ d e : Fin k → Fin (D + 1),
        coefProd (fun i => lamDivWeight (F i) N) (fun i => lamDivWeight (G i) N)
          (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) ≠ 0 →
        (∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ)) ≤ Q)
    (hclass : ∀ q : ℕ, q ≠ 0 → q ≤ W * Q → |thetaClassSum N q h - (N : ℝ)| ≤ κ) :
    |thetaErrSum (D := D) F G N W h| ≤
      κ * (BF ^ k * BG ^ k) * C * (Real.log (Q : ℝ) + 1) ^ (2 ^ (3 * k)) := by
  classical
  set T : Finset ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1))) :=
    (Finset.univ : Finset ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)))).filter
      (fun p : (Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)) => lcmGood W p.1 p.2 ∧
        (∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) ≤ Q) with hT
  have hTmem : ∀ p : (Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)),
      p ∈ T ↔ lcmGood W p.1 p.2 ∧ (∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) ≤ Q := by
    intro p
    rw [hT, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hterm : ∀ p : (Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)),
      |phiPairWeight F G N W p.1 p.2| *
        |thetaClassSum N (W * ∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) h - (N : ℝ)| ≤
      (if lcmGood W p.1 p.2 ∧ (∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) ≤ Q
        then κ * |phiPairWeight F G N W p.1 p.2| else 0) := by
    intro p
    by_cases hp : lcmGood W p.1 p.2 ∧ (∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) ≤ Q
    · rw [if_pos hp]
      obtain ⟨hgood, hprod⟩ := hp
      have hq : W * (∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) ≤ W * Q :=
        Nat.mul_le_mul_left W hprod
      have hlcm0 : ∀ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ) ≠ 0 := by
        intro i hzero
        have hc := hgood.1 i
        rw [hzero] at hc
        simp [Nat.Coprime] at hc
        omega
      have hqne : W * (∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) ≠ 0 :=
        Nat.mul_ne_zero (by omega)
          (Finset.prod_ne_zero_iff.mpr fun i _ => hlcm0 i)
      have hcl := hclass _ hqne hq
      calc |phiPairWeight F G N W p.1 p.2| *
            |thetaClassSum N (W * ∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) h - (N : ℝ)|
          ≤ |phiPairWeight F G N W p.1 p.2| * κ :=
            mul_le_mul_of_nonneg_left hcl (abs_nonneg _)
        _ = κ * |phiPairWeight F G N W p.1 p.2| := by ring
    · rw [if_neg hp]
      by_cases hg : lcmGood W p.1 p.2
      · have hgt : Q < ∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ) :=
          lt_of_not_ge fun hle => hp ⟨hg, hle⟩
        have hcoef : coefProd (fun i => lamDivWeight (F i) N) (fun i => lamDivWeight (G i) N)
            (fun i => (p.1 i : ℕ)) (fun i => (p.2 i : ℕ)) = 0 := by
          by_contra hne
          exact absurd (hQ p.1 p.2 hne) (not_le.mpr hgt)
        have hzero : (∏ i : Fin k, (lamDivWeight (F i) N (p.1 i : ℕ) *
            lamDivWeight (G i) N (p.2 i : ℕ) /
            (((Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)).totient : ℕ) : ℝ))) = 0 := by
          rw [Finset.prod_div_distrib,
            show (∏ i : Fin k, (lamDivWeight (F i) N (p.1 i : ℕ) *
                lamDivWeight (G i) N (p.2 i : ℕ))) =
              coefProd (fun i => lamDivWeight (F i) N) (fun i => lamDivWeight (G i) N)
                (fun i => (p.1 i : ℕ)) (fun i => (p.2 i : ℕ)) from rfl, hcoef, zero_div]
        rw [phiPairWeight, hzero, mul_zero, abs_zero, zero_mul]
      · simp only [phiPairWeight, goodInd, if_neg hg, zero_mul, abs_zero, zero_mul, le_refl]
  have hstep1 : |thetaErrSum (D := D) F G N W h| ≤
      ∑ p : (Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)),
        |phiPairWeight F G N W p.1 p.2| *
          |thetaClassSum N (W * ∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) h - (N : ℝ)| := by
    simp only [thetaErrSum]
    rw [← Fintype.sum_prod_type (f := fun p :
      (Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)) =>
        phiPairWeight F G N W p.1 p.2 *
          (thetaClassSum N (W * ∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) h - (N : ℝ)))]
    exact le_of_le_of_eq
      (Finset.abs_sum_le_sum_abs (fun p : (Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)) =>
        phiPairWeight F G N W p.1 p.2 *
          (thetaClassSum N (W * ∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) h - (N : ℝ)))
        Finset.univ)
      (Finset.sum_congr rfl fun p _ => abs_mul _ _)
  have hstep2 : (∑ p : (Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)),
        |phiPairWeight F G N W p.1 p.2| *
          |thetaClassSum N (W * ∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) h - (N : ℝ)|) ≤
      ∑ p : (Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)),
        (if lcmGood W p.1 p.2 ∧ (∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) ≤ Q
          then κ * |phiPairWeight F G N W p.1 p.2| else 0) :=
    Finset.sum_le_sum (s := (Finset.univ : Finset
      ((Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1))))) fun p _ => hterm p
  have hstep3 : (∑ p : (Fin k → Fin (D + 1)) × (Fin k → Fin (D + 1)),
        (if lcmGood W p.1 p.2 ∧ (∏ i : Fin k, Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)) ≤ Q
          then κ * |phiPairWeight F G N W p.1 p.2| else 0)) =
      κ * ∑ p ∈ T, |phiPairWeight F G N W p.1 p.2| := by
    rw [Finset.mul_sum, hT, ← Finset.sum_filter]
  have hstep4 : (∑ p ∈ T, |phiPairWeight F G N W p.1 p.2|) ≤
      (BF ^ k * BG ^ k) * ∑ p ∈ T,
        ∏ i : Fin k, (1 / (((Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)).totient : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ =>
      abs_phiPairWeight_le F G N W hBF hBG hFbd hGbd p.1 p.2
  have hstep5 : (∑ p ∈ T,
        ∏ i : Fin k, (1 / (((Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)).totient : ℕ) : ℝ)))
      ≤ C * (Real.log (Q : ℝ) + 1) ^ (2 ^ (3 * k)) :=
    sum_phiDomWeight_le (k := k) (D := D) (Q := Q) (W := W) hW hCb
  calc |thetaErrSum (D := D) F G N W h|
      ≤ _ := hstep1
    _ ≤ _ := hstep2
    _ = κ * ∑ p ∈ T, |phiPairWeight F G N W p.1 p.2| := hstep3
    _ ≤ κ * ((BF ^ k * BG ^ k) * ∑ p ∈ T,
          ∏ i : Fin k, (1 / (((Nat.lcm (p.1 i : ℕ) (p.2 i : ℕ)).totient : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hstep4 hκ
    _ ≤ κ * ((BF ^ k * BG ^ k) * (C * (Real.log (Q : ℝ) + 1) ^ (2 ^ (3 * k)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hstep5 (by positivity)) hκ
    _ = κ * (BF ^ k * BG ^ k) * C * (Real.log (Q : ℝ) + 1) ^ (2 ^ (3 * k)) := by ring

/-! ## The main term of Polymath8a Theorem 3.5(i) -/

/-- `√(log x) ≤ c·log x` eventually, for every `c > 0`. -/
private lemma eventually_sqrt_log_le_mul_log {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, Real.sqrt (Real.log (x : ℝ)) ≤ c * Real.log (x : ℝ) := by
  have h1 : ∀ᶠ x : ℕ in atTop, 1 / c ^ 2 ≤ Real.log (x : ℝ) :=
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop (1 / c ^ 2))
  refine h1.mono fun x hx => ?_
  have hy : 0 < Real.log (x : ℝ) := lt_of_lt_of_le (by positivity) hx
  have hsqrt : 0 ≤ Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_nonneg _
  have h1c : 1 / c ≤ Real.sqrt (Real.log (x : ℝ)) := by
    calc 1 / c = Real.sqrt ((1 / c) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Real.log (x : ℝ)) :=
          Real.sqrt_le_sqrt (by rw [div_pow, one_pow]; exact hx)
  have h2 : 1 ≤ c * Real.sqrt (Real.log (x : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left h1c hc.le
    rwa [mul_one_div_cancel (ne_of_gt hc)] at hmul
  calc Real.sqrt (Real.log (x : ℝ)) = 1 * Real.sqrt (Real.log (x : ℝ)) := (one_mul _).symm
    _ ≤ (c * Real.sqrt (Real.log (x : ℝ))) * Real.sqrt (Real.log (x : ℝ)) :=
        mul_le_mul_of_nonneg_right h2 hsqrt
    _ = c * (Real.sqrt (Real.log (x : ℝ)) * Real.sqrt (Real.log (x : ℝ))) := by ring
    _ = c * Real.log (x : ℝ) := by rw [← sq, Real.sq_sqrt hy.le]

/-- `log (W x) ≤ c·log x` eventually, for every `c > 0`, under the hypothesis
`log W = o(√(log x))` of the sieve. -/
private lemma eventually_log_le_mul_log {W : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hlq : Tendsto (fun x : ℕ =>
      Real.log ((W x : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ))) atTop (𝓝 0)) :
    ∀ᶠ x : ℕ in atTop, Real.log ((W x : ℕ) : ℝ) ≤ c * Real.log (x : ℝ) := by
  have h1 : ∀ᶠ x : ℕ in atTop,
      Real.log ((W x : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)) < 1 :=
    (tendsto_order.1 hlq).2 1 zero_lt_one
  have h2 : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.sqrt (Real.log (x : ℝ)) := by
    refine (tendsto_log_nat_atTop.eventually (eventually_ge_atTop (1 : ℝ))).mono ?_
    intro x hx
    rw [Real.one_le_sqrt]
    exact hx
  have h3 := eventually_sqrt_log_le_mul_log hc
  refine (h1.and (h2.and h3)).mono fun x hx => ?_
  obtain ⟨h1x, h2x, h3x⟩ := hx
  have hsq : 0 < Real.sqrt (Real.log (x : ℝ)) := lt_of_lt_of_le zero_lt_one h2x
  have key : Real.log ((W x : ℕ) : ℝ) = Real.sqrt (Real.log (x : ℝ)) *
      (Real.log ((W x : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ))) := by
    rw [mul_div_cancel₀ _ (ne_of_gt hsq)]
  rw [key]
  calc Real.sqrt (Real.log (x : ℝ)) *
        (Real.log ((W x : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      ≤ Real.sqrt (Real.log (x : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left h1x.le (Real.sqrt_nonneg _)
    _ = Real.sqrt (Real.log (x : ℝ)) := mul_one _
    _ ≤ c * Real.log (x : ℝ) := h3x

/-- `W x ≤ x^c` eventually, for every `c > 0`. -/
private lemma eventually_le_rpow_of_log_ratio {W : ℕ → ℕ} (hW : ∀ x, W x ≠ 0) {c : ℝ}
    (hc : 0 < c)
    (hlq : Tendsto (fun x : ℕ =>
      Real.log ((W x : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ))) atTop (𝓝 0)) :
    ∀ᶠ x : ℕ in atTop, ((W x : ℕ) : ℝ) ≤ (x : ℝ) ^ c := by
  have h := eventually_log_le_mul_log (W := W) hc hlq
  refine (h.and (eventually_ge_atTop 2)).mono fun x hx => ?_
  obtain ⟨hlog, hx2⟩ := hx
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hWpos : (0 : ℝ) < ((W x : ℕ) : ℝ) := by
    have := Nat.pos_of_ne_zero (hW x)
    exact_mod_cast this
  calc ((W x : ℕ) : ℝ) = Real.exp (Real.log ((W x : ℕ) : ℝ)) :=
        (Real.exp_log hWpos).symm
    _ ≤ Real.exp (c * Real.log (x : ℝ)) := Real.exp_le_exp.mpr hlog
    _ = (x : ℝ) ^ c := by rw [Real.rpow_def_of_pos (by linarith)]; ring_nf

/-- `2·x^a ≤ x^b` eventually, for `a < b`. -/
private lemma eventually_two_mul_rpow_le {a b : ℝ} (hab : a < b) :
    ∀ᶠ x : ℕ in atTop, 2 * (x : ℝ) ^ a ≤ (x : ℝ) ^ b := by
  have hb : 0 < b - a := by linarith
  have hlim : Tendsto (fun x : ℕ => (x : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop
  refine (hlim.eventually (eventually_ge_atTop 2)).mono fun x hx => ?_
  have hxne : (x : ℝ) ≠ 0 := by
    intro h0
    rw [h0, Real.zero_rpow (ne_of_gt hb)] at hx
    norm_num at hx
  have hxpos : (0 : ℝ) < x := lt_of_le_of_ne (by positivity) (Ne.symm hxne)
  calc 2 * (x : ℝ) ^ a ≤ (x : ℝ) ^ (b - a) * (x : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg (by positivity) _)
    _ = (x : ℝ) ^ (b - a + a) := (Real.rpow_add hxpos _ _).symm
    _ = (x : ℝ) ^ b := by rw [show b - a + a = b by ring]

/-- **Polymath8a Theorem 3.5(i), main term.**  For a modulus family `Wf` with
`log Wf = o(√(log x))` and every prime `≤ w x → ∞` dividing `Wf x`, for smooth
compactly supported `F, G : Fin k → ℝ → ℝ` whose support radii satisfy
`Σᵢ(Mfᵢ + Mgᵢ) < ϑ < 1/2`, the main part of the θ-weighted window sum satisfies

    `thetaMainSum = (1/φ(W))·x·prefactor^k·∏ᵢ∫₀^∞Fᵢ′Gᵢ′`

up to a relative error `ε x → 0`. -/
theorem thetaMainSum_asymptotic {k : ℕ} (hk : 1 ≤ k)
    (F G : Fin k → ℝ → ℝ) (hcsF : ∀ i, HasCompactSupport (F i))
    (hsmF : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (F i)) (hcsG : ∀ i, HasCompactSupport (G i))
    (hsmG : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (G i))
    (Wf : ℕ → ℕ) (hW : ∀ x, Wf x ≠ 0)
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ Wf x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log ((Wf x : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ))) atTop (𝓝 0))
    {BF BG : ℝ} (hBF : 0 ≤ BF) (hBG : 0 ≤ BG)
    (hFbd : ∀ (i : Fin k) (t : ℝ), |F i t| ≤ BF)
    (hGbd : ∀ (i : Fin k) (t : ℝ), |G i t| ≤ BG)
    {M : ℝ} (hM : ∀ i : Fin k, ∀ t : ℝ, M < |t| → F i t = 0 ∧ G i t = 0)
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ2 : ϑ < 1 / 2) {Mf Mg : Fin k → ℝ}
    (hMf : ∀ (i : Fin k) (t : ℝ), Mf i < |t| → F i t = 0)
    (hMg : ∀ (i : Fin k) (t : ℝ), Mg i < |t| → G i t = 0)
    (hsum : ∑ i : Fin k, (Mf i + Mg i) < ϑ)
    (h : ℕ)
    {Cdiv : ℝ} (hCdiv : 0 < Cdiv)
    (hdiv : ∀ Q : ℕ, (∑ M ∈ Finset.Icc 1 Q,
        ((M.divisors.card : ℝ)) ^ (3 * k) / (M.totient : ℝ))
      ≤ Cdiv * (Real.log (Q : ℝ) + 1) ^ (2 ^ (3 * k)))
    (D : ℕ → ℕ) (hDM : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ M ≤ (D x : ℝ))
    (hDϑ : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ ϑ ≤ (D x : ℝ)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ x : ℕ, x₀ ≤ x →
      |thetaMainSum (N := x) (W := Wf x) (h := h) (D := D x)
          (α := fun i => lamDivWeight (F i) x) (β := fun i => lamDivWeight (G i) x) -
        (1 / ((Wf x).totient : ℝ)) * (x : ℝ) * (prefactor Wf (fun _ => 1) x) ^ k *
          ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0, deriv (F j) t * deriv (G j) t)| ≤
      ε x * ((1 / ((Wf x).totient : ℝ)) * (x : ℝ) * (prefactor Wf (fun _ => 1) x) ^ k) := by
  classical
  classical
  obtain ⟨x₁, ε₁, hε₁, hb₁⟩ :=
    phiBoxSum_asymptotic hk F G hcsF hsmF hcsG hsmG Wf hW w hw hsmall hlq hM D hDM
  set n : ℕ := 2 ^ (3 * k) with hndef
  set A : ℝ := (n : ℝ) + (k : ℝ) + 1 with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  obtain ⟨Cp, hCp, hpnt⟩ := thetaClassSum_bound A hApos
  set c : ℝ := (1 / 2 - ϑ) / 2 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; linarith
  have hcϑ : c + ϑ < 1 / 2 := by rw [hcdef]; linarith
  have hWgr : ∀ᶠ x : ℕ in atTop, ((Wf x : ℕ) : ℝ) ≤ (x : ℝ) ^ c :=
    eventually_le_rpow_of_log_ratio hW hcpos hlq
  have hW2 : ∀ᶠ x : ℕ in atTop, 2 ≤ Wf x := by
    refine (hw.eventually (eventually_ge_atTop 2)).mono fun x hx => ?_
    obtain ⟨m, hm⟩ := hsmall x 2 Nat.prime_two hx
    have hpos : 0 < Wf x := Nat.pos_of_ne_zero (hW x)
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, mul_zero] at hm; omega
      · exact h0
    omega
  have hQle : ∀ᶠ x : ℕ in atTop, ((Nat.ceil ((x : ℝ) ^ ϑ) : ℕ) : ℝ) ≤ 2 * (x : ℝ) ^ ϑ := by
    refine (eventually_ge_atTop 1).mono fun x hx1 => ?_
    have hx1' : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    have h1ϑ : (1 : ℝ) ≤ (x : ℝ) ^ ϑ := Real.one_le_rpow hx1' hϑ0.le
    have hlt := Nat.ceil_lt_add_one
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (x : ℝ)) ϑ)
    have : ((Nat.ceil ((x : ℝ) ^ ϑ) : ℕ) : ℝ) < (x : ℝ) ^ ϑ + 1 := hlt
    linarith
  have hQx : ∀ᶠ x : ℕ in atTop, ((Nat.ceil ((x : ℝ) ^ ϑ) : ℕ) : ℝ) ≤ (x : ℝ) := by
    have hδ : 0 < 1 - ϑ := by linarith
    have hlim : Tendsto (fun x : ℕ => (x : ℝ) ^ (1 - ϑ)) atTop atTop :=
      (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
    refine (hlim.eventually (eventually_ge_atTop 2)).mono fun x hx => ?_
    have hx1' : (1 : ℝ) ≤ (x : ℝ) := by
      rcases Nat.eq_zero_or_pos x with h0 | h0
      · rw [h0] at hx
        simp only [Nat.cast_zero, Real.zero_rpow (ne_of_gt hδ)] at hx
        norm_num at hx
      · exact_mod_cast h0
    have hxp : (x : ℝ) ^ (1 - ϑ) ≤ (x : ℝ) := by
      rcases lt_or_eq_of_le hx1' with h1 | h1
      · calc (x : ℝ) ^ (1 - ϑ) ≤ (x : ℝ) ^ (1 : ℝ) :=
              (Real.rpow_le_rpow_left_iff h1).mpr (by linarith)
          _ = (x : ℝ) := Real.rpow_one _
      · simp [h1.symm]
    have hxge : (2 : ℝ) ≤ (x : ℝ) := le_trans hx hxp
    have hx1'' : (1 : ℝ) < (x : ℝ) := by linarith
    have hxϑle : (x : ℝ) ^ ϑ ≤ (x : ℝ) := by
      calc (x : ℝ) ^ ϑ ≤ (x : ℝ) ^ (1 : ℝ) :=
            (Real.rpow_le_rpow_left_iff hx1'').mpr (by linarith)
        _ = (x : ℝ) := Real.rpow_one _
    exact_mod_cast Nat.ceil_le.mpr hxϑle
  have hqbound : ∀ᶠ x : ℕ in atTop,
      (Wf x : ℝ) * ((Nat.ceil ((x : ℝ) ^ ϑ) : ℕ) : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) := by
    refine (hWgr.and (hQle.and (eventually_two_mul_rpow_le hcϑ))).mono fun x hx => ?_
    obtain ⟨h1, h2, h3⟩ := hx
    have hxpos : (0 : ℝ) < x := by
      by_contra h
      push_neg at h
      have hx0 : x = 0 := by
        rcases Nat.eq_zero_or_pos x with h0 | h0
        · exact h0
        · exfalso
          have : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h0
          linarith
      subst hx0
      simp only [Nat.cast_zero, Real.zero_rpow (ne_of_gt hcpos)] at h1
      have : (1 : ℝ) ≤ (Wf 0 : ℝ) := by
        have := Nat.pos_of_ne_zero (hW 0)
        exact_mod_cast this
      linarith
    calc (Wf x : ℝ) * ((Nat.ceil ((x : ℝ) ^ ϑ) : ℕ) : ℝ)
        ≤ (x : ℝ) ^ c * (2 * (x : ℝ) ^ ϑ) :=
          mul_le_mul h1 h2 (by positivity) (Real.rpow_nonneg hxpos.le _)
      _ = 2 * (x : ℝ) ^ (c + ϑ) := by
          rw [Real.rpow_add hxpos]; ring
      _ ≤ (x : ℝ) ^ (1 / 2 : ℝ) := h3
  have hlogx : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hle : ∀ᶠ x : ℕ in atTop,
      Real.log (((Nat.ceil ((x : ℝ) ^ ϑ) : ℕ)) : ℝ) + 1 ≤ 2 * Real.log (x : ℝ) := by
    refine (hQx.and (hlogx.and (eventually_ge_atTop 1))).mono fun x hx => ?_
    obtain ⟨h1, h2, h3⟩ := hx
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have hQpos : (0 : ℝ) < ((Nat.ceil ((x : ℝ) ^ ϑ) : ℕ) : ℝ) := by
      have hle0 := Nat.le_ceil ((x : ℝ) ^ ϑ)
      have hx1' : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h3
      have h1ϑ : (1 : ℝ) ≤ (x : ℝ) ^ ϑ := Real.one_le_rpow hx1' hϑ0.le
      have h2' : (1 : ℝ) ≤ ((Nat.ceil ((x : ℝ) ^ ϑ) : ℕ) : ℝ) := le_trans h1ϑ hle0
      linarith
    have hlog := Real.log_le_log hQpos h1
    linarith
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp
    (hDM.and (hDϑ.and (hW2.and (hqbound.and ((eventually_ge_atTop (h + 1)).and
      ((eventually_ge_atTop 2).and (hlogx.and hle)))))))
  refine ⟨max x₀ x₁, fun x =>
      ε₁ x + Cp * ((BF ^ k * BG ^ k) * Cdiv * (2 : ℝ) ^ n) * (Real.log (x : ℝ))⁻¹, ?_, ?_⟩
  · have hinv : Tendsto (fun x : ℕ => (Real.log (x : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_log_nat_atTop
    have h2 : Tendsto (fun x : ℕ =>
        Cp * ((BF ^ k * BG ^ k) * Cdiv * (2 : ℝ) ^ n) * (Real.log (x : ℝ))⁻¹)
        atTop (𝓝 (Cp * ((BF ^ k * BG ^ k) * Cdiv * (2 : ℝ) ^ n) * 0)) :=
      hinv.const_mul _
    simpa using hε₁.add h2
  · intro x hx
    obtain ⟨hxa, hxb⟩ : x₀ ≤ x ∧ x₁ ≤ x :=
      ⟨le_trans (le_max_left _ _) hx, le_trans (le_max_right _ _) hx⟩
    obtain ⟨hDMx, hDϑx, hW2x, hqbx, hhx, hx2, hlogx1, hlex⟩ := hx₀ x hxa
    have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hlogx1
    set Q : ℕ := Nat.ceil ((x : ℝ) ^ ϑ) with hQdef
    have hQle' : (x : ℝ) ^ ϑ ≤ (Q : ℝ) := Nat.le_ceil _
    have hdivev : (∑ M ∈ Finset.Icc 1 Q,
        ((M.divisors.card : ℝ)) ^ (3 * k) / (M.totient : ℝ))
        ≤ Cdiv * (Real.log (Q : ℝ) + 1) ^ (2 ^ (3 * k)) := hdiv Q
    have hQbound : ∀ d e : Fin k → Fin (D x + 1),
        coefProd (fun i => lamDivWeight (F i) x) (fun i => lamDivWeight (G i) x)
          (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) ≠ 0 →
        (∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ)) ≤ Q := by
      intro d e hne
      have hreal : ((∏ i : Fin k, Nat.lcm (d i : ℕ) (e i : ℕ) : ℕ) : ℝ) ≤ (Q : ℝ) :=
        lcm_prod_le_of_coefProd_ne_zero (D := D x) F G x (by omega) hMf hMg
          hsum.le hQle' hne
      exact_mod_cast hreal
    have hclass : ∀ q : ℕ, q ≠ 0 → q ≤ Wf x * Q →
        |thetaClassSum x q h - (x : ℝ)| ≤ Cp * (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
      intro q hq hqQ
      refine hpnt x q h hx2 hq ?_ (by omega)
      have h1 : (q : ℝ) ≤ (Wf x : ℝ) * (Q : ℝ) := by exact_mod_cast hqQ
      have h2 : (Wf x : ℝ) * (Q : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) := by
        rw [hQdef]; exact hqbx
      linarith
    have hκnn : (0 : ℝ) ≤ Cp * (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
      have h1 : (0 : ℝ) < (Real.log (x : ℝ)) ^ A := Real.rpow_pos_of_pos hLpos A
      exact div_nonneg (by positivity) h1.le
    have hE0 := abs_thetaErrSum_le (D := D x)
      (κ := Cp * (x : ℝ) / (Real.log (x : ℝ)) ^ A) F G x (Wf x) h hW2x hBF hBG hκnn
      hFbd hGbd hdivev hQbound hclass
    have hLQnn : 0 ≤ Real.log (Q : ℝ) + 1 := by
      have hq1 : (1 : ℝ) ≤ (Q : ℝ) := by
        have hle0 := Nat.le_ceil ((x : ℝ) ^ ϑ)
        have hx1' : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
        have h1ϑ : (1 : ℝ) ≤ (x : ℝ) ^ ϑ := Real.one_le_rpow hx1' hϑ0.le
        exact le_trans h1ϑ hle0
      linarith [Real.log_nonneg hq1]
    have hpow : (Real.log (Q : ℝ) + 1) ^ n ≤ (2 : ℝ) ^ n * (Real.log (x : ℝ)) ^ n := by
      have h2 : Real.log (Q : ℝ) + 1 ≤ 2 * Real.log (x : ℝ) := by
        rw [hQdef] at hlex; exact hlex
      calc (Real.log (Q : ℝ) + 1) ^ n ≤ (2 * Real.log (x : ℝ)) ^ n :=
            pow_le_pow_left₀ hLQnn h2 n
        _ = (2 : ℝ) ^ n * (Real.log (x : ℝ)) ^ n := mul_pow _ _ _
    have hkey : (Real.log (x : ℝ)) ^ (-A) * (Real.log (Q : ℝ) + 1) ^ n ≤
        (2 : ℝ) ^ n * (Real.log (x : ℝ)) ^ (-(k : ℝ) - 1) := by
      calc (Real.log (x : ℝ)) ^ (-A) * (Real.log (Q : ℝ) + 1) ^ n
          ≤ (Real.log (x : ℝ)) ^ (-A) * ((2 : ℝ) ^ n * (Real.log (x : ℝ)) ^ n) :=
            mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hLpos.le _)
        _ = (2 : ℝ) ^ n * ((Real.log (x : ℝ)) ^ (-A) * (Real.log (x : ℝ)) ^ ((n : ℕ) : ℝ)) := by
            rw [Real.rpow_natCast]; ring
        _ = (2 : ℝ) ^ n * (Real.log (x : ℝ)) ^ (-A + (n : ℝ)) := by
            rw [← Real.rpow_add hLpos]
        _ = (2 : ℝ) ^ n * (Real.log (x : ℝ)) ^ (-(k : ℝ) - 1) := by
            congr 2
            rw [hAdef]; push_cast; ring
    have hpref : (Real.log (x : ℝ))⁻¹ ≤ prefactor Wf (fun _ => 1) x :=
      inv_log_le_prefactor_one (hW x) hx2
    have hprefk : ((Real.log (x : ℝ))⁻¹) ^ k ≤ (prefactor Wf (fun _ => 1) x) ^ k :=
      pow_le_pow_left₀ (by positivity) hpref k
    have hLk : ((Real.log (x : ℝ))⁻¹) ^ k = (Real.log (x : ℝ)) ^ (-(k : ℝ)) := by
      rw [inv_pow, ← Real.rpow_natCast (Real.log (x : ℝ)) k, ← Real.rpow_neg hLpos.le]
    have hkey' : (Real.log (x : ℝ)) ^ (-A) * (Real.log (Q : ℝ) + 1) ^ n ≤
        (2 : ℝ) ^ n * (Real.log (x : ℝ))⁻¹ * (prefactor Wf (fun _ => 1) x) ^ k := by
      have hsplit : (Real.log (x : ℝ)) ^ (-(k : ℝ) - 1) =
          (Real.log (x : ℝ))⁻¹ * (Real.log (x : ℝ)) ^ (-(k : ℝ)) := by
        rw [← Real.rpow_neg_one (Real.log (x : ℝ)), ← Real.rpow_add hLpos]
        congr 1
        ring
      have hstep : (Real.log (x : ℝ)) ^ (-(k : ℝ)) ≤
          (prefactor Wf (fun _ => 1) x) ^ k := by
        rw [← hLk]; exact hprefk
      calc (Real.log (x : ℝ)) ^ (-A) * (Real.log (Q : ℝ) + 1) ^ n
          ≤ (2 : ℝ) ^ n * (Real.log (x : ℝ)) ^ (-(k : ℝ) - 1) := hkey
        _ = (2 : ℝ) ^ n * ((Real.log (x : ℝ))⁻¹ * (Real.log (x : ℝ)) ^ (-(k : ℝ))) := by
            rw [hsplit]
        _ ≤ (2 : ℝ) ^ n * ((Real.log (x : ℝ))⁻¹ * (prefactor Wf (fun _ => 1) x) ^ k) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hstep (by positivity)) (by positivity)
        _ = (2 : ℝ) ^ n * (Real.log (x : ℝ))⁻¹ * (prefactor Wf (fun _ => 1) x) ^ k := by ring
    have hmain : Cp * (x : ℝ) / (Real.log (x : ℝ)) ^ A * (BF ^ k * BG ^ k) * Cdiv *
          (Real.log (Q : ℝ) + 1) ^ n
        ≤ Cp * ((BF ^ k * BG ^ k) * Cdiv * (2 : ℝ) ^ n) * (Real.log (x : ℝ))⁻¹ *
          (x : ℝ) * (prefactor Wf (fun _ => 1) x) ^ k := by
      have hCn : (0 : ℝ) ≤ Cp * ((BF ^ k * BG ^ k) * Cdiv) * (x : ℝ) := by positivity
      calc Cp * (x : ℝ) / (Real.log (x : ℝ)) ^ A * (BF ^ k * BG ^ k) * Cdiv *
            (Real.log (Q : ℝ) + 1) ^ n
          = Cp * ((BF ^ k * BG ^ k) * Cdiv) * (x : ℝ) *
              ((Real.log (x : ℝ)) ^ (-A) * (Real.log (Q : ℝ) + 1) ^ n) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg hLpos.le]; ring
        _ ≤ Cp * ((BF ^ k * BG ^ k) * Cdiv) * (x : ℝ) *
              ((2 : ℝ) ^ n * (Real.log (x : ℝ))⁻¹ * (prefactor Wf (fun _ => 1) x) ^ k) :=
            mul_le_mul_of_nonneg_left hkey' hCn
        _ = Cp * ((BF ^ k * BG ^ k) * Cdiv * (2 : ℝ) ^ n) * (Real.log (x : ℝ))⁻¹ *
              (x : ℝ) * (prefactor Wf (fun _ => 1) x) ^ k := by ring
    have hE : |thetaErrSum (D := D x) F G x (Wf x) h| ≤
        Cp * ((BF ^ k * BG ^ k) * Cdiv * (2 : ℝ) ^ n) * (Real.log (x : ℝ))⁻¹ *
          (x : ℝ) * (prefactor Wf (fun _ => 1) x) ^ k := by
      rw [← hndef] at hE0
      exact le_trans hE0 hmain
    have hP : |phiBoxSum (D := D x) F G x (Wf x) -
        prefactor Wf (fun _ => 1) x ^ k *
          ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0, deriv (F j) t * deriv (G j) t)| ≤
        ε₁ x * prefactor Wf (fun _ => 1) x ^ k := by
      have hc := hb₁ x hxb
      have hcast : (((phiBoxSum (D := D x) F G x (Wf x) -
              prefactor Wf (fun _ => 1) x ^ k *
                ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
                  deriv (F j) t * deriv (G j) t)) : ℝ) : ℂ)
          = ((phiBoxSum (D := D x) F G x (Wf x) : ℝ) : ℂ) -
            (((prefactor Wf (fun _ => 1) x : ℝ)) : ℂ) ^ k *
              ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
                ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ)) := by
        rw [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_prod]
        congr 2
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [show (∫ t : ℝ in Set.Ioi 0,
              ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ))
            = ∫ t : ℝ in Set.Ioi 0,
              (((deriv (F j) t) * (deriv (G j) t) : ℝ) : ℂ) from
          integral_congr_ae (Eventually.of_forall fun t => (Complex.ofReal_mul _ _).symm)]
        exact (integral_ofReal (μ := volume.restrict (Set.Ioi 0))
          (f := fun t : ℝ => (deriv (F j) t) * (deriv (G j) t))).symm
      rw [← hcast, norm_ofReal_complex] at hc
      exact hc
    have hinner : |(x : ℝ) * (phiBoxSum (D := D x) F G x (Wf x) -
              prefactor Wf (fun _ => 1) x ^ k *
                ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0, deriv (F j) t * deriv (G j) t)) +
            thetaErrSum (D := D x) F G x (Wf x) h|
        ≤ (x : ℝ) * (ε₁ x * prefactor Wf (fun _ => 1) x ^ k) +
          Cp * ((BF ^ k * BG ^ k) * Cdiv * (2 : ℝ) ^ n) * (Real.log (x : ℝ))⁻¹ *
            (x : ℝ) * (prefactor Wf (fun _ => 1) x) ^ k := by
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x)]
      exact add_le_add (mul_le_mul_of_nonneg_left hP (by positivity)) hE
    have hφpos : 0 < 1 / ((Wf x).totient : ℝ) := by
      have h : 0 < (Wf x).totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hW x))
      have h2 : (0 : ℝ) < ((Wf x).totient : ℝ) := by exact_mod_cast h
      positivity
    have hstep1 : thetaMainSum (N := x) (W := Wf x) (h := h) (D := D x)
        (α := fun i => lamDivWeight (F i) x) (β := fun i => lamDivWeight (G i) x) =
        (1 / ((Wf x).totient : ℝ)) * ((x : ℝ) * phiBoxSum (D := D x) F G x (Wf x) +
          thetaErrSum (D := D x) F G x (Wf x) h) := by
      rw [thetaMainSum_eq_inv_totient_mul (D := D x) (N := x) (W := Wf x) (h := h) F G
          (hW x) hW2x,
        sum_phiWeight_classSum_eq (D := D x) (N := x) (W := Wf x) (h := h) F G]
    rw [hstep1]
    have hsplit : (1 / ((Wf x).totient : ℝ)) *
          ((x : ℝ) * phiBoxSum (D := D x) F G x (Wf x) +
            thetaErrSum (D := D x) F G x (Wf x) h) -
        (1 / ((Wf x).totient : ℝ)) * (x : ℝ) * (prefactor Wf (fun _ => 1) x) ^ k *
          ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0, deriv (F j) t * deriv (G j) t) =
        (1 / ((Wf x).totient : ℝ)) *
          ((x : ℝ) * (phiBoxSum (D := D x) F G x (Wf x) -
              prefactor Wf (fun _ => 1) x ^ k *
                ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0, deriv (F j) t * deriv (G j) t)) +
            thetaErrSum (D := D x) F G x (Wf x) h) := by ring
    rw [hsplit, abs_mul, abs_of_nonneg hφpos.le]
    calc (1 / ((Wf x).totient : ℝ)) *
          |(x : ℝ) * (phiBoxSum (D := D x) F G x (Wf x) -
              prefactor Wf (fun _ => 1) x ^ k *
                ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0, deriv (F j) t * deriv (G j) t)) +
            thetaErrSum (D := D x) F G x (Wf x) h|
        ≤ (1 / ((Wf x).totient : ℝ)) *
            ((x : ℝ) * (ε₁ x * prefactor Wf (fun _ => 1) x ^ k) +
              Cp * ((BF ^ k * BG ^ k) * Cdiv * (2 : ℝ) ^ n) * (Real.log (x : ℝ))⁻¹ *
                (x : ℝ) * (prefactor Wf (fun _ => 1) x) ^ k) :=
          mul_le_mul_of_nonneg_left hinner hφpos.le
      _ = (ε₁ x + Cp * ((BF ^ k * BG ^ k) * Cdiv * (2 : ℝ) ^ n) *
              (Real.log (x : ℝ))⁻¹) *
            ((1 / ((Wf x).totient : ℝ)) * (x : ℝ) *
              (prefactor Wf (fun _ => 1) x) ^ k) := by ring

/-- **Polymath8a Theorem 3.5(i), main term — hypothesis-free form.**  Identical
to `thetaMainSum_asymptotic` with the uniform divisor-sum bound
`Σ_{M≤Q}τ(M)^{3k}/φ(M) ≪ (log Q)^{2^{3k}}` supplied by the commons lemma
`Commons.NumberTheory.ArithmeticFunction.sum_card_divisors_pow_div_totient_le_uniform`. -/
theorem thetaMainSum_asymptotic_unconditional {k : ℕ} (hk : 1 ≤ k)
    (F G : Fin k → ℝ → ℝ) (hcsF : ∀ i, HasCompactSupport (F i))
    (hsmF : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (F i)) (hcsG : ∀ i, HasCompactSupport (G i))
    (hsmG : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (G i))
    (Wf : ℕ → ℕ) (hW : ∀ x, Wf x ≠ 0)
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ Wf x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log ((Wf x : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ))) atTop (𝓝 0))
    {BF BG : ℝ} (hBF : 0 ≤ BF) (hBG : 0 ≤ BG)
    (hFbd : ∀ (i : Fin k) (t : ℝ), |F i t| ≤ BF)
    (hGbd : ∀ (i : Fin k) (t : ℝ), |G i t| ≤ BG)
    {M : ℝ} (hM : ∀ i : Fin k, ∀ t : ℝ, M < |t| → F i t = 0 ∧ G i t = 0)
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ2 : ϑ < 1 / 2) {Mf Mg : Fin k → ℝ}
    (hMf : ∀ (i : Fin k) (t : ℝ), Mf i < |t| → F i t = 0)
    (hMg : ∀ (i : Fin k) (t : ℝ), Mg i < |t| → G i t = 0)
    (hsum : ∑ i : Fin k, (Mf i + Mg i) < ϑ)
    (h : ℕ)
    (D : ℕ → ℕ) (hDM : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ M ≤ (D x : ℝ))
    (hDϑ : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ ϑ ≤ (D x : ℝ)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ x : ℕ, x₀ ≤ x →
      |thetaMainSum (N := x) (W := Wf x) (h := h) (D := D x)
          (α := fun i => lamDivWeight (F i) x) (β := fun i => lamDivWeight (G i) x) -
        (1 / ((Wf x).totient : ℝ)) * (x : ℝ) * (prefactor Wf (fun _ => 1) x) ^ k *
          ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0, deriv (F j) t * deriv (G j) t)| ≤
      ε x * ((1 / ((Wf x).totient : ℝ)) * (x : ℝ) * (prefactor Wf (fun _ => 1) x) ^ k) := by
  obtain ⟨C, hC, hCb⟩ :=
    Commons.NumberTheory.ArithmeticFunction.sum_card_divisors_pow_div_totient_le_uniform k
  exact thetaMainSum_asymptotic hk F G hcsF hsmF hcsG hsmG Wf hW w hw hsmall hlq
    hBF hBG hFbd hGbd hM hϑ0 hϑ2 hMf hMg hsum h hC hCb D hDM hDϑ

end Commons.NumberTheory.MaynardSieve
