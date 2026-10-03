/-
# The sharp `\xi`-derivative bound for the symbol difference `M_0` of the §6 model approximation

This file proves `Work.A7.ModelApproxCore_M0_deriv_bound`: for the `(\xi_1,\xi_2)`-derivatives
`M0deriv P N q \alpha_1 \alpha_2 \xi_1 \xi_2 j_1 j_2` (`j_1,j_2 \le 2`) of the symbol difference
`M_0 = E_{n\in[N]} e(\alpha_1n+\alpha_2P(n)) e(\xi_1n+\xi_2P(n)) 1_{n>N/2} - m_{\hat Z} \tilde m_{N,\mathbb R}`
of Proposition `mod-approx` of Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional
bilinear polynomial averages*, Ann. of Math. **195** (3) 2022,

`\|M0deriv\| \le C q^2 (1 + (2^{k_1}+2^{d k_2})^2/N) N^{j_1 + d j_2 - 1}`,

where `d = P.natDegree` and `q` is a period of the arithmetic characters (`q \bullet \alpha_1 =
q \bullet \alpha_2 = 0`).  This is the *sharp* form of the paper's estimate: the paper's
`2^{O(\max(2^{\rho l}, s))} N^{-1}` carries a factor `2^{O(s)}`, `s = \max(k_1,k_2)`, which the weight
`modelWeight A \rho l_1 l_2 k_1 k_2 = \langle L\rangle^A 2^{A 2^{\rho L}}` of the model
approximation cannot absorb; the estimate proved here has no such factor (see
`NOTES_A7_ModelApproxCore.md`, §2.1--2.2).

## The argument

Write `V = m0w P \xi_1 \xi_2 j_1 j_2` (`M0WBasic`), the common weight of the discrete summand
`momPhaseDeriv` and of the integrand of `mTildeDeriv`.  Then
`M0deriv = N^{-1} (\sum_{N/2<n\le N} \mathrm{arithW}(n) V(n)) - m_{\hat Z} \int_{1/2}^1 V(Nt) dt`
(`momPhaseDeriv_eq_arithW_m0w`, `mTildeDeriv_eq_integral_m0w`), and

* `sum_arithW_fiber` regroups the discrete sum by the residue class of `n` modulo `q`, turning it
  into `\sum_{a<q} \mathrm{arithW}(a) \sum_{n\equiv a} V(n)`, while `m_{\hat Z} = q^{-1}\sum_{a<q}
  \mathrm{arithW}(a)` is its average;
* `fiber_stepQ_trapezoid` compares each residue-class sum with `q^{-1}\int` (a step-`q` Euler--
  Maclaurin comparison, obtained from `ModelApproxCore_trapezoid` by rescaling), at the cost
  `3 B + (q/8)\int\|V''\|` where `B` bounds `\|V\|`;
* `m0w_bound` supplies `B = C_0 N^{j_1+d j_2}` and `\|V''\| \le C_0 N^{j_1+dj_2-2}(1+S+S^2)`,
  `S = 2^{k_1}+2^{d k_2}`;
* `rpow_absorb` performs the final elementary absorption of the `4qN^{E-1}` and the
  `(q^2/8)N^{E-2}(1+S+S^2)` terms into `5q^2(1+S^2/N)N^{E-1}`.

The `N^{-1}` and the `q^2` are exactly the losses of the single-scale model approximation; no
factor `2^{O(k_1+k_2)}` is lost.
-/
import Mathlib
import Submission.Work.A7.fiber_stepQ_trapezoid
import Submission.Work.A7.sum_arithW_fiber
import Submission.Work.A7.m0w_bound
import Submission.Work.A7.rpow_absorb


set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.A7

open MeasureTheory Polynomial Finset Topology
open scoped BigOperators

noncomputable section

private lemma sum_fiber_algebra (f s : ℕ → ℂ) (c w : ℂ) (q : ℕ) :
    (∑ a ∈ Finset.range q, f a * s a) - c * (∑ a ∈ Finset.range q, f a) * w
      = ∑ a ∈ Finset.range q, f a * (s a - c * w) := by
  have h1 : (∑ a ∈ Finset.range q, f a * (s a - c * w))
      = ∑ a ∈ Finset.range q, (f a * s a - f a * (c * w)) :=
    Finset.sum_congr rfl (fun a _ => mul_sub (f a) (s a) (c * w))
  have h2 : (∑ a ∈ Finset.range q, f a * (c * w)) = c * (∑ a ∈ Finset.range q, f a) * w := by
    rw [← Finset.sum_mul]; ring
  rw [h1, Finset.sum_sub_distrib, h2]

private lemma arith_step {C₀ Nrad B B₂ Int2 Srad : ℝ} {q E : ℕ}
    (hC₀ : 0 < C₀) (hN : 1 ≤ Nrad) (hq : 1 ≤ q) (hS : 0 ≤ Srad)
    (hB : B = C₀ * Nrad ^ ((E : ℕ) : ℝ))
    (hB₂ : B₂ = C₀ * Nrad ^ (((E : ℕ) : ℝ) - 2) * (1 + Srad + Srad ^ 2))
    (hInt2 : Int2 ≤ Nrad * B₂) :
    Nrad⁻¹ * ((q : ℝ) * (3 * B + ((q : ℝ) / 8) * Int2) + B)
      ≤ 5 * C₀ * (q : ℝ) ^ 2 * (1 + Srad ^ 2 / Nrad) * Nrad ^ (((E : ℕ) : ℝ) - 1) := by
  have hNpos : (0 : ℝ) < Nrad := lt_of_lt_of_le one_pos hN
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hE1 : 0 < Nrad ^ (((E : ℕ) : ℝ) - 1) := Real.rpow_pos_of_pos hNpos _
  have hE2 : 0 < Nrad ^ (((E : ℕ) : ℝ) - 2) := Real.rpow_pos_of_pos hNpos _
  have hEE : 0 < Nrad ^ ((E : ℕ) : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hSc : (0 : ℝ) ≤ 1 + Srad + Srad ^ 2 := by nlinarith
  have hNE : Nrad * Nrad ^ (((E : ℕ) : ℝ) - 1) = Nrad ^ ((E : ℕ) : ℝ) := by
    have h1 : Nrad * Nrad ^ (((E : ℕ) : ℝ) - 1)
        = Nrad ^ (((E : ℕ) : ℝ) - 1) * Nrad ^ (1 : ℝ) := by rw [Real.rpow_one]; ring
    rw [h1, ← Real.rpow_add hNpos]; congr 1; ring
  have hNE2 : Nrad * Nrad ^ (((E : ℕ) : ℝ) - 2) = Nrad ^ (((E : ℕ) : ℝ) - 1) := by
    have h1 : Nrad * Nrad ^ (((E : ℕ) : ℝ) - 2)
        = Nrad ^ (((E : ℕ) : ℝ) - 2) * Nrad ^ (1 : ℝ) := by rw [Real.rpow_one]; ring
    rw [h1, ← Real.rpow_add hNpos]; congr 1; ring
  have hkey : Nrad⁻¹ * ((q : ℝ) * (3 * B + ((q : ℝ) / 8) * Int2) + B)
      ≤ C₀ * (4 * (q : ℝ) * Nrad ^ (((E : ℕ) : ℝ) - 1)
          + ((q : ℝ) ^ 2 / 8) * Nrad ^ (((E : ℕ) : ℝ) - 2) * (1 + Srad + Srad ^ 2)) := by
    rw [hB, hB₂] at *
    have hA : (q : ℝ) * (3 * (C₀ * Nrad ^ ((E : ℕ) : ℝ))) + C₀ * Nrad ^ ((E : ℕ) : ℝ)
        ≤ Nrad * (C₀ * (4 * (q : ℝ) * Nrad ^ (((E : ℕ) : ℝ) - 1))) := by
      have h1 : (q : ℝ) * (3 * (C₀ * Nrad ^ ((E : ℕ) : ℝ))) + C₀ * Nrad ^ ((E : ℕ) : ℝ)
          = C₀ * Nrad ^ ((E : ℕ) : ℝ) * (3 * (q : ℝ) + 1) := by ring
      rw [h1, ← hNE]
      have h2 : 3 * (q : ℝ) + 1 ≤ 4 * (q : ℝ) := by linarith
      have h3 : (0 : ℝ) ≤ C₀ * (Nrad * Nrad ^ (((E : ℕ) : ℝ) - 1)) := by positivity
      calc C₀ * (Nrad * Nrad ^ (((E : ℕ) : ℝ) - 1)) * (3 * (q : ℝ) + 1)
          ≤ C₀ * (Nrad * Nrad ^ (((E : ℕ) : ℝ) - 1)) * (4 * (q : ℝ)) :=
            mul_le_mul_of_nonneg_left h2 h3
        _ = Nrad * (C₀ * (4 * (q : ℝ) * Nrad ^ (((E : ℕ) : ℝ) - 1))) := by ring
    have hBb : (q : ℝ) * (((q : ℝ) / 8) * Int2)
        ≤ Nrad * (C₀ * (((q : ℝ) ^ 2 / 8) * Nrad ^ (((E : ℕ) : ℝ) - 2) * (1 + Srad + Srad ^ 2))) := by
      have h1 : (q : ℝ) * (((q : ℝ) / 8) * Int2) = ((q : ℝ) ^ 2 / 8) * Int2 := by ring
      rw [h1]
      calc ((q : ℝ) ^ 2 / 8) * Int2
          ≤ ((q : ℝ) ^ 2 / 8) * (Nrad * (C₀ * Nrad ^ (((E : ℕ) : ℝ) - 2) * (1 + Srad + Srad ^ 2))) :=
            mul_le_mul_of_nonneg_left hInt2 (by positivity)
        _ = Nrad * (C₀ * (((q : ℝ) ^ 2 / 8) * Nrad ^ (((E : ℕ) : ℝ) - 2) * (1 + Srad + Srad ^ 2))) := by
            ring
    have hsum : (q : ℝ) * (3 * (C₀ * Nrad ^ ((E : ℕ) : ℝ)) + ((q : ℝ) / 8) * Int2)
          + C₀ * Nrad ^ ((E : ℕ) : ℝ)
        ≤ Nrad * (C₀ * (4 * (q : ℝ) * Nrad ^ (((E : ℕ) : ℝ) - 1)
            + ((q : ℝ) ^ 2 / 8) * Nrad ^ (((E : ℕ) : ℝ) - 2) * (1 + Srad + Srad ^ 2))) := by
      have hsplit : (q : ℝ) * (3 * (C₀ * Nrad ^ ((E : ℕ) : ℝ)) + ((q : ℝ) / 8) * Int2)
            + C₀ * Nrad ^ ((E : ℕ) : ℝ)
          = ((q : ℝ) * (3 * (C₀ * Nrad ^ ((E : ℕ) : ℝ))) + C₀ * Nrad ^ ((E : ℕ) : ℝ))
            + (q : ℝ) * (((q : ℝ) / 8) * Int2) := by ring
      rw [hsplit]
      calc ((q : ℝ) * (3 * (C₀ * Nrad ^ ((E : ℕ) : ℝ))) + C₀ * Nrad ^ ((E : ℕ) : ℝ))
            + (q : ℝ) * (((q : ℝ) / 8) * Int2)
          ≤ Nrad * (C₀ * (4 * (q : ℝ) * Nrad ^ (((E : ℕ) : ℝ) - 1)))
            + Nrad * (C₀ * (((q : ℝ) ^ 2 / 8) * Nrad ^ (((E : ℕ) : ℝ) - 2) * (1 + Srad + Srad ^ 2))) :=
            add_le_add hA hBb
        _ = Nrad * (C₀ * (4 * (q : ℝ) * Nrad ^ (((E : ℕ) : ℝ) - 1)
            + ((q : ℝ) ^ 2 / 8) * Nrad ^ (((E : ℕ) : ℝ) - 2) * (1 + Srad + Srad ^ 2))) := by ring
    calc Nrad⁻¹ * ((q : ℝ) * (3 * (C₀ * Nrad ^ ((E : ℕ) : ℝ)) + ((q : ℝ) / 8) * Int2)
            + C₀ * Nrad ^ ((E : ℕ) : ℝ))
        ≤ Nrad⁻¹ * (Nrad * (C₀ * (4 * (q : ℝ) * Nrad ^ (((E : ℕ) : ℝ) - 1)
            + ((q : ℝ) ^ 2 / 8) * Nrad ^ (((E : ℕ) : ℝ) - 2) * (1 + Srad + Srad ^ 2)))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = C₀ * (4 * (q : ℝ) * Nrad ^ (((E : ℕ) : ℝ) - 1)
            + ((q : ℝ) ^ 2 / 8) * Nrad ^ (((E : ℕ) : ℝ) - 2) * (1 + Srad + Srad ^ 2)) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hNpos), one_mul]
  refine hkey.trans ?_
  calc C₀ * (4 * (q : ℝ) * Nrad ^ (((E : ℕ) : ℝ) - 1)
        + ((q : ℝ) ^ 2 / 8) * Nrad ^ (((E : ℕ) : ℝ) - 2) * (1 + Srad + Srad ^ 2))
      ≤ C₀ * (5 * (q : ℝ) ^ 2 * (1 + Srad ^ 2 / Nrad) * Nrad ^ (((E : ℕ) : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left (rpow_absorb hN hS hq E) (le_of_lt hC₀)
    _ = 5 * C₀ * (q : ℝ) ^ 2 * (1 + Srad ^ 2 / Nrad) * Nrad ^ (((E : ℕ) : ℝ) - 1) := by ring

private lemma rpow_to_zpow {N : ℝ} {j₁ j₂ d : ℕ} :
    N ^ (((j₁ + d * j₂ : ℕ) : ℝ) - 1) = N ^ ((j₁ : ℤ) + (d : ℤ) * (j₂ : ℤ) - 1) := by
  have h1 : (((j₁ + d * j₂ : ℕ) : ℝ) - 1) = ((((j₁ + d * j₂ : ℕ) : ℤ) - 1 : ℤ) : ℝ) := by
    push_cast; ring
  have h2 : (((j₁ + d * j₂ : ℕ) : ℤ) - 1) = (j₁ : ℤ) + (d : ℤ) * (j₂ : ℤ) - 1 := by
    push_cast; ring
  rw [h1, h2, Real.rpow_intCast]

theorem ModelApproxCore_M0_deriv_bound (P : Polynomial ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N q j₁ j₂ k₁ k₂ : ℕ)
      (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ : ℝ),
      j₁ ≤ 2 → j₂ ≤ 2 → 1 ≤ N → 0 < q → q • α₁ = 0 → q • α₂ = 0 →
      |ξ₁| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ) →
      |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree →
      ‖Work.KMTAreas.A7.M0deriv P N q α₁ α₂ ξ₁ ξ₂ j₁ j₂‖
        ≤ C * (q : ℝ) ^ 2 * (1 + ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 / (N : ℝ))
            * (N : ℝ) ^ ((j₁ : ℤ) + (P.natDegree : ℤ) * (j₂ : ℤ) - 1) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := m0w_bound P
  refine ⟨5 * C₀, by positivity, ?_⟩
  intro N q j₁ j₂ k₁ k₂ α₁ α₂ ξ₁ ξ₂ hj₁ hj₂ hN hq hα₁ hα₂ hξ₁ hξ₂
  let V : ℝ → ℂ := m0w P ξ₁ ξ₂ j₁ j₂
  let E : ℕ := j₁ + P.natDegree * j₂
  let S : ℝ := Sval P k₁ k₂
  let K : ℕ := N / 2
  have hKle : K ≤ N := Nat.div_le_self N 2
  have hVc : ContDiff ℝ 2 V := contDiff_two_m0w P ξ₁ ξ₂ j₁ j₂
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hSnn : 0 ≤ S := by
    rw [show S = Sval P k₁ k₂ from rfl]
    simp only [Sval]; positivity
  have hBv : ∀ u ∈ Set.Icc (0 : ℝ) (N : ℝ), ‖V u‖ ≤ C₀ * (N : ℝ) ^ (E : ℝ) := fun u hu =>
    (hC₀ N k₁ k₂ j₁ j₂ ξ₁ ξ₂ hN hj₁ hj₂ hξ₁ hξ₂ u hu).1
  have hB2v : ∀ u ∈ Set.Icc (0 : ℝ) (N : ℝ),
      ‖iteratedDeriv 2 V u‖ ≤ C₀ * (N : ℝ) ^ ((E : ℝ) - 2) * (1 + S + S ^ 2) := fun u hu =>
    (hC₀ N k₁ k₂ j₁ j₂ ξ₁ ξ₂ hN hj₁ hj₂ hξ₁ hξ₂ u hu).2
  have hB2nn : (0 : ℝ) ≤ C₀ * (N : ℝ) ^ ((E : ℝ) - 2) * (1 + S + S ^ 2) := by
    have h1 : (0 : ℝ) < (N : ℝ) ^ ((E : ℝ) - 2) := Real.rpow_pos_of_pos hNpos _
    have h2 : (0 : ℝ) ≤ 1 + S + S ^ 2 := by nlinarith
    positivity
  have hInt2 : (∫ u in (K : ℝ)..(N : ℝ), ‖iteratedDeriv 2 V u‖)
      ≤ (N : ℝ) * (C₀ * (N : ℝ) ^ ((E : ℝ) - 2) * (1 + S + S ^ 2)) := by
    have hKN : (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hKle
    have hcont : Continuous (fun u : ℝ => ‖iteratedDeriv 2 V u‖) :=
      (hVc.continuous_iteratedDeriv 2 le_rfl).norm
    calc (∫ u in (K : ℝ)..(N : ℝ), ‖iteratedDeriv 2 V u‖)
        ≤ ∫ u in (K : ℝ)..(N : ℝ), (C₀ * (N : ℝ) ^ ((E : ℝ) - 2) * (1 + S + S ^ 2)) := by
          refine intervalIntegral.integral_mono_on hKN (hcont.intervalIntegrable _ _)
            intervalIntegrable_const ?_
          intro u hu
          exact hB2v u ⟨le_trans (Nat.cast_nonneg K) hu.1, hu.2⟩
      _ = ((N : ℝ) - (K : ℝ)) * (C₀ * (N : ℝ) ^ ((E : ℝ) - 2) * (1 + S + S ^ 2)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ (N : ℝ) * (C₀ * (N : ℝ) ^ ((E : ℝ) - 2) * (1 + S + S ^ 2)) := by
          apply mul_le_mul_of_nonneg_right _ hB2nn
          linarith
  have hKN2 : (K : ℝ) ≤ (N : ℝ) / 2 := by
    have h2K : 2 * K ≤ N := by rw [show K = N / 2 from rfl]; exact Nat.mul_div_le N 2
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have h : ((2 * K : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2K
    push_cast at h
    linarith
  have hN2K : (N : ℝ) / 2 - (K : ℝ) ≤ 1 := by
    rw [sub_le_iff_le_add]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have h2 : N < 2 * (N / 2) + 2 := by
      have hmod : N = N % 2 + 2 * (N / 2) := (Nat.mod_add_div N 2).symm
      have hlt : N % 2 < 2 := Nat.mod_lt N (by norm_num)
      omega
    have h3 : (N : ℝ) < ((2 * (N / 2) + 2 : ℕ) : ℝ) := by exact_mod_cast h2
    rw [show K = N / 2 from rfl] at *
    push_cast at h3
    linarith
  let Z : ℂ := ∫ u in ((N : ℝ) / 2)..(K : ℝ), V u
  let Y : ℂ := ∫ u in (K : ℝ)..(N : ℝ), V u
  let W : ℂ := ∫ u in ((N : ℝ) / 2)..(N : ℝ), V u
  let Sf : ℕ → ℂ := fun a => ∑ n ∈ (Finset.Ioc K N).filter (fun n => n % q = a), V (n : ℝ)
  have hZbound : ‖Z‖ ≤ C₀ * (N : ℝ) ^ (E : ℝ) := by
    have hb : ∀ x ∈ Set.uIoc ((N : ℝ) / 2) (K : ℝ), ‖V x‖ ≤ C₀ * (N : ℝ) ^ (E : ℝ) := by
      intro x hx
      rw [Set.uIoc_comm, Set.uIoc_of_le hKN2] at hx
      exact hBv x ⟨le_trans (Nat.cast_nonneg K) hx.1.le, le_trans hx.2 (by linarith)⟩
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := V) hb
    have hlen : |((K : ℝ) - (N : ℝ) / 2)| ≤ 1 := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    calc ‖Z‖ ≤ C₀ * (N : ℝ) ^ (E : ℝ) * |((K : ℝ) - (N : ℝ) / 2)| := h
      _ ≤ C₀ * (N : ℝ) ^ (E : ℝ) * 1 := by
          apply mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = C₀ * (N : ℝ) ^ (E : ℝ) := by ring
  have hWYZ : W = Z + Y := by
    have h1 : IntervalIntegrable V volume ((N : ℝ) / 2) (K : ℝ) :=
      hVc.continuous.intervalIntegrable _ _
    have h2 : IntervalIntegrable V volume (K : ℝ) (N : ℝ) :=
      hVc.continuous.intervalIntegrable _ _
    have h3 := intervalIntegral.integral_add_adjacent_intervals h1 h2
    exact h3.symm
  have hsub : (∫ t in (1 / 2 : ℝ)..1, V ((N : ℝ) * t)) = (N : ℂ)⁻¹ * W := by
    have h := intervalIntegral.integral_comp_mul_add (a := (1 / 2 : ℝ)) (b := 1)
      (c := (N : ℝ)) (f := V) (ne_of_gt hNpos) 0
    simp only [add_zero, mul_one] at h
    rw [show (N : ℝ) * (1 / 2) = (N : ℝ) / 2 from by ring] at h
    rw [h, Algebra.smul_def, map_inv₀, map_natCast]
  have harithWnorm : ∀ n : ℤ, ‖arithW P α₁ α₂ n‖ = 1 := by
    intro n
    rw [arithW, norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe]
    norm_num
  have hsum1 : (∑ n ∈ Finset.Ioc (N / 2) N,
        Work.KMTAreas.A7.momPhaseDeriv P N α₁ α₂ ξ₁ ξ₂ (n : ℤ) j₁ j₂)
      = ∑ n ∈ Finset.Ioc K N, arithW P α₁ α₂ (n : ℤ) * V (n : ℝ) := by
    rw [show K = N / 2 from rfl]
    exact Finset.sum_congr rfl
      (fun n _ => momPhaseDeriv_eq_arithW_m0w P N α₁ α₂ ξ₁ ξ₂ n j₁ j₂)
  have hsum2 : (∑ n ∈ Finset.Ioc K N, arithW P α₁ α₂ (n : ℤ) * V (n : ℝ))
      = ∑ a ∈ Finset.range q, arithW P α₁ α₂ (a : ℤ) * Sf a :=
    sum_arithW_fiber P q α₁ α₂ hq hα₁ hα₂ K N (fun n => V (n : ℝ))
  have htil : Work.KMTAreas.A7.mTildeDeriv P N ξ₁ ξ₂ j₁ j₂
      = ∫ t in (1 / 2 : ℝ)..1, V ((N : ℝ) * t) :=
    mTildeDeriv_eq_integral_m0w P N ξ₁ ξ₂ j₁ j₂
  have hmZ : Work.KMTAreas.A7.mZ P q α₁ α₂
      = (q : ℂ)⁻¹ * (∑ a ∈ Finset.range q, arithW P α₁ α₂ (a : ℤ)) := rfl
  have hqcast : Complex.ofReal ((q : ℝ)⁻¹) = (q : ℂ)⁻¹ := by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]
  have hXid : Work.KMTAreas.A7.M0deriv P N q α₁ α₂ ξ₁ ξ₂ j₁ j₂
      = (N : ℂ)⁻¹ * ∑ a ∈ Finset.range q, arithW P α₁ α₂ (a : ℤ) * (Sf a - (q : ℝ)⁻¹ * W) := by
    unfold Work.KMTAreas.A7.M0deriv
    rw [hsum1, hsum2, htil, hsub, hmZ]
    rw [show (N : ℂ)⁻¹ * (∑ a ∈ Finset.range q, arithW P α₁ α₂ (a : ℤ) * Sf a)
          - (q : ℂ)⁻¹ * (∑ a ∈ Finset.range q, arithW P α₁ α₂ (a : ℤ)) * ((N : ℂ)⁻¹ * W)
        = (N : ℂ)⁻¹ * ((∑ a ∈ Finset.range q, arithW P α₁ α₂ (a : ℤ) * Sf a)
          - (q : ℂ)⁻¹ * (∑ a ∈ Finset.range q, arithW P α₁ α₂ (a : ℤ)) * W) from by ring]
    rw [← hqcast]
    rw [sum_fiber_algebra (fun a => arithW P α₁ α₂ (a : ℤ)) Sf (Complex.ofReal ((q : ℝ)⁻¹)) W q]
  have hper : ∀ a ∈ Finset.range q,
      ‖Sf a - (q : ℝ)⁻¹ * W‖ ≤ ‖Sf a - (q : ℝ)⁻¹ * Y‖ + (q : ℝ)⁻¹ * ‖Z‖ := by
    intro a _
    have h1 : Sf a - (q : ℝ)⁻¹ * W = (Sf a - (q : ℝ)⁻¹ * Y) - (q : ℝ)⁻¹ * Z := by
      rw [hWYZ]; ring
    rw [h1]
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [hqcast, norm_mul, norm_inv, Complex.norm_natCast]
  have hfib : ∀ a ∈ Finset.range q,
      ‖Sf a - (q : ℝ)⁻¹ * Y‖ ≤ 3 * (C₀ * (N : ℝ) ^ (E : ℝ)) + ((q : ℝ) / 8) *
        (∫ u in (K : ℝ)..(N : ℝ), ‖iteratedDeriv 2 V u‖) := by
    intro a ha
    have ha' : a < q := Finset.mem_range.mp ha
    have h := fiber_stepQ_trapezoid V hVc hKle hq ha' (by positivity)
      (fun u hu => hBv u ⟨le_trans (Nat.cast_nonneg K) hu.1, hu.2⟩)
    simpa only [Sf, Y] using h
  have hSf_bound : ‖∑ a ∈ Finset.range q, arithW P α₁ α₂ (a : ℤ) * (Sf a - (q : ℝ)⁻¹ * W)‖
      ≤ (q : ℝ) * (3 * (C₀ * (N : ℝ) ^ (E : ℝ)) + ((q : ℝ) / 8) *
          (∫ u in (K : ℝ)..(N : ℝ), ‖iteratedDeriv 2 V u‖)) + ‖Z‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc (∑ a ∈ Finset.range q, ‖arithW P α₁ α₂ (a : ℤ) * (Sf a - (q : ℝ)⁻¹ * W)‖)
        = ∑ a ∈ Finset.range q, ‖Sf a - (q : ℝ)⁻¹ * W‖ := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [norm_mul, harithWnorm (a : ℤ), one_mul]
      _ ≤ ∑ a ∈ Finset.range q, (‖Sf a - (q : ℝ)⁻¹ * Y‖ + (q : ℝ)⁻¹ * ‖Z‖) :=
          Finset.sum_le_sum (fun a ha => hper a ha)
      _ ≤ ∑ a ∈ Finset.range q, ((3 * (C₀ * (N : ℝ) ^ (E : ℝ)) + ((q : ℝ) / 8) *
              (∫ u in (K : ℝ)..(N : ℝ), ‖iteratedDeriv 2 V u‖)) + (q : ℝ)⁻¹ * ‖Z‖) :=
          Finset.sum_le_sum (fun a ha => add_le_add (hfib a ha) le_rfl)
      _ = (q : ℝ) * ((3 * (C₀ * (N : ℝ) ^ (E : ℝ)) + ((q : ℝ) / 8) *
              (∫ u in (K : ℝ)..(N : ℝ), ‖iteratedDeriv 2 V u‖)) + (q : ℝ)⁻¹ * ‖Z‖) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (q : ℝ) * (3 * (C₀ * (N : ℝ) ^ (E : ℝ)) + ((q : ℝ) / 8) *
              (∫ u in (K : ℝ)..(N : ℝ), ‖iteratedDeriv 2 V u‖)) + ‖Z‖ := by
          have hqne : (q : ℝ) ≠ 0 := by positivity
          have hterm : (q : ℝ) * ((q : ℝ)⁻¹ * ‖Z‖) = ‖Z‖ := by
            rw [← mul_assoc, mul_inv_cancel₀ hqne, one_mul]
          conv_lhs => rw [mul_add, hterm]
  have hfinal : ‖Work.KMTAreas.A7.M0deriv P N q α₁ α₂ ξ₁ ξ₂ j₁ j₂‖
      ≤ 5 * C₀ * (q : ℝ) ^ 2 * (1 + S ^ 2 / (N : ℝ)) * (N : ℝ) ^ ((E : ℝ) - 1) := by
    rw [hXid]
    calc ‖(N : ℂ)⁻¹ * ∑ a ∈ Finset.range q, arithW P α₁ α₂ (a : ℤ) * (Sf a - (q : ℝ)⁻¹ * W)‖
        = (N : ℝ)⁻¹ * ‖∑ a ∈ Finset.range q, arithW P α₁ α₂ (a : ℤ) * (Sf a - (q : ℝ)⁻¹ * W)‖ := by
          rw [norm_mul, norm_inv, Complex.norm_natCast]
      _ ≤ (N : ℝ)⁻¹ * ((q : ℝ) * (3 * (C₀ * (N : ℝ) ^ (E : ℝ)) + ((q : ℝ) / 8) *
              (∫ u in (K : ℝ)..(N : ℝ), ‖iteratedDeriv 2 V u‖)) + ‖Z‖) := by
          apply mul_le_mul_of_nonneg_left hSf_bound (by positivity)
      _ ≤ (N : ℝ)⁻¹ * ((q : ℝ) * (3 * (C₀ * (N : ℝ) ^ (E : ℝ)) + ((q : ℝ) / 8) *
              (∫ u in (K : ℝ)..(N : ℝ), ‖iteratedDeriv 2 V u‖)) + C₀ * (N : ℝ) ^ (E : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [hZbound]
      _ ≤ 5 * C₀ * (q : ℝ) ^ 2 * (1 + S ^ 2 / (N : ℝ)) * (N : ℝ) ^ ((E : ℝ) - 1) :=
          arith_step hC₀pos hN1 hq hSnn rfl rfl hInt2
  have hEeq : E = j₁ + P.natDegree * j₂ := rfl
  rw [hEeq] at hfinal
  rw [show S = Sval P k₁ k₂ from rfl] at hfinal
  rw [rpow_to_zpow] at hfinal
  simpa only [Sval] using hfinal


/-- **The undifferentiated case `j₁ = j₂ = 0`**: the sharp bound for the symbol difference `M₀`
itself.  This is the form in which the §6 single-scale estimate is consumed (see
`Work.KMTAreas.A7.ModelApproxCore`); it is an immediate consequence of
`ModelApproxCore_M0_deriv_bound`. -/
theorem ModelApproxCore_M0_bound_of_deriv (P : Polynomial ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N q k₁ k₂ : ℕ)
      (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (ξ₁ ξ₂ : ℝ),
      1 ≤ N → 0 < q → q • α₁ = 0 → q • α₂ = 0 →
      |ξ₁| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ) →
      |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree →
      ‖Work.KMTAreas.A7.M0 P N q α₁ α₂ ξ₁ ξ₂‖
        ≤ C * (q : ℝ) ^ 2
            * (1 + ((2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂)) ^ 2 / (N : ℝ)) / (N : ℝ) := by
  obtain ⟨C, hC, h⟩ := ModelApproxCore_M0_deriv_bound P
  refine ⟨C, hC, ?_⟩
  intro N q k₁ k₂ α₁ α₂ ξ₁ ξ₂ hN hq hα₁ hα₂ hξ₁ hξ₂
  have h0 := h N q 0 0 k₁ k₂ α₁ α₂ ξ₁ ξ₂ (by norm_num) (by norm_num) hN hq hα₁ hα₂ hξ₁ hξ₂
  have hM0 : Work.KMTAreas.A7.M0deriv P N q α₁ α₂ ξ₁ ξ₂ 0 0
      = Work.KMTAreas.A7.M0 P N q α₁ α₂ ξ₁ ξ₂ := by
    simp only [Work.KMTAreas.A7.M0deriv, Work.KMTAreas.A7.M0, Work.KMTAreas.A7.momPhaseDeriv,
      Work.KMTAreas.A7.mTildeDeriv, Work.KMTAreas.A7.weylAvg, Work.KMTAreas.A7.mTilde,
      pow_zero, mul_one]
  rw [hM0] at h0
  refine h0.trans (le_of_eq ?_)
  rw [show ((0 : ℕ) : ℤ) + (P.natDegree : ℤ) * ((0 : ℕ) : ℤ) - 1 = (-1 : ℤ) from by simp,
    zpow_neg_one]
  ring

end

end Work.A7
