import Mathlib
import Submission.Work.BMF.mr_direct_range_defs
import Submission.Work.BMF.mr_direct.buchstab_aux
import Submission.Work.BMF.mr_direct.buchstab_decomp
import Submission.Work.BMF.mr_direct.mv_natIcc_mean_value

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Range-generalised Buchstab/Ramaré vocabulary

This file collects the elementary vocabulary needed for the general-range Buchstab/Ramaré
decomposition of the Dirichlet polynomial `dirPolyR a X₁ X₂` over a range `[X₁,X₂]` with
bounded ratio (`X₂ ≤ 4 X₁`), generalising `Work.BMF.mrDirect.dirPolyM` (the dyadic case
`X₂ = 2 X₁`, `Submission/Work/BMF/mr_direct_defs.lean`) and its Buchstab decomposition
(`Submission/Work/BMF/mr_direct/dirPolyM_eq_mainA_add_ep2.lean` and following files).

The dictionary is `X ↦ X₁ =: A` (the left endpoint, which plays the role of the *scale*) and
`2X ↦ X₂ =: B` (the right endpoint):

* `winIdxR K A B j = ℕ ∩ [A e^{-(j+1)/K}, B e^{-j/K}]` (the m-window of the remainder
  polynomial), and `remPolyR b P Q K A B j` is the corresponding remainder polynomial;
* `mainAR`, `ep2R`, `mainBR`, `eboundR`, `dupExtraR` are the range analogues of `mainA`,
  `ep2`, `mainB`, `ebound`, `dupExtra`.

The main outputs needed by the assembly are

* `dirPolyR_eq_mainAR_add_ep2R` (Buchstab identity, `Submission.Work.BMF.mr_direct.buchstab_id_range`);
* `mainAR_eq_mainBR_sub_eboundR` and `mainTermR_eq_mainBR_add_dupExtraR` (the two regroupings,
  `Submission.Work.BMF.mr_direct.mainAR_regroup` / `mainTermR_regroup`);
* the mean-square bounds `eboundR_integral_le`, `ep2R_integral_le`, `dupExtraR_integral_le`;
* the support count `card_has_prime_factorR_le`.

This file itself only fixes the notation and proves the elementary membership/continuity lemmas
and the `card × Σ` bound `mainTermR_integral_le`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Work.BMF

open MeasureTheory intervalIntegral
open scoped BigOperators

namespace mrDirect

noncomputable section


/-
## Adaptation guide for the range-generalised statements

All the following statements are the dyadic ones with `X ↦ A` (the left endpoint, the "scale")
and `2 * X ↦ B` (the right endpoint), with `A, B` satisfying `1 ≤ A ≤ B ≤ 4 * A`:

* `dirPolyR_eq_mainAR_add_ep2R` — the Buchstab/Ramaré identity; template
  `Submission/Work/BMF/mr_direct/dirPolyM_eq_mainA_add_ep2.lean` (its internal `buchSigma`,
  `phi_mem`, `buchF`, `buchE`, `image_fiber`, `mainA_sigma`, `ep2_sigma`, `buchF_eval`,
  `fiber_sum_eq` all carry over verbatim with `natIcc (A/p) (B/p)` in place of
  `natIcc (X/p) (2*X/p)`).

* `mainAR_eq_mainBR_sub_eboundR` — regrouping; template
  `Work.BMF.mr_direct.bi_mainA_eq_mainB_sub_ebound` in `buchstab_identity.lean`;
  the geometric input is `natIcc_div_subset_winIdxR` (proved above).

* `mainTermR_eq_mainBR_add_dupExtraR` — regrouping; template
  `Work.BMF.mr_direct.bi_mainTerm_eq_mainB_add_dupExtra` in `buchstab_identity.lean`;
  the range-independent inputs `bi_canon_set`, `bi_primeSet_group` can be reused verbatim.

* `eboundR_integral_le` — template `Submission/Work/BMF/mr_direct/ebound_integral_le.lean` and
  its satellites `ebound_defs.lean`, `ebound_eq_fiber_sum.lean`, `pSetB_mem_range.lean`,
  `ebD_norm_sq_le_one.lean`, `ebD_sum_div_sq_le.lean`, `card_diff_natIcc_le.lean`.
  The merged frequency is `i.1 * i.2` and lives in `[A e^{-1/K}, B e^{1/K}]`; the number of
  integers in that range but outside `[A,B]` is at most `8*B/K + 8`.

* `ep2R_integral_le` — template `Submission/Work/BMF/mr_direct/ep2_integral_le.lean`.

* `dupExtraR_integral_le` — template `Submission/Work/BMF/mr_direct/dupExtra_integral_le.lean`
  (whose only gap is the sorried `pairSetD_inv_le`; use the *proved*
  `Work.BMF.mr_direct.pairSetD_inv_le` from `pairSetD_inv_le.lean` instead) and its satellites
  `dupExtra_defs.lean`, `dupExtra_expand.lean`, `dupExtra_nnD_bounds.lean`,
  `dupExtra_fiber_card.lean`, `winIdx_sum_bounds.lean`, `sum_inv_sq_filter_dvd_le.lean`.

* `card_has_prime_factorR_le` — template
  `Submission/Work/BMF/mr_direct/card_has_prime_factor_le.lean`.
-/

/-! ### Range-independent elementary helpers, restated here for self-containedness -/

/-- Continuity of `t ↦ n^{-(1+it)}`. -/
lemma continuous_cpow_R (n : ℕ) (hn : 1 ≤ n) :
    Continuous fun t : ℝ => (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
  have hfun : (fun t : ℝ => (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))
      = fun t : ℝ => (n : ℂ)⁻¹ *
          Complex.exp (Complex.I * (((-(Real.log (n : ℝ)) : ℝ) : ℂ) * (t : ℂ))) := by
    funext t
    exact Work.BMF.cpow_neg_one_sub_I n hn t
  rw [hfun]
  fun_prop

/-- Continuity of the prime polynomial `t ↦ Q_j(t)`. -/
lemma continuous_primePoly_R (c : ℕ → ℂ) (K : ℝ) (j : ℕ) :
    Continuous fun t => primePoly c K j t := by
  unfold primePoly
  refine continuous_finsetSum _ fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact Continuous.mul continuous_const (continuous_cpow_R p hp.2.one_le)

/-- Continuity of `t ↦ dirPolyR a A B t`. -/
lemma continuous_dirPolyR (a : ℕ → ℂ) (A B : ℝ) (hA : 0 < A) :
    Continuous fun t => dirPolyR a A B t := by
  unfold dirPolyR
  refine continuous_finsetSum _ fun n hn => ?_
  rw [Work.BMF.natIcc, Finset.mem_Icc] at hn
  exact Continuous.mul continuous_const
    (continuous_cpow_R n (le_trans (Nat.one_le_ceil_iff.mpr hA) hn.1))

/-- `Σ` over a filtered set plus its complement. -/
lemma sum_filter_add_R (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℂ) :
    (∑ x ∈ s.filter p, f x) + (∑ x ∈ s.filter (fun x => ¬ p x), f x) = ∑ x ∈ s, f x := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : p x <;> simp [h]

/-- The canonical set of a prime window: the primes of `winPrimes K j` that lie in `[P,Q]`
and have `j` as their index. -/
lemma canon_set_R (K P Q : ℝ) (hK : 0 < K) (hP : 2 ≤ P) (hPQ : P ≤ Q) (j : ℕ) :
    (primeSet P Q).filter (fun p => jdex K p = j)
      = (winPrimes K j).filter
          (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p) := by
  have hQnn : (0 : ℝ) ≤ Q := by linarith
  ext p
  constructor
  · intro hp
    obtain ⟨hp', hjd⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpp, hPp, hpQ⟩ := (mem_primeSet hQnn).mp hp'
    have hw : p ∈ winPrimes K j := by
      rw [← hjd]
      exact mem_winPrimes_jdex hK hpp
    exact Finset.mem_filter.mpr ⟨hw, hPp, hpQ, hjd.symm⟩
  · intro hp
    obtain ⟨hpw, hPp, hpQ, hjd⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨mem_primeSet' (mem_winPrimes.mp hpw).1 hPp hpQ, hjd.symm⟩

/-- Sums over `primeSet P Q` regrouped by the canonical window of each prime. -/
lemma primeSet_group_R (Ψ : ℕ → ℂ) (K P Q : ℝ) (hK : 0 < K) (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    (∑ p ∈ primeSet P Q, Ψ p) =
      ∑ j ∈ indexSet K P Q,
        ∑ p ∈ (winPrimes K j).filter
            (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p), Ψ p := by
  have hmem : ∀ p ∈ primeSet P Q, jdex K p ∈ indexSet K P Q := by
    intro p hp
    obtain ⟨hpp, hPp, hpQ⟩ := (mem_primeSet (by linarith : (0 : ℝ) ≤ Q)).mp hp
    exact jdex_mem_indexSet hK hpp.one_le (by linarith) hPp hpQ
  rw [← Finset.sum_fiberwise_of_maps_to (s := primeSet P Q) (t := indexSet K P Q)
    (g := fun p => jdex K p) hmem]
  exact Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr (canon_set_R K P Q hK hP hPQ j) (fun _ _ => rfl)

/-! ### The integer window and the remainder polynomial -/

/-- The integer window `ℕ ∩ [A e^{-(j+1)/K}, B e^{-j/K}]` of `remPolyR`. -/
def winIdxR (K A B : ℝ) (j : ℕ) : Finset ℕ :=
  Work.BMF.natIcc (A * Real.exp (-((j : ℝ) + 1) / K)) (B * Real.exp (-(j : ℝ) / K))

/-- `remPolyR` unfolded as a sum over `winIdxR`. -/
lemma remPolyR_eq_winIdxR (b : ℕ → ℂ) (P Q K A B : ℝ) (j : ℕ) (t : ℝ) :
    remPolyR b P Q K A B j t =
      ∑ m ∈ winIdxR K A B j, b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
        (m : ℂ) ^ (-(1 + Complex.I * t)) := rfl

/-- Membership in `winIdxR`, as real inequalities. -/
lemma mem_winIdxR {K A B : ℝ} {j m : ℕ} (h : 0 ≤ B * Real.exp (-(j : ℝ) / K)) :
    m ∈ winIdxR K A B j ↔
      A * Real.exp (-((j : ℝ) + 1) / K) ≤ (m : ℝ) ∧
        (m : ℝ) ≤ B * Real.exp (-(j : ℝ) / K) :=
  mem_natIcc h

/-- For a prime `p` in the `j`-th logarithmic window, the interval `[A/p, B/p]` of the
Buchstab main term is contained in the corresponding `remPolyR` window. -/
lemma natIcc_div_subset_winIdxR {K A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {j p : ℕ}
    (hp : p ∈ winPrimes K j) : Work.BMF.natIcc (A / p) (B / p) ⊆ winIdxR K A B j := by
  obtain ⟨-, h1, h2⟩ := mem_winPrimes.mp hp
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le (Real.exp_pos _) h1
  refine natIcc_mono ?_ ?_
  · have h3 : Real.exp (-((j : ℝ) + 1) / K) ≤ 1 / (p : ℝ) := by
      rw [show -((j : ℝ) + 1) / K = -(((j : ℝ) + 1) / K) by ring, Real.exp_neg, one_div]
      simpa only [one_div] using one_div_le_one_div_of_le hp0 h2
    calc A * Real.exp (-((j : ℝ) + 1) / K) ≤ A * (1 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 hA
      _ = A / (p : ℝ) := by ring
  · have h4 : 1 / (p : ℝ) ≤ Real.exp (-(j : ℝ) / K) := by
      rw [show -(j : ℝ) / K = -((j : ℝ) / K) by ring, Real.exp_neg, one_div]
      simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos ((j : ℝ) / K)) h1
    calc B / (p : ℝ) = B * (1 / (p : ℝ)) := by ring
      _ ≤ B * Real.exp (-(j : ℝ) / K) := mul_le_mul_of_nonneg_left h4 hB

/-- Continuity of `t ↦ remPolyR b P Q K A B j t`. -/
lemma continuous_remPolyR (b : ℕ → ℂ) (P Q K A B : ℝ) (j : ℕ) (hA : 0 < A) :
    Continuous fun t => remPolyR b P Q K A B j t := by
  unfold remPolyR
  refine continuous_finsetSum _ fun m hm => ?_
  rw [Work.BMF.natIcc, Finset.mem_Icc] at hm
  have hm1 : 1 ≤ m := le_trans (Nat.one_le_ceil_iff.mpr (mul_pos hA (Real.exp_pos _))) hm.1
  exact Continuous.mul (Continuous.mul continuous_const continuous_const)
    (continuous_cpow_R m hm1)

/-! ### The terms of the range decomposition -/

/-- The range main term `Σ_p c p p^{-s} Σ_{A/p ≤ m ≤ B/p} b m (ω(m;P,Q)+1)^{-1} m^{-s}`. -/
noncomputable def mainAR (b c : ℕ → ℂ) (P Q A B : ℝ) (t : ℝ) : ℂ :=
  ∑ p ∈ primeSet P Q, c p * (p : ℂ) ^ (-(1 + Complex.I * t)) *
    ∑ m ∈ Work.BMF.natIcc (A / p) (B / p),
      b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ * (m : ℂ) ^ (-(1 + Complex.I * t))

/-- The range `p²`-correction term. -/
noncomputable def ep2R (a b c : ℕ → ℂ) (P Q A B : ℝ) (t : ℝ) : ℂ :=
  ∑ p ∈ primeSet P Q,
    ∑ m ∈ (Work.BMF.natIcc (A / p) (B / p)).filter (fun m => p ∣ m),
      (a (m * p) * (((omegaCount P Q m : ℕ) : ℕ) : ℂ)⁻¹ -
        b m * c p * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹) *
        ((m * p : ℕ) : ℂ) ^ (-(1 + Complex.I * t))

/-- The main term grouped by the canonical window of each prime. -/
noncomputable def mainBR (b c : ℕ → ℂ) (K P Q A B : ℝ) (t : ℝ) : ℂ :=
  ∑ p ∈ primeSet P Q, c p * (p : ℂ) ^ (-(1 + Complex.I * t)) *
    remPolyR b P Q K A B (jdex K p) t

/-- The range-extension error: `mainBR - mainAR`. -/
noncomputable def eboundR (b c : ℕ → ℂ) (K P Q A B : ℝ) (t : ℝ) : ℂ :=
  ∑ p ∈ primeSet P Q, c p * (p : ℂ) ^ (-(1 + Complex.I * t)) *
    ∑ m ∈ (winIdxR K A B (jdex K p)).filter
        (fun m => m ∉ Work.BMF.natIcc (A / p) (B / p)),
      b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ * (m : ℂ) ^ (-(1 + Complex.I * t))

/-- The error from primes lying in a window but outside `[P,Q]`, or in a non-canonical window. -/
noncomputable def dupExtraR (b c : ℕ → ℂ) (K P Q A B : ℝ) (t : ℝ) : ℂ :=
  ∑ j ∈ indexSet K P Q,
    (∑ p ∈ (winPrimes K j).filter
        (fun (p : ℕ) => ¬(P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p)),
      c p * (p : ℂ) ^ (-(1 + Complex.I * t))) * remPolyR b P Q K A B j t

lemma continuous_eboundR (b c : ℕ → ℂ) (K P Q A B : ℝ) (hA : 0 < A) (hP : 2 ≤ P)
    (hPQ : P ≤ Q) :
    Continuous fun t => eboundR b c K P Q A B t := by
  unfold eboundR
  refine continuous_finsetSum _ fun p hp => Continuous.mul ?_ ?_
  · exact Continuous.mul continuous_const (continuous_cpow_R p (by
      exact ((mem_primeSet (by linarith : (0 : ℝ) ≤ Q)).mp hp).1.one_le))
  · refine continuous_finsetSum _ fun m hm => ?_
    have hm1 : 1 ≤ m := by
      have hmem := (Finset.mem_filter.mp hm).1
      rw [winIdxR, Work.BMF.natIcc, Finset.mem_Icc] at hmem
      exact le_trans (Nat.one_le_ceil_iff.mpr (mul_pos hA (Real.exp_pos _))) hmem.1
    exact Continuous.mul (Continuous.mul continuous_const continuous_const)
      (continuous_cpow_R m hm1)

lemma continuous_dupExtraR (b c : ℕ → ℂ) (K P Q A B : ℝ) (hA : 0 < A) :
    Continuous fun t => dupExtraR b c K P Q A B t := by
  unfold dupExtraR
  refine continuous_finsetSum _ fun j _ =>
    Continuous.mul ?_ (continuous_remPolyR b P Q K A B j hA)
  refine continuous_finsetSum _ fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact Continuous.mul continuous_const
    (continuous_cpow_R p (mem_winPrimes.mp hp.1).1.one_le)

lemma continuous_ep2R (a b c : ℕ → ℂ) (P Q A B : ℝ) (hA : 0 < A) :
    Continuous fun t => ep2R a b c P Q A B t := by
  unfold ep2R
  refine continuous_finsetSum _ fun p hp => ?_
  have hp1 : 1 ≤ p := (Finset.mem_filter.mp hp).2.one_le
  have hppos : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp1)
  refine continuous_finsetSum _ fun m hm => ?_
  have hm1 : 1 ≤ m * p := by
    have h2 : 1 ≤ m := by
      have hmem := (Finset.mem_filter.mp hm).1
      rw [Work.BMF.natIcc, Finset.mem_Icc] at hmem
      exact le_trans (Nat.one_le_ceil_iff.mpr (div_pos hA hppos)) hmem.1
    calc 1 ≤ 1 * 1 := by norm_num
      _ ≤ m * p := Nat.mul_le_mul h2 hp1
  exact Continuous.mul (Continuous.sub (Continuous.mul continuous_const continuous_const)
    (Continuous.mul (Continuous.mul continuous_const continuous_const) continuous_const))
    (continuous_cpow_R _ hm1)

/-! ### Preparatory bounds proved here -/

/-- Continuity of the main sum `Σ_j Q_j R_j`. -/
lemma continuous_MT_R (b c : ℕ → ℂ) (K P Q A B : ℝ) (hA : 0 < A) :
    Continuous fun t =>
      ∑ j ∈ indexSet K P Q, primePoly c K j t * remPolyR b P Q K A B j t :=
  continuous_finsetSum _ fun j _ =>
    (continuous_primePoly_R c K j).mul (continuous_remPolyR b P Q K A B j hA)

/-- The `card × Σ` mean-square bound for the main term. -/
lemma mainTermR_integral_le (c b : ℕ → ℂ) (K P Q A B S : ℝ) (hA : 0 < A) (hS : 0 ≤ S) :
    (∫ t in (-S)..S,
        ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2)
      ≤ ((indexSet K P Q).card : ℝ) *
          (∑ j ∈ indexSet K P Q,
            ∫ t in (-S)..S, ‖primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2) := by
  have hpt : ∀ t, ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2
      ≤ ((indexSet K P Q).card : ℝ) *
        ∑ j ∈ indexSet K P Q, ‖primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2 := by
    intro t
    calc ‖∑ j ∈ indexSet K P Q, primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2
        ≤ (∑ j ∈ indexSet K P Q, ‖primePoly c K j t * remPolyR b P Q K A B j t‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := sq_sum_le_card_mul_sum_sq
  have hcont : Continuous fun t => ((indexSet K P Q).card : ℝ) *
        ∑ j ∈ indexSet K P Q, ‖primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2 :=
    Continuous.mul continuous_const (continuous_finsetSum _ fun j _ =>
      ((continuous_primePoly_R c K j).mul (continuous_remPolyR b P Q K A B j hA)).norm.pow 2)
  have hint : (∫ t in (-S)..S, ((indexSet K P Q).card : ℝ) *
        ∑ j ∈ indexSet K P Q, ‖primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2)
      = ((indexSet K P Q).card : ℝ) *
        (∑ j ∈ indexSet K P Q,
          ∫ t in (-S)..S, ‖primePoly c K j t * remPolyR b P Q K A B j t‖ ^ 2) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
    intro j _
    exact (((continuous_primePoly_R c K j).mul
      (continuous_remPolyR b P Q K A B j hA)).norm.pow 2).intervalIntegrable _ _
  exact (intervalIntegral.integral_mono (by linarith)
    (((continuous_MT_R b c K P Q A B hA).norm.pow 2).intervalIntegrable (-S) S)
    (hcont.intervalIntegrable (-S) S) hpt).trans (le_of_eq hint)


/-! ### The large-sieve mean value hypothesis, as a named predicate -/

/-- The Montgomery–Vaughan large-sieve mean value theorem for `δ`-separated frequencies
(`Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies`), packaged as a
predicate on the constant `C₀`. -/
def MVConst (C₀ : ℝ) : Prop :=
  ∀ (δ : ℝ), 0 < δ → ∀ (N : ℕ) (μ : Fin N → ℝ) (b : Fin N → ℂ),
    (∀ i j, i ≠ j → δ ≤ |μ i - μ j|) → ∀ (A B : ℝ), A ≤ B →
      (∫ t in A..B, ‖∑ n, b n * Complex.exp (Complex.I * ((μ n : ℂ) * (t : ℂ)))‖ ^ 2)
        ≤ (B - A + C₀ / δ) * ∑ n, ‖b n‖ ^ 2

/-- A mean-value constant is nonnegative. -/
lemma MVConst.nonneg {C₀ : ℝ} (h : MVConst C₀) : 0 ≤ C₀ :=
  Work.BMF.mr_direct.c0_nonneg_of_mv C₀ h

/-- The mean value theorem for a Dirichlet polynomial over an arbitrary integer range. -/
lemma MVConst.mv_natIcc {C₀ : ℝ} (h : MVConst C₀) (d : ℕ → ℂ) (A B S : ℝ) (hA : 0 < A)
    (hAB : A ≤ B) (hS : 0 ≤ S) :
    (∫ t in (-S)..S,
        ‖∑ n ∈ Work.BMF.natIcc A B, d n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2)
      ≤ (2 * S + 3 * C₀ * B) * ∑ n ∈ Work.BMF.natIcc A B, ‖d n‖ ^ 2 / (n : ℝ) ^ 2 :=
  Work.BMF.mr_direct.mv_natIcc_mean_value C₀ h d A B S hA hAB hS

/-- `dirPolyR` with `X₂ = 2 X₁` is the dyadic polynomial `dirPolyM`. -/
lemma dirPolyR_dyadic (a : ℕ → ℂ) (A t : ℝ) :
    dirPolyR a A (2 * A) t = dirPolyM a A t := rfl

/-- `remPolyR` with `X₂ = 2 X₁` is the dyadic remainder polynomial `remPoly`. -/
lemma remPolyR_dyadic (b : ℕ → ℂ) (P Q K A : ℝ) (j : ℕ) (t : ℝ) :
    remPolyR b P Q K A (2 * A) j t = remPoly b P Q K A j t := rfl

end

end mrDirect

end Work.BMF
