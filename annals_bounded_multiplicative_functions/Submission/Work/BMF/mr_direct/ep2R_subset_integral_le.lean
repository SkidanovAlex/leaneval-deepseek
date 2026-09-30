import Mathlib
import Submission.Work.BMF.mr_direct.range_defs
import Submission.Work.BMF.mr_direct.ep2R_defs
import Submission.Work.BMF.mr_direct.integral_norm_sum_le
import Submission.Work.BMF.mr_direct.card_primeSet_filter_dvd
import Submission.Work.BMF.mr_direct.goodSet_bound_range_defs
import Submission.Work.BMF.mr_direct.card_sq_dvd_le
import Submission.Work.BMF.mr_direct.card_sq_dvd_range_le
import Submission.Work.BMF.mr_direct.mv_natIcc_mean_value
import Submission.Work.BMF.mr_direct.ep2R_fiber_card_le
import Submission.Work.BMF.mr_direct.ep2R_coef_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Mean-square bound for `ep2R` over a measurable subset of `[-S,S]`

This file proves `Work.BMF.mr_direct.ep2R_subset_integral_le`.  The proof writes `ep2R` as a
Finset-indexed Dirichlet polynomial over `pSetER P Q A B` (via `ep2R_eq_sum_coef`), localises
`∫_u ≤ ∫_{(-S)..S}` (`setIntegral_le_intervalIntegral`), applies the Montgomery–Vaughan mean
value theorem `integral_norm_sum_le` (giving the fibre-weighted energy
`Σ_n |F_n| (Σ_{F_n} ‖coef‖²)/n²`), and finally bounds that energy by `100/(P·A)`: on a fibre
`F_n` the coefficients are `≤ 2/ω(n;P,Q)` and `|F_n| ≤ ω(n;P,Q)`, so each fibre contributes at
most `4`; a nonempty fibre forces `x.1² ∣ n`, so only the `≤ 12A/P` integers of `[A,B]` divisible
by a prime square contribute, and each contributes at most `4/A²`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral Finset
open scoped BigOperators

open Work.BMF.mrDirect

noncomputable section

/-! ### The per-fibre bound -/

/-- The numerator `|F_n| · Σ_{x ∈ F_n} ‖coef x‖²` attached to a fibre `F_n` of `freq` is at
most `4`: `|F_n| ≤ ω(n;P,Q)` and every coefficient in the fibre has norm `≤ 2/ω(n;P,Q)`. -/
private lemma ep2R_fibre_numer_le (a b c : ℕ → ℂ) (P Q A B : ℝ) (hA : 1 ≤ A)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1) (n : ℕ) :
    (((pSetER P Q A B).filter (fun x => freq x = n)).card : ℝ) *
      (∑ x ∈ (pSetER P Q A B).filter (fun x => freq x = n), ‖coef a b c P Q x‖ ^ 2)
      ≤ 4 := by
  set F := (pSetER P Q A B).filter (fun x => freq x = n) with hF
  by_cases hne : F.Nonempty
  · obtain ⟨x0, hx0⟩ := hne
    have hx0' : x0 ∈ pSetER P Q A B := (Finset.mem_filter.mp hx0).1
    have hf0 : freq x0 = n := (Finset.mem_filter.mp hx0).2
    have hr1 : 1 ≤ omegaCount P Q n := by
      rw [← hf0, omegaCount_freq_eqR hx0']
      exact one_le_omegaCount_sndR hA hx0'
    have hwpos : (0 : ℝ) < (omegaCount P Q n : ℝ) := by
      exact_mod_cast (by omega : 0 < omegaCount P Q n)
    have hcardR : (F.card : ℝ) ≤ (omegaCount P Q n : ℝ) := by
      rw [hF]
      exact_mod_cast ep2R_fiber_card_le P Q A B hA n
    have hterm : ∀ x ∈ F, ‖coef a b c P Q x‖ ^ 2 ≤ (2 / (omegaCount P Q n : ℝ)) ^ 2 := by
      intro x hx
      have hx' : x ∈ pSetER P Q A B := (Finset.mem_filter.mp hx).1
      have hfx : freq x = n := (Finset.mem_filter.mp hx).2
      have h := ep2R_coef_bound (A := A) (B := B) hA a b c ha hb hc x hx'
      rw [hfx] at h
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    have hsum : (∑ x ∈ F, ‖coef a b c P Q x‖ ^ 2)
        ≤ (F.card : ℝ) * (2 / (omegaCount P Q n : ℝ)) ^ 2 := by
      calc (∑ x ∈ F, ‖coef a b c P Q x‖ ^ 2)
          ≤ ∑ _x ∈ F, (2 / (omegaCount P Q n : ℝ)) ^ 2 := Finset.sum_le_sum hterm
        _ = (F.card : ℝ) * (2 / (omegaCount P Q n : ℝ)) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
    calc (F.card : ℝ) * (∑ x ∈ F, ‖coef a b c P Q x‖ ^ 2)
        ≤ (F.card : ℝ) * ((F.card : ℝ) * (2 / (omegaCount P Q n : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ((F.card : ℝ) * (F.card : ℝ)) * (4 / (omegaCount P Q n : ℝ) ^ 2) := by ring
      _ ≤ ((omegaCount P Q n : ℝ) * (omegaCount P Q n : ℝ)) *
            (4 / (omegaCount P Q n : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul hcardR hcardR (by positivity) (by positivity)
      _ = 4 := by field_simp
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/-! ### The energy bound -/

/-- `Σ_{n ∈ [A,B]} |F_n| (Σ_{x ∈ F_n} ‖coef x‖²)/n² ≤ 100/(P·A)`. -/
private lemma ep2R_energy_le_priv (a b c : ℕ → ℂ) (P Q A B : ℝ)
    (hA : 1 ≤ A) (hAB : A ≤ B) (hB4 : B ≤ 4 * A) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1) :
    (∑ n ∈ Work.BMF.natIcc A B,
        (((pSetER P Q A B).filter (fun x => freq x = n)).card : ℝ) *
          (∑ x ∈ (pSetER P Q A B).filter (fun x => freq x = n), ‖coef a b c P Q x‖ ^ 2)
          / (n : ℝ) ^ 2) ≤ 100 / (P * A) := by
  have hApos : (0 : ℝ) < A := by linarith
  have hBpos : (0 : ℝ) < B := by linarith
  have hPpos : (0 : ℝ) < P := by linarith
  set S := (Work.BMF.natIcc A B).filter
      (fun n => ∃ p ∈ primeSet P Q, p * p ∣ n) with hS
  have hSsub : S ⊆ Work.BMF.natIcc A B := by rw [hS]; exact Finset.filter_subset _ _
  have hzero : ∀ n ∈ Work.BMF.natIcc A B, n ∉ S →
      (((pSetER P Q A B).filter (fun x => freq x = n)).card : ℝ) *
        (∑ x ∈ (pSetER P Q A B).filter (fun x => freq x = n), ‖coef a b c P Q x‖ ^ 2)
        / (n : ℝ) ^ 2 = 0 := by
    intro n hnB hnS
    have hpred : ¬ (∃ p ∈ primeSet P Q, p * p ∣ n) := by
      intro hcon
      exact hnS (by rw [hS]; exact Finset.mem_filter.mpr ⟨hnB, hcon⟩)
    have hempty : (pSetER P Q A B).filter (fun x => freq x = n) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨hxE, hfx⟩ := hx
      obtain ⟨k, hk⟩ := mem_pSetER_dvd hxE
      exact hpred ⟨x.1, mem_pSetER_fst hxE, k, by rw [← hfx, freq, hk]; ring⟩
    rw [hempty]
    simp
  rw [← Finset.sum_subset hSsub hzero]
  have hterm : ∀ n ∈ S,
      (((pSetER P Q A B).filter (fun x => freq x = n)).card : ℝ) *
        (∑ x ∈ (pSetER P Q A B).filter (fun x => freq x = n), ‖coef a b c P Q x‖ ^ 2)
        / (n : ℝ) ^ 2 ≤ 4 / (n : ℝ) ^ 2 := by
    intro n _hn
    exact div_le_div_of_nonneg_right (ep2R_fibre_numer_le a b c P Q A B hA ha hb hc n)
      (by positivity)
  have hcardS : (S.card : ℝ) ≤ 12 * A / P := by
    have h := card_sq_dvd_range_le A B P Q hA hAB hB4 hP hPQ
    rw [hS]
    exact h
  have hleA : ∀ n ∈ S, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / A ^ 2 := by
    intro n hn
    have hnB : n ∈ Work.BMF.natIcc A B := hSsub hn
    have hnA : A ≤ (n : ℝ) := (natIcc_bounds_gen hBpos hnB).1
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [hnA, hApos]
  calc (∑ n ∈ S,
        (((pSetER P Q A B).filter (fun x => freq x = n)).card : ℝ) *
          (∑ x ∈ (pSetER P Q A B).filter (fun x => freq x = n), ‖coef a b c P Q x‖ ^ 2)
          / (n : ℝ) ^ 2)
      ≤ ∑ n ∈ S, 4 / (n : ℝ) ^ 2 := Finset.sum_le_sum hterm
    _ = 4 * ∑ n ∈ S, 1 / (n : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ ≤ 4 * ((S.card : ℝ) / A ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc (∑ n ∈ S, 1 / (n : ℝ) ^ 2) ≤ ∑ _n ∈ S, 1 / A ^ 2 := Finset.sum_le_sum hleA
          _ = (S.card : ℝ) * (1 / A ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ = (S.card : ℝ) / A ^ 2 := by ring
    _ ≤ 4 * ((12 * A / P) / A ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact div_le_div_of_nonneg_right hcardS (by positivity)
    _ = 48 / (P * A) := by
        field_simp
        ring
    _ ≤ 100 / (P * A) := by
        have hPA : (0 : ℝ) < P * A := mul_pos hPpos hApos
        rw [div_le_div_iff₀ hPA hPA]
        linarith

/-! ### The main theorem -/

/-- Mean-square bound for the `p²`-correction term `ep2R` of the Buchstab/Ramaré decomposition,
integrated over a measurable set `u ⊆ [-S,S]`.

The term `ep2R a b c P Q A B` is a Dirichlet polynomial over the index set `pSetER P Q A B`
(pairs of a prime in `[P,Q]` and `m ∈ [A/p,B/p]` divisible by that prime), with frequency
`freq x = x.2 * x.1` and coefficient `coef x`; see `Work.BMF.mr_direct.ep2R_eq_sum_coef`,
`omegaCount_freq_eqR`, `phi_memR` in `Submission/Work/BMF/mr_direct/ep2R_defs.lean`.  The
Montgomery-Vaughan mean value theorem `Work.BMF.mr_direct.integral_norm_sum_le` applied to that
Finset-indexed polynomial (with the outer sum over `natIcc A B`, since all frequencies lie in
`[A,B]`), together with the localisation `∫_u ≤ ∫_{(-S)..S}` (`setIntegral_le_intervalIntegral`
in `goodSet_bound_range_defs.lean`), gives

`∫_u ‖ep2R‖² ≤ (2S+3C₀B) · Σ_{n ∈ natIcc A B} (card (fibre n) · Σ_{x : freq x = n} ‖coef x‖²)/n²`,

and that energy is at most `100/(P*A)`: the fibre of `n` is the set of primes `p ∈ primeSet P Q`
with `p² ∣ n`, of cardinality at most `ω(n;P,Q)`, and for `x` in the fibre of `n` one has
`ω(freq x) = ω(x.2) ≥ 1` and `‖coef x‖ ≤ 2/ω(n)`, so each fibre contributes at most `4`; only the
at most `12A/P` integers of `[A,B]` divisible by a prime square have a nonempty fibre, and each
contributes at most `4/A²`.  Hence the energy is at most `48/(P*A) ≤ 100/(P*A)`.
Note: the interval version `ep2R_integral_le` is not used here; the proof below is
self-contained apart from the elementary lemma `card_sq_dvd_range_le`. -/
theorem ep2R_subset_integral_le (C₀ : ℝ) (hC₀ : Work.BMF.mrDirect.MVConst C₀)
    (a b c : ℕ → ℂ) (P Q A B S : ℝ)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hA : 1 ≤ A) (hAB : A ≤ B) (hB4 : B ≤ 4 * A) (hP : 2 ≤ P) (hPQ : P ≤ Q) (hS : 0 ≤ S)
    (u : Set ℝ) (hu : MeasurableSet u) (husub : u ⊆ Set.Icc (-S) S) :
    (∫ t in u, ‖Work.BMF.mrDirect.ep2R a b c P Q A B t‖ ^ 2)
      ≤ (2 * S + 3 * C₀ * B) * (100 / (P * A)) := by
  have hApos : (0 : ℝ) < A := by linarith
  have hBpos : (0 : ℝ) < B := by linarith
  have hC0 : (0 : ℝ) ≤ C₀ := Work.BMF.mrDirect.MVConst.nonneg hC₀
  -- localise the integral from `u ⊆ [-S,S]` to the full interval
  have hmono : (∫ t in u, ‖ep2R a b c P Q A B t‖ ^ 2)
      ≤ ∫ t in (-S)..S, ‖ep2R a b c P Q A B t‖ ^ 2 :=
    setIntegral_le_intervalIntegral hS husub
      (((continuous_ep2R a b c P Q A B hApos).norm).pow 2)
      (fun _ _ => by positivity)
  -- rewrite `ep2R` as a Finset-indexed Dirichlet polynomial
  have hpoint : ∀ t : ℝ, ‖ep2R a b c P Q A B t‖ ^ 2
      = ‖∑ x ∈ pSetER P Q A B, coef a b c P Q x *
          ((freq x : ℕ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2 :=
    fun t => congrArg (fun z : ℂ => ‖z‖ ^ 2) (ep2R_eq_sum_coef a b c P Q A B t)
  have hint : (∫ t in (-S)..S, ‖ep2R a b c P Q A B t‖ ^ 2)
      = ∫ t in (-S)..S, ‖∑ x ∈ pSetER P Q A B, coef a b c P Q x *
          ((freq x : ℕ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2 :=
    intervalIntegral.integral_congr (fun t _ => hpoint t)
  -- Montgomery–Vaughan on the index set `pSetER`
  have hmem : ∀ i ∈ pSetER P Q A B, freq i ∈ Work.BMF.natIcc A B :=
    fun i hi => by simpa only [freq] using phi_memR hApos hAB hi
  have hAle : ∀ i ∈ pSetER P Q A B, A ≤ (freq i : ℝ) :=
    fun i hi => ((Work.BMF.mrDirect.mem_natIcc hBpos.le).mp (hmem i hi)).1
  have hBle : ∀ i ∈ pSetER P Q A B, (freq i : ℝ) ≤ B :=
    fun i hi => ((Work.BMF.mrDirect.mem_natIcc hBpos.le).mp (hmem i hi)).2
  have hmv := integral_norm_sum_le C₀ hC₀ (pSetER P Q A B) (coef a b c P Q) freq
    (Work.BMF.natIcc A B) A B S hApos hAB hS hmem hAle hBle
  have henergy := ep2R_energy_le_priv a b c P Q A B hA hAB hB4 hP hPQ ha hb hc
  calc (∫ t in u, ‖ep2R a b c P Q A B t‖ ^ 2)
      ≤ ∫ t in (-S)..S, ‖ep2R a b c P Q A B t‖ ^ 2 := hmono
    _ = ∫ t in (-S)..S, ‖∑ x ∈ pSetER P Q A B, coef a b c P Q x *
          ((freq x : ℕ) : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2 := hint
    _ ≤ (2 * S + 3 * C₀ * B) * ∑ n ∈ Work.BMF.natIcc A B,
          (((pSetER P Q A B).filter (fun x => freq x = n)).card : ℝ) *
            (∑ x ∈ (pSetER P Q A B).filter (fun x => freq x = n),
              ‖coef a b c P Q x‖ ^ 2) / (n : ℝ) ^ 2 := hmv
    _ ≤ (2 * S + 3 * C₀ * B) * (100 / (P * A)) := by
        apply mul_le_mul_of_nonneg_left henergy
        nlinarith [hS, hC0, hBpos]

end

end Work.BMF.mr_direct

