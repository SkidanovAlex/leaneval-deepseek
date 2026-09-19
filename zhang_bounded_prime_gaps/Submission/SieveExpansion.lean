import Mathlib
import Submission.Commons.NumberTheory.SieveWindows.divisorSumProduct_window_eq_k
import Submission.SieveSFunction
import Submission.Commons.Algebra.BigOperators.sum_pi_prod_abs
import Submission.S2Expansion

open scoped BigOperators

set_option maxHeartbeats 0

/-!
# The `k`-coordinate window expansion, tied to the `S`-set counting

The fleet-proven `k`-coordinate expansion
(`Commons.NumberTheory.SieveWindows.divisorSumProduct_window_eq_k`) expands a
window sum of a product of one-dimensional divisor sums into a sum over
divisor-function pairs `(d, e : Fin k → Fin (D+1))` whose coefficient is
`# {n ∈ window : ∀ i, lcm (d i) (e i) | n + H i}`.

This file records the *sieve-shaped* consequence: when the window is the
residue class `n ≡ b (mod W)` (as in Polymath8a §4.1), that coefficient is
exactly the `S`-set count with moduli `m i := [d i, d′ i]` — the object whose
size `Sset_lcm_card_window_bounds` evaluates as `N/(W·∏ᵢ [dᵢ,d′ᵢ]) + O(1)`. -/

namespace Commons.NumberTheory.MaynardSieve

/-- **Sieve expansion.**  Over the residue-class window `n ≡ b (mod W)`, a
product of per-coordinate divisor-sum products expands into a sum over divisor
function pairs of `(∏ᵢ αᵢ(dᵢ)βᵢ(eᵢ))` times the corresponding `S`-set count
with moduli `lcm (d i) (e i)`.  (Polymath8a §4.1, expansion (42).) -/
theorem residueWindowProduct_eq_weighted_Sset {k D N W b : ℕ} {H : Fin k → ℕ}
    (α β : Fin k → ℕ → ℝ) :
    (∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => n % W = b % W),
        ∏ i : Fin k,
          (∑ d : Fin (D + 1),
            α i (d : ℕ) * (if (d : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
          (∑ e : Fin (D + 1),
            β i (e : ℕ) * (if (e : ℕ) ∣ n + H i then (1 : ℝ) else 0))) =
    ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
      (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
        ((Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))).card : ℝ) := by
  classical
  rw [Commons.NumberTheory.SieveWindows.divisorSumProduct_window_eq_k
    (k := k) (D := D) (s := (Finset.Icc N (2 * N)).filter (fun n => n % W = b % W))
    (H := H) (α := α) (β := β)]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  rw [Sset_eq_class_filter (k := k) (N := N) (W := W) (b := b) (H := H)
    (m := fun i => Nat.lcm (d i : ℕ) (e i : ℕ))]


/-! ## Main-term substitution per divisor pair

The evaluation `S = x/(W·∏ᵢ [dᵢ,d′ᵢ]) + O(1)` is now applied *inside* the
`(d,e)`-sum: for each divisor pair we write

    coeff(d,e) · #S = coeff(d,e) · N/(W·∏ᵢ [dᵢ,eᵢ])  +  coeff(d,e)·err(d,e)

with `|err(d,e)| ≤ 2` once the lcm-moduli are pairwise coprime and coprime to
`W`.  Summing the last term is the (fleet-delegated) crude-divisor error
bound; the main term is exactly what P8 Lemma 4.1 evaluates. -/

/-- The coefficient `∏ᵢ αᵢ(dᵢ)·βᵢ(eᵢ)` of a divisor pair. -/
noncomputable def coefProd {k : ℕ} (α β : Fin k → ℕ → ℝ) (d e : Fin k → ℕ) : ℝ :=
  ∏ i : Fin k, α i (d i) * β i (e i)

/-- The main term `N/(W·∏ᵢ mᵢ)` for a tuple of moduli. -/
noncomputable def mainTerm (N W : ℕ) {k : ℕ} (m : Fin k → ℕ) : ℝ :=
  (N : ℝ) / ((W * (∏ i : Fin k, m i) : ℕ) : ℝ)

/-- The `O(1)` error `#S − N/(W·∏ᵢ mᵢ)`. -/
noncomputable def SsetErr (N W b : ℕ) {k : ℕ} (H : Fin k → ℕ) (m : Fin k → ℕ) : ℝ :=
  ((Sset N W b H m).card : ℝ) - mainTerm N W m

/-- `|err| ≤ 2` for pairwise-coprime moduli (the `O(1)` in Polymath8a §4.1). -/
theorem Sset_lcm_error_bound {k N W b : ℕ} {H : Fin k → ℕ} {d e : Fin k → ℕ}
    (hW : 0 < W) (hd : ∀ i : Fin k, d i ≠ 0) (he : ∀ i : Fin k, e i ≠ 0)
    (hcopW : ∀ i : Fin k, (Nat.lcm (d i) (e i)).Coprime W)
    (hcopm : ∀ i j : Fin k, i ≠ j →
      (Nat.lcm (d i) (e i)).Coprime (Nat.lcm (d j) (e j))) :
    |SsetErr N W b H (fun i => Nat.lcm (d i) (e i))| ≤ 2 := by
  have hb := Sset_lcm_card_window_bounds (k := k) (N := N) (W := W) (b := b) (H := H)
    (d := d) (d' := e) hW hd he hcopW hcopm
  simpa [SsetErr, mainTerm] using hb

/-- Per divisor pair: coefficient·`#S` splits into main term plus a
coefficient-times-error, with `|error·coefficient| ≤ 2·|coefficient|`. -/
theorem Sset_lcm_coefficient_substitution {k N W b : ℕ} {H : Fin k → ℕ}
    {d e : Fin k → ℕ} {α β : Fin k → ℕ → ℝ}
    (hW : 0 < W) (hd : ∀ i : Fin k, d i ≠ 0) (he : ∀ i : Fin k, e i ≠ 0)
    (hcopW : ∀ i : Fin k, (Nat.lcm (d i) (e i)).Coprime W)
    (hcopm : ∀ i j : Fin k, i ≠ j →
      (Nat.lcm (d i) (e i)).Coprime (Nat.lcm (d j) (e j))) :
    let m : Fin k → ℕ := fun i => Nat.lcm (d i) (e i)
    coefProd α β d e * ((Sset N W b H m).card : ℝ) =
      coefProd α β d e * mainTerm N W m + coefProd α β d e * SsetErr N W b H m := by
  intro m
  rw [SsetErr]
  ring

/-- The error part of the substitution is bounded by `2·|coefficient|`. -/
theorem Sset_lcm_substitution_error_bound {k N W b : ℕ} {H : Fin k → ℕ}
    {d e : Fin k → ℕ} {α β : Fin k → ℕ → ℝ}
    (hW : 0 < W) (hd : ∀ i : Fin k, d i ≠ 0) (he : ∀ i : Fin k, e i ≠ 0)
    (hcopW : ∀ i : Fin k, (Nat.lcm (d i) (e i)).Coprime W)
    (hcopm : ∀ i j : Fin k, i ≠ j →
      (Nat.lcm (d i) (e i)).Coprime (Nat.lcm (d j) (e j))) :
    |coefProd α β d e * SsetErr N W b H (fun i => Nat.lcm (d i) (e i))| ≤
      2 * |coefProd α β d e| := by
  have hee := Sset_lcm_error_bound (k := k) (N := N) (W := W) (b := b) (H := H)
    (d := d) (e := e) hW hd he hcopW hcopm
  rw [abs_mul]
  have hmul : |SsetErr N W b H (fun i => Nat.lcm (d i) (e i))| *
        |coefProd α β d e| ≤ 2 * |coefProd α β d e| := by
    exact mul_le_mul_of_nonneg_right hee (abs_nonneg (coefProd α β d e))
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul


/-! ## Zero contributions of non-coprime pairs

A divisor pair whose lcm-moduli are not coprime to `W`, or not pairwise
coprime, has empty `S`-set, hence contributes nothing to the expansion sum.
These are the "the `S`-function vanishes unless the `[dᵢ,d′ᵢ]` are pairwise
coprime and coprime to `W`" statements of Polymath8a §4.1 at the level of
individual pairs, ready to be summed over. -/

/-- A divisor pair is *good* when its lcm-moduli are pairwise coprime and each
is coprime to `W`. -/
def lcmGood {k D : ℕ} (W : ℕ) (d e : Fin k → Fin (D + 1)) : Prop :=
  (∀ i : Fin k, (Nat.lcm (d i : ℕ) (e i : ℕ)).Coprime W) ∧
    (∀ i j : Fin k, i ≠ j →
      (Nat.lcm (d i : ℕ) (e i : ℕ)).Coprime (Nat.lcm (d j : ℕ) (e j : ℕ)))

/-- A pair with some lcm-modulus sharing a factor with `W` contributes zero. -/
theorem nonGoodW_pair_contribution_zero {k D N W b : ℕ} {H : Fin k → ℕ}
    {d e : Fin k → Fin (D + 1)} {α β : Fin k → ℕ → ℝ}
    (hbW : ∀ i : Fin k, (b + H i).Coprime W)
    (hbad : ¬ ∀ i : Fin k, (Nat.lcm (d i : ℕ) (e i : ℕ)).Coprime W) :
    coefProd α β (fun i : Fin k => (d i : ℕ)) (fun i : Fin k => (e i : ℕ)) *
      ((Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))).card : ℝ) = 0 := by
  classical
  have hex : ∃ i : Fin k, ¬ (Nat.lcm (d i : ℕ) (e i : ℕ)).Coprime W := by
    exact not_forall.mp hbad
  rcases hex with ⟨i, hi⟩
  have hs : Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) = ∅ :=
    Sset_card_eq_zero_of_not_coprime_W (k := k) (N := N) (W := W) (b := b)
      (H := H) (m := fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) (i := i) (hbW i) hi
  simp [hs]

/-- A pair whose lcm-moduli are not pairwise coprime contributes zero. -/
theorem nonGoodM_pair_contribution_zero {k D N W b wd : ℕ} {H : Fin k → ℕ}
    {d e : Fin k → Fin (D + 1)} {α β : Fin k → ℕ → ℝ}
    (hWdiv : ∀ p : ℕ, p.Prime → p ≤ wd → p ∣ W)
    (hHinj : Function.Injective H) (hbW : ∀ i : Fin k, (b + H i).Coprime W)
    (hsep : ∀ i j : Fin k, i ≠ j → H j - H i < wd)
    (hbad : ¬ ∀ i j : Fin k, i ≠ j →
      (Nat.lcm (d i : ℕ) (e i : ℕ)).Coprime (Nat.lcm (d j : ℕ) (e j : ℕ))) :
    coefProd α β (fun i : Fin k => (d i : ℕ)) (fun i : Fin k => (e i : ℕ)) *
      ((Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))).card : ℝ) = 0 := by
  classical
  have hex : ∃ i : Fin k, ∃ j : Fin k, i ≠ j ∧
      ¬ (Nat.lcm (d i : ℕ) (e i : ℕ)).Coprime (Nat.lcm (d j : ℕ) (e j : ℕ)) := by
    push Not at hbad
    exact hbad
  rcases hex with ⟨i, j, hij, hb⟩
  have hs : Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) = ∅ :=
    Sset_card_eq_zero_of_not_pairwise_coprime (k := k) (N := N) (W := W) (b := b) (wd := wd)
      (H := H) (m := fun i => Nat.lcm (d i : ℕ) (e i : ℕ)) (i := i) (j := j)
      hWdiv hHinj hbW hsep hij hb
  simp [hs]


/-! ## Splitting the divisor-pair sum over good pairs

The `(d,e)`-sum of the expansion is split into the `lcmGood` part and its
complement; the complement contributes zero by the vanishing lemmas, so the
full sum equals the good-restricted sum.  The good part is then ready for the
main-term substitution. -/

/-- Indicator of the good (pairwise-coprime / coprime-to-`W`) divisor pairs. -/
noncomputable def goodInd {k D : ℕ} (W : ℕ) (d e : Fin k → Fin (D + 1)) : ℝ := by
  classical
  exact if lcmGood W d e then 1 else 0

/-- A generic double sum over divisor pairs splits into the good part and its
complement. -/
theorem expansion_sum_split_good {k D : ℕ} (W : ℕ)
    (f : (Fin k → Fin (D + 1)) → (Fin k → Fin (D + 1)) → ℝ) :
    (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)), f d e) =
      (∑ d, ∑ e, goodInd W d e * f d e) +
      (∑ d, ∑ e, (1 - goodInd W d e) * f d e) := by
  classical
  have hterm : ∀ d e : (Fin k → Fin (D + 1)),
      f d e = goodInd W d e * f d e + (1 - goodInd W d e) * f d e := by
    intro d e
    by_cases hg : lcmGood W d e <;> simp [goodInd, hg]
  calc
    (∑ d, ∑ e, f d e) =
        ∑ d, ∑ e, (goodInd W d e * f d e + (1 - goodInd W d e) * f d e) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            refine Finset.sum_congr rfl ?_
            intro e he
            exact hterm d e
    _ = (∑ d, ∑ e, goodInd W d e * f d e) +
        (∑ d, ∑ e, (1 - goodInd W d e) * f d e) := by
            simp [Finset.sum_add_distrib]

/-- The complement of `lcmGood` contributes nothing: each bad pair has empty
`S`-set. -/
theorem expansion_bad_sum_zero {k D N W b wd : ℕ} {H : Fin k → ℕ}
    {α β : Fin k → ℕ → ℝ}
    (hWdiv : ∀ p : ℕ, p.Prime → p ≤ wd → p ∣ W)
    (hHinj : Function.Injective H) (hbW : ∀ i : Fin k, (b + H i).Coprime W)
    (hsep : ∀ i j : Fin k, i ≠ j → H j - H i < wd) :
    (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
      (1 - goodInd W d e) *
        (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
          ((Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))).card : ℝ))) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro e he
  by_cases hG : lcmGood W d e
  · simp [goodInd, hG]
  · have hnot : ¬ (lcmGood W d e) := hG
    by_cases hWgood : ∀ i : Fin k, (Nat.lcm (d i : ℕ) (e i : ℕ)).Coprime W
    · have hMbad : ¬ (∀ i j : Fin k, i ≠ j →
          (Nat.lcm (d i : ℕ) (e i : ℕ)).Coprime (Nat.lcm (d j : ℕ) (e j : ℕ))) := by
        intro hM
        exact hnot (by simpa [lcmGood] using ⟨hWgood, hM⟩)
      have hz : coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
            ((Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))).card : ℝ) = 0 :=
        nonGoodM_pair_contribution_zero (k := k) (D := D) (N := N) (W := W) (b := b)
          (wd := wd) (H := H) (α := α) (β := β) (d := d) (e := e) hWdiv hHinj hbW hsep hMbad
      simp [goodInd, hG, hz]
    · have hz : coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
          ((Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))).card : ℝ) = 0 :=
        nonGoodW_pair_contribution_zero (k := k) (D := D) (N := N) (W := W) (b := b)
          (H := H) (α := α) (β := β) (d := d) (e := e) hbW hWgood
      simp [goodInd, hG, hz]

/-- **Split-and-kill.**  The full divisor-pair sum of the expansion equals its
`lcmGood`-restricted part; the non-good pairs vanish. -/
theorem expansion_sum_eq_good_part {k D N W b wd : ℕ} {H : Fin k → ℕ}
    {α β : Fin k → ℕ → ℝ}
    (hWdiv : ∀ p : ℕ, p.Prime → p ≤ wd → p ∣ W)
    (hHinj : Function.Injective H) (hbW : ∀ i : Fin k, (b + H i).Coprime W)
    (hsep : ∀ i j : Fin k, i ≠ j → H j - H i < wd) :
    (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
      coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
        ((Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))).card : ℝ)) =
    (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
      goodInd W d e *
        (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
          ((Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))).card : ℝ))) := by
  classical
  let f : (Fin k → Fin (D + 1)) → (Fin k → Fin (D + 1)) → ℝ := fun d e =>
    coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
      ((Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))).card : ℝ)
  have hsplit := expansion_sum_split_good (k := k) (D := D) (W := W) (f := f)
  have hbad := expansion_bad_sum_zero (k := k) (D := D) (N := N) (W := W) (b := b) (wd := wd)
    (H := H) (α := α) (β := β) hWdiv hHinj hbW hsep
  dsimp [f] at hsplit hbad
  rw [hsplit, hbad]
  ring


/-! ## The collect step: main term plus controlled error over good pairs

Over each good pair the substitution `Sset_lcm_coefficient_substitution` gives
`coeff·#S = coeff·N/(W·∏ᵢ [dᵢ,eᵢ]) + coeff·err` with `|err| ≤ 2`
(`Sset_lcm_substitution_error_bound`).  This section defines the main and
error sums over good pairs and records the assembly: decomposition of the good
part, the error bound, the full collected statement, and the coefficient
factorization. -/

/-- Main term, summed over good pairs:
`Σ_{good} coeff·N/(W·∏ᵢ lcm (dᵢ) (eᵢ))`. -/
noncomputable def goodMainSum {k D N W : ℕ} (α β : Fin k → ℕ → ℝ) : ℝ :=
  ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
    goodInd W d e *
      (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
        mainTerm N W (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)))

/-- Error term, summed over good pairs:
`Σ_{good} coeff·(#S − N/(W·∏ᵢ lcm))`. -/
noncomputable def goodErrSum {k D N W b : ℕ} (H : Fin k → ℕ) (α β : Fin k → ℕ → ℝ) : ℝ :=
  ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
    goodInd W d e *
      (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
        SsetErr N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)))

/-- The good-part sum decomposes into main term plus error (pure algebra). -/
theorem goodSum_eq_main_add_error {k D N W b : ℕ} {H : Fin k → ℕ} {α β : Fin k → ℕ → ℝ} :
    (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
      goodInd W d e *
        (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
          ((Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))).card : ℝ))) =
    goodMainSum (k := k) (D := D) (N := N) (W := W) (α := α) (β := β) +
    goodErrSum (k := k) (D := D) (N := N) (W := W) (b := b) (H := H) (α := α) (β := β) := by
  classical
  have hterm : ∀ d e : (Fin k → Fin (D + 1)),
      goodInd W d e *
          (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
            ((Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))).card : ℝ)) =
        goodInd W d e *
            (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
              mainTerm N W (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))) +
        goodInd W d e *
            (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
              SsetErr N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))) := by
    intro d e
    dsimp [SsetErr]
    ring
  calc
    (∑ d, ∑ e, goodInd W d e * (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
        ((Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))).card : ℝ)))
        = ∑ d, ∑ e, (goodInd W d e *
              (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
                mainTerm N W (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))) +
            goodInd W d e *
              (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
                SsetErr N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)))) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            refine Finset.sum_congr rfl ?_
            intro e he
            exact hterm d e
    _ = goodMainSum (k := k) (D := D) (N := N) (W := W) (α := α) (β := β) +
        goodErrSum (k := k) (D := D) (N := N) (W := W) (b := b) (H := H) (α := α) (β := β) := by
            simp [goodMainSum, goodErrSum, Finset.sum_add_distrib]

/-- `0` cannot be coprime to a `W ≥ 2`. -/
lemma not_coprime_zero_W {W : ℕ} (hW2 : 2 ≤ W) : ¬ (0 : ℕ).Coprime W := by
  intro h
  have hg : (0 : ℕ).gcd W = 1 := h.gcd_eq_one
  simp at hg
  omega

/-- Coprimality of an lcm with `W ≥ 2` forces both factors to be nonzero. -/
lemma coprime_lcm_ne_zero_left {d e W : ℕ} (hW2 : 2 ≤ W)
    (h : (Nat.lcm d e).Coprime W) : d ≠ 0 := by
  intro hd
  apply not_coprime_zero_W (W := W) hW2
  simpa [hd] using h

lemma coprime_lcm_ne_zero_right {d e W : ℕ} (hW2 : 2 ≤ W)
    (h : (Nat.lcm d e).Coprime W) : e ≠ 0 := by
  intro he
  apply not_coprime_zero_W (W := W) hW2
  simpa [he, Nat.lcm_comm] using h

/-- **Error estimate.**  Over good pairs `|coeff·err| ≤ 2|coeff|`, so the
collected error is bounded by twice the total absolute coefficient sum. -/
theorem goodErrSum_bound {k D N W b : ℕ} {H : Fin k → ℕ} {α β : Fin k → ℕ → ℝ}
    (hW2 : 2 ≤ W) :
    |goodErrSum (k := k) (D := D) (N := N) (W := W) (b := b) (H := H) (α := α) (β := β)| ≤
      2 * (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
        |coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ))|) := by
  classical
  have hWpos : 0 < W := by omega
  have hpair : ∀ d e : (Fin k → Fin (D + 1)),
      |goodInd W d e *
        (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
          SsetErr N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)))| ≤
        2 * |coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ))| := by
    intro d e
    by_cases hg : lcmGood W d e
    · have hg' : (∀ i : Fin k, (Nat.lcm (d i : ℕ) (e i : ℕ)).Coprime W) ∧
          (∀ i j : Fin k, i ≠ j →
            (Nat.lcm (d i : ℕ) (e i : ℕ)).Coprime (Nat.lcm (d j : ℕ) (e j : ℕ))) := by
        simpa [lcmGood] using hg
      have hcopW : ∀ i : Fin k, (Nat.lcm (d i : ℕ) (e i : ℕ)).Coprime W := hg'.1
      have hcopm : ∀ i j : Fin k, i ≠ j →
          (Nat.lcm (d i : ℕ) (e i : ℕ)).Coprime (Nat.lcm (d j : ℕ) (e j : ℕ)) := hg'.2
      have hd : ∀ i : Fin k, (d i : ℕ) ≠ 0 := fun i =>
        coprime_lcm_ne_zero_left (d := (d i : ℕ)) (e := (e i : ℕ)) (W := W) hW2 (hcopW i)
      have he : ∀ i : Fin k, (e i : ℕ) ≠ 0 := fun i =>
        coprime_lcm_ne_zero_right (d := (d i : ℕ)) (e := (e i : ℕ)) (W := W) hW2 (hcopW i)
      have hb := Sset_lcm_substitution_error_bound (k := k) (N := N) (W := W) (b := b)
        (H := H) (d := fun i : Fin k => (d i : ℕ)) (e := fun i : Fin k => (e i : ℕ))
        (α := α) (β := β) hWpos hd he hcopW hcopm
      simpa [goodInd, hg] using hb
    · have hz : goodInd W d e *
          (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
            SsetErr N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))) = 0 := by
        simp [goodInd, hg]
      simp [hz]
  calc
    |goodErrSum (k := k) (D := D) (N := N) (W := W) (b := b) (H := H) (α := α) (β := β)|
        = |∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
            goodInd W d e *
              (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
                SsetErr N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)))| := by
            rfl
    _ ≤ ∑ d : (Fin k → Fin (D + 1)),
          |∑ e : (Fin k → Fin (D + 1)),
            goodInd W d e *
              (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
                SsetErr N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)))| := by
            exact Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin k → Fin (D + 1))))
              (f := fun d => ∑ e : (Fin k → Fin (D + 1)),
                goodInd W d e *
                  (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
                    SsetErr N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))))
    _ ≤ ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
          |goodInd W d e *
            (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
              SsetErr N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)))| := by
            refine Finset.sum_le_sum ?_
            intro d hd
            exact Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin k → Fin (D + 1))))
              (f := fun e => goodInd W d e *
                (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
                  SsetErr N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))))
    _ ≤ ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
          2 * |coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ))| := by
            refine Finset.sum_le_sum ?_
            intro d hd
            refine Finset.sum_le_sum ?_
            intro e he
            exact hpair d e
    _ = 2 * (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
          |coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ))|) := by
            have h : (∑ d : (Fin k → Fin (D + 1)),
                  ∑ e : (Fin k → Fin (D + 1)),
                    (2 : ℝ) * |coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ))|) =
                2 * (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
                  |coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ))|) := by
              calc
                (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
                    (2 : ℝ) * |coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ))|)
                    = ∑ d : (Fin k → Fin (D + 1)), (2 : ℝ) *
                        (∑ e : (Fin k → Fin (D + 1)), |coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ))|) := by
                        apply Finset.sum_congr rfl
                        intro d hd
                        rw [← Finset.mul_sum]
                _ = 2 * (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
                    |coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ))|) := by
                        rw [Finset.mul_sum]
            simpa using h

/-- **Collected.**  Over the residue class window, a product of one-dimensional
divisor-sum products splits into the `lcmGood`-main term
`goodMainSum` (= `Σ_{good} coeff·N/(W·∏ᵢ[dᵢ,eᵢ])`) plus the controlled error
`goodErrSum` (with `|goodErrSum| ≤ 2·Σ_{all}|coeff|` by
`goodErrSum_bound`).  Inputs: the k-coordinate expansion
(`divisorSumProduct_window_eq_k`, commons), the split-and-kill
(`expansion_sum_eq_good_part`), and the algebraic decomposition
(`goodSum_eq_main_add_error`). -/
theorem residueWindowProduct_eq_goodMainSum_add_goodErrSum {k D N W b wd : ℕ}
    {H : Fin k → ℕ} {α β : Fin k → ℕ → ℝ}
    (hWdiv : ∀ p : ℕ, p.Prime → p ≤ wd → p ∣ W)
    (hHinj : Function.Injective H) (hbW : ∀ i : Fin k, (b + H i).Coprime W)
    (hsep : ∀ i j : Fin k, i ≠ j → H j - H i < wd) :
    (∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => n % W = b % W),
        ∏ i : Fin k,
          (∑ d : Fin (D + 1), α i (d : ℕ) * (if (d : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
          (∑ e : Fin (D + 1), β i (e : ℕ) * (if (e : ℕ) ∣ n + H i then (1 : ℝ) else 0))) =
    goodMainSum (k := k) (D := D) (N := N) (W := W) (α := α) (β := β) +
    goodErrSum (k := k) (D := D) (N := N) (W := W) (b := b) (H := H) (α := α) (β := β) := by
  classical
  calc
    (∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => n % W = b % W),
        ∏ i : Fin k,
          (∑ d : Fin (D + 1), α i (d : ℕ) * (if (d : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
          (∑ e : Fin (D + 1), β i (e : ℕ) * (if (e : ℕ) ∣ n + H i then (1 : ℝ) else 0)))
        = ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
            (∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)) *
              ((Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))).card : ℝ) := by
            exact residueWindowProduct_eq_weighted_Sset (k := k) (D := D) (N := N) (W := W)
              (b := b) (H := H) (α := α) (β := β)
    _ = ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
          coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
            ((Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))).card : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            refine Finset.sum_congr rfl ?_
            intro e he
            dsimp [coefProd]
    _ = ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
          goodInd W d e *
            (coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
              ((Sset N W b H (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))).card : ℝ)) := by
            exact expansion_sum_eq_good_part (k := k) (D := D) (N := N) (W := W) (b := b)
              (wd := wd) (H := H) (α := α) (β := β) hWdiv hHinj hbW hsep
    _ = goodMainSum (k := k) (D := D) (N := N) (W := W) (α := α) (β := β) +
        goodErrSum (k := k) (D := D) (N := N) (W := W) (b := b) (H := H) (α := α) (β := β) := by
            exact goodSum_eq_main_add_error (k := k) (D := D) (N := N) (W := W) (b := b)
              (H := H) (α := α) (β := β)

/-- **Coefficient factorization.**  The total absolute coefficient sum over
all divisor pairs factors as `(∏ᵢ Σ|αᵢ|)·(∏ᵢ Σ|βᵢ|)` (via the fleet's
`sum_pi_prod_abs`). -/
theorem abs_coefProd_sum_factor {k D : ℕ} {α β : Fin k → ℕ → ℝ} :
    (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
      |coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ))|) =
    (∏ i : Fin k, ∑ y : Fin (D + 1), |α i (y : ℕ)|) *
    (∏ i : Fin k, ∑ y : Fin (D + 1), |β i (y : ℕ)|) := by
  classical
  have hcoef : ∀ d e : (Fin k → Fin (D + 1)),
      |coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ))| =
        (∏ i : Fin k, |α i (d i : ℕ)|) * (∏ i : Fin k, |β i (e i : ℕ)|) := by
    intro d e
    dsimp [coefProd]
    calc
      |∏ i : Fin k, α i (d i : ℕ) * β i (e i : ℕ)|
          = ∏ i : Fin k, |α i (d i : ℕ) * β i (e i : ℕ)| := by
              simpa using (Finset.abs_prod (s := (Finset.univ : Finset (Fin k)))
                (f := fun i => α i (d i : ℕ) * β i (e i : ℕ)))
      _ = (∏ i : Fin k, |α i (d i : ℕ)|) * (∏ i : Fin k, |β i (e i : ℕ)|) := by
              have h1 : (∏ i : Fin k, |α i (d i : ℕ) * β i (e i : ℕ)|) =
                  ∏ i : Fin k, (|α i (d i : ℕ)| * |β i (e i : ℕ)|) := by
                  apply Finset.prod_congr rfl
                  intro i hi
                  rw [abs_mul]
              rw [h1, Finset.prod_mul_distrib]
  calc
    (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
        |coefProd α β (fun i => (d i : ℕ)) (fun i => (e i : ℕ))|)
        = ∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
            (∏ i : Fin k, |α i (d i : ℕ)|) * (∏ i : Fin k, |β i (e i : ℕ)|) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            refine Finset.sum_congr rfl ?_
            intro e he
            exact hcoef d e
    _ = ∑ d : (Fin k → Fin (D + 1)), (∏ i : Fin k, |α i (d i : ℕ)|) *
          (∑ e : (Fin k → Fin (D + 1)), ∏ i : Fin k, |β i (e i : ℕ)|) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            rw [← Finset.mul_sum]
    _ = (∑ d : (Fin k → Fin (D + 1)), ∏ i : Fin k, |α i (d i : ℕ)|) *
        (∑ e : (Fin k → Fin (D + 1)), ∏ i : Fin k, |β i (e i : ℕ)|) := by
            rw [← Finset.sum_mul]
    _ = (∏ i : Fin k, ∑ y : Fin (D + 1), |α i (y : ℕ)|) *
        (∏ i : Fin k, ∑ y : Fin (D + 1), |β i (y : ℕ)|) := by
            congr 1
            · have hA : (∑ d : (Fin k → Fin (D + 1)), ∏ i : Fin k, |α i (d i : ℕ)|) =
                  ∏ i : Fin k, ∑ y : Fin (D + 1), |α i (y : ℕ)| := by
                  have h := Commons.Algebra.BigOperators.sum_pi_prod_abs (ι := Fin k)
                    (κ := fun _ : Fin k => Fin (D + 1)) (a := fun i y => |α i (y : ℕ)|)
                  simpa using h
              rw [hA]
            · have hB : (∑ e : (Fin k → Fin (D + 1)), ∏ i : Fin k, |β i (e i : ℕ)|) =
                  ∏ i : Fin k, ∑ y : Fin (D + 1), |β i (y : ℕ)| := by
                  have h := Commons.Algebra.BigOperators.sum_pi_prod_abs (ι := Fin k)
                    (κ := fun _ : Fin k => Fin (D + 1)) (a := fun i y => |β i (y : ℕ)|)
                  simpa using h
              rw [hB]

end Commons.NumberTheory.MaynardSieve

namespace Commons.NumberTheory.MaynardSieve

/-! ## The Maynard divisor weights

The actual sieve sets the per-coordinate weights to the one-dimensional
Maynard divisor weights `αᵢ(d) := μ(d)·Fᵢ(log d / log R)` (and likewise
`βᵢ(e) := μ(e)·Gᵢ(log e / log R)`), where `μ` is the Möbius function and
`Fᵢ, Gᵢ` are smooth cutoffs (Polymath8a (16)).  This section records that
instantiation of the collected decomposition; the weights vanish on `d = 0`
(since `μ(0) = 0`), matching divisor sums over `d ≥ 1`. -/

/-- Möbius μ as a real number. -/
noncomputable def moebiusReal (d : ℕ) : ℝ := (ArithmeticFunction.moebius d : ℝ)

/-- The one-dimensional Maynard divisor weight `μ(d)·F(log d / log R)`. -/
noncomputable def lamDivWeight (F : ℝ → ℝ) (R d : ℕ) : ℝ :=
  moebiusReal d * F (Real.log (d : ℝ) / Real.log (R : ℝ))

/-- **Weight-instantiated decomposition.**  The residue-window product of the
Maynard divisor sums `λ_{Fᵢ}·λ_{Gᵢ}` equals `goodMainSum + goodErrSum` with
the weights `αᵢ = μ·Fᵢ(log_R ·)`, `βᵢ = μ·Gᵢ(log_R ·)`. -/
theorem windowLambdaProduct_eq_main_add_error {k D N W b wd R : ℕ} {H : Fin k → ℕ}
    {F G : Fin k → ℝ → ℝ}
    (hWdiv : ∀ p : ℕ, p.Prime → p ≤ wd → p ∣ W)
    (hHinj : Function.Injective H) (hbW : ∀ i : Fin k, (b + H i).Coprime W)
    (hsep : ∀ i j : Fin k, i ≠ j → H j - H i < wd) :
    (∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => n % W = b % W),
        ∏ i : Fin k,
          (∑ d : Fin (D + 1),
            lamDivWeight (F i) R (d : ℕ) * (if (d : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
          (∑ e : Fin (D + 1),
            lamDivWeight (G i) R (e : ℕ) * (if (e : ℕ) ∣ n + H i then (1 : ℝ) else 0))) =
    goodMainSum (k := k) (D := D) (N := N) (W := W)
      (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d) +
    goodErrSum (k := k) (D := D) (N := N) (W := W) (b := b) (H := H)
      (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d) := by
  classical
  exact residueWindowProduct_eq_goodMainSum_add_goodErrSum (k := k) (D := D) (N := N)
    (W := W) (b := b) (wd := wd) (H := H)
    (α := fun i d => lamDivWeight (F i) R d) (β := fun i d => lamDivWeight (G i) R d)
    hWdiv hHinj hbW hsep

end Commons.NumberTheory.MaynardSieve

namespace Commons.NumberTheory.MaynardSieve

/-! ## Möbius structure of the Maynard weights

With `αᵢ(d) = μ(d)·Fᵢ(log_R d)`, the coefficient of a divisor pair factors as
`(∏ᵢ μ(dᵢ)μ(eᵢ))·(∏ᵢ Fᵢ(log_R dᵢ)Gᵢ(log_R eᵢ))`, and it vanishes unless every
coordinate `dᵢ, eᵢ` is squarefree (since `μ(n) = 0` for non-squarefree `n`).
These are the elementary facts behind writing the main sum over squarefree
divisors only (P8 Lemma 4.1's sum). -/

/-- For Maynard weights the pair coefficient factors into the product of the
Möbius values and the product of the smooth cutoffs. -/
theorem coefProd_lamDiv_eq {k : ℕ} (F G : Fin k → ℝ → ℝ) (R : ℕ)
    (d e : Fin k → ℕ) :
    coefProd (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d) d e =
      (∏ i : Fin k, moebiusReal (d i) * moebiusReal (e i)) *
      (∏ i : Fin k, F i (Real.log (d i : ℝ) / Real.log (R : ℝ)) *
        G i (Real.log (e i : ℝ) / Real.log (R : ℝ))) := by
  classical
  unfold coefProd lamDivWeight
  calc
    (∏ i : Fin k, (moebiusReal (d i) * F i (Real.log (d i : ℝ) / Real.log (R : ℝ))) *
        (moebiusReal (e i) * G i (Real.log (e i : ℝ) / Real.log (R : ℝ))))
        = ∏ i : Fin k, (moebiusReal (d i) * moebiusReal (e i)) *
            (F i (Real.log (d i : ℝ) / Real.log (R : ℝ)) *
              G i (Real.log (e i : ℝ) / Real.log (R : ℝ))) := by
            apply Finset.prod_congr rfl
            intro i hi
            ring
    _ = (∏ i : Fin k, moebiusReal (d i) * moebiusReal (e i)) *
        (∏ i : Fin k, F i (Real.log (d i : ℝ) / Real.log (R : ℝ)) *
          G i (Real.log (e i : ℝ) / Real.log (R : ℝ))) := by
            rw [Finset.prod_mul_distrib]

/-- A non-squarefree coordinate kills the coefficient (μ's support is the
squarefree numbers). -/
theorem coefProd_lamDiv_eq_zero_of_not_squarefree {k : ℕ} {F G : Fin k → ℝ → ℝ}
    (R : ℕ) {d e : Fin k → ℕ} {i : Fin k} (hd : ¬ Squarefree (d i)) :
    coefProd (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d) d e = 0 := by
  classical
  have hμ : (ArithmeticFunction.moebius (d i) : ℝ) = 0 := by
    have hz : ArithmeticFunction.moebius (d i) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd
    simp [hz]
  rw [coefProd_lamDiv_eq]
  have hzero : (∏ j : Fin k, moebiusReal (d j) * moebiusReal (e j)) = 0 := by
    have hz0 : moebiusReal (d i) * moebiusReal (e i) = 0 := by
      simp [moebiusReal, hμ]
    exact Finset.prod_eq_zero (s := (Finset.univ : Finset (Fin k)))
      (f := fun j => moebiusReal (d j) * moebiusReal (e j)) (i := i) (Finset.mem_univ i) hz0
  rw [hzero]
  ring

/-- The dual statement: a non-squarefree coordinate of the second factor kills
the coefficient. -/
theorem coefProd_lamDiv_eq_zero_of_not_squarefree_right {k : ℕ} {F G : Fin k → ℝ → ℝ}
    (R : ℕ) {d e : Fin k → ℕ} {i : Fin k} (he : ¬ Squarefree (e i)) :
    coefProd (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d) d e = 0 := by
  classical
  have hμ : (ArithmeticFunction.moebius (e i) : ℝ) = 0 := by
    have hz : ArithmeticFunction.moebius (e i) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree he
    simp [hz]
  rw [coefProd_lamDiv_eq]
  have hzero : (∏ j : Fin k, moebiusReal (d j) * moebiusReal (e j)) = 0 := by
    have hz0 : moebiusReal (d i) * moebiusReal (e i) = 0 := by
      simp [moebiusReal, hμ]
    exact Finset.prod_eq_zero (s := (Finset.univ : Finset (Fin k)))
      (f := fun j => moebiusReal (d j) * moebiusReal (e j)) (i := i) (Finset.mem_univ i) hz0
  rw [hzero]
  ring

end Commons.NumberTheory.MaynardSieve

namespace Commons.NumberTheory.MaynardSieve

/-! ## Sum-level squarefree restriction

Since `coefProd(μ·Fᵢ, μ·Gᵢ)` vanishes unless every coordinate `dᵢ, eᵢ` is
squarefree, the whole double sum over divisor pairs equals the same sum
restricted (by the classical indicator `sqInd`) to all-squarefree tuples.  This
is the statement the `goodMainSum(μF, μG)` identification will consume. -/

/-- A divisor pair is *all-squarefree* when every coordinate is squarefree. -/
def allSqfree {k D : ℕ} (d e : Fin k → Fin (D + 1)) : Prop :=
  (∀ i : Fin k, Squarefree (d i : ℕ)) ∧ (∀ i : Fin k, Squarefree (e i : ℕ))

/-- Classical indicator of the all-squarefree pairs. -/
noncomputable def sqInd {k D : ℕ} (d e : Fin k → Fin (D + 1)) : ℝ := by
  classical
  exact if allSqfree d e then 1 else 0

/-- Pointwise: the Maynard coefficient times any `X` equals the all-squarefree
indicator times itself (non-squarefree pairs vanish). -/
lemma coefProd_lamDiv_mul_eq_sqInd {k D : ℕ} {F G : Fin k → ℝ → ℝ} (R : ℕ)
    {d e : Fin k → Fin (D + 1)} (X : ℝ) :
    coefProd (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d)
        (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) * X =
      sqInd d e *
        (coefProd (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d)
          (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) * X) := by
  classical
  by_cases hs : allSqfree d e
  · simp [sqInd, hs]
  · have hzero : coefProd (fun i d => lamDivWeight (F i) R d)
        (fun i d => lamDivWeight (G i) R d) (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) = 0 := by
      by_cases hA : ∀ i : Fin k, Squarefree (d i : ℕ)
      · have hB : ¬ ∀ i : Fin k, Squarefree (e i : ℕ) := by
          intro hB'
          exact hs ⟨hA, hB'⟩
        have hex : ∃ i : Fin k, ¬ Squarefree (e i : ℕ) := not_forall.mp hB
        rcases hex with ⟨i, hi⟩
        exact coefProd_lamDiv_eq_zero_of_not_squarefree_right (R := R) (i := i) hi
      · have hex : ∃ i : Fin k, ¬ Squarefree (d i : ℕ) := not_forall.mp hA
        rcases hex with ⟨i, hi⟩
        exact coefProd_lamDiv_eq_zero_of_not_squarefree (R := R) (i := i) hi
    simp [sqInd, hs, hzero]

/-- **Squarefree restriction.**  The double sum of the Maynard coefficients
(weighted by any `X`) equals the same sum restricted to all-squarefree tuples;
non-squarefree pairs contribute zero. -/
theorem lamDiv_coef_sum_eq_sqfree {k D : ℕ} {F G : Fin k → ℝ → ℝ} {R : ℕ}
    (X : (Fin k → Fin (D + 1)) → (Fin k → Fin (D + 1)) → ℝ) :
    (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
        coefProd (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d)
            (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) * X d e) =
    (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
        sqInd d e *
          (coefProd (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d)
            (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) * X d e)) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro d hd
  refine Finset.sum_congr rfl ?_
  intro e he
  exact coefProd_lamDiv_mul_eq_sqInd (R := R) (X := X d e)

end Commons.NumberTheory.MaynardSieve

namespace Commons.NumberTheory.MaynardSieve

/-! ## Möbius signs over squarefree coordinates

On all-squarefree coordinates the surviving `∏ᵢ μ(dᵢ)μ(eᵢ)` becomes the sign
factor `(-1)^(Σᵢ (cardFactors dᵢ + cardFactors eᵢ))`, via
`moebius_apply_of_squarefree` (`μ(n) = (-1)^{cardFactors n}`). -/

/-- `∏` over a finite set of `a ^ (f i)` equals `a ^ (Σ f i)`. -/
lemma prod_pow_eq_pow_sum {α : Type*} {M : Type*} [CommMonoid M] [DecidableEq α]
    (s : Finset α) (a : M) (f : α → ℕ) :
    (∏ i ∈ s, a ^ f i) = a ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s' hx ih =>
      rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, pow_add]

/-- Casting `(-1 : ℤ) ^ n` to ℝ gives `(-1 : ℝ) ^ n`. -/
lemma Int_neg_one_pow_cast (n : ℕ) : (((-1 : ℤ) ^ n : ℤ) : ℝ) = (-1 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        (((-1 : ℤ) ^ (n + 1) : ℤ) : ℝ) = (((-1 : ℤ) ^ n * (-1 : ℤ) : ℤ) : ℝ) := by rw [pow_succ]
        _ = (((-1 : ℤ) ^ n : ℤ) : ℝ) * ((-1 : ℤ) : ℝ) := by norm_num
        _ = (-1 : ℝ) ^ n * (-1 : ℝ) := by rw [ih]; norm_num
        _ = (-1 : ℝ) ^ (n + 1) := by rw [pow_succ]

/-- For squarefree `n`, `μ(n) = (-1)^{cardFactors n}` as a real. -/
lemma moebiusReal_squarefree {n : ℕ} (h : Squarefree n) :
    moebiusReal n = (-1 : ℝ) ^ ArithmeticFunction.cardFactors n := by
  have hm : ArithmeticFunction.moebius n = (-1) ^ ArithmeticFunction.cardFactors n :=
    ArithmeticFunction.moebius_apply_of_squarefree h
  have hc : (ArithmeticFunction.moebius n : ℝ) =
      (((-1 : ℤ) ^ ArithmeticFunction.cardFactors n : ℤ) : ℝ) := by
    exact congrArg (fun z : ℤ => (z : ℝ)) hm
  unfold moebiusReal
  rw [hc, Int_neg_one_pow_cast]

/-- On all-squarefree coordinates the Maynard coefficient is the sign factor
times the product of the smooth cutoffs. -/
theorem lamDiv_coef_sqfree_sign {k D : ℕ} {F G : Fin k → ℝ → ℝ} (R : ℕ)
    {d e : Fin k → Fin (D + 1)}
    (hds : ∀ i : Fin k, Squarefree (d i : ℕ))
    (hes : ∀ i : Fin k, Squarefree (e i : ℕ)) :
    coefProd (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d)
        (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) =
      ((-1 : ℝ) ^ (∑ i : Fin k,
        (ArithmeticFunction.cardFactors (d i : ℕ) + ArithmeticFunction.cardFactors (e i : ℕ)))) *
      (∏ i : Fin k, F i (Real.log (d i : ℝ) / Real.log (R : ℝ)) *
        G i (Real.log (e i : ℝ) / Real.log (R : ℝ))) := by
  classical
  rw [coefProd_lamDiv_eq]
  congr 1
  · have hmui : ∀ i : Fin k,
        moebiusReal (d i : ℕ) * moebiusReal (e i : ℕ) =
          (-1 : ℝ) ^ (ArithmeticFunction.cardFactors (d i : ℕ) +
            ArithmeticFunction.cardFactors (e i : ℕ)) := by
        intro i
        rw [moebiusReal_squarefree (hds i), moebiusReal_squarefree (hes i), pow_add]
    calc
      (∏ i : Fin k, moebiusReal (d i : ℕ) * moebiusReal (e i : ℕ))
          = ∏ i : Fin k, (-1 : ℝ) ^ (ArithmeticFunction.cardFactors (d i : ℕ) +
              ArithmeticFunction.cardFactors (e i : ℕ)) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              exact hmui i
      _ = (-1 : ℝ) ^ (∑ i : Fin k,
            (ArithmeticFunction.cardFactors (d i : ℕ) + ArithmeticFunction.cardFactors (e i : ℕ))) := by
              have hgen := prod_pow_eq_pow_sum (s := (Finset.univ : Finset (Fin k)))
                (a := (-1 : ℝ)) (f := fun i => ArithmeticFunction.cardFactors (d i : ℕ) +
                  ArithmeticFunction.cardFactors (e i : ℕ))
              simpa using hgen

end Commons.NumberTheory.MaynardSieve

namespace Commons.NumberTheory.MaynardSieve

/-! ## Assembly: the Maynard main sum is all-squarefree

Instantiating the pointwise squarefree identity at
`X d e := goodInd W d e · mainTerm N W (lcm-moduli d e)` turns
`goodMainSum(μ·Fᵢ(log_R·), μ·Gᵢ(log_R·))` into the same sum over
all-squarefree pairs only — the exact object whose Möbius signs
`lamDiv_coef_sqfree_sign` rewrites, and which the P8 Lemma 4.1 identification
will consume. -/

/-- **Assembly.**  The `goodMainSum` with Maynard divisor weights equals its
all-squarefree restriction (non-squarefree pairs contribute zero through the
Möbius support). -/
theorem goodMainSum_lamDiv_eq_sqfree {k D N W : ℕ} {F G : Fin k → ℝ → ℝ} {R : ℕ} :
    goodMainSum (k := k) (D := D) (N := N) (W := W)
        (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d) =
      (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
        sqInd d e * goodInd W d e *
          (coefProd (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d)
            (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
          mainTerm N W (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)))) := by
  classical
  dsimp [goodMainSum]
  refine Finset.sum_congr rfl ?_
  intro d hd
  refine Finset.sum_congr rfl ?_
  intro e he
  -- LHS summand: goodInd·(coefProd·main); RHS summand: sqInd·goodInd·(coefProd·main)
  calc
    goodInd W d e *
        (coefProd (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d)
          (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
        mainTerm N W (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)))
        = coefProd (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d)
            (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
            (goodInd W d e * mainTerm N W (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))) := by
            ring
    _ = sqInd d e *
          (coefProd (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d)
            (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
          (goodInd W d e * mainTerm N W (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)))) := by
            exact coefProd_lamDiv_mul_eq_sqInd (R := R)
              (X := goodInd W d e * mainTerm N W (fun i => Nat.lcm (d i : ℕ) (e i : ℕ)))
    _ = sqInd d e * goodInd W d e *
          (coefProd (fun i d => lamDivWeight (F i) R d) (fun i d => lamDivWeight (G i) R d)
            (fun i => (d i : ℕ)) (fun i => (e i : ℕ)) *
          mainTerm N W (fun i => Nat.lcm (d i : ℕ) (e i : ℕ))) := by
            ring

end Commons.NumberTheory.MaynardSieve

namespace Commons.NumberTheory.MaynardSieve

/-! ## Coordinate factorization (the Lemma 4.1 rearrangement)

P8 Lemma 4.1's sum (36) is a product over coordinates: its summand is
`∏ᵢ μ(dᵢ)μ(d′ᵢ)Fᵢ(log_x dᵢ)Gᵢ(log_x d′ᵢ)/[dᵢ,d′ᵢ]`, so the whole k-fold sum
factors into `∏ᵢ` of single-coordinate sums (given per-coordinate restrictions).
The lemmas here provide that pure rearrangement: sums of products over
coordinate functions factor into products of coordinate sums, and the
all-squarefree indicator `sqInd` is the product over coordinates of the
per-coordinate squarefree indicators. -/

/-- Sum over coordinate pairs of a product over coordinates equals the product
of the single-coordinate pair sums. -/
theorem sum_prod_coord {k D : ℕ} (u : Fin (D + 1) → Fin (D + 1) → ℝ) :
    (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
        ∏ i : Fin k, u (d i) (e i)) =
    ∏ i : Fin k, ∑ a : Fin (D + 1), ∑ b : Fin (D + 1), u a b := by
  classical
  calc
    (∑ d : (Fin k → Fin (D + 1)), ∑ e : (Fin k → Fin (D + 1)),
        ∏ i : Fin k, u (d i) (e i))
        = ∑ d : (Fin k → Fin (D + 1)), ∏ i : Fin k, ∑ b : Fin (D + 1), u (d i) b := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            exact (Fintype.prod_sum (ι := Fin k) (κ := fun _ : Fin k => Fin (D + 1))
              (f := fun i y => u (d i) y)).symm
    _ = ∏ i : Fin k, ∑ a : Fin (D + 1), ∑ b : Fin (D + 1), u a b := by
            exact (Fintype.prod_sum (ι := Fin k) (κ := fun _ : Fin k => Fin (D + 1))
              (f := fun i a => ∑ b : Fin (D + 1), u a b)).symm

/-- Casting a finite product of naturals to ℝ. -/
lemma natProd_cast {ι : Type*} (s : Finset ι) (m : ι → ℕ) :
    ((s.prod m : ℕ) : ℝ) = s.prod (fun i => (m i : ℝ)) := by
  classical
  induction s using Finset.induction_on with
  | empty => norm_num
  | insert x s' hx ih => simp [Finset.prod_insert hx, ih]

/-- Product of two boolean indicators over a finite type. -/
lemma prod_ite_two_indicators {ι : Type*} [Fintype ι] (u v : ι → Prop)
    [DecidablePred u] [DecidablePred v] :
    (∏ i : ι, (if u i then (1 : ℝ) else 0) * (if v i then (1 : ℝ) else 0)) =
      if (∀ i, u i) ∧ (∀ i, v i) then (1 : ℝ) else 0 := by
  classical
  calc
    (∏ i : ι, (if u i then (1 : ℝ) else 0) * (if v i then (1 : ℝ) else 0))
        = (∏ i : ι, if u i then (1 : ℝ) else 0) * (∏ i : ι, if v i then (1 : ℝ) else 0) := by
            rw [Finset.prod_mul_distrib]
    _ = (if (∀ i, u i) then (1 : ℝ) else 0) * (if (∀ i, v i) then (1 : ℝ) else 0) := by
            rw [Finset.prod_boole, Finset.prod_boole]
            simp
    _ = if (∀ i, u i) ∧ (∀ i, v i) then (1 : ℝ) else 0 := by
            by_cases hu : ∀ i, u i <;> by_cases hv : ∀ i, v i <;> simp [hu, hv]

/-- The all-squarefree indicator is the product over coordinates of the
per-coordinate squarefree indicators (of `d` and `e`). -/
lemma sqInd_eq_prod {k D : ℕ} {d e : Fin k → Fin (D + 1)} :
    sqInd d e =
      ∏ i : Fin k,
        ((if Squarefree (d i : ℕ) then (1 : ℝ) else 0) *
          (if Squarefree (e i : ℕ) then (1 : ℝ) else 0)) := by
  classical
  unfold sqInd allSqfree
  by_cases hc : (∀ i : Fin k, Squarefree (d i : ℕ)) ∧ (∀ i : Fin k, Squarefree (e i : ℕ))
  · have hu : ∀ i : Fin k, Squarefree (d i : ℕ) := hc.1
    have hv : ∀ i : Fin k, Squarefree (e i : ℕ) := hc.2
    simp [hc, hu, hv]
  · have hz : (∏ i : Fin k,
          ((if Squarefree (d i : ℕ) then (1 : ℝ) else 0) *
            (if Squarefree (e i : ℕ) then (1 : ℝ) else 0))) = 0 := by
      by_cases hA : ∀ i : Fin k, Squarefree (d i : ℕ)
      · have hB : ¬ ∀ i : Fin k, Squarefree (e i : ℕ) := by
          intro hB'
          exact hc ⟨hA, hB'⟩
        have hex : ∃ i : Fin k, ¬ Squarefree (e i : ℕ) := not_forall.mp hB
        rcases hex with ⟨i, hi⟩
        have hf : (if Squarefree (d i : ℕ) then (1 : ℝ) else 0) *
            (if Squarefree (e i : ℕ) then (1 : ℝ) else 0) = 0 := by simp [hA i, hi]
        exact Finset.prod_eq_zero (s := (Finset.univ : Finset (Fin k)))
          (f := fun j => (if Squarefree (d j : ℕ) then (1 : ℝ) else 0) *
            (if Squarefree (e j : ℕ) then (1 : ℝ) else 0)) (i := i) (Finset.mem_univ i) hf
      · have hex : ∃ i : Fin k, ¬ Squarefree (d i : ℕ) := not_forall.mp hA
        rcases hex with ⟨i, hi⟩
        have hf : (if Squarefree (d i : ℕ) then (1 : ℝ) else 0) *
            (if Squarefree (e i : ℕ) then (1 : ℝ) else 0) = 0 := by simp [hi]
        exact Finset.prod_eq_zero (s := (Finset.univ : Finset (Fin k)))
          (f := fun j => (if Squarefree (d j : ℕ) then (1 : ℝ) else 0) *
            (if Squarefree (e j : ℕ) then (1 : ℝ) else 0)) (i := i) (Finset.mem_univ i) hf
    rw [if_neg hc, hz]

end Commons.NumberTheory.MaynardSieve

namespace Commons.NumberTheory.MaynardSieve

/-! ## Factorization of the main term

`mainTerm N W m = N/(W·∏ᵢ mᵢ)` factors per coordinate as
`(N/W)·∏ᵢ 1/mᵢ`, turning the `goodMainSum` denominator into a product over
coordinates — the shape P8 Lemma 4.1's per-coordinate sum (36) requires. -/

/-- The main term `N/(W·∏ᵢ mᵢ)` factors as `(N/W)·∏ᵢ (1/mᵢ)`. -/
theorem mainTerm_factor {k N W : ℕ} (hW : W ≠ 0) {m : Fin k → ℕ}
    (hm : ∀ i : Fin k, m i ≠ 0) :
    mainTerm N W m = (N : ℝ) / (W : ℝ) * ∏ i : Fin k, (((m i : ℕ) : ℝ))⁻¹ := by
  classical
  unfold mainTerm
  have hp : ((∏ i : Fin k, m i : ℕ) : ℝ) = ∏ i : Fin k, ((m i : ℕ) : ℝ) := by
    simpa using (natProd_cast (Finset.univ : Finset (Fin k)) m)
  have hden : (((W * (∏ i : Fin k, m i) : ℕ) : ℝ)) =
      (W : ℝ) * (∏ i : Fin k, ((m i : ℕ) : ℝ)) := by
    rw [Nat.cast_mul]
    rw [hp]
  rw [hden]
  have hWr : (W : ℝ) ≠ 0 := by exact_mod_cast hW
  have hmi : ∀ i : Fin k, ((m i : ℕ) : ℝ) ≠ 0 := fun i => by exact_mod_cast (hm i)
  have hprod : (∏ i : Fin k, ((m i : ℕ) : ℝ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => hmi i)
  have hinv : (∏ i : Fin k, ((m i : ℕ) : ℝ)) *
      ∏ i : Fin k, (((m i : ℕ) : ℝ))⁻¹ = 1 := by
    calc
      (∏ i : Fin k, ((m i : ℕ) : ℝ)) * (∏ i : Fin k, (((m i : ℕ) : ℝ))⁻¹)
          = ∏ i : Fin k, (((m i : ℕ) : ℝ) * (((m i : ℕ) : ℝ))⁻¹) := by
              exact (Finset.prod_mul_distrib (s := (Finset.univ : Finset (Fin k)))
                (f := fun i => ((m i : ℕ) : ℝ))
                (g := fun i => (((m i : ℕ) : ℝ))⁻¹)).symm
      _ = ∏ i : Fin k, (1 : ℝ) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              exact mul_inv_cancel₀ (hmi i)
      _ = 1 := by simp
  field_simp [hWr, hprod, hmi]
  have hQ : (∏ i : Fin k, 1 / ((m i : ℕ) : ℝ)) =
      ∏ i : Fin k, (((m i : ℕ) : ℝ))⁻¹ := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    rw [one_div]
  rw [mul_assoc, hQ, hinv, mul_one]

end Commons.NumberTheory.MaynardSieve

/-! ## Boundary marker: the P8 Lemma 4.1 evaluation is the next subproject

Everything algebraic through the coordinate-factorized Maynard main sum is on
disk above.  What remains to *match Lemma 4.1* is analytic, not algebraic:

  * the per-coordinate multiplicative sum
      Z(F, G) := Σ_{d,d′ ≥ 1, ([d,d′], WN) = 1} μ(d)μ(d′) F(log_R d) G(log_R d′)
                 / [d, d′]
    (with F, G smooth cutoffs) must be evaluated as
      Z(F, G) = (1 + o(1)) · B⁻¹ · N/φ(N) · ∫₀^∞ F′(t) G′(t) dt,
    B := φ(W)/W · log R,  matching P8 Lemma 4.1 (36) per coordinate;
  * its proof decomposes into: (i) the Fourier representation of the smooth
    cutoff (P8 (37)); (ii) the Euler product of the modified zeta
    `ζ_{WN}(s) := ∏_{p ∤ WN} (1 - p⁻ˢ)⁻¹` and its simple pole at s = 1;
    (iii) truncation/error estimates reducing the ξ-integrals to the pole
    contribution `∫ F′G′ · B⁻¹ · N/φ(N)`.

That is a separate analytic-number-theory campaign (formal home suggested:
`Submission/Lemma41.lean` plus commons `NumberTheory.Zeta.*` helpers).  The
product-form main sum above is its clean input; nothing further should be
added to this file until Lemma 4.1 exists. -/
