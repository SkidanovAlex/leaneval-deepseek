import Mathlib
import Submission.Refine
import Submission.Refine2
import Submission.Ell2UpdateMain

open Submission.L2Norm

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Prop refinement, part 3: the phase-1 per-step counting instantiation

Tikhomirov 2020, Section 3 (`prop: refinement`, proof lines ~1330–1370).

At each mixing step `i` of Prop refinement, conditioned on the past (so that
`g := g_{i−1}` is fixed), either `Event_{i−1}` holds — every `N`-interval has at
most `μN` points with `g ≥ H := L/(2N√n)` — or `g` has an `N`-interval with at
least `μN` points at `≥ H ≥ 8R` (`R := Rt/(N√n)`, valid since `L ≥ 16Rt`), in
which case the counting form of Prop ell-2 update
(`Ell2Greedy.ell2_update_counting`) applies with `g₁ = g₂ = g` and yields:
all but `1024μ|J|` of the shifts `y ∈ J` produce the single-step ℓ₂-drop
`‖g₁,y‖₂² ≤ ‖g‖₂² − (1/2)p(1−p)μ⁶Rt²/(Nn)`.

This module proves that per-step counting lemma (`step_bad_count`), plus the
small `Ĩ = I₀ ∪ (I₀+N)` window-splitting lemma feeding its mass hypothesis.
Binomial-tail counting, the (a)-or-(b) export and the phase-2 walk are separate
later steps.
-/

namespace Submission.Refine3

attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- `Ĩ = Icc lo (lo+2N−1)` splits into `I₀ lo N` and `I₀ (lo+N) N`. -/
lemma It_eq_union (lo : ℤ) (N : ℕ) :
    Ell2Greedy.It lo N = Ell2Greedy.I0 lo N ∪ Ell2Greedy.I0 (lo + (N : ℤ)) N := by
  ext t
  rw [Finset.mem_union]
  rw [Ell2Greedy.mem_It]
  rw [Ell2Greedy.mem_I0]
  rw [Ell2Greedy.mem_I0]
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩
    by_cases ht : t ≤ lo + (N : ℤ) - 1
    · left
      exact ⟨h1, ht⟩
    · right
      constructor <;> omega
  · intro h
    rcases h with h | h
    · rcases h with ⟨h1, h2⟩
      constructor <;> omega
    · rcases h with ⟨h1, h2⟩
      constructor <;> omega

/-- the two halves of `Ĩ` are disjoint. -/
lemma It_halves_disjoint (lo : ℤ) (N : ℕ) :
    Disjoint (Ell2Greedy.I0 lo N) (Ell2Greedy.I0 (lo + (N : ℤ)) N) := by
  rw [Finset.disjoint_left]
  intro t ht₁ ht₂
  rw [Ell2Greedy.mem_I0] at ht₁ ht₂
  omega

/-- the window sum over `Ĩ` is the sum of the two halves. -/
lemma sum_It_split {f : ℤ → ℝ} (lo : ℤ) (N : ℕ) :
    (∑ t ∈ Ell2Greedy.It lo N, f t) =
      (∑ t ∈ Ell2Greedy.I0 lo N, f t) + (∑ t ∈ Ell2Greedy.I0 (lo + (N : ℤ)) N, f t) := by
  rw [It_eq_union lo N]
  rw [Finset.sum_union (It_halves_disjoint lo N)]

/-- (phase-1 per-step counting) conditioned on a fixed level function `g`, if
`g` is NOT flat (some `N`-interval has more than `μN` points `≥ H =
L/(2N√n)`), then for the interval `J = Icc c d` with `|J| ≥ N`, all but
`1024μ|J|` shifts `y ∈ J` satisfy the single-step ℓ₂-drop
`‖(1−p)g + p·g(·+y)‖₂² ≤ ‖g‖₂² − (1/2)p(1−p)μ⁶Rt²/(Nn)`. -/
theorem step_bad_count {g : ℤ → ℝ} {p : unitInterval} {Rt μ L : ℝ} {N n : ℕ} {c d : ℤ}
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2)
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64)
    (hR0 : 0 < Rt) (hN1 : 1 ≤ N) (hn1 : 1 ≤ n)
    (hL16 : 16 * Rt ≤ L)
    (hg0 : ∀ t : ℤ, 0 ≤ g t)
    (hg2 : Summable (fun t : ℤ => (g t) ^ 2))
    (hlip : Ell2Update.ratioLip (μ ^ 4) g)
    (hmass : ∀ lo : ℤ, (∑ t ∈ Ell2Greedy.I0 lo N, g t) ≤ Rt / Real.sqrt (n : ℝ))
    (hJlen : (N : ℝ) ≤ ((Finset.Icc c d).card : ℝ))
    (hnf : ¬ (∀ lo : ℤ,
      (Refine.spikeCnt g (L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ)))) lo N : ℝ) ≤ μ * (N : ℝ))) :
    (((Finset.Icc c d).filter (fun y : ℤ =>
      ¬ (norm₂sq (fun t : ℤ => (1 - (p : ℝ)) * g t + (p : ℝ) * g (t + y)) ≤
          norm₂sq g -
            (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 / ((N : ℝ) * (n : ℝ))))).card : ℝ)
      ≤ 1024 * μ * ((Finset.Icc c d).card : ℝ) := by
  classical
  -- choose the spiky N-interval
  have hnotall : ∃ lo : ℤ, ¬ ((Refine.spikeCnt g (L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ)))) lo N : ℝ)
      ≤ μ * (N : ℝ)) := by
    exact not_forall.mp hnf
  rcases hnotall with ⟨lo, hgt⟩
  have hspH : μ * (N : ℝ) < (Refine.spikeCnt g (L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ)))) lo N : ℝ) :=
    lt_of_not_ge hgt
  -- constants
  let R : ℝ := Rt / ((N : ℝ) * Real.sqrt (n : ℝ))
  let H : ℝ := L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ)))
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN1)
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) (le_trans (by omega) (by omega))) )
    exact ne_of_gt hs
  have hR0' : 0 < R := by
    dsimp [R]
    positivity
  -- spikes at 8R contain the H-spikes
  have h8leH : 8 * R ≤ H := by
    dsimp [R, H]
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) (le_trans (by omega) (by omega))))
    field_simp [hNne, hsqrt]
    nlinarith [hL16]
  have hsub : ((Ell2Greedy.I0 lo N).filter (fun t : ℤ => H ≤ g t)) ⊆
      ((Ell2Greedy.I0 lo N).filter (fun t : ℤ => 8 * R ≤ g t)) := by
    intro t ht
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, le_trans h8leH ht.2⟩
  have hspH' : ((Refine.spikeCnt g H lo N : ℝ)) ≤
      ((((Ell2Greedy.I0 lo N).filter (fun t : ℤ => 8 * R ≤ g t)).card : ℕ) : ℝ) := by
    have hc := Finset.card_le_card hsub
    dsimp [Refine.spikeCnt] at hc ⊢
    simpa [H] using hc
  have hsp : μ * (N : ℝ) ≤
      (((Finset.Icc lo (lo + (N : ℤ) - 1)).filter (fun t : ℤ => 8 * R ≤ g t)).card : ℝ) := by
    have hc1 : μ * (N : ℝ) ≤ ((Refine.spikeCnt g H lo N : ℕ) : ℝ) := le_of_lt hspH
    have hc2 : ((Refine.spikeCnt g H lo N : ℕ) : ℝ) ≤
        (((Ell2Greedy.I0 lo N).filter (fun t : ℤ => 8 * R ≤ g t)).card : ℝ) := by
      simpa [H] using hspH'
    have hc3 : (((Ell2Greedy.I0 lo N).filter (fun t : ℤ => 8 * R ≤ g t)).card : ℝ) =
        (((Finset.Icc lo (lo + (N : ℤ) - 1)).filter (fun t : ℤ => 8 * R ≤ g t)).card : ℝ) := by
      rfl
    linarith
  -- mass over Ĩ ≤ 2RN
  have hIt : (∑ t ∈ Ell2Greedy.It lo N, g t) ≤ 2 * R * (N : ℝ) := by
    calc
      (∑ t ∈ Ell2Greedy.It lo N, g t)
          = (∑ t ∈ Ell2Greedy.I0 lo N, g t) + (∑ t ∈ Ell2Greedy.I0 (lo + (N : ℤ)) N, g t) :=
            sum_It_split lo N
      _ ≤ Rt / Real.sqrt (n : ℝ) + Rt / Real.sqrt (n : ℝ) := by
            exact add_le_add (hmass lo) (hmass (lo + (N : ℤ)))
      _ = 2 * R * (N : ℝ) := by
            dsimp [R]
            have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
            have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) (le_trans (by omega) (by omega))))
            field_simp [hNne, hsqrt]
            ring
  -- apply the counting form of Prop ell-2 update
  have hel2 := Ell2Greedy.ell2_update_counting (g1 := g) (g2 := g) (R := R) (μ := μ) (p := (p : ℝ))
    (lo := lo) (c := c) (d := d) (N := N)
    hμ0 hμ1 hR0' hN1 hp0 (by linarith : (p : ℝ) ≤ 1) hg0 hg2 hg2 hlip hIt hsp hJlen
  -- rewrite its drop condition into the Rt-form
  have hdrop_eq : ∀ y : ℤ,
      (norm₂sq (fun t : ℤ => (1 - (p : ℝ)) * g t + (p : ℝ) * g (t + y)) ≤
          (1 - (p : ℝ)) * norm₂sq g + (p : ℝ) * norm₂sq g -
            (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * R ^ 2 * (N : ℝ)) ↔
        (norm₂sq (fun t : ℤ => (1 - (p : ℝ)) * g t + (p : ℝ) * g (t + y)) ≤
          norm₂sq g -
            (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 / ((N : ℝ) * (n : ℝ))) := by
    intro y
    have hE : (1 - (p : ℝ)) * norm₂sq g + (p : ℝ) * norm₂sq g -
            (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * R ^ 2 * (N : ℝ) =
          norm₂sq g -
            (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 / ((N : ℝ) * (n : ℝ)) := by
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hn1))
      have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) (le_trans (by omega) (by omega))))
      have hcore : R ^ 2 * (N : ℝ) = Rt ^ 2 / ((N : ℝ) * (n : ℝ)) := by
        dsimp [R]
        calc
          (Rt / ((N : ℝ) * Real.sqrt (n : ℝ))) ^ 2 * (N : ℝ)
              = Rt ^ 2 / (((N : ℝ) * Real.sqrt (n : ℝ)) ^ 2) * (N : ℝ) := by
                rw [div_pow]
          _ = Rt ^ 2 / ((N : ℝ) ^ 2 * (n : ℝ)) * (N : ℝ) := by
                congr 1
                rw [mul_pow]
                have hs : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
                  Real.sq_sqrt (by exact_mod_cast (Nat.zero_le n))
                rw [hs]
          _ = Rt ^ 2 / ((N : ℝ) * (n : ℝ)) := by
                field_simp [hNne, hn0]
      calc
        (1 - (p : ℝ)) * norm₂sq g + (p : ℝ) * norm₂sq g -
            (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * R ^ 2 * (N : ℝ)
            = norm₂sq g -
                (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * (R ^ 2 * (N : ℝ)) := by ring
        _ = norm₂sq g -
                (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 *
                  (Rt ^ 2 / ((N : ℝ) * (n : ℝ))) := by
                  rw [hcore]
        _ = norm₂sq g -
              (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 / ((N : ℝ) * (n : ℝ)) := by ring
    rw [hE]
  have hfilters : (Finset.Icc c d).filter (fun y : ℤ =>
      ¬ (norm₂sq (fun t : ℤ => (1 - (p : ℝ)) * g t + (p : ℝ) * g (t + y)) ≤
          (1 - (p : ℝ)) * norm₂sq g + (p : ℝ) * norm₂sq g -
            (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * R ^ 2 * (N : ℝ))) =
      (Finset.Icc c d).filter (fun y : ℤ =>
      ¬ (norm₂sq (fun t : ℤ => (1 - (p : ℝ)) * g t + (p : ℝ) * g (t + y)) ≤
          norm₂sq g -
            (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 / ((N : ℝ) * (n : ℝ)))) := by
    ext y
    by_cases hy : y ∈ Finset.Icc c d
    · have hif : (¬ (norm₂sq (fun t : ℤ => (1 - (p : ℝ)) * g t + (p : ℝ) * g (t + y)) ≤
            (1 - (p : ℝ)) * norm₂sq g + (p : ℝ) * norm₂sq g -
              (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * R ^ 2 * (N : ℝ))) ↔
          (¬ (norm₂sq (fun t : ℤ => (1 - (p : ℝ)) * g t + (p : ℝ) * g (t + y)) ≤
              norm₂sq g -
                (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 / ((N : ℝ) * (n : ℝ)))) := by
        constructor
        · intro hn1 hA2
          exact hn1 ((hdrop_eq y).2 hA2)
        · intro hn2 hA1
          exact hn2 ((hdrop_eq y).1 hA1)
      rw [Finset.mem_filter, Finset.mem_filter]
      simp only [hy, true_and]
      exact hif
    · rw [Finset.mem_filter, Finset.mem_filter]
      simp only [hy, false_and]
  have hel2' : (((Finset.Icc c d).filter (fun y : ℤ =>
      ¬ (norm₂sq (fun t : ℤ => (1 - (p : ℝ)) * g t + (p : ℝ) * g (t + y)) ≤
          norm₂sq g -
            (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 / ((N : ℝ) * (n : ℝ))))).card : ℝ)
      ≤ 1024 * μ * ((Finset.Icc c d).card : ℝ) := by
    rwa [← hfilters]
  exact hel2'

end Submission.Refine3
