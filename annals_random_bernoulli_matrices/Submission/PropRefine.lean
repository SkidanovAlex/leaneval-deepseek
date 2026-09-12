import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Prop refinement: binomial-tail combinatorial core

Tikhomirov 2020, Section 3 (`prop: refinement`, proof lines ~1360–1370).
Phase 1 of the proof bounds the number of coordinate tuples for which at least
`r := ⌈m/2⌉` of the `m := ⌊εn/2⌋` mixing steps "fail" (in the sense that
neither `Event_{i−1}` nor the ℓ₂-drop `~Event_i` occurred).  The union bound
over the `C(m, r)` choices of the failing positions reduces the estimate to a
sum over `r`-subsets `S ⊆ Fin m` of the per-`S` product bound `(1024μ)^r ·
∏|J_i|`:

`Σ_{S ∈ powersetCard r (univ : Finset (Fin m))} (1024μ)^r = C(m,r)·(1024μ)^r`.

This module contains only that combinatorial core (plus its two immediate
corollaries): a clean `Finset` lemma independent of the analytic parameters.
-/

namespace Submission.PropRefine

attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- the `r`-subsets of the `m` coordinates. -/
def rSubsets (m r : ℕ) : Finset (Finset (Fin m)) :=
  ((Finset.univ : Finset (Fin m)).powersetCard r)

/-- number of `r`-subsets of `m` coordinates is `C(m,r)`. -/
lemma card_rSubsets (m r : ℕ) : (rSubsets m r).card = m.choose r := by
  dsimp [rSubsets]
  rw [Finset.card_powersetCard]
  simp

/-- the sum of a constant `q` over the `r`-subsets is `C(m,r)·q`. -/
lemma sum_powersetCard_const (m r : ℕ) (q : ℝ) :
    (∑ S ∈ ((Finset.univ : Finset (Fin m)).powersetCard r), q) =
      (m.choose r : ℝ) * q := by
  classical
  calc
    (∑ S ∈ ((Finset.univ : Finset (Fin m)).powersetCard r), q)
        = (((Finset.univ : Finset (Fin m)).powersetCard r).card : ℝ) * q := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (m.choose r : ℝ) * q := by
          congr 1
          rw [Finset.card_powersetCard]
          simp

/-- the same sum, written with the `rSubsets` abbreviation. -/
lemma sum_rSubsets_const (m r : ℕ) (q : ℝ) :
    (∑ S ∈ rSubsets m r, q) = (m.choose r : ℝ) * q := by
  dsimp [rSubsets]
  exact sum_powersetCard_const m r q

/-- the binomial-tail core: summing `(1024μ)^r` over the `r`-subsets of `m`
coordinates gives `C(m,r)·(1024μ)^r`. -/
theorem binomial_tail_core {m r : ℕ} {μ : ℝ} :
    (∑ S ∈ ((Finset.univ : Finset (Fin m)).powersetCard r), (1024 * μ) ^ r) =
      (m.choose r : ℝ) * (1024 * μ) ^ r :=
  sum_powersetCard_const m r ((1024 * μ) ^ r)

/-- binomial-tail in the ≤-form (needed for the union bound over the choices of
the `r` failing steps). -/
theorem binomial_tail_le {m r : ℕ} {μ : ℝ} (hμ : 0 ≤ μ) :
    (∑ S ∈ ((Finset.univ : Finset (Fin m)).powersetCard r), (1024 * μ) ^ r) ≤
      (m.choose r : ℝ) * (1024 * μ) ^ r := by
  rw [binomial_tail_core]

/-- the natural-number binomial coefficient in `ℝ` (helper: `C(m,r)` is the
cardinality). -/
lemma choose_real (m r : ℕ) : (m.choose r : ℝ) = (rSubsets m r).card := by
  rw [card_rSubsets]


/-- the number of elements of `X` where at least `r` of the `m` events `E k`
hold is at most the sum over the `r`-subsets `S` of the number of elements of
`X` where every event of `S` holds (pure union bound over the failing
positions). -/
theorem card_ge_events {α : Type} [DecidableEq α] {m r : ℕ} (X : Finset α)
    (E : Fin m → Finset α) :
    ((X.filter (fun x => r ≤ ((Finset.univ : Finset (Fin m)).filter (fun k : Fin m => x ∈ E k)).card)).card : ℕ) ≤
      ∑ S ∈ ((Finset.univ : Finset (Fin m)).powersetCard r),
        (X.filter (fun x => ∀ k : Fin m, k ∈ S → x ∈ E k)).card := by
  classical
  let P : Finset (Finset (Fin m)) := (Finset.univ : Finset (Fin m)).powersetCard r
  let A : Finset (Fin m) → Finset α :=
    fun S => X.filter (fun x => ∀ k : Fin m, k ∈ S → x ∈ E k)
  have hEq : X.filter (fun x =>
      r ≤ ((Finset.univ : Finset (Fin m)).filter (fun k : Fin m => x ∈ E k)).card) =
      P.biUnion A := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_biUnion]
      let T : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter (fun k : Fin m => x ∈ E k)
      have hT : T.card = ((Finset.univ : Finset (Fin m)).filter (fun k : Fin m => x ∈ E k)).card := rfl
      have hr : r ≤ T.card := by simpa [T] using hx.2
      rcases Finset.exists_subset_card_eq (s := T) hr with ⟨S, hST, hSc⟩
      refine ⟨S, ?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        exact ⟨le_trans hST (by simp), hSc⟩
      · rw [Finset.mem_filter]
        constructor
        · exact hx.1
        · intro k hkS
          have hkT : k ∈ T := hST hkS
          rw [Finset.mem_filter] at hkT
          exact hkT.2
    · intro hx
      rw [Finset.mem_biUnion] at hx
      rcases hx with ⟨S, hS, hxS⟩
      rw [Finset.mem_filter] at hxS
      rw [Finset.mem_filter]
      constructor
      · exact hxS.1
      · -- all S-events hold, so the number of holding events ≥ r (S ⊆ {k : x∈Ek} and |S| = r)
        have hS' : S ⊆ (Finset.univ : Finset (Fin m)) ∧ S.card = r :=
          (Finset.mem_powersetCard.mp hS)
        have hsub : S ⊆ (Finset.univ : Finset (Fin m)).filter (fun k : Fin m => x ∈ E k) := by
          intro k hk
          rw [Finset.mem_filter]
          exact ⟨by simp, hxS.2 k hk⟩
        have hc := Finset.card_le_card hsub
        rwa [hS'.2] at hc
  rw [hEq]
  exact Finset.card_biUnion_le (s := P) (t := A)

/-- a real-version corollary: with each `r`-subset contribution at most `Q`,
the number of elements with at least `r` events is at most `C(m,r)·Q`. -/
theorem count_ge_events_le {α : Type} [DecidableEq α] {m r : ℕ} (X : Finset α)
    (E : Fin m → Finset α) (Q : ℝ) (hQ : 0 ≤ Q)
    (hS : ∀ S ∈ ((Finset.univ : Finset (Fin m)).powersetCard r),
      (((X.filter (fun x => ∀ k : Fin m, k ∈ S → x ∈ E k)).card : ℕ) : ℝ) ≤ Q) :
    (((X.filter (fun x => r ≤ ((Finset.univ : Finset (Fin m)).filter (fun k : Fin m => x ∈ E k)).card)).card : ℕ) : ℝ) ≤
      (m.choose r : ℝ) * Q := by
  classical
  have hc := card_ge_events (X := X) (E := E) (m := m) (r := r)
  have hsum : (∑ S ∈ ((Finset.univ : Finset (Fin m)).powersetCard r),
        (X.filter (fun x => ∀ k : Fin m, k ∈ S → x ∈ E k)).card) ≤
      (m.choose r : ℕ) * Q := by
    -- convert each term to real and bound by Q; sum over C(m,r) terms
    have hterms : ∀ S ∈ ((Finset.univ : Finset (Fin m)).powersetCard r),
        (((X.filter (fun x => ∀ k : Fin m, k ∈ S → x ∈ E k)).card : ℕ) : ℝ) ≤ Q := hS
    have hR : (((∑ S ∈ ((Finset.univ : Finset (Fin m)).powersetCard r),
        (X.filter (fun x => ∀ k : Fin m, k ∈ S → x ∈ E k)).card) : ℕ) : ℝ) ≤
        ((m.choose r : ℕ) : ℝ) * Q := by
      -- Σ (nat cards) ≤ choose·Q as real: bound each real term by Q; count = choose
      calc
        (((∑ S ∈ ((Finset.univ : Finset (Fin m)).powersetCard r),
            (X.filter (fun x => ∀ k : Fin m, k ∈ S → x ∈ E k)).card) : ℕ) : ℝ)
            = ∑ S ∈ ((Finset.univ : Finset (Fin m)).powersetCard r),
                (((X.filter (fun x => ∀ k : Fin m, k ∈ S → x ∈ E k)).card : ℕ) : ℝ) := by
              exact_mod_cast (rfl : (∑ S ∈ ((Finset.univ : Finset (Fin m)).powersetCard r),
                (X.filter (fun x => ∀ k : Fin m, k ∈ S → x ∈ E k)).card) =
                ∑ S ∈ ((Finset.univ : Finset (Fin m)).powersetCard r),
                  (X.filter (fun x => ∀ k : Fin m, k ∈ S → x ∈ E k)).card)
        _ ≤ ∑ S ∈ ((Finset.univ : Finset (Fin m)).powersetCard r), Q :=
              Finset.sum_le_sum hterms
        _ = (((Finset.univ : Finset (Fin m)).powersetCard r).card : ℕ) * Q := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((m.choose r : ℕ) : ℝ) * Q := by
              rw [Finset.card_powersetCard]
              simp
    exact_mod_cast hR
  calc
    (((X.filter (fun x => r ≤ ((Finset.univ : Finset (Fin m)).filter (fun k : Fin m => x ∈ E k)).card)).card : ℕ) : ℝ)
        ≤ (((∑ S ∈ ((Finset.univ : Finset (Fin m)).powersetCard r),
            (X.filter (fun x => ∀ k : Fin m, k ∈ S → x ∈ E k)).card) : ℕ) : ℝ) := by
          exact_mod_cast hc
    _ ≤ (m.choose r : ℝ) * Q := by
          exact_mod_cast hsum

end Submission.PropRefine
