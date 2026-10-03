import Mathlib
import Submission.Work.KMTContract.Defs
import Submission.Work.KMTContract.periodizeCoeEqTsum

/-!
# Evenness of the Ionescu–Wainger symbol in the frequency variable

The Ionescu–Wainger symbol attached to a finite set `A ⊆ ℝ/ℤ` of arithmetic frequencies and a
symbol `Φ` on the circle is `iwSymbolSet A Φ ξ = ∑_{α ∈ A} Φ (ξ - α)`.  This file proves that for
the concrete choice `A = (ℚ/ℤ)_{≤l} = iwArithFreqs ρ l` and `Φ = periodize (η_{≤k})` — the
periodisation of the KMT cutoff `kmtEta` rescaled by `2^k` — the symbol is an **even** function of
the frequency:

`iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) (-ξ)
  = iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) ξ`.

This is `iwSymbolSetNegEq` below.  It rests on the two structural facts

* `neg_mem_iwArithFreqs` — `(ℚ/ℤ)_{≤l}` is closed under negation (immediate from
  `mem_iwArithFreqs`: `q • α = 0` implies `q • (-α) = 0`);
* `even_periodize_etaCut` — `periodize (η_{≤k})` is an even function on `ℝ/ℤ`, because the cutoff
  `η_{≤k}(θ) = kmtEta (θ / 2^k)` is even and the periodisation `ξ ↦ ∑_{j : ℤ} φ (x + j)` of an
  even function (with `x` a representative of `ξ`) is even.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.KMTAreas.A4

/-- The arithmetic frequency set `(ℚ/ℤ)_{≤l}` is closed under negation: `α` is killed by some
`q ∈ P_{≤l}` iff `-α` is. -/
lemma neg_mem_iwArithFreqs {ρ : ℝ} {l : ℕ} {α : Work.Analysis.IonescuWainger.Circle}
    (h : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l) :
    -α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l := by
  rw [Work.Analysis.IonescuWainger.mem_iwArithFreqs] at h ⊢
  obtain ⟨q, hq, hqα⟩ := h
  exact ⟨q, hq, by rw [smul_neg, hqα, neg_zero]⟩

/-- The rescaled cutoff `η_{≤k}(θ) = η(θ / 2^k)` is even. -/
lemma etaCut_kmtEta_neg (k : ℤ) (θ : ℝ) :
    Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k (-θ)
      = Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ := by
  simp only [Work.Analysis.IonescuWainger.etaCut]
  rw [neg_div, Work.KMTContract.kmtEta_neg]

/-- The periodisation `periodize (η_{≤k})` of the rescaled KMT cutoff is an even function on the
circle: `Φ(-ξ) = Φ(ξ)`. -/
lemma even_periodize_etaCut (k : ℤ) (ξ : Work.Analysis.IonescuWainger.Circle) :
    Work.Analysis.IonescuWainger.periodize
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) (-ξ)
      = Work.Analysis.IonescuWainger.periodize
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) ξ := by
  -- Write `ξ = (x : ℝ/ℤ)` with `x` the canonical representative of `ξ` in `[0,1)`; then
  -- `-ξ = (-x : ℝ/ℤ)`, and `periodizeCoeEqTsum` identifies both periodisations with the
  -- `ℤ`-orbit sums `∑'_n φ(±x + n)`.
  set x : ℝ := (AddCircle.equivIco (1 : ℝ) 0 ξ).val with hxdef
  have hxξ : ((x : ℝ) : Work.Analysis.IonescuWainger.Circle) = ξ := AddCircle.coe_equivIco
  have hneg : -ξ = (((-x : ℝ)) : Work.Analysis.IonescuWainger.Circle) := by
    rw [← hxξ, AddCircle.coe_neg]
  have h1 : Work.Analysis.IonescuWainger.periodize
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) (-ξ)
      = ∑' n : ℤ, Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k (-x + ↑n) := by
    rw [hneg, Work.KMTContract.periodizeCoeEqTsum]
  have h2 : Work.Analysis.IonescuWainger.periodize
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) ξ
      = ∑' n : ℤ, Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k (x + ↑n) := by
    rw [← hxξ, Work.KMTContract.periodizeCoeEqTsum]
  rw [h1, h2]
  -- `η_{≤k}(-x + n) = η_{≤k}(x - n)` by evenness, then reindex `n ↦ -n` in the `tsum`.
  calc ∑' n : ℤ, Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k (-x + ↑n)
      = ∑' n : ℤ, Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k (x - ↑n) := by
        refine tsum_congr fun n => ?_
        rw [show (-x + (n : ℝ)) = -(x - (n : ℝ)) by ring, etaCut_kmtEta_neg]
    _ = ∑' n : ℤ, Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k (x + ↑n) := by
        rw [show (fun n : ℤ =>
              Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k (x - ↑n))
            = (fun n : ℤ =>
              Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k
                (x + ↑(Equiv.neg ℤ n))) from ?_]
        · exact Equiv.tsum_eq (Equiv.neg ℤ)
            (fun n : ℤ => Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k (x + ↑n))
        · funext n; simp [sub_eq_add_neg]

/-- **The Ionescu–Wainger symbol `∑_{α ∈ (ℚ/ℤ)_{≤l}} η_{≤k}(ξ - α)` is even in the frequency
`ξ`.**  Both ingredients are structural: the arithmetic frequency set `(ℚ/ℤ)_{≤l}` is invariant
under `α ↦ -α`, and the symbol `η_{≤k}` is even. -/
theorem iwSymbolSetNegEq (ρ : ℝ) (l : ℕ) (k : ℤ) (ξ : Work.Analysis.IonescuWainger.Circle) :
    Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
      (Work.Analysis.IonescuWainger.periodize (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k)) (-ξ)
      = Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
      (Work.Analysis.IonescuWainger.periodize (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k)) ξ := by
  simp only [Work.Analysis.IonescuWainger.iwSymbolSet_apply]
  -- Reindex the sum over `(ℚ/ℤ)_{≤l}` by `α ↦ -α`, which permutes the set.
  refine Finset.sum_bij (fun a (_ : a ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l) => -a)
    ?_ ?_ ?_ ?_
  · intro a ha
    exact neg_mem_iwArithFreqs ha
  · intro a₁ _ a₂ _ h
    exact neg_injective h
  · intro b hb
    exact ⟨-b, neg_mem_iwArithFreqs hb, neg_neg b⟩
  · intro a ha
    -- `η_{≤k}(-ξ - a) = η_{≤k}(-(ξ + a)) = η_{≤k}(ξ + a) = η_{≤k}(ξ - (-a))`.
    have h := even_periodize_etaCut k (ξ + a)
    have key : -ξ - a = -(ξ + a) := by abel
    have key2 : ξ - -a = ξ + a := by abel
    rw [key, key2]
    exact h

end Work.KMTAreas.A4
