import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFock.ledgerParen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latDeficit_eq_regions_closed` — the region split of `L(δ_c)`, with **no**
support hypothesis

`Submission/Work/BoseBoxFock/latDeficit_eq_regions.lean` proves the exact region decomposition of
`latDeficit ℓ c g`, but carries a *spare* hypothesis `tsupport g ⊆ Metric.ball 0 (ℓ/2)`: the proof
there never uses it (`deficit_mul_split` is a pointwise identity and `summable_latDeficit` needs
only smoothness + compact support), and Lean itself flags the binding as unreferenced.

This file removes it.  Nothing else changes: the argument is the same pointwise region split of
`δ_c`,

* `deficit_eq_zero_of_le` : `r ≤ c ⟹ δ_c(r) = 0`,
* `deficit_eq_sharp`      : `r ≥ c ⟹ δ_c(r) = (r−c)² − c²·tauPhi(r/c)`,
* `deficit_eq_tail`       : `r ≥ 2c ⟹ δ_c(r) = c·r − (5/4+c₀)c²` (`c₀ = tauC0phi`),

assembled by `tsum_add` after transferring summability of the whole family (`summable_latDeficit`)
to each of the two nonnegative branches (`Summable.of_nonneg_of_le`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `tauPhiC0` (`tauPhi_row.lean`) and `tauC0phi` (`tauGapDefs.lean`) are the same number
`∫ t² tauKer t` — the two spellings of the second moment of the smoothing kernel. -/
private lemma tauPhiC0_eq_tauC0phi' : tauPhiC0 = tauC0phi := rfl

/-- Above the threshold `c` the `max` defining `deficit` is inactive:
`δ_c(r) = (r−c)² − c²·tauPhi(r/c)` for `r ≥ c`. -/
private lemma deficit_eq_sharp' {c r : ℝ} (hr : c ≤ r) :
    deficit c r = (r - c) ^ 2 - c ^ 2 * tauPhi (r / c) := by
  rw [deficit, max_eq_left (by linarith : (0:ℝ) ≤ r - c)]

/-- **The pointwise region split of the deficit**, with the overall constant `a` carried inside:

    a·δ_c(r)·W = 1_{c < r < 2c}·a·((r−c)² − c²τ(r/c))·W + 1_{2c ≤ r}·a·(c·r − (5/4+c₀)c²)·W .

The regions `{c < r < 2c}` and `{2c ≤ r}` are disjoint and their union contains everything where
`δ_c ≠ 0` (the shell `r = 2c` is in the *second* region only, and `r ≤ c` contributes `0` to
both). -/
private lemma deficit_mul_split' {a c r W : ℝ} (hc : 0 < c) :
    a * deficit c r * W
      = (if c < r ∧ r < 2 * c then a * ((r - c) ^ 2 - c ^ 2 * tauPhi (r / c)) * W else 0)
        + (if 2 * c ≤ r then a * (c * r - (5 / 4 + tauC0phi) * c ^ 2) * W else 0) := by
  by_cases h2 : 2 * c ≤ r
  · -- tail region: the first branch is empty, the deficit is exactly linear
    have h1 : ¬ (c < r ∧ r < 2 * c) := fun h => absurd h.2 (not_lt.mpr h2)
    rw [if_neg h1, if_pos h2, deficit_eq_tail hc h2, tauPhiC0_eq_tauC0phi']
    ring
  · have h2' : r < 2 * c := lt_of_not_ge h2
    by_cases h1 : c < r
    · -- middle region: the `max` is inactive
      rw [if_pos ⟨h1, h2'⟩, if_neg h2, deficit_eq_sharp' h1.le]
      ring
    · -- below the threshold: the deficit vanishes
      have h1' : r ≤ c := le_of_not_gt h1
      rw [if_neg (fun h => h1 h.1), if_neg h2, deficit_eq_zero_of_le hc h1']
      ring

/-- The first (middle-region) branch is nonnegative: there the value is `δ_c(r) ≥ 0`. -/
private lemma deficit_sharp_piece_nonneg' {a c r W : ℝ} (hc : 0 < c) (ha : 0 ≤ a)
    (hW : 0 ≤ W) :
    0 ≤ (if c < r ∧ r < 2 * c then a * ((r - c) ^ 2 - c ^ 2 * tauPhi (r / c)) * W else 0) := by
  by_cases h : c < r ∧ r < 2 * c
  · rw [if_pos h]
    have hd : 0 ≤ deficit c r := deficit_nonneg hc (hc.trans h.1).le
    rw [deficit_eq_sharp' h.1.le] at hd
    exact mul_nonneg (mul_nonneg ha hd) hW
  · rw [if_neg h]

/-- The second (tail) branch is nonnegative: there the value is
`c·r − (5/4+c₀)c² ≥ (3/4−c₀)c² ≥ 0` because `r ≥ 2c` and `c₀ = tauC0phi ≤ 1/16`. -/
private lemma deficit_tail_piece_nonneg' {a c r W : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hW : 0 ≤ W) :
    0 ≤ (if 2 * c ≤ r then a * (c * r - (5 / 4 + tauC0phi) * c ^ 2) * W else 0) := by
  by_cases h : 2 * c ≤ r
  · rw [if_pos h]
    have hc0 : tauC0phi ≤ 1 / 16 := tauC0phi_le
    have hb : 0 ≤ c * r - (5 / 4 + tauC0phi) * c ^ 2 := by
      have h2 : (2:ℝ) * c ^ 2 ≤ c * r := by
        have := mul_le_mul_of_nonneg_left h hc.le
        nlinarith [this]
      have h5 : (5 / 4 + tauC0phi) * c ^ 2 ≤ 2 * c ^ 2 := by nlinarith [hc0, sq_nonneg c]
      linarith
    exact mul_nonneg (mul_nonneg ha hb) hW
  · rw [if_neg h]

/-- **The region decomposition of the lattice deficit `L(δ_c)`, unconditionally**: no support
hypothesis on `g` beyond compact support and smoothness is needed, because the argument is a
pointwise split of the symbol `δ_c` plus summability of the weight `‖ĝ(kₙ)‖²` against `‖kₙ‖`
(which holds for every compactly supported `C^∞` `g`, by Poisson summation). -/
theorem latDeficit_eq_regions_closed {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    Work.BoseBoxFock.latDeficit ℓ c g
      = (∑' n : Fin 3 → ℤ, if c < ‖Work.BoseBoxFock.kmomInt ℓ n‖
              ∧ ‖Work.BoseBoxFock.kmomInt ℓ n‖ < 2 * c then
            (ℓ ^ 3)⁻¹ * ((‖Work.BoseBoxFock.kmomInt ℓ n‖ - c) ^ 2
                - c ^ 2 * Work.BoseBoxFock.tauPhi (‖Work.BoseBoxFock.kmomInt ℓ n‖ / c))
              * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2
          else (0 : ℝ))
        + (∑' n : Fin 3 → ℤ, if 2 * c ≤ ‖Work.BoseBoxFock.kmomInt ℓ n‖ then
            (ℓ ^ 3)⁻¹ * (c * ‖Work.BoseBoxFock.kmomInt ℓ n‖
                - (5 / 4 + Work.BoseBoxFock.tauC0phi) * c ^ 2)
              * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2
          else (0 : ℝ)) := by
  classical
  set F1 : (Fin 3 → ℤ) → ℝ := fun n => if c < ‖kmomInt ℓ n‖ ∧ ‖kmomInt ℓ n‖ < 2 * c then
      (ℓ ^ 3)⁻¹ * ((‖kmomInt ℓ n‖ - c) ^ 2 - c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c))
        * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
    else 0 with hF1
  set F2 : (Fin 3 → ℤ) → ℝ := fun n => if 2 * c ≤ ‖kmomInt ℓ n‖ then
      (ℓ ^ 3)⁻¹ * (c * ‖kmomInt ℓ n‖ - (5 / 4 + tauC0phi) * c ^ 2)
        * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
    else 0 with hF2
  have hpt : ∀ n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * deficit c ‖kmomInt ℓ n‖
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 = F1 n + F2 n := by
    intro n
    rw [hF1, hF2]
    exact deficit_mul_split' (a := (ℓ ^ 3)⁻¹) hc
  have hFs : Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * deficit c ‖kmomInt ℓ n‖
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := summable_latDeficit hℓ hc hg hgc
  have h1nn : ∀ n, 0 ≤ F1 n := by
    intro n
    rw [hF1]
    exact deficit_sharp_piece_nonneg' hc (by positivity) (sq_nonneg _)
  have h2nn : ∀ n, 0 ≤ F2 n := by
    intro n
    rw [hF2]
    exact deficit_tail_piece_nonneg' hc (by positivity) (sq_nonneg _)
  have hs1 : Summable F1 :=
    Summable.of_nonneg_of_le h1nn (fun n => by rw [hpt n]; linarith [h2nn n]) hFs
  have hs2 : Summable F2 :=
    Summable.of_nonneg_of_le h2nn (fun n => by rw [hpt n]; linarith [h1nn n]) hFs
  rw [latDeficit]
  exact (tsum_congr hpt).trans (hs1.tsum_add hs2)

end Work.BoseBoxFock
