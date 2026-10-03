/-
# Elementary facts about the KMT cutoff `η` and the Ionescu--Wainger projections

This file collects the elementary bookkeeping about the KMT cutoff `kmtEta` (and its rescalings
`etaCut kmtEta k`) that the area-`A7` development of `Work.KMTContract.AreaA7` needs:

* `kmtEta` and its rescalings `etaCut kmtEta k` are real-valued (`star_etaCut`), hence so are
  their periodisations (`star_periodize_etaCut`) — needed to pass from the even exponents of the
  Ionescu--Wainger multiplier theorem (area `A1`) to the dual exponents by `IWLqBound_of_dual`;
* `etaCut kmtEta k` is smooth with compact support, so it is a Schwartz function; it is realised
  as a `SchwartzMap` by `etaCutSchwartz k`, with the defining properties
  `(etaCutSchwartz k : ℝ → ℂ) = etaCut kmtEta k`, `‖etaCutSchwartz k x‖ ≤ 1`, and
  `etaCutSchwartz k x ≠ 0 → x ∈ realArc k` — the hypotheses under which the even exponents of
  area `A1` apply;
* the translates `j ↦ etaCut kmtEta k (x + j)` are summable, the summability hypothesis of the
  `q = 2` case of `A1`.
-/
import Mathlib
import Submission.Work.KMTContract.etaCutRegular

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-! ## Real-valuedness -/

/-- The KMT cutoff `η` is real-valued. -/
lemma star_kmtEta (x : ℝ) : star (Work.KMTContract.kmtEta x) = Work.KMTContract.kmtEta x := by
  simp [Work.KMTContract.kmtEta]

/-- The rescaled cutoff `η_{≤k} = η(·/2^k)` is real-valued. -/
lemma star_etaCut (k : ℤ) (x : ℝ) :
    star (etaCut Work.KMTContract.kmtEta k x) = etaCut Work.KMTContract.kmtEta k x := by
  simp only [etaCut]
  exact star_kmtEta _

/-- The periodisation of a real-valued `1`-periodic candidate is real-valued. -/
lemma star_periodize_etaCut (k : ℤ) (ξ : Work.Analysis.IonescuWainger.Circle) :
    star (periodize (etaCut Work.KMTContract.kmtEta k) ξ)
      = periodize (etaCut Work.KMTContract.kmtEta k) ξ := by
  simp only [periodize]
  rw [tsum_star]
  exact tsum_congr (fun j => star_etaCut k _)

/-- The IW symbol `∑_{α ∈ A} Φ(· - α)` of a real-valued `Φ` is real-valued. -/
lemma star_iwSymbolSet_etaCut (A : Finset Work.Analysis.IonescuWainger.Circle) (k : ℤ) (ξ : Work.Analysis.IonescuWainger.Circle) :
    star (iwSymbolSet A (periodize (etaCut Work.KMTContract.kmtEta k)) ξ)
      = iwSymbolSet A (periodize (etaCut Work.KMTContract.kmtEta k)) ξ := by
  simp only [iwSymbolSet]
  rw [star_sum]
  exact Finset.sum_congr rfl (fun α _ => star_periodize_etaCut k _)

/-! ## The cutoff as a Schwartz function -/

/-- The rescaled cutoff is smooth. -/
lemma contDiff_etaCut (k : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (etaCut Work.KMTContract.kmtEta k) :=
  (Work.KMTContract.etaCutRegular k).1

/-- The rescaled cutoff vanishes off the arc `[-2^k, 2^k]`. -/
lemma etaCut_eq_zero_of_le {k : ℤ} {θ : ℝ} (h : (2 : ℝ) ^ k ≤ |θ|) :
    etaCut Work.KMTContract.kmtEta k θ = 0 :=
  (Work.KMTContract.etaCutRegular k).2.2 θ h

/-- The rescaled cutoff has compact support. -/
lemma hasCompactSupport_etaCut (k : ℤ) : HasCompactSupport (etaCut Work.KMTContract.kmtEta k) := by
  refine HasCompactSupport.intro (K := Set.Icc (-(2 : ℝ) ^ k) ((2 : ℝ) ^ k))
    isCompact_Icc (fun x hx => etaCut_eq_zero_of_le ?_)
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · have h' : (2 : ℝ) ^ k < -x := by linarith
    exact le_of_lt (lt_of_lt_of_le h' (neg_le_abs x))
  · exact le_of_lt (lt_of_lt_of_le h (le_abs_self x))

/-- The rescaled cutoff, as a Schwartz function. -/
noncomputable def etaCutSchwartz (k : ℤ) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_etaCut k).toSchwartzMap (contDiff_etaCut k)

@[simp] lemma etaCutSchwartz_coe (k : ℤ) :
    (etaCutSchwartz k : ℝ → ℂ) = etaCut Work.KMTContract.kmtEta k := by
  funext x
  simp [etaCutSchwartz]

/-- The rescaled cutoff is bounded by `1`. -/
lemma norm_etaCut_le_one (k : ℤ) (x : ℝ) :
    ‖etaCut Work.KMTContract.kmtEta k x‖ ≤ 1 :=
  Work.KMTContract.norm_kmtEta_le _

/-- A nonzero value of the rescaled cutoff lies in the arc `ℝ_{≤k}`. -/
lemma etaCut_ne_zero_mem_realArc (k : ℤ) {x : ℝ}
    (h : etaCut Work.KMTContract.kmtEta k x ≠ 0) : x ∈ realArc k := by
  by_contra hx
  refine h (etaCut_eq_zero_of_le ?_)
  rw [realArc, Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h' | h'
  · have h'' : (2 : ℝ) ^ k < -x := by linarith
    exact le_of_lt (lt_of_lt_of_le h'' (neg_le_abs x))
  · exact le_of_lt (lt_of_lt_of_le h' (le_abs_self x))

/-! ## Summability of the translates -/

/-- For fixed `x`, only finitely many translates `η_{≤k}(x + j)`, `j ∈ ℤ`, are nonzero, so the
family is summable.  This is the summability hypothesis of the `q = 2` case of `A1`. -/
lemma summable_etaCut_shift (k : ℤ) (x : ℝ) :
    Summable (fun j : ℤ => etaCut Work.KMTContract.kmtEta k (x + j)) := by
  set K : ℕ := Nat.ceil (|x| + (2 : ℝ) ^ k) with hKdef
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(K : ℤ)) (K : ℤ)) (fun j hj => ?_)
  by_contra hne
  have hmem : |x + (j : ℝ)| ≤ (2 : ℝ) ^ k := by
    have h := etaCut_ne_zero_mem_realArc k hne
    rw [realArc, Set.mem_Icc] at h
    exact abs_le.mpr h
  have hKle : |x| + (2 : ℝ) ^ k ≤ (K : ℝ) := by
    rw [hKdef]; exact Nat.le_ceil _
  have hj' : |(j : ℝ)| ≤ (K : ℝ) := by
    calc |(j : ℝ)| = |(x + (j : ℝ)) + (-x)| := by ring_nf
      _ ≤ |x + (j : ℝ)| + |-x| := abs_add_le _ _
      _ = |x + (j : ℝ)| + |x| := by rw [abs_neg]
      _ ≤ (2 : ℝ) ^ k + |x| := by linarith
      _ = |x| + (2 : ℝ) ^ k := by ring
      _ ≤ (K : ℝ) := hKle
  have habs : (|j| : ℤ) ≤ (K : ℤ) := by
    rw [← Int.cast_le (R := ℝ), Int.cast_abs]
    exact_mod_cast hj'
  exact absurd (abs_le.mp habs) (by simpa [Finset.mem_Icc] using hj)

end Work.KMTAreas.A7
