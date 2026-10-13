import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.HonestCut.radGreen_compact_source
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/ClassCHon/radGreen_compact_source_interval`

The source facts needed by the per-mode weighted `L²` bound for the radial Green function
`radGreen α m c`, for a source `c` which is `C^∞` on `(0,∞)`, bounded, and supported in an
**arbitrary** interval `[a,b]` with `0 < a` (rather than in `[1,2]`, the case treated by the
sibling `Work.FTS.ClassC.HonestCut.radGreen_compact_source`):

* `c` is continuous on `(0,∞)`;
* `|c t| ≤ K/t` for `t ≥ 1`;
* `|c t| ≤ K t^p` on `(0,1]` for some `p > 3/2`;
* the four weighted integrals `∫_{0}^{1} c t^{(2m+5)/α-1}`, `∫_{0}^{1} c t^{-2m/α-1}`,
  `∫_{1}^{∞} c t^{-2m/α-1}` and `∫_{0}^{∞} c² w²` (with `w(z) = (1+z)²/z²`) are finite.

The mathematical content is elementary.  The observation needed beyond the sibling's proof is that
a function continuous on `(0,∞)` and vanishing off `[a,b] ⊂ (0,∞)` is **compactly supported**,
hence integrable on `(0,∞)` (`integrableOn_Ioi_of_contOn_of_support` below, which splits
`(0,∞) = (0,a) ∪ [a,b] ∪ (b,∞)` when `a ≤ b` and is trivial when `b < a`, because then
`Icc a b = ∅` and `f ≡ 0`), together with the two pointwise bounds `decay_of_support` (with
`K = M · max b 1 + 1`) and `vanishing_of_support` (with `K = M/a² + 1`, `p = 2`).  No hypothesis
comparing `a` and `b` is needed, since membership in `Icc a b` always forces `a ≤ z`.
-/

noncomputable section

open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.ClassCHon

/-- **Integrability on `(0,∞)` from continuity and compact support.**

If `f` is continuous on `(0,∞)` and vanishes off an interval `[a,b]` with `0 < a` (so that
`[a,b] ⊆ (0,∞)`), then `f` is integrable on `(0,∞)`.  The proof splits
`(0,∞) = (0,a) ∪ [a,b] ∪ (b,∞)`; on the two open pieces `f ≡ 0`, and on `[a,b]` it is continuous
on a compact set. -/
private theorem integrableOn_Ioi_of_contOn_of_support {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hf : ContinuousOn f (Set.Ioi 0)) (hsupp : ∀ z : ℝ, z ∉ Set.Icc a b → f z = 0) :
    MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
  by_cases hab : a ≤ b
  swap
  · -- if `b < a` then `Icc a b = ∅`, so `f ≡ 0`
    rw [show f = fun _ => (0 : ℝ) from funext fun z =>
      hsupp z (fun h => hab (le_trans (Set.mem_Icc.mp h).1 (Set.mem_Icc.mp h).2))]
    exact MeasureTheory.integrableOn_zero
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha (Set.mem_Icc.mp hz).1
  have hIcc : MeasureTheory.IntegrableOn f (Set.Icc a b) :=
    (hf.mono hsub).integrableOn_compact isCompact_Icc
  have hleft : MeasureTheory.IntegrableOn f (Set.Ioo 0 a) :=
    MeasureTheory.integrableOn_zero.congr_fun
      (fun z hz => by
        rw [hsupp z (fun h => absurd (Set.mem_Icc.mp h).1 (not_le.mpr hz.2))])
      measurableSet_Ioo
  have hright : MeasureTheory.IntegrableOn f (Set.Ioi b) :=
    MeasureTheory.integrableOn_zero.congr_fun
      (fun z hz => by
        rw [hsupp z (fun h => absurd (Set.mem_Icc.mp h).2 (not_le.mpr hz))])
      measurableSet_Ioi
  have hU : MeasureTheory.IntegrableOn f (Set.Ioo 0 a ∪ Set.Icc a b ∪ Set.Ioi b) :=
    (hleft.union hIcc).union hright
  have hset : Set.Ioo 0 a ∪ Set.Icc a b ∪ Set.Ioi b = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Icc, Set.mem_Ioi]
    constructor
    · rintro ((⟨h1, _⟩ | ⟨h2, _⟩) | h3) <;> linarith
    · intro hx
      rcases lt_or_ge x a with h | h
      · exact Or.inl (Or.inl ⟨hx, h⟩)
      · rcases le_or_gt x b with h' | h'
        · exact Or.inl (Or.inr ⟨h, h'⟩)
        · exact Or.inr h'
  rwa [hset] at hU

/-- **The decay of a source supported in `[a,b]` at `∞`:** `|c t| ≤ K/t` for `t ≥ 1`. -/
private theorem decay_of_support {c : ℝ → ℝ} {a b : ℝ} {M : ℝ} (hMnn : 0 ≤ M)
    (hMb : ∀ t : ℝ, |c t| ≤ M) (hsupp : ∀ z : ℝ, z ∉ Set.Icc a b → c z = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t := by
  refine ⟨M * max b 1 + 1, by positivity, ?_⟩
  intro t ht1
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  rcases lt_or_ge b t with hbt | hbt
  · rw [hsupp t (fun h => absurd (Set.mem_Icc.mp h).2 (not_le.mpr hbt)), abs_zero]
    positivity
  · have htle : t ≤ max b 1 := le_trans hbt (le_max_left b 1)
    have h1 : M ≤ (M * max b 1) / t := by
      rw [le_div_iff₀ ht0]
      linarith [mul_le_mul_of_nonneg_left htle hMnn]
    have h2 : (M * max b 1) / t ≤ (M * max b 1 + 1) / t :=
      div_le_div_of_nonneg_right (by linarith) ht0.le
    linarith [hMb t]

/-- **The vanishing rate of a source supported in `[a,b]` near `0`:** `|c t| ≤ K t^p` on `(0,1]`
for some `p > 3/2`.  Since `c` vanishes on `(0,a)`, `p = 2` and `K = M/a² + 1` suffice. -/
private theorem vanishing_of_support {c : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) {M : ℝ} (hMnn : 0 ≤ M)
    (hMb : ∀ t : ℝ, |c t| ≤ M) (hsupp : ∀ z : ℝ, z ∉ Set.Icc a b → c z = 0) :
    ∃ K p : ℝ, 0 < K ∧ 3 / 2 < p ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → |c t| ≤ K * t ^ p := by
  refine ⟨M / a ^ 2 + 1, 2, by positivity, by norm_num, ?_⟩
  intro t _ht0 ht1
  by_cases hta : t < a
  · rw [hsupp t (fun h => absurd (Set.mem_Icc.mp h).1 (not_le.mpr hta)), abs_zero]
    positivity
  · have hge : a ≤ t := le_of_not_gt hta
    have hcoef : 0 ≤ M / a ^ 2 + 1 := by positivity
    have hK : (M / a ^ 2 + 1) * a ^ 2 = M + a ^ 2 := by field_simp
    rw [Real.rpow_two]
    calc |c t| ≤ M := hMb t
      _ ≤ M + a ^ 2 := by linarith [sq_nonneg a]
      _ = (M / a ^ 2 + 1) * a ^ 2 := hK.symm
      _ ≤ (M / a ^ 2 + 1) * t ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hge 2) hcoef

theorem radGreen_compact_source_interval {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ)
    {a b : ℝ} (ha : 0 < a) {c : ℝ → ℝ}
    (hc : ∀ n : ℕ, ContDiffOn ℝ n c (Set.Ioi 0))
    (hM : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |c t| ≤ M)
    (hsupp : ∀ z : ℝ, z ∉ Set.Icc a b → c z = 0) :
    ContinuousOn c (Set.Ioi 0)
    ∧ (∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t)
    ∧ (∃ K p : ℝ, 0 < K ∧ 3 / 2 < p ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → |c t| ≤ K * t ^ p)
    ∧ MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
        (Set.Ioo 0 1)
    ∧ MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
        (Set.Ioo 0 1)
    ∧ MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
        (Set.Ioi 1)
    ∧ MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        (Set.Ioi 0) := by
  obtain ⟨M, hMnn, hMb⟩ := hM
  have hc0 : ContinuousOn c (Set.Ioi 0) := (hc 0).continuousOn
  -- the squared weight `w²` is continuous on `(0,∞)`
  have hw : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    unfold Work.Spaces.w
    refine (((continuous_const.add continuous_id).continuousOn.pow 2).div
      (continuous_id.continuousOn.pow 2) (fun z hz => ?_)).pow 2
    exact pow_ne_zero 2 (ne_of_gt hz)
  -- the power factor `t ↦ t^e` is continuous on `(0,∞)`
  have hrpow : ∀ e : ℝ, ContinuousOn (fun z : ℝ => z ^ e) (Set.Ioi 0) := fun e => by
    intro z hz
    exact (Real.continuousAt_rpow_const z e (Or.inl (ne_of_gt hz))).continuousWithinAt
  refine ⟨hc0, decay_of_support hMnn hMb hsupp, vanishing_of_support ha hMnn hMb hsupp,
    ?_, ?_, ?_, ?_⟩
  · -- `c · t^((2m+5)/α-1)` on `(0,1)`
    refine (integrableOn_Ioi_of_contOn_of_support (a := a) (b := b) ha
      (hc0.mul (hrpow ((2 * (m : ℝ) + 5) / α - 1))) ?_).mono_set fun z hz => hz.1
    intro z hz
    simp [hsupp z hz]
  · -- `c · t^(-2m/α-1)` on `(0,1)`
    refine (integrableOn_Ioi_of_contOn_of_support (a := a) (b := b) ha
      (hc0.mul (hrpow (-(2 * (m : ℝ) / α) - 1))) ?_).mono_set fun z hz => hz.1
    intro z hz
    simp [hsupp z hz]
  · -- `c · t^(-2m/α-1)` on `(1,∞)`
    refine (integrableOn_Ioi_of_contOn_of_support (a := a) (b := b) ha
      (hc0.mul (hrpow (-(2 * (m : ℝ) / α) - 1))) ?_).mono_set ?_
    · intro z hz
      simp [hsupp z hz]
    · intro z hz
      exact Set.mem_Ioi.mpr (lt_trans zero_lt_one (Set.mem_Ioi.mp hz))
  · -- `c² w²` on `(0,∞)`
    refine integrableOn_Ioi_of_contOn_of_support (a := a) (b := b) ha ((hc0.pow 2).mul hw) ?_
    intro z hz
    simp [hsupp z hz]

end Work.FTS.ClassCHon
