/-
# Auxiliary structure of the randomised small-scale cut-off

This module collects the elementary combinatorial facts about the index condition
`randAct` of `Work.KMTAreas.A7.randSymbDefs` that turn the randomised symbol
`randSymb (smallSymbF …) ε K` of the small-scale tuple into the *finite* linear combination

  `∑_{m ≤ K} randCoeff m • φ_{N_m,t}`

of the modulated bumps, with coefficients `randCoeff` that are bounded by `2` and whose
partial sums over any interval are bounded by `4`.

The two facts are

* `randAct_interval` — the set of active indices `{m | randAct … m}` is an *interval* of `ℕ`:
  the small-scale condition `smallCond` is the conjunction of the upward closed conditions
  `inIndexSet` and `mainRegime` (both monotone in the scale `N`) with the downward closed
  condition `N ≤ splitCut`, and `N = ⌊a m⌋` is monotone in `m`;
* `sum_Icc_unit_step_le_two` — consequently the indicator of an interval-like predicate has at
  most two jumps inside any interval `Icc c e`: at most one up-jump and at most one down-jump.
  This is exactly what makes the randomised telescoping sum of the bumps bounded.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.randSymbDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar

/-- `Nat.floor ∘ a` is monotone for a monotone `a : ℕ → ℝ≥0`. -/
lemma monotone_floor_nnreal {a : ℕ → NNReal} (ha : Monotone a) :
    Monotone fun m => Nat.floor (a m) :=
  Nat.floor_mono.comp (NNReal.coe_mono.comp ha)

/-- The integer logarithmic scale `N ↦ (Log N).toNat` is monotone. -/
lemma monotone_logN_toNat : Monotone fun N : ℕ => (logN N).toNat := by
  intro m n h
  exact Int.toNat_le_toNat (logN_mono h)

/-- **The active indices form an interval.**  If `randAct` holds at `j ≤ m` and at `k ≥ m`
then it holds at `m`: `smallCond` is the conjunction of the upward closed index conditions
`inIndexSet` (`heightScale C₀ N ≥ …`) and `mainRegime` (`(Log N).toNat ≥ …`) with the downward
closed condition `N ≤ splitCut`, and the scale `N = ⌊a m⌋` is monotone because `a` is. -/
lemma randAct_interval {ρ : ℝ} {C₀ : ℕ} {a : ℕ → NNReal} {l₁ l₂ k₁ k₂ : ℕ} (ha : Monotone a)
    {j m k : ℕ} (hjm : j ≤ m) (hmk : m ≤ k)
    (hj : randAct ρ C₀ a l₁ l₂ k₁ k₂ j) (hk : randAct ρ C₀ a l₁ l₂ k₁ k₂ k) :
    randAct ρ C₀ a l₁ l₂ k₁ k₂ m := by
  obtain ⟨hj0, hjc⟩ := hj
  obtain ⟨_, hkc⟩ := hk
  have hN : Monotone fun n => Nat.floor (a n) := monotone_floor_nnreal ha
  have hjN : Nat.floor (a j) ≤ Nat.floor (a m) := hN hjm
  have hmN : Nat.floor (a m) ≤ Nat.floor (a k) := hN hmk
  have hsc : Nat.floor (a k) ≤ splitCut ρ (smallL l₁ l₂ k₁ k₂) := hkc.2.1
  refine ⟨by omega, ?_⟩
  simp only [smallCond, inIndexSet, mainRegime] at hjc hkc ⊢
  refine ⟨⟨le_trans hjc.1.1 (Int.ofNat_le.mpr (heightScale_mono C₀ hjN)),
    le_trans hjc.1.2.1 (Int.ofNat_le.mpr (heightScale_mono C₀ hjN)),
    le_trans hjc.1.2.2 (Int.ofNat_le.mpr (heightScale_mono C₀ hjN))⟩,
    le_trans hmN hsc,
    le_trans hjc.2.2.1 (monotone_logN_toNat hjN),
    le_trans hjc.2.2.2 (monotone_logN_toNat hjN)⟩

/-- **Telescoping over an interval of `ℕ`.**  `∑_{m=c}^{e} (f (m-1) - f m) = f (c-1) - f e`. -/
lemma sum_Icc_sub_succ_sub (f : ℕ → ℂ) (c : ℕ) :
    ∀ e : ℕ, c ≤ e →
      ∑ m ∈ Finset.Icc c e, (f (m - 1) - f m) = f (c - 1) - f e := by
  intro e hce
  induction e, hce using Nat.le_induction with
  | base => rw [Finset.Icc_self, Finset.sum_singleton]
  | succ e hce ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.add_sub_cancel]
      ring

/-- **At most two jumps of an interval-like indicator over any interval.**
If `P : ℕ → Prop` has the property that `P j ∧ P k` forces `P m` for `j ≤ m ≤ k` — i.e. the
level set of `P` is an interval — then the indicator `u = 1_P` has at most one up-jump and at
most one down-jump, so the total variation of `u` over any interval `Icc c e` is at most `2`. -/
lemma sum_Icc_unit_step_le_two (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ {j m k : ℕ}, j ≤ m → m ≤ k → P j → P k → P m) (c e : ℕ) :
    ∑ m ∈ Finset.Icc c e,
        ‖(if P m then (1 : ℂ) else 0) - (if P (m - 1) then (1 : ℂ) else 0)‖ ≤ 2 := by
  set s := Finset.Icc c e with hs
  set sf := s.filter (fun m =>
    (if P m then (1 : ℂ) else 0) ≠ (if P (m - 1) then (1 : ℂ) else 0)) with hsf
  set Up := s.filter (fun m => ¬ P (m - 1) ∧ P m) with hUp
  set Down := s.filter (fun m => P (m - 1) ∧ ¬ P m) with hDown
  have hUp1 : Up.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro m hm m' hm'
    by_contra hne
    obtain ⟨-, hnm, hpm⟩ := Finset.mem_filter.mp hm
    obtain ⟨-, hnm', hpm'⟩ := Finset.mem_filter.mp hm'
    rcases lt_or_gt_of_ne hne with h | h
    · exact hnm' (hP (by omega) (by omega) hpm hpm')
    · exact hnm (hP (by omega) (by omega) hpm' hpm)
  have hDown1 : Down.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro m hm m' hm'
    by_contra hne
    obtain ⟨-, hpm, hnm⟩ := Finset.mem_filter.mp hm
    obtain ⟨-, hpm', hnm'⟩ := Finset.mem_filter.mp hm'
    rcases lt_or_gt_of_ne hne with h | h
    · exact hnm (hP (by omega) (by omega) hpm hpm')
    · exact hnm' (hP (by omega) (by omega) hpm' hpm)
  have hsub : sf ⊆ Up ∪ Down := by
    intro m hm
    obtain ⟨hms, hne⟩ := Finset.mem_filter.mp hm
    rw [Finset.mem_union]
    by_cases h : P m
    · refine Or.inl (Finset.mem_filter.mpr ⟨hms, ⟨?_, h⟩⟩)
      intro h2
      exact hne (by rw [if_pos h, if_pos h2])
    · refine Or.inr (Finset.mem_filter.mpr ⟨hms, ⟨?_, h⟩⟩)
      by_contra h2
      exact hne (by rw [if_neg h, if_neg h2])
  have hcard : sf.card ≤ 2 :=
    calc sf.card ≤ (Up ∪ Down).card := Finset.card_le_card hsub
      _ ≤ Up.card + Down.card := Finset.card_union_le Up Down
      _ ≤ 1 + 1 := add_le_add hUp1 hDown1
      _ = 2 := by norm_num
  have hswap : ∑ m ∈ sf, ‖(if P m then (1 : ℂ) else 0)
      - (if P (m - 1) then (1 : ℂ) else 0)‖
      = ∑ m ∈ s, ‖(if P m then (1 : ℂ) else 0) - (if P (m - 1) then (1 : ℂ) else 0)‖ := by
    refine Finset.sum_filter_of_ne ?_
    intro m hm h
    simpa [ne_eq, sub_eq_zero] using h
  have hterm : ∀ m ∈ sf, ‖(if P m then (1 : ℂ) else 0)
      - (if P (m - 1) then (1 : ℂ) else 0)‖ ≤ (1 : ℝ) := by
    intro m _
    by_cases h : P m <;> by_cases h' : P (m - 1) <;> simp [h, h']
  have hsum : ∑ m ∈ sf, ‖(if P m then (1 : ℂ) else 0)
      - (if P (m - 1) then (1 : ℂ) else 0)‖ ≤ (sf.card : ℝ) := by
    calc ∑ m ∈ sf, ‖(if P m then (1 : ℂ) else 0) - (if P (m - 1) then (1 : ℂ) else 0)‖
        ≤ ∑ _m ∈ sf, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = (sf.card : ℝ) := by simp
  rw [← hswap]
  exact le_trans hsum (by exact_mod_cast hcard)

end

end Work.KMTAreas.A7
