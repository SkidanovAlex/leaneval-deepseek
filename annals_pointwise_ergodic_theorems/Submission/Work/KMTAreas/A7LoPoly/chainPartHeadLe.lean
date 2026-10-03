import Mathlib
import Submission.Work.KMTAreas.A7Hi.LowpassDefs
import Submission.Work.Analysis.Variation.Basic
import Submission.Work.KMTAreas.A7.variationalNorm_mul_le

/-!
# The chain part of a walk truncated from above

`Work.KMTAreas.A7Hi.chainPart r a` is the chain term of the `r`-variational norm of a sequence
`a : ℕ → ℂ`: the supremum, over the lengths `J` and the monotone chains `N : ℕ → ℕ`, of the `ℓ^r`
norm of the jump vector `i ↦ a (N (i+1)) - a (N i)`.

The target compares the chain functional of the **truncated from above** walk
`n ↦ if n < M then a n else 0` (the walk `a` with everything from `M` on replaced by `0`) with the
values-supremum `supPart r a = ⨆ n, ‖a n‖ₑ` and the head `r`-variation
`Vr r M (a - a 0)` (the `r`-variation, anchored at `0`, over chains with indices `≤ M`):

`chainPart r (n ↦ if n < M then a n else 0) ≤ 2 * supPart r a + 2 * Vr r M (a - a 0)`.

**The mechanism.**  Fix a chain `N` and cap it at `M` by `w k = min (N k) M`; since the truncated
walk vanishes from `M` on, `b (N k) = b (w k)` for every `k`, so the jump vector of `b` along `N`
is the jump vector of `b` along `w`, a monotone chain with values in `[0, M]`.

Then write the jump of `b = n ↦ if n < M then a n else 0` along `w` as the sum of

* the jump of `c = a - a 0` along `w`: `D i = c (w (i+1)) - c (w i)`, and
* the discrepancy `E i = (b (w (i+1)) - b (w i)) - (c (w (i+1)) - c (w i))`.

The `ℓ^r` norm is subadditive (`r ≥ 1`), and:

* `E` vanishes except at the (at most one) *crossing* index `i` with `w i < M ≤ w (i+1)`; there
  `E i = -a M`, because `b` vanishes at and beyond `M` while `c` does not.  Hence at most one
  coordinate of `E` is nonzero, each of norm `≤ supPart r a`, and the `ℓ^r` norm of `E` is
  `≤ supPart r a`;
* `D` is the jump vector of `c` along a monotone chain with values in `[0, M]`; prepending `0` to
  that chain (an extra nonnegative jump, since `Vr` is anchored at `0`) exhibits it as a term of
  `Vr r M c`.

The two bounds `supPart` and `Vr` are then compared by the elementary inequality
`x + y ≤ 2 * x + 2 * y`.
-/

namespace Work.KMTAreas.A7LoPoly

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped ENNReal NNReal BigOperators

/-- **The `ℓ^r` norm of a vector supported on at most one point.**  For `1 ≤ r`, if `d : Fin J → ℂ`
vanishes off a set of cardinality at most `1` and every entry is bounded by `α` in the extended
norm, then `ofReal ‖WithLp.toLp r d‖ ≤ α`.

The `ℓ^r` norm is the `r`-sum `(Σ_i ‖d i‖ₑ^r)^{1/r}`
(`Work.KMTAreas.A7.ofReal_norm_toLp_eq_sum`); at most one summand is nonzero and it is `≤ α^r`, so
the sum is `≤ 1 · α^r` and taking `r`-th roots gives `≤ α`. -/
private lemma ofReal_norm_toLp_le_of_support {r : NNReal} (hr : 1 ≤ r) {J : ℕ} {d : Fin J → ℂ}
    {α : ℝ≥0∞} (hcard : (Finset.univ.filter (fun i : Fin J => d i ≠ 0)).card ≤ 1)
    (hbound : ∀ i : Fin J, ‖d i‖ₑ ≤ α) :
    ENNReal.ofReal ‖WithLp.toLp r d‖ ≤ α := by
  classical
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  rw [Work.KMTAreas.A7.ofReal_norm_toLp_eq_sum r hr d]
  set cc : ℝ≥0∞ := (((Finset.univ.filter (fun i : Fin J => d i ≠ 0)).card : ℕ) : ℝ≥0∞) with hcc
  have hsum : (∑ i : Fin J, ‖d i‖ₑ ^ (r : ℝ)) ≤ cc * α ^ (r : ℝ) := by
    have hsplit : (∑ i : Fin J, ‖d i‖ₑ ^ (r : ℝ))
        = ∑ i ∈ Finset.univ.filter (fun i : Fin J => d i ≠ 0), ‖d i‖ₑ ^ (r : ℝ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : d i ≠ 0
      · rw [if_pos hi]
      · rw [if_neg hi]
        rw [show d i = 0 from by simpa using hi]
        simp [ENNReal.zero_rpow_of_pos hr0]
    rw [hsplit, hcc]
    calc ∑ i ∈ Finset.univ.filter (fun i : Fin J => d i ≠ 0), ‖d i‖ₑ ^ (r : ℝ)
        ≤ ∑ _i ∈ Finset.univ.filter (fun i : Fin J => d i ≠ 0), α ^ (r : ℝ) :=
          Finset.sum_le_sum (fun i _ => ENNReal.rpow_le_rpow (hbound i) hr0.le)
      _ = ((Finset.univ.filter (fun i : Fin J => d i ≠ 0)).card : ℕ) * α ^ (r : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hc1 : cc ≤ 1 := by
    rw [hcc]
    exact_mod_cast hcard
  calc (((∑ i : Fin J, ‖d i‖ₑ ^ (r : ℝ))) ^ (1 / (r : ℝ)))
      ≤ (cc * α ^ (r : ℝ)) ^ (1 / (r : ℝ)) := ENNReal.rpow_le_rpow hsum (by positivity)
    _ = cc ^ (1 / (r : ℝ)) * (α ^ (r : ℝ)) ^ (1 / (r : ℝ)) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = cc ^ (1 / (r : ℝ)) * α := by
        rw [← ENNReal.rpow_mul, mul_one_div, div_self hr0.ne', ENNReal.rpow_one]
    _ ≤ 1 ^ (1 / (r : ℝ)) * α :=
        mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow hc1 (by positivity)) bot_le
    _ = α := by rw [ENNReal.one_rpow, one_mul]

/-- **The `ℓ^r` norm of the jumps of a sequence along a chain in `[0, M]` is at most `Vr r M`.**
The chain `w` need not start at `0`; prepending `0` to it adds one nonnegative jump, which is why
`Vr` (anchored at `0`) still dominates. -/
private lemma ofReal_norm_toLp_jumps_le_Vr (r : NNReal) (hr : 1 ≤ r) (c : ℕ → ℂ) (M J : ℕ)
    (w : ℕ → ℕ) (hw : Monotone w) (hwle : ∀ k : ℕ, w k ≤ M) :
    ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J => c (w ((i : ℕ) + 1)) - c (w (i : ℕ)))‖
      ≤ Work.Analysis.Variation.Vr (r : ℝ) M c := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  rw [Work.KMTAreas.A7.ofReal_norm_toLp_eq_sum r hr]
  -- the chain `0, w 0, w 1, …, w J` of `Vr` (with `J + 1` jumps)
  let u : Fin (J + 2) → ℕ := fun i => if (i : ℕ) = 0 then 0 else w ((i : ℕ) - 1)
  have hua : ∀ i : Fin (J + 2), u i = (if (i : ℕ) = 0 then 0 else w ((i : ℕ) - 1)) :=
    fun i => rfl
  have hu0 : u 0 = 0 := by rw [hua]; simp
  have hus : ∀ k : Fin (J + 1), u k.succ = w (k : ℕ) := by
    intro k
    rw [hua]
    simp
  have humono : Monotone u := by
    rw [Fin.monotone_iff_le_succ]
    intro i
    rw [hus i, hua i.castSucc, Fin.val_castSucc]
    by_cases hi : (i : ℕ) = 0
    · rw [if_pos hi]
      exact Nat.zero_le _
    · rw [if_neg hi]
      exact hw (Nat.sub_le _ _)
  have hule : ∀ i : Fin (J + 2), u i ≤ M := by
    intro i
    rw [hua i]
    by_cases hi : (i : ℕ) = 0
    · rw [if_pos hi]
      exact Nat.zero_le _
    · rw [if_neg hi]
      exact hwle _
  -- the `Vr` chain sum covers our chain sum
  have hsum_le : (∑ i : Fin J, ‖c (w ((i : ℕ) + 1)) - c (w (i : ℕ))‖ₑ ^ (r : ℝ))
      ≤ ∑ j : Fin (J + 1), ‖c (u j.succ) - c (u j.castSucc)‖ₑ ^ (r : ℝ) := by
    rw [Fin.sum_univ_succ]
    have heq : (∑ i : Fin J, ‖c (w ((i : ℕ) + 1)) - c (w (i : ℕ))‖ₑ ^ (r : ℝ))
        = ∑ k : Fin J, ‖c (u (k.succ).succ) - c (u (k.succ).castSucc)‖ₑ ^ (r : ℝ) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 : u ((k.succ).succ) = w ((k : ℕ) + 1) := hus k.succ
      have h2 : u ((k.succ).castSucc) = w (k : ℕ) := hus k.castSucc
      rw [h1, h2]
    rw [heq]
    exact le_add_left le_rfl
  calc (∑ i : Fin J, ‖c (w ((i : ℕ) + 1)) - c (w (i : ℕ))‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ))
      ≤ (∑ j : Fin (J + 1), ‖c (u j.succ) - c (u j.castSucc)‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) :=
        ENNReal.rpow_le_rpow hsum_le (by positivity)
    _ ≤ Work.Analysis.Variation.Vr (r : ℝ) M c := by
        rw [Work.Analysis.Variation.Vr]
        exact le_iSup_of_le (J + 1) (le_iSup_of_le u (le_iSup_of_le humono
          (le_iSup_of_le hu0 (le_iSup_of_le hule le_rfl))))

/-- **The discrepancy between the truncated walk and `a - a 0` is bounded by the values
supremum.**  For a monotone chain `w` with values in `[0, M]`, the vector
`E i = (b (w (i+1)) - b (w i)) - (c (w (i+1)) - c (w i))`, where `b n = if n < M then a n else 0`
and `c n = a n - a 0`, vanishes off the (at most one) crossing index, where it equals `-a M`. -/
private lemma ofReal_norm_toLp_truncDiff_le_supPart (r : NNReal) (hr : 1 ≤ r) (a : ℕ → ℂ) (M J : ℕ)
    (w : ℕ → ℕ) (hw : Monotone w) (hwle : ∀ k : ℕ, w k ≤ M) :
    ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J =>
        ((if w ((i : ℕ) + 1) < M then a (w ((i : ℕ) + 1)) else 0)
          - (if w (i : ℕ) < M then a (w (i : ℕ)) else 0))
        - ((a (w ((i : ℕ) + 1)) - a 0) - (a (w (i : ℕ)) - a 0)))‖
      ≤ Work.KMTAreas.A7Hi.supPart r a := by
  have hsup : ∀ n : ℕ, ‖a n‖ₑ ≤ Work.KMTAreas.A7Hi.supPart r a :=
    fun n => le_iSup (fun n : ℕ => ‖a n‖ₑ) n
  let v : Fin J → ℂ := fun i =>
    ((if w ((i : ℕ) + 1) < M then a (w ((i : ℕ) + 1)) else 0)
      - (if w (i : ℕ) < M then a (w (i : ℕ)) else 0))
    - ((a (w ((i : ℕ) + 1)) - a 0) - (a (w (i : ℕ)) - a 0))
  have hva : ∀ i : Fin J, v i = (((if w ((i : ℕ) + 1) < M then a (w ((i : ℕ) + 1)) else 0)
      - (if w (i : ℕ) < M then a (w (i : ℕ)) else 0))
    - ((a (w ((i : ℕ) + 1)) - a 0) - (a (w (i : ℕ)) - a 0))) := fun i => rfl
  -- at the crossing index the discrepancy is `-a M`
  have hvM : ∀ i : Fin J, w (i : ℕ) < M → M ≤ w ((i : ℕ) + 1) → v i = -(a M) := by
    intro i h1 h2
    have h2' : w ((i : ℕ) + 1) = M := le_antisymm (hwle _) h2
    rw [hva i, if_neg (by rw [h2']; exact lt_irrefl M), if_pos h1, h2']
    ring
  -- off the crossing index the discrepancy vanishes
  have hv0 : ∀ i : Fin J, ¬(w (i : ℕ) < M ∧ M ≤ w ((i : ℕ) + 1)) → v i = 0 := by
    intro i hi
    by_cases h1 : w (i : ℕ) < M
    · have h2 : w ((i : ℕ) + 1) < M := by
        by_contra hc
        exact hi ⟨h1, not_lt.mp hc⟩
      rw [hva i, if_pos h2, if_pos h1]
      ring
    · have h1' : w (i : ℕ) = M := le_antisymm (hwle _) (not_lt.mp h1)
      have h2' : w ((i : ℕ) + 1) = M :=
        le_antisymm (hwle _) (le_trans (not_lt.mp h1) (hw (Nat.le_succ _)))
      rw [hva i, if_neg (by rw [h2']; exact lt_irrefl M),
        if_neg (by rw [h1']; exact lt_irrefl M), h2', h1']
      ring
  have hcard : (Finset.univ.filter (fun i : Fin J => v i ≠ 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    by_contra hij
    have hi' : w (i : ℕ) < M ∧ M ≤ w ((i : ℕ) + 1) := by
      by_contra hcon
      exact (Finset.mem_filter.mp hi).2 (hv0 i hcon)
    have hj' : w (j : ℕ) < M ∧ M ≤ w ((j : ℕ) + 1) := by
      by_contra hcon
      exact (Finset.mem_filter.mp hj).2 (hv0 j hcon)
    have hvne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hvne with hlt | hgt
    · have hle : (i : ℕ) + 1 ≤ (j : ℕ) := by omega
      have := hw hle
      omega
    · have hle : (j : ℕ) + 1 ≤ (i : ℕ) := by omega
      have := hw hle
      omega
  have hbound : ∀ i : Fin J, ‖v i‖ₑ ≤ Work.KMTAreas.A7Hi.supPart r a := by
    intro i
    by_cases h : w (i : ℕ) < M ∧ M ≤ w ((i : ℕ) + 1)
    · rw [hvM i h.1 h.2, enorm_neg]
      exact hsup M
    · rw [hv0 i h, enorm_zero]
      exact bot_le
  rw [show (fun i : Fin J =>
        ((if w ((i : ℕ) + 1) < M then a (w ((i : ℕ) + 1)) else 0)
          - (if w (i : ℕ) < M then a (w (i : ℕ)) else 0))
        - ((a (w ((i : ℕ) + 1)) - a 0) - (a (w (i : ℕ)) - a 0))) = v from funext hva]
  exact ofReal_norm_toLp_le_of_support hr hcard hbound

/-- The elementary comparison `x + y ≤ 2 * x + 2 * y` in `ℝ≥0∞`. -/
private lemma add_le_two_mul_add_two_mul (x y : ℝ≥0∞) : x + y ≤ 2 * x + 2 * y := by
  rw [two_mul, two_mul]
  exact add_le_add (le_add_right le_rfl) (le_add_right le_rfl)

theorem chainPartHeadLe (r : NNReal) (hr : 1 ≤ r) (M : ℕ) (hM : 1 ≤ M) (a : ℕ → ℂ) :
    Work.KMTAreas.A7Hi.chainPart r (fun n : ℕ => if n < M then a n else 0)
      ≤ 2 * Work.KMTAreas.A7Hi.supPart r a
        + 2 * Work.Analysis.Variation.Vr (r : ℝ) M (fun n : ℕ => a n - a 0) := by
  haveI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  let b : ℕ → ℂ := fun n => if n < M then a n else 0
  let c : ℕ → ℂ := fun n => a n - a 0
  have hba : ∀ n : ℕ, b n = (if n < M then a n else 0) := fun n => rfl
  have hca : ∀ n : ℕ, c n = (a n - a 0) := fun n => rfl
  rw [Work.KMTAreas.A7Hi.chainPart]
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  -- cap the chain at `M`
  let w : ℕ → ℕ := fun k => min (N k) M
  have hwdef : ∀ k : ℕ, w k = min (N k) M := fun k => rfl
  have hwm : Monotone w := by
    intro i j hij
    rw [hwdef i, hwdef j]
    exact min_le_min (hN hij) le_rfl
  have hwle : ∀ k : ℕ, w k ≤ M := fun k => by rw [hwdef k]; exact min_le_right _ _
  -- the truncated walk cannot see beyond `M`
  have hbw : ∀ k : ℕ, b (N k) = b (w k) := by
    intro k
    by_cases h : N k < M
    · have hw' : w k = N k := by rw [hwdef k]; exact min_eq_left (le_of_lt h)
      rw [hba, hba, hw', if_pos h]
    · have hw' : w k = M := by rw [hwdef k]; exact min_eq_right (not_lt.mp h)
      rw [hba, hba, hw', if_neg h, if_neg (lt_irrefl M)]
  rw [show (fun i : Fin J => b (N ((i : ℕ) + 1)) - b (N (i : ℕ)))
      = (fun i : Fin J => b (w ((i : ℕ) + 1)) - b (w (i : ℕ))) from by
        funext i; rw [hbw ((i : ℕ) + 1), hbw (i : ℕ)]]
  -- split the jump vector into the `c`-jump and the discrepancy
  let D : Fin J → ℂ := fun i => c (w ((i : ℕ) + 1)) - c (w (i : ℕ))
  let E : Fin J → ℂ := fun i =>
    ((if w ((i : ℕ) + 1) < M then a (w ((i : ℕ) + 1)) else 0)
      - (if w (i : ℕ) < M then a (w (i : ℕ)) else 0))
    - ((a (w ((i : ℕ) + 1)) - a 0) - (a (w (i : ℕ)) - a 0))
  have hDa : ∀ i : Fin J, D i = c (w ((i : ℕ) + 1)) - c (w (i : ℕ)) := fun i => rfl
  have hEa : ∀ i : Fin J, E i = (((if w ((i : ℕ) + 1) < M then a (w ((i : ℕ) + 1)) else 0)
      - (if w (i : ℕ) < M then a (w (i : ℕ)) else 0))
    - ((a (w ((i : ℕ) + 1)) - a 0) - (a (w (i : ℕ)) - a 0))) := fun i => rfl
  have hsplit : (fun i : Fin J => b (w ((i : ℕ) + 1)) - b (w (i : ℕ))) = D + E := by
    funext i
    simp only [Pi.add_apply, hDa i, hEa i]
    rw [hba, hba, hca, hca]
    ring
  have hnorm : ENNReal.ofReal
      ‖WithLp.toLp r (fun i : Fin J => b (w ((i : ℕ) + 1)) - b (w (i : ℕ)))‖
      ≤ ENNReal.ofReal ‖WithLp.toLp r D‖ + ENNReal.ofReal ‖WithLp.toLp r E‖ := by
    calc ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J => b (w ((i : ℕ) + 1)) - b (w (i : ℕ)))‖
        = ENNReal.ofReal ‖WithLp.toLp r D + WithLp.toLp r E‖ := by rw [hsplit, WithLp.toLp_add]
      _ ≤ ENNReal.ofReal (‖WithLp.toLp r D‖ + ‖WithLp.toLp r E‖) :=
          ENNReal.ofReal_le_ofReal (norm_add_le _ _)
      _ = ENNReal.ofReal ‖WithLp.toLp r D‖ + ENNReal.ofReal ‖WithLp.toLp r E‖ :=
          ENNReal.ofReal_add (norm_nonneg (WithLp.toLp r D)) (norm_nonneg (WithLp.toLp r E))
  have hDle : ENNReal.ofReal ‖WithLp.toLp r D‖ ≤ Work.Analysis.Variation.Vr (r : ℝ) M c := by
    rw [show D = (fun i : Fin J => c (w ((i : ℕ) + 1)) - c (w (i : ℕ))) from funext hDa]
    exact ofReal_norm_toLp_jumps_le_Vr r hr c M J w hwm hwle
  have hEle : ENNReal.ofReal ‖WithLp.toLp r E‖ ≤ Work.KMTAreas.A7Hi.supPart r a := by
    rw [show E = (fun i : Fin J =>
        ((if w ((i : ℕ) + 1) < M then a (w ((i : ℕ) + 1)) else 0)
          - (if w (i : ℕ) < M then a (w (i : ℕ)) else 0))
        - ((a (w ((i : ℕ) + 1)) - a 0) - (a (w (i : ℕ)) - a 0))) from funext hEa]
    exact ofReal_norm_toLp_truncDiff_le_supPart r hr a M J w hwm hwle
  calc ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J => b (w ((i : ℕ) + 1)) - b (w (i : ℕ)))‖
      ≤ ENNReal.ofReal ‖WithLp.toLp r D‖ + ENNReal.ofReal ‖WithLp.toLp r E‖ := hnorm
    _ ≤ Work.Analysis.Variation.Vr (r : ℝ) M c + Work.KMTAreas.A7Hi.supPart r a :=
        add_le_add hDle hEle
    _ = Work.KMTAreas.A7Hi.supPart r a + Work.Analysis.Variation.Vr (r : ℝ) M c := add_comm _ _
    _ ≤ 2 * Work.KMTAreas.A7Hi.supPart r a + 2 * Work.Analysis.Variation.Vr (r : ℝ) M c :=
        add_le_two_mul_add_two_mul _ _
    _ = 2 * Work.KMTAreas.A7Hi.supPart r a
          + 2 * Work.Analysis.Variation.Vr (r : ℝ) M (fun n : ℕ => a n - a 0) := by
        rw [show c = (fun n : ℕ => a n - a 0) from funext hca]

end Work.KMTAreas.A7LoPoly
