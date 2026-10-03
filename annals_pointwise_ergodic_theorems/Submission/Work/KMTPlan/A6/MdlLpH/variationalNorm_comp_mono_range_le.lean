import Mathlib
import ChallengeDeps
import Submission.VarPrep

/-!
# The variational norm of a monotone reindexing supported on an interval

For a monotone map `σ : ℕ → ℕ` taking only the values `< Y` on the index interval `[a, b)`, the
sequence `n ↦ if a ≤ n ∧ n < b then u (σ n) else 0` has `r`-variational norm (`r ≥ 1`) at most
`∑_{m < Y} 4‖u m‖`.

The mechanism is that `σ` is monotone, so each level set `{n | σ n = m}` is an *interval* of
`ℕ`; hence the sequence is a sum, over the (at most `Y`) values `m < Y`, of a constant multiple
of an interval-indicator, and the `V^r`-norm of such a spike is at most `4‖c‖`
(`variationalNorm_interval_le`, from the two "step" estimates of `Submission.VarPrep`).
-/

set_option autoImplicit false

namespace Work.KMTPlan.A6.MdlLpH

open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Elementary variational-norm bounds -/

/-- The variational norm of the zero sequence is zero (for `r ≥ 1`), by homogeneity. -/
lemma variationalNorm_zero_aux {r : ℝ≥0} (hr : 1 ≤ r) :
    PointwiseErgodicTheorems.variationalNorm r (0 : ℕ → ℂ) = 0 := by
  have h := Submission.PointwiseErgodicTheorems.variationalNorm_smul (r := r) hr
    (0 : ℂ) (0 : ℕ → ℂ)
  simpa using h

/-- The variational norm is invariant under negation. -/
lemma variationalNorm_neg_aux {r : ℝ≥0} (hr : 1 ≤ r) (w : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (-w)
      = PointwiseErgodicTheorems.variationalNorm r w := by
  have h := Submission.PointwiseErgodicTheorems.variationalNorm_smul (r := r) hr (-1 : ℂ) w
  rw [neg_one_smul] at h
  have h1 : ‖(-1 : ℂ)‖ₑ = 1 := by simp
  rw [h, h1, one_mul]

/-- Finite subadditivity of the variational norm. -/
lemma variationalNorm_finset_sum_le_aux {r : ℝ≥0} (hr : 1 ≤ r) {ι : Type*} (s : Finset ι)
    (a : ι → ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => ∑ i ∈ s, a i n)
      ≤ ∑ i ∈ s, PointwiseErgodicTheorems.variationalNorm r (a i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h0 : (fun n : ℕ => ∑ i ∈ (∅ : Finset ι), a i n) = 0 := by
        funext n; simp
      rw [h0, Finset.sum_empty, variationalNorm_zero_aux hr]
  | insert i s hi ih =>
      have h1 : (fun n : ℕ => ∑ j ∈ insert i s, a j n) = a i + (fun n => ∑ j ∈ s, a j n) := by
        funext n; simp [Finset.sum_insert hi]
      rw [h1, Finset.sum_insert hi]
      exact (Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr _ _).trans
        (add_le_add le_rfl ih)

/-- **The variational norm of a constant multiple of an interval indicator** is at most
`4‖c‖`: such a sequence is the difference of the two step sequences
`n ↦ if n < q then c else 0` and `n ↦ if n < p then c else 0`, each of variational norm at most
`2‖c‖`. -/
lemma variationalNorm_interval_le {r : ℝ≥0} (hr : 1 ≤ r) (c : ℂ) (p q : ℕ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if p ≤ n ∧ n < q then c else 0)
      ≤ 4 * ‖c‖ₑ := by
  by_cases hpq : p ≤ q
  · have hdecomp : (fun n : ℕ => if p ≤ n ∧ n < q then c else 0)
        = (fun n : ℕ => if n < q then c else 0)
          + (-(fun n : ℕ => if n < p then c else 0)) := by
      funext n
      simp only [Pi.add_apply, Pi.neg_apply]
      by_cases h1 : n < p
      · have hq : n < q := lt_of_lt_of_le h1 hpq
        rw [if_neg (by rintro ⟨hp, hq'⟩; omega), if_pos hq, if_pos h1]
        ring
      · by_cases h3 : n < q
        · have hp : p ≤ n := not_lt.mp h1
          rw [if_pos ⟨hp, h3⟩, if_pos h3, if_neg h1]
          ring
        · rw [if_neg (by rintro ⟨hp, hq'⟩; omega), if_neg h3, if_neg h1]
          ring
    have hmain : PointwiseErgodicTheorems.variationalNorm r
        ((fun n : ℕ => if n < q then c else 0)
          + (-(fun n : ℕ => if n < p then c else 0))) ≤ 4 * ‖c‖ₑ := by
      calc PointwiseErgodicTheorems.variationalNorm r
            ((fun n : ℕ => if n < q then c else 0)
              + (-(fun n : ℕ => if n < p then c else 0)))
          ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if n < q then c else 0)
            + PointwiseErgodicTheorems.variationalNorm r
                (-(fun n : ℕ => if n < p then c else 0)) :=
            Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr _ _
        _ = PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if n < q then c else 0)
            + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if n < p then c else 0) := by
            rw [variationalNorm_neg_aux hr]
        _ ≤ 2 * ‖c‖ₑ + 2 * ‖c‖ₑ := add_le_add
            (Submission.PointwiseErgodicTheorems.variationalNorm_step_le hr q c)
            (Submission.PointwiseErgodicTheorems.variationalNorm_step_le hr p c)
        _ = 4 * ‖c‖ₑ := by ring
    rw [hdecomp]
    exact hmain
  · have hz : (fun n : ℕ => if p ≤ n ∧ n < q then c else 0) = 0 := by
      funext n
      rw [if_neg (by rintro ⟨hp, hq'⟩; omega)]
      rfl
    rw [hz, variationalNorm_zero_aux hr]
    exact bot_le

/-! ## The level sets of a monotone map are intervals -/

/-- If `σ` is monotone, then for every `m` the set of `n ∈ [a, b)` with `σ n = m` is an interval
`[p, q)` of `ℕ`. -/
lemma exists_interval_levelSet {σ : ℕ → ℕ} (hσ : Monotone σ) (a b m : ℕ) :
    ∃ p q : ℕ, ∀ n : ℕ, (a ≤ n ∧ n < b ∧ σ n = m) ↔ (p ≤ n ∧ n < q) := by
  classical
  by_cases hne : ∃ n, a ≤ n ∧ n < b ∧ σ n = m
  · obtain ⟨n₀, hn₀⟩ := hne
    set S : Finset ℕ := (Finset.range b).filter (fun n => a ≤ n ∧ σ n = m) with hS
    have hmem : ∀ n : ℕ, n ∈ S ↔ a ≤ n ∧ n < b ∧ σ n = m := by
      intro n
      rw [hS, Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩
    have hSne : S.Nonempty := ⟨n₀, (hmem n₀).mpr hn₀⟩
    refine ⟨S.min' hSne, S.max' hSne + 1, fun n => ?_⟩
    constructor
    · intro hn
      have hnS : n ∈ S := (hmem n).mpr hn
      exact ⟨Finset.min'_le S n hnS, Nat.lt_succ_of_le (Finset.le_max' S n hnS)⟩
    · rintro ⟨h1, h2⟩
      have h2' : n ≤ S.max' hSne := Nat.lt_succ_iff.mp h2
      have hmin := (hmem _).mp (Finset.min'_mem S hSne)
      have hmax := (hmem _).mp (Finset.max'_mem S hSne)
      have hs1 : σ (S.min' hSne) ≤ σ n := hσ h1
      have hs2 : σ n ≤ σ (S.max' hSne) := hσ h2'
      exact ⟨le_trans hmin.1 h1, lt_of_le_of_lt h2' hmax.2.1, by omega⟩
  · refine ⟨0, 0, fun n => ?_⟩
    constructor
    · intro hn; exact (hne ⟨n, hn⟩).elim
    · intro hn; exact absurd hn.2 (by omega)

/-! ## The main estimate -/

theorem variationalNorm_comp_mono_range_le {r : NNReal} (hr : 1 ≤ r) (u : ℕ → ℂ) (σ : ℕ → ℕ)
    (hσ : Monotone σ) (a b Y : ℕ) (hY : ∀ n : ℕ, a ≤ n → n < b → σ n < Y) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if a ≤ n ∧ n < b then u (σ n) else 0)
      ≤ ∑ m ∈ Finset.range Y, 4 * ENNReal.ofReal ‖u m‖ := by
  classical
  have hdecomp : (fun n : ℕ => if a ≤ n ∧ n < b then u (σ n) else 0)
      = fun n : ℕ => ∑ m ∈ Finset.range Y,
          (if a ≤ n ∧ n < b ∧ σ n = m then u m else 0) := by
    funext n
    by_cases hn : a ≤ n ∧ n < b
    · rw [if_pos hn]
      have hσY : σ n < Y := hY n hn.1 hn.2
      have hsum : (∑ m ∈ Finset.range Y, (if a ≤ n ∧ n < b ∧ σ n = m then u m else 0))
          = ∑ m ∈ Finset.range Y, (if σ n = m then u m else 0) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        by_cases hmn : σ n = m
        · rw [if_pos ⟨hn.1, hn.2, hmn⟩, if_pos hmn]
        · rw [if_neg (fun h => hmn h.2.2), if_neg hmn]
      rw [hsum, Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hσY)]
    · rw [if_neg hn]
      refine (Finset.sum_eq_zero (fun m _ => ?_)).symm
      rw [if_neg (fun h => hn ⟨h.1, h.2.1⟩)]
  rw [hdecomp]
  have h1 := variationalNorm_finset_sum_le_aux hr (Finset.range Y)
    (fun m n => if a ≤ n ∧ n < b ∧ σ n = m then u m else 0)
  have h2 : (∑ m ∈ Finset.range Y, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if a ≤ n ∧ n < b ∧ σ n = m then u m else 0))
      ≤ ∑ m ∈ Finset.range Y, 4 * ENNReal.ofReal ‖u m‖ := by
    refine Finset.sum_le_sum (fun m _ => ?_)
    obtain ⟨p, q, hpq⟩ := exists_interval_levelSet hσ a b m
    have heq : (fun n : ℕ => if a ≤ n ∧ n < b ∧ σ n = m then u m else 0)
        = (fun n : ℕ => if p ≤ n ∧ n < q then u m else 0) := by
      funext n
      by_cases h : a ≤ n ∧ n < b ∧ σ n = m
      · rw [if_pos h, if_pos ((hpq n).mp h)]
      · rw [if_neg h, if_neg (fun h' => h ((hpq n).mpr h'))]
    rw [heq, ofReal_norm]
    exact variationalNorm_interval_le hr (u m) p q
  exact h1.trans h2

end

end Work.KMTPlan.A6.MdlLpH
