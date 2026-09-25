import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star

namespace Commons.Analysis.Real

/-- For natural numbers `a`, `b`: if the real distance is `< 1`, they are equal. -/
lemma nat_eq_of_abs_cast_sub_lt_one {a b : ℕ} (h : |(a : ℝ) - (b : ℝ)| < 1) : a = b := by
  have hz : |((a : ℤ) - (b : ℤ))| < 1 := by
    have hreal : ((|((a : ℤ) - (b : ℤ))| : ℤ) : ℝ) < 1 := by
      rw [Int.cast_abs]
      push_cast
      simpa using h
    exact_mod_cast hreal
  have h0 : (a : ℤ) - (b : ℤ) = 0 := Int.abs_lt_one_iff.mp hz
  have h1 : (a : ℤ) = (b : ℤ) := sub_eq_zero.mp h0
  exact_mod_cast h1

theorem exists_gap_height (T : ℝ) {n : ℕ} (hn : 1 ≤ n) (S : Finset ℝ)
    (hcard : S.card ≤ n) (hS : ∀ s ∈ S, T - 1 ≤ s ∧ s ≤ T + 2) :
    ∃ Tp : ℝ, T ≤ Tp ∧ Tp ≤ T + 1 ∧ ∀ s ∈ S, 1 / (2 * n + 2) ≤ |Tp - s| := by
  classical
  set c : ℝ := (n : ℝ) + 1 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  set δ : ℝ := 1 / (2 * c) with hδ
  set t : Fin (n + 2) → ℝ := fun j => T + (j : ℝ) / c with ht
  set bad : Finset (Fin (n + 2)) :=
    Finset.univ.filter (fun j => ∃ s ∈ S, |t j - s| < δ) with hbad
  have h2δ : 2 * δ = 1 / c := by
    rw [hδ]; ring_nf
  -- Distinct candidates are `1 / c` apart; each `s` can rule out at most one of them.
  have key : ∀ {a b : Fin (n + 2)} {s : ℝ}, |t a - s| < δ → |t b - s| < δ → a = b := by
    intro a b s ha hb
    have htri : |t a - t b| < 1 / c := by
      have h1 : |t a - t b| ≤ |t a - s| + |t b - s| := by
        have h := abs_add_le (t a - s) (s - t b)
        rw [show (t a - s) + (s - t b) = t a - t b by ring] at h
        rwa [abs_sub_comm s (t b)] at h
      linarith
    have htab : |t a - t b| = |(a : ℝ) - (b : ℝ)| / c := by
      have hsub : t a - t b = ((a : ℝ) - (b : ℝ)) / c := by
        rw [ht]; simp only; ring
      rw [hsub, abs_div, abs_of_pos hcpos]
    rw [htab] at htri
    have hnum : |(a : ℝ) - (b : ℝ)| < 1 := by
      rw [div_lt_iff₀ hcpos] at htri
      rwa [one_div, inv_mul_cancel₀ (ne_of_gt hcpos)] at htri
    exact Fin.ext (nat_eq_of_abs_cast_sub_lt_one hnum)
  have hbad_card : bad.card ≤ S.card := by
    have hbad_eq : bad = S.biUnion (fun s => Finset.univ.filter (fun j => |t j - s| < δ)) := by
      ext j
      rw [hbad]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    rw [hbad_eq]
    calc (S.biUnion (fun s => Finset.univ.filter (fun j => |t j - s| < δ))).card
        ≤ ∑ s ∈ S, (Finset.univ.filter (fun j => |t j - s| < δ)).card := Finset.card_biUnion_le
      _ ≤ ∑ s ∈ S, 1 := by
          apply Finset.sum_le_sum
          intro s _
          rw [Finset.card_le_one]
          intro a ha b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          exact key ha hb
      _ = S.card := by simp
  have hbad_lt : bad.card < (Finset.univ : Finset (Fin (n + 2))).card := by
    calc bad.card ≤ S.card := hbad_card
      _ ≤ n := hcard
      _ < n + 2 := by omega
      _ = (Finset.univ : Finset (Fin (n + 2))).card := by simp
  obtain ⟨j, _, hjbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad_lt
  have hδgoal : 1 / (2 * (n : ℝ) + 2) = δ := by
    rw [hδ, hc]; congr 1; ring
  refine ⟨t j, ?_, ?_, ?_⟩
  · rw [ht]; simp only
    have : (0 : ℝ) ≤ (j : ℝ) / c := div_nonneg (by positivity) (le_of_lt hcpos)
    linarith
  · rw [ht]; simp only
    have hjle : (j : ℝ) ≤ c := by
      rw [hc]
      have hjn : (j : ℕ) ≤ n + 1 := by have := j.isLt; omega
      have : (j : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hjn
      linarith
    have : (j : ℝ) / c ≤ 1 := by rw [div_le_one hcpos]; exact hjle
    linarith
  · intro s hs
    rw [hδgoal]
    have hnot : ¬ |t j - s| < δ := by
      intro hcon
      exact hjbad (by
        rw [hbad]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, ⟨s, hs, hcon⟩⟩)
    exact not_lt.mp hnot

end Commons.Analysis.Real