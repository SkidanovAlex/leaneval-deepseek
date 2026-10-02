import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.KahnPartition
import Submission.Work.Deep.Prob.Colouring.card_weighted_dev_le

open scoped BigOperators

namespace Work.Deep.Nibble

/-- **Chernoff count for the intersection of a set with a random part.**  With `π : Fin n → Fin p` a uniform random function (`p ≥ 2`) and a fixed set `S ⊆ Fin n`, the number of vertices of `S` landing in a fixed part `i` is `Bin(|S|, 1/p)`, so for `k ≥ |S|/p` the number of `π` with `k ≤ |S ∩ part i|` is at most `p^n · 2 exp(-(k - |S|/p)²/(2(|S|/p + (k - |S|/p)/3)))`.  This is a direct corollary of `Work.Deep.Prob.Colouring.card_weighted_dev_le` (with all weights `1`, `C = 1`), after splitting `π` into its restrictions to `S` and to the complement and multiplying by the number `p^{n-|S|}` of free choices. -/
theorem partBalCount {n p : ℕ} (hp : 2 ≤ p) (S : Set (Fin n)) (i : Fin p) {k : ℕ}
    (hk : (S.ncard : ℝ) / (p : ℝ) ≤ (k : ℝ)) :
    ((Finset.univ.filter (fun π : Fin n → Fin p =>
        k ≤ (S ∩ partSet π i).ncard)).card : ℝ)
      ≤ (p : ℝ) ^ n * (2 * Real.exp (-(((k : ℝ) - (S.ncard : ℝ) / (p : ℝ)) ^ 2)
          / (2 * ((S.ncard : ℝ) / (p : ℝ) + ((k : ℝ) - (S.ncard : ℝ) / (p : ℝ)) / 3)))) := by
  classical
  set X : Fin n → ℝ := fun r => if r ∈ S then 1 else 0 with hXdef
  set τ : ℝ := (k : ℝ) - (S.ncard : ℝ) / (p : ℝ) with hτdef
  have hτ : 0 ≤ τ := by rw [hτdef]; linarith
  have hX0 : ∀ r, 0 ≤ X r := by
    intro r; rw [hXdef]; by_cases h : r ∈ S <;> simp [h]
  have hXC : ∀ r, X r ≤ (1 : ℝ) := by
    intro r; rw [hXdef]; by_cases h : r ∈ S <;> simp [h]
  have hnf : ∀ T : Set (Fin n),
      T.ncard = (Finset.univ.filter (fun r : Fin n => r ∈ T)).card := by
    intro T
    rw [Set.ncard_eq_toFinset_card]
    congr 1
    ext x
    simp
  have hXsum : (∑ r : Fin n, X r) = (S.ncard : ℝ) := by
    have e1 : (∑ r : Fin n, X r)
        = ((Finset.univ.filter (fun r : Fin n => r ∈ S)).card : ℝ) := by
      rw [Finset.card_eq_sum_ones]
      push_cast
      rw [Finset.sum_filter]
    rw [e1, hnf S]
  have hcount : ∀ π : Fin n → Fin p,
      ((S ∩ partSet π i).ncard : ℝ)
        = ∑ r : Fin n, (if π r = i then X r else 0) := by
    intro π
    rw [hnf (S ∩ partSet π i)]
    rw [Finset.card_eq_sum_ones]
    push_cast
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    rw [hXdef]
    by_cases h1 : r ∈ S <;> by_cases h2 : π r = i <;> simp [h1, h2, partSet]
  have hsub : (Finset.univ.filter (fun π : Fin n → Fin p =>
        k ≤ (S ∩ partSet π i).ncard))
      ⊆ (Finset.univ.filter (fun π : Fin n → Fin p =>
        τ ≤ |(∑ r : Fin n, (if π r = i then X r else 0)) - (∑ r : Fin n, X r) / (p : ℝ)|)) := by
    intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    have hk' : (k : ℝ) ≤ ((S ∩ partSet π i).ncard : ℝ) := by exact_mod_cast hπ
    rw [← hcount π, hXsum, hτdef]
    rw [abs_of_nonneg (by linarith)]
    linarith
  calc ((Finset.univ.filter (fun π : Fin n → Fin p =>
          k ≤ (S ∩ partSet π i).ncard)).card : ℝ)
      ≤ ((Finset.univ.filter (fun π : Fin n → Fin p =>
          τ ≤ |(∑ r : Fin n, (if π r = i then X r else 0))
                - (∑ r : Fin n, X r) / (p : ℝ)|)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (p : ℝ) ^ (Fintype.card (Fin n)) *
          (2 * Real.exp (-(τ ^ 2)
            / (2 * (1 : ℝ) * ((∑ r : Fin n, X r) / (p : ℝ) + τ / 3)))) :=
        _root_.Work.Deep.Prob.Colouring.card_weighted_dev_le hp X hX0 (by norm_num) hXC i hτ
    _ = (p : ℝ) ^ n * (2 * Real.exp (-(((k : ℝ) - (S.ncard : ℝ) / (p : ℝ)) ^ 2)
          / (2 * ((S.ncard : ℝ) / (p : ℝ) + ((k : ℝ) - (S.ncard : ℝ) / (p : ℝ)) / 3)))) := by
        rw [Fintype.card_fin, hXsum, hτdef]
        norm_num

end Work.Deep.Nibble
