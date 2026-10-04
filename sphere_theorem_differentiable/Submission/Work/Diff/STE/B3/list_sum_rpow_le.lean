import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-- Auxiliary form of the target, indexed by `Fin n` (so that the Finset form of Jensen's
inequality applies directly). -/
private lemma ofFn_sum_rpow_le {p : ℝ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n) {f : Fin n → ℝ}
    (hf : ∀ i, 0 ≤ f i) :
    (List.ofFn f).sum ^ p ≤ (n : ℝ) ^ p * (List.ofFn (fun i => f i ^ p)).sum := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hSn : 0 ≤ ∑ i : Fin n, f i ^ p :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) p
  have hmain := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (Finset.univ : Finset (Fin n)) hp
    (fun i _ => hf i)
  rw [Finset.card_univ, Fintype.card_fin] at hmain
  rw [List.sum_ofFn, List.sum_ofFn]
  exact hmain.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) hSn)

/-- For a list of nonnegative reals and an exponent `p ≥ 1`, the `p`-th power of the sum is
bounded by the number of terms to the `p`, times the sum of the `p`-th powers. -/
theorem list_sum_rpow_le {p : ℝ} (hp : 1 ≤ p) (L : List ℝ) (hL : ∀ z ∈ L, 0 ≤ z) :
    L.sum ^ p ≤ (L.length : ℝ) ^ p * (L.map (fun z => z ^ p)).sum := by
  have hp0 : p ≠ 0 := by linarith
  rcases eq_or_ne L.length 0 with hn | hn
  · have hnil : L = [] := List.length_eq_zero_iff.mp hn
    subst hnil
    simp [Real.zero_rpow hp0]
  · have hn1 : 1 ≤ L.length := Nat.one_le_iff_ne_zero.mpr hn
    have h := ofFn_sum_rpow_le (p := p) hp hn1 (f := L.get) (fun i => hL _ (List.get_mem L i))
    rw [List.ofFn_get L] at h
    have step : (List.ofFn (fun i => L.get i ^ p)) = L.map (fun z => z ^ p) := by
      rw [← List.ofFn_getElem_eq_map L (fun z => z ^ p)]
      congr 1
    rw [step] at h
    exact h

end Work.Diff.STE.B3
