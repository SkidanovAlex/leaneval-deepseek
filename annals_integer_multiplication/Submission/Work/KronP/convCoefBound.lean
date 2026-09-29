import Mathlib
import Submission.Work.KronP.kdefs
import Submission.Work.KronP.math

/-!
# Bound on the convolution coefficients of two length-`r` integer lists

If `l₁, l₂` are lists of length `r` with all entries of absolute value `≤ 2^p`, and
`r < 2^{p-1}`, then every convolution coefficient `Work.KronP.convCoef l₁ l₂ m` satisfies
`2·|coeff| < 2^{3p}`.  This is the ingredient that makes the base-`2^{3p}` digits of the packed
product well defined (paper Lemma 2.5).

The proof bounds `|coeff|` by `r·2^{2p}` (at most `r` terms, each of absolute value `≤ 2^{2p}`),
and `r < 2^{p-1}` gives `2r < 2^p`, whence `2·|coeff| ≤ 2r·2^{2p} < 2^{3p}`.
-/

set_option autoImplicit false

namespace Work.KronP

/-- `getD` of a list whose entries are bounded stays bounded. -/
theorem getD_natAbs_le {l : List ℤ} {L : ℕ} (h : ∀ x ∈ l, x.natAbs ≤ L) (k : ℕ) :
    (l.getD k 0).natAbs ≤ L := by
  rcases lt_or_ge k l.length with hk | hk
  · rw [List.getD_eq_getElem _ _ hk]
    exact h _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ hk]
    simp

/-- `|Σ aᵢ| ≤ length · L` when every entry has absolute value `≤ L`. -/
theorem sum_natAbs_le {l : List ℤ} {L : ℕ} (h : ∀ x ∈ l, x.natAbs ≤ L) :
    l.sum.natAbs ≤ l.length * L := by
  refine le_trans (natAbs_sum_le_map l) ?_
  have h1 : (l.map Int.natAbs).sum ≤ (l.map (fun _ => L)).sum := by
    apply List.sum_le_sum
    intro x hx
    exact h x hx
  have h2 : (l.map (fun _ => L)).sum = l.length * L := by
    simp
  rw [h2] at h1
  exact h1

/-- Every convolution coefficient of two lists with entries bounded by `L` is bounded by
`l₁.length · L²`. -/
theorem convCoef_natAbs_le {l₁ l₂ : List ℤ} {L : ℕ}
    (hb₁ : ∀ x ∈ l₁, x.natAbs ≤ L) (hb₂ : ∀ x ∈ l₂, x.natAbs ≤ L) (m : ℕ) :
    (convCoef l₁ l₂ m).natAbs ≤ l₁.length * (L * L) := by
  have hterm : ∀ x ∈ (((List.range (min l₁.length (m + 1))).filter
      (fun j => m - j < l₂.length)).map (fun j => l₁.getD j 0 * l₂.getD (m - j) 0)),
      x.natAbs ≤ L * L := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (getD_natAbs_le hb₁ j) (getD_natAbs_le hb₂ (m - j))
  unfold convCoef
  refine le_trans (sum_natAbs_le hterm) ?_
  rw [List.length_map]
  apply Nat.mul_le_mul_right
  have h1 : (((List.range (min l₁.length (m + 1))).filter
      (fun j => m - j < l₂.length))).length ≤ (List.range (min l₁.length (m + 1))).length :=
    List.length_filter_le _ _
  rw [List.length_range] at h1
  exact le_trans h1 (Nat.min_le_left _ _)

/-- Main estimate: with `r < 2^{p-1}` and entries bounded by `2^p`, twice each convolution
coefficient is `< 2^{3p}`. -/
theorem convCoefBound {p r : ℕ} (hp : 1 ≤ p) (hr : r < 2 ^ (p - 1)) {l₁ l₂ : List ℤ}
    (h₁ : l₁.length = r) (h₂ : l₂.length = r) (hb₁ : ∀ x ∈ l₁, x.natAbs ≤ 2 ^ p)
    (hb₂ : ∀ x ∈ l₂, x.natAbs ≤ 2 ^ p) (m : ℕ) :
    2 * (Work.KronP.convCoef l₁ l₂ m).natAbs < 2 ^ (3 * p) := by
  have hle : (convCoef l₁ l₂ m).natAbs ≤ r * (2 ^ p * 2 ^ p) := by
    rw [← h₁]
    exact convCoef_natAbs_le hb₁ hb₂ m
  have h2r : 2 * r < 2 ^ p := by
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp
    have hle' : r + 1 ≤ 2 ^ (p - 1) := Nat.lt_iff_add_one_le.mp hr
    have h2 : 2 * (r + 1) ≤ 2 * 2 ^ (p - 1) := Nat.mul_le_mul_left 2 hle'
    have hpow : 2 * 2 ^ (p - 1) = 2 ^ p := by rw [← pow_succ', hp1]
    rw [hpow] at h2
    omega
  calc 2 * (convCoef l₁ l₂ m).natAbs
      ≤ 2 * (r * (2 ^ p * 2 ^ p)) := Nat.mul_le_mul_left 2 hle
    _ = (2 * r) * (2 ^ p * 2 ^ p) := by ring
    _ < 2 ^ p * (2 ^ p * 2 ^ p) := Nat.mul_lt_mul_of_pos_right h2r (by positivity)
    _ = 2 ^ (3 * p) := by
        rw [← pow_add, ← pow_add]
        congr 1
        ring

end Work.KronP
