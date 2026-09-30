import Mathlib
import Submission.Work.BW.bpOddDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! Auxiliary: `bpOddF η n = ∏_{t<n} (2t+2−η)` is the single-factor product whose product
over the two blocks `A`, `B` gives `bpG η A B`. -/

noncomputable def bpOddF (η : ℝ) (n : ℕ) : ℝ :=
  ∏ t ∈ Finset.range n, (2*(t:ℝ) + 2 - η)

lemma bpG_eq_bpOddF (η : ℝ) (A B : ℕ) : bpG η A B = bpOddF η A * bpOddF η B := rfl

lemma bpOddF_nonneg {η : ℝ} (hη : η ≤ 2) (n : ℕ) : 0 ≤ bpOddF η n := by
  unfold bpOddF
  apply Finset.prod_nonneg
  intro t ht
  have : (0:ℝ) ≤ (t:ℝ) := Nat.cast_nonneg t
  linarith

lemma bpOddF_pos {η : ℝ} (hη : η < 2) (n : ℕ) : 0 < bpOddF η n := by
  unfold bpOddF
  apply Finset.prod_pos
  intro t ht
  have : (0:ℝ) ≤ (t:ℝ) := Nat.cast_nonneg t
  linarith

lemma bpOddF_add (η : ℝ) (i j : ℕ) :
    bpOddF η (i + j) = bpOddF η i * ∏ t ∈ Finset.range j, (2*((i+t:ℕ):ℝ) + 2 - η) := by
  unfold bpOddF
  rw [Finset.prod_range_add]

lemma bpG_comm (η : ℝ) (A B : ℕ) : bpG η A B = bpG η B A := by
  rw [bpG_eq_bpOddF, bpG_eq_bpOddF, mul_comm]

/-- Shift of the index: `bpOddF η m = (2−η)·∏_{t<m−1}(2t+4−η)`. -/
lemma bpOddF_shift (η : ℝ) (n : ℕ) :
    bpOddF η (n+1) = (∏ t ∈ Finset.range n, (2*(t:ℝ) + 4 - η)) * (2 - η) := by
  unfold bpOddF
  rw [Finset.prod_range_succ']
  congr 1
  · apply Finset.prod_congr rfl
    intro t ht
    push_cast
    ring
  · ring

/-- The balanced split is the minimum, quantitatively: at `A = m−1`, `B = m` the value
`bpG η (m−1) m` is at least `2(1−η/2)·bpNum m`, by comparing `(2t+2−η)(2t+4−η) ≥ (2t+1)(2t+3)`
term by term (difference `(1−η)(4t+5−η) ≥ 0`). -/
lemma bpG_balanced_lower {η : ℝ} (hη : η ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    2 * (1 - η/2) * bpNum m ≤ bpG η (m - 1) m := by
  have hshift : bpOddF η m = (∏ t ∈ Finset.range (m-1), (2*(t:ℝ) + 4 - η)) * (2 - η) := by
    have h := bpOddF_shift η (m-1)
    rwa [Nat.sub_add_cancel hm] at h
  have h2η : 2 * (1 - η/2) = 2 - η := by ring
  rw [h2η, bpG_eq_bpOddF, hshift]
  unfold bpNum
  have hND : bpOddF η (m-1) * (∏ t ∈ Finset.range (m-1), (2*(t:ℝ) + 4 - η))
      = ∏ t ∈ Finset.range (m-1), ((2*(t:ℝ)+2-η)*(2*(t:ℝ)+4-η)) := by
    rw [bpOddF, Finset.prod_mul_distrib]
  have hpt : (∏ t ∈ Finset.range (m-1), ((2*(t:ℝ)+1)*(2*(t:ℝ)+3)))
      ≤ ∏ t ∈ Finset.range (m-1), ((2*(t:ℝ)+2-η)*(2*(t:ℝ)+4-η)) := by
    apply Finset.prod_le_prod₀
    · intro t ht
      have ht0 : (0:ℝ) ≤ (t:ℝ) := Nat.cast_nonneg t
      have ha : (0:ℝ) ≤ 2*(t:ℝ)+1 := by linarith
      have hb : (0:ℝ) ≤ 2*(t:ℝ)+3 := by linarith
      exact mul_nonneg ha hb
    · intro t ht
      have ht0 : (0:ℝ) ≤ (t:ℝ) := Nat.cast_nonneg t
      have h1 : (0:ℝ) ≤ 1 - η := by linarith
      have h2 : (0:ℝ) ≤ 4*(t:ℝ) + 5 - η := by linarith
      nlinarith [mul_nonneg h1 h2]
  have hmain : (∏ t ∈ Finset.range (m-1), ((2*(t:ℝ)+1)*(2*(t:ℝ)+3)))
      ≤ bpOddF η (m-1) * (∏ t ∈ Finset.range (m-1), (2*(t:ℝ) + 4 - η)) := by
    rw [hND]; exact hpt
  have hpos : (0:ℝ) ≤ 2 - η := by linarith
  have e1 := mul_le_mul_of_nonneg_left hmain hpos
  have e2 : (2 - η) * (bpOddF η (m-1) * (∏ t ∈ Finset.range (m-1), (2*(t:ℝ) + 4 - η)))
      = bpOddF η (m-1) * ((∏ t ∈ Finset.range (m-1), (2*(t:ℝ) + 4 - η)) * (2 - η)) := by ring
  linarith [e1, e2]

/-- The balanced split minimises `bpG` over `A + B = 2m−1`: when `A ≤ m−1` (so `B = m + k`
with `k = m−1−A`), both factors decompose as `bpOddF A · (extra)` and `bpOddF m · (extra)`,
and the two `extra` products compare term by term. -/
lemma bpG_balanced_min {η : ℝ} (hη : η < 2) {m A B : ℕ} (hm : 1 ≤ m)
    (hAB : A + B = 2*m - 1) (hA : A ≤ m - 1) :
    bpG η (m - 1) m ≤ bpG η A B := by
  set k := (m - 1) - A with hk
  have hAk : A + k = m - 1 := by omega
  have hBk : m + k = B := by omega
  have h1 : bpOddF η (m - 1)
      = bpOddF η A * (∏ t ∈ Finset.range k, (2*((A+t:ℕ):ℝ)+2-η)) := by
    rw [← hAk]; exact bpOddF_add η A k
  have h2 : bpOddF η B
      = bpOddF η m * (∏ t ∈ Finset.range k, (2*((m+t:ℕ):ℝ)+2-η)) := by
    rw [← hBk]; exact bpOddF_add η m k
  have hpt : (∏ t ∈ Finset.range k, (2*((A+t:ℕ):ℝ)+2-η))
      ≤ (∏ t ∈ Finset.range k, (2*((m+t:ℕ):ℝ)+2-η)) := by
    apply Finset.prod_le_prod₀
    · intro t ht
      have : (0:ℝ) ≤ ((A+t:ℕ):ℝ) := Nat.cast_nonneg _
      linarith
    · intro t ht
      have hle : A + t ≤ m + t := by omega
      have hcast : ((A+t:ℕ):ℝ) ≤ ((m+t:ℕ):ℝ) := by exact_mod_cast hle
      linarith
  have hFA : (0:ℝ) ≤ bpOddF η A := bpOddF_nonneg (by linarith) A
  have hFm : (0:ℝ) ≤ bpOddF η m := bpOddF_nonneg (by linarith) m
  rw [bpG_eq_bpOddF, bpG_eq_bpOddF, h1, h2]
  have e1 : bpOddF η A * (∏ t ∈ Finset.range k, (2*((A+t:ℕ):ℝ)+2-η))
      ≤ bpOddF η A * (∏ t ∈ Finset.range k, (2*((m+t:ℕ):ℝ)+2-η)) :=
    mul_le_mul_of_nonneg_left hpt hFA
  have e2 : bpOddF η A * (∏ t ∈ Finset.range k, (2*((A+t:ℕ):ℝ)+2-η)) * bpOddF η m
      ≤ bpOddF η A * (∏ t ∈ Finset.range k, (2*((m+t:ℕ):ℝ)+2-η)) * bpOddF η m :=
    mul_le_mul_of_nonneg_right e1 hFm
  have e3 : bpOddF η A * (∏ t ∈ Finset.range k, (2*((m+t:ℕ):ℝ)+2-η)) * bpOddF η m
      = bpOddF η A * (bpOddF η m * (∏ t ∈ Finset.range k, (2*((m+t:ℕ):ℝ)+2-η))) := by ring
  linarith [e2, e3]

/-- Minimisation of `bpG η A B = ∏_{t<A}(2t+2−η)·∏_{t<B}(2t+2−η)` over `A + B = 2m−1`:
the ratio of consecutive values is `(2A+2−η)/(2B−η)`, so the minimum sits at the balanced split
`{A,B} = {m−1,m}`; there `bpG η (m−1) m = (2−η)·∏_{t=1}^{m−1}(2t−η)(2t+2−η)`, and
`(2t−η)(2t+2−η) − (2t−1)(2t+1) = 4t(1−η) + (1−η)² ≥ 0` gives
`bpG η (m−1) m ≥ (2−η)·bpNum m = 2(1−η/2)·bpNum m`. -/
theorem bpOdd_dist_arith {η : ℝ} (hη : 0 < η) (hη' : η < 1/2) {m : ℕ} (hm : 1 ≤ m) {A B : ℕ}
    (hAB : A + B = 2*m - 1) :
    2 * (1 - η/2) * bpNum m ≤ bpG η A B := by
  have hη2 : η < 2 := by linarith
  have hη1 : η ≤ 1 := by linarith
  have hlow := bpG_balanced_lower (η := η) hη1 hm
  by_cases hAle : A ≤ m - 1
  · exact le_trans hlow (bpG_balanced_min hη2 hm hAB hAle)
  · have hB : B ≤ m - 1 := by omega
    have hBA : B + A = 2*m - 1 := by omega
    have hmin := bpG_balanced_min (η := η) hη2 hm hBA hB
    calc 2 * (1 - η/2) * bpNum m ≤ bpG η (m - 1) m := hlow
      _ ≤ bpG η B A := hmin
      _ = bpG η A B := bpG_comm η B A

end Work.BW
