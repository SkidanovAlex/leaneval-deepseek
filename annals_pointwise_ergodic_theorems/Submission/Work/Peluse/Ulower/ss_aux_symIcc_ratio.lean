import Mathlib
import Submission.Work.Peluse.Ulower.ss_char_entry_defs

namespace Work.Peluse.Ulower

set_option linter.unusedVariables false

/-- The scalar arithmetic behind `ss_aux_symIcc_ratio`: for `A ≥ 3`, `k ≥ 1`, `Ns ≥ 1`,
`Ns ≤ L` and `M ≤ A · Ns` one has

`2 / (3 A k) ≤ (2 L + 1) / (k (2 M + 1))`.

Indeed `M ≤ A·Ns ≤ A·L` gives `2(2M+1) ≤ 2(2AL+1) ≤ 3A(2L+1)` (using `A ≥ 1`, `L ≥ 1`), and
multiplying by `k > 0` gives the claim after clearing denominators. -/
private lemma ss_aux_symIcc_ratio_arith {A k L M Ns : ℕ} (hA : 3 ≤ A) (hk : 1 ≤ k)
    (hNs : 1 ≤ Ns) (hLge : Ns ≤ L) (hMle : M ≤ A * Ns) :
    2 / (3 * (A : ℝ) * (k : ℝ)) ≤ (2 * (L : ℝ) + 1) / ((k : ℝ) * (2 * (M : ℝ) + 1)) := by
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast (by omega : 1 ≤ A)
  have hA3 : (3 : ℝ) ≤ A := by exact_mod_cast hA
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hML : (M : ℝ) ≤ (A : ℝ) * (Ns : ℝ) := by exact_mod_cast hMle
  have hNs1 : (1 : ℝ) ≤ Ns := by exact_mod_cast hNs
  have hLN : (Ns : ℝ) ≤ L := by exact_mod_cast hLge
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hkey : 2 * (2 * (M : ℝ) + 1) ≤ 3 * (A : ℝ) * (2 * (L : ℝ) + 1) := by nlinarith
  nlinarith [hkey, hk1]

/-- The symmetric interval `symIcc L = [-L,L]` has `2L+1` elements. -/
private lemma ss_aux_symIcc_ratio_card (L : ℕ) :
    ((Work.Peluse.symIcc L).card : ℝ) = 2 * (L : ℝ) + 1 := by
  rw [Work.Peluse.symIcc, Int.card_Icc]
  have h : ((L : ℤ) + 1 - -((L : ℤ))) = ((2 * L + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]
  push_cast
  ring

/-- **The size ratio of the two support boxes of the `U²`-inverse entry.**  With
`P : ℤ[X]`, `c ≠ 0`, `1 ≤ Ns`, `1 ≤ D` and `L'' := max (dSup P Ns N / |c| + 1) D ≤ ssAmax P · Ns`,

`2 / (3 · ssAmax P · |c|) ≤ |symIcc (dSup P Ns N)| / (|c| · |symIcc L''|)`,

i.e. the decimated box is smaller than the original one by at most the explicit constant
`3 · ssAmax P · |c| / 2` (`ssAmax P = 3 + 2 ∑|a_i|` is the constant of
`Ulower/ss_char_entry_defs`).  This is the elementary cardinality bookkeeping of the entrance
`ss_char_entry`. -/
theorem ss_aux_symIcc_ratio {P : Polynomial ℤ} {c : ℤ} (hc : c ≠ 0) {Ns N D : ℕ}
    (hc1 : 1 ≤ c.natAbs) (hNs : 1 ≤ Ns) (hD : 1 ≤ D)
    (hL'' : max ((Work.Peluse.dSup P Ns N) / c.natAbs + 1) D ≤ Work.Peluse.Ulower.ssAmax P * Ns) :
    2 / (3 * (Work.Peluse.Ulower.ssAmax P : ℝ) * (c.natAbs : ℝ)) ≤
      ((Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)).card : ℝ) /
        ((c.natAbs : ℝ) *
          ((Work.Peluse.symIcc (max ((Work.Peluse.dSup P Ns N) / c.natAbs + 1) D)).card : ℝ)) := by
  rw [ss_aux_symIcc_ratio_card, ss_aux_symIcc_ratio_card]
  refine ss_aux_symIcc_ratio_arith (three_le_ssAmax P) hc1 hNs ?_ hL''
  rw [Work.Peluse.dSup]
  exact Nat.le_add_right _ _

end Work.Peluse.Ulower
