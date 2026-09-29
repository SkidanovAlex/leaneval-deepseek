import Mathlib
import Submission.Work.Params.defs
import Submission.Work.Params.basic
import Submission.Work.Params.qall
import Submission.Work.Params.rparbig

/-!
# `constSizesBig`

In the "big `n`" regime (`n.size ≥ 65755586`) every *constant* of the `Params` area —
the small numbers `6, 12d², 1, 4, d-1, d, 2d-1, 4d` together with the huge ones
`F = (d-1)!`, `Q = ∏(2Fk±1)`, `F·Q`, `F·Q-1-Q`, `2F` — has `Nat.size` at most `n.size + 4`.

The only non-elementary input is `F·Q ≤ 2^{n.size}` (`Ffac_mul_Qall_le_size` below, the same
computation as in `listSizesBig`), which is exactly what the threshold `65755586` is for:
`F ≤ 2^19008` and `Q ≤ 2^{65736576}`.
-/

set_option autoImplicit false

namespace Work.Params

open HvdH

/-- If `m ≤ 2 ^ E` then `m` has size at most `E + 1`. -/
private theorem size_le_of_le_pow {m E : ℕ} (h : m ≤ 2 ^ E) : m.size ≤ E + 1 := by
  rw [Nat.size_le]
  calc m ≤ 2 ^ E := h
    _ < 2 ^ E + 1 := Nat.lt_succ_self _
    _ ≤ 2 ^ E + 2 ^ E := Nat.add_le_add_left Nat.one_le_two_pow _
    _ = 2 ^ (E + 1) := by rw [pow_succ]; ring

/-- `F·Q ≤ 2^{n.size}` as soon as `n.size ≥ 65755586`. -/
private theorem Ffac_mul_Qall_le_size (n : ℕ) (hsz : 65755586 ≤ n.size) :
    Ffac * Qall ≤ 2 ^ n.size := by
  have h19008 : 19008 ≤ n.size := by omega
  have hE : 19021 * 3456 ≤ n.size - 19008 := by omega
  have hQ : Qall ≤ 2 ^ (n.size - 19008) := Qall_le_pow _ hE
  calc Ffac * Qall ≤ 2 ^ 19008 * 2 ^ (n.size - 19008) := Nat.mul_le_mul Ffac_le_two_pow hQ
    _ = 2 ^ (19008 + (n.size - 19008)) := (pow_add 2 19008 (n.size - 19008)).symm
    _ = 2 ^ n.size := by rw [Nat.add_sub_of_le h19008]

theorem constSizesBig (n : ℕ) (hsz : 65755586 ≤ n.size) :
    ∀ m ∈ [6, 12 * HvdH.D * HvdH.D, 1, 4, HvdH.D - 1, HvdH.D, 2 * HvdH.D - 1, 4 * HvdH.D,
        Work.Params.Ffac, Work.Params.Qall, Work.Params.Ffac * Work.Params.Qall,
        Work.Params.Ffac * Work.Params.Qall - 1 - Work.Params.Qall, 2 * Work.Params.Ffac],
      m.size ≤ n.size + 4 := by
  have hFQ : Ffac * Qall ≤ 2 ^ n.size := Ffac_mul_Qall_le_size n hsz
  have hQall : Qall ≤ 2 ^ n.size := le_trans (Nat.le_mul_of_pos_left Qall Ffac_pos) hFQ
  have hsub : Ffac * Qall - 1 - Qall ≤ 2 ^ n.size :=
    le_trans (le_trans (Nat.sub_le (Ffac * Qall - 1) Qall) (Nat.sub_le (Ffac * Qall) 1)) hFQ
  have h2F : 2 * Ffac ≤ 2 ^ (n.size + 1) := by
    calc 2 * Ffac ≤ 2 * 2 ^ 19008 := Nat.mul_le_mul_left 2 Ffac_le_two_pow
      _ = 2 ^ (19008 + 1) := (pow_succ' 2 19008).symm
      _ ≤ 2 ^ (n.size + 1) := Nat.pow_le_pow_right (by norm_num : 0 < 2)
          (by omega : 19008 + 1 ≤ n.size + 1)
  have b1 : (6 : ℕ).size ≤ n.size + 4 :=
    le_trans (size_le_of_le_pow (show (6 : ℕ) ≤ 2 ^ 3 by norm_num)) (by omega)
  have b2 : (12 * HvdH.D * HvdH.D).size ≤ n.size + 4 :=
    le_trans (size_le_of_le_pow (show 12 * HvdH.D * HvdH.D ≤ 2 ^ 26 by norm_num [HvdH.D]))
      (by omega)
  have b3 : (1 : ℕ).size ≤ n.size + 4 :=
    le_trans (size_le_of_le_pow (show (1 : ℕ) ≤ 2 ^ 1 by norm_num)) (by omega)
  have b4 : (4 : ℕ).size ≤ n.size + 4 :=
    le_trans (size_le_of_le_pow (show (4 : ℕ) ≤ 2 ^ 2 by norm_num)) (by omega)
  have b5 : (HvdH.D - 1).size ≤ n.size + 4 :=
    le_trans (size_le_of_le_pow (show HvdH.D - 1 ≤ 2 ^ 11 by norm_num [HvdH.D])) (by omega)
  have b6 : HvdH.D.size ≤ n.size + 4 :=
    le_trans (size_le_of_le_pow (show HvdH.D ≤ 2 ^ 11 by norm_num [HvdH.D])) (by omega)
  have b7 : (2 * HvdH.D - 1).size ≤ n.size + 4 :=
    le_trans (size_le_of_le_pow (show 2 * HvdH.D - 1 ≤ 2 ^ 12 by norm_num [HvdH.D])) (by omega)
  have b8 : (4 * HvdH.D).size ≤ n.size + 4 :=
    le_trans (size_le_of_le_pow (show 4 * HvdH.D ≤ 2 ^ 13 by norm_num [HvdH.D])) (by omega)
  have b9 : Ffac.size ≤ n.size + 4 :=
    le_trans (size_le_of_le_pow Ffac_le_two_pow) (by omega)
  have b10 : Qall.size ≤ n.size + 4 := le_trans (size_le_of_le_pow hQall) (by omega)
  have b11 : (Ffac * Qall).size ≤ n.size + 4 := le_trans (size_le_of_le_pow hFQ) (by omega)
  have b12 : (Ffac * Qall - 1 - Qall).size ≤ n.size + 4 :=
    le_trans (size_le_of_le_pow hsub) (by omega)
  have b13 : (2 * Ffac).size ≤ n.size + 4 :=
    le_trans (size_le_of_le_pow h2F) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩

end Work.Params
