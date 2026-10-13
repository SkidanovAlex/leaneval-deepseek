import Mathlib
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Norm.HomoDefs

namespace Work.DSCOH.Struct

open Work.DSCOH.Norm

variable {ι : Type*} [LinearOrder ι]

/-- `Fin.succAbove` increases the value by at most one. -/
lemma succAbove_val_le {N : ℕ} (b : Fin (N + 1)) (c : Fin N) :
    (b.succAbove c).val ≤ c.val + 1 := by
  by_cases h : c.castSucc < b
  · rw [Fin.succAbove_of_castSucc_lt b c h, Fin.val_castSucc]; omega
  · have h2 : (b.succAbove c).val = c.val + 1 := by
      rw [Fin.succAbove_of_le_castSucc b c (not_lt.mp h), Fin.val_succ]
    omega

/-- `(-1 : ℤ) ^ n` is invariant under adding two to the exponent. -/
lemma negOne_pow_add_two (n : ℕ) : (-1 : ℤ) ^ (n + 2) = (-1 : ℤ) ^ n := by
  rw [pow_add]; norm_num

/-- `(-1) ^ (b + (N - 1)) = - (-1) ^ (N + b)` for `N ≥ 1`. -/
lemma negOne_pow_eq_neg (N b : ℕ) (h : 1 ≤ N) :
    (-1 : ℤ) ^ (b + (N - 1)) = -(-1 : ℤ) ^ (N + b) := by
  have h1 : N + b + 1 = (b + (N - 1)) + 2 := by omega
  rw [show -(-1 : ℤ) ^ (N + b) = (-1 : ℤ) ^ (N + b + 1) from by rw [pow_succ]; ring,
    h1, negOne_pow_add_two]

/-- If a nondecreasing tuple which is not strictly increasing takes equal values at `u < v`,
then the first repeat position is at most `v - 1`. -/
lemma frA_val_le_pred {k : ℕ} (y : Fin (k + 2) → ι) (hy : Monotone y) (hh : ¬ StrictMono y)
    {u v : Fin (k + 2)} (huv : u < v) (h : y u = y v) :
    (frA y hy hh).val ≤ v.val - 1 := by
  set p : Fin (k + 1) := ⟨v.val - 1, by have := v.isLt; omega⟩ with hp
  have hpv : p.val = v.val - 1 := by simp [hp]
  have hpe : (p.castSucc : Fin (k + 2)).val = v.val - 1 := by rw [Fin.val_castSucc, hpv]
  have hlt' : u.val < v.val := huv
  have hu_le : u ≤ p.castSucc := by rw [Fin.le_def, hpe]; omega
  have hp_le : p.castSucc ≤ v := by rw [Fin.le_def, hpe]; omega
  have hps : p.succ = v := by
    apply Fin.ext; rw [Fin.val_succ, hpv]; omega
  have hyuv : y p.castSucc = y p.succ := by
    rw [hps]
    exact le_antisymm (hy hp_le) (by rw [← h]; exact hy hu_le)
  have hle := firstRepeat_le y hy hh p hyuv
  rw [Fin.le_def] at hle
  rw [hpv] at hle
  exact hle

theorem readD_lt {k : ℕ} {ι : Type*} [LinearOrder ι] (y : Fin (k + 2) → ι)
    (hy : Monotone y) (hh : ¬ StrictMono y) (b : Fin (k + 2))
    (hb : (b : ℕ) < (Work.DSCOH.Norm.frA y hy hh : ℕ)) :
    Work.DSCOH.Norm.readD y hy hh b =
        Work.DSCOH.Norm.del (Work.DSCOH.Norm.dup y (Work.DSCOH.Norm.frA y hy hh).castSucc)
          b.castSucc ∧
      Work.DSCOH.Norm.signD y hy hh b =
        -(-1 : ℤ) ^ ((Work.DSCOH.Norm.frA y hy hh : ℕ) + (b : ℕ)) := by
  have ha : frA y hy hh ≠ 0 := by
    intro h
    rw [h] at hb
    simp at hb
  have hA1 : 1 ≤ (frA y hy hh).val := by omega
  -- the witness that `del y b` has a repeat at `frA - 1`
  have hrep : del y b ((frA y hy hh).pred ha).castSucc
      = del y b ((frA y hy hh).pred ha).succ := by
    have hb1 : b ≤ (((frA y hy hh).pred ha).castSucc).castSucc := by
      rw [Fin.le_def, Fin.val_castSucc, Fin.val_castSucc, Fin.val_pred]; omega
    have hb2 : b ≤ (((frA y hy hh).pred ha).succ).castSucc := by
      rw [Fin.le_def, Fin.val_castSucc, Fin.val_succ, Fin.val_pred]; omega
    have e1 : b.succAbove ((frA y hy hh).pred ha).castSucc = (frA y hy hh).castSucc := by
      rw [Fin.succAbove_of_le_castSucc b ((frA y hy hh).pred ha).castSucc hb1]
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_pred]; omega
    have e2 : b.succAbove ((frA y hy hh).pred ha).succ = (frA y hy hh).succ := by
      rw [Fin.succAbove_of_le_castSucc b ((frA y hy hh).pred ha).succ hb2]
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_pred]; omega
    simp only [del_apply]
    rw [e1, e2]
    exact firstRepeat_spec y hy hh
  have hz_not : ¬ StrictMono (del y b) := by
    intro hsm
    have hlt : ((frA y hy hh).pred ha).castSucc < ((frA y hy hh).pred ha).succ :=
      Fin.castSucc_lt_succ
    have := hsm hlt
    rw [hrep] at this
    exact absurd this (lt_irrefl _)
  -- any repeat position of `del y b` is at least `frA - 1`
  have key : ∀ i : Fin k, del y b i.castSucc = del y b i.succ → (frA y hy hh).pred ha ≤ i := by
    intro i hi
    have huv : b.succAbove i.castSucc < b.succAbove i.succ :=
      Fin.strictMono_succAbove b (Fin.castSucc_lt_succ (i := i))
    have hyuv : y (b.succAbove i.castSucc) = y (b.succAbove i.succ) := by
      simpa only [del_apply] using hi
    have hAle := frA_val_le_pred y hy hh huv hyuv
    have hvle : (b.succAbove i.succ).val ≤ i.val + 2 := by
      have := succAbove_val_le b i.succ
      rw [Fin.val_succ] at this
      omega
    rw [Fin.le_def, Fin.val_pred]
    omega
  have hfr : firstRepeat (del y b) (monotone_del y b hy) hz_not = (frA y hy hh).pred ha := by
    apply le_antisymm
    · exact firstRepeat_le (del y b) (monotone_del y b hy) hz_not _ hrep
    · exact key _ (firstRepeat_spec (del y b) (monotone_del y b hy) hz_not)
  have hreadD : readD y hy hh b = dup (del y b) ((frA y hy hh).pred ha).castSucc := by
    unfold readD
    rw [dif_neg hz_not, hfr]
  have hsignD : signD y hy hh b = (-1 : ℤ) ^ (b.val + ((frA y hy hh).pred ha).val) := by
    unfold signD
    rw [dif_neg hz_not, hfr]
  refine ⟨?_, ?_⟩
  · rw [hreadD]
    funext i
    simp only [dup_apply, del_apply]
    exact congrArg y (succAbove_predAbove_lt (frA y hy hh) ha b hb i)
  · rw [hsignD, Fin.val_pred]
    exact negOne_pow_eq_neg (frA y hy hh).val b.val hA1

end Work.DSCOH.Struct
