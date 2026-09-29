import Mathlib
import Submission.Work.SB.BW2.Defs
import Submission.Work.SB.slicesFacts
import Submission.Work.SB.phase1

namespace Work.SB.BW2

open HvdH

/-!
# Size bookkeeping for the `branchWord2` cost

`BIG N L = (N+1)*(L+N.size+1)*(N.size+1)` and `S A m B = isz A + isz m + isz B` are the
two size parameters of the `branchWord2` cost.  This file collects the elementary monotonicity
and arithmetic facts about them that the branch programs' cost bounds need, together with the
two size bounds on the input list (`vsz (ofList es) ≤ BIG`) and on its flattened slices
(`vsz (ofList (slices A m B es).flatten) ≤ BIG`).
-/

private lemma BIG_eq (N L : ℕ) : BIG N L = (N+1)*(L+N.size+1)*(N.size+1) := rfl

private lemma one_le_BIG (N L : ℕ) : 1 ≤ BIG N L := by
  rw [BIG_eq]
  exact Nat.succ_le_of_lt (by positivity)

private lemma le_BIG_self (N L : ℕ) : N + 1 ≤ BIG N L := by
  rw [BIG_eq]
  have h : 1 ≤ (L + N.size + 1) * (N.size+1) := Nat.succ_le_of_lt (by positivity)
  calc N + 1 = (N+1)*1 := by ring
    _ ≤ (N+1)*((L + N.size + 1) * (N.size+1)) := Nat.mul_le_mul_left _ h
    _ = (N+1)*(L+N.size+1)*(N.size+1) := by ring

private lemma le_BIG_size (N L : ℕ) : N.size + 1 ≤ BIG N L := by
  rw [BIG_eq]
  have h1 : 1 ≤ N + 1 := by omega
  have h2 : N.size + 1 ≤ L + N.size + 1 := by omega
  have h3 : 1 ≤ N.size + 1 := by omega
  calc N.size + 1 = 1 * ((N.size+1) * 1) := by ring
    _ ≤ (N+1)*((L + N.size + 1) * (N.size+1)) := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    _ = (N+1)*(L + N.size + 1)*(N.size+1) := by ring

private lemma mul_le_BIG (N L : ℕ) : (N+1)*(L+1) ≤ BIG N L := by
  rw [BIG_eq]
  have h : L + 1 ≤ L + N.size + 1 := by omega
  have h2 : 1 ≤ N.size + 1 := by omega
  calc (N+1)*(L+1) ≤ (N+1)*(L + N.size + 1) := Nat.mul_le_mul_left _ h
    _ = (N+1)*(L + N.size + 1)*1 := by ring
    _ ≤ (N+1)*(L + N.size + 1)*(N.size+1) := Nat.mul_le_mul_left ((N+1)*(L + N.size + 1)) h2
    _ = (N+1)*(L+N.size+1)*(N.size+1) := by ring

private lemma S_ge_six (A m B : ℕ) : 6 ≤ S A m B := by
  unfold S
  rw [Work.IntLib.isz_eq, Work.IntLib.isz_eq, Work.IntLib.isz_eq]
  simp only [Int.natAbs_natCast]
  omega

private lemma isz_le_Sa (A m B : ℕ) : isz (A:ℤ) ≤ S A m B := by unfold S; omega
private lemma isz_le_Sm (A m B : ℕ) : isz (m:ℤ) ≤ S A m B := by unfold S; omega
private lemma isz_le_Sb (A m B : ℕ) : isz (B:ℤ) ≤ S A m B := by unfold S; omega

private lemma size_two_le (A m B N L : ℕ) : N.size + 2 ≤ BIG N L + S A m B := by
  have h3 := le_BIG_size N L
  have h6 := S_ge_six A m B
  omega

private lemma isz_zero : isz (((0:ℕ) : ℤ)) = 2 := by
  rw [Work.IntLib.isz_eq]
  have h1 : (((0:ℕ) : ℤ)).natAbs = 0 := by simp
  rw [h1]
  have h2 : (0:ℕ).size ≤ 0 := (Nat.size_le (m := 0) (n := 0)).mpr (by norm_num)
  omega

private lemma isz_natCast_mul_le (A B m N L : ℕ) (hAB : A * B ≤ N) :
    isz (((A*B : ℕ) : ℤ)) ≤ BIG N L + S A m B := by
  have h1 : isz (((A*B : ℕ) : ℤ)) ≤ N.size + 2 := Work.SB.isz_nat_le (A*B) N hAB
  have h2 := size_two_le A m B N L
  omega

private lemma iszAB_le (A m B N L : ℕ) (hAB : A * B ≤ N) :
    isz (A:ℤ) * isz (B:ℤ) ≤ 4 * BIG N L + 4 * S A m B := by
  rcases Nat.eq_zero_or_pos A with hA | hA
  · subst hA
    have h2 : isz (B:ℤ) ≤ S 0 m B := isz_le_Sb 0 m B
    calc isz (((0:ℕ)):ℤ) * isz (B:ℤ) = 2 * isz (B:ℤ) := by rw [isz_zero]
      _ ≤ 2 * S 0 m B := Nat.mul_le_mul_left 2 h2
      _ ≤ 4 * BIG N L + 4 * S 0 m B := by
            have h1 := one_le_BIG N L; omega
  · rcases Nat.eq_zero_or_pos B with hB | hB
    · subst hB
      have h2 : isz (A:ℤ) ≤ S A m 0 := isz_le_Sa A m 0
      calc isz (A:ℤ) * isz (((0:ℕ)):ℤ) = isz (A:ℤ) * 2 := by rw [isz_zero]
        _ = 2 * isz (A:ℤ) := by ring
        _ ≤ 2 * S A m 0 := Nat.mul_le_mul_left 2 h2
        _ ≤ 4 * BIG N L + 4 * S A m 0 := by
              have h1 := one_le_BIG N L; omega
    · have hA' : A ≤ N := le_trans (Nat.le_mul_of_pos_right A hB) hAB
      have hB' : B ≤ N := le_trans (Nat.le_mul_of_pos_left B hA) hAB
      have h1 : isz (A:ℤ) ≤ N.size + 2 := by
        rw [Work.IntLib.isz_eq]
        simp only [Int.natAbs_natCast]
        exact Nat.add_le_add_right (Nat.size_le_size hA') 2
      have h2 : isz (B:ℤ) ≤ N.size + 2 := by
        rw [Work.IntLib.isz_eq]
        simp only [Int.natAbs_natCast]
        exact Nat.add_le_add_right (Nat.size_le_size hB') 2
      have h3 : (N.size+2)*(N.size+2) ≤ 4 * BIG N L := by
        rw [BIG_eq]
        have hle : N.size + 2 ≤ 2 * (N.size + 1) := by omega
        have h6 : (N.size+2)*(N.size+2) ≤ (2*(N.size+1))*(2*(N.size+1)) :=
          Nat.mul_le_mul hle hle
        have h7 : (2*(N.size+1))*(2*(N.size+1)) = 4*((N.size+1)*(N.size+1)) := by ring
        have h8 : (N.size+1)*(N.size+1) ≤ (N+1)*((L+N.size+1)*(N.size+1)) := by
          have h2' : N.size + 1 ≤ L + N.size + 1 := by omega
          have h9 := Nat.mul_le_mul (by omega : 1 ≤ N + 1)
            (Nat.mul_le_mul h2' (le_refl (N.size+1)))
          simpa using h9
        calc (N.size+2)*(N.size+2) ≤ (2*(N.size+1))*(2*(N.size+1)) := h6
          _ = 4*((N.size+1)*(N.size+1)) := h7
          _ ≤ 4*((N+1)*((L+N.size+1)*(N.size+1))) := Nat.mul_le_mul_left 4 h8
          _ = 4*((N+1)*(L+N.size+1)*(N.size+1)) := by ring
      calc isz (A:ℤ) * isz (B:ℤ) ≤ (N.size+2) * (N.size+2) := Nat.mul_le_mul h1 h2
        _ ≤ 4 * BIG N L := h3
        _ ≤ 4 * BIG N L + 4 * S A m B := by omega

private lemma ab_mul_isz_m_le (A m B N L : ℕ) (hAB : A * B ≤ N) (hAmB : A * m * B ≤ N) :
    (A * B + 1) * isz (m:ℤ) ≤ BIG N L + S A m B := by
  rcases Nat.eq_zero_or_pos (A * B) with h | h
  · rw [h]
    have hone : (0 + 1) * isz (m:ℤ) = isz (m:ℤ) := by ring
    rw [hone]
    have hsm := isz_le_Sm A m B
    have h6 := S_ge_six A m B
    have h1 := one_le_BIG N L
    omega
  · have hm : m ≤ A * m * B := by
      have h1 : m ≤ (A*B) * m := Nat.le_mul_of_pos_left m h
      calc m ≤ A*B*m := h1
        _ = A*m*B := by ring
    have hmN : m ≤ N := le_trans hm hAmB
    have hN1 : 1 ≤ N := le_trans h hAB
    have hszm : isz (m:ℤ) ≤ N.size + 2 := Work.SB.isz_nat_le m N hmN
    have hab1 : A * B + 1 ≤ N + 1 := by omega
    have hs2 : 2 ≤ N.size + 1 := by
      have h' := Nat.size_pos.mpr hN1
      omega
    have hkey : N.size + 2 ≤ (N.size+1)*(N.size+1) := by
      have h2 : N.size + 2 ≤ 2*(N.size+1) := by omega
      have h3 : 2*(N.size+1) ≤ (N.size+1)*(N.size+1) := by
        calc 2*(N.size+1) = (N.size+1)*2 := by ring
          _ ≤ (N.size+1)*(N.size+1) := Nat.mul_le_mul_left (N.size+1) hs2
      omega
    calc (A*B+1) * isz (m:ℤ) ≤ (N+1)*(N.size+2) := Nat.mul_le_mul hab1 hszm
      _ ≤ (N+1)*((N.size+1)*(N.size+1)) := Nat.mul_le_mul_left _ hkey
      _ = (N+1)*(N.size+1)*(N.size+1) := by ring
      _ ≤ (N+1)*(L+N.size+1)*(N.size+1) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left (N+1) (by omega : N.size+1 ≤ L+N.size+1))
              (le_refl (N.size+1))
      _ ≤ BIG N L + S A m B := by
            rw [BIG_eq]
            omega

theorem sizeKit (A m B N L : ℕ) (es : List HvdH.Val)
    (hAB : A * B ≤ N) (hAmB : A * m * B ≤ N) (hlen : es.length = A * m * B)
    (hv : ∀ x ∈ es, HvdH.vsz x ≤ L) :
    1 ≤ Work.SB.BW2.BIG N L + Work.SB.BW2.S A m B ∧
    HvdH.vsz (HvdH.ofList es) ≤ Work.SB.BW2.BIG N L ∧
    HvdH.vsz (HvdH.ofList (HvdH.slices A m B es).flatten) ≤ Work.SB.BW2.BIG N L ∧
    HvdH.isz (A : ℤ) ≤ Work.SB.BW2.S A m B ∧
    HvdH.isz (m : ℤ) ≤ Work.SB.BW2.S A m B ∧
    HvdH.isz (B : ℤ) ≤ Work.SB.BW2.S A m B ∧
    HvdH.isz (A : ℤ) + 1 ≤ 2 * (Work.SB.BW2.BIG N L + Work.SB.BW2.S A m B) ∧
    HvdH.isz (m : ℤ) + 1 ≤ 2 * (Work.SB.BW2.BIG N L + Work.SB.BW2.S A m B) ∧
    HvdH.isz (B : ℤ) + 1 ≤ 2 * (Work.SB.BW2.BIG N L + Work.SB.BW2.S A m B) ∧
    HvdH.vsz (HvdH.ofList es) + 1
      ≤ 2 * (Work.SB.BW2.BIG N L + Work.SB.BW2.S A m B) ∧
    HvdH.vsz (HvdH.ofList es) + HvdH.isz (m : ℤ) + 1
      ≤ 2 * (Work.SB.BW2.BIG N L + Work.SB.BW2.S A m B) ∧
    HvdH.vsz (HvdH.ofList es) + HvdH.isz (m : ℤ) + HvdH.isz (B : ℤ) + 1
      ≤ 2 * (Work.SB.BW2.BIG N L + Work.SB.BW2.S A m B) ∧
    HvdH.isz ((A * B : ℕ) : ℤ) ≤ Work.SB.BW2.BIG N L + Work.SB.BW2.S A m B ∧
    2 + HvdH.isz ((A * B : ℕ) : ℤ)
      ≤ 2 * Work.SB.BW2.BIG N L + 2 * Work.SB.BW2.S A m B ∧
    HvdH.isz (A : ℤ) * HvdH.isz (B : ℤ)
      ≤ 4 * Work.SB.BW2.BIG N L + 4 * Work.SB.BW2.S A m B ∧
    2 * (A * B + 1) + HvdH.isz ((A * B : ℕ) : ℤ) + 1
      ≤ 4 * Work.SB.BW2.BIG N L + 4 * Work.SB.BW2.S A m B ∧
    (A * B + 1) * HvdH.isz (m : ℤ) ≤ Work.SB.BW2.BIG N L + Work.SB.BW2.S A m B := by
  have hBIG1 : 1 ≤ BIG N L := one_le_BIG N L
  have hS6 : 6 ≤ S A m B := S_ge_six A m B
  have hSA : isz (A:ℤ) ≤ S A m B := isz_le_Sa A m B
  have hSm : isz (m:ℤ) ≤ S A m B := isz_le_Sm A m B
  have hSB : isz (B:ℤ) ≤ S A m B := isz_le_Sb A m B
  -- sizes of the input list
  have hes : vsz (ofList es) ≤ BIG N L := by
    have h1 : vsz (ofList es) ≤ (es.length + 1) * (L + 1) :=
      Work.SB.Core.vsz_ofList_le (B := L) hv
    have h2 : es.length + 1 ≤ N + 1 := by rw [hlen]; omega
    exact le_trans h1 (le_trans (Nat.mul_le_mul_right (L+1) h2) (mul_le_BIG N L))
  -- sizes of the flattened slices
  have hflat : vsz (ofList (slices A m B es).flatten) ≤ BIG N L := by
    have hlenflat : (slices A m B es).flatten.length = A * m * B :=
      (Work.SB.slicesFacts A m B es).2.2.1
    have hentry : ∀ x ∈ (slices A m B es).flatten, vsz x ≤ L := by
      intro x hx
      by_cases hz : A * m * B = 0
      · have hnil : (slices A m B es).flatten = [] := by
          cases hfl : (slices A m B es).flatten with
          | nil => rfl
          | cons y ys =>
              have hl : A * m * B = (y :: ys).length := by
                rw [← hlenflat, hfl]
              simp only [List.length_cons] at hl
              exfalso
              omega
        rw [hnil] at hx
        simp at hx
      · have hmpos : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h | h
          · exact absurd (by rw [h]; ring) hz
          · exact h
        have hBpos : 0 < B := by
          rcases Nat.eq_zero_or_pos B with h | h
          · exact absurd (by rw [h]; ring) hz
          · exact h
        rw [Work.SB.Core.slicesFlattenEq A m B hmpos hBpos es hlen] at hx
        obtain ⟨t, ht, htx⟩ := List.mem_map.mp hx
        have ht' : t < A * m * B := List.mem_range.mp ht
        have hidx : Work.Layout.invIdx1 m B t < es.length := by
          rw [hlen]
          exact Work.Layout.invIdx1_lt A m B hmpos hBpos t ht'
        rw [← htx]
        exact Work.SB.getD_mem_le es L hv _ hidx
    have h1 : vsz (ofList (slices A m B es).flatten)
        ≤ ((slices A m B es).flatten.length + 1) * (L + 1) :=
      Work.SB.Core.vsz_ofList_le (B := L) hentry
    have h2 : (slices A m B es).flatten.length + 1 ≤ N + 1 := by
      rw [hlenflat]; omega
    exact le_trans h1 (le_trans (Nat.mul_le_mul_right (L+1) h2) (mul_le_BIG N L))
  -- the remaining arithmetic
  have hAB1 : A * B + 1 ≤ BIG N L := by
    have h := le_BIG_self N L
    omega
  have h2AB : 2 * (A * B + 1) ≤ 2 * BIG N L := by
    have h1 : A * B + 1 ≤ N + 1 := by omega
    have h2 := le_BIG_self N L
    omega
  have habm : (A * B + 1) * isz (m:ℤ) ≤ BIG N L + S A m B := ab_mul_isz_m_le A m B N L hAB hAmB
  have hszAB : isz (((A*B : ℕ) : ℤ)) ≤ BIG N L + S A m B := isz_natCast_mul_le A B m N L hAB
  have hmul : isz (A:ℤ) * isz (B:ℤ) ≤ 4 * BIG N L + 4 * S A m B := iszAB_le A m B N L hAB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · exact hes
  · exact hflat
  · exact hSA
  · exact hSm
  · exact hSB
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact hszAB
  · omega
  · exact hmul
  · omega
  · exact habm

end Work.SB.BW2
