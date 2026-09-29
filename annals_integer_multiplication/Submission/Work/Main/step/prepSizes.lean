import Mathlib
import Submission.Work.Main.defs
import Submission.Work.IntLib.encodeNatBridge

namespace Work.Main.step

open HvdH

/-! ## Elementary size bookkeeping for the values built by the preparation step

These are the five estimates quoted by `Work.Main.step.prep` to justify that the numeric
parameters it feeds into the transform pipeline really do bound the word sizes it later assumes
(`vsz (cvecVal F)`, `vsz (intList ss)`, `isz` of the scaled chunks, the range of `chunks`, and the
extraction of the `m`-th entry of a `cvecVal`). -/

/-- Size of a `cons`-node: the two encodings plus the `cons` marker. -/
theorem psz_vsz_cons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  show (a.enc ++ b.enc).length + 1 = a.enc.length + b.enc.length + 1
  rw [List.length_append]

/-- Exact size of an `ofList` chain of values: the sum of the sizes, one `cons` per element, and the
final `nil`. -/
theorem psz_vsz_ofList : ∀ (vs : List Val), vsz (ofList vs) = (vs.map vsz).sum + vs.length + 1
  | [] => rfl
  | a :: t => by
      rw [show ofList (a :: t) = Val.cons a (ofList t) from rfl, psz_vsz_cons, psz_vsz_ofList t]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      ring

/-- Size of an integer value. -/
theorem psz_vsz_int (z : ℤ) : vsz (Val.int z) = isz z := Work.IntLib.vsz_int z

/-- Size of a fixed-point complex value. -/
theorem psz_vsz_cfxVal (z : ℤ × ℤ) : vsz (cfxVal z) = isz z.1 + isz z.2 + 1 := by
  show vsz (Val.cons (Val.int z.1) (Val.int z.2)) = isz z.1 + isz z.2 + 1
  rw [psz_vsz_cons, psz_vsz_int, psz_vsz_int]

/-- Size of a `cons`-chain of values bounded elementwise by `c`. -/
theorem psz_ofList_sum_le (l : List Val) (c : ℕ) (h : ∀ v ∈ l, vsz v ≤ c) :
    vsz (ofList l) ≤ l.length * (c + 1) + 1 := by
  induction l with
  | nil => simp [ofList, vsz, Val.enc]
  | cons a t ih =>
      have ha : vsz a ≤ c := h a (by simp)
      have ht : ∀ v ∈ t, vsz v ≤ c := fun v hv => h v (by simp [hv])
      have hih : vsz (ofList t) ≤ t.length * (c + 1) + 1 := ih ht
      rw [show ofList (a :: t) = Val.cons a (ofList t) from rfl, psz_vsz_cons]
      simp only [List.length_cons]
      have hsplit : (t.length + 1) * (c + 1) + 1 = t.length * (c + 1) + c + 1 + 1 := by ring
      rw [hsplit]
      omega

/-- Size bound for a `cvecVal`, given elementwise bounds on the coordinates. -/
theorem psz_cvecVal_le (zs : List (ℤ × ℤ)) (p : ℕ)
    (hz : ∀ z ∈ zs, isz z.1 ≤ p + 2 ∧ isz z.2 ≤ p + 2) :
    vsz (cvecVal zs) ≤ zs.length * (2 * p + 6) + 1 := by
  induction zs with
  | nil => simp [cvecVal, ofList, vsz, Val.enc]
  | cons z t ih =>
      have hz1 : isz z.1 ≤ p + 2 := (hz z (by simp)).1
      have hz2 : isz z.2 ≤ p + 2 := (hz z (by simp)).2
      have hih : vsz (cvecVal t) ≤ t.length * (2 * p + 6) + 1 :=
        ih (fun w hw => hz w (by simp [hw]))
      rw [show cvecVal (z :: t) = Val.cons (cfxVal z) (cvecVal t) from rfl, psz_vsz_cons,
        psz_vsz_cfxVal]
      simp only [List.length_cons]
      have hsplit : (t.length + 1) * (2 * p + 6) + 1 = t.length * (2 * p + 6) + 2 * p + 6 + 1 := by
        ring
      rw [hsplit]
      omega

/-- Size bound for an `intList`, given a bound on the bit sizes of the entries. -/
theorem psz_intList_le (l : List ℕ) (B : ℕ) (h : ∀ n ∈ l, n.size ≤ B) :
    vsz (intList l) ≤ l.length * (B + 3) + 1 := by
  induction l with
  | nil => simp [intList, ofList, vsz, Val.enc]
  | cons n t ih =>
      have hn : n.size ≤ B := h n (by simp)
      have hih : vsz (intList t) ≤ t.length * (B + 3) + 1 :=
        ih (fun m hm => h m (by simp [hm]))
      rw [show intList (n :: t) = Val.cons (Val.int (n : ℤ)) (intList t) from rfl, psz_vsz_cons,
        psz_vsz_int, Work.IntLib.isz_eq, Int.natAbs_natCast]
      simp only [List.length_cons]
      have hsplit : (t.length + 1) * (B + 3) + 1 = t.length * (B + 3) + B + 3 + 1 := by ring
      rw [hsplit]
      omega

theorem prepSizes :
    (∀ (zs : List (ℤ × ℤ)) (p : ℕ), (∀ z ∈ zs, HvdH.isz z.1 ≤ p + 2 ∧ HvdH.isz z.2 ≤ p + 2) →
      HvdH.vsz (HvdH.cvecVal zs) ≤ zs.length * (2 * p + 6) + 1) ∧
    (∀ (l : List ℕ) (B : ℕ), (∀ n ∈ l, n.size ≤ B) →
      HvdH.vsz (HvdH.intList l) ≤ l.length * (B + 3) + 1) ∧
    (∀ (n b p : ℕ), b ≤ p → n < 2 ^ b → HvdH.isz (((n : ℤ) * 2 ^ (p - b))) ≤ p + 2) ∧
    (∀ (x b S : ℕ), ∀ n ∈ HvdH.chunks x b S, n < 2 ^ b) ∧
    (∀ (zs : List (ℤ × ℤ)) (m : ℕ), m < zs.length →
      (zs.map HvdH.cfxVal).getD m HvdH.Val.nil = HvdH.cfxVal (zs.getD m (0, 0))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro zs p hz
    exact psz_cvecVal_le zs p hz
  · intro l B hB
    exact psz_intList_le l B hB
  · intro n b p hb hn
    have hzabs : (((n : ℤ) * 2 ^ (p - b)).natAbs) = n * 2 ^ (p - b) := by
      rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow]
      norm_num
    have hlt : n * 2 ^ (p - b) < 2 ^ p := by
      calc n * 2 ^ (p - b) < 2 ^ b * 2 ^ (p - b) :=
            Nat.mul_lt_mul_of_pos_right hn (Nat.pow_pos (by norm_num))
        _ = 2 ^ (b + (p - b)) := (pow_add 2 b (p - b)).symm
        _ = 2 ^ p := by rw [show b + (p - b) = p by omega]
    rw [Work.IntLib.isz_eq, hzabs]
    have hsz := Nat.size_le.mpr hlt
    omega
  · intro x b S n hn
    unfold chunks at hn
    simp only [List.mem_map, List.mem_range] at hn
    obtain ⟨j, hj, rfl⟩ := hn
    exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  · intro zs m hm
    have h1 : m < (zs.map cfxVal).length := by rwa [List.length_map]
    rw [List.getD_eq_getElem _ _ h1]
    rw [List.getElem_map, List.getD_eq_getElem _ _ hm]

end Work.Main.step
