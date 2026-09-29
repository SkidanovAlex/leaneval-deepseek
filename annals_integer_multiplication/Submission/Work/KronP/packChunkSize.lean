import Mathlib
import Submission.Work.KronP.defs
import Submission.Work.IntLib.chunksAPI

namespace Work.KronP

open HvdH

/-- Telescoping identity behind the geometric bound for `evalChunks`. -/
theorem pow_geom_step (b t : ℕ) :
    (2 ^ b - 1) + 2 ^ b * (2 ^ (b * t) - 1) = 2 ^ (b * (t + 1)) - 1 := by
  rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.pow_add]
  have h : b + b * t = b * (t + 1) := by ring
  rw [h]
  have hle : 2 ^ b ≤ 2 ^ (b * (t + 1)) := by
    apply Nat.pow_le_pow_right (by norm_num); nlinarith
  have h1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  omega

/-- Exact geometric bound: for digits `< 2^{3b}`,
`evalChunks hs b · (2^b - 1) ≤ (2^{3b} - 1) · (2^{b·n} - 1)` where `n = hs.length`. -/
theorem evalChunks_mul_bound {hs : List ℕ} {b : ℕ}
    (h : ∀ x ∈ hs, x < 2 ^ (3 * b)) :
    HvdH.evalChunks hs b * (2 ^ b - 1)
      ≤ (2 ^ (3 * b) - 1) * (2 ^ (b * hs.length) - 1) := by
  induction hs with
  | nil => simp [HvdH.evalChunks]
  | cons a t ih =>
    have ha : a ≤ 2 ^ (3 * b) - 1 := by
      have := h a (by simp); omega
    have ht : ∀ x ∈ t, x < 2 ^ (3 * b) := fun x hx => h x (by simp [hx])
    have ih' := ih ht
    rw [Work.IntLib.evalChunks_cons]
    simp only [List.length_cons]
    have h1 : a * (2 ^ b - 1) ≤ (2 ^ (3 * b) - 1) * (2 ^ b - 1) :=
      Nat.mul_le_mul_right _ ha
    have h3 : 2 ^ b * (HvdH.evalChunks t b * (2 ^ b - 1))
        ≤ 2 ^ b * ((2 ^ (3 * b) - 1) * (2 ^ (b * t.length) - 1)) :=
      Nat.mul_le_mul_left _ ih'
    calc (a + 2 ^ b * HvdH.evalChunks t b) * (2 ^ b - 1)
        = a * (2 ^ b - 1) + 2 ^ b * (HvdH.evalChunks t b * (2 ^ b - 1)) := by ring
      _ ≤ (2 ^ (3 * b) - 1) * (2 ^ b - 1)
            + 2 ^ b * ((2 ^ (3 * b) - 1) * (2 ^ (b * t.length) - 1)) :=
            Nat.add_le_add h1 h3
      _ = (2 ^ (3 * b) - 1) * ((2 ^ b - 1) + 2 ^ b * (2 ^ (b * t.length) - 1)) := by ring
      _ = (2 ^ (3 * b) - 1) * (2 ^ (b * (t.length + 1)) - 1) := by
            rw [pow_geom_step]

/-- Strict size bound for `evalChunks`: `evalChunks hs b < 2^{b·(n+2)+1}`. -/
theorem evalChunks_lt {hs : List ℕ} {b : ℕ} (hb : 1 ≤ b)
    (h : ∀ x ∈ hs, x < 2 ^ (3 * b)) :
    HvdH.evalChunks hs b < 2 ^ (b * (hs.length + 2) + 1) := by
  have hE := evalChunks_mul_bound h
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have hpow : 2 ^ c ≤ 2 ^ (c + 1) - 1 := by
    have h2 : 2 ^ (c + 1) = 2 ^ c + 2 ^ c := by rw [pow_succ]; ring
    rw [h2]
    have h1 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
    omega
  have hle : HvdH.evalChunks hs (c + 1) * 2 ^ c
      ≤ (2 ^ (3 * (c + 1)) - 1) * (2 ^ ((c + 1) * hs.length) - 1) :=
    le_trans (Nat.mul_le_mul_left _ hpow) hE
  have hlt : (2 ^ (3 * (c + 1)) - 1) * (2 ^ ((c + 1) * hs.length) - 1)
      < 2 ^ (3 * (c + 1)) * 2 ^ ((c + 1) * hs.length) :=
    Nat.mul_lt_mul_of_lt_of_le
      (Nat.sub_lt (pow_pos (by norm_num) _) (by norm_num))
      (Nat.sub_le _ _) (pow_pos (by norm_num) _)
  have hlt2 : HvdH.evalChunks hs (c + 1) * 2 ^ c
      < 2 ^ (3 * (c + 1)) * 2 ^ ((c + 1) * hs.length) := lt_of_le_of_lt hle hlt
  rw [← Nat.pow_add] at hlt2
  have hgoal : 2 ^ (3 * (c + 1) + (c + 1) * hs.length)
      = 2 ^ c * 2 ^ ((c + 1) * (hs.length + 2) + 1) := by
    rw [← Nat.pow_add]; congr 1; ring
  rw [hgoal] at hlt2
  rw [Nat.mul_comm (HvdH.evalChunks hs (c + 1)) (2 ^ c)] at hlt2
  exact Nat.lt_of_mul_lt_mul_left hlt2

theorem packChunkSize {hs : List ℕ} {b : ℕ} (hb : 1 ≤ b) (h : ∀ x ∈ hs, x < 2 ^ (3 * b)) :
    HvdH.isz ((HvdH.evalChunks hs b : ℕ) : ℤ) ≤ 4 * (hs.length * (b + 1)) + 8 := by
  rcases hs with _ | ⟨a, t⟩
  · simp [HvdH.evalChunks, HvdH.isz]
  · have hlt := evalChunks_lt hb h
    have hsize : (HvdH.evalChunks (a :: t) b).size ≤ b * ((a :: t).length + 2) + 1 :=
      Nat.size_le.2 hlt
    have hisz : HvdH.isz ((HvdH.evalChunks (a :: t) b : ℕ) : ℤ)
        = (HvdH.evalChunks (a :: t) b).size + 2 := by simp [HvdH.isz]
    rw [hisz]
    have hn : 1 ≤ (a :: t).length := by simp
    have hkey : b * ((a :: t).length + 2) + 3 ≤ 4 * ((a :: t).length * (b + 1)) + 8 := by
      nlinarith [hn, hb]
    omega

end Work.KronP
