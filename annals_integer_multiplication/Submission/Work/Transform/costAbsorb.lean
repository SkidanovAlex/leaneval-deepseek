import Mathlib
import Submission.Work.Transform.SeqUtil

/-!
# Cost absorption for the Transform pipeline

The Transform pipeline (paper Theorem 3.1) is a sequential composition of twenty
`WordR` steps whose costs `n₁, …, n₂₀` are each bounded by `Kᵢ · (3000000 · A) + Kᵢ`
(where `A = T·p² + Σts·(p+1)^K` is the size of the data), except for the one deep
recursive call `n₁₈` which additionally pays `4·M·Cm(3rp)` for the multiplication.

Since every `Kᵢ ≤ Sg` and `2^(Sg+100) ≤ K`, the total cost of the whole sequence fits
into `4·M·Cm(3rp) + K·A`, i.e. the twenty small factors are absorbed by the single
large factor `K` (the paper's "`2^{something}` beats any polynomial in the parameters"
step).  This file proves that purely numerical absorption lemma.
-/

namespace Work.Transform

/-- Elementary numeric fact: `2^(Sg+100)` dominates `60000020*Sg+1`.
This is the quantitative form of "an exponential beats any linear function". -/
theorem costAbsorb_two_pow (Sg : ℕ) : 60000020 * Sg + 1 ≤ 2 ^ (Sg + 100) := by
  rcases Nat.eq_zero_or_pos Sg with h | h
  · subst h; norm_num
  · have h1 : Sg ≤ 2 ^ Sg := le_of_lt (Nat.lt_two_pow_self (n := Sg))
    have h2 : (60000021 : ℕ) ≤ 2 ^ 100 := by norm_num
    have h3 : 2 ^ (Sg + 100) = 2 ^ Sg * 2 ^ 100 := by rw [pow_add]
    rw [h3]
    nlinarith [h1, h2, h]

/-- Twenty blocks of size `Sg*(3000000*A)+Sg` (together with the final `+1` of `csum`)
fit into `K*A`, provided `1 ≤ A` and `K ≥ 60000020*Sg+1`. -/
theorem costAbsorb_twenty (A K Sg : ℕ) (hA : 1 ≤ A) (hkey : 60000020 * Sg + 1 ≤ K) :
    20 * (Sg * (3000000 * A) + Sg) + 1 ≤ K * A := by
  -- Multiply `hkey` by `A`.
  have h1 : (60000020 * Sg + 1) * A ≤ K * A := Nat.mul_le_mul_right A hkey
  -- And bound the left-hand side by `(60000020*Sg+1)*A` using `1 ≤ A`.
  have hstep : 20 * Sg + 1 ≤ (20 * Sg + 1) * A := by
    calc 20 * Sg + 1 = (20 * Sg + 1) * 1 := by ring
      _ ≤ (20 * Sg + 1) * A := Nat.mul_le_mul_left _ hA
  have h2 : 20 * (Sg * (3000000 * A) + Sg) + 1 ≤ (60000020 * Sg + 1) * A := by
    nlinarith [hstep]
  linarith

/-- **Cost absorption.**  The sum of twenty step costs, each bounded by
`Kᵢ·(3000000·A) + Kᵢ` with `Kᵢ ≤ Sg` (and the recursive cost `n₁₈` additionally
paying `4·M·Cm(3rp)`), is bounded by `4·M·Cm(3rp) + K·A` with `A` the data size,
as soon as `2^(Sg+100) ≤ K`. -/
theorem costAbsorb (p T r M K Sg : ℕ) (ts : List ℕ) (Cm : ℕ → ℕ)
    (Kp Kz Kc Ks Ka Km Kph Kps Kr KR : ℕ)
    (hKp : Kp ≤ Sg) (hKz : Kz ≤ Sg) (hKc : Kc ≤ Sg) (hKs : Ks ≤ Sg) (hKa : Ka ≤ Sg)
    (hKm : Km ≤ Sg) (hKph : Kph ≤ Sg) (hKps : Kps ≤ Sg) (hKr : Kr ≤ Sg) (hKR : KR ≤ Sg)
    (hK : 2 ^ (Sg + 100) ≤ K)
    (hA : 1 ≤ T * p ^ 2 + ts.sum * (p + 1) ^ K)
    (n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 : ℕ)
    (h1 : n1 ≤ Kp * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Kp)
    (h2 : n2 ≤ Kz * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Kz)
    (h3 : n3 ≤ Kr * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Kr)
    (h4 : n4 ≤ Kr * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Kr)
    (h5 : n5 ≤ Kc * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Kc)
    (h6 : n6 ≤ Ks * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Ks)
    (h7 : n7 ≤ Ka * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Ka)
    (h8 : n8 ≤ Km * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Km)
    (h9 : n9 ≤ Kph * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Kph)
    (h10 : n10 ≤ Kr * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Kr)
    (h11 : n11 ≤ Kr * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Kr)
    (h12 : n12 ≤ Kr * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Kr)
    (h13 : n13 ≤ Kr * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Kr)
    (h14 : n14 ≤ Kph * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Kph)
    (h15 : n15 ≤ Kr * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Kr)
    (h16 : n16 ≤ Kr * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Kr)
    (h17 : n17 ≤ Kr * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Kr)
    (h18 : n18 ≤ 4 * M * Cm (3 * r * p) + KR * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + KR)
    (h19 : n19 ≤ Kps * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Kps)
    (h20 : n20 ≤ Km * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Km) :
    Work.Transform.csum [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16,
        n17, n18, n19, n20] ≤
      4 * M * Cm (3 * r * p) + K * T * p ^ 2 + K * ts.sum * (p + 1) ^ K := by
  -- Rewrite the right-hand side as `4·M·Cm(3rp) + K·A` with `A = T·p² + Σts·(p+1)^K`.
  have hKA : 4 * M * Cm (3 * r * p) + K * T * p ^ 2 + K * ts.sum * (p + 1) ^ K
      = 4 * M * Cm (3 * r * p) + K * (T * p ^ 2 + ts.sum * (p + 1) ^ K) := by ring
  rw [hKA]
  have hkey : 60000020 * Sg + 1 ≤ K := le_trans (costAbsorb_two_pow Sg) hK
  have harith := costAbsorb_twenty (T * p ^ 2 + ts.sum * (p + 1) ^ K) K Sg hA hkey
  -- Bound each individual step cost by `Sg * (3000000 * A) + Sg` (monotonicity in `Kᵢ`).
  have b1 : n1 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h1 (Nat.add_le_add (Nat.mul_le_mul_right _ hKp) hKp)
  have b2 : n2 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h2 (Nat.add_le_add (Nat.mul_le_mul_right _ hKz) hKz)
  have b3 : n3 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h3 (Nat.add_le_add (Nat.mul_le_mul_right _ hKr) hKr)
  have b4 : n4 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h4 (Nat.add_le_add (Nat.mul_le_mul_right _ hKr) hKr)
  have b5 : n5 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h5 (Nat.add_le_add (Nat.mul_le_mul_right _ hKc) hKc)
  have b6 : n6 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h6 (Nat.add_le_add (Nat.mul_le_mul_right _ hKs) hKs)
  have b7 : n7 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h7 (Nat.add_le_add (Nat.mul_le_mul_right _ hKa) hKa)
  have b8 : n8 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h8 (Nat.add_le_add (Nat.mul_le_mul_right _ hKm) hKm)
  have b9 : n9 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h9 (Nat.add_le_add (Nat.mul_le_mul_right _ hKph) hKph)
  -- `n₁₈` also carries the recursive multiplication cost, which is kept as is.
  have b18 : n18 ≤ 4 * M * Cm (3 * r * p)
      + Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h18 (Nat.add_le_add (Nat.add_le_add (le_refl _) (Nat.mul_le_mul_right _ hKR)) hKR)
  have b10 : n10 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h10 (Nat.add_le_add (Nat.mul_le_mul_right _ hKr) hKr)
  have b11 : n11 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h11 (Nat.add_le_add (Nat.mul_le_mul_right _ hKr) hKr)
  have b12 : n12 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h12 (Nat.add_le_add (Nat.mul_le_mul_right _ hKr) hKr)
  have b13 : n13 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h13 (Nat.add_le_add (Nat.mul_le_mul_right _ hKr) hKr)
  have b14 : n14 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h14 (Nat.add_le_add (Nat.mul_le_mul_right _ hKph) hKph)
  have b15 : n15 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h15 (Nat.add_le_add (Nat.mul_le_mul_right _ hKr) hKr)
  have b16 : n16 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h16 (Nat.add_le_add (Nat.mul_le_mul_right _ hKr) hKr)
  have b17 : n17 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h17 (Nat.add_le_add (Nat.mul_le_mul_right _ hKr) hKr)
  have b19 : n19 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h19 (Nat.add_le_add (Nat.mul_le_mul_right _ hKps) hKps)
  have b20 : n20 ≤ Sg * (3000000 * (T * p ^ 2 + ts.sum * (p + 1) ^ K)) + Sg :=
    le_trans h20 (Nat.add_le_add (Nat.mul_le_mul_right _ hKm) hKm)
  -- Unfold `csum` and add up the twenty bounds.
  rw [csum_eq_sum_add_one]
  simp only [List.sum_cons, List.sum_nil, add_zero]
  linarith only [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17,
    b18, b19, b20, harith]

end Work.Transform
