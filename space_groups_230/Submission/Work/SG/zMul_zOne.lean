import Mathlib
import Submission.Work.SG.SGprelude
import Submission.Work.SG.imatOfList_inj

namespace Work.SG

/-! ## Elementary facts about the integer mirror of the affine product

`zMul d p q` is the integer (denominator-`d`) mirror of `sgMulPair`: the matrix part is the
usual product of flat matrices, the translation part is `u + A v` reduced modulo `d`.
The three lemmas below isolate the two components of the right unit law. -/

/-- A flat matrix times the zero vector is the zero vector. -/
theorem m9vecZ_zero (a : List ℤ) : m9vecZ a [0, 0, 0] = [0, 0, 0] := by
  simp [m9vecZ, List.range_succ, List.range_zero, List.sum_cons]

/-- The flat identity is a right unit for flat matrix multiplication (as soon as the left
factor has nine entries, which is the only case in which `m9mul` is meaningful). -/
theorem m9mul_zOne_fst {a : List ℤ} (ha : a.length = 9) : m9mul a zOne.1 = a := by
  change m9mul a [1, 0, 0, 0, 1, 0, 0, 0, 1] = a
  refine imatOfList_inj (length_m9mul a _) ha ?_
  rw [imatOfList_mul, imatOfList_one, mul_one]

/-- Reduction modulo `d` fixes a list all of whose entries already lie in `[0, d)`. -/
theorem emodList_eq_self {d : ℕ} {u : List ℤ} (hr : ∀ x ∈ u, 0 ≤ x ∧ x < (d : ℤ)) :
    emodList d u = u := by
  show u.map (fun x => x % (d : ℤ)) = u
  rw [show u.map (fun x => x % (d : ℤ)) = u.map id from
      List.map_congr_left (fun x hx => Int.emod_eq_of_lt (hr x hx).1 (hr x hx).2),
    List.map_id]

/-- Multiplying a reduced pair on the right by the identity does nothing. -/
theorem zMul_zOne {d : ℕ} {p : List ℤ × List ℤ} (h9 : p.1.length = 9) (h3 : p.2.length = 3)
    (hr : ∀ x ∈ p.2, 0 ≤ x ∧ x < (d : ℤ)) : zMul d p zOne = p := by
  obtain ⟨A, u⟩ := p
  simp only at h9 h3 hr
  -- matrix part
  have hmat : m9mul A zOne.1 = A := m9mul_zOne_fst h9
  -- translation part
  have htr : emodList d (List.zipWith (· + ·) u (m9vecZ A zOne.2)) = u := by
    have hvec : m9vecZ A zOne.2 = [0, 0, 0] := m9vecZ_zero A
    rw [hvec]
    have hzip : List.zipWith (· + ·) u [0, 0, 0] = u := by
      obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp h3
      simp
    rw [hzip, emodList_eq_self hr]
  have hz : zMul d (A, u) zOne =
      (m9mul A zOne.1, emodList d (List.zipWith (· + ·) u (m9vecZ A zOne.2))) := rfl
  rw [hz, hmat, htr]

end Work.SG
