import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.lvlNLevelsLib

namespace Work.SynFFT

open HvdH

set_option autoImplicit false

/-- Reading a `take` at an index inside the taken range. -/
lemma blkLvlRead_getD_take {α : Type*} {l : List α} {n q : ℕ} {d : α} (h : q < n) :
    (l.take n).getD q d = l.getD q d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left h]

/-- Pure list/array maths: the butterfly outputs of a block of size `m` (with `m * 2^sh = 2r`),
`(u i + u (i+m/2))/2` for the first half and `y^{sgn*(i*2^sh)}(u i - u (i+m/2))/2` for the second
half (`i < m - m/2`), reassembled as `(lowsVecs.take (m/2)) ++ highsVecs`, approximate
`Work.SynFFT.lvlN r m sgn u` (the list-level `blkLvl` of one radix-two level pass) with error `e+1`. -/
theorem blkLvlRead (p r m sh : ℕ) (sgn : ℤ) (u : Work.SynFFT.Arr r) (e : ℝ)
    (lowsVecs highsVecs : List (List (ℤ × ℤ)))
    (h2 : 2 ≤ m) (hmul : m * 2 ^ sh = 2 * r) (hp : 2 * r < 2 ^ p)
    (hlow : lowsVecs.length = m - m / 2) (hhigh : highsVecs.length = m - m / 2)
    (hlowapp : ∀ i, i < m - m / 2 → ∀ c : Fin r,
      (2 : ℝ) ^ p * ‖HvdH.fxC p ((lowsVecs.getD i []).getD (c : ℕ) (0, 0)) -
        (u i c + u (i + m / 2) c) / 2‖ ≤ e + 1)
    (hhighapp : ∀ i, i < m - m / 2 → ∀ c : Fin r,
      (2 : ℝ) ^ p * ‖HvdH.fxC p ((highsVecs.getD i []).getD (c : ℕ) (0, 0)) -
        HvdH.yMul r (sgn * (((i * 2 ^ sh : ℕ)) : ℤ)) (fun c' => (u i c' - u (i + m / 2) c') / 2) c‖ ≤ e + 1) :
    Work.SynFFT.ApproxSL p r m (lowsVecs.take (m / 2) ++ highsVecs) (Work.SynFFT.lvlN r m sgn u) (e + 1) := by
  have hm0 : 0 < m := by omega
  -- `2r/m = 2^sh`, the bridge between the twiddle exponents of `lvlN` and of the word.
  have hdiv : 2 * r / m = 2 ^ sh := by
    rw [← hmul, Nat.mul_comm m (2 ^ sh), Nat.mul_div_left _ hm0]
  have hle : m / 2 ≤ m - m / 2 := by omega
  have hlt : (lowsVecs.take (m / 2)).length = m / 2 := by
    rw [List.length_take, hlow, Nat.min_eq_left hle]
  refine ⟨?_, ?_⟩
  · rw [List.length_append, hlt, hhigh]; omega
  · intro q hq c
    rcases lt_or_ge q (m / 2) with hqlt | hqge
    · -- first half: the sum output
      have hgd : (lowsVecs.take (m / 2) ++ highsVecs).getD q [] = lowsVecs.getD q [] := by
        rw [List.getD_append _ _ _ _ (by rw [hlt]; exact hqlt), blkLvlRead_getD_take hqlt]
      have hstep : lvlN r m sgn u q c = (u q c + u (q + m / 2) c) / 2 := by
        have hmod : q % m = q := Nat.mod_eq_of_lt (by omega)
        simp only [lvlN, hmod, ite_eq_left hqlt]
      rw [hgd, hstep]
      exact hlowapp q (by omega) c
    · -- second half: the difference output, with twiddle exponent `(q - m/2) * 2^sh`
      have hi : q - m / 2 < m - m / 2 := by omega
      have hgd : (lowsVecs.take (m / 2) ++ highsVecs).getD q [] = highsVecs.getD (q - m / 2) [] := by
        rw [List.getD_append_right _ _ _ _ (by rw [hlt]; exact hqge), hlt]
      have hstep : lvlN r m sgn u q c =
          yMul r (sgn * (((q - m / 2) * 2 ^ sh : ℕ)) : ℤ)
            (fun c' => (u (q - m / 2) c' - u q c') / 2) c := by
        have hmod : q % m = q := Nat.mod_eq_of_lt hq
        have hdm : (2 * r / m) * (q - m / 2) = (q - m / 2) * 2 ^ sh := by
          rw [hdiv, Nat.mul_comm]
        simp only [lvlN, hmod, hdm, ite_eq_right (not_lt.mpr hqge)]
      rw [hgd, hstep]
      have hh := hhighapp (q - m / 2) hi c
      rwa [Nat.sub_add_cancel hqge] at hh

end Work.SynFFT
