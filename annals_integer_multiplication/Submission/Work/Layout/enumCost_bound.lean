import Mathlib
import Submission.Work.Layout.enumDefs

/-!
# Cost bound for the enumerate loop

`Work.Layout.enumCost c i xs` is the cost budget of the `enumerate` walk over the value list `xs`
with a binary counter starting at `i`: one element step per element plus the final step that
discovers the trailing `nil` (cost `10`), see `enumCost_nil` / `enumCost_cons` in `enumDefs`.

The main content is the *general* induction `enumCost_le_general`: for a counter starting at `i`,
the cost is at most `c * (vsz (ofList xs) + S(i, N) + 4 * N) + N + 10`, where `N = xs.length` and
`S(i, N) = Σ_{j < N} isz (i + j)` is the total counter size (`enumIszSum`).  Specialising to `i = 0`
and using `S(0, N) ≤ N * (N.size + 2)` (`enumIszSum_le`) gives `enumCost_bound`.
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-! ## The counter-size sum -/

/-- Total size of the counters `i, i+1, …, i+N-1`: `Σ_{j<N} isz (i+j)`. -/
def enumIszSum (i N : ℕ) : ℕ := ((List.range N).map fun j => isz ((i + j : ℕ) : ℤ)).sum

/-- Recursion of `enumIszSum` at the *front* of the list of counters (the direction in which the
walk consumes elements). -/
theorem enumIszSum_succ (i N : ℕ) :
    enumIszSum i (N + 1) = isz ((i : ℕ) : ℤ) + enumIszSum (i + 1) N := by
  unfold enumIszSum
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons]
  have h : (List.map (fun j => isz ((i + j : ℕ) : ℤ)) (List.map Nat.succ (List.range N))).sum
      = (List.map (fun j => isz ((i + 1 + j : ℕ) : ℤ)) (List.range N)).sum := by
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro j _
    exact congrArg (fun m : ℕ => isz ((m : ℤ))) (by omega)
  rw [h]
  rfl

/-- Each counter `i + j` (`j < N`) is at most `i + N` in bit size, so
`enumIszSum i N ≤ N * ((i + N).size + 2)`. -/
theorem enumIszSum_le (i N : ℕ) : enumIszSum i N ≤ N * ((i + N).size + 2) := by
  induction N generalizing i with
  | zero => simp [enumIszSum]
  | succ N ih =>
    rw [enumIszSum_succ]
    have h := ih (i + 1)
    have hsz : ((i + 1) + N).size = (i + (N + 1)).size := by congr 1; omega
    rw [hsz] at h
    set B := (i + (N + 1)).size + 2 with hBdef
    have hB : isz ((i : ℕ) : ℤ) ≤ B := by
      rw [hBdef]
      simp only [isz]
      exact Nat.add_le_add_right (Nat.size_le_size (by omega)) 2
    have h2 : enumIszSum (i + 1) N ≤ N * B := by rwa [hBdef] at h
    have key : (N + 1) * B = B + N * B := by ring
    rw [key]
    omega

/-! ## Size of a `cons`-value -/

/-- `vsz` of `ofList (x :: t)`: one `cons` glyph plus the two encodings. -/
theorem vsz_ofList_cons_enum (x : Val) (t : List Val) :
    vsz (ofList (x :: t)) = vsz x + vsz (ofList t) + 1 := by
  have h : ofList (x :: t) = Val.cons x (ofList t) := rfl
  rw [h, vsz, vsz, vsz, Val.enc]
  simp only [List.length_cons, List.length_append]

/-! ## The general cost bound -/

/-- Cost bound of the enumerate loop with an arbitrary starting counter `i`.  The counter-size
part is kept exact (`enumIszSum`), so that the induction step only costs the slack `c` coming from
`vsz (ofList (x :: t)) = vsz x + vsz (ofList t) + 1`. -/
theorem enumCost_le_general (c i : ℕ) (xs : List Val) :
    enumCost c i xs ≤ c * (vsz (ofList xs) + enumIszSum i xs.length + 4 * xs.length)
      + xs.length + 10 := by
  induction xs generalizing i with
  | nil => simp [enumCost, enumIszSum, ofList, vsz, Val.enc]
  | cons x t ih =>
    rw [enumCost_cons, vsz_ofList_cons_enum, List.length_cons]
    have hIH : enumCost c (i + 1) t ≤
        c * (vsz (ofList t) + enumIszSum (i + 1) t.length + 4 * t.length) + t.length + 10 :=
      ih (i + 1)
    have hsum := enumIszSum_succ i t.length
    have key : c * (vsz x + vsz (ofList t) + 1 + (isz ((i : ℕ) : ℤ) + enumIszSum (i + 1) t.length)
          + 4 * (t.length + 1)) + (t.length + 1) + 10
        = (c * (vsz x + isz ((i : ℕ) : ℤ) + 4) + 1
            + (c * (vsz (ofList t) + enumIszSum (i + 1) t.length + 4 * t.length)
              + t.length + 10)) + c := by
      ring
    rw [hsum, key]
    simp only [iterCost]
    omega

/-! ## The arithmetic of the final bound -/

/-- The pure `Nat.size` inequality behind the bound: `N * (N.size + 2) + 4 * N ≤ 4 * N * (N.size + 1)`. -/
theorem size_mul_key (N : ℕ) : N * (N.size + 2) + 4 * N ≤ 4 * N * (N.size + 1) := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have hsz : 1 ≤ N.size := Nat.size_pos.mpr h
    have hle : N.size + 6 ≤ 4 * (N.size + 1) := by omega
    calc N * (N.size + 2) + 4 * N = N * (N.size + 6) := by ring
      _ ≤ N * (4 * (N.size + 1)) := Nat.mul_le_mul_left N hle
      _ = 4 * N * (N.size + 1) := by ring

/-- The final cost arithmetic: if the counter sizes total at most `N * (N.size + 2)`, the loop cost
`c * (V + S + 4 * N) + N + 11` fits in `4 * (c + 1) * (V + N * (N.size + 1) + 10)`. -/
theorem enumCost_arith (c N V S : ℕ) (h : S ≤ N * (N.size + 2)) :
    c * (V + S + 4 * N) + N + 10 + 1 ≤ 4 * (c + 1) * (V + N * (N.size + 1) + 10) := by
  have hk := size_mul_key N
  have h1 : c * S ≤ c * (N * (N.size + 2)) := Nat.mul_le_mul_left c h
  have h2 : c * (N * (N.size + 2)) + 4 * (c * N) ≤ c * (4 * N * (N.size + 1)) := by
    have := Nat.mul_le_mul_left c hk
    nlinarith [this]
  have h3 : c * (4 * N * (N.size + 1)) ≤ 4 * (c + 1) * (N * (N.size + 1)) := by
    nlinarith [Nat.le_succ c]
  have hSN : c * S + 4 * (c * N) ≤ 4 * (c + 1) * (N * (N.size + 1)) := by omega
  have hN : N ≤ 4 * N * (N.size + 1) := by
    calc N = N * 1 := (Nat.mul_one N).symm
      _ ≤ N * (4 * (N.size + 1)) := Nat.mul_le_mul_left N (by omega)
      _ = 4 * N * (N.size + 1) := by ring
  have h4 : N + 10 + 1 ≤ 4 * N * (N.size + 1) + 40 * (c + 1) := by omega
  have h5 : 4 * N * (N.size + 1) ≤ 4 * (c + 1) * (N * (N.size + 1)) := by
    nlinarith [Nat.le_succ c]
  have h6 : c * V ≤ 4 * (c + 1) * V := by nlinarith [Nat.le_succ c]
  nlinarith [hSN, h4, h5, h6]

/-! ## The requested bound -/

/-- Cost budget of the enumerate loop: `enumCost c i xs` is defined recursively by
`enumCost c i [] = 10` and `enumCost c i (x :: xs) = c * (vsz x + isz i + 4) + 1 + enumCost c (i+1) xs`.
(The loop runs one iteration per element plus one final iteration discovering the trailing `nil`.)
For the counter starting at `0` the whole loop fits in `4*(c+1)*(vsz (ofList xs) + N*(N.size+1) + 10)`,
`N = xs.length`; the `+1` on the left is the final failing loop test. -/
theorem enumCost_bound (c : ℕ) (xs : List HvdH.Val) :
    Work.Layout.enumCost c 0 xs + 1 ≤
      4 * (c + 1) * (HvdH.vsz (HvdH.ofList xs) + xs.length * (xs.length.size + 1) + 10) := by
  have hgen := enumCost_le_general c 0 xs
  have hsum : enumIszSum 0 xs.length ≤ xs.length * (xs.length.size + 2) := by
    simpa using enumIszSum_le 0 xs.length
  have harith := enumCost_arith c xs.length (vsz (ofList xs)) (enumIszSum 0 xs.length) hsum
  omega

end Work.Layout
