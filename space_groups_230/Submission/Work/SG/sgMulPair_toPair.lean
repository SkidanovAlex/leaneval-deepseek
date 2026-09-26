import Mathlib
import Submission.Work.SG.SGprelude
import Submission.Work.SG.m9vecZ_toPair

/-!
# `sgMulPair_toPair`: the `ℚ`-side product is the `toPair`-image of the `ℤ`-side one

`toPair d` interprets an integer affine pair `(A, u)` (denominator `d`) as the pair of the
`Defs` shape `(A, u/d)`, and `zMul d` is the integer mirror of the rational multiplication
`sgMulPair` with `· % d` in place of `Int.fract` (`SGprelude`).

The point of this file is that the two multiplications commute with `toPair`:

`sgMulPair (toPair d p) (toPair d q) = toPair d (zMul d p q)`.

The matrix components agree definitionally.  For the translations one reduces (elementwise,
through `List.zipWith`) to the arithmetic identity

`Int.fract (n/d + m/d) = ((n + m) % d)/d`   (`n, m : ℤ`, `d : ℕ`),

which is `fract_divQ_add` below.  Note that it holds for `d = 0` as well, so no side
condition on the denominator is needed (the statement of `sgMulPair_toPair` has none).
-/

namespace Work.SG

/-- `(n + m)/d = n/d + m/d` at the level of numerators; valid for every `d` (in particular
`d = 0`, where both sides vanish). -/
private lemma divQ_add (d : ℕ) (x y : ℤ) : divQ d x + divQ d y = divQ d (x + y) := by
  simp only [divQ]
  rw [← add_div, Int.cast_add]

/-- Reduction of the fractional part of a single rational numerator:
`fract (n/d) = (n % d)/d`.  For `d = 0` both sides vanish; for `d > 0` the right-hand side
lies in `[0, 1)` and differs from `n/d` by the integer `n / d` (`Int.fract_eq_iff`). -/
private lemma fract_divQ (d : ℕ) (n : ℤ) :
    Int.fract (divQ d n) = divQ d (n % (d : ℤ)) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp [divQ]
  · simp only [divQ]
    have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hd)
    have hdQpos : (0 : ℚ) < d := by exact_mod_cast hd
    rw [Int.fract_eq_iff]
    refine ⟨?_, ?_, ⟨n / (d : ℤ), ?_⟩⟩
    · exact div_nonneg (by exact_mod_cast Int.emod_nonneg n hd0) (by positivity)
    · rw [div_lt_one hdQpos]
      exact_mod_cast Int.emod_lt_of_pos n (by exact_mod_cast hd)
    · rw [← sub_div, ← Int.cast_sub]
      rw [show n - n % (d : ℤ) = (d : ℤ) * (n / (d : ℤ)) from by
        have := Int.mul_ediv_add_emod n (d : ℤ); linarith]
      rw [Int.cast_mul]
      push_cast
      exact mul_div_cancel_left₀ _ (by positivity : (d : ℚ) ≠ 0)

/-- The additive form of `fract_divQ`: the reduction of `n/d + m/d` is `(n + m) % d` over
`d`.  This is the elementwise arithmetic content of `sgMulPair_toPair`. -/
private lemma fract_divQ_add (d : ℕ) (x y : ℤ) :
    Int.fract (divQ d x + divQ d y) = divQ d ((x + y) % (d : ℤ)) := by
  rw [divQ_add, fract_divQ]

/-- `List.zipWith` respects pointwise equal functions.  (`List.zipWith_congr` is not directly
applicable here, as the two lists need not have the same length.) -/
private lemma zipWith_congr_pts {α β γ : Type*} {f g : α → β → γ}
    (h : ∀ a b, f a b = g a b) :
    ∀ (l₁ : List α) (l₂ : List β), List.zipWith f l₁ l₂ = List.zipWith g l₁ l₂
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: l₁, b :: l₂ => by
      simp only [List.zipWith_cons_cons, h a b, zipWith_congr_pts h l₁ l₂]

/-- The translation components of the two products agree: `fract` on the `ℚ`-side corresponds
to `· % d` on the `ℤ`-side, entry by entry along the `List.zipWith`. -/
private lemma zipWith_fract_divQ (d : ℕ) (u l : List ℤ) :
    (List.zipWith (· + ·) (u.map (divQ d)) (l.map (divQ d))).map Int.fract
      = (emodList d (List.zipWith (· + ·) u l)).map (divQ d) := by
  have h1 : (List.zipWith (· + ·) (u.map (divQ d)) (l.map (divQ d))).map Int.fract
      = List.zipWith (fun x y => Int.fract (divQ d x + divQ d y)) u l := by
    rw [List.zipWith_map, List.map_zipWith]
  have h2 : (emodList d (List.zipWith (· + ·) u l)).map (divQ d)
      = List.zipWith (fun x y => divQ d ((x + y) % (d : ℤ))) u l := by
    rw [emodList, List.map_map, List.map_zipWith]
    rfl
  rw [h1, h2]
  exact zipWith_congr_pts (fun x y => fract_divQ_add d x y) u l

/-- Scaling the integer matrix–vector product by `1/d` commutes with interpreting the vector
over `ℚ`.  (The statement of `m9vecZ_toPair` uses an unannotated binder, hence the explicit
λ here; `divQ` is definitionally that λ.) -/
private lemma m9vec_scale (d : ℕ) (a v : List ℤ) :
    m9vec a (v.map (fun n : ℤ => (n : ℚ) / (d : ℚ))) =
      (m9vecZ a v).map (fun n : ℤ => (n : ℚ) / (d : ℚ)) := by
  have hget : ∀ k, (v.map (fun n : ℤ => (n : ℚ) / (d : ℚ))).getD k 0 =
      ((v.getD k 0 : ℤ) : ℚ) / (d : ℚ) := by
    intro k
    have h0 : (fun n : ℤ => (n : ℚ) / (d : ℚ)) (0 : ℤ) = (0 : ℚ) := by norm_num
    rw [← h0, List.getD_map]
  have h3 : (List.range 3) = [0, 1, 2] := rfl
  simp only [m9vec, m9vecZ, h3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hget,
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> (push_cast; ring)

/-- The rational affine product is the `toPair`-image of the integer one. -/
theorem sgMulPair_toPair (d : ℕ) (p q : List ℤ × List ℤ) :
    sgMulPair (toPair d p) (toPair d q) = toPair d (zMul d p q) := by
  obtain ⟨A, u⟩ := p
  obtain ⟨B, v⟩ := q
  have hmv : m9vec A (v.map (divQ d)) = (m9vecZ A v).map (divQ d) := m9vec_scale d A v
  show (m9mul A B,
      (List.zipWith (· + ·) (u.map (divQ d)) (m9vec A (v.map (divQ d)))).map Int.fract)
    = (m9mul A B, (emodList d (List.zipWith (· + ·) u (m9vecZ A v))).map (divQ d))
  rw [hmv]
  exact Prod.ext rfl (zipWith_fract_divQ d u (m9vecZ A v))

end Work.SG
