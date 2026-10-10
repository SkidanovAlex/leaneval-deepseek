import Mathlib.Algebra.MonoidAlgebra.Support
import Submission.Work.SSGRoute.prop5.witt.Vocab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# The leading term of the bracketed monomial of a Hall tree

For a Hall tree `c` over a linearly ordered alphabet, the expansion of the iterated commutator
`monBrk c` in `ℤ[FreeMonoid X]` has, with respect to the lexicographic order on words, the
*foliage* of `c` as its lowest word, occurring with coefficient `1`; all smaller words have
coefficient `0`.

The proof is an induction on `c`.  Two ingredients are needed.

* `coeffF_mul_lead_eq` : the coefficient of `u ++ v` in a product `A * B` is the product of the
  coefficient of `u` in `A` and the coefficient of `v` in `B`, as soon as every word occurring
  in `A` (resp. `B`) is `≥ u` (resp. `≥ v`) with the same length as `u` (resp. `v`).  Indeed the
  only pair of words `(x, y)` with `x ++ y = u ++ v` allowed by these bounds is `(u, v)`.
* `SuppAbove.mul` : under the same hypotheses every word occurring in `A * B` is `≥ u ++ v`
  (and has length `|u| + |v|`).

For a Hall product `mul a b`, Viennot's Hall condition (here taken as the hypothesis `hswap`)
gives `foliage a ++ foliage b < foliage b ++ foliage a`, so that in the difference
`monBrk a * monBrk b - monBrk b * monBrk a` the leading terms do not cancel and the leading term
of the difference is `foliage a ++ foliage b` with coefficient `1`.
-/

namespace Work.SSGRoute.prop5.witt

open Work.SSGRoute.prop5

open scoped Pointwise

section

variable {X : Type*} [LinearOrder X]

/-! ## Elementary list combinatorics -/

/-- Lexicographic comparison of concatenations when the first factors have the same length:
`x < u` implies `x ++ y < u ++ v`, for any `y`, `v`. -/
theorem lex_append_append_of_length_eq :
    ∀ (x u y v : List X), x.length = u.length → x < u → x ++ y < u ++ v := by
  intro x
  induction x with
  | nil =>
      intro u y v hlen h
      obtain rfl : u = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      cases h
  | cons a l ih =>
      intro u y v hlen h
      cases u with
      | nil => exact absurd h (by simp)
      | cons b m =>
          cases h with
          | rel hab => exact List.Lex.rel hab
          | cons hlm =>
              simp only [List.length_cons] at hlen
              exact List.Lex.cons (ih m y v (by omega) hlm)

/-- If `u ≤ x` and `v ≤ y`, and `x` has the same length as `u`, then `u ++ v ≤ x ++ y`. -/
theorem le_append_append_of_length_eq {x u y v : List X} (hux : u ≤ x)
    (hlx : x.length = u.length) (hvy : v ≤ y) : u ++ v ≤ x ++ y := by
  rcases eq_or_lt_of_le hux with h | h
  · rw [h]
    rcases eq_or_lt_of_le hvy with h2 | h2
    · rw [← h2]
    · exact le_of_lt (List.Lex.append_left (· < ·) h2 x)
  · exact le_of_lt (lex_append_append_of_length_eq u x v y hlx.symm h)

/-- If `v < y` and `u ≤ x`, and `x` has the same length as `u`, then `u ++ v < x ++ y`. -/
theorem lt_append_append_of_lt_right {x u y v : List X} (hvy : v < y) (hux : u ≤ x)
    (hlx : x.length = u.length) : u ++ v < x ++ y := by
  rcases eq_or_lt_of_le hux with h | h
  · rw [h]
    exact List.Lex.append_left (· < ·) hvy x
  · exact lex_append_append_of_length_eq u x v y hlx.symm h

/-! ## Coefficients of products -/

/-- The coefficient of a single monomial: `coeffF (single (ofList v) r) w` is `r` if `w = v` and
`0` otherwise. -/
theorem coeffF_single_ofList (v : List X) (r : ℤ) (w : List X) :
    coeffF (MonoidAlgebra.single (FreeMonoid.ofList v) r) w = if v = w then r else 0 := by
  by_cases h : v = w
  · rw [h, coeffF, MonoidAlgebra.coeff_single, Finsupp.single_eq_same, if_pos rfl]
  · have h' : FreeMonoid.ofList w ≠ FreeMonoid.ofList v := fun hh =>
      h (FreeMonoid.ofList.injective hh).symm
    rw [coeffF, MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne h', if_neg h]

/-- **The support of a product.**  If a word occurs with nonzero coefficient in `A * B`, then it
is the concatenation of a word occurring in `A` and a word occurring in `B`. -/
theorem exists_of_coeffF_mul_ne_zero {A B : MonoidAlgebra ℤ (FreeMonoid X)} {w : List X}
    (h : coeffF (A * B) w ≠ 0) :
    ∃ x y : List X, coeffF A x ≠ 0 ∧ coeffF B y ≠ 0 ∧ w = x ++ y := by
  haveI : DecidableEq (FreeMonoid X) := inferInstanceAs (DecidableEq (List X))
  have hmem : FreeMonoid.ofList w ∈ (A * B).coeff.support := Finsupp.mem_support_iff.mpr h
  have hsub : FreeMonoid.ofList w ∈ A.coeff.support * B.coeff.support :=
    MonoidAlgebra.support_coeff_mul_subset (k := ℤ) A B hmem
  rw [Finset.mem_mul] at hsub
  obtain ⟨m, hm, n, hn, hmn⟩ := hsub
  rw [Finsupp.mem_support_iff] at hm hn
  refine ⟨FreeMonoid.toList m, FreeMonoid.toList n, ?_, ?_, ?_⟩
  · rw [coeffF, FreeMonoid.ofList_toList]; exact hm
  · rw [coeffF, FreeMonoid.ofList_toList]; exact hn
  · have h1 : FreeMonoid.ofList w
        = FreeMonoid.ofList (FreeMonoid.toList m ++ FreeMonoid.toList n) := by
      rw [FreeMonoid.ofList_append]
      simp only [FreeMonoid.ofList_toList]
      exact hmn.symm
    have h2 := congrArg FreeMonoid.toList h1
    simpa using h2

/-- The coefficient of `u ++ v` in `A * single (ofList v) b` is the coefficient of `u` in `A`
times `b`. -/
theorem coeffF_mul_single (A : MonoidAlgebra ℤ (FreeMonoid X)) (u v : List X) (b : ℤ) :
    coeffF (A * MonoidAlgebra.single (FreeMonoid.ofList v) b) (u ++ v) = coeffF A u * b := by
  rw [coeffF, coeffF]
  refine MonoidAlgebra.coeff_mul_single_eq_coeff_mul (m := FreeMonoid.ofList v)
    (m₁ := FreeMonoid.ofList (u ++ v)) (m₂ := FreeMonoid.ofList u) ?_
  intro m _
  constructor
  · intro h
    have h1 : FreeMonoid.ofList (FreeMonoid.toList m ++ v)
        = FreeMonoid.ofList (u ++ v) := by
      rw [FreeMonoid.ofList_append, FreeMonoid.ofList_toList m]
      exact h
    have h2 := congrArg FreeMonoid.toList h1
    simp only [FreeMonoid.toList_ofList] at h2
    have h3 : FreeMonoid.toList m = u := List.append_cancel_right h2
    exact (FreeMonoid.ofList_toList m).symm.trans (congrArg FreeMonoid.ofList h3)
  · intro h
    rw [h, ← FreeMonoid.ofList_append]

/-! ## Support bounds -/

/-- Every word occurring in `A` is lexicographically `≥ u`, and has the same length as `u`. -/
def SuppAbove (u : List X) (A : MonoidAlgebra ℤ (FreeMonoid X)) : Prop :=
  ∀ w : List X, coeffF A w ≠ 0 → u ≤ w ∧ w.length = u.length

/-- Every word occurring in `A` is lexicographically `> u`, and has the same length as `u`. -/
def SuppAboveStrict (u : List X) (A : MonoidAlgebra ℤ (FreeMonoid X)) : Prop :=
  ∀ w : List X, coeffF A w ≠ 0 → u < w ∧ w.length = u.length

/-- An element whose support is strictly above `u` has zero coefficient at `u`. -/
theorem SuppAboveStrict.coeff_self {u : List X} {A : MonoidAlgebra ℤ (FreeMonoid X)}
    (h : SuppAboveStrict u A) : coeffF A u = 0 := by
  by_contra hc
  exact absurd (h u hc).1 (lt_irrefl u)

/-- The support bound is preserved by products: words occurring in `A * B` are `≥ u ++ v`. -/
theorem SuppAbove.mul {u v : List X} {A B : MonoidAlgebra ℤ (FreeMonoid X)}
    (hA : SuppAbove u A) (hB : SuppAbove v B) : SuppAbove (u ++ v) (A * B) := by
  intro w hw
  obtain ⟨x, y, hx, hy, rfl⟩ := exists_of_coeffF_mul_ne_zero hw
  obtain ⟨hux, hlx⟩ := hA x hx
  obtain ⟨hvy, hly⟩ := hB y hy
  exact ⟨le_append_append_of_length_eq hux hlx hvy,
    by simp [List.length_append, hlx, hly]⟩

/-- If in addition the support of `B` is *strictly* above `v`, then the same is true of `A * B`
(with `u ++ v` in place of `v`). -/
theorem SuppAbove.mul_strict_right {u v : List X} {A B : MonoidAlgebra ℤ (FreeMonoid X)}
    (hA : SuppAbove u A) (hB : SuppAboveStrict v B) :
    SuppAboveStrict (u ++ v) (A * B) := by
  intro w hw
  obtain ⟨x, y, hx, hy, rfl⟩ := exists_of_coeffF_mul_ne_zero hw
  obtain ⟨hux, hlx⟩ := hA x hx
  obtain ⟨hvy, hly⟩ := hB y hy
  exact ⟨lt_append_append_of_lt_right hvy hux hlx,
    by simp [List.length_append, hlx, hly]⟩

/-- Subtracting the leading monomial `single (ofList v) (coeffF B v)` from `B` makes the support
strictly larger than `v`. -/
theorem SuppAboveStrict.sub_single {v : List X} {B : MonoidAlgebra ℤ (FreeMonoid X)}
    (hB : SuppAbove v B) :
    SuppAboveStrict v (B - MonoidAlgebra.single (FreeMonoid.ofList v) (coeffF B v)) := by
  intro w hw
  have hsingle : coeffF (MonoidAlgebra.single (FreeMonoid.ofList v) (coeffF B v)) w
      = if v = w then coeffF B v else 0 := coeffF_single_ofList v (coeffF B v) w
  rw [coeffF_sub, hsingle] at hw
  have hBw : coeffF B w ≠ 0 := by
    by_cases hv : v = w
    · rw [hv, if_pos rfl] at hw
      exact fun h0 => hw (by rw [h0, sub_self])
    · rw [if_neg hv, sub_zero] at hw
      exact hw
  have hne : v ≠ w := by
    intro hvw
    rw [hvw, if_pos rfl] at hw
    exact hw (sub_self _)
  exact ⟨lt_of_le_of_ne (hB w hBw).1 hne, (hB w hBw).2⟩

/-! ## The leading term of a product -/

/-- **The leading coefficient of a product.**  If the words occurring in `A` are `≥ u` and those
occurring in `B` are `≥ v` (with matching lengths), then the coefficient of `u ++ v` in `A * B`
is the product of the coefficients of `u` in `A` and of `v` in `B`. -/
theorem coeffF_mul_lead_eq {u v : List X} {A B : MonoidAlgebra ℤ (FreeMonoid X)}
    (hA : SuppAbove u A) (hB : SuppAbove v B) :
    coeffF (A * B) (u ++ v) = coeffF A u * coeffF B v := by
  have hstrict : SuppAboveStrict v
      (B - MonoidAlgebra.single (FreeMonoid.ofList v) (coeffF B v)) :=
    SuppAboveStrict.sub_single hB
  have hmain : A * B = A * MonoidAlgebra.single (FreeMonoid.ofList v) (coeffF B v)
      + A * (B - MonoidAlgebra.single (FreeMonoid.ofList v) (coeffF B v)) := by
    rw [← mul_add, add_sub_cancel]
  rw [hmain, coeffF_add, coeffF_mul_single]
  rw [SuppAboveStrict.coeff_self (SuppAbove.mul_strict_right hA hstrict), add_zero]

/-- **The leading term of the commutator of two elements with leading terms `u` and `v`.**  If
`A` has leading term `u` with coefficient `1`, `B` has leading term `v` with coefficient `1`,
and `u ++ v < v ++ u`, then `A * B - B * A` has leading term `u ++ v` with coefficient `1`. -/
theorem coeffF_mul_sub_leading {u v : List X} {A B : MonoidAlgebra ℤ (FreeMonoid X)}
    (hA1 : coeffF A u = 1) (hA : SuppAbove u A) (hB1 : coeffF B v = 1) (hB : SuppAbove v B)
    (hswap : u ++ v < v ++ u) :
    coeffF (A * B - B * A) (u ++ v) = 1 ∧ SuppAbove (u ++ v) (A * B - B * A) := by
  have hAB : SuppAbove (u ++ v) (A * B) := SuppAbove.mul hA hB
  have hBA : SuppAbove (v ++ u) (B * A) := SuppAbove.mul hB hA
  have hBA0 : coeffF (B * A) (u ++ v) = 0 := by
    by_contra hc
    exact absurd (hBA (u ++ v) hc).1 (not_le.mpr hswap)
  constructor
  · rw [coeffF_sub, coeffF_mul_lead_eq hA hB, hBA0, hA1, hB1]
    ring
  · intro w hw
    rw [coeffF_sub] at hw
    rcases eq_or_ne (coeffF (A * B) w) 0 with h1 | h1
    · have h2 : coeffF (B * A) w ≠ 0 := by
        intro h2
        exact hw (by rw [h1, h2, sub_zero])
      obtain ⟨hle, hlen⟩ := hBA w h2
      exact ⟨le_trans (le_of_lt hswap) hle,
        by rw [hlen, List.length_append, List.length_append, Nat.add_comm]⟩
    · exact hAB w h1

end

/-! ## The leading term of the bracketed monomial of a Hall tree -/

lemma leading_term_coeff {X : Type*} [LinearOrder X] {c : Magma X} (hc : IsHall c)
    (hswap : ∀ a b : Magma X, IsHall (Magma.mul a b) →
      Magma.foliage a ++ Magma.foliage b < Magma.foliage b ++ Magma.foliage a) :
    coeffF (monBrk X c) (Magma.foliage c) = 1 ∧
      ∀ w : List X, w < Magma.foliage c → coeffF (monBrk X c) w = 0 := by
  have main : ∀ c : Magma X, IsHall c →
      coeffF (monBrk X c) (Magma.foliage c) = 1 ∧
        SuppAbove (Magma.foliage c) (monBrk X c) := by
    intro c
    induction c with
    | gen x =>
        intro _
        constructor
        · rw [monBrk_gen, coeffF, MonoidAlgebra.coeff_single]
          exact Finsupp.single_eq_same
        · intro w hw
          rw [monBrk_gen, coeffF, MonoidAlgebra.coeff_single] at hw
          have hw' : FreeMonoid.of x = FreeMonoid.ofList w := by
            by_contra hc
            exact hw (Finsupp.single_eq_of_ne (Ne.symm hc))
          have hxw : [x] = w := by
            simpa using congrArg FreeMonoid.toList hw'
          rw [Magma.foliage_gen, ← hxw]
          exact ⟨le_rfl, rfl⟩
    | mul a b iha ihb =>
        intro hc
        obtain ⟨hA1, hA⟩ := iha (IsHall.left hc)
        obtain ⟨hB1, hB⟩ := ihb (IsHall.right hc)
        have key := coeffF_mul_sub_leading (A := monBrk X a) (B := monBrk X b)
          hA1 hA hB1 hB (hswap a b hc)
        simpa only [Magma.foliage_mul, monBrk_mul] using key
  obtain ⟨h1, h2⟩ := main c hc
  refine ⟨h1, fun w hw => ?_⟩
  by_contra h0
  exact absurd (h2 w h0).1 (not_le.mpr hw)

end Work.SSGRoute.prop5.witt
