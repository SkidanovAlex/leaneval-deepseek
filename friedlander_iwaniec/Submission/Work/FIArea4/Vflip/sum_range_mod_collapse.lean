import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4.Vflip

open Finset
open scoped BigOperators

/-!
# Collapsing a `mod q`-restricted range sum to a `mod d1`-restricted one

For `1 ≤ d1`, `1 ≤ q`, `d1 ∣ q` and `r` coprime to `q`, the sum over `a ∈ [0,q)` of the
indicator of `s ≡ r a (mod q)` weighted by `h (a % d1)` collapses to the corresponding sum over
`[0,d1)`:

`∑_{a<q} [s ≡ r a (mod q)] · h (a % d1) = ∑_{b<d1} [s ≡ r b (mod d1)] · h b`.

Both sides equal `h (x % d1)` where `x` is the (unique) solution in `[0,q)` of `r x ≡ s (mod q)`;
the reduction mod `d1` of `x` is the unique solution of `r y ≡ s (mod d1)` in `[0,d1)`.

The uniqueness of the solution comes from cancelling the unit `r` in `ZMod n`; it is provided here
by `sol`, the `Nat`-value of `r⁻¹ · s` in `ZMod n`. -/

/-- The unique residue class `x ∈ [0,n)` solving `r x = s` in `ZMod n`, realised as the
`Nat`-value of `r⁻¹ · s` (valid whenever `r` is a unit of `ZMod n`, i.e. `(r,n) = 1`). -/
private noncomputable def sol (r s n : ℕ) (hn : Nat.Coprime r n) : ℕ :=
  ((ZMod.unitOfCoprime r hn)⁻¹ * (s : ZMod n)).val

/-- `sol` is indeed a solution of the congruence `r x ≡ s (mod n)`. -/
private lemma sol_spec (r s n : ℕ) (hn : Nat.Coprime r n) (hn1 : 1 ≤ n) :
    (r * sol r s n hn) % n = s % n := by
  have : NeZero n := ⟨by omega⟩
  have hkey : (ZMod.unitOfCoprime r hn : ZMod n) *
      (((ZMod.unitOfCoprime r hn)⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := Units.mul_inv _
  have hcoat : (ZMod.unitOfCoprime r hn : ZMod n) = (r : ZMod n) := ZMod.coe_unitOfCoprime r hn
  have key : ((r * sol r s n hn : ℕ) : ZMod n) = (s : ZMod n) := by
    rw [Nat.cast_mul]
    unfold sol
    rw [ZMod.natCast_zmod_val]
    rw [← hcoat, ← mul_assoc, hkey, one_mul]
  rw [ZMod.natCast_eq_natCast_iff] at key
  exact key

/-- The solution of `r x ≡ s (mod n)` in `[0,n)` is unique when `(r,n) = 1`. -/
private lemma sol_unique (r s n : ℕ) (hn : Nat.Coprime r n) (hn1 : 1 ≤ n) {a : ℕ} (ha : a < n)
    (h : (r * a) % n = s % n) : a = sol r s n hn := by
  have : NeZero n := ⟨by omega⟩
  have hspec := sol_spec r s n hn hn1
  have hsoln_lt : sol r s n hn < n := ZMod.val_lt _
  have hmod : r * a ≡ r * sol r s n hn [MOD n] := by
    rw [Nat.ModEq]
    rw [h, hspec]
  have hcancel : a ≡ sol r s n hn [MOD n] :=
    Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hn) hmod
  exact Nat.ModEq.eq_of_lt_of_lt hcancel ha hsoln_lt

theorem sum_range_mod_collapse (q d1 r s : ℕ) (hd1 : 1 ≤ d1) (hq : 1 ≤ q) (hd1q : d1 ∣ q)
    (hrq : Nat.Coprime r q) (h : ℕ → ℝ) :
    ∑ a ∈ Finset.range q, (if s % q = (r * a) % q then (1 : ℝ) else 0) * h (a % d1)
      = ∑ a1 ∈ Finset.range d1, (if s % d1 = (r * a1) % d1 then (1 : ℝ) else 0) * h a1 := by
  have hq0 : NeZero q := ⟨by omega⟩
  have hd10 : NeZero d1 := ⟨by omega⟩
  have hrd1 : Nat.Coprime r d1 := hrq.of_dvd_right hd1q
  set A := sol r s q hrq with hA
  set B := sol r s d1 hrd1 with hB
  have hA_lt : A < q := by rw [hA]; exact ZMod.val_lt _
  have hB_lt : B < d1 := by rw [hB]; exact ZMod.val_lt _
  have hspecq : (r * A) % q = s % q := by rw [hA]; exact sol_spec r s q hrq hq
  have hspecd : (r * B) % d1 = s % d1 := by rw [hB]; exact sol_spec r s d1 hrd1 hd1
  -- LHS: only `a = A` survives
  have hL : (∑ a ∈ Finset.range q, (if s % q = (r * a) % q then (1 : ℝ) else 0) * h (a % d1))
      = h (A % d1) := by
    have hpoint : ∀ a ∈ Finset.range q,
        (if s % q = (r * a) % q then (1 : ℝ) else 0) * h (a % d1)
          = (if a = A then h (A % d1) else 0) := by
      intro a ha
      rw [Finset.mem_range] at ha
      by_cases hAa : a = A
      · subst hAa; rw [if_pos hspecq.symm, if_pos rfl, one_mul]
      · have hc : ¬ (s % q = (r * a) % q) :=
          fun hc => hAa ((sol_unique r s q hrq hq ha hc.symm).trans hA.symm)
        rw [if_neg hc, if_neg hAa, zero_mul]
    calc (∑ a ∈ Finset.range q, (if s % q = (r * a) % q then (1 : ℝ) else 0) * h (a % d1))
        = ∑ a ∈ Finset.range q, (if a = A then h (A % d1) else 0) := Finset.sum_congr rfl hpoint
      _ = h (A % d1) := Finset.sum_ite_eq_of_mem' _ _ _ (Finset.mem_range.mpr hA_lt)
  -- RHS: only `a1 = B` survives
  have hR : (∑ a1 ∈ Finset.range d1, (if s % d1 = (r * a1) % d1 then (1 : ℝ) else 0) * h a1)
      = h B := by
    have hpoint : ∀ a1 ∈ Finset.range d1,
        (if s % d1 = (r * a1) % d1 then (1 : ℝ) else 0) * h a1
          = (if a1 = B then h B else 0) := by
      intro a1 ha
      rw [Finset.mem_range] at ha
      by_cases hBa : a1 = B
      · subst hBa; rw [if_pos hspecd.symm, if_pos rfl, one_mul]
      · have hc : ¬ (s % d1 = (r * a1) % d1) :=
          fun hc => hBa ((sol_unique r s d1 hrd1 hd1 ha hc.symm).trans hB.symm)
        rw [if_neg hc, if_neg hBa, zero_mul]
    calc (∑ a1 ∈ Finset.range d1, (if s % d1 = (r * a1) % d1 then (1 : ℝ) else 0) * h a1)
        = ∑ a1 ∈ Finset.range d1, (if a1 = B then h B else 0) := Finset.sum_congr rfl hpoint
      _ = h B := Finset.sum_ite_eq_of_mem' _ _ _ (Finset.mem_range.mpr hB_lt)
  -- `A % d1` is the unique solution mod `d1`, hence equals `B`
  have hAB : A % d1 = B := by
    have h1 : r * (A % d1) ≡ s [MOD d1] := by
      have hq' : r * A ≡ s [MOD q] := hspecq
      exact ((Nat.mod_modEq A d1).mul_left r).trans (Nat.ModEq.of_dvd hd1q hq')
    exact (sol_unique r s d1 hrd1 hd1 (Nat.mod_lt A (by omega)) h1).trans hB.symm
  rw [hL, hR, hAB]

end Work.FIArea4.Vflip
