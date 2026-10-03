import Mathlib
import Submission.Work.FIArea2.congCount
import Submission.Work.FIArea2.Ncount_mul
import Submission.Work.FIArea1.L51Rec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The refined local count of *FI* §9 (`card_sq_congr_l51`)

This file sets up the vocabulary used in `Submission/Work/FIArea1/card_sq_congr_l51.lean`:

* `Nc q a b` is the number of pairs `(γ₁,γ₂) ∈ (ℤ/q)²` with `aγ₁² ≡ bγ₂² (mod q)`, with the value
  `0` at `q = 0`.  It is a total function of `q`, which makes it usable inside inductions and
  products without having to carry `NeZero` hypotheses through the statements (the same trick as
  `Work.FIArea2.Nsol`);
* `Nc_eq_Ncount_of_ne` / `Ncount_eq_Nc` / `Nc_pow_eq` relate it to `Work.FIArea2.Ncount`;
* `Nc_swap` is the symmetry in the two coefficients and `Nc_mul` the multiplicativity under the
  Chinese remainder theorem (transported from `Work.FIArea2`).
-/

namespace Work.FIArea1

open Finset

attribute [local instance] Classical.propDecidable

/-- `Nc q a b`: the number of pairs `(γ₁,γ₂)` modulo `q` with `aγ₁² ≡ bγ₂² (mod q)`, and `0` at
`q = 0` (so that `Nc` is a total function of `q`).  For `q ≠ 0` this is `Work.FIArea2.Ncount`. -/
def Nc (q a b : ℕ) : ℕ :=
  if h : q = 0 then 0 else @Work.FIArea2.Ncount q ⟨h⟩ a b

lemma Nc_zero (a b : ℕ) : Nc 0 a b = 0 := by
  rw [Nc, dif_pos rfl]

/-- The defining equation of `Nc` for a non-zero modulus. -/
lemma Nc_eq_Ncount_of_ne (q : ℕ) (hq : q ≠ 0) (a b : ℕ) :
    Nc q a b = @Work.FIArea2.Ncount q ⟨hq⟩ a b := by
  rw [Nc, dif_neg hq]

/-- `Nc` agrees with `Work.FIArea2.Ncount` for a non-zero modulus. -/
lemma Ncount_eq_Nc (q a b : ℕ) [NeZero q] : Work.FIArea2.Ncount q a b = Nc q a b := by
  rw [Nc_eq_Ncount_of_ne q (NeZero.ne q) a b]

/-- `Nc (p^e) a b` written in the form in which the reduction lemmas of `L51Rec` apply. -/
lemma Nc_pow_eq (p e a b : ℕ) (hp : p.Prime) :
    Nc (p ^ e) a b = @Work.FIArea2.Ncount (p ^ e) ⟨pow_ne_zero e hp.ne_zero⟩ a b :=
  Nc_eq_Ncount_of_ne (p ^ e) (pow_ne_zero e hp.ne_zero) a b

/-- `Nc` is symmetric in its two coefficients. -/
lemma Nc_swap (q a b : ℕ) : Nc q a b = Nc q b a := by
  rcases eq_or_ne q 0 with hq | hq
  · subst hq; rw [Nc_zero, Nc_zero]
  · haveI : NeZero q := ⟨hq⟩
    rw [Nc_eq_Ncount_of_ne q hq a b, Nc_eq_Ncount_of_ne q hq b a]
    exact Ncount_swap q a b

/-- **Multiplicativity of `Nc` in the modulus** (Chinese remainder theorem). -/
lemma Nc_mul (m n a b : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    Nc (m * n) a b = Nc m a b * Nc n a b := by
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  haveI : NeZero m := ⟨hm⟩
  haveI : NeZero n := ⟨hn⟩
  haveI : NeZero (m * n) := ⟨hmn⟩
  rw [Nc_eq_Ncount_of_ne (m * n) hmn a b, Nc_eq_Ncount_of_ne m hm a b,
    Nc_eq_Ncount_of_ne n hn a b]
  exact Work.FIArea2.Ncount_mul h a b

/-- The trivial bound `Nc q a b ≤ q * q`. -/
lemma Nc_le (q a b : ℕ) : Nc q a b ≤ q * q := by
  rcases eq_or_ne q 0 with hq | hq
  · subst hq; rw [Nc_zero]
  · haveI : NeZero q := ⟨hq⟩
    rw [Nc_eq_Ncount_of_ne q hq a b, Work.FIArea2.Ncount]
    calc _ ≤ (Finset.univ : Finset (ZMod q × ZMod q)).card := Finset.card_filter_le _ _
      _ = q * q := by rw [Finset.card_univ, Fintype.card_prod, ZMod.card]

end Work.FIArea1
