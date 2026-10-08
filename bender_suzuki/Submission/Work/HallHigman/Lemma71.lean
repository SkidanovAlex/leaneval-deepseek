/-
Area A10 of the Feit--Thompson (odd order theorem) drive:
**Feit--Thompson, Chapter II, Lemma 7.1**, deduced from Hall--Higman Theorem B.

The paper (p. 791) states:  *if `H` is a `p`-solvable linear group of odd order over a field of
characteristic `p`, then `O_p(H)` contains every element whose minimal polynomial is
`(x - I) ^ 2`*.  This is the first of the two Hall--Higman-type inputs of the local analysis; the
proof is in `Submission/Work/HallHigman/FTLemma71_zmod_of_HallHigmanB.lean`, and the ingredients it
uses are documented in `Submission/Work/HallHigman/NOTES.md` §4 (T2).

Here we record the statement in the unfolded form in which it will be used downstream: as a
function of the hypothesis `hB` that Hall--Higman Theorem B holds for `F_p = ZMod p`.
-/
import Mathlib
import Submission.Work.HallHigman.Basic
import Submission.Work.HallHigman.HallHigmanB
import Submission.Work.HallHigman.FT71
import Submission.Work.HallHigman.FTLemma71_zmod_of_HallHigmanB
import Submission.Work.HallHigman.minpoly_eq_X_sub_one_sq_of_sq_eq_zero
import Submission.Work.HallHigman.GLCore.hallHigmanB1
import Submission.Work.HallHigman.GLCore.FTLemma71_zmod_of_HallHigmanB1
import Submission.Work.HallHigman.GLCore.FTLemma71_of_HallHigmanB1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

universe u v

namespace Work.HallHigman

open Polynomial

/-- **Feit--Thompson, Lemma 7.1** (odd order form, deduced from Hall--Higman Theorem B):  if `H` is
a `p`-solvable group of odd order with `p ≠ 2` acting faithfully on a finite dimensional
`F_p`-module `V`, then every element whose minimal polynomial on `V` is `(X - 1) ^ 2` lies in the
`p`-core `O_p(H)`. -/
theorem lemma_7_1 {p : ℕ} [Fact p.Prime] (hB : HallHigmanB.{0, v} (ZMod p) p) (hp : p ≠ 2)
    {H : Type v} [Group H] [Finite H] (hsol : IsPSolvable p H) (hodd : Odd (Nat.card H))
    (V : FDRep (ZMod p) H) (hfaith : Function.Injective V.ρ) (x : H)
    (hx : minpoly (ZMod p) (V.ρ x) = (X - 1) ^ 2) : x ∈ pCore p H :=
  FTLemma71_zmod_of_HallHigmanB hB hp H hsol hodd V hfaith x hx

/-- The same statement with the minimal polynomial hypothesis replaced by the equivalent
"`(ρ x - 1) ^ 2 = 0` and `x ≠ 1`" (the form used in the induction). -/
theorem lemma_7_1' {p : ℕ} [Fact p.Prime] (hB : HallHigmanB.{0, v} (ZMod p) p) (hp : p ≠ 2)
    {H : Type v} [Group H] [Finite H] (hsol : IsPSolvable p H) (hodd : Odd (Nat.card H))
    (V : FDRep (ZMod p) H) (hfaith : Function.Injective V.ρ) (x : H)
    (hx : (V.ρ x - 1) ^ 2 = 0) (hx1 : x ≠ 1) : x ∈ pCore p H :=
  lemma_7_1 hB hp hsol hodd V hfaith x
    (minpoly_eq_X_sub_one_sq_of_sq_eq_zero (f := V.ρ x) hx
      (fun hρ => hx1 (hfaith (by rw [hρ, map_one]))))

/-! ### The unconditional form

With the order-`p` form of Hall--Higman Theorem B proved (`Work.HallHigman.GLCore.hallHigmanB1`,
via the GL-core of `NOTES_LEAD_ft_hallhigman.md`: L0--L18), Feit--Thompson's Lemma 7.1 becomes
unconditional over `F_p`. -/

/-- **Feit--Thompson, Chapter II, Lemma 7.1** (unconditional, over `F_p`):  if `H` is a `p`-solvable
group of odd order with `p ≠ 2` acting faithfully on an `F_p`-module `V`, then every element whose
minimal polynomial on `V` is `(X - 1) ^ 2` lies in the `p`-core `O_p(H)`. -/
theorem lemma_7_1_unconditional {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {H : Type v} [Group H]
    [Finite H] (hsol : IsPSolvable p H) (hodd : Odd (Nat.card H)) (V : FDRep (ZMod p) H)
    (hfaith : Function.Injective V.ρ) (x : H)
    (hx : minpoly (ZMod p) (V.ρ x) = (X - 1) ^ 2) : x ∈ pCore p H :=
  GLCore.FTLemma71_zmod_of_HallHigmanB1 (GLCore.hallHigmanB1 hp (ZMod p)) hp H hsol hodd
    V hfaith x hx

/-- The same statement with the minimal polynomial hypothesis replaced by the equivalent
"`(ρ x - 1) ^ 2 = 0` and `x ≠ 1`". -/
theorem lemma_7_1_unconditional' {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {H : Type v} [Group H]
    [Finite H] (hsol : IsPSolvable p H) (hodd : Odd (Nat.card H)) (V : FDRep (ZMod p) H)
    (hfaith : Function.Injective V.ρ) (x : H) (hx : (V.ρ x - 1) ^ 2 = 0) (hx1 : x ≠ 1) :
    x ∈ pCore p H :=
  lemma_7_1_unconditional hp hsol hodd V hfaith x
    (minpoly_eq_X_sub_one_sq_of_sq_eq_zero (f := V.ρ x) hx
      (fun hρ => hx1 (hfaith (by rw [hρ, map_one]))))

/-- **Feit--Thompson, Chapter II, Lemma 7.1**, in the generality of the paper (any field of
characteristic `p ≠ 2`), unconditional: every element of a `p`-solvable linear group of odd order
whose minimal polynomial is `(X - 1) ^ 2` lies in the `p`-core. -/
theorem lemma_7_1_field_unconditional {K : Type u} [Field K] {p : ℕ} [CharP K p] [Fact p.Prime] (hp : p ≠ 2)
    {H : Type v} [Group H] [Finite H] (hsol : IsPSolvable p H) (hodd : Odd (Nat.card H))
    (V : FDRep K H) (hfaith : Function.Injective V.ρ) (x : H)
    (hx : minpoly K (V.ρ x) = (X - 1) ^ 2) : x ∈ pCore p H :=
  GLCore.FTLemma71_of_HallHigmanB1 (K := K) (p := p) hp H hsol hodd V hfaith x hx

end Work.HallHigman
