import Mathlib
import Submission.Work.ThmF.ChV12.transitive_orbit_basics
import Submission.Work.ThmF.ChV12.Fitting_cyclic_fpf
import Submission.Work.ThmF.ChV12.centralizer_irreducible_isCyclic
import Submission.Work.ThmF.ChV12.irreducible_of_orderOf_prime
import Submission.Work.ThmF.ChV12.solvable_of_cyclic_normal_irreducible
import Submission.Work.ThmF.ChV12.card_mulAut_two_pow_six
import Submission.Work.ThmF.ChV12.solvable_of_card_dvd_615195

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

/-- **Solvability of `D` for `|A| = 2 ^ 6`.**

`D` acts faithfully on the elementary abelian `2`-group `A` of order `64`, hence embeds in
`MulAut A ≅ GL₆(𝔽₂)`, of order `2 ^ 15 * 615195`.  As `|D|` is odd it divides
`615195 = 3 ^ 4 * 5 * 7 ^ 2 * 31`, and every group of odd order dividing `615195` is solvable
(elementary Sylow counting together with Burnside's normal `p`-complement theorem for the
prime `5`).

The transitivity hypothesis is not needed for this route: the bound on `|D|` alone suffices.  (It
remains essential for the *other* uses of the lemma, hence is retained in the statement.) -/
theorem solvable_of_transitive_two_pow_six {A D : Type} [Group A] [Group D] [Finite A] [Finite D]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x)
    (hk : Nat.card A = 2 ^ 6) (hodd : Odd (Nat.card D)) (ρ : D →* MulAut A)
    (hfaith : Function.Injective ρ)
    (htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ d : D, ρ d a = b) :
    Group.IsSolvable D :=
  solvable_of_card_dvd_615195 hodd (card_dvd_615195 hA2 hAc hk hodd ρ hfaith)

end Work.ThmF.ChV12
