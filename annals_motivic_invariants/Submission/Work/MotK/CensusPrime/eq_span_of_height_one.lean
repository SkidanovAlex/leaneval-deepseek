import Mathlib
import Submission.Work.MotK.CensusBridge.resF_span_eq_ratFunc

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.CensusPrime

/-- **Uniqueness of the height-one prime above a principal prime.**

If `(G)` is a height-one prime of `K[x₀,x₁,x₂]` and `p` is any prime of height one containing `G`,
then `p = (G)`.

This is the bookkeeping step that discharges the `G_other` / `F_all` conditions of
`Work.MotV.LinkCert`: once the link's two divisor polynomials have been *identified* with a
principal prime of the coordinate ring (via `Work.MotK.CensusBridge.resF_span_eq_ratFunc`), the only
height-one prime above them is that principal prime itself, so "every other height-one prime above
`G` is junk" is vacuous, and "every height-one prime above `F` has residue field ≅ `RatFunc F₂` or
is junk" reduces to the single prime `(F)`.

Proof: Mathlib's `Ideal.eq_span_singleton_of_height_eq_one` (`Prime G` is obtained from the
primality of `(G)` via `Ideal.span_singleton_prime`, `G ≠ 0` from `hheight`). -/
theorem eq_span_of_height_one {K : Type} [Field K] (G : MvPolynomial (Fin 3) K)
    (hprime : (Ideal.span {G} : Ideal (MvPolynomial (Fin 3) K)).IsPrime)
    (hheight : Ideal.height (Ideal.span {G} : Ideal (MvPolynomial (Fin 3) K)) = 1)
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime] (hp : p.height = 1) (hGp : G ∈ p) :
    p = Ideal.span {G} := by
  -- `hheight = 1` forces `(G) ≠ ⊥`, so `G ≠ 0`; hence `G` is a prime element.
  have hG0 : G ≠ 0 := by
    intro h
    exact Ideal.ne_bot_of_height_eq_one hheight (by rw [Ideal.span_singleton_eq_bot]; exact h)
  have hGprime : Prime G := (Ideal.span_singleton_prime hG0).mp hprime
  -- A height-one prime containing `G` is then exactly the principal prime `(G)`.
  exact Ideal.eq_span_singleton_of_height_eq_one hp hGp hGprime

end Work.MotK.CensusPrime
