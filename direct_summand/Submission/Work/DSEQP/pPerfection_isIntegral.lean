import Mathlib
import Submission.Work.DSEQP.Perfection

namespace Work.DSEQP

namespace pPerfection

variable {A : Type*} [CommRing A] {p : ℕ} [Fact p.Prime] [CharP A p]

/-- The `e`-th element of the root tower of `a` is a `p ^ e`-th root of (the image of) `a`. -/
theorem of_pow_pow (e : ℕ) (a : A) :
    (of (A := A) (p := p) e a) ^ (p ^ e) = of (A := A) (p := p) 0 a := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', pow_mul, of_succ_pow, ih]

end pPerfection

/-- Every element of the `p`-perfection `A^{1/p^∞}` is integral over `A`: the element
`of e a` satisfies the monic equation `X ^ (p ^ e) - (of 0 a) = 0`. -/
theorem pPerfection_isIntegral (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime] [CharP A p] :
    Algebra.IsIntegral A (pPerfection A p) := by
  refine ⟨fun z => ?_⟩
  refine Ring.DirectLimit.induction_on (G := fun _ : ℕ => A)
    (f := fun i j _ => ⇑(frobPowHom A p (j - i))) z ?_
  intro i x
  have h : IsIntegral A ((pPerfection.of (A := A) (p := p) i x) ^ (p ^ i)) := by
    rw [pPerfection.of_pow_pow]
    exact isIntegral_algebraMap
  exact (IsIntegral.pow_iff (R := A) (n := p ^ i) (pow_pos (Fact.out : p.Prime).pos i)).mp h

end Work.DSEQP
