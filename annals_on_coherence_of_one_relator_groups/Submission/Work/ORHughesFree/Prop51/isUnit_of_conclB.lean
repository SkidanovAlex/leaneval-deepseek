import Mathlib
import Submission.Work.ORHughesFree.Prop51
import Submission.Work.ORHughesFree.SkewLaurentSeries.exists_least_nonzero_coeff
import Submission.Work.ORHughesFree.SkewLaurentSeries.exists_inverse_of_vanishesBelow_of_coeff_isUnit

set_option autoImplicit false

namespace Work.ORHughesFree.Prop51

/-- **The final step of [JZLA20, Proposition 5.1] for an element whose series has only unit
coefficients.**  If `a ∈ D_{H,P}` satisfies the conclusion `Prop51Concl` of [JZLA20, Proposition
5.1] — so that `a = laurentEmbed f` for a series `f ∈ D_{N,P}((t;τ))` — and if every non-zero
coefficient `f.1 k` of that series is a **unit** of `D_{N,P}`, then `a` is a unit of `P`, hence
(given `D_{H,P}`'s inverse-closure `Prop51Data.DH_inv_closed`) invertible in `D_{H,P}`.

This replaces the earlier `inv_of_prop51Concl`, which deduced the same conclusion from the
*stronger* hypothesis `IsDivisionRing ↥DN`.  The hypothesis `hunit` is what the induction of
[JZLA20, Theorem 6.1] supplies: for the coefficients of strictly smaller `H`-complexity it comes
from the induction hypothesis together with `Prop51Data.DN_inv_closed` (a unit of `D_{H,P}` that
lies in `D_{N,P}` has its inverse in `D_{N,P}`), and the remaining case — `a` a single monomial
`a_n t^n` — is excluded by the primitive-realiser argument of the paper (see the README). -/
theorem isUnit_of_conclB {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Work.ORHughesFree.Prop51Data Γ P DN)
    {a : P} (ha : a ∈ d.DH) (h : Work.ORHughesFree.Prop51Concl d a) (hne : a ≠ 0)
    (hunit : ∀ (f : Work.ORHughesFree.SkewLaurentSeries ↥DN), d.laurentEmbed f = a →
      ∀ k : ℤ, f.1 k ≠ 0 → IsUnit (f.1 k)) :
    ∃ y ∈ d.DH, a * y = 1 := by
  obtain ⟨f, hf, -, -⟩ := h
  have hf0 : f ≠ 0 := fun h0 => hne (by rw [← hf, h0, map_zero])
  obtain ⟨m, hm', hm⟩ := Work.ORHughesFree.SkewLaurentSeries.exists_least_nonzero_coeff f hf0
  obtain ⟨u, hfu, huf, -⟩ := Work.ORHughesFree.SkewLaurentSeries.exists_inverse_of_vanishesBelow_of_coeff_isUnit hm (hunit f hf m hm')
  have hunit : IsUnit f := ⟨⟨f, u, hfu, huf⟩, rfl⟩
  exact d.DH_inv_closed a ha (by rw [← hf]; exact hunit.map d.laurentEmbed)

end Work.ORHughesFree.Prop51
