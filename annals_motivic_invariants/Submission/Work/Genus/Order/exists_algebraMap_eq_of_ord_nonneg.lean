import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Order.ord_div

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Order

/-- **A rational function with no finite poles is a polynomial.**  If `ord π f ≥ 0` at every
irreducible `π`, then `f` is the image of a polynomial.  Route: `f.denom` is monic, so if it were
non-constant it would have an irreducible factor `π` (`WfDvdMonoid.exists_irreducible_factor`),
which divides `f.denom` but not `f.num` (`RatFunc.isCoprime_num_denom`), giving `ord π f < 0`. -/
theorem exists_algebraMap_eq_of_ord_nonneg {F : Type*} [Field F] {f : RatFunc F}
    (h : ∀ π : Polynomial F, Irreducible π → 0 ≤ Work.Genus.ord π f) :
    ∃ p : Polynomial F, f = algebraMap (Polynomial F) (RatFunc F) p := by
  classical
  -- The denominator is a unit: otherwise some irreducible `π` divides it.
  have hdvd : f.denom ∣ 1 := by
    by_contra hnot
    have hnu : ¬ IsUnit f.denom := fun hu => hnot hu.dvd
    obtain ⟨π, hπirr, hπdvd⟩ :=
      WfDvdMonoid.exists_irreducible_factor hnu (RatFunc.denom_ne_zero f)
    -- `π` cannot divide the numerator, by coprimality of the reduced form.
    have hπnum : ¬ π ∣ f.num := fun hnumdvd =>
      hπirr.not_isUnit ((RatFunc.isCoprime_num_denom f).isUnit_of_dvd' hnumdvd hπdvd)
    have hmnum : multiplicity π f.num = 0 := multiplicity_eq_zero_of_not_dvd hπnum
    have hmden : 0 < multiplicity π f.denom :=
      multiplicity_pos_of_dvd hπdvd
        (FiniteMultiplicity.of_not_isUnit hπirr.not_isUnit (RatFunc.denom_ne_zero f))
    have hord : Work.Genus.ord π f < 0 := by
      have hpos : (0 : ℤ) < (multiplicity π f.denom : ℤ) := by exact_mod_cast hmden
      simp only [Work.Genus.ord, hmnum, Nat.cast_zero, zero_sub]
      omega
    have := h π hπirr
    omega
  rw [RatFunc.denom_dvd (one_ne_zero : (1 : Polynomial F) ≠ 0)] at hdvd
  obtain ⟨p, hp⟩ := hdvd
  exact ⟨p, by rw [hp, map_one, div_one]⟩

end Work.Genus.Order
