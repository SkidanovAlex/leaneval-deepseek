import Mathlib
import Submission.Work.DSREG.Defs

namespace Work.DSREG.QuotQuotDim

theorem ringKrullDim_quotient_le_quotQuot_add_one (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) :
    ringKrullDim (R ⧸ p) ≤
      ringKrullDim ((R ⧸ Ideal.span {x}) ⧸ p.map (Ideal.Quotient.mk (Ideal.span {x}))) + 1 := by
  -- The image of `x` in `R ⧸ p` lies in the Jacobson radical: it lies in the maximal ideal
  -- `(x) + p ⧸ p` of the local ring `R ⧸ p`.
  have hxJ : Ideal.Quotient.mk p x ∈ Ring.jacobson (R ⧸ p) := by
    have h1 : x ∈ p.jacobson := IsLocalRing.maximalIdeal_le_jacobson p hx
    have h2 : Ideal.Quotient.mk p x ∈ Ideal.map (Ideal.Quotient.mk p) p.jacobson :=
      Ideal.mem_map_of_mem _ h1
    rw [Ideal.map_jacobson_of_surjective (I := p) (f := Ideal.Quotient.mk p)
        Ideal.Quotient.mk_surjective Ideal.mk_ker.le, Ideal.map_quotient_self,
      Ideal.jacobson_bot] at h2
    exact h2
  -- Krull's principal ideal theorem, in the form: an element of the Jacobson radical can be
  -- divided out at the cost of one in the Krull dimension.
  have hmain := ringKrullDim_le_ringKrullDim_quotient_add_encard (R := R ⧸ p)
    ({Ideal.Quotient.mk p x} : Set (R ⧸ p)) (by rw [Set.singleton_subset_iff]; exact hxJ)
  rw [Set.encard_singleton] at hmain
  -- The two "double quotients" are the same ring: `(R ⧸ p) ⧸ (x)` and `(R ⧸ (x)) ⧸ p`.
  have hspan : (Ideal.span {Ideal.Quotient.mk p x} : Ideal (R ⧸ p))
      = Ideal.map (Ideal.Quotient.mk p) (Ideal.span {x}) := by
    rw [Ideal.map_span]; simp
  have key : ringKrullDim ((R ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p x})
      = ringKrullDim ((R ⧸ Ideal.span {x}) ⧸ Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) p) := by
    rw [hspan, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {x})),
      ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup (Ideal.span {x}) p)]
    rw [sup_comm]
  rw [key] at hmain
  simpa using hmain

end Work.DSREG.QuotQuotDim
