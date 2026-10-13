import Mathlib
import Submission.Work.DSG4b.RootLift

/-!
# DSG4b — the root presentation of the residue-field enlargement

Let `R` be a regular local ring, `k = R/𝔪` its residue field and `K = k̄ = AlgebraicClosure k`.
Choose, once and for all, a set-theoretic section `coeffLift : k → R` of the residue map
(`Submission/Work/DSG4b/RootLift.lean`).

For `s ∈ K` let `rel R s ∈ MvPolynomial K R` be the image of `polyLift (minpoly k s)` under
`X s`.  Its reduction modulo `𝔪` is the minimal polynomial of `s`, so `rel R s` is *monic* in the
single variable `X s`.  Quotienting `MvPolynomial K R` by all the `rel R s` therefore has a
`K`-valued point

`ev : MvPolynomial K R →+* K,   X s ↦ s,   coefficients via R → k ⊆ K`

which kills all the relations, hence descends to `rootEv : rootRing R →+* K`.  Its kernel is a
prime (indeed maximal) ideal `rootKer R`, and localising at it gives the ring
`rootLocal R := Localization.AtPrime (rootKer R)`, a local `R`-algebra with residue field `K`,
which is the carrier of the residue-field enlargement (see the follow-up files for flatness over
`R` and for the statement that `𝔪L` is *the* maximal ideal of `L`).

## Status / to do (important)

`relIdeal R` consists of the minimal-polynomial relations alone (one monic equation per variable)
and is exactly the ideal of `Work.DSG4b.flat_mvPolynomial_quotient_monic`, so `rootRing R` is flat
over `R` and has the `K`-valued point `rootEv`.

However, `𝔪 · rootLocal R` is in general *strictly smaller* than the maximal ideal of
`rootLocal R`: the reductions of the relations modulo `𝔪` are the minimal polynomials of the
elements of `K` over `k`, and for `k` imperfect these generate a ring whose localisation at
`ker (C → K)` has nilpotents.  Example: `k = 𝔽_p(t)`, `K = k̄`, and the two variables
`T_1 = X_{t^{1/p}}`, `T_2 = X_{t^{1/p²}}`.  The relations are `T_1 ^ p = t` and `T_2 ^ (p²) = t`,
whence `(T_2 ^ p - T_1) ^ p = 0`; the element `ε = T_2 ^ p - T_1` lies in the maximal ideal and is
a non-zero nilpotent.  Only the extra "Frobenius compatibility" relation
`X_{s^p} = X_s ^ p` (for all `s ∈ K`, in residue characteristic `p`) forces `ε = 0`.  With these
relations added the `𝔪`-fibre is the compositum of the (separable) minimal-polynomial steps with
the purely inseparable `p`-power-root tower, which *is* a field, and `𝔪 · rootLocal R` becomes the
maximal ideal, giving `edim = dim R` as needed for regularity.

So: the honest split is
* `relIdeal R` as defined here (minimal polynomials only) — flat over `R`, residue field `K`;
* the full relation ideal `relIdeal R + (X_{s^p} - X_s^p : s ∈ K)` — of which one must show
  that it still gives a flat `R`-algebra (a *triangular/monic* flatness statement finer than
  `flat_mvPolynomial_quotient_monic`, because the Frobenius relations are linear, not monic, in
  their variable) and that its `𝔪`-fibre is a field.
-/

namespace Work.DSG4b

open Polynomial

universe u

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

noncomputable section

/-- The residue field of `R`. -/
abbrev ResField : Type u := IsLocalRing.ResidueField R

/-- The target residue field: the algebraic closure of the residue field of `R`. -/
abbrev AlgebrClosure : Type u := AlgebraicClosure (IsLocalRing.ResidueField R)

/-- The monic polynomial attached to `s : K`: a coefficientwise lift of its minimal polynomial
over `k` (`R`-valued, so that it can be evaluated in an `R`-algebra). -/
noncomputable def minPolyLift (s : AlgebrClosure R) : Polynomial R :=
  polyLift (minpoly (IsLocalRing.ResidueField R) s)

lemma minPolyLift_monic (s : AlgebrClosure R) : (minPolyLift R s).Monic :=
  polyLift_monic (minpoly.monic (Algebra.IsIntegral.isIntegral s))

/-- The relation attached to `s : K`: the lift of its minimal polynomial, evaluated at the
variable `X s`. -/
noncomputable def rel (s : AlgebrClosure R) : MvPolynomial (AlgebrClosure R) R :=
  Polynomial.aeval (MvPolynomial.X s) (minPolyLift R s)

/-- Evaluation of the "root presentation" ring at the chosen roots: coefficients go through
`R → k ⊆ K` and `X s` goes to `s`. -/
noncomputable def ev : MvPolynomial (AlgebrClosure R) R →+* AlgebrClosure R :=
  MvPolynomial.eval₂Hom
    ((algebraMap (IsLocalRing.ResidueField R) (AlgebrClosure R)).comp (IsLocalRing.residue R))
    (fun s => s)

lemma ev_X (s : AlgebrClosure R) : ev R (MvPolynomial.X s) = s := by
  rw [ev, MvPolynomial.eval₂Hom_X']

lemma ev_algebraMap (a : R) :
    ev R (algebraMap R (MvPolynomial (AlgebrClosure R) R) a) =
      algebraMap (IsLocalRing.ResidueField R) (AlgebrClosure R) (IsLocalRing.residue R a) := by
  rw [MvPolynomial.algebraMap_eq, ev, MvPolynomial.eval₂Hom_C]
  rfl

lemma ev_C (a : R) :
    ev R (MvPolynomial.C a) = algebraMap (IsLocalRing.ResidueField R) (AlgebrClosure R)
      (IsLocalRing.residue R a) := by
  rw [← MvPolynomial.algebraMap_eq]
  exact ev_algebraMap R a

/-- The relations are killed by the evaluation, i.e. `s` is a root of the minimal polynomial of
`s` — the whole point of the construction. -/
lemma ev_rel (s : AlgebrClosure R) : ev R (rel R s) = 0 := by
  have hcomp : (ev R).comp (algebraMap R (MvPolynomial (AlgebrClosure R) R)) =
      (algebraMap (IsLocalRing.ResidueField R) (AlgebrClosure R)).comp
        (IsLocalRing.residue R) :=
    RingHom.ext fun a => by rw [RingHom.comp_apply, RingHom.comp_apply, ev_algebraMap]
  rw [rel, Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp, ev_X]
  rw [← Polynomial.eval₂_map (f := IsLocalRing.residue R)
    (g := algebraMap (IsLocalRing.ResidueField R) (AlgebrClosure R)) (x := s)]
  rw [minPolyLift, map_polyLift, ← Polynomial.aeval_def]
  exact minpoly.aeval (IsLocalRing.ResidueField R) s

/-- The ideal of relations. -/
noncomputable def relIdeal : Ideal (MvPolynomial (AlgebrClosure R) R) :=
  Ideal.span (Set.range (rel R))

lemma rel_mem_relIdeal (s : AlgebrClosure R) : rel R s ∈ relIdeal R :=
  Ideal.subset_span (Set.mem_range_self s)

lemma ev_eq_zero_of_mem_relIdeal {x : MvPolynomial (AlgebrClosure R) R} (hx : x ∈ relIdeal R) :
    ev R x = 0 := by
  refine RingHom.mem_ker.mp ((Ideal.span_le.mpr ?_) hx)
  rintro y ⟨s, rfl⟩
  exact ev_rel R s

/-- The "root presentation" ring. -/
abbrev rootRing : Type u :=
  MvPolynomial (AlgebrClosure R) R ⧸ relIdeal R

instance : CommRing (rootRing R) := Ideal.Quotient.commRing _

/-- The `K`-valued point of the root presentation ring. -/
noncomputable def rootEv : rootRing R →+* AlgebrClosure R :=
  Ideal.Quotient.lift (relIdeal R) (ev R) (fun _ hx => ev_eq_zero_of_mem_relIdeal R hx)

lemma rootEv_mk (x : MvPolynomial (AlgebrClosure R) R) :
    rootEv R (Ideal.Quotient.mk _ x) = ev R x :=
  Ideal.Quotient.lift_mk _ _ _

lemma rootEv_surjective : Function.Surjective (rootEv R) := by
  intro y
  refine ⟨Ideal.Quotient.mk _ (MvPolynomial.X y), ?_⟩
  rw [rootEv_mk, ev_X]

/-- The kernel of the `K`-valued point: the (maximal) ideal at which we localise. -/
noncomputable def rootKer : Ideal (rootRing R) := RingHom.ker (rootEv R)

instance : (rootKer R).IsPrime := RingHom.ker_isPrime _

/-- The local ring of the root presentation at its `K`-valued point. -/
abbrev rootLocal : Type u := Localization.AtPrime (rootKer R)

instance : CommRing (rootLocal R) := inferInstance

instance : IsLocalRing (rootLocal R) :=
  IsLocalization.AtPrime.isLocalRing _ (rootKer R)

end

end Work.DSG4b
