import Submission.Work.DSM8m2.Setup
import Submission.Work.DSM8m2.Body
import Submission.Work.DSM8m2.Basic.injective_phi_functionField
import Submission.Work.DSM8m2.Zariski.functionField_finiteDimensional
import Submission.Work.DSREG.Main

/-!
# DSM8m2 — `area_M8mpos`: the monogenic presentation of the generic chart

Deliverable of the subproject: a proof of the frozen node `DSMap.Mix2Fix.area_M8mpos`, i.e. of
`DSMap.Mix2.area_M8m` with the additional clause `0 < F.natDegree` that removes the degenerate
solution `F = 1`.

See `DESIGN.md` for the route.  The four inputs of `Submission/Work/DSM8m/DESIGN.md` §3 (integral
closedness of `A`, finiteness of `Γ(X,⊤)`, `IsFractionRing Γ(X,⊤) K(X)`, generation of `Γ(X,U_j)`
by `Γ(X,⊤)` and the coordinates) are *not* used.  Instead:

* `Work.DSM8m2.Algebra.exists_integral_primitive`: a primitive element `θ` of `K(X)/K` may be
  scaled to an element `η` which is integral over `A` and whose minimal polynomial over `K` already
  has coefficients in `A` (so `A[η] = A[T]/(minpoly A η)`);
* `Work.DSM8m2.Chart.finiteType_phiU`: the chart ring `Γ(X,U_j)` is a finitely generated
  `A`-algebra (local finite type of the proper morphism `f`);
* `Work.DSM8m2.Algebra.exists_clearing_denominator` puts `Γ(X,U_j) ⊆ A[η][1/c]`, and
  `Work.DSM8m2.Assemble` turns that into an `A`-algebra map into
  `(AdjoinRoot (minpoly A η))[1/(p·g)]`, with `g ∉ (p)` from
  `Work.DSM8m2.Normalize.exists_notMem_span_dvd` (Krull's intersection theorem).

The only geometric input left is the finiteness of `K(X)/K`, isolated in
`Work.DSM8m2.Zariski.functionField_finiteDimensional`; `Work.DSM8m2.Body` contains the rest of the
proof with that finiteness as a hypothesis.
-/

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Work.DSM8m2

universe a

/-- **M8mpos**: `area_M8m` plus `0 < F.natDegree`. -/
theorem area_M8mpos (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (p : ℕ) [Fact p.Prime] [CharZero A]
    [CharP (ResidueField A) p] (X : Scheme.{a}) [IsIntegral X] (f : X ⟶ Spec (.of A))
    [IsProper f] (hs : Function.Surjective f) (hg : DSMap.IsGenFinite A f)
    (hp : DSMap.IsProjOver A f) :
    ∃ (g : A) (N : ℕ) (i : X ⟶ DSMap.PSpace A N) (j : Fin (N + 1)) (F : Polynomial A)
      (θ : Γ(X, DSMap.Mix2.chartCover i ⟨j⟩) →+*
        Localization.Away (algebraMap A (AdjoinRoot F) ((p : A) * g))),
      g ∉ Ideal.span {(p : A)} ∧ IsClosedImmersion i ∧ i ≫ DSMap.PSpace.toSpec A N = f ∧
      F.Monic ∧
      0 < F.natDegree ∧
      θ.comp (DSMap.phiU A X f (DSMap.Mix2.chartCover i ⟨j⟩)) =
        (algebraMap (AdjoinRoot F) _).comp (algebraMap A (AdjoinRoot F)) := by
  -- `A` is a domain (`DSREG`); a point of `X` gives nonempty sections everywhere it is needed
  haveI hAdom : IsDomain A := DSMap.area_REG_proved A
  have hXne : Nonempty X := by
    obtain ⟨𝔭⟩ : Nonempty (Spec (CommRingCat.of A)) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
    obtain ⟨x, -⟩ := hs 𝔭
    exact ⟨x⟩
  haveI hTop : Nonempty (⊤ : X.Opens) := ⟨⟨hXne.some, trivial⟩⟩
  -- the `A`-algebra structure on `L = K(X)`, and `K = Frac A`
  let L := X.functionField
  let φL : A →+* L := phiL A X f
  have hφLinj : Function.Injective φL := Basic.injective_phi_functionField f hs
  letI hAlgA : Algebra A L := φL.toAlgebra
  have hφL : ∀ a : A, algebraMap A L a =
      (Scheme.germToFunctionField X ⊤).hom (DSMap.phi A X f a) := fun a => rfl
  letI hAlgK : Algebra (FractionRing A) L := (IsFractionRing.lift (g := φL) hφLinj).toAlgebra
  haveI hTower : IsScalarTower A (FractionRing A) L :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      show φL a = IsFractionRing.lift (g := φL) hφLinj (algebraMap A (FractionRing A) a)
      exact (IsFractionRing.lift_algebraMap hφLinj a).symm)
  -- the geometric input: `K(X)` is finite over `K` (and separable, in characteristic zero)
  haveI hFin : FiniteDimensional (FractionRing A) L :=
    Zariski.functionField_finiteDimensional f hs hg hφL
  haveI hCharZero : CharZero (FractionRing A) := IsFractionRing.charZero A
  haveI hPerfect : PerfectField (FractionRing A) := PerfectField.ofCharZero
  haveI hAlgAlg : Algebra.IsAlgebraic (FractionRing A) L :=
    Algebra.IsAlgebraic.of_finite (FractionRing A) L
  haveI hSep : Algebra.IsSeparable (FractionRing A) L := inferInstance
  exact area_M8mpos_of_finiteDimensional A p X f hs hg hp hφL

end Work.DSM8m2

universe a

/-- the proven node has exactly the frozen type of `DSMap.Mix2Fix.area_M8mpos` -/
example : type_of% (@Work.DSM8m2.area_M8mpos.{a}) = type_of% (@DSMap.Mix2Fix.area_M8mpos.{a}) :=
  rfl
