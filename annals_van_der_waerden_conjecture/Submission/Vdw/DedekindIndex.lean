import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Submission.Commons.NumberTheory.NumberField.discr_dvd_of_isIntegral_basis
import Submission.Commons.FieldTheory.Discriminant.discr_powerBasis_eq_discr
import Submission.Commons.RingTheory.Polynomial.discr_map
import Submission.Vdw.CaseI

open Function Polynomial
open scoped BigOperators NumberField

set_option autoImplicit false

/-!
# The Dedekind index bridge: `D_f | disc(f)`

Bhargava, *Galois groups of random integer polynomials* (Annals of Math 201(2)
(2025)), proof of Theorem 1 — Case I needs the classical **Dedekind
divisibility** `D_f = |discr K_f|` divides the polynomial discriminant
`disc(f)` (so `D_f ≤ |disc(f)| ≤ C_n H^{2n-2}` inside the box, and so the
`mod C_f` congruence conditions of Case I can be phrased through `disc(f)`).

Proof structure (this module supplies all the *local* glue; the two purely
general bridges are in the shared commons):

1. `kpolyPowerBasis f hf`: the canonical `PowerBasis ℚ (Kpoly f)` of the
   number field `K_f = ℚ[x]/(f)`, whose generator `α` is the root of
   `f` (integral over `ℤ` since `f` is monic integer).
2. `minpoly_kpoly_gen`: `minpoly ℚ α = f.map φℚ` (monic irreducible).
3. **Commons bridge 1** `Commons.FieldTheory.Discriminant.discr_powerBasis_eq_discr`:
   `Polynomial.discr (minpoly F pb.gen) = Algebra.discr F pb.basis`, so
   `disc(f) = Algebra.discr ℚ (α-basis)`.
4. **Commons bridge 2** `Commons.NumberTheory.NumberField.discr_dvd_of_isIntegral_basis`:
   since the power basis consists of algebraic integers, its discriminant is
   an integer multiple of `discr K_f`.
5. Conclusion: `(fieldDisc f : ℤ) ∣ polyDisc f`
   (`fieldDisc_dvd_polyDisc`, proved at the bottom of this file).

All three bridge lemmas are now in the shared commons and the whole chain is
proved below.
-/

namespace Submission.Vdw

noncomputable section

variable (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))] (hf : f.Monic)

/-- The canonical power basis of `K_f = ℚ[x]/(f)`: the powers of the root. -/
noncomputable def kpolyPowerBasis (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (hf : f.Monic) : PowerBasis ℚ (Kpoly f) :=
  (AdjoinRoot.isAdjoinRootMonic (f.map φℚ) (hf.map φℚ)).powerBasis

/-- The generator of the power basis is the adjoined root of `f`. -/
theorem kpolyPowerBasis_gen_eq_root :
    (kpolyPowerBasis f hf).gen =
      (AdjoinRoot.isAdjoinRootMonic (f.map φℚ) (hf.map φℚ)).root := by
  rfl

/-- The generator `α` of `K_f` is an algebraic integer: it is a root of the
monic integer polynomial `f`. -/
theorem kpolyPowerBasis_gen_isIntegralInt : IsIntegral ℤ (kpolyPowerBasis f hf).gen := by
  rw [kpolyPowerBasis_gen_eq_root]
  refine ⟨f, hf, ?_⟩
  -- the ℤ-algebra and ℚ-algebra actions on `Kpoly f` agree (any ring hom
  -- from ℤ is `Int.cast`)
  have hcomp : (algebraMap ℚ (Kpoly f)).comp φℚ = algebraMap ℤ (Kpoly f) := by
    ext n
    rw [eq_intCast (f := (algebraMap ℚ (Kpoly f)).comp φℚ),
      eq_intCast (f := algebraMap ℤ (Kpoly f))]
  -- the ℤ-aeval of `f` at the root equals the ℚ-aeval of `f.map φℚ`, which
  -- vanishes because the root is a root of the adjoined polynomial
  have hEq : Polynomial.aeval (R := ℤ) (A := Kpoly f)
      (AdjoinRoot.isAdjoinRootMonic (f.map φℚ) (hf.map φℚ)).root f = 0 := by
    rw [Polynomial.aeval_eq_aeval_map (R := ℤ) (S := Kpoly f) (T := ℚ) (φ := φℚ) hcomp
      (p := f) (a := (AdjoinRoot.isAdjoinRootMonic (f.map φℚ) (hf.map φℚ)).root)]
    exact (AdjoinRoot.isAdjoinRootMonic (f.map φℚ) (hf.map φℚ)).aeval_root_self
  simpa [Polynomial.aeval_def] using hEq

/-- Every power-basis vector `αⁱ` is an algebraic integer. -/
theorem kpolyPowerBasis_basis_isIntegralInt :
    ∀ i : Fin (kpolyPowerBasis f hf).dim, IsIntegral ℤ ((kpolyPowerBasis f hf).basis i) := by
  intro i
  rw [PowerBasis.basis_eq_pow]
  exact IsIntegral.pow (kpolyPowerBasis_gen_isIntegralInt f hf) i

/-- The minimal polynomial of the generator is `f.map φℚ` (monic irreducible
with the generator as a root). -/
theorem minpoly_kpoly_gen : minpoly ℚ (kpolyPowerBasis f hf).gen = f.map φℚ := by
  rw [kpolyPowerBasis_gen_eq_root]
  exact IsAdjoinRootMonic.minpoly_eq (AdjoinRoot.isAdjoinRootMonic (f.map φℚ) (hf.map φℚ))
    (Fact.out : Irreducible (f.map φℚ))

/-- The polynomial discriminant commutes with the change of base ring
`φℚ : ℤ → ℚ`: `disc(f)` as an element of `ℚ` equals `disc(f.map φℚ)`.
(From `Commons.RingTheory.Polynomial.discr_map` — `f` is monic.) -/
theorem polyDisc_cast (f : ℤ[X]) (hf : f.Monic) :
    (polyDisc f : ℚ) = Polynomial.discr (f.map φℚ) := by
  dsimp [polyDisc]
  exact (Commons.RingTheory.Polynomial.discr_map (φ := φℚ) (p := f) hf).symm

/-- The integer divisibility of the field discriminant by the polynomial
discriminant, before taking absolute values. -/
theorem fieldDisc_dvd_polyDisc_aux (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (hf : f.Monic) : (NumberField.discr (Kpoly f) : ℤ) ∣ polyDisc f := by
  let pb := kpolyPowerBasis f hf
  obtain ⟨m, hm⟩ := Commons.NumberTheory.NumberField.discr_dvd_of_isIntegral_basis
    pb.basis (kpolyPowerBasis_basis_isIntegralInt f hf)
  have hd2 : Polynomial.discr (minpoly ℚ pb.gen) = Algebra.discr ℚ pb.basis :=
    Commons.FieldTheory.Discriminant.discr_powerBasis_eq_discr (F := ℚ) (S := Kpoly f) (pb := pb)
  have hd2' : Polynomial.discr (f.map φℚ) = Algebra.discr ℚ pb.basis := by
    rw [show minpoly ℚ pb.gen = f.map φℚ by
      dsimp [pb]
      exact minpoly_kpoly_gen f hf] at hd2
    exact hd2
  have hcast : (polyDisc f : ℚ) = Polynomial.discr (f.map φℚ) := polyDisc_cast f hf
  have hEqQ : (polyDisc f : ℚ) = (NumberField.discr (Kpoly f) : ℚ) * m := by
    rw [hcast, hd2', hm]
  have hInt : polyDisc f = NumberField.discr (Kpoly f) * m := by
    exact_mod_cast hEqQ
  exact ⟨m, hInt⟩

/-- **Dedekind:** the field discriminant `D_f = |discr K_f|` divides the
polynomial discriminant `disc(f)` of a monic irreducible `f`.  (Standard
proof via `disc(f) = discr(K) · [𝒪_K : ℤ[α]]²`; the square is witnessed by
the change-of-basis determinant between the integral basis of `𝓞 K` and the
power basis of `ℤ[α]`.) -/
theorem fieldDisc_dvd_polyDisc (f : ℤ[X]) [Fact (Irreducible (f.map φℚ))]
    (hf : f.Monic) : (fieldDisc f : ℤ) ∣ polyDisc f := by
  obtain ⟨m, hm⟩ := fieldDisc_dvd_polyDisc_aux f hf
  rcases Int.natAbs_eq (NumberField.discr (Kpoly f)) with hc | hc
  · refine ⟨m, ?_⟩
    calc
      polyDisc f = NumberField.discr (Kpoly f) * m := hm
      _ = ((NumberField.discr (Kpoly f)).natAbs : ℤ) * m := by
        exact congrArg (fun d : ℤ => d * m) hc
  · refine ⟨-m, ?_⟩
    calc
      polyDisc f = NumberField.discr (Kpoly f) * m := hm
      _ = -((NumberField.discr (Kpoly f)).natAbs : ℤ) * m := by
        exact congrArg (fun d : ℤ => d * m) hc
      _ = ((NumberField.discr (Kpoly f)).natAbs : ℤ) * -m := by ring

end
end Submission.Vdw
