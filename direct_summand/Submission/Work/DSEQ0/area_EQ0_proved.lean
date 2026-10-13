import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSMap.Mix2
import Submission.Work.DSEQ0.Basic
import Submission.Work.DSEQ0.Gamma
import Submission.Work.DSEQ0.exists_finite_affineCover
import Submission.Work.DSEQ0.eq0_inputs
import Submission.Work.DSF1.Main
import Submission.Work.DSMX0bU.Main

/-!
# Area `EQ0` (equal characteristic zero): the deliverable `Work.DSEQ0.area_EQ0_proved`

This file proves the frozen statement of the equal-characteristic-zero area,

```lean
theorem area_EQ0_proved ... : DSMap.DSplit.{a, b, c} A X f
```

by the trace argument of the area (Bhatt, *On the direct summand conjecture and its derived
variant*, the remark after Theorem 5.2): the trace on the perfect complex `RΓ(X, 𝒪_X)`.

## The assembly

1. A finite affine cover `U` of `X` (proved in this area: `Work.DSEQ0.exists_finite_affineCover`,
   from `IsProper f`).
2. A strictly unital finite free model of the Čech complex `Č(U; 𝒪_X)`, carrying its
   coaugmentation, together with the trace functional on it: this is the single remaining input of
   the area, `Work.DSEQ0.exists_traceModelFunctional`
   (`Submission/Work/DSEQ0/eq0_inputs.lean`), which is proved from the three nodes
   `Work.DSEQ0.exists_unitalModel`, `Work.DSEQ0.exists_traceFunctional` and
   `Work.DSEQ0.eulerChar_ne_zero` — see `Submission/Work/DSEQ0/NEXT_input4.md`.
3. Rescaling: any nonzero *integer* is a unit of `A`, because the residue field has characteristic
   zero (`Work.DSEQ0.isUnit_intCast_of_charZero_residueField`), so a functional on `P⁰` killing
   `d⁻¹` and with value `n ≠ 0` at the coaugmentation class exhibits the *honest splitting*
   `DSMap.Mix.ModSplit P ε (RingHom.id A) ⊥ 1` (`Work.DSEQ0.modSplit_of_functional_int`).
4. The bridge `DSMap.Mix2.area_MX0bU_of_F1` (proved, axiom-clean, in
   `Submission/Work/DSMX0bU/Main.lean`) turns the honest splitting of the model into
   `DSplit A X f`; it needs, as its only extra input, the area `F1`
   (`RΓ(X,𝒪) ≅ Q(Č(U;𝒪))` compatibly with the units), which is supplied here by the *proved*
   `DSMap.area_F1_cech_proved` of `Submission/Work/DSF1/Main.lean` (axiom-clean).  Hence no
   placeholder-backed frozen node is cited by this file any more.
-/

open CategoryTheory AlgebraicGeometry

namespace Work.DSEQ0

universe a b c

/-- **The honest splitting from the trace functional.**

If `φ₀ : P⁰ ⟶ A` is an `A`-linear functional killing the differential `d⁻¹ : P⁻¹ ⟶ P⁰` and
taking the value `χ ≠ 0` at the coaugmentation class `ε 1`, then — since every nonzero natural
number is a *unit* of `A`, the residue field having characteristic zero — the rescaled functional
`χ⁻¹ • φ₀` has value `1` at `ε 1` and kills the differential as well.  Transported along the
canonical identification `A ⊗[A] P⁰ ≅ P⁰` this is exactly
`DSMap.Mix.ModSplit P ε (RingHom.id A) ⊥ 1`, the "honest splitting" of the model.

This is the last step of the trace argument of area `EQ0`: it is where the arithmetic input
`χ ∈ A^×` (`Work.DSEQ0.isUnit_natCast_of_charZero_residueField`) is consumed. -/
theorem modSplit_of_functional {A : Type a} [CommRing A] [IsLocalRing A]
    [CharZero (IsLocalRing.ResidueField A)]
    {P : CochainComplex (ModuleCat.{a} A) ℤ} {ε : ModuleCat.of A A ⟶ P.X 0}
    {φ₀ : P.X 0 ⟶ ModuleCat.of A A} {χ : ℕ} (hχ : χ ≠ 0) (hval : φ₀ (ε.hom 1) = (χ : A))
    (hker : P.d (-1) 0 ≫ φ₀ = 0) :
    DSMap.Mix.ModSplit P ε (RingHom.id A) ⊥ 1 := by
  have hunit : IsUnit ((χ : ℕ) : A) := isUnit_natCast_of_charZero_residueField hχ
  -- `φ₀` kills the image of the differential
  have hkill : ∀ z : ↥(P.X (-1)), φ₀.hom ((P.d (-1) 0).hom z) = 0 := by
    intro z
    have h := congrArg (fun (f : P.X (-1) ⟶ ModuleCat.of A A) => f.hom z) hker
    simpa using h
  -- `lid` intertwines the base-changed differential with the differential
  have hlid : ∀ y : TensorProduct A A ↥(P.X (-1)),
      (TensorProduct.lid A ↥(P.X 0)).toLinearMap ((P.d (-1) 0).hom.baseChange A y)
        = (P.d (-1) 0).hom ((TensorProduct.lid A ↥(P.X (-1))).toLinearMap y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [LinearMap.baseChange_tmul]
      calc (TensorProduct.lid A ↥(P.X 0)).toLinearMap (r ⊗ₜ[A] (P.d (-1) 0).hom m)
          = r • (P.d (-1) 0).hom m := TensorProduct.lid_tmul _ r
        _ = (P.d (-1) 0).hom (r • m) := ((P.d (-1) 0).hom.map_smul r m).symm
        _ = (P.d (-1) 0).hom
              ((TensorProduct.lid A ↥(P.X (-1))).toLinearMap (r ⊗ₜ[A] m)) :=
              congrArg (fun z => (P.d (-1) 0).hom z) (TensorProduct.lid_tmul m r).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨(↑hunit.unit⁻¹ : A) •
      ((Ideal.Quotient.mkₐ A (⊥ : Ideal A)).toLinearMap.comp
        (φ₀.hom.comp (TensorProduct.lid A ↥(P.X 0)).toLinearMap)), ?_, ?_⟩
  · intro y
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [hlid y, hkill, map_zero, smul_zero]
  · have h1 : ((TensorProduct.lid A ↥(P.X 0)).toLinearMap ((1 : A) ⊗ₜ[A] (ε.hom 1)))
        = ε.hom 1 := (TensorProduct.lid_tmul (ε.hom 1) (1 : A)).trans (one_smul A (ε.hom 1))
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.mkₐ_eq_mk]
    rw [h1, hval, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      hunit.val_inv_mul]

/-- **Nonzero integers are units** of a local ring whose residue field has characteristic zero:
the composite `ℤ → A → ResidueField A` is injective, so `n ≠ 0` gives `n ∉ 𝔪` and `n` is a unit.

This is the arithmetic input of the trace argument in the form in which it is produced by the
supertrace: the value of the trace functional at the coaugmentation class is the *Euler
characteristic* `Σᵢ (-1)ⁱ rk (Pⁱ)`, an integer, not a natural number. -/
theorem isUnit_intCast_of_charZero_residueField {A : Type a} [CommRing A] [IsLocalRing A]
    [CharZero (IsLocalRing.ResidueField A)] {n : ℤ} (hn : n ≠ 0) : IsUnit ((n : A)) := by
  obtain ⟨m, hm | hm⟩ := n.eq_nat_or_neg
  · have hm0 : m ≠ 0 := by rintro rfl; exact hn hm
    rw [hm]
    push_cast
    exact isUnit_natCast_of_charZero_residueField hm0
  · have hm0 : m ≠ 0 := by rintro rfl; exact hn (by rw [hm]; simp)
    rw [hm]
    push_cast
    exact (isUnit_natCast_of_charZero_residueField hm0).neg

/-- **The honest splitting from an integer-valued functional.**  Same as
`Work.DSEQ0.modSplit_of_functional`, with the value of the functional at the coaugmentation class
given as an arbitrary nonzero *integer* `n` (the shape in which the supertrace produces it), and
with the differential-killing condition in pointwise form. -/
theorem modSplit_of_functional_int {A : Type a} [CommRing A] [IsLocalRing A]
    [CharZero (IsLocalRing.ResidueField A)]
    {P : CochainComplex (ModuleCat.{a} A) ℤ} {ε : ModuleCat.of A A ⟶ P.X 0}
    {φ₀ : ↥(P.X 0) →ₗ[A] A} {n : ℤ} (hn : n ≠ 0)
    (hval : φ₀ (ε.hom 1) = (n : A))
    (hker : ∀ y : ↥(P.X (-1)), φ₀ ((P.d (-1) 0).hom y) = 0) :
    DSMap.Mix.ModSplit P ε (RingHom.id A) ⊥ 1 := by
  have hunit : IsUnit ((n : A)) := isUnit_intCast_of_charZero_residueField hn
  have hlid : ∀ y : TensorProduct A A ↥(P.X (-1)),
      (TensorProduct.lid A ↥(P.X 0)).toLinearMap ((P.d (-1) 0).hom.baseChange A y)
        = (P.d (-1) 0).hom ((TensorProduct.lid A ↥(P.X (-1))).toLinearMap y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [LinearMap.baseChange_tmul]
      calc (TensorProduct.lid A ↥(P.X 0)).toLinearMap (r ⊗ₜ[A] (P.d (-1) 0).hom m)
          = r • (P.d (-1) 0).hom m := TensorProduct.lid_tmul _ r
        _ = (P.d (-1) 0).hom (r • m) := ((P.d (-1) 0).hom.map_smul r m).symm
        _ = (P.d (-1) 0).hom
              ((TensorProduct.lid A ↥(P.X (-1))).toLinearMap (r ⊗ₜ[A] m)) :=
              congrArg (fun z => (P.d (-1) 0).hom z) (TensorProduct.lid_tmul m r).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨(↑hunit.unit⁻¹ : A) •
      ((Ideal.Quotient.mkₐ A (⊥ : Ideal A)).toLinearMap.comp
        (φ₀.comp (TensorProduct.lid A ↥(P.X 0)).toLinearMap)), ?_, ?_⟩
  · intro y
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [hlid y, hker]
    simp
  · have h1 : ((TensorProduct.lid A ↥(P.X 0)).toLinearMap ((1 : A) ⊗ₜ[A] (ε.hom 1)))
        = ε.hom 1 := (TensorProduct.lid_tmul (ε.hom 1) (1 : A)).trans (one_smul A (ε.hom 1))
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.mkₐ_eq_mk]
    rw [h1, hval, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      hunit.val_inv_mul]

/-- **Area `EQ0`**: the equal-characteristic-zero case of the derived direct summand theorem,
in the exact form of the frozen statement (the complete regular local `A` with algebraically
closed residue field of characteristic zero, `X` integral, `f` proper, surjective, generically
finite and projective).

The proof is the assembly described in the header: cover, strictly unital finite free model with
its trace functional (`Work.DSEQ0.exists_traceModelFunctional`), rescaling
(`Work.DSEQ0.modSplit_of_functional_int`), and the proved bridge
`DSMap.Mix2.area_MX0bU_of_F1` fed by the proved area `F1` (`DSMap.area_F1_cech_proved`). -/
theorem area_EQ0_proved (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsAlgClosed (IsLocalRing.ResidueField A)]
    [CharZero (IsLocalRing.ResidueField A)] (X : AlgebraicGeometry.Scheme.{a})
    [AlgebraicGeometry.IsIntegral X]
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) [AlgebraicGeometry.IsProper f]
    (hs : Function.Surjective f) (hg : DSMap.IsGenFinite A f) (hp : DSMap.IsProjOver A f) :
    DSMap.DSplit.{a, b, c} A X f := by
  obtain ⟨J, hJ, U, hU, hcov⟩ := Work.DSEQ0.exists_finite_affineCover (A := A) f
  obtain ⟨P, ε, φ₀, n, hn, hP, hker, hval⟩ :=
    Work.DSEQ0.exists_traceModelFunctional A X f hs hg hp U hU hcov
  refine DSMap.Mix2.area_MX0bU_of_F1 A X f U hU hcov P ε hP
    (Work.DSEQ0.modSplit_of_functional_int hn hval hker) ?_
  intro hb hc hEn
  letI := hb
  letI := hc
  letI := hEn
  haveI : QuasiCompact f := Work.DSMX0bU.quasiCompact_of_isProper f
  exact DSMap.area_F1_cech_proved A X f U hU hcov

end Work.DSEQ0
