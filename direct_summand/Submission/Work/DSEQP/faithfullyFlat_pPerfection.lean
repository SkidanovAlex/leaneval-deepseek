/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `A → A^{1/p^∞}` is faithfully flat when Frobenius is flat

This is the easy direction of Kunz's theorem, in the form needed by the equal characteristic `p`
route to the direct summand theorem (see `Work.DSEQP.AffineCharP`): if `A` is a domain of
characteristic `p` whose Frobenius endomorphism `x ↦ x ^ p` is flat, then the `p`-perfection
`A^{1/p^∞}` (`Work.DSEQP.pPerfection`, the filtered colimit of `A --F--> A --F--> ⋯`) is a
faithfully flat `A`-algebra.

The pieces of the argument:

* `A^{1/p^∞}` is the filtered colimit of the modules `A_e` (`e : ℕ`), where `A_e = FrobTwist A p e`
  is `A` regarded as an `A`-algebra via `a ↦ a ^ p ^ e` (the `e`-th *Frobenius twist*).  Each `A_e`
  is flat over `A` because `frobenius A p` is flat and flat ring maps are closed under composition.
* A directed colimit of flat modules is flat: this is `Work.DSEQP.flat_of_directedCover`, whose
  mathematical input is `Work.DSEQP.exists_directedCover_lTensor` -- every element of `I ⊗[A] M`
  already lives at a single level.
* Faithfulness: `A → A^{1/p^∞}` is injective (`Work.DSEQP.pPerfection_algebraMap_injective`) and
  integral (`Work.DSEQP.pPerfection_isIntegral`), and an integral injective ring map is surjective
  on prime spectra (`Algebra.IsIntegral.comap_surjective`), whence
  `Module.FaithfullyFlat.of_comap_surjective`.
-/
import Mathlib
import Submission.Work.DSEQP.Perfection
import Submission.Work.DSEQP.exists_directedCover_lTensor
import Submission.Work.DSEQP.pPerfection_algebraMap_injective
import Submission.Work.DSEQP.pPerfection_isIntegral

open scoped TensorProduct

namespace Work.DSEQP

universe u

set_option linter.unusedVariables false

/-! ## 1. Flatness of a directed cover of a module

The mathematical heart of the flatness of `A^{1/p^∞}`: an `R`-module `M` covered by a directed
family of flat `R`-modules is flat. -/

section DirectedCover

variable {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
  {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  {M : Type*} [AddCommGroup M] [Module R M]

/-- **Flatness of a directed cover.**  Let `M` be an `R`-module and `g i : G i →ₗ[R] M` a
compatible directed family of `R`-linear maps from flat modules, which covers `M` and is levelwise
injective.  Then `M` is flat.

Indeed, for a finitely generated ideal `I` and `z ∈ I ⊗[R] M` with `i ⊗ m ↦ i • m`-image `0`,
choose a level `j` and `y ∈ I ⊗[R] G j` with `z = (g j).lTensor I y`
(`Work.DSEQP.exists_directedCover_lTensor`).  Then the image of `y` in `G j` is killed by `g j`,
hence is `0` by injectivity, so `y = 0` because `G j` is flat. -/
theorem flat_of_directedCover (g : ∀ i, G i →ₗ[R] M) (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
    (hcompat : ∀ i j (h : i ≤ j) (x : G i), g j (f i j h x) = g i x)
    (hcover : ∀ m : M, ∃ i x, g i x = m)
    (hflat : ∀ i, Module.Flat R (G i))
    (hinj : ∀ i, Function.Injective (g i)) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I hI
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨j, y, hy⟩ := exists_directedCover_lTensor g f hcompat hcover I z
  set μ : TensorProduct R I (G j) →ₗ[R] G j :=
    TensorProduct.lift ((LinearMap.lsmul R (G j)).comp I.subtype) with hμ
  have hfac : (TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)).comp
        (LinearMap.lTensor I (g j)) = (g j).comp μ := by
    apply TensorProduct.ext'
    intro i x
    simp only [LinearMap.comp_apply, TensorProduct.lift.tmul, LinearMap.lsmul_apply,
      Submodule.subtype_apply, LinearMap.lTensor_tmul, hμ]
    rw [map_smul]
  have hflatj : Function.Injective μ :=
    (Module.Flat.iff_lift_lsmul_comp_subtype_injective.mp (hflat j)) hI
  have hzero : μ y = 0 :=
    (injective_iff_map_eq_zero (g j)).mp (hinj j) (μ y) (by
      rw [← LinearMap.comp_apply, ← hfac, LinearMap.comp_apply, hy, hz])
  have hy0 : y = 0 := hflatj (by rw [hzero, map_zero])
  calc z = LinearMap.lTensor I (g j) y := hy.symm
    _ = LinearMap.lTensor I (g j) 0 := by rw [hy0]
    _ = 0 := map_zero _

end DirectedCover

/-! ## 2. The Frobenius twist of `A`

`FrobTwist A p e` is a copy of `A` carrying the `A`-algebra structure `a • x = a ^ p ^ e * x`
(i.e. the structure map is the `e`-th iterate of Frobenius).  It is a *new* type (not a type
synonym) so that different `e` can carry different `A`-module structures simultaneously; the
ring structure is transported from `A` along the obvious equivalence, so that the underlying
element `FrobTwist.val` is a ring homomorphism onto `A` and the flatness of `A_e` reduces to the
flatness of the *ring map* `frobPowHom A p e`. -/

/-- The `e`-th **Frobenius twist** of a commutative ring `A`: a copy of `A`, regarded as an
`A`-algebra via `a ↦ a ^ p ^ e`. -/
@[ext]
structure FrobTwist (A : Type u) (p e : ℕ) where
  /-- The underlying element of `A`. -/
  val : A

namespace FrobTwist

variable {A : Type*} [CommRing A] {p : ℕ} [Fact p.Prime] [CharP A p]

/-- The underlying element is a bijection onto `A`. -/
def equiv (e : ℕ) : FrobTwist A p e ≃ A where
  toFun x := x.val
  invFun a := ⟨a⟩
  left_inv x := by ext; rfl
  right_inv _ := rfl

noncomputable instance instCommRing (e : ℕ) : CommRing (FrobTwist A p e) := (equiv e).commRing

@[simp] lemma val_zero (e : ℕ) : (0 : FrobTwist A p e).val = 0 := rfl
@[simp] lemma val_one (e : ℕ) : (1 : FrobTwist A p e).val = 1 := rfl
@[simp] lemma val_add (e : ℕ) (x y : FrobTwist A p e) : (x + y).val = x.val + y.val := rfl
@[simp] lemma val_mul (e : ℕ) (x y : FrobTwist A p e) : (x * y).val = x.val * y.val := rfl
@[simp] lemma val_neg (e : ℕ) (x : FrobTwist A p e) : (-x).val = -x.val := rfl
@[simp] lemma val_sub (e : ℕ) (x y : FrobTwist A p e) : (x - y).val = x.val - y.val := rfl
@[simp] lemma val_pow (e : ℕ) (x : FrobTwist A p e) (n : ℕ) : (x ^ n).val = x.val ^ n := rfl
@[simp] lemma val_natCast (e : ℕ) (n : ℕ) : (n : FrobTwist A p e).val = n := rfl

lemma val_injective (e : ℕ) : Function.Injective (fun x : FrobTwist A p e => x.val) :=
  fun _ _ h => FrobTwist.ext h

/-- The `n`-th Frobenius power on elements: `x ↦ x ^ p ^ n`. -/
lemma frobPowHom_apply (n : ℕ) : ∀ a : A, frobPowHom A p n a = a ^ p ^ n := by
  intro a
  induction n generalizing a with
  | zero => rw [pow_zero, pow_one]; rfl
  | succ n ih =>
    have h : frobPowHom A p (n + 1) = (frobPowHom A p n).comp (frobenius A p) := by
      rw [frobPowHom, pow_succ, RingHom.mul_def]
      rfl
    rw [h, RingHom.comp_apply, frobenius_def, pow_succ', pow_mul, ← ih (a ^ p)]

/-- Composition of Frobenius powers. -/
lemma frobPowHom_comp (m n : ℕ) (a : A) :
    frobPowHom A p m (frobPowHom A p n a) = frobPowHom A p (m + n) a := by
  rw [frobPowHom_apply m, frobPowHom_apply n, frobPowHom_apply (m + n), ← pow_mul, ← pow_add,
    Nat.add_comm]

/-- Iterates of the Frobenius are flat ring maps. -/
lemma frobPowHom_flat (h : (frobenius A p).Flat) (n : ℕ) : (frobPowHom A p n).Flat := by
  induction n with
  | zero => rw [frobPowHom, pow_zero]; exact RingHom.Flat.id A
  | succ n ih => rw [frobPowHom, pow_succ', RingHom.mul_def]; exact RingHom.Flat.comp ih h

/-- The "underlying element" ring homomorphism `A → A_e`, which is a bijection. -/
noncomputable def up (e : ℕ) : A →+* FrobTwist A p e where
  toFun a := ⟨a⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

lemma bijective_up (e : ℕ) : Function.Bijective ⇑(up (A := A) (p := p) e) :=
  (equiv e).symm.bijective

/-- The structure map `A → A_e` of the Frobenius twist, `a ↦ a ^ p ^ e`. -/
noncomputable def structMap (e : ℕ) : A →+* FrobTwist A p e :=
  (up (p := p) e).comp (frobPowHom A p e)

noncomputable instance instAlgebra (e : ℕ) : Algebra A (FrobTwist A p e) :=
  (structMap (p := p) e).toAlgebra

@[simp] lemma val_algebraMap (e : ℕ) (a : A) :
    (algebraMap A (FrobTwist A p e) a).val = frobPowHom A p e a := by
  rw [RingHom.algebraMap_toAlgebra]
  rfl

@[simp] lemma val_smul (e : ℕ) (a : A) (x : FrobTwist A p e) :
    (a • x).val = frobPowHom A p e a * x.val := by
  rw [Algebra.smul_def, val_mul, val_algebraMap]

/-- The `e`-th Frobenius twist of `A` is flat over `A` when `frobenius A p` is flat: the
structure map `A → A_e` is `frobPowHom A p e = F ^ e` followed by a bijection, and a composition
of flat ring maps is flat. -/
theorem flat_of_frobPowHom (h : (frobenius A p).Flat) (e : ℕ) :
    Module.Flat A (FrobTwist A p e) :=
  (RingHom.Flat.comp (frobPowHom_flat h e) (RingHom.Flat.of_bijective (bijective_up e)) :
    (structMap (p := p) e).Flat)

/-- The transition map of the Frobenius tower: `A_e → A_{e'}`, `x ↦ x ^ p ^ (e' - e)`. -/
noncomputable def tr (e e' : ℕ) (h : e ≤ e') : FrobTwist A p e →ₗ[A] FrobTwist A p e' where
  toFun x := ⟨frobPowHom A p (e' - e) x.val⟩
  map_add' x y := by
    apply val_injective e'
    show frobPowHom A p (e' - e) (x.val + y.val)
      = frobPowHom A p (e' - e) x.val + frobPowHom A p (e' - e) y.val
    rw [map_add]
  map_smul' a x := by
    apply val_injective e'
    show frobPowHom A p (e' - e) (frobPowHom A p e a * x.val)
      = frobPowHom A p e' a * frobPowHom A p (e' - e) x.val
    rw [map_mul, frobPowHom_comp, Nat.sub_add_cancel h]

@[simp] lemma tr_apply (e e' : ℕ) (h : e ≤ e') (x : FrobTwist A p e) :
    (tr e e' h x).val = frobPowHom A p (e' - e) x.val := rfl

end FrobTwist

/-- The structure map of the perfection is the level-`0` inclusion. -/
lemma pPerfection_algebraMap_eq_of_zero (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime]
    [CharP A p] :
    algebraMap A (pPerfection A p) = pPerfection.of (A := A) (p := p) 0 := by
  rw [show pPerfection.of (A := A) (p := p) 0 = pPerfection.algebraMap' (A := A) (p := p)
    from rfl]
  exact RingHom.algebraMap_toAlgebra _

/-- The level-`e` structure map `A^{1/p^e} → A^{1/p^∞}` as an `A`-linear map. -/
noncomputable def FrobTwist.ofLin (A : Type u) [CommRing A] (p e : ℕ) [Fact p.Prime]
    [CharP A p] : FrobTwist A p e →ₗ[A] pPerfection A p where
  toFun x := pPerfection.of (A := A) (p := p) e x.val
  map_add' x y := by rw [FrobTwist.val_add, map_add]
  map_smul' a x := by
    rw [FrobTwist.val_smul, map_mul, Algebra.smul_def, pPerfection_algebraMap_eq_of_zero]
    congr 1
    simpa using pPerfection.of_f (A := A) (p := p) (i := 0) (j := e) (Nat.zero_le e) a

/-! ## 3. Flatness of the perfection -/

/-- `A → A^{1/p^∞}` is flat when `frobenius A p` is flat: the perfection is the directed colimit
of the flat modules `FrobTwist A p e`, and `flat_of_directedCover` says that such a colimit is
flat. -/
theorem pPerfection_flat (A : Type u) [CommRing A] [IsDomain A] (p : ℕ) [Fact p.Prime]
    [CharP A p] (h : (frobenius A p).Flat) : Module.Flat A (pPerfection A p) := by
  refine flat_of_directedCover (R := A) (ι := ℕ) (G := fun e => FrobTwist A p e)
    (M := pPerfection A p) (fun e => FrobTwist.ofLin A p e) (fun e e' h => FrobTwist.tr e e' h)
    ?_ ?_ ?_ ?_
  · -- compatibility of the structure maps with the transition maps
    intro e e' hee' x
    show pPerfection.of (A := A) (p := p) e' ((FrobTwist.tr e e' hee' x).val)
      = pPerfection.of (A := A) (p := p) e x.val
    rw [FrobTwist.tr_apply]
    exact pPerfection.of_f (A := A) (p := p) hee' x.val
  · -- every element of the perfection lies at some level
    intro m
    obtain ⟨e, a, ha⟩ := Ring.DirectLimit.exists_of (G := fun _ : ℕ => A)
      (f := fun i j (_ : i ≤ j) => ⇑(frobPowHom A p (j - i))) m
    exact ⟨e, ⟨a⟩, by rw [← ha]; rfl⟩
  · -- each level is flat
    intro e
    exact FrobTwist.flat_of_frobPowHom h e
  · -- each structure map is injective
    intro e x y hxy
    have hxy' : pPerfection.of (A := A) (p := p) e x.val
        = pPerfection.of (A := A) (p := p) e y.val := hxy
    have h0 := congrArg (fun z => z ^ (p ^ e)) hxy'
    rw [pPerfection.of_pow_pow, pPerfection.of_pow_pow] at h0
    have h1 : x.val = y.val :=
      pPerfection_algebraMap_injective A p (by
        have : algebraMap A (pPerfection A p) x.val
            = algebraMap A (pPerfection A p) y.val := by
          simpa [pPerfection_algebraMap_eq_of_zero] using h0
        exact this)
    exact FrobTwist.ext h1

/-! ## 4. Main theorem -/

/-- **Kunz's easy direction.**  If `A` is a domain of characteristic `p` whose Frobenius is flat,
then the perfection `A → A^{1/p^∞}` is faithfully flat. -/
theorem faithfullyFlat_pPerfection (A : Type*) [CommRing A] [IsDomain A] (p : ℕ)
    [Fact p.Prime] [CharP A p] (h : (frobenius A p).Flat) :
    Module.FaithfullyFlat A (pPerfection A p) := by
  haveI hflat : Module.Flat A (pPerfection A p) := pPerfection_flat A p h
  haveI hint : Algebra.IsIntegral A (pPerfection A p) := pPerfection_isIntegral A p
  haveI hfs : FaithfulSMul A (pPerfection A p) :=
    (faithfulSMul_iff_algebraMap_injective A (pPerfection A p)).mpr
      (pPerfection_algebraMap_injective A p)
  exact Module.FaithfullyFlat.of_comap_surjective
    (Algebra.IsIntegral.comap_surjective A (pPerfection A p))

end Work.DSEQP
