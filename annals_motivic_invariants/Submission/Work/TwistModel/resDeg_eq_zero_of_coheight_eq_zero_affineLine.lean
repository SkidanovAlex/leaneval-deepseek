import Mathlib
import Submission.Work.Arithmetic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The residue degree at a point of coheight zero on the affine line

We prove `Work.TwistModel.resDeg_eq_zero_of_coheight_eq_zero_affineLine`: on
`Spec 𝕜[X]` with `𝕜` a field, every point `x` with `Order.coheight x = 0` has
`Work.Arithmetic.resDeg 𝕜 x = 0`.  Since `Spec 𝕜[X]` is irreducible, such a point
is the generic point `⊥`, where the structure map `𝕜 → κ(x)` factors through the
domain `𝕜[X]`, so that `κ(x)` contains an infinite `𝕜`-linearly independent family
(the images of `1, X, X², …`) and hence has `Module.finrank` zero.

The two supporting lemmas are the affine computation of the structure map
`Work.Arithmetic.resMap 𝕜 x : 𝕜 →+* κ(x)` of `Spec R` over `Spec 𝕜`, and the
pointwise naturality of `Scheme.ΓSpecIso` on global sections which it rests on.
-/

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.TwistModel

noncomputable section

open CategoryTheory AlgebraicGeometry Scheme Order

/-- **Naturality of `ΓSpecIso` on global sections, pointwise form.**  For a ring homomorphism
`φ : A ⟶ B` of commutative rings, the induced map on global sections of `Spec`, evaluated on
`(ΓSpecIso A).inv a`, is `(ΓSpecIso B).inv (φ a)`. -/
lemma spec_appTop_ΓSpecIso_inv {A B : CommRingCat} (φ : A ⟶ B) (a : A) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv a) = (Scheme.ΓSpecIso B).inv (φ a) := by
  have h := congrArg (fun (f : A ⟶ Γ(Spec B, ⊤)) => f.hom a)
    (Scheme.ΓSpecIso_inv_naturality φ)
  exact h.symm

/-- **`resMap` on an affine chart.**  For `Spec R` over `Spec 𝕜` given by the algebra structure
`𝕜 → R`, the structure map `resMap 𝕜 (Spec R) p : 𝕜 →+* κ(p)` is the composite of the
canonical map `Spec.residueFieldIso R p : κ(p) ≅ p.asIdeal.ResidueField` with the algebra map
`𝕜 → R → p.asIdeal.ResidueField`. -/
lemma resMap_spec_eq (𝕜 : Type) [Field 𝕜] (R : Type) [CommRing R] [Algebra 𝕜 R]
    (p : PrimeSpectrum R) :
    Work.Arithmetic.resMap 𝕜 (X := Spec (CommRingCat.of R)) p =
      ((Spec.residueFieldIso (CommRingCat.of R) p).inv.hom).comp
        ((algebraMap R p.asIdeal.ResidueField).comp (algebraMap 𝕜 R)) := by
  have hhom : (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of 𝕜)) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝕜 R)) := specOverSpec_over
  ext a
  simp only [Work.Arithmetic.resMap, hhom, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [spec_appTop_ΓSpecIso_inv (CommRingCat.ofHom (algebraMap 𝕜 R)) a]
  exact (congrArg (fun (f : CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).residueField p) =>
    f.hom (algebraMap 𝕜 R a)) (Spec.algebraMap_residueFieldIso_inv (CommRingCat.of R) p)).symm

/-- **The residue degree at a point of coheight zero on `Spec 𝕜[X]` is zero.**

`Order.coheight x = 0` on a scheme means that `x` is the *generic point of an irreducible
component*, and **not** that `x` is closed: the scheme carries the specialisation preorder
(`AlgebraicGeometry.Scheme.le_iff_specializes`), under which a closed point is a *minimal*
element (`AlgebraicGeometry.Scheme.height_of_isClosed`) and `Order.coheight_eq_zero` reads
`IsMax x`.  Equivalently, `Order.coheight x = x.asIdeal.height` for `x : Spec R`
(`AlgebraicGeometry.idealHeight_eq_coheight`), i.e. `coheight x = ringKrullDim (stalk x)`
(`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`).  So for `Spec 𝕜[X]` with `𝕜` a field,
`Order.coheight x = 0` means `x.asIdeal = ⊥` (the generic point), where the residue field is
the rational function field `𝕜(X)`: there `1, X, X², …` are `𝕜`-linearly independent, so the
residue field is infinite-dimensional over `𝕜` and `Module.finrank` — hence
`Work.Arithmetic.resDeg`, which is `Module.finrank 𝕜 (κ x)` — vanishes
(`Cardinal.toNat_eq_zero`). -/
theorem resDeg_eq_zero_of_coheight_eq_zero_affineLine (𝕜 : Type) [Field 𝕜]
    (x : AlgebraicGeometry.Spec (CommRingCat.of (Polynomial 𝕜)))
    (hx : Order.coheight x = 0) :
    Work.Arithmetic.resDeg 𝕜 x = 0 := by
  -- On the irreducible scheme `Spec 𝕜[X]`, the points of coheight zero are the points of
  -- maximal `Ideal.height`; these are the minimal primes, so `x.asIdeal = ⊥`.
  haveI : x.asIdeal.IsPrime := x.isPrime
  have hbot : x.asIdeal = ⊥ := by
    have hA : x.asIdeal.height = 0 :=
      (idealHeight_eq_coheight (CommRingCat.of (Polynomial 𝕜)) x).trans hx
    let z : PrimeSpectrum (Polynomial 𝕜) := ⟨x.asIdeal, x.isPrime⟩
    have hH : Order.height z = 0 := by
      rw [← PrimeSpectrum.height_eq_orderHeight z]
      exact hA
    have hmin : IsMin z := Order.height_eq_zero.mp hH
    have hyx : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Polynomial 𝕜)) ≤ z := by
      rw [← PrimeSpectrum.asIdeal_le_asIdeal]
      exact bot_le
    have hxy : z ≤ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Polynomial 𝕜)) := hmin hyx
    have hle : z.asIdeal ≤ (⊥ : Ideal (Polynomial 𝕜)) :=
      (PrimeSpectrum.asIdeal_le_asIdeal z ⟨⊥, Ideal.isPrime_bot⟩).mp hxy
    have hzb : z.asIdeal = ⊥ := le_bot_iff.mp hle
    simpa using hzb
  -- The structure map `𝕜 →+* κ(x)` factors through the domain `𝕜[X]`.
  set φ : Polynomial 𝕜 →+* (Spec (CommRingCat.of (Polynomial 𝕜))).residueField x :=
    ((Spec.residueFieldIso (CommRingCat.of (Polynomial 𝕜)) x).inv.hom).comp
      (algebraMap (Polynomial 𝕜) x.asIdeal.ResidueField) with hφ
  have hres : Work.Arithmetic.resMap 𝕜 x = φ.comp (algebraMap 𝕜 (Polynomial 𝕜)) := by
    rw [hφ]
    exact resMap_spec_eq 𝕜 (Polynomial 𝕜) x
  have hinj_alg : Function.Injective (algebraMap (Polynomial 𝕜) x.asIdeal.ResidueField) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    rw [Ideal.algebraMap_residueField_eq_zero] at hz
    rw [hbot] at hz
    simpa using hz
  have hinj_iso : Function.Injective
      ((Spec.residueFieldIso (CommRingCat.of (Polynomial 𝕜)) x).inv.hom) :=
    (ConcreteCategory.bijective_of_isIso
      (Spec.residueFieldIso (CommRingCat.of (Polynomial 𝕜)) x).inv).1
  have hφinj : Function.Injective φ := by
    rw [hφ]
    intro a b hab
    exact hinj_alg (hinj_iso hab)
  -- `resDeg` is the `𝕜`-dimension of `κ(x)` for the algebra structure defined by `resMap`.
  letI : Algebra 𝕜 ((Spec (CommRingCat.of (Polynomial 𝕜))).residueField x) :=
    (Work.Arithmetic.resMap 𝕜 x).toAlgebra
  change Module.finrank 𝕜 ((Spec (CommRingCat.of (Polynomial 𝕜))).residueField x) = 0
  -- The monomials are `𝕜`-linearly independent and the embedding `𝕜[X] ↪ κ(x)` is `𝕜`-linear,
  -- so the images of `1, X, X², …` are `𝕜`-linearly independent in `κ(x)`.
  have hliR : LinearIndependent 𝕜 (fun n : ℕ => (Polynomial.X : Polynomial 𝕜) ^ n) := by
    simpa [Polynomial.X_pow_eq_monomial] using (Polynomial.basisMonomials 𝕜).linearIndependent
  let φL : Polynomial 𝕜 →ₗ[𝕜] (Spec (CommRingCat.of (Polynomial 𝕜))).residueField x :=
    { toFun := φ
      map_add' := fun a b => map_add φ a b
      map_smul' := fun a r => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        rw [RingHom.algebraMap_toAlgebra]
        exact (congrArg (fun f : 𝕜 →+* _ => f a) hres).symm }
  have hli : LinearIndependent 𝕜 (fun n : ℕ => φL ((Polynomial.X : Polynomial 𝕜) ^ n)) :=
    hliR.map' φL (LinearMap.ker_eq_bot_of_injective (f := φL) hφinj)
  exact hli.finrank_eq_zero_of_infinite

end

end Work.TwistModel
