import Mathlib
import Submission.Work.SSGRoute.homCoindDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The seam `Ω → M` on units, and the coefficient change it induces

The localisation comparison square `(★')` of `PT/NOTE_e1a_square_session10.md` compares the
*global* `E1c` dictionary over `Ω` with the *local* one over `M = localClosureAt k A hA`.  The
bridge between the two coefficient fields is the **seam**

    seam y = e (coInAdjoin y)        (`e = NK.Mine.adjoinSepEquiv`, see `exists_localField_place_data`)

which is a ring hom `Ω →+* M` whose `D_A`-equivariance is
`Work.SSGRoute.localGaloisEquiv_coInAdjoin_compat_general`, and whose compatibility on `K` (the
pointwise identity of the two embeddings `K → M`) is the `hψ` clause of
`Work.SSGRoute.PT.exists_localField_place_data`.

This file records, in a form independent of the (heavy) local-data plumbing, the two purely formal
consequences of those two facts that the assembly of `(★')` consumes:

* `unitsAddMap` — the additive map `Ωˣ →+ Mˣ` induced by the seam, with its compatibility with the
  Galois actions (`unitsAddMap_equivariant`, from the pointwise identity of the two embeddings) —
  this is the `hψ`-facing value comparison of `(★')`'s ingredient (ii);
* `homComp` — the induced coefficient change `Hom_ℤ(V, Ωˣ) →+ Hom_ℤ(V, Mˣ)`, which is the map on
  the coefficients of the `E1c` resolution (its `mapH0`/`mapH1` are the `Ξ₀`/`Ξ` of the note §1).
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.PT

open scoped Classical

noncomputable section

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
  {M : Type} [Field M] [Algebra k M]

/-- **The seam on units.**  A ring hom `e : Ω →+* M` induces an additive homomorphism
`Ωˣ →+ Mˣ`. -/
def unitsAddMap (e : Ω →+* M) : Additive Ωˣ →+ Additive Mˣ :=
  (Units.map e.toMonoidHom).toAdditive

@[simp] theorem unitsAddMap_apply (e : Ω →+* M) (u : Additive Ωˣ) :
    unitsAddMap e u = Additive.ofMul (Units.map e.toMonoidHom (Additive.toMul u)) := rfl

theorem unitsAddMap_toMul (e : Ω →+* M) (u : Additive Ωˣ) :
    Additive.toMul (unitsAddMap e u) = Units.map e.toMonoidHom (Additive.toMul u) := rfl

/-- **The `hψ`-facing value comparison.**  If the two embeddings `e : Ω → M` and
`γ : Ω ≃ₐ[k] Ω`, `η : M ≃ₐ[k] M` agree pointwise (`η (e y) = e (γ y)` — the content of `hψ`
pushed through the Galois actions), then the induced maps on units are equivariant:

  `unitsAddMap e (γ • u) = η • unitsAddMap e u`. -/
theorem unitsAddMap_equivariant (e : Ω →+* M) (γ : Ω ≃ₐ[k] Ω) (η : M ≃ₐ[k] M)
    (h : ∀ y : Ω, η (e y) = e (γ y)) (u : Additive Ωˣ) :
    unitsAddMap e (Additive.ofMul (Work.SSGRoute.algEquivUnitsMapΩ k Ω γ (Additive.toMul u)))
      = Additive.ofMul (Work.SSGRoute.algEquivUnitsMapΩ k M η
          (Additive.toMul (unitsAddMap e u))) := by
  have key : (Units.map e.toMonoidHom)
        (Work.SSGRoute.algEquivUnitsMapΩ k Ω γ (Additive.toMul u))
      = Work.SSGRoute.algEquivUnitsMapΩ k M η
          (Units.map e.toMonoidHom (Additive.toMul u)) := by
    refine Units.ext ?_
    simp only [Units.coe_map, MonoidHom.coe_coe, Work.SSGRoute.algEquivUnitsMapΩ_coe]
    exact (h ((Additive.toMul u : Ωˣ) : Ω)).symm
  rw [unitsAddMap_apply]
  show Additive.ofMul ((Units.map e.toMonoidHom)
      (Work.SSGRoute.algEquivUnitsMapΩ k Ω γ (Additive.toMul u)))
    = Additive.ofMul ((Work.SSGRoute.algEquivUnitsMapΩ k M η)
        (Additive.toMul (unitsAddMap e u)))
  rw [key, unitsAddMap_toMul]

/-- **The coefficient change of the `E1c` resolution.**  Postcomposition with the seam turns the
coefficient module `Hom_ℤ(V, Ωˣ)` of the dualised canonical resolution into `Hom_ℤ(V, Mˣ)`. -/
def homComp (e : Ω →+* M) (V : Type) [AddCommGroup V] :
    (V →+ Additive Ωˣ) →+ (V →+ Additive Mˣ) :=
  AddMonoidHom.compHom (unitsAddMap e)

theorem homComp_apply (e : Ω →+* M) (V : Type) [AddCommGroup V]
    (φ : V →+ Additive Ωˣ) :
    homComp e V φ = (unitsAddMap e).comp φ := rfl

theorem homComp_apply_apply (e : Ω →+* M) (V : Type) [AddCommGroup V]
    (φ : V →+ Additive Ωˣ) (v : V) :
    homComp e V φ v = unitsAddMap e (φ v) := rfl

/-! ### The conjugation action and the `hΨ`-equivariance of the coefficient change

`AbsoluteKummer.mapH0`/`mapH1` and `Work.SSGRoute.PT.h1TransferAddHom` all take their coefficient
map together with an *equivariance* proof `hΨ`.  For the coefficient change `homComp e V` the
relevant actions are the conjugation actions: a group element acts on `Ωˣ` (resp. `Mˣ`) through its
automorphism of the field and on `V` through the action `τ` of the same element.  The
`hΨ`-equivariance is then *exactly* `unitsAddMap_equivariant` above, pointwise. -/

variable {V : Type} [AddCommGroup V]

/-- **The conjugation action** of `(γ, τ)` on `Hom_ℤ(V, Ωˣ)`: `γ` acts on the target `Ωˣ` and
`τ : V ≃+ V` is the action of the same group element on the source. -/
def conjHom (γ : Ω ≃ₐ[k] Ω) (τ : V ≃+ V) (φ : V →+ Additive Ωˣ) : V →+ Additive Ωˣ where
  toFun v := Additive.ofMul
    (Work.SSGRoute.algEquivUnitsMapΩ k Ω γ (Additive.toMul (φ (τ.symm v))))
  map_zero' := by
    show Additive.ofMul
      (Work.SSGRoute.algEquivUnitsMapΩ k Ω γ (Additive.toMul (φ (τ.symm 0)))) = 0
    simp
  map_add' v w := by
    show Additive.ofMul
        (Work.SSGRoute.algEquivUnitsMapΩ k Ω γ (Additive.toMul (φ (τ.symm (v + w)))))
      = Additive.ofMul
          (Work.SSGRoute.algEquivUnitsMapΩ k Ω γ (Additive.toMul (φ (τ.symm v))))
        + Additive.ofMul
          (Work.SSGRoute.algEquivUnitsMapΩ k Ω γ (Additive.toMul (φ (τ.symm w))))
    rw [map_add (τ.symm) v w, map_add]
    rw [show Additive.toMul (φ (τ.symm v) + φ (τ.symm w))
        = Additive.toMul (φ (τ.symm v)) * Additive.toMul (φ (τ.symm w)) from rfl,
      map_mul]
    rfl

@[simp] theorem conjHom_apply (γ : Ω ≃ₐ[k] Ω) (τ : V ≃+ V) (φ : V →+ Additive Ωˣ) (v : V) :
    conjHom γ τ φ v = Additive.ofMul
      (Work.SSGRoute.algEquivUnitsMapΩ k Ω γ (Additive.toMul (φ (τ.symm v)))) := rfl

/-- **The `hΨ`-equivariance of the coefficient change `homComp e V`.**  If the two embeddings agree
pointwise (`η (e y) = e (γ y)`, i.e. the `K`-part of `hψ` pushed through the Galois actions), then
the coefficient change intertwines the two conjugation actions:

  `conjHom η τ (homComp e V φ) = homComp e V (conjHom γ τ φ)`. -/
theorem homComp_conjHom (e : Ω →+* M) (γ : Ω ≃ₐ[k] Ω) (η : M ≃ₐ[k] M)
    (h : ∀ y : Ω, η (e y) = e (γ y)) (τ : V ≃+ V) (φ : V →+ Additive Ωˣ) :
    conjHom (Ω := M) η τ (homComp e V φ)
      = homComp e V (conjHom (Ω := Ω) γ τ φ) := by
  refine AddMonoidHom.ext fun v => ?_
  show Additive.ofMul (Work.SSGRoute.algEquivUnitsMapΩ k M η
        (Additive.toMul (homComp e V φ (τ.symm v))))
    = unitsAddMap e (Additive.ofMul (Work.SSGRoute.algEquivUnitsMapΩ k Ω γ
        (Additive.toMul (φ (τ.symm v)))))
  rw [unitsAddMap_apply, homComp_apply_apply]
  exact (unitsAddMap_equivariant e γ η h (φ (τ.symm v))).symm

end

end Work.SSGRoute.PT
