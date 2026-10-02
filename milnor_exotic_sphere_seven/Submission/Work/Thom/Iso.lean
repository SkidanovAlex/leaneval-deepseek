import Mathlib
import Submission.Work.Thom.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Isomorphisms of vector bundles (gluing-data model)

`Submission/Work/TangentClasses/Bundle.lean` promises a notion of *isomorphism of bundles* ("a
caller can state identifications such as `TX` restricted to the disc bundle is `π^*(TS⁴ ⊕ ξ)`")
but never defines one.  This module supplies it.

An isomorphism between two gluing data `Z` (fibre `F`, cover `ι`) and `Z'` (fibre `F'`, cover
`ι'`) over a common base `B` is:

* a family of `𝕜`-linear maps `hom b : Z.Fiber b →ₗ[𝕜] Z'.Fiber b` (i.e. `F →ₗ[𝕜] F'`) together
  with a two-sided inverse family `inv b`;
* whose induced maps of **total spaces** `p ↦ ⟨p.1, hom p.1 p.2⟩` are continuous.

Nothing else is needed: the induced maps of total spaces are automatically over `B`
(`(toTotalSpace e p).1 = p.1` is `rfl`), and being mutually inverse on fibres they are mutually
inverse on total spaces.

## What is here

* `Work.Thom.BundleIso` — the notion, with `refl`, `symm`, `trans`, `ofEq` and the induced maps
  `toTotalSpace`, `invTotalSpace`, `toHomeomorph` of total spaces;
* the induced homeomorphism of the punctured total spaces and the induced isomorphism of the
  relative cohomology of the **Thom pairs** `(E, E∖0)`, which live in the companion module
  `Submission/Work/Thom/IsoPunct.lean` (`Work.Thom.BundleIso.punctHomeomorph`,
  `Work.Thom.BundleIso.relCohMap_bijective`), together with the pullback
  `Work.Thom.BundleIso.comap` of an isomorphism along a continuous map of bases (needs the
  field-general total-space continuity lemma of that module).

## Why it matters

Isomorphism-invariance of the characteristic classes of this chapter is the missing tool for
*stability* `c(E ⊕ ε) = c(E)` (and hence for the Whitney formula `p(E ⊕ F) = p(E)p(F)`, the
splitting principle): it is what allows one to identify the Chern classes of the tautological
quotient `Q_V` of `V = E ⊕ ε` on the locus `{u ≠ 0}` with those of `π^*E`.  See `README.md`
ADDENDUM 23 for the exact remaining content and for the two routes that make it work.
-/

open Work.TangentClasses

namespace Work.Thom

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B : Type*} [TopologicalSpace B]
variable {F F' F'' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [NormedAddCommGroup F''] [NormedSpace 𝕜 F'']
variable {ι ι' ι'' : Type*}

/-- **An isomorphism of two vector bundles over a common base.**  It is a fibrewise linear
two-sided inverse pair whose induced maps of total spaces are continuous (continuity alone does not
determine the fibrewise maps, since the fibres are all equal to the model fibre, so it is part of
the data). -/
structure BundleIso (Z : VectorBundleCore 𝕜 B F ι) (Z' : VectorBundleCore 𝕜 B F' ι') where
  /-- the fibrewise linear map `Z.Fiber b →ₗ[𝕜] Z'.Fiber b` -/
  hom : ∀ b : B, Z.Fiber b →ₗ[𝕜] Z'.Fiber b
  /-- its fibrewise inverse -/
  inv : ∀ b : B, Z'.Fiber b →ₗ[𝕜] Z.Fiber b
  left_inv : ∀ b (x : Z.Fiber b), inv b (hom b x) = x
  right_inv : ∀ b (y : Z'.Fiber b), hom b (inv b y) = y
  continuous_hom : Continuous fun p : Z.TotalSpace => (⟨p.1, hom p.1 p.2⟩ : Z'.TotalSpace)
  continuous_inv : Continuous fun p : Z'.TotalSpace => (⟨p.1, inv p.1 p.2⟩ : Z.TotalSpace)

namespace BundleIso

variable {Z : VectorBundleCore 𝕜 B F ι} {Z' : VectorBundleCore 𝕜 B F' ι'}
  {Z'' : VectorBundleCore 𝕜 B F'' ι''}

/-! ## The induced maps of total spaces -/

/-- The map of total spaces induced by a bundle isomorphism. -/
def toTotalSpace (e : BundleIso Z Z') : Z.TotalSpace → Z'.TotalSpace :=
  fun p => ⟨p.1, e.hom p.1 p.2⟩

/-- The map of total spaces induced by the inverse of a bundle isomorphism. -/
def invTotalSpace (e : BundleIso Z Z') : Z'.TotalSpace → Z.TotalSpace :=
  fun p => ⟨p.1, e.inv p.1 p.2⟩

@[simp] theorem toTotalSpace_apply (e : BundleIso Z Z') (p : Z.TotalSpace) :
    e.toTotalSpace p = ⟨p.1, e.hom p.1 p.2⟩ := rfl

@[simp] theorem invTotalSpace_apply (e : BundleIso Z Z') (p : Z'.TotalSpace) :
    e.invTotalSpace p = ⟨p.1, e.inv p.1 p.2⟩ := rfl

/-- **The induced map of total spaces lies over the base.** -/
@[simp] theorem toTotalSpace_proj (e : BundleIso Z Z') (p : Z.TotalSpace) :
    (e.toTotalSpace p).1 = p.1 := rfl

@[simp] theorem invTotalSpace_proj (e : BundleIso Z Z') (p : Z'.TotalSpace) :
    (e.invTotalSpace p).1 = p.1 := rfl

theorem toTotalSpace_left_inv (e : BundleIso Z Z') (p : Z.TotalSpace) :
    e.invTotalSpace (e.toTotalSpace p) = p := by
  show (⟨p.1, e.inv p.1 (e.hom p.1 p.2)⟩ : Z.TotalSpace) = p
  rw [e.left_inv p.1 p.2]

theorem toTotalSpace_right_inv (e : BundleIso Z Z') (p : Z'.TotalSpace) :
    e.toTotalSpace (e.invTotalSpace p) = p := by
  show (⟨p.1, e.hom p.1 (e.inv p.1 p.2)⟩ : Z'.TotalSpace) = p
  rw [e.right_inv p.1 p.2]

/-- A bundle isomorphism is in particular a homeomorphism of total spaces. -/
def toHomeomorph (e : BundleIso Z Z') : Z.TotalSpace ≃ₜ Z'.TotalSpace where
  toFun := e.toTotalSpace
  invFun := e.invTotalSpace
  left_inv := e.toTotalSpace_left_inv
  right_inv := e.toTotalSpace_right_inv
  continuous_toFun := e.continuous_hom
  continuous_invFun := e.continuous_inv

@[simp] theorem toHomeomorph_apply (e : BundleIso Z Z') (p : Z.TotalSpace) :
    e.toHomeomorph p = e.toTotalSpace p := rfl

/-- The zero section is preserved, as is the punctured total space. -/
theorem hom_zero (e : BundleIso Z Z') (b : B) : e.hom b 0 = 0 := map_zero _

theorem hom_ne_zero (e : BundleIso Z Z') {b : B} {x : Z.Fiber b} (hx : x ≠ 0) :
    e.hom b x ≠ 0 := fun h => hx (by
      have := congrArg (e.inv b) h
      rwa [e.left_inv b x, map_zero] at this)

/-! ## The groupoid structure -/

/-- The identity isomorphism. -/
@[refl]
def refl (Z : VectorBundleCore 𝕜 B F ι) : BundleIso Z Z where
  hom _ := LinearMap.id
  inv _ := LinearMap.id
  left_inv _ _ := rfl
  right_inv _ _ := rfl
  continuous_hom := continuous_id
  continuous_inv := continuous_id

@[simp] theorem refl_hom (Z : VectorBundleCore 𝕜 B F ι) (b : B) : (refl Z).hom b = LinearMap.id :=
  rfl

/-- The inverse of an isomorphism. -/
@[symm]
def symm (e : BundleIso Z Z') : BundleIso Z' Z where
  hom := e.inv
  inv := e.hom
  left_inv := e.right_inv
  right_inv := e.left_inv
  continuous_hom := e.continuous_inv
  continuous_inv := e.continuous_hom

/-- The composite of two isomorphisms. -/
def trans (e : BundleIso Z Z') (e' : BundleIso Z' Z'') : BundleIso Z Z'' where
  hom b := (e'.hom b).comp (e.hom b)
  inv b := (e.inv b).comp (e'.inv b)
  left_inv b x := by
    simp only [LinearMap.comp_apply]
    rw [e'.left_inv, e.left_inv]
  right_inv b y := by
    simp only [LinearMap.comp_apply]
    rw [e.right_inv, e'.right_inv]
  continuous_hom := e'.continuous_hom.comp e.continuous_hom
  continuous_inv := e.continuous_inv.comp e'.continuous_inv

@[simp] theorem trans_hom (e : BundleIso Z Z') (e' : BundleIso Z' Z'') (b : B) :
    (e.trans e').hom b = (e'.hom b).comp (e.hom b) := rfl

/-- Isomorphic bundles in the sense of an equality of gluing data. -/
def ofEq {Z Z' : VectorBundleCore 𝕜 B F ι} (h : Z = Z') : BundleIso Z Z' :=
  h ▸ refl Z

end BundleIso

end

end Work.Thom
