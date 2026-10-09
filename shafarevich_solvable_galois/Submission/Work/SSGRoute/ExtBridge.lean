import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Towards "group cohomology is `Ext`-cohomology": the resolution comparison

`Ext`-cohomology of a group `G` with coefficients in `A : Rep k G` is `Extⁿ_G(k, A)`
(`= Abelian.Ext (trivial k G k) A n`).  Comparing it with Mathlib's `groupCohomology A n` needs,
for each `n`, an additive isomorphism

`groupCohomology A n ≃+ (R.complex.linearYonedaObj k A).homology n`

for a projective resolution `R` of `k`, whose inverse is the "class of a cocycle goes to `extMk`"
map.  This file supplies the technical core of that comparison, in the general form needed:

* `cycHom` and its API: the underlying morphism `R.complex.X n ⟶ Y` of an element of the
  `n`-cycles of `Hom(R_•, Y)`.  This is an `irreducible` definition whose only purpose is to give
  the coercion `↑((R.complex.linearYonedaObj k Y).X n) = (R.complex.X n ⟶ Y)` a name, so that
  tactics which use non-definitional transparency still see a term of the expected type.

* `linearYonedaObj_d_apply`: the differential of `Hom(K_•, Y)` is precomposition with the
  differential of `K` (stated for a general chain complex `K`).  This is the missing link between
  `linearYonedaObj` and `ProjectiveResolution.extMk` (whose hypothesis is
  `R.complex.d (n+1) n ≫ f = 0`).

* `extMk_congr`: `extMk` is insensitive to the proof of the cocycle condition.

The remaining steps of the comparison (an additive map `K.cycles n →+ Ext` given by `cycHom`
followed by `extMk`, descended to `K.homology n` along the cokernel `K.homologyπ n = cokernel of
the boundary map`, using `ProjectiveResolution.extMk_eq_zero_iff` for well-definedness and
`ProjectiveResolution.extMk_surjective` for surjectivity) are assembled from exactly this API; see
`Submission/Work/SSGRoute/EXT_BRIDGE_STATUS.md`.
-/

open CategoryTheory

namespace Work.SSGRoute

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type*} [Ring k] [Linear k C]
  {X Y : C}

/-- The underlying morphism `R.complex.X n ⟶ Y` of an element of the `n`-cycles of the complex
`Hom(R_•, Y) = R.complex.linearYonedaObj k Y`. -/
@[irreducible] noncomputable def cycHom (R : ProjectiveResolution X) (n : ℕ)
    (z : (R.complex.linearYonedaObj k Y).cycles n) : R.complex.X n ⟶ Y :=
  (R.complex.linearYonedaObj k Y).iCycles n z

variable [HasExt.{v} C]

set_option linter.unusedSectionVars false

lemma cycHom_add (R : ProjectiveResolution X) (n : ℕ)
    (z w : (R.complex.linearYonedaObj k Y).cycles n) :
    cycHom R n (z + w) = cycHom R n z + cycHom R n w := by
  unfold cycHom
  exact map_add (ModuleCat.Hom.hom ((R.complex.linearYonedaObj k Y).iCycles n)) z w

lemma cycHom_smul (R : ProjectiveResolution X) (n : ℕ) (r : k)
    (z : (R.complex.linearYonedaObj k Y).cycles n) :
    cycHom R n (r • z) = r • cycHom R n z := by
  unfold cycHom
  exact map_smul (ModuleCat.Hom.hom ((R.complex.linearYonedaObj k Y).iCycles n)) r z

lemma cycHom_zero (R : ProjectiveResolution X) (n : ℕ) :
    cycHom R n (0 : (R.complex.linearYonedaObj k Y).cycles n) = 0 := by
  unfold cycHom
  exact map_zero (ModuleCat.Hom.hom ((R.complex.linearYonedaObj k Y).iCycles n))

/-- Every element of the `n`-cycles gives a morphism `R.complex.X n ⟶ Y` satisfying the cocycle
condition of `ProjectiveResolution.extMk`. -/
lemma cycHom_cocycle (R : ProjectiveResolution X) (n : ℕ)
    (z : (R.complex.linearYonedaObj k Y).cycles n) :
    R.complex.d (n + 1) n ≫ cycHom R n z = 0 := by
  unfold cycHom
  have h := ConcreteCategory.congr_hom ((R.complex.linearYonedaObj k Y).iCycles_d n (n+1)) z
  rw [ConcreteCategory.comp_apply] at h
  change (R.complex.linearYonedaObj k Y).d n (n+1)
    ((R.complex.linearYonedaObj k Y).iCycles n z) = 0 at h
  change R.complex.d (n+1) n ≫ ((R.complex.linearYonedaObj k Y).iCycles n z) = 0
  exact h

/-- On the `n`-cycles produced by `HomologicalComplex.cyclesMk` out of a cocycle `f`, `cycHom`
returns `f`. -/
lemma cycHom_cyclesMk (R : ProjectiveResolution X) (n : ℕ) (f : R.complex.X n ⟶ Y)
    (hK : (R.complex.linearYonedaObj k Y).d n (n+1) f = 0) :
    cycHom R n ((R.complex.linearYonedaObj k Y).cyclesMk f (n+1)
        (ComplexShape.next_eq' (c := ComplexShape.up ℕ) rfl) hK) = f := by
  unfold cycHom
  have hK' : (ConcreteCategory.hom ((forget₂ (ModuleCat k) Ab).map ((R.complex.linearYonedaObj k Y).d n (n+1)))) f = 0 := hK
  exact HomologicalComplex.i_cyclesMk (R.complex.linearYonedaObj k Y) f (n+1)
    (ComplexShape.next_eq' (c := ComplexShape.up ℕ) rfl) hK'

/-- The differential of `Hom(K_•, Y)` is precomposition with the differential of `K`. -/
lemma linearYonedaObj_d_apply (K : ChainComplex C ℕ) (Y : C) {i j : ℕ} (hij : i + 1 = j)
    (f : K.X i ⟶ Y) :
    (K.linearYonedaObj k Y).d i j f = (K.d j i) ≫ f := by
  subst hij
  rfl

/-- On the boundaries `K.toCycles i n x`, `cycHom` returns the composite with the differential. -/
lemma cycHom_toCycles (R : ProjectiveResolution X) (n : ℕ)
    (x : (R.complex.linearYonedaObj k Y).X ((ComplexShape.up ℕ).prev n))
    (hp : (ComplexShape.up ℕ).prev n + 1 = n) :
    cycHom R n ((R.complex.linearYonedaObj k Y).toCycles ((ComplexShape.up ℕ).prev n) n x)
      = R.complex.d n ((ComplexShape.up ℕ).prev n) ≫ x := by
  let K := R.complex.linearYonedaObj k Y
  unfold cycHom
  have h := ConcreteCategory.congr_hom (K.toCycles_i ((ComplexShape.up ℕ).prev n) n) x
  rw [ConcreteCategory.comp_apply] at h
  change K.iCycles n (K.toCycles ((ComplexShape.up ℕ).prev n) n x)
    = K.d ((ComplexShape.up ℕ).prev n) n x at h
  rw [h]
  exact linearYonedaObj_d_apply R.complex Y hp x

/-- In degree `0` the boundary map `K.toCycles (prev 0) 0` is the zero map, so `cycHom` vanishes
on its image. -/
lemma cycHom_toCycles_zero (R : ProjectiveResolution X)
    (x : (R.complex.linearYonedaObj k Y).X ((ComplexShape.up ℕ).prev 0)) :
    cycHom R 0 ((R.complex.linearYonedaObj k Y).toCycles ((ComplexShape.up ℕ).prev 0) 0 x) = 0 := by
  let K := R.complex.linearYonedaObj k Y
  unfold cycHom
  have h := ConcreteCategory.congr_hom (K.toCycles_i ((ComplexShape.up ℕ).prev 0) 0) x
  rw [ConcreteCategory.comp_apply] at h
  change K.iCycles 0 (K.toCycles ((ComplexShape.up ℕ).prev 0) 0 x)
    = K.d ((ComplexShape.up ℕ).prev 0) 0 x at h
  rw [h]
  rw [HomologicalComplex.shape]
  · rfl
  · rw [ComplexShape.up_Rel]
    omega

/-- `extMk` only depends on the morphism, not on the proof of the cocycle condition. -/
lemma extMk_congr (R : ProjectiveResolution X) {n : ℕ} {f g : R.complex.X n ⟶ Y} (h : f = g)
    (hf : R.complex.d (n + 1) n ≫ f = 0) (hg : R.complex.d (n + 1) n ≫ g = 0) :
    R.extMk f (n + 1) rfl hf = R.extMk g (n + 1) rfl hg := by
  subst h
  simp only [ProjectiveResolution.extMk]


end Work.SSGRoute
