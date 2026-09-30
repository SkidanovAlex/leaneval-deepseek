/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area CH — route B of COV′: the definitions

This file sets up the vocabulary of **route B** of `Submission/Work/NOTES_LEAD_jacobian_charts3.md`
§1–§4, the proof of COV′ which replaces the (unsound) covering chain of `CoverReduction.lean`
by a direct construction over the base field `k`:

* `ρ : Sym^{g+g} C ⇢ Sym^g C`, `Σ ↦ |Σ − g·P₀|` — the residue map of area `DM` (RESID) at
  `r = m = g`, `a =` the constant map at `g·P₀` and `b = 𝟙` (`rho`);
* `W′ := dom ρ ∩ ρ⁻¹(V)` — the open of `Sym^{g+g} C` on which the residue map is defined and
  takes its value in the Brill–Noether chart (`Wp`);
* `addCentre E : S_L ⟶ Sym^{g+g} C` — "add the centre `E`" (`addCentre`);
* `Ω_E := S ∖ fst((addCentre E)⁻¹(W′)ᶜ)` — the open of `Sym^g C` attached to a centre `E` over
  a *finite* extension `L/K` (`omegaOpen`); it is open because `fst : S_L ⟶ S` is finite, hence
  a closed map (`isClosedMap_bcFst`);
* `step3b x`, `step3Z x`, `step3U x` — the three sets of §1(S): `b_x := add(x ∘ snd, fst)`,
  `Z_x := b_x⁻¹(W′)ᶜ` and `U_x := S ∖ fst(Z_x)`, for a closed point `x` of `S = Sym^g C`.

The point of `Ω_E` is that it is a *`K`-open* of `S`: hence for every field `F` containing `L`
and every `F`-point `D` of `S` landing in `Ω_E`, the translate `add(D, E)` lands in `W′` — for
*every* `K`-embedding `L ↪ F` at once.  That is the whole Galois-orbit condition of COV′,
obtained for free (`addMor_landsIn_Wp_of_landsIn_omega`).

Everything here is a definition (no `sorry`); the lemmas about them live one per file in this
directory.
-/
import Submission.Work.Charts.Core
import Submission.Work.Charts.FinBC
import Submission.Work.Domain.Resid.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K]

/-! ### The instance-carrying abbreviations -/

/-- **Pushforward of a point along a morphism**: `ptComp p f = p ≫ f`.

It exists so that statements about points can be written without the composition notation `≫`,
which in this pin is only available inside the `CategoryTheory` namespace. -/
def ptComp {X Y : Sch K} {F : Type u} [Field F] [Algebra K F] (p : FPt X F) (f : X ⟶ Y) :
    FPt Y F :=
  p ≫ f

@[simp]
theorem ptComp_apply {X Y : Sch K} {F : Type u} [Field F] [Algebra K F] (p : FPt X F)
    (f : X ⟶ Y) : ptComp p f = p ≫ f := rfl

/-- `SymProps C n` for the instance coming from a family `symGeom : ∀ n, SymGeom C n`. -/
abbrev SymPropsAt {C : Curve K} [Work.SpecLin.DivBase C]
    (symGeom : ∀ n, Work.SpecLin.SymGeom C n) (n : ℕ) : Prop :=
  @SymProps K _ C _ n (symGeom n)

/-- `BNData C R` for the instance coming from a family `symGeom : ∀ n, SymGeom C n`. -/
abbrev BNDataAt {C : Curve K} [Work.SpecLin.DivBase C] (R : RochData C)
    (symGeom : ∀ n, Work.SpecLin.SymGeom C n) : Type u :=
  @BNData K _ C _ R (symGeom R.g)

section ToUnit

variable {C : Curve K} [Work.SpecLin.DivBase C]

/-- The terminal `K`-scheme `Spec K`, i.e. `𝟙_ (Sch K)`, under a notation-free name (the
monoidal-unit notation `𝟙_` is only available inside the `CategoryTheory` namespace at this
pin, which makes it unusable in statements elaborated elsewhere). -/
abbrev unitSch (K : Type u) [Field K] : Sch K :=
  𝟙_ (Sch K)

/-- The unique morphism from a `K`-scheme to the terminal object `𝟙_ (Sch K)`. -/
def toUnit (X : Sch K) : X ⟶ 𝟙_ (Sch K) :=
  SemiCartesianMonoidalCategory.toUnit X

theorem toUnit_unique {X : Sch K} (f g : X ⟶ 𝟙_ (Sch K)) : f = g :=
  SemiCartesianMonoidalCategory.toUnit_unique f g

theorem comp_toUnit {X Y : Sch K} (f : X ⟶ Y) : f ≫ toUnit Y = toUnit X :=
  SemiCartesianMonoidalCategory.comp_toUnit f

/-- **The base point as a `K`-point of `C`**: the `𝟙_ (Sch K)`-point `P0` of areas `GC`/`DS`,
read as a point of `C` over `K`. -/
def toCurveFPt (P0 : 𝟙_ (Sch K) ⟶ C.toOver) : Work.SpecLin.CurveFPt C K :=
  toUnit (specOf K K) ≫ P0

/-- **The divisor `[P₀]` of the base point**, in the form used by route B. -/
noncomputable def P0DivOf (P0 : 𝟙_ (Sch K) ⟶ C.toOver) : Dv C K :=
  Work.SpecLin.ptDiv (toCurveFPt P0)

/-- **The constant map at `n · P₀`**: `T ⟶ Sym^n C` sending every point of `T` to the
`K`-point `n · P₀` of `Sym^n C`.  (Route B applies this with `T = Sym^{g+g} C`, `n = g`.) -/
noncomputable def constMap (symGeom : ∀ n, Work.SpecLin.SymGeom C n) (n : ℕ)
    (P0 : 𝟙_ (Sch K) ⟶ C.toOver) (T : Sch K) : T ⟶ (symGeom n).S :=
  (symGeom n).powMap (fun _ : Fin n => toUnit T ≫ P0)

end ToUnit

/-! ### The geometric hypotheses of route B -/

/-- **The geometric hypotheses of route B** (`NOTES_LEAD_jacobian_charts3.md` §3).  They are
the parts of `SymProps C g` and `SymProps C (g+g)` that the construction uses, together with
area `NM`'s normality input for `Sym^{g+g} C` (needed by area `DM`'s RESID theorems). -/
structure Step3Geo {C : Curve K} [Work.SpecLin.DivBase C] (R : RochData C)
    (symGeom : ∀ n, Work.SpecLin.SymGeom C n) : Prop where
  /-- `Sym^g C` is integral -/
  integral_g : IsIntegral ((symGeom R.g).S).left
  /-- `Sym^{g+g} C` is integral -/
  integral_gg : IsIntegral ((symGeom (R.g + R.g)).S).left
  /-- `Sym^g C` is separated over `K` -/
  separated_g : IsSeparated ((symGeom R.g).S).hom
  /-- `Sym^g C` is geometrically irreducible over `K` -/
  geomIrr_g : GeometricallyIrreducible ((symGeom R.g).S).hom
  /-- `Sym^{g+g} C` is geometrically irreducible over `K` -/
  geomIrr_gg : GeometricallyIrreducible ((symGeom (R.g + R.g)).S).hom
  /-- `Sym^g C` is quasi-compact over `K` -/
  quasiCompact_g : QuasiCompact ((symGeom R.g).S).hom
  /-- `Sym^g C` is locally of finite type over `K` -/
  locallyOfFiniteType_g : LocallyOfFiniteType ((symGeom R.g).S).hom
  /-- **area `NM`**: the local rings of `Sym^{g+g} C` are integrally closed -/
  hstalk : ∀ x : ((symGeom (R.g + R.g)).S).left,
    IsIntegrallyClosed (((symGeom (R.g + R.g)).S).left.presheaf.stalk x)

/-- **All the inputs of route B**, bundled (the curve `C` and the Riemann–Roch data `R` stay
parameters): the family of symmetric powers, the RESID data, the geometry of `Sym^g C` and
`Sym^{g+g} C`, the constant map `a` at `g·P₀` together with its divisor computation `ha`, and
the Brill–Noether chart `d`. -/
structure Step3Data {C : Curve K} [Work.SpecLin.DivBase C] (R : RochData C) where
  /-- the symmetric powers (area `SY`) -/
  symGeom : ∀ n, Work.SpecLin.SymGeom C n
  /-- RESID (area `DM`) -/
  resid : Work.Domain.Resid.ResidData (K := K) symGeom R.g
  /-- the geometry of `Sym^g C` and `Sym^{g+g} C` -/
  geo : Step3Geo R symGeom
  /-- the constant map at `g · P₀` -/
  a : (symGeom (R.g + R.g)).S ⟶ (symGeom R.g).S
  /-- the base divisor `[P₀]` -/
  P0Div : Dv C K
  /-- `[P₀]` has degree one -/
  hP0 : Ddeg C K P0Div = 1
  /-- the divisor of `a` is `g · [P₀]` -/
  ha : ∀ {F : Type u} [Field F] [Algebra K F]
    (p : FPt ((symGeom (R.g + R.g)).S) F),
    (symGeom R.g).divOf (ptComp p a) = (R.g : ℤ) • pullK C P0Div
  /-- the Brill–Noether chart -/
  d : BNDataAt R symGeom

section Defs

variable {C : Curve K} [Work.SpecLin.DivBase C] (R : RochData C)
  (symGeom : ∀ n, Work.SpecLin.SymGeom C n)
  (D : Work.Domain.Resid.ResidData (K := K) symGeom R.g)
  (G : Step3Geo R symGeom)

/-- **`ρ : Sym^{g+g} C ⇢ Sym^g C`, `Σ ↦ |Σ − g·P₀|`** — the residue map of area `DM` (RESID)
at `r = m = g`, `b = 𝟙`; the value of `ρ` at a point `Σ` is the effective representative of
the class of `divOf Σ − divOf (a Σ)`, where `a` is the map named by `a` below. -/
noncomputable def rho (a : (symGeom (R.g + R.g)).S ⟶ (symGeom R.g).S) :
    ((symGeom (R.g + R.g)).S).left ⤏ ((symGeom R.g).S).left := by
  haveI := G.integral_gg
  exact D.residMap a (𝟙 _) le_rfl

/-- **`W′ := dom ρ ∩ ρ⁻¹(V)`**: the open of `Sym^{g+g} C` on which the residue map is defined
and its value lies in the Brill–Noether chart `V`.

The two properties of `W′` are `exists_V_of_landsIn_Wp` (POINT: a point of `W′` has a
representative in `V`) and `landsIn_Wp_of_linEquiv` (CRIT: a point whose class is represented
by a point of `V` lies in `W′`). -/
noncomputable def Wp (a : (symGeom (R.g + R.g)).S ⟶ (symGeom R.g).S)
    (d : BNDataAt R symGeom) : ((symGeom (R.g + R.g)).S).left.Opens := by
  haveI := G.integral_gg
  haveI : IsReduced ((symGeom (R.g + R.g)).S).left :=
    isReduced_of_isIntegral (X := ((symGeom (R.g + R.g)).S).left)
  haveI := G.separated_g
  exact (rho R symGeom D G a).domain.ι ''ᵁ
    ((rho R symGeom D G a).toPartialMap.hom ⁻¹ᵁ d.V)

/-- **`addCentre E : S_L ⟶ Sym^{g+g} C`**, where `S = Sym^g C` and `E` is an `L`-point of `S`:
the map `add(fst, E ∘ snd)`, i.e. "add the centre `E`" to a point of `S_L`. -/
noncomputable def addCentre {L : Type u} [Field L] [Algebra K L]
    (E : FPt ((symGeom R.g).S) L) :
    bcSch ((symGeom R.g).S) L ⟶ (symGeom (R.g + R.g)).S :=
  Work.Domain.Resid.addMor symGeom D.addMap (bcFst ((symGeom R.g).S) L)
    (bcSnd ((symGeom R.g).S) L ≫ E)

/-- **`Ω_E := S ∖ fst((addCentre E)⁻¹(W′)ᶜ)`** — the open of `S = Sym^g C` attached to an
`L`-point `E` of `S`, for a **finite** extension `L/K` (so that `fst : S_L ⟶ S` is finite,
hence closed, so that the complement of the image is open).

`addMor_landsIn_Wp_of_landsIn_omega` shows that every `F`-point of `S` landing in `Ω_E` has
`add(D, E^ε)` in `W′`, for every `K`-embedding `ε : L → F`. -/
noncomputable def omegaOpen {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
    (E : FPt ((symGeom R.g).S) L) (a : (symGeom (R.g + R.g)).S ⟶ (symGeom R.g).S)
    (d : BNDataAt R symGeom) : ((symGeom R.g).S).left.Opens :=
  ⟨((bcFst ((symGeom R.g).S) L).left.base ''
      ((addCentre R symGeom D E).left ⁻¹ᵁ (Wp R symGeom D G a d) : Set _)ᶜ)ᶜ,
   (isClosedMap_bcFst ((symGeom R.g).S) L _
     ((addCentre R symGeom D E).left ⁻¹ᵁ (Wp R symGeom D G a d)).2.isClosed_compl).isOpen_compl⟩

/-- **`b_x := add(x ∘ snd, fst) : S_{κ(x)} ⟶ Sym^{g+g} C`**, for a point `x` of `S`. -/
noncomputable def step3b (x : ((symGeom R.g).S).left) :
    bcSch ((symGeom R.g).S) (resField ((symGeom R.g).S) x) ⟶ (symGeom (R.g + R.g)).S :=
  Work.Domain.Resid.addMor symGeom D.addMap
    (bcSnd ((symGeom R.g).S) (resField ((symGeom R.g).S) x) ≫ resPt ((symGeom R.g).S) x)
    (bcFst ((symGeom R.g).S) (resField ((symGeom R.g).S) x))

/-- **`Z_x := b_x⁻¹(W′)ᶜ`**, the closed subset of `S_{κ(x)}` of §1(S) of the design. -/
noncomputable def step3Z (x : ((symGeom R.g).S).left)
    (a : (symGeom (R.g + R.g)).S ⟶ (symGeom R.g).S) (d : BNDataAt R symGeom) :
    Set (bcSch ((symGeom R.g).S) (resField ((symGeom R.g).S) x)).left :=
  ((step3b R symGeom D x).left ⁻¹ᵁ (Wp R symGeom D G a d) : Set _)ᶜ

@[simp]
theorem mem_step3Z {x : ((symGeom R.g).S).left}
    {a : (symGeom (R.g + R.g)).S ⟶ (symGeom R.g).S} {d : BNDataAt R symGeom}
    {z : (bcSch ((symGeom R.g).S) (resField ((symGeom R.g).S) x)).left} :
    z ∈ step3Z R symGeom D G x a d ↔
      (step3b R symGeom D x).left z ∉ (Wp R symGeom D G a d :
        Set ((symGeom (R.g + R.g)).S).left) :=
  Iff.rfl

/-- `Z_x` is closed (it is the complement of the preimage of the open `W′`). -/
theorem isClosed_step3Z (x : ((symGeom R.g).S).left)
    (a : (symGeom (R.g + R.g)).S ⟶ (symGeom R.g).S) (d : BNDataAt R symGeom) :
    IsClosed (step3Z R symGeom D G x a d) :=
  ((step3b R symGeom D x).left ⁻¹ᵁ (Wp R symGeom D G a d)).2.isClosed_compl

/-- **`U_x := S ∖ fst(Z_x)`**, the open of `S` of §1(S) of the design. -/
noncomputable def step3U (x : ((symGeom R.g).S).left)
    (a : (symGeom (R.g + R.g)).S ⟶ (symGeom R.g).S) (d : BNDataAt R symGeom)
    [FiniteDimensional K (resField ((symGeom R.g).S) x)] :
    ((symGeom R.g).S).left.Opens :=
  ⟨((bcFst ((symGeom R.g).S) (resField ((symGeom R.g).S) x)).left.base ''
      (step3Z R symGeom D G x a d))ᶜ,
   (isClosedMap_bcFst ((symGeom R.g).S) (resField ((symGeom R.g).S) x) _
     (isClosed_step3Z R symGeom D G x a d)).isOpen_compl⟩

end Defs

end

end Work.Charts
