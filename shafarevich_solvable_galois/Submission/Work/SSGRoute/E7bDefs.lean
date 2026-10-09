import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E7b vocabulary (DEFINITIONS ONLY; lead-placed, do not edit)

To be created as `Submission/Work/SSGRoute/E7bDefs.lean`.  See `requests/ssg6/DESIGN_E7B.md`.

* `RightDetect f ι M` — the "right radical = 0" clause of the level pairing for an *abstract* local
  tower `f : G →* D`, `ι : res_f A ⟶ B` (no fields involved).  E7b clause (ii) is
  `RightDetect f ι (res M)` at every level with `p ∣ |D_{w'}|`, turned into realisation by the proved
  `Work.SSGRoute.local_duality_ext_realization_of_detection`.
* `PTorsLE p X` — the `p`-torsion of `X` is finite with at most `p` elements.
* `VanishesAbove` / `DetectAbove` — clause (i) in *cone* form: detection by the levels lying above
  an arbitrary level `(L₀, w₀)`, with the level data at `L` written as the composite
  `(f₀ ∘ g, res_g ι₀ ≫ ι₁)` of the data at `L₀` and the restriction data `L ⊇ L₀`.
  `DetectAbove` at the base level `L₀ = K` is clause (i) of E7b.
-/

open CategoryTheory

noncomputable section

namespace SSGRoute.PTExt

section Abstract

variable {G D : Type} [Group G] [Group D]

/-- **Right detection** for the abstract tower `f : G →* D`, `ι : res_f A ⟶ B`: every nonzero
`h ∈ H¹(G, res_f M)` pairs nontrivially with some `y ∈ Ext¹_D(M, A)`. -/
def RightDetect (f : G →* D) {A : Rep.{0} Coeff D} {B : Rep.{0} Coeff G}
    (ι : Rep.res f A ⟶ B) (M : Rep.{0} Coeff D) : Prop :=
  ∀ h : extH (Rep.res f M) 1, h ≠ 0 → ∃ y : Abelian.Ext.{0} M A 1, levelPair f ι y h ≠ 0

/-- The `p`-torsion subgroup of `X` is finite with at most `p` elements. -/
def PTorsLE (p : ℕ) (X : Type) [AddCommGroup X] : Prop :=
  Finite {x : X // p • x = 0} ∧ Nat.card {x : X // p • x = 0} ≤ p

end Abstract

section Cone

open NK.GlobalCFT

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- **`y` vanishes above the level `(L₀, w₀, f₀, ι₀)`**: at every level `L ⊇ L₀` (Galois over
`k`), every place `w' ∣ w₀`, with the restriction data `g : D_{w'} →* D_{w₀}` and the local
embedding `ι₁ : L₀,w₀ˣ → L_{w'}ˣ`, the level pairing of `y` with every `h ∈ H¹(D_{w'}, N)` is `0`. -/
def VanishesAbove {w : Place K} {N : Rep.{0} Coeff (decompK (k := k) w)}
    (y : Abelian.Ext.{0} N (localUnitsK (k := k) w) 1)
    (L₀ : Type) [Field L₀] [NumberField L₀] [Algebra k L₀] [FiniteDimensional k L₀]
    [IsGalois k L₀] (w₀ : Place L₀)
    (f₀ : MulAction.stabilizer (L₀ ≃ₐ[k] L₀) w₀ →* decompK (k := k) w)
    (ι₀ : Rep.res f₀ (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L₀ w₀) :
    Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra L₀ L] [IsScalarTower k L₀ L]
    [FiniteDimensional k L] [IsGalois k L]
    (w' : Place L) (hw' : Place.LiesOver w' w₀)
    (g : MulAction.stabilizer (L ≃ₐ[k] L) w' →* MulAction.stabilizer (L₀ ≃ₐ[k] L₀) w₀)
    (_hg : ∀ σ, ((g σ : MulAction.stabilizer (L₀ ≃ₐ[k] L₀) w₀) : L₀ ≃ₐ[k] L₀) =
      galRes k L₀ L (σ : L ≃ₐ[k] L))
    (ι₁ : Rep.res g (NK.HassePrinciple.localUnitsRep k L₀ w₀) ⟶
      NK.HassePrinciple.localUnitsRep k L w')
    (_hι₁ : ∀ u : (Place.localField L₀ w₀)ˣ,
      ι₁.hom (Additive.ofMul u) = Additive.ofMul (Place.localAlgebraMapUnits w' w₀ hw' u))
    (h : extH (Rep.res (f₀.comp g) N) 1),
    levelPair (f₀.comp g) (Rep.resMap g ι₀ ≫ ι₁) y h = 0

/-- **Clause (i) in cone form**: for every level `(L₀, w₀ ∣ w)` with its canonical data
`(f₀, ι₀)`, a class `y ∈ Ext¹_{D_w}(N, K_wˣ)` vanishing above `(L₀, w₀)` is `0`. -/
def DetectAbove (w : Place K) (N : Rep.{0} Coeff (decompK (k := k) w)) : Prop :=
  ∀ (L₀ : Type) [Field L₀] [NumberField L₀] [Algebra k L₀] [Algebra K L₀] [IsScalarTower k K L₀]
    [FiniteDimensional k L₀] [IsGalois k L₀]
    (w₀ : Place L₀) (hw₀ : Place.LiesOver w₀ w)
    (f₀ : MulAction.stabilizer (L₀ ≃ₐ[k] L₀) w₀ →* decompK (k := k) w)
    (_hf₀ : ∀ σ, ((f₀ σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L₀ (σ : L₀ ≃ₐ[k] L₀))
    (ι₀ : Rep.res f₀ (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L₀ w₀)
    (_hι₀ : ∀ u : (Place.localField K w)ˣ,
      ι₀.hom (Additive.ofMul u) = Additive.ofMul (Place.localAlgebraMapUnits w₀ w hw₀ u))
    (y : Abelian.Ext.{0} N (localUnitsK (k := k) w) 1),
    VanishesAbove k K y L₀ w₀ f₀ ι₀ → y = 0

end Cone

end SSGRoute.PTExt
