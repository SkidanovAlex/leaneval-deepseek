import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.NK.NUV2.RouteC.Invariant
import Submission.NK.NUV2.RouteC.doubleDual_surjective
import Submission.NK.NUV2.RouteC.map_powHom_eq_zero_of_mem_normGroup
import Submission.NK.NUV2.RouteE.levelH2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level symbol `θ : Fˣ →* Gal(E/F)` of a fundamental class

For a finite abelian Galois extension `E/F` and a *fundamental class*
`u ∈ H²(Gal(E/F), Eˣ)` of additive order `[E : F]` (`NK.NUV2.RouteE.h2_cyclicLevel` produces
one), the `ℚ/ℤ`-valued invariant `ι_u` of `NK.NUV2.RouteC.Invariant` converts the cup product
with a character into a character of `Fˣ`:

`χ(θ a) = ι_u (a ∪ δχ)`,

and Pontryagin duality (Mathlib's `AddChar.doubleDualEmb_bijective`, via
`NK.NUV2.RouteC.doubleDual_surjective`) pins the element `θ a ∈ Gal(E/F)` down uniquely.  The
resulting map `θ` is a monoid homomorphism — this is the *level symbol* of the character-formula
route to the local reciprocity law.

## Main definitions and results

* `NK.NUV2.RouteE.map_add_apply`: `groupCohomology.map` is additive in the coefficient morphism
  (degree `2`);
* `NK.NUV2.RouteE.doubleDual_injective`: for a finite abelian group the characters separate
  points (the injectivity half of Pontryagin duality);
* `NK.NUV2.RouteE.charValue`, `NK.NUV2.RouteE.levelSymbol`: the character formula and the level
  symbol;
* `NK.NUV2.RouteE.levelSymbol_apply`: the defining character formula;
* `NK.NUV2.RouteE.levelSymbol_one`, `NK.NUV2.RouteE.levelSymbol_mul`: `θ` is multiplicative.
-/

open scoped BigOperators
open CategoryTheory

namespace NK.NUV2.RouteE

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-! ## Additivity of the cohomology map in the coefficient morphism -/

section Additive

variable {k : Type} [CommRing k] {G H : Type} [Group G] [Group H]

/-- The pointwise formula for the cochain map `cochainsMap₂`. -/
theorem cochainsMap₂_apply (f : G →* H) {A : Rep k H} {B : Rep k G}
    (φ : Rep.res f A ⟶ B) (x : H × H → A) (p : G × G) :
    (groupCohomology.cochainsMap₂ f φ) x p = φ.hom (x (f p.1, f p.2)) := rfl

/-- **`groupCohomology.map` is additive in the coefficient morphism** (in degree `2`). -/
theorem map_add_apply (f : G →* H) {A : Rep k H} {B : Rep k G}
    (φ ψ : Rep.res f A ⟶ B) (x : groupCohomology A 2) :
    (groupCohomology.map f (φ + ψ) 2) x
      = (groupCohomology.map f φ 2) x + (groupCohomology.map f ψ 2) x := by
  refine groupCohomology.H2_induction_on x (fun z => ?_)
  have h1 : (groupCohomology.map f (φ + ψ) 2) (groupCohomology.H2π A z)
      = groupCohomology.H2π B
        (groupCohomology.mapCocycles₂ f (φ + ψ) z) := by
    have h := congrArg (fun m => (ConcreteCategory.hom m) z)
      (groupCohomology.H2π_comp_map f (φ + ψ))
    simpa only [ConcreteCategory.comp_apply] using h
  have h2 : (groupCohomology.map f φ 2) (groupCohomology.H2π A z)
      = groupCohomology.H2π B (groupCohomology.mapCocycles₂ f φ z) := by
    have h := congrArg (fun m => (ConcreteCategory.hom m) z)
      (groupCohomology.H2π_comp_map f φ)
    simpa only [ConcreteCategory.comp_apply] using h
  have h3 : (groupCohomology.map f ψ 2) (groupCohomology.H2π A z)
      = groupCohomology.H2π B (groupCohomology.mapCocycles₂ f ψ z) := by
    have h := congrArg (fun m => (ConcreteCategory.hom m) z)
      (groupCohomology.H2π_comp_map f ψ)
    simpa only [ConcreteCategory.comp_apply] using h
  rw [h1, h2, h3, ← map_add]
  congr 1

end Additive

/-! ## The injectivity half of Pontryagin duality -/

section Separation

/-- **Characters separate points of a finite abelian group**: if all `ℚ/ℤ`-valued additive
characters agree on `a` and `b` then `a = b`.  (The injectivity half of Pontryagin duality,
obtained from Mathlib's `AddChar.doubleDualEmb_bijective` via the bridge
`NK.NUV2.RouteC.qmodZDualEquivComplex` between `ℚ/ℤ`-valued and `ℂ`-valued characters.) -/
theorem doubleDual_injective_add {A : Type} [AddCommGroup A] [Finite A] {a b : A}
    (h : ∀ χ : A →+ NK.NUV2.RouteC.qmodZ, χ a = χ b) : a = b := by
  refine AddChar.doubleDualEmb_bijective.1 ?_
  ext ψ
  rw [AddChar.doubleDualEmb_apply, AddChar.doubleDualEmb_apply]
  have h2 := h ((NK.NUV2.RouteC.qmodZDualEquivComplex (A := A)).symm ψ)
  have h3 : NK.NUV2.RouteC.qmodZDualEquivComplex (A := A)
      ((NK.NUV2.RouteC.qmodZDualEquivComplex (A := A)).symm ψ) = ψ :=
    AddEquiv.apply_symm_apply _ _
  have h4 : ψ = NK.NUV2.RouteC.toComplexChar
      ((NK.NUV2.RouteC.qmodZDualEquivComplex (A := A)).symm ψ) := h3.symm
  rw [h4]
  exact congrArg (fun z => (NK.NUV2.RouteC.expQmodZ z).toMul) h2

/-- **Characters separate points of a finite commutative group** (in multiplicative notation). -/
theorem doubleDual_injective {Γ : Type} [Group Γ] [Fintype Γ]
    (hcomm : ∀ a b : Γ, a * b = b * a) {g h : Γ}
    (hh : ∀ χ : Additive Γ →+ NK.NUV2.RouteC.qmodZ,
      χ (Additive.ofMul g) = χ (Additive.ofMul h)) : g = h := by
  letI : CommGroup Γ := { ‹Group Γ› with mul_comm := hcomm }
  haveI : Finite (Additive Γ) := Fintype.finite inferInstance
  have h2 := doubleDual_injective_add (A := Additive Γ) (a := Additive.ofMul g)
    (b := Additive.ofMul h) hh
  exact Additive.ofMul.injective h2

end Separation

end NK.NUV2.RouteE

namespace NK.NUV2.RouteE

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open scoped BigOperators
open CategoryTheory

section LevelSymbol

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [Fintype (E ≃ₐ[F] E)]
variable [Finite (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)]

/-- The cup product with `a ∈ Fˣ` is the zero coefficient change: `powHom 1 = 0`. -/
theorem powHom_one : NK.NUV2.RouteC.powHom (F := F) (E := E) (1 : Fˣ) = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro n
  show n • (Additive.ofMul (Units.map (algebraMap F E).toMonoidHom (1 : Fˣ)) : Additive Eˣ) = 0
  simp

theorem map_zero_apply {k : Type} [CommRing k] {G H : Type} [Group G] [Group H]
    (f : G →* H) {A : Rep k H} {B : Rep k G} (x : groupCohomology A 2) :
    (groupCohomology.map f (0 : Rep.res f A ⟶ B) 2) x = 0 := by
  have h := map_add_apply f (0 : Rep.res f A ⟶ B) (0 : Rep.res f A ⟶ B) x
  rw [add_zero] at h
  have h2 := congrArg (fun z => z - (groupCohomology.map f (0 : Rep.res f A ⟶ B) 2) x) h
  simp only [sub_self, add_sub_cancel_right] at h2
  exact h2.symm

/-- **The character pairing** attached to a fundamental class `u`: the additive map sending a
character `χ` of `Gal(E/F)` to the `ℚ/ℤ`-value `ι_u (a ∪ δχ)`. -/
noncomputable def charValue (u : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)
    (hu : addOrderOf u = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2))
    (a : Fˣ) : (Additive (E ≃ₐ[F] E) →+ NK.NUV2.RouteC.qmodZ) →+ NK.NUV2.RouteC.qmodZ where
  toFun χ := NK.NUV2.RouteC.invariantOf u hu
    (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
      (NK.NUV2.RouteC.powHom (F := F) (E := E) a) 2
      (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) χ))
  map_zero' := by
    show NK.NUV2.RouteC.invariantOf u hu
      (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
        (NK.NUV2.RouteC.powHom (F := F) (E := E) a) 2
        (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) 0)) = 0
    rw [map_zero, map_zero, map_zero]
  map_add' χ χ' := by
    show NK.NUV2.RouteC.invariantOf u hu
        (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
          (NK.NUV2.RouteC.powHom (F := F) (E := E) a) 2
          (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) (χ + χ'))) =
      NK.NUV2.RouteC.invariantOf u hu
        (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
          (NK.NUV2.RouteC.powHom (F := F) (E := E) a) 2
          (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) χ)) +
      NK.NUV2.RouteC.invariantOf u hu
        (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
          (NK.NUV2.RouteC.powHom (F := F) (E := E) a) 2
          (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) χ'))
    rw [map_add, map_add, map_add]

/-- **The character pairing is multiplicative in `a`**, by the bilinearity of the cup product. -/
theorem charValue_mul (u : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)
    (hu : addOrderOf u = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2))
    (a b : Fˣ) : charValue u hu (a * b) = charValue u hu a + charValue u hu b := by
  ext χ
  show NK.NUV2.RouteC.invariantOf u hu
      (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
        (NK.NUV2.RouteC.powHom (F := F) (E := E) (a * b)) 2
        (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) χ)) =
    NK.NUV2.RouteC.invariantOf u hu
        (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
          (NK.NUV2.RouteC.powHom (F := F) (E := E) a) 2
          (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) χ)) +
      NK.NUV2.RouteC.invariantOf u hu
        (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
          (NK.NUV2.RouteC.powHom (F := F) (E := E) b) 2
          (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) χ))
  rw [NK.NUV2.RouteC.powHom_mul, map_add_apply]
  rw [map_add]

theorem charValue_one (u : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)
    (hu : addOrderOf u = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)) :
    charValue u hu 1 = 0 := by
  ext χ
  show NK.NUV2.RouteC.invariantOf u hu
      (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
        (NK.NUV2.RouteC.powHom (F := F) (E := E) 1) 2
        (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) χ)) = 0
  rw [powHom_one, map_zero_apply, map_zero]

variable (hcomm : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ)

/-- **The level symbol** `θ_{E,u} : Fˣ →* Gal(E/F)` attached to a fundamental class `u`: the
unique homomorphism whose values are characterized by `χ (θ a) = ι_u (a ∪ δχ)` for every character
`χ`.  Pontryagin duality (`NK.NUV2.RouteE.doubleDual_injective`) makes it multiplicative. -/
noncomputable def levelSymbol (u : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)
    (hu : addOrderOf u = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)) :
    Fˣ →* (E ≃ₐ[F] E) where
  toFun a := Classical.choose (NK.NUV2.RouteC.doubleDual_surjective (charValue u hu a))
  map_one' := by
    set g := Classical.choose (NK.NUV2.RouteC.doubleDual_surjective (charValue u hu 1)) with hg
    have hspec := Classical.choose_spec (NK.NUV2.RouteC.doubleDual_surjective (charValue u hu 1))
    refine doubleDual_injective hcomm (fun χ => ?_)
    rw [show χ (Additive.ofMul g) = charValue u hu 1 χ from (hspec χ).symm, charValue_one]
    simp
  map_mul' a b := by
    set ga := Classical.choose (NK.NUV2.RouteC.doubleDual_surjective (charValue u hu a)) with hga
    set gb := Classical.choose (NK.NUV2.RouteC.doubleDual_surjective (charValue u hu b)) with hgb
    set gab := Classical.choose (NK.NUV2.RouteC.doubleDual_surjective (charValue u hu (a * b)))
      with hgab
    have ha := Classical.choose_spec (NK.NUV2.RouteC.doubleDual_surjective (charValue u hu a))
    have hb := Classical.choose_spec (NK.NUV2.RouteC.doubleDual_surjective (charValue u hu b))
    have hab := Classical.choose_spec (NK.NUV2.RouteC.doubleDual_surjective (charValue u hu (a * b)))
    refine doubleDual_injective hcomm (fun χ => ?_)
    calc χ (Additive.ofMul gab) = charValue u hu (a * b) χ := (hab χ).symm
      _ = (charValue u hu a + charValue u hu b) χ := by rw [charValue_mul]
      _ = charValue u hu a χ + charValue u hu b χ := rfl
      _ = χ (Additive.ofMul ga) + χ (Additive.ofMul gb) := by rw [ha χ, hb χ]
      _ = χ (Additive.ofMul ga + Additive.ofMul gb) := (map_add χ _ _).symm
      _ = χ (Additive.ofMul (ga * gb)) := by
            rw [show Additive.ofMul (ga * gb) = Additive.ofMul ga + Additive.ofMul gb from rfl]

/-- **The defining character formula** of the level symbol:
`χ (θ_{E,u} a) = ι_u (a ∪ δχ)`. -/
theorem levelSymbol_apply (u : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)
    (hu : addOrderOf u = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)) (a : Fˣ)
    (χ : Additive (E ≃ₐ[F] E) →+ NK.NUV2.RouteC.qmodZ) :
    χ (Additive.ofMul (levelSymbol hcomm u hu a)) = charValue u hu a χ :=
  (Classical.choose_spec (NK.NUV2.RouteC.doubleDual_surjective (charValue u hu a)) χ).symm

end LevelSymbol

end NK.NUV2.RouteE
