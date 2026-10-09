import Mathlib
import Submission.Work.SSGRoute.ZConstruction.levelK_canonicalPairing
import Submission.Work.SSGRoute.LT_abGal_kills_of_artin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bilinearity of the canonical level-`K` local pairing, and the family of forms

The canonical pairing `levelKCanonPairing` of `levelK_canonicalPairing.lean` is constructed as

`x ↦ χ_x ↦ χ̄_x ∘ rec_A`  and  `y ↦ β_y`,

i.e. a *linear* map in `x` (the character of a sum of classes is the product of the characters —
`levelKModelIso_add`, transported along the local Galois identification and the abelianisation) and
a *linear* map in `y` (the local Kummer class of a sum is the product of the Kummer classes, the
dictionary being a monoid isomorphism), followed by the bilinear evaluation of a character at a
group element.

This file makes that explicit:

* `levelKCharLevelKToGal_add`, `levelKCharToAbGal_mul`, `levelKPairMul_mul` — additivity in `x`;
* `levelKLocalClass_mul` — additivity in `y`;
* `levelKCanonFormA` — the pairing at a fixed place `A` as a `ZMod p`-bilinear map
  `V_A →ₗ V_A →ₗ ZMod p`;
* `levelKCanonFamily` — the same, packaged as a function of the *subgroup*
  `H = levelKLocalGroup k Ω K A` (the shape the gate consumes), extended by `0` elsewhere.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ p}
  {A : ValuationSubring Ω}

/-- Coefficients of a product of locally constant characters: the product in the subgroup
`lcHoms` is the pointwise product of the underlying monoid homomorphisms. -/
theorem lcHoms_coe_mul {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    (χ ψ : ↥(Work.SSGRoute.lcHoms p Γ)) :
    (↑(χ * ψ) : Γ →* Multiplicative (ZMod p)) = ↑χ * ↑ψ := rfl

/-- **Additivity of the transported character**: the character of a sum of level-`K` local classes
is the product of the characters, transported to the completion. -/
theorem levelKCharLevelKToGal_add (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x x' : Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A)) :
    levelKCharLevelKToGal (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK (x + x') =
      levelKCharLevelKToGal (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x *
        levelKCharLevelKToGal (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x' := by
  simp only [levelKCharLevelKToGal, levelKModelIso_add, map_mul]

/-- **Multiplicativity of the abelianised character.**  Two characters of `Gal(κ^ab/κ)` are equal
as soon as they are equal after composition with the restriction to `Gal(κ̄/κ)`, which is
surjective. -/
theorem levelKCharToAbGal_mul (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x x' : Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A)) :
    levelKCharToAbGal (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK (x + x') =
      levelKCharToAbGal (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x *
        levelKCharToAbGal (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x' := by
  refine Subtype.ext (MonoidHom.ext fun σ => ?_)
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := Work.SSGRoute.ZDataMup.mupCompletion
    (K := K) A hAK) (K₁ := NK.LocalReciprocity.maxAbelianSubext
      (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)
      (SeparableClosure (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)))
    (SeparableClosure (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)) σ
  have h := levelKCharToAbGal_spec (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK (x + x') τ
  have h2 := levelKCharToAbGal_spec (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x τ
  have h3 := levelKCharToAbGal_spec (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x' τ
  have h4 := levelKCharLevelKToGal_add (A := A) hA hAK x x'
  simp only [h, h2, h3, h4, lcHoms_coe_mul, MonoidHom.mul_apply]

/-- **Additivity of the local pairing in the first variable.** -/
theorem levelKPairMul_mul (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x x' : Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A)) :
    levelKPairMul (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK (x + x') =
      levelKPairMul (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x *
        levelKPairMul (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x' := by
  refine MonoidHom.ext fun c => ?_
  induction c using QuotientGroup.induction_on with
  | H a =>
    simp only [levelKPairMul, QuotientGroup.lift_mk', MonoidHom.mul_apply,
      MonoidHom.comp_apply, levelKCharToAbGal_mul, lcHoms_coe_mul]

/-- **Additivity of the local Kummer class**: the Kummer class of a sum of level-`K` local classes is
the product of the Kummer classes (the model identification and the Kummer dictionary are monoid
isomorphisms). -/
theorem levelKLocalClass_mul (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (y y' : Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A)) :
    levelKLocalClass (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
        (A := A) hA hAK (y + y') =
      levelKLocalClass (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
        (A := A) hA hAK y *
      levelKLocalClass (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
        (A := A) hA hAK y' := by
  simp only [levelKLocalClass, levelKModelIso_add, map_mul]

/-- **Additivity of the canonical pairing in the second variable** (the local Kummer class is a
group homomorphism). -/
theorem levelKCanonPairing_add_right (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x y y' : Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A)) :
    levelKCanonPairing (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
        (A := A) hA hAK x (y + y') =
      levelKCanonPairing (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
        (A := A) hA hAK x y +
      levelKCanonPairing (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
        (A := A) hA hAK x y' := by
  simp only [levelKCanonPairing, levelKLocalClass_mul, map_mul, toAdd_mul]

/-- **Additivity of the canonical pairing in the first variable** (the character of a sum is the
product of the characters). -/
theorem levelKCanonPairing_add_left (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x x' y : Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A)) :
    levelKCanonPairing (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
        (A := A) hA hAK (x + x') y =
      levelKCanonPairing (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
        (A := A) hA hAK x y +
      levelKCanonPairing (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
        (A := A) hA hAK x' y := by
  simp only [levelKCanonPairing, levelKPairMul_mul, MonoidHom.mul_apply, toAdd_mul]

/-- **The canonical local pairing at a fixed place, as a bilinear form.** -/
noncomputable def levelKCanonFormA (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A) →ₗ[ZMod p]
      (Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A) →ₗ[ZMod p] ZMod p) :=
  (AddMonoidHom.mk' (fun x =>
      (AddMonoidHom.mk' (fun y => levelKCanonPairing (p := p) (k := k) (Ω := Ω) (K := K)
          (ζ := ζ) (hζ := hζ) (A := A) hA hAK x y)
        (fun y y' => levelKCanonPairing_add_right (p := p) (k := k) (Ω := Ω) (K := K)
          (ζ := ζ) (hζ := hζ) (A := A) hA hAK x y y')).toZModLinearMap (n := p))
    (fun x x' => by
      refine LinearMap.ext fun y => ?_
      exact levelKCanonPairing_add_left (p := p) (k := k) (Ω := Ω) (K := K)
        (ζ := ζ) (hζ := hζ) (A := A) hA hAK x x' y)).toZModLinearMap (n := p)

/-- **The canonical family of local forms**, as a function of the level-`K` local group
`H = levelKLocalGroup k Ω K A` — the shape the gate consumes — extended by `0` at the subgroups
which are not level-`K` local groups. -/
noncomputable def levelKCanonFamily (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Work.SSGRoute.H1loc p k Ω K (ZMod p) H →ₗ[ZMod p]
      (Work.SSGRoute.H1loc p k Ω K (ZMod p) H →ₗ[ZMod p] ZMod p) := by
  classical
  exact if h : ∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = levelKLocalGroup k Ω K A
    then h.choose_spec.2.symm ▸ levelKCanonFormA (p := p) (k := k) (Ω := Ω) (K := K)
      (ζ := ζ) (hζ := hζ) (A := h.choose) h.choose_spec.1
        (isFinPlace_of_isFinPlace_below (K := K) (A := h.choose) h.choose_spec.1)
    else 0

/-- **The local Kummer class map is surjective** (the model identification and the level-`K` local
Kummer dictionary are bijective). -/
theorem levelKLocalClass_surjective (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) :
    Function.Surjective (levelKLocalClass (p := p) (k := k) (Ω := Ω) (K := K)
      (ζ := ζ) (hζ := hζ) (A := A) hA hAK) := by
  intro c
  obtain ⟨χ, rfl⟩ := (Work.SSGRoute.ZDataMup.mupKummerEquiv (p := p) (k := k) (Ω := Ω) (K := K)
    (ζ := ζ) (hζ := hζ) (A := A) hA hAK).symm.surjective c
  obtain ⟨y, rfl⟩ := (levelKModelIso_bijective (p := p) (k := k) (Ω := Ω) (K := K)
    (A := A) hA).2 χ
  exact ⟨y, rfl⟩

/-- **First-variable non-degeneracy of the canonical local pairing**: a level-`K` local class which
pairs trivially with everything is zero.  This is the density of the image of the local Artin map
(`LT_abGal_kills_of_artin`) together with the bijectivity of the model identification and of the
Kummer dictionary. -/
theorem levelKCanonPairing_nondegenerate (hA : SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (x : Work.SSGRoute.H1loc p k Ω K (ZMod p) (levelKLocalGroup k Ω K A))
    (hx : ∀ y, levelKCanonPairing (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
      (A := A) hA hAK x y = 0) :
    x = 0 := by
  -- the multiplicative pairing is trivial
  have h1 : levelKPairMul (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x = 1 := by
    refine MonoidHom.ext fun c => ?_
    obtain ⟨y, rfl⟩ := levelKLocalClass_surjective (p := p) (k := k) (Ω := Ω) (K := K)
      (ζ := ζ) (hζ := hζ) (A := A) hA hAK c
    refine Multiplicative.toAdd.injective ?_
    simpa only [levelKCanonPairing, MonoidHom.one_apply, toAdd_one] using hx y
  -- hence the abelianised character is trivial (density of the local Artin image)
  have h2 : (levelKCharToAbGal (p := p) (k := k) (Ω := Ω) (K := K)
      (A := A) hA hAK x).1 = 1 := by
    refine Work.SSGRoute.LT_abGal_kills_of_artin
      (Work.SSGRoute.ZDataMup.mupArtinReciprocity (K := K) A hAK) p
      (levelKCharToAbGal (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x) ?_
    intro a
    have h3 : levelKPairMul (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x
        ((a : (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)ˣ) :
          (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)ˣ ⧸
            (powMonoidHom p : (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)ˣ →*
              (Work.SSGRoute.ZDataMup.mupCompletion (K := K) A hAK)ˣ).range)
        = (levelKCharToAbGal (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x).1
            (Work.SSGRoute.ZDataMup.mupRec (K := K) A hAK a) := rfl
    rw [h1, MonoidHom.one_apply] at h3
    exact h3.symm
  -- hence the character at the completion is trivial
  have h4 : levelKCharLevelKToGal (p := p) (k := k) (Ω := Ω) (K := K)
      (A := A) hA hAK x = 1 := by
    refine Subtype.ext (MonoidHom.ext fun σ => ?_)
    rw [← levelKCharToAbGal_spec (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA hAK x σ, h2]
    rfl
  -- hence the model identification kills `x`
  have h5 : levelKModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x = 1 := by
    refine (levelKLocalGalTransport (p := p) (k := k) (Ω := Ω) (K := K) (A := A)
      hAK).injective ?_
    rw [map_one]
    exact h4
  have h6 : levelKModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA x =
      levelKModelIso (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA 0 := by
    rw [h5, levelKModelIso_zero]
  exact (levelKModelIso_bijective (p := p) (k := k) (Ω := Ω) (K := K) (A := A) hA).1 h6

end

end Work.SSGRoute.ZConstruction
