import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Submission.NK.Reconstruct.gammaBaseChange
import Submission.NK.Reconstruct.moduleFinite_gamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `π_{L/K} : Γ_L → Γ_K` is `ℤ_ℓ`-linear

`NK.Reconstruct.gammaBaseChangeHom ℓ L` is the base-change map of Shimizu's §4 on the ℓ-adic
abelianisations, induced by the inclusion `G_L ⊆ G_K`; both `Γ_L` and `Γ_K` are `ℤ_ℓ`-modules whose
scalar action is *componentwise* on the finite levels (`NK.Reconstruct.instModuleAdditiveGamma`).
This file proves that `π_{L/K}` is a morphism of `ℤ_ℓ`-modules
(`NK.Reconstruct.gammaBaseChangeHom_smul`, `NK.Reconstruct.gammaBaseChangeLinear`).

This is what makes `ker π_{L/K}` — and, after descent, the kernel of the induced map on the
Hausdorff quotients `Γ_K ↠ Γ_K^{tf}` — a `ℤ_ℓ`-submodule, which is what the *rank* computations of
Shimizu's §4 (Lemma 4f.1, Proposition 4f.5) are about.

## The two computations

The projection formula `proj_N (π f) = ellRestrict_N ∘ ellIncl ∘ proj_{N ⊔ L} f` reduces the claim
to the linearity of its three factors:

* `Gamma.proj` is linear by definition of the scalar action (it acts componentwise);
* `ellRestrict` is linear: `NK.Reconstruct.ellRestrictAdd_smul`;
* `ellIncl` is linear: `NK.Reconstruct.ellInclAdd_smul`, proved here.

The proof of `ellInclAdd_smul` is the same *modular* computation as `ellRestrictAdd_smul`: writing
the scalar action on a finite ℓ-part as a power map with exponent `(toZModPow N a).val`
(`NK.Reconstruct.smul_ellPart_eq_pow`), the two exponents `A₁ = (toZModPow N₁ a).val` and
`A₂ = (toZModPow N₂ a).val` for the source and target exponents `N₁`, `N₂` have to be compared only
*modulo the order* of the image element `z = Abelianization.map (levelInclHom L M h) y`; that order
divides both `ℓ ^ N₁` (image of an element of the source ℓ-part) and `ℓ ^ N₂` (the image lies in the
target ℓ-part), hence divides `ℓ ^ min N₁ N₂`, and the two exponents agree modulo `ℓ ^ min N₁ N₂`
by the compatibility `PadicInt.cast_toZModPow` of the reductions.  (Note that the two exponents
`N₁`, `N₂` are *not* ordered in general, unlike the situation for `ellRestrict`.)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NK.Reconstruct

open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsGalois K K']

/-- The additive form of the level inclusion `NK.Reconstruct.ellIncl`. -/
noncomputable def ellInclAdd (ℓ : ℕ) (L M : FrobLevel K K') (h : L.L ≤ M.L) :
    Additive (LevelEllPart (K := ↥L.L) (K' := K') (levelExtend L M h).L ℓ) →+
      Additive (LevelEllPart (K := K) (K' := K') M.L ℓ) :=
  (ellIncl ℓ L M h).toAdditive

@[simp] theorem ellInclAdd_apply (ℓ : ℕ) (L M : FrobLevel K K') (h : L.L ≤ M.L)
    (x : Additive (LevelEllPart (K := ↥L.L) (K' := K') (levelExtend L M h).L ℓ)) :
    Additive.toMul (ellInclAdd ℓ L M h x)
      = ellIncl ℓ L M h (Additive.toMul x) := rfl

/-- **The level inclusion `ellIncl` is `ℤ_ℓ`-linear.**  See the module docstring for the modular
comparison of the two exponents. -/
theorem ellInclAdd_smul (ℓ : ℕ) [Fact ℓ.Prime] (L M : FrobLevel K K') (h : L.L ≤ M.L)
    (a : PadicInt ℓ)
    (x : Additive (LevelEllPart (K := ↥L.L) (K' := K') (levelExtend L M h).L ℓ)) :
    ellInclAdd ℓ L M h (a • x) = a • ellInclAdd ℓ L M h x := by
  obtain ⟨y, rfl⟩ : ∃ y : LevelEllPart (K := ↥L.L) (K' := K') (levelExtend L M h).L ℓ,
      Additive.ofMul y = x := ⟨Additive.toMul x, ofMul_toMul x⟩
  set N₁ := ellExp (LevelAbelianization (levelExtend L M h).L) ℓ with hN₁
  set N₂ := ellExp (LevelAbelianization M.L) ℓ with hN₂
  set w : LevelEllPart M.L ℓ := ellIncl ℓ L M h y with hw
  have hL : a • (Additive.ofMul y) = Additive.ofMul (y ^ (PadicInt.toZModPow (p := ℓ) N₁ a).val) :=
    smul_ellPart_eq_pow (A := LevelAbelianization (levelExtend L M h).L) ℓ a y
  have hinc : ellInclAdd ℓ L M h (Additive.ofMul (y ^ (PadicInt.toZModPow (p := ℓ) N₁ a).val))
      = Additive.ofMul (w ^ (PadicInt.toZModPow (p := ℓ) N₁ a).val) := by
    show Additive.ofMul (ellIncl ℓ L M h (y ^ (PadicInt.toZModPow (p := ℓ) N₁ a).val)) = _
    rw [map_pow]
  have hR : a • (ellInclAdd ℓ L M h (Additive.ofMul y))
      = Additive.ofMul (w ^ (PadicInt.toZModPow (p := ℓ) N₂ a).val) := by
    show a • Additive.ofMul (ellIncl ℓ L M h y) = _
    rw [smul_ellPart_eq_pow (A := LevelAbelianization M.L) ℓ a w]
  rw [hL, hinc, hR]
  refine Subtype.ext ?_
  -- the two exponents agree modulo the order of the underlying element `z`
  have hy : y ^ (ℓ ^ N₁) = 1 := pow_ellExp_eq_one (A := LevelAbelianization _) ℓ y
  have hz1 : (w : LevelAbelianization M.L) ^ (ℓ ^ N₁) = 1 := by
    have h1 : w ^ (ℓ ^ N₁) = 1 := by
      rw [hw, ← map_pow, hy, map_one]
    have h2 := map_pow (Subgroup.subtype (ellPart (LevelAbelianization M.L) ℓ)) w (ℓ ^ N₁)
    rw [h1, map_one] at h2
    exact h2.symm
  have hz2 : (w : LevelAbelianization M.L) ^ (ℓ ^ N₂) = 1 := by
    have h1 : w ^ (ℓ ^ N₂) = 1 := pow_ellExp_eq_one (A := LevelAbelianization M.L) ℓ w
    have h2 := map_pow (Subgroup.subtype (ellPart (LevelAbelianization M.L) ℓ)) w (ℓ ^ N₂)
    rw [h1, map_one] at h2
    exact h2.symm
  have hdiv1 : orderOf (w : LevelAbelianization M.L) ∣ ℓ ^ N₁ :=
    orderOf_dvd_iff_pow_eq_one.mpr hz1
  have hdiv2 : orderOf (w : LevelAbelianization M.L) ∣ ℓ ^ N₂ :=
    orderOf_dvd_iff_pow_eq_one.mpr hz2
  have hord : orderOf (w : LevelAbelianization M.L) ∣ ℓ ^ min N₁ N₂ := by
    rcases le_total N₁ N₂ with hle | hle
    · rwa [min_eq_left hle]
    · rwa [min_eq_right hle]
  have hmod : ((PadicInt.toZModPow (p := ℓ) N₁ a).val : ℕ)
      ≡ (PadicInt.toZModPow (p := ℓ) N₂ a).val [MOD ℓ ^ min N₁ N₂] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    have e1 : (((PadicInt.toZModPow (p := ℓ) N₁ a).val : ℕ) : ZMod (ℓ ^ min N₁ N₂))
        = PadicInt.toZModPow (p := ℓ) (min N₁ N₂) a := by
      rw [← ZMod.cast_natCast (R := ZMod (ℓ ^ min N₁ N₂)) (m := ℓ ^ min N₁ N₂) (n := ℓ ^ N₁)
        (pow_dvd_pow ℓ (min_le_left N₁ N₂)) ((PadicInt.toZModPow (p := ℓ) N₁ a).val)]
      rw [ZMod.natCast_zmod_val]
      exact PadicInt.cast_toZModPow (min N₁ N₂) N₁ (min_le_left N₁ N₂) a
    have e2 : (((PadicInt.toZModPow (p := ℓ) N₂ a).val : ℕ) : ZMod (ℓ ^ min N₁ N₂))
        = PadicInt.toZModPow (p := ℓ) (min N₁ N₂) a := by
      rw [← ZMod.cast_natCast (R := ZMod (ℓ ^ min N₁ N₂)) (m := ℓ ^ min N₁ N₂) (n := ℓ ^ N₂)
        (pow_dvd_pow ℓ (min_le_right N₁ N₂)) ((PadicInt.toZModPow (p := ℓ) N₂ a).val)]
      rw [ZMod.natCast_zmod_val]
      exact PadicInt.cast_toZModPow (min N₁ N₂) N₂ (min_le_right N₁ N₂) a
    rw [e1, e2]
  exact pow_eq_pow_iff_modEq.mpr (Nat.ModEq.of_dvd hord hmod)

/-- **The base-change map `π_{L/K} : Γ_L → Γ_K` is `ℤ_ℓ`-linear.**

This is the projection-formula computation: on the level `N` of `K'/K` the left-hand side is
`ellRestrict ∘ ellIncl ∘ proj_{N ⊔ L}` applied to the component of `a • f`, which is
`a • f_{N ⊔ L}` by definition of the componentwise scalar action, and both `ellIncl`
(`NK.Reconstruct.ellInclAdd_smul`) and `ellRestrict`
(`NK.Reconstruct.ellRestrictAdd_smul`) are linear. -/
theorem gammaBaseChangeHom_smul (ℓ : ℕ) [Fact ℓ.Prime] (L : FrobLevel K K') (a : PadicInt ℓ)
    (f : Additive (Gamma ↥L.L K' ℓ)) :
    MonoidHom.toAdditive (gammaBaseChangeHom (K := K) (K' := K') ℓ L) (a • f)
      = a • MonoidHom.toAdditive (gammaBaseChangeHom (K := K) (K' := K') ℓ L) f := by
  refine gamma_ext_add (K := K) (K' := K') ℓ (f := _) (g := _) (fun N => ?_)
  -- component of the left-hand side
  have hleft : Additive.ofMul (Gamma.proj N (Additive.toMul
        (MonoidHom.toAdditive (gammaBaseChangeHom (K := K) (K' := K') ℓ L) (a • f))))
      = Additive.ofMul (ellRestrict ℓ N (L.sup N) (FrobLevel.le_sup_right L N)
          (Additive.toMul (ellInclAdd ℓ L (L.sup N) (FrobLevel.le_sup_left L N)
            (a • Additive.ofMul (Gamma.proj (levelExtend L (L.sup N) (FrobLevel.le_sup_left L N))
              (Additive.toMul f)))))) := rfl
  have hright : Additive.ofMul (Gamma.proj N (Additive.toMul
        (a • MonoidHom.toAdditive (gammaBaseChangeHom (K := K) (K' := K') ℓ L) f)))
      = Additive.ofMul (a • Additive.ofMul (ellRestrict ℓ N (L.sup N)
          (FrobLevel.le_sup_right L N)
          (ellIncl ℓ L (L.sup N) (FrobLevel.le_sup_left L N)
            (Gamma.proj (levelExtend L (L.sup N) (FrobLevel.le_sup_left L N))
              (Additive.toMul f))))) := rfl
  rw [hleft, hright]
  -- rewrite the level inclusion and the restriction through their linearity
  have h1 : Additive.toMul (ellInclAdd ℓ L (L.sup N) (FrobLevel.le_sup_left L N)
        (a • Additive.ofMul (Gamma.proj (levelExtend L (L.sup N) (FrobLevel.le_sup_left L N))
          (Additive.toMul f))))
      = a • Additive.ofMul (ellIncl ℓ L (L.sup N) (FrobLevel.le_sup_left L N)
          (Gamma.proj (levelExtend L (L.sup N) (FrobLevel.le_sup_left L N))
            (Additive.toMul f))) := by
    rw [ellInclAdd_smul]
    rfl
  rw [h1]
  congr 1
  exact ellRestrictAdd_smul ℓ (L := N) (M := L.sup N) (FrobLevel.le_sup_right L N) a _

/-- **The base-change map `π_{L/K} : Γ_L → Γ_K` is a morphism of `ℤ_ℓ`-modules.** -/
theorem gammaBaseChangeLinear (ℓ : ℕ) [Fact ℓ.Prime] (L : FrobLevel K K') :
    ∃ F : Additive (Gamma ↥L.L K' ℓ) →ₗ[PadicInt ℓ] Additive (Gamma K K' ℓ),
      ∀ f, F f = MonoidHom.toAdditive (gammaBaseChangeHom (K := K) (K' := K') ℓ L) f :=
  ⟨{ toFun := MonoidHom.toAdditive (gammaBaseChangeHom (K := K) (K' := K') ℓ L)
     map_add' := fun f g => map_add _ f g
     map_smul' := fun a f => gammaBaseChangeHom_smul ℓ L a f }, fun _ => rfl⟩

end NK.Reconstruct
