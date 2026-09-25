import Mathlib
import Submission.NK.NUV2.RouteC.cup_pow
import Submission.NK.NUV2.RouteC.delta_qmodz
import Submission.NK.NUV2.RouteC.map_norm_eq_zero
import Submission.Commons.RepresentationTheory.GroupCohomology.subsingleton_groupCohomology_coind_bot
import Submission.Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_eq_of_fundamental_class

/-!
# The cup product with a norm is zero on `H²` (Route C, "`θ` kills norms")

For a finite Galois extension `E / F` with group `G = Gal(E/F)`, an element `a ∈ Fˣ` and a
character `χ : G → ℚ/ℤ`, the class

`a ∪ δχ = map (MonoidHom.id G) (powHom a) 2 (δχ) ∈ H²(G, Eˣ)`

(`powHom a` is the coefficient change `ℤ → Eˣ`, `n ↦ aⁿ`; `δ : H¹(G,ℚ/ℤ) ≅ H²(G,ℤ)` is the
connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0`) **vanishes whenever `a` is a norm**,
`a ∈ N_{E/F}(Eˣ)`.  This is the "kills norms" half of Tate's theorem / of the character formula
`χ(θ_L a) = inv_L(a ∪ δχ)`: it shows that the level Artin map `θ_L` factors through
`Fˣ ⧸ N_{E/F}(Eˣ)`.

## The proof

Write `a = N(y) = ∏_{σ ∈ G} σ(y)` for `y ∈ Eˣ`.  The `G`-module map `γ_a : ℤ → Eˣ`, `n ↦ aⁿ`
factors through the **regular representation** `ℤ[G]`:

* `s : ℤ ⟶ ℤ[G]` is the "trace" map `1 ↦ ∑_σ σ` (a `ℤ[G]`-module map because `∑_σ σ` is
  `G`-invariant);
* `φ : ℤ[G] ⟶ Eˣ` is Mathlib's `Rep.leftRegularHom A (ofMul y)`, i.e. the `ℤ[G]`-module map
  `σ ↦ σ(y)`;
* `φ ∘ s = γ_a`, since `φ (∑_σ σ) = ∏_σ σ(y) = N(y) = a`.

Since `ℤ[G]` is a free `ℤ[G]`-module of rank one, `H²(G, ℤ[G]) = 0`
(`subsingleton_groupCohomology_leftRegular`, from Shapiro's lemma for the coinduction from the
trivial subgroup and `Commons…leftRegularIsoCoind`), so `map (id) s 2 = 0` and hence
`map (id) (powHom a) 2 = map (id) s 2 ≫ map (id) φ 2 = 0`.

Note that the *individual* maps `s` and `φ` are genuinely needed here (the naive guess
"`powHom a` factors through the norm endomorphism `A.norm` of a `Rep`" is **false**: the map
`n ↦ yⁿ` is not `G`-equivariant).  Only the *composite* `φ ∘ s` is the `G`-module map we want,
and the factorization therefore happens through the free module `ℤ[G]`.
-/

open CategoryTheory CategoryTheory.Limits

set_option linter.style.haveILetI false

namespace NK.NUV2.RouteC

section LeftRegular

variable {G : Type} [Group G] [Fintype G]

/-- The trace element `∑_{σ ∈ G} σ ∈ ℤ[G]`, i.e. the norm element of the group algebra. -/
noncomputable def leftRegularTrace : MonoidAlgebra ℤ G := ∑ g : G, MonoidAlgebra.single g (1 : ℤ)

/-- The trace element of the regular representation is `G`-invariant. -/
lemma leftRegular_ρ_trace (τ : G) :
    (Rep.leftRegular ℤ G).ρ τ (leftRegularTrace (G := G)) = leftRegularTrace (G := G) := by
  unfold leftRegularTrace
  rw [map_sum]
  have h : ∀ σ : G, (Rep.leftRegular ℤ G).ρ τ (MonoidAlgebra.single σ (1 : ℤ))
      = MonoidAlgebra.single (τ * σ) (1 : ℤ) := by
    intro σ
    rw [Representation.ofMulAction_single]
    simp
  rw [Finset.sum_congr rfl (fun σ _ => h σ)]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) (fun σ : G => MonoidAlgebra.single (τ * σ) (1 : ℤ))
    (fun σ : G => MonoidAlgebra.single σ (1 : ℤ)) (fun σ => rfl)

/-- **The trace map `ℤ ⟶ ℤ[G]`, `1 ↦ ∑_{σ} σ`**, as a morphism of `ℤ[G]`-modules. -/
noncomputable def traceHom : Rep.trivial ℤ G ℤ ⟶ Rep.leftRegular ℤ G :=
  Rep.ofHom
    ⟨AddMonoidHom.toIntLinearMap
        { toFun := fun n : ℤ => n • leftRegularTrace (G := G)
          map_zero' := by simp
          map_add' := fun m n => add_zsmul _ m n }, fun τ => by
      apply LinearMap.ext
      intro n
      show (n • leftRegularTrace (G := G)) = (Rep.leftRegular ℤ G).ρ τ (n • leftRegularTrace (G := G))
      rw [map_zsmul, leftRegular_ρ_trace]⟩

lemma traceHom_apply (n : ℤ) :
    (traceHom (G := G)).hom.toLinearMap n = n • leftRegularTrace (G := G) := rfl

/-- **The regular representation has no positive cohomology**: `Hⁿ⁺¹(G, ℤ[G]) = 0`.

`ℤ[G]` is the coinduction of the trivial representation from the trivial subgroup
(`Commons…leftRegularIsoCoind`), and `Hⁿ⁺¹(G, Coind_1^G A) = Hⁿ⁺¹(1, A) = 0` by Shapiro's
lemma (`Commons…isZero_groupCohomology_coind_bot`). -/
theorem subsingleton_groupCohomology_leftRegular (n : ℕ) :
    Subsingleton (groupCohomology (Rep.leftRegular ℤ G) (n + 1)) := by
  have hz : IsZero (groupCohomology
      (Rep.coind (⊥ : Subgroup G).subtype (Rep.trivial ℤ (↥(⊥ : Subgroup G)) ℤ)) (n + 1)) :=
    Commons.RepresentationTheory.GroupCohomology.isZero_groupCohomology_coind_bot _ n
  have hiso : groupCohomology (Rep.leftRegular ℤ G) (n + 1) ≅ groupCohomology
      (Rep.coind (⊥ : Subgroup G).subtype (Rep.trivial ℤ (↥(⊥ : Subgroup G)) ℤ)) (n + 1) :=
    CategoryTheory.Iso.mk
      (groupCohomology.map (MonoidHom.id G) (NU.leftRegularIsoCoind G).hom (n + 1))
      (groupCohomology.map (MonoidHom.id G) (NU.leftRegularIsoCoind G).inv (n + 1))
      (by rw [← groupCohomology.map_id_comp (NU.leftRegularIsoCoind G).hom
            (NU.leftRegularIsoCoind G).inv (n + 1), Iso.hom_inv_id]
          simp only [Rep.res_id]
          rw [groupCohomology.map_id])
      (by rw [← groupCohomology.map_id_comp (NU.leftRegularIsoCoind G).inv
            (NU.leftRegularIsoCoind G).hom (n + 1), Iso.inv_hom_id]
          simp only [Rep.res_id]
          rw [groupCohomology.map_id])
  exact ModuleCat.subsingleton_of_isZero (IsZero.of_iso hz hiso)

end LeftRegular

section NormUnit

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

set_option backward.isDefEq.respectTransparency false in
/-- **The norm endomorphism of `Eˣ`** (as the `Gal(E/F)`-representation `Rep.ofAlgebraAutOnUnits`)
is the unit of `E` attached to `N_{E/F}`: for `y ∈ Eˣ`,

`A.norm (ofMul y) = ofMul (algebraMap (N_{E/F} y))`.

This is Mathlib's `groupCohomology.norm_ofAlgebraAutOnUnits_eq`
(`(∏ σ) • y = N_{E/F}(y)`), transported to the unit at hand. -/
lemma norm_hom_ofMul_eq (y : Eˣ) :
    (Rep.ofAlgebraAutOnUnits F E).norm.hom (Additive.ofMul y : Additive Eˣ)
      = Additive.ofMul (Units.map (algebraMap F E).toMonoidHom
          (Units.map (Algebra.norm F) y)) := by
  have h1 : Additive.toMul ((Rep.ofAlgebraAutOnUnits F E).norm.hom (Additive.ofMul y : Additive Eˣ))
      = Units.map (algebraMap F E).toMonoidHom (Units.map (Algebra.norm F) y) := by
    apply Units.ext
    have h := groupCohomology.norm_ofAlgebraAutOnUnits_eq (K := F) (L := E) y
    rw [Rep.toAdditive_symm_apply, Rep.toAdditive_apply] at h
    simp only [Units.coe_map]
    exact h
  rw [← h1]
  exact (Additive.ofMul.apply_symm_apply _).symm

set_option backward.isDefEq.respectTransparency false in
/-- **The factorization of the cup product with a norm through `ℤ[G]`**: for `y ∈ Eˣ`,

`powHom (N(y)) = traceHom ≫ leftRegularHom A (y)`.

The right hand side is the composite of the trace map `ℤ ⟶ ℤ[G]` with the `ℤ[G]`-module map
`ℤ[G] ⟶ Eˣ` sending `σ ↦ σ(y)`; on `1` it takes the value `∏_σ σ(y) = N(y)`. -/
lemma powHom_eq_traceHom_comp_leftRegularHom (y : Eˣ) :
    powHom (F := F) (E := E) (Units.map (Algebra.norm F) y)
      = traceHom (G := E ≃ₐ[F] E)
        ≫ Rep.leftRegularHom (Rep.ofAlgebraAutOnUnits F E) (Additive.ofMul y : Additive Eˣ) := by
  have hkey : (Rep.leftRegularHom (Rep.ofAlgebraAutOnUnits F E) (Additive.ofMul y : Additive Eˣ)).hom
      (leftRegularTrace (G := E ≃ₐ[F] E))
      = Additive.ofMul (Units.map (algebraMap F E).toMonoidHom
          (Units.map (Algebra.norm F) y)) := by
    rw [leftRegularTrace, map_sum]
    have h2 : ∀ σ : E ≃ₐ[F] E,
        (Rep.leftRegularHom (Rep.ofAlgebraAutOnUnits F E) (Additive.ofMul y : Additive Eˣ)).hom
          (MonoidAlgebra.single σ (1 : ℤ))
        = (Rep.ofAlgebraAutOnUnits F E).ρ σ (Additive.ofMul y : Additive Eˣ) := by
      intro σ
      rw [Rep.leftRegularHom_hom_single]
      simp
    rw [Finset.sum_congr rfl (fun σ _ => h2 σ)]
    exact ((norm_apply_eq_sum (A := Rep.ofAlgebraAutOnUnits F E)
        (Additive.ofMul y : Additive Eˣ)).symm).trans (norm_hom_ofMul_eq y)
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro n
  show (powHom (F := F) (E := E) (Units.map (Algebra.norm F) y)).hom.toLinearMap n
    = (Rep.leftRegularHom (Rep.ofAlgebraAutOnUnits F E) (Additive.ofMul y : Additive Eˣ)).hom.toLinearMap
        ((traceHom (G := E ≃ₐ[F] E)).hom.toLinearMap n)
  rw [show (powHom (F := F) (E := E) (Units.map (Algebra.norm F) y)).hom.toLinearMap n
      = n • (Additive.ofMul (Units.map (algebraMap F E).toMonoidHom
          (Units.map (Algebra.norm F) y)) : Additive Eˣ) from by
    unfold powHom
    simp only [Rep.hom_ofHom]
    rfl]
  rw [traceHom_apply, map_zsmul]
  congr 1
  exact hkey.symm

end NormUnit

section Main

/-- **The cup product with a norm vanishes on `H²`.**  For a finite Galois extension `E/F`, a
character `χ : Gal(E/F) → ℚ/ℤ` and `a ∈ Fˣ` which is a norm from `E`, the class
`a ∪ δχ = map (MonoidHom.id G) (powHom a) 2 (δχ) ∈ H²(Gal(E/F), Eˣ)` is zero.

This is the "`θ` kills norms" step of the character-formula construction of the local Artin map:
it shows `a ∪ δχ = 0` for `a ∈ N_{E/F}(Eˣ)`, hence that the level symbol `θ_E` factors through
`Fˣ ⧸ N_{E/F}(Eˣ)`. -/
theorem map_powHom_eq_zero_of_mem_normGroup {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (χ : Additive (E ≃ₐ[F] E) →+ NK.NUV2.RouteC.qmodZ)
    (a : Fˣ) (ha : a ∈ MonoidHom.range (Units.map (Algebra.norm F : E →* F))) :
    groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
        (NK.NUV2.RouteC.powHom (F := F) (E := E) a) 2
        (NK.NUV2.RouteC.deltaHomChar (E ≃ₐ[F] E) χ) = 0 := by
  obtain ⟨y, hy⟩ := ha
  rw [← hy]
  have hfac : powHom (F := F) (E := E) (Units.map (Algebra.norm F) y)
      = traceHom (G := E ≃ₐ[F] E) ≫ Rep.leftRegularHom (Rep.ofAlgebraAutOnUnits F E)
          (Additive.ofMul y : Additive Eˣ) := powHom_eq_traceHom_comp_leftRegularHom y
  rw [hfac, groupCohomology.map_id_comp]
  haveI : Subsingleton (groupCohomology (Rep.leftRegular ℤ (E ≃ₐ[F] E)) 2) :=
    subsingleton_groupCohomology_leftRegular (G := E ≃ₐ[F] E) 1
  have hzero : (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
      (traceHom (G := E ≃ₐ[F] E)) 2) (deltaHomChar (E ≃ₐ[F] E) χ) = 0 :=
    Subsingleton.elim _ _
  change (ConcreteCategory.hom (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
      (Rep.leftRegularHom (Rep.ofAlgebraAutOnUnits F E) (Additive.ofMul y : Additive Eˣ)) 2))
      ((ConcreteCategory.hom (groupCohomology.map (MonoidHom.id (E ≃ₐ[F] E))
        (traceHom (G := E ≃ₐ[F] E)) 2)) (deltaHomChar (E ≃ₐ[F] E) χ)) = 0
  rw [hzero]
  exact map_zero _

end Main

end NK.NUV2.RouteC
