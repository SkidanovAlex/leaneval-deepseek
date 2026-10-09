/-
# Tate duality in degrees `-2` and `1`: `H₁(G,M) ≅ H¹(G,M^∨)^∨`

For a finite group `G`, a prime `p` and a finite `𝔽_p[G]`-module `M`, the first homology of `G`
with coefficients in `M` is the `𝔽_p`-dual of the first cohomology of `G` with coefficients in the
contragredient module `M^∨ = Hom_{𝔽_p}(M, 𝔽_p)`:

`H₁(G, M) ≅ H¹(G, M^∨)^∨`.

This is the standard perfect Tate pairing `Ĥ^i(G, A) × Ĥ^{-1-i}(G, A^∨) → ℚ/ℤ` at `i = -2`, using
`H₁ = Ĥ^{-2}` and `H¹ = Ĥ¹` (see `Submission.Work.SSGRoute.H1Dual.tateDual_main`).

The proof in this file consists of two parts:

* **The naturality of the degree-`0` evaluation pairing** `(H₀(G,N))^∨ ≅ H⁰(G,N^∨)` in the
  coefficient module `N` (`H0DualMap_naturality` below). This is the one ingredient that
  `H1Dual.tateDual_main` takes as a hypothesis: the assembly there must be able to identify the
  transpose of the map `H₀(G,M') → H₀(G,Coind(M))` with the map
  `H⁰(G,Coind(M)^∨) → H⁰(G,(M')^∨)`.
  It is proved by combining the three naturality statements
  * `H0DualAux_natural`: the auxiliary pairing `(N_G)^∨ → (N^∨)^G`, `l ↦ l ∘ mk`, is natural;
  * `H0Iso_natural_hom`: the isomorphism `H₀(G,N) ≅ N_G` is natural (`groupHomology`
    `map_id_comp_H0Iso_hom`);
  * `H0Iso_natural_coh`: the isomorphism `H⁰(G,N) ≅ N^G` is natural (`groupCohomology`
    `map_id_comp_H0Iso_hom`).

* **The assembly** `H1_tateDual_clean`, which feeds this naturality to `tateDual_main`.

## References

* `Submission.Work.SSGRoute.H1Dual.Defs`: the coinduced resolution `0 → M' → Coind(M) → M → 0`
  and the contragredient.
* `Submission.Work.SSGRoute.H1Dual.LES`: the two dimension shifts.
* `Submission.Work.SSGRoute.H1Dual.Vanish`: acyclicity of `Coind(M)` and `Coind(M)^∨`.
* `Submission.Work.SSGRoute.H1Dual.DegreeZero`: the degree-`0` pairing `H0DualMap`.
* `Submission.Work.SSGRoute.H1Dual.Main`: the assembly `tateDual_main`.
-/
import Mathlib
import Submission.Work.SSGRoute.H1Dual.Main
import Submission.Work.SSGRoute.H1Dual.degreeZeroBijective
import Submission.Work.SSGRoute.H1Dual.dualSES_shortExact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

noncomputable section

variable {k : Type} [Field k] {G : Type} [Group G]

/-! ## Naturality of the degree-`0` evaluation pairing -/

/-- Evaluation of the map induced by a morphism on the invariants of the contragredient:
for `ψ` in `(Y^∨)^G` and `x : X`, the invariant `(f^∨)(ψ)` of `X^∨` takes `x` to `ψ (f x)`. -/
theorem invariantsFunctor_map_apply {X Y : Rep k G} (f : X ⟶ Y)
    (ψ : ↥((dualRep Y).ρ.invariants)) (x : X) :
    ((Rep.invariantsFunctor k G).map (dualHom f) ψ).1 x = (ψ.1) (Rep.Hom.hom f x) := by
  change (ModuleCat.Hom.hom ((Rep.invariantsFunctor k G).map (dualHom f)) ψ).1 x =
    ψ.1 (Rep.Hom.hom f x)
  rw [Rep.invariantsFunctor_map_hom]
  change (((Rep.Hom.hom (dualHom f)).toLinearMap) ψ.1) x = ψ.1 (Rep.Hom.hom f x)
  rw [show ((Rep.Hom.hom (dualHom f)).toLinearMap) ψ.1 =
      (ψ.1).comp (Rep.Hom.hom f).toLinearMap from dualHom_apply f ψ.1]
  rfl

/-- **Naturality of the auxiliary degree-`0` pairing** `(N_G)^∨ → (N^∨)^G`, `l ↦ l ∘ mk`:
for a morphism `f : X ⟶ Y` of representations the square

`(Y_G)^∨ --(f_G)^∨--> (X_G)^∨`

`  |                          |`

`(Y^∨)^G --(f^∨)^G--> (X^∨)^G`

commutes.  Both composites send a functional `l` to the invariant `x ↦ l (f_G (mk_X x))`; the
concrete input is the naturality of the quotient map `mk : N → N_G`. -/
theorem H0DualAux_natural {X Y : Rep k G} (f : X ⟶ Y)
    (l : Module.Dual k ((Rep.coinvariantsFunctor k G).obj Y)) :
    H0DualAux X ((ModuleCat.Hom.hom ((Rep.coinvariantsFunctor k G).map f)).dualMap l) =
      (Rep.invariantsFunctor k G).map (dualHom f) (H0DualAux Y l) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  simp only [H0DualAux, LinearMap.comp_apply, LinearMap.dualMap_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  rw [invariantsFunctor_map_apply]
  have hmk : ModuleCat.Hom.hom ((Rep.coinvariantsFunctor k G).map f)
        ((Representation.Coinvariants.mk X.ρ) x) =
      (Representation.Coinvariants.mk Y.ρ) (Rep.Hom.hom f x) := by
    have h := congrArg ModuleCat.Hom.hom ((Rep.coinvariantsMk k G).naturality f)
    simp only [ModuleCat.hom_comp, Rep.coinvariantsMk_app_hom] at h
    exact LinearMap.congr_fun h x
  erw [hmk]
  try rfl

/-- **Naturality of `H₀(G, ·) ≅ ·_G`**: for `f : X ⟶ Y`, the map induced by `f` on the zero-th
group homology corresponds to the map induced on the coinvariants. -/
theorem H0Iso_natural_hom {X Y : Rep k G} (f : X ⟶ Y) :
    ((Iso.toLinearEquiv (groupHomology.H0Iso Y)).toLinearMap).comp
      (ModuleCat.Hom.hom ((groupHomology.functor k G 0).map f))
    = (ModuleCat.Hom.hom ((Rep.coinvariantsFunctor k G).map f)).comp
      (Iso.toLinearEquiv (groupHomology.H0Iso X)).toLinearMap := by
  have h := congrArg ModuleCat.Hom.hom (groupHomology.map_id_comp_H0Iso_hom f)
  simp only [ModuleCat.hom_comp] at h
  simp only [Iso.toLinearMap_toLinearEquiv, groupHomology.functor_map]
  exact h

/-- **Naturality of `H⁰(G, ·) ≅ ·^G`**: for `f : X ⟶ Y`, the map induced by `f` on the zero-th
group cohomology corresponds to the restriction of invariants. -/
theorem H0Iso_natural_coh {X Y : Rep k G} (f : X ⟶ Y) :
    ((Iso.toLinearEquiv (groupCohomology.H0Iso Y)).toLinearMap).comp
      (ModuleCat.Hom.hom ((groupCohomology.functor k G 0).map f))
    = (ModuleCat.Hom.hom ((Rep.invariantsFunctor k G).map f)).comp
      (Iso.toLinearEquiv (groupCohomology.H0Iso X)).toLinearMap := by
  have h := congrArg ModuleCat.Hom.hom (groupCohomology.map_id_comp_H0Iso_hom f)
  simp only [ModuleCat.hom_comp] at h
  simp only [Iso.toLinearMap_toLinearEquiv, groupCohomology.functor_map]
  exact h

/-- Unfolding of the degree-`0` pairing `H0DualMap`:
`H0DualMap N = (H⁰(G,N^∨) ≅ (N^∨)^G)⁻¹ ∘ H0DualAux N ∘ ((H₀(G,N) ≅ N_G)⁻¹)^∨`. -/
theorem H0DualMap_apply (N : Rep k G) (z : Module.Dual k (groupHomology.H0 N)) :
    H0DualMap N z =
      (Iso.toLinearEquiv (groupCohomology.H0Iso (dualRep N))).symm
        (H0DualAux N
          ((LinearEquiv.dualMap (Iso.toLinearEquiv (groupHomology.H0Iso N)).symm) z)) := rfl

/-- **Naturality of the degree-`0` evaluation pairing** `(H₀(G,N))^∨ ≅ H⁰(G,N^∨)` in the
coefficient module `N`: for a morphism `f : X ⟶ Y` of representations, the square

`(H₀(G,Y))^∨ --(H₀(G,f))^∨--> (H₀(G,X))^∨`

`  |                                      |`

`H⁰(G,Y^∨) --H⁰(G,f^∨)--> H⁰(G,X^∨)`

commutes.

The proof reduces, through the natural isomorphisms `H₀(G,N) ≅ N_G` and `H⁰(G,N) ≅ N^G`, to the
naturality of the auxiliary pairing `H0DualAux` (`H0DualAux_natural`): both sides then compute a
functional `l : (Y_G)^∨` at `x : X` as `l (f_G (mk_X x))`. -/
theorem H0DualMap_naturality {X Y : Rep k G} (f : X ⟶ Y)
    (l : Module.Dual k (groupHomology.H0 Y)) :
    H0DualMap X ((ModuleCat.Hom.hom ((groupHomology.functor k G 0).map f)).dualMap l) =
      (ModuleCat.Hom.hom ((groupCohomology.functor k G 0).map (dualHom f)))
        (H0DualMap Y l) := by
  -- unfold the pairing on both sides
  rw [show H0DualMap X
        ((ModuleCat.Hom.hom ((groupHomology.functor k G 0).map f)).dualMap l) =
      (Iso.toLinearEquiv (groupCohomology.H0Iso (dualRep X))).symm
        (H0DualAux X ((LinearEquiv.dualMap
          (Iso.toLinearEquiv (groupHomology.H0Iso X)).symm)
            ((ModuleCat.Hom.hom ((groupHomology.functor k G 0).map f)).dualMap l)))
      from H0DualMap_apply X _]
  rw [show H0DualMap Y l =
      (Iso.toLinearEquiv (groupCohomology.H0Iso (dualRep Y))).symm
        (H0DualAux Y ((LinearEquiv.dualMap
          (Iso.toLinearEquiv (groupHomology.H0Iso Y)).symm) l))
      from H0DualMap_apply Y _]
  -- abbreviations for the maps appearing in the square
  set cX : groupHomology.H0 X ≃ₗ[k] (Rep.coinvariantsFunctor k G).obj X :=
    Iso.toLinearEquiv (groupHomology.H0Iso X) with hcX
  set cY : groupHomology.H0 Y ≃ₗ[k] (Rep.coinvariantsFunctor k G).obj Y :=
    Iso.toLinearEquiv (groupHomology.H0Iso Y) with hcY
  set dX : groupCohomology.H0 (dualRep X) ≃ₗ[k]
      ↥((dualRep X).ρ.invariants) :=
    Iso.toLinearEquiv (groupCohomology.H0Iso (dualRep X)) with hdX
  set dY : groupCohomology.H0 (dualRep Y) ≃ₗ[k]
      ↥((dualRep Y).ρ.invariants) :=
    Iso.toLinearEquiv (groupCohomology.H0Iso (dualRep Y)) with hdY
  set u : groupHomology.H0 X →ₗ[k] groupHomology.H0 Y :=
    ModuleCat.Hom.hom ((groupHomology.functor k G 0).map f) with hu
  set v : groupCohomology.H0 (dualRep Y) →ₗ[k]
      groupCohomology.H0 (dualRep X) :=
    ModuleCat.Hom.hom ((groupCohomology.functor k G 0).map (dualHom f)) with hv
  set fG : (Rep.coinvariantsFunctor k G).obj X →ₗ[k] (Rep.coinvariantsFunctor k G).obj Y :=
    ModuleCat.Hom.hom ((Rep.coinvariantsFunctor k G).map f) with hfG
  -- `u ∘ cX⁻¹ = cY⁻¹ ∘ fG`
  have hB' : ∀ x : groupHomology.H0 X, cY (u x) = fG (cX x) := by
    intro x
    have h := LinearMap.congr_fun (H0Iso_natural_hom (k := k) (G := G) f) x
    simp only [hu, hcY, hcX, hfG] at h ⊢
    exact h
  -- the transposed equation `(cX⁻¹)^∨ ∘ u^∨ = (fG)^∨ ∘ (cY⁻¹)^∨`
  have keyX : (LinearEquiv.dualMap cX.symm) (u.dualMap l) =
      fG.dualMap ((LinearEquiv.dualMap cY.symm) l) := by
    apply LinearMap.ext
    intro a
    simp only [LinearEquiv.dualMap_apply, LinearMap.dualMap_apply]
    have : u (cX.symm a) = cY.symm (fG a) := by
      rw [← LinearEquiv.symm_apply_apply cY (u (cX.symm a)), hB' (cX.symm a),
        LinearEquiv.apply_symm_apply]
    rw [this]
  erw [keyX]
  -- naturality of the auxiliary pairing
  rw [show H0DualAux X (fG.dualMap ((LinearEquiv.dualMap cY.symm) l)) =
      (Rep.invariantsFunctor k G).map (dualHom f)
        (H0DualAux Y ((LinearEquiv.dualMap cY.symm) l)) from
    H0DualAux_natural (k := k) (G := G) f ((LinearEquiv.dualMap cY.symm) l)]
  -- the cohomological square, inverted: `v ∘ dY⁻¹ = dX⁻¹ ∘ (f^∨)^G`
  have hC' : ∀ z : ↥((dualRep Y).ρ.invariants),
      v (dY.symm z) = dX.symm
        ((ModuleCat.Hom.hom ((Rep.invariantsFunctor k G).map (dualHom f))) z) := by
    intro z
    rw [← LinearEquiv.symm_apply_apply dX (v (dY.symm z))]
    rw [show dX (v (dY.symm z)) =
        (ModuleCat.Hom.hom ((Rep.invariantsFunctor k G).map (dualHom f)))
          (dY (dY.symm z)) from by
      have h := LinearMap.congr_fun
        (H0Iso_natural_coh (k := k) (G := G) (dualHom f)) (dY.symm z)
      simp only [hdY] at h
      exact h]
    rw [LinearEquiv.apply_symm_apply]
  erw [hC']

end

/-! ## Tate duality in degrees `-2` and `1` -/

/-- **Tate duality for a finite group, in degrees `-2` and `1`.**

For a finite group `G`, a prime `p` and a finite `𝔽_p[G]`-module `M`, the first homology of `G`
with coefficients `M` is the `𝔽_p`-dual of the first cohomology of `G` with coefficients in the
contragredient module `M^∨ = Hom_{𝔽_p}(M, 𝔽_p)`: `H₁(G, M) ≅ H¹(G, M^∨)^∨`.

This is the standard perfect Tate pairing `Ĥ^i(G, A) × Ĥ^{-1-i}(G, A^∨) → ℚ/ℤ` at `i = -2`
(using `H₁ = Ĥ^{-2}` and `H¹ = Ĥ¹`), restricted to finite coefficient modules of exponent `p`,
where `Ĥ^{-1-(-2)} = Ĥ¹` and the target `ℚ/ℤ` may be replaced by `𝔽_p` because `pM = 0`.

The proof is the assembly `H1Dual.tateDual_main`: the two dimension shifts along the coinduced
resolution `0 → M' → Coind(M) → M → 0` and its dual express `H₁(G,M)` as `ker (H₀(G,M') → H₀(G,Coind M))`
and `H¹(G,M^∨)` as the cokernel of `H⁰(G,Coind(M)^∨) → H⁰(G,(M')^∨)`, the middle terms being
acyclic; the degree-`0` evaluation pairing `(H₀)^∨ ≅ H⁰` identifies the two maps as transposes,
by the naturality `H0DualMap_naturality` proved in this file, and a final double dual finishes. -/
theorem H1_tateDual_clean {G : Type} [Group G] [Fintype G] (p : ℕ) [Fact p.Prime]
    (M : Rep (ZMod p) G) [Finite M.V] :
    Nonempty (groupHomology.H1 M ≃ₗ[ZMod p]
      Module.Dual (ZMod p) (groupCohomology.H1 (Rep.of M.ρ.dual))) := by
  exact H1Dual.tateDual_main M (H1Dual.dualSES_shortExact M)
    (fun {_ _} f l => H0DualMap_naturality f l)

end Work.SSGRoute
