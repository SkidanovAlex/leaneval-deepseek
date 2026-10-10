import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Basic
import Submission.Work.CohomologicallyTrivial.pgroup_invariants_ne_bot
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Right detection: a nonzero `p`-torsion representation of a `p`-group maps onto `𝔽_p`

Let `p` be prime, `D` a finite `p`-group, and `M` a finite nontrivial representation of `D` over
`Coeff = ULift ℤ` on which `p` acts as `0` (so that `M` is really a `ZMod p`-representation).  Then
there is a surjective `D`-equivariant `Coeff`-linear map `M ⟶ 𝔽_p` (the trivial representation).

This is the "fixed functional" input of the design `DESIGN_E7B.md` (node `X2`/`rightDetect_pgroup`
and its consumers): a nonzero `M` has a nonzero `D`-fixed functional, and a nonzero functional to
the one-dimensional `𝔽_p` is automatically surjective.

## Proof

* `p • m = 0` makes `M.V` a `ZMod p`-module (`AddCommGroup.zmodModule`), and every `ρ g` is
  `ZMod p`-linear (`ZMod.map_smul`), so `M.V` becomes a `ZMod p`-representation `ρz` of `D`.
* The contragredient representation `ρz.dual` on `Module.Dual (ZMod p) M.V` is nontrivial
  (`instNontrivialLinearMapId`), so `pgroup_invariants_ne_bot` produces a nonzero `D`-fixed
  functional `f`.
* A fixed functional is `D`-invariant pointwise, and every `ZMod p`-linear functional is
  `Coeff`-linear (`Int.cast_smul_eq_zsmul`, since `Module (ULift ℤ) M.V` is the `ℤ`-module
  structure along the ring isomorphism `ULift ℤ ≃+* ℤ`), so `f` gives a morphism
  `M ⟶ Rep.trivial Coeff D (ZMod p)`.
* It is onto because its image is a nonzero subspace of the one-dimensional `𝔽_p`.

Two instance diamonds have to be handled explicitly:
* the `Module (ZMod p) M.V` structure must be bound to a *variable* before being installed as an
  instance, otherwise the elaborator inlines the `AddCommGroup.zmodModule` term into every
  `M.V →ₗ[ZMod p] _` type;
* `Module Coeff M.V` has to be pinned to `M.hV2`, since otherwise type class search may pick the
  equivalent-but-not-syntactically-equal `ULift.module` instance.
-/

open CategoryTheory

noncomputable section

namespace Work.SSGRoute

open SSGRoute.PTExt

set_option linter.style.haveILetI false in
theorem rightDetect_fixed_functional (p : ℕ) [Fact p.Prime] {D : Type} [Group D] [Finite D] (hD : IsPGroup p D) (M : Rep SSGRoute.PTExt.Coeff D) [Finite M] (hM : ∀ m : M, p • m = 0) (hMn : Nontrivial ↥M) : ∃ φ : M ⟶ Rep.trivial SSGRoute.PTExt.Coeff D (ZMod p), Function.Surjective φ.hom := by
  classical
  haveI : Fintype D := Fintype.ofFinite D
  -- Pin the `Coeff`-module structure on `M.V` to the one carried by `M`.
  letI coeffM : Module Coeff M.V := M.hV2
  -- The `ZMod p`-module structure on `M.V`; bound to a variable first (see the module docstring).
  have hmod : Module (ZMod p) M.V := AddCommGroup.zmodModule hM
  letI modZp : Module (ZMod p) M.V := hmod
  -- The `D`-action on `M.V` as a `DistribMulAction`, and its compatibility with `ZMod p`.
  letI actD : DistribMulAction D M.V :=
    { smul := fun g m => M.ρ g m
      one_smul := fun m => by show M.ρ 1 m = m; simp
      mul_smul := fun g h m => by
        show M.ρ (g * h) m = M.ρ g (M.ρ h m)
        rw [map_mul]; rfl
      smul_zero := fun g => by show M.ρ g 0 = 0; simp
      smul_add := fun g m n => by show M.ρ g (m + n) = M.ρ g m + M.ρ g n; simp }
  letI scD : SMulCommClass D (ZMod p) M.V :=
    ⟨fun g c m => by
      show M.ρ g (c • m) = c • M.ρ g m
      exact ZMod.map_smul (M.ρ g) c m⟩
  -- `M.V` as a `ZMod p`-representation of `D`, and its contragredient.
  let ρz : Representation (ZMod p) D M.V := Representation.ofDistribMulAction (ZMod p) D M.V
  let dualRep : Rep (ZMod p) D := Rep.of (ρz.dual)
  haveI hWnt : Nontrivial dualRep.V := by
    change Nontrivial (M.V →ₗ[ZMod p] ZMod p)
    exact instNontrivialLinearMapId
  -- A nonzero `D`-fixed functional.
  obtain ⟨f₀, hfne₀, hffix₀⟩ :=
    Work.CohomologicallyTrivial.pgroup_invariants_ne_bot hD dualRep hWnt
  set f : M.V →ₗ[ZMod p] ZMod p := f₀ with hf
  have hffix : ∀ g : D, (dualRep.ρ g) f = f := by intro g; simpa [hf] using hffix₀ g
  have hfne : f ≠ 0 := hfne₀
  -- `f` is invariant under the action of `D`.
  have hfix : ∀ (g : D) (m : M.V), f (M.ρ g m) = f m := by
    intro g m
    have htrans : (Module.Dual.transpose (ρz g)) f = f := by
      have h := hffix g⁻¹
      simpa [dualRep, Rep.of_ρ, Representation.dual_apply, inv_inv] using h
    have hh : f ∘ₗ ρz g = f := by
      rw [Module.Dual.transpose_apply] at htrans
      exact htrans
    have h3 : f ((ρz g) m) = f m :=
      congrArg (fun L : M.V →ₗ[ZMod p] ZMod p => L m) hh
    have hgm : (ρz g) m = M.ρ g m := by
      simp only [ρz, Representation.ofDistribMulAction_apply_apply, actD]
      rfl
    rw [hgm] at h3
    exact h3
  -- A `ZMod p`-linear functional is `Coeff`-linear: `Coeff = ULift ℤ` acts as `ℤ` does.
  let fC : M.V →ₗ[Coeff] ZMod p :=
    { toFun := f
      map_add' := fun a b => map_add f a b
      map_smul' := fun c m => by
        rw [show c = ((c.down : ℤ) : ULift ℤ) from (ULift.up_intCast (R := ℤ) c.down).symm]
        simp only [RingHom.id_apply]
        rw [Int.cast_smul_eq_zsmul (ULift ℤ) c.down m,
            Int.cast_smul_eq_zsmul (ULift ℤ) c.down (f m)]
        exact map_zsmul f c.down m }
  refine ⟨Rep.ofHom ⟨fC, ?_⟩, ?_⟩
  · -- `fC` is `D`-equivariant (the target representation is trivial).
    intro g
    ext m
    rw [Rep.trivial_ρ]
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    exact hfix g m
  · -- A nonzero linear functional into the one-dimensional `𝔽_p` is surjective.
    intro z
    change ∃ m : M.V, f m = z
    have hm0 : ∃ m, f m ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hfne (by ext m; simpa using h m)
    obtain ⟨m₀, hm₀⟩ := hm0
    refine ⟨(z * (f m₀)⁻¹) • m₀, ?_⟩
    rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hm₀, mul_one]

end Work.SSGRoute
