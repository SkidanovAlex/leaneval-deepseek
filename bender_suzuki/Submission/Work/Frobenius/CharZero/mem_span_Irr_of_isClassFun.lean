import Mathlib
import Submission.Work.Frobenius.Pair
import Submission.Work.CharCore.classFun_eq_sum_irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Frobenius.CharZero.mem_span_Irr_of_isClassFun`

Every complex-valued class function on a finite group is a complex linear combination of
irreducible characters, i.e. lies in `Submodule.span ℂ (Irr G)`.

This is the completeness half of the character theory of finite groups, phrased in the
`Work.Frobenius` interface.  The argument reuses the character theory core
`Work.CharCore`: its finite family `Work.CharCore.Irr G` spans the class functions
(`Work.CharCore.classFun_eq_sum_irr`), so it suffices to see that every member of
`Work.CharCore.Irr G` is an irreducible character in the sense of `Work.Frobenius.Irr G`.

That last step needs a small point about universes.  `Work.Frobenius.IrrRep` bundles a
vector space of the *same* universe as `ℂ` (i.e. `Type 0`), whereas the members of
`Work.CharCore.Irr G` are characters of simple submodules of the regular module
`ℂ[G]`, which live in the universe of `G`.  The bridge is that the character of *any*
finite dimensional complex representation of `G` — in particular of a representation on a
space in a higher universe — is carried by an isomorphic representation on the `Type 0`
space `Fin n → ℂ` (`char_mem_Irr_of_isIrreducible`).
-/

@[expose] public section

noncomputable section

open Classical

open scoped MonoidAlgebra

namespace Work.Frobenius.CharZero

/-- **Transport of characters to a `Type 0` space.**  The character of any irreducible
finite dimensional complex representation of `G` is the character of an irreducible
representation on the space `Fin n → ℂ` (where `n` is the dimension), because a choice of
`ℂ`-basis identifies any finite dimensional complex vector space with `Fin n → ℂ`.

This is the bridge between the (universe-restricted) `Work.Frobenius.IrrRep` and
representations on spaces in arbitrary universes, e.g. the simple submodules of the
regular module `ℂ[G]` used by `Work.CharCore`. -/
theorem char_mem_Irr_of_isIrreducible {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible) :
    ρ.character ∈ Irr G := by
  classical
  obtain ⟨e⟩ : Nonempty (V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ)) := by
    refine ⟨LinearEquiv.ofFinrankEq V (Fin (Module.finrank ℂ V) → ℂ) ?_⟩
    rw [Module.finrank_fintype_fun_eq_card]; simp
  -- The representation transported along `e` to `Fin n → ℂ`.
  let σ : Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) :=
    e.conjRingEquiv.toMonoidHom.comp ρ
  -- Same character, by invariance of the trace under conjugation.
  have hchar : σ.character = ρ.character := by
    funext g
    show LinearMap.trace ℂ (Fin (Module.finrank ℂ V) → ℂ) (σ g) = LinearMap.trace ℂ V (ρ g)
    have h1 : (σ g : Module.End ℂ (Fin (Module.finrank ℂ V) → ℂ)) = e.conj (ρ g) := rfl
    rw [h1, LinearMap.trace_conj']
  -- Same (ir)reducibility, because `e` is an isomorphism of `ℂ[G]`-modules.
  have hσ : σ.IsIrreducible := by
    rw [Representation.irreducible_iff_isSimpleModule_asModule]
    have hρ' : IsSimpleModule ℂ[G] ρ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hρ
    have hinter : ∀ (r : ℂ[G]) (x : V), e (ρ.asAlgebraHom r x) = σ.asAlgebraHom r (e x) := by
      intro r
      induction r using MonoidAlgebra.induction_on with
      | of m =>
        intro x
        rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of]
        show e ((ρ m) x) = (σ m) (e x)
        rw [show (σ m : Module.End ℂ (Fin (Module.finrank ℂ V) → ℂ)) = e.conj (ρ m) from rfl]
        simp
      | add r s hr hs =>
        intro x
        rw [map_add, map_add]
        simp only [LinearMap.add_apply, map_add]
        rw [hr x, hs x]
      | smul c r hr =>
        intro x
        rw [map_smul, map_smul]
        simp only [LinearMap.smul_apply]
        rw [map_smul, hr x]
    have hψ : ρ.asModule ≃ₗ[ℂ[G]] σ.asModule :=
      { toFun := e, invFun := e.symm, left_inv := e.left_inv, right_inv := e.right_inv,
        map_add' := e.map_add, map_smul' := hinter }
    exact IsSimpleModule.congr (M := σ.asModule) (N := ρ.asModule) hψ.symm
  exact ⟨{ V := Fin (Module.finrank ℂ V) → ℂ, ρ := σ, irred := hσ }, hchar⟩

/-- `Representation.ofModule' M` is the representation whose associated algebra
homomorphism is the scalar action of `ℂ[G]` on `M`. -/
private theorem asAlgebraHom_ofModule' {G : Type*} [Group G] (M : Type*) [AddCommGroup M]
    [Module ℂ M] [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M] :
    (Representation.ofModule' (k := ℂ) (G := G) M).asAlgebraHom =
      Algebra.lsmul ℂ (A := ℂ[G]) (B := ℂ) M := by
  have h : (Representation.ofModule' (k := ℂ) (G := G) M : G →* Module.End ℂ M) =
      (MonoidAlgebra.lift ℂ (M →ₗ[ℂ] M) G).symm
        (Algebra.lsmul ℂ (A := ℂ[G]) (B := ℂ) M) := rfl
  rw [Representation.asAlgebraHom_def, h]
  exact Equiv.apply_symm_apply (MonoidAlgebra.lift ℂ (M →ₗ[ℂ] M) G)
    (Algebra.lsmul ℂ (A := ℂ[G]) (B := ℂ) M)

/-- A simple `ℂ[G]`-module, viewed through `Representation.ofModule'`, is an irreducible
representation. -/
private theorem isIrreducible_ofModule' {G : Type*} [Group G] (M : Type*) [AddCommGroup M]
    [Module ℂ M] [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M] [IsSimpleModule ℂ[G] M] :
    (Representation.ofModule' (k := ℂ) (G := G) M).IsIrreducible := by
  have hae := asAlgebraHom_ofModule' (G := G) M
  have hsmul : ∀ (m : ℂ[G]) (x : (Representation.ofModule' (k := ℂ) (G := G) M).asModule),
      (show M from (m • x)) = m • (show M from x) := by
    intro m x
    have h := Representation.asModuleEquiv_map_smul
      (ρ := Representation.ofModule' (k := ℂ) (G := G) M) m x
    rw [hae] at h
    rw [Algebra.lsmul_apply] at h
    exact h
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  let e : (Representation.ofModule' (k := ℂ) (G := G) M).asModule ≃ₗ[ℂ[G]] M :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun m x => hsmul m x }
  exact IsSimpleModule.congr e

/-- Every member of the core's irreducible-character finset is an irreducible character in
the Frobenius interface. -/
private theorem charCore_mem_Irr {G : Type*} [Group G] [Fintype G] {χ : G → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr G) : χ ∈ Irr G := by
  obtain ⟨N, hN, hNχ⟩ := (Work.CharCore.mem_Irr_iff_exists χ).mp hχ
  have hsimple : IsSimpleModule (Work.CharCore.groupAlgebra G) N :=
    Work.CharCore.isSimpleModule_of_mem_irrSubmodules N hN
  have hmem : (Work.CharCore.submoduleRep N).character ∈ Irr G :=
    char_mem_Irr_of_isIrreducible (Work.CharCore.submoduleRep N)
      (isIrreducible_ofModule' N)
  rwa [hNχ] at hmem

/-- **Every class function is a linear combination of irreducible characters.** -/
theorem mem_span_Irr_of_isClassFun {G : Type*} [Group G] [Fintype G] {f : G → ℂ}
    (hf : IsClassFun f) : f ∈ Submodule.span ℂ (Irr G) := by
  have hf' : Work.CharCore.IsClassFun f := hf
  rw [Work.CharCore.classFun_eq_sum_irr hf']
  refine Submodule.sum_mem _ fun χ hχ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span (charCore_mem_Irr hχ)

end Work.Frobenius.CharZero
