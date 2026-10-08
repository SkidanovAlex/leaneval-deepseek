import Mathlib
import Submission.Work.CharCore.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Every irreducible character occurs in `Irr G`

`Work.CharCore.Irr G` is the finset of characters of a chosen finite independent generating
family `irrSubmodules G` of simple submodules of the regular module `ℂ[G]`.  This file shows
that the family is complete: the character of *any* irreducible finite dimensional complex
representation of `G` lies in `Irr G`.

The mathematical content is the standard argument that every simple `ℂ[G]`-module is
isomorphic to a direct summand of the regular module:

* `ℂ[G]` is semisimple (Maschke's theorem, `Mathlib.RepresentationTheory.Maschke`), so every
  simple `ℂ[G]`-module `M` is isomorphic to a left ideal of `ℂ[G]`, i.e. to a simple submodule
  of the regular module (`IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule`);
* if `s` is an independent family of simple submodules with `sSup s = ⊤` — as
  `irrSubmodules G` is by construction — then every simple submodule `W ≤ ℂ[G]` is isomorphic
  to some member of `s` (`exists_linearEquiv_of_sSupIndep_isSimpleModule`, proved by projecting
  `W` onto the direct sum decomposition);
* the character of a representation only depends on the isomorphism class of the underlying
  `ℂ[G]`-module (`character_eq_of_linearEquiv`, `character_eq_asModule`).

The main theorem is `Work.CharCore.irreducible_character_mem_Irr`.
-/

noncomputable section

open Classical
open scoped MonoidAlgebra

namespace Work.CharCore

set_option linter.style.haveILetI false

section Helpers

/-- A representation obtained from a `ℂ[G]`-module structure via `Representation.ofModule'`
acts by multiplication by `MonoidAlgebra.of ℂ G g`. -/
theorem ofModule'_apply_of {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module ℂ[G] V] [IsScalarTower ℂ ℂ[G] V] (g : G) (v : V) :
    (Representation.ofModule' (k := ℂ) (G := G) V) g v = MonoidAlgebra.of ℂ G g • v := by
  show (MonoidAlgebra.lift ℂ (V →ₗ[ℂ] V) G).symm (Algebra.lsmul ℂ ℂ V) g v = _
  rw [MonoidAlgebra.lift_symm_apply]
  simp [Algebra.lsmul_apply]

/-- Isomorphic `ℂ[G]`-modules give rise (via `Representation.ofModule'`) to representations with
the same character. -/
theorem character_eq_of_linearEquiv {G : Type*} [Group G] {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [Module ℂ[G] V] [IsScalarTower ℂ ℂ[G] V]
    [AddCommGroup W] [Module ℂ W] [Module ℂ[G] W] [IsScalarTower ℂ ℂ[G] W]
    (e : V ≃ₗ[ℂ[G]] W) :
    (Representation.ofModule' (k := ℂ) (G := G) V).character =
      (Representation.ofModule' (k := ℂ) (G := G) W).character := by
  funext g
  rw [Representation.character, Representation.character]
  have key : (LinearEquiv.restrictScalars ℂ e).conj ((Representation.ofModule' (k:=ℂ) (G:=G) V) g)
      = (Representation.ofModule' (k:=ℂ) (G:=G) W) g := by
    ext x
    simp [LinearEquiv.conj_apply_apply, ofModule'_apply_of, e.map_smul]
  rw [← key, LinearMap.trace_conj']

/-- The character of a representation `ρ` agrees with that of the representation attached to the
`ℂ[G]`-module `ρ.asModule`. -/
theorem character_eq_asModule {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    ρ.character = (Representation.ofModule' (k := ℂ) (G := G) ρ.asModule).character := by
  funext g
  rw [Representation.character, Representation.character]
  have key : ((ρ.asModuleEquiv).symm).conj (ρ g)
      = (Representation.ofModule' (k:=ℂ) (G:=G) ρ.asModule) g := by
    ext x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm]
    exact Representation.asModuleEquiv_symm_map_rho ρ g x
  rw [← key, LinearMap.trace_conj']

/-- If `s` is an independent family of simple submodules of `M` whose supremum is `⊤`, then every
simple submodule `W ≤ M` is isomorphic to some member of `s`. -/
theorem exists_linearEquiv_of_sSupIndep_isSimpleModule {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {s : Set (Submodule R M)} (hind : sSupIndep s) (hsup : sSup s = ⊤)
    (hsimple : ∀ m ∈ s, IsSimpleModule R m)
    (W : Submodule R M) [IsSimpleModule R W] :
    ∃ N ∈ s, Nonempty (W ≃ₗ[R] N) := by
  classical
  have hind' : iSupIndep (fun m : s => m.1) := (sSupIndep_iff s).mp hind
  have hsup' : ⨆ m : s, (m : Submodule R M) = ⊤ := by
    rw [← sSup_eq_iSup', hsup]
  let e : M ≃ₗ[R] (Π₀ m : s, m.1) := (hind'.linearEquiv hsup').symm
  let f : W →ₗ[R] (Π₀ m : s, m.1) := e.toLinearMap.comp W.subtype
  haveI : Nontrivial W := IsSimpleModule.nontrivial R W
  obtain ⟨w, hw⟩ : ∃ w : W, w ≠ 0 := exists_ne 0
  have hfw : f w ≠ 0 := by
    intro h
    refine hw ?_
    apply Subtype.ext
    have h1 : e (w : M) = 0 := h
    have := congrArg (⇑e.symm) h1
    simpa using this
  obtain ⟨j, hj⟩ : ∃ j : s, (f w) j ≠ 0 := by
    by_contra h
    push Not at h
    exact hfw (DFinsupp.ext fun i => h i)
  let g : W →ₗ[R] j.1 := (DFinsupp.lapply j).comp f
  have hgw : g w ≠ 0 := hj
  have hgne : g ≠ 0 := fun h => hgw (by rw [h]; rfl)
  have hker : LinearMap.ker g = ⊥ := by
    rcases eq_bot_or_eq_top (LinearMap.ker g) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) hgne
  have hinj : Function.Injective g := LinearMap.ker_eq_bot.mp hker
  haveI : IsSimpleModule R j.1 := hsimple j.1 j.2
  have hrange : LinearMap.range g = ⊤ := by
    rcases eq_bot_or_eq_top (LinearMap.range g) with h | h
    · have hmem : g w ∈ (⊥ : Submodule R j.1) := h ▸ LinearMap.mem_range_self g w
      exact absurd (by simpa using hmem) hgw
    · exact h
  have hsurj : Function.Surjective g := LinearMap.range_eq_top.mp hrange
  exact ⟨j.1, j.2, ⟨LinearEquiv.ofBijective g ⟨hinj, hsurj⟩⟩⟩

end Helpers

/-- Every irreducible complex character of `G` occurs among the characters of the chosen simple
submodules `irrSubmodules G` of the regular module. -/
theorem irreducible_character_mem_Irr {G : Type*} [Group G] [Fintype G] {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (h : ρ.IsIrreducible) : ρ.character ∈ Irr G := by
  -- `ℂ[G]` has the semisimplicity supplied by Maschke's theorem
  haveI : NeZero (Nat.card G : ℂ) := ⟨by
    have hc : 0 < Nat.card G := Nat.card_pos
    exact_mod_cast hc.ne'⟩
  -- an irreducible representation is a simple `ℂ[G]`-module
  haveI : IsSimpleModule (groupAlgebra G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp h
  haveI : IsSemisimpleRing (groupAlgebra G) := inferInstance
  -- every simple module is isomorphic to a left ideal of the regular module
  obtain ⟨I, ⟨e₁⟩⟩ :=
    IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule (groupAlgebra G) ρ.asModule
  haveI : IsSimpleModule (groupAlgebra G) I := IsSimpleModule.congr e₁.symm
  -- and the chosen independent generating family of simples captures its isomorphism class
  obtain ⟨N, hN, ⟨e₂⟩⟩ := exists_linearEquiv_of_sSupIndep_isSimpleModule
    (s := ((irrSubmodules G : Finset (Submodule (groupAlgebra G) (groupAlgebra G))) : Set _))
    (sSupIndep_irrSubmodules G) (sSup_irrSubmodules G)
    (fun m hm => isSimpleModule_of_mem_irrSubmodules m hm) I
  refine (mem_Irr_iff_exists ρ.character).mpr ⟨N, hN, ?_⟩
  exact (character_eq_of_linearEquiv (e₁.trans e₂)).symm.trans (character_eq_asModule ρ).symm

end Work.CharCore
