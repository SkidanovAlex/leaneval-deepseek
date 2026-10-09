import Mathlib
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of `Ĥ⁰` and `Ĥ¹` for a finitely generated `ℤ[G]`-module

For a finite group `G` and a `ℤ[G]`-module `M` that is finitely generated over `ℤ`, the two
Tate cohomology groups `Ĥ⁰(G, M)` and `Ĥ¹(G, M)` are finite.

Indeed, both are finitely generated abelian groups (they are subquotients of finitely generated
modules, respectively `M` and the module of `1`-cochains `G → M`) and both are annihilated by
`|G|`: for `Ĥ⁰(G, M) = M^G ⧸ N(M)` this is the identity `N(x) = |G|·x` for `x ∈ M^G`, and for
`Ĥ¹(G, M)` it is the identity `|G|·f = d(f)` for the derivation `f` and the explicit element
`Σ_{g : G} f(g)`.  A finitely generated torsion abelian group is finite.

The instances are delicate because for `k = ℤ` there are two competing `ℤ`-module structures
(`Rep.hV2` and `AddCommGroup.toIntModule`); the proof therefore pins the relevant module
structures with `letI` and passes between them through `Subsingleton.elim`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open CategoryTheory

namespace NK.GlobalCFTdeep.Herbrand

theorem finite_tateCohomology_of_moduleFinite {G : Type} [Group G] [Fintype G] (M : Rep ℤ G)
    [Module.Finite ℤ M.V] :
    Finite ↥(tateCohomology M 0) ∧ Finite ↥(tateCohomology M 1) := by
  classical
  -- the hypothesis is stated with the canonical `ℤ`-module structure
  have hMfin_c : @Module.Finite ℤ M.V _ _ (AddCommGroup.toIntModule M.V) :=
    ‹Module.Finite ℤ M.V›
  -- from now on use the `ℤ`-module structure carried by `M`
  letI : Module ℤ M.V := M.hV2
  haveI hMfin_h : @Module.Finite ℤ M.V _ _ M.hV2 :=
    (Subsingleton.elim (AddCommGroup.toIntModule M.V) M.hV2) ▸ hMfin_c
  haveI hNoeth : @IsNoetherian ℤ M.V _ _ M.hV2 :=
    isNoetherian_of_isNoetherianRing_of_finite ℤ M.V
  constructor
  · -- ## Degree `0`: `Ĥ⁰(G, M) ≅ M^G ⧸ N(M)`
    letI : Module ℤ ↥(M.ρ.invariants) := M.ρ.invariants.module
    have hAfg : (M.ρ.invariants).FG := IsNoetherian.noetherian _
    haveI hAfin : Module.Finite ℤ ↥(M.ρ.invariants) := Module.Finite.iff_fg.mpr hAfg
    let p : Submodule ℤ ↥(M.ρ.invariants) :=
      (LinearMap.range M.ρ.norm).comap M.ρ.invariants.subtype
    letI : Module ℤ (↥(M.ρ.invariants) ⧸ p) := Submodule.Quotient.module p
    have hQfg : Module.Finite ℤ (↥(M.ρ.invariants) ⧸ p) := by
      refine Module.Finite.of_fg_top ?_
      have h := Submodule.FG.map (f := Submodule.mkQ p) (hAfin.fg_top)
      rw [Submodule.map_top] at h
      rw [← LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective p)]
      exact h
    -- the norm of an invariant is `|G|` times it
    have hnorm : ∀ x : M.V, x ∈ M.ρ.invariants → M.ρ.norm x = Fintype.card G • x := by
      intro x hx
      rw [Representation.norm]
      rw [LinearMap.sum_apply]
      simp_rw [(Representation.mem_invariants M.ρ x).mp hx]
      rw [Finset.sum_const, Finset.card_univ]
    -- the quotient is torsion, being annihilated by `|G|`
    have htor : IsAddTorsion (↥(M.ρ.invariants) ⧸ p) := by
      intro x
      rw [isOfFinAddOrder_iff_nsmul_eq_zero]
      refine ⟨Fintype.card G, Fintype.card_pos, ?_⟩
      obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective p x
      rw [← hy]
      have h1 : (Submodule.mkQ p) (Fintype.card G • y) =
          Fintype.card G • (Submodule.mkQ p) y :=
        map_nsmul (Submodule.mkQ p).toAddMonoidHom (Fintype.card G) y
      rw [← Submodule.mkQ_apply p y, ← h1, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      rw [Submodule.mem_comap, LinearMap.mem_range]
      refine ⟨(y : M.V), ?_⟩
      rw [Submodule.subtype_apply]
      rw [AddSubgroup.coe_nsmul (M.ρ.invariants.toAddSubgroup) y (Fintype.card G)]
      exact hnorm (y : M.V) y.2
    have hFG : AddGroup.FG (↥(M.ρ.invariants) ⧸ p) := by
      have hcanon : @Module.Finite ℤ (↥(M.ρ.invariants) ⧸ p) _ _
          (AddCommGroup.toIntModule (↥(M.ρ.invariants) ⧸ p)) :=
        (Subsingleton.elim (Submodule.Quotient.module p)
          (AddCommGroup.toIntModule (↥(M.ρ.invariants) ⧸ p))) ▸ hQfg
      exact Module.Finite.iff_addGroup_fg.mp hcanon
    haveI hQfin : Finite (↥(M.ρ.invariants) ⧸ p) :=
      AddCommGroup.finite_of_fg_isAddTorsion _ htor
    -- transport along `Ĥ⁰(G, M) ≅ M^G ⧸ N(M)`
    obtain ⟨e⟩ := Commons.RepresentationTheory.GroupCohomology.tateCohomology_zero_iso_general
      (k := ℤ) (G := G) (V := M.V) M.ρ
    have hrep : Rep.of M.ρ = M := rfl
    rw [hrep] at e
    exact Finite.of_equiv _ e.toEquiv.symm
  · -- ## Degree `1`: `Ĥ¹(G, M) ≅ H¹(G, M)`, a subquotient of the `1`-cochains `G → M`
    letI : Module ℤ (G → M.V) := Pi.module G (fun _ => M.V) ℤ
    haveI hCfin : Module.Finite ℤ (G → M.V) := Module.Finite.pi
    haveI hNoethC : IsNoetherian ℤ (G → M.V) :=
      isNoetherian_of_isNoetherianRing_of_finite ℤ (G → M.V)
    letI : Module ℤ ↥(groupCohomology.cocycles₁ M) := (groupCohomology.cocycles₁ M).module
    have hcoc_fg : (groupCohomology.cocycles₁ M).FG := IsNoetherian.noetherian _
    haveI hcoc_fin : Module.Finite ℤ ↥(groupCohomology.cocycles₁ M) :=
      Module.Finite.iff_fg.mpr hcoc_fg
    have hFGcoc : AddGroup.FG ↥(groupCohomology.cocycles₁ M) := by
      have hcanon : @Module.Finite ℤ ↥(groupCohomology.cocycles₁ M) _ _
          (AddCommGroup.toIntModule ↥(groupCohomology.cocycles₁ M)) :=
        (Subsingleton.elim (groupCohomology.cocycles₁ M).module
          (AddCommGroup.toIntModule ↥(groupCohomology.cocycles₁ M))) ▸ hcoc_fin
      exact Module.Finite.iff_addGroup_fg.mp hcanon
    -- `H¹` is a quotient of the finitely generated `1`-cocycles
    have hFG1 : AddGroup.FG ↥(groupCohomology.H1 M) :=
      AddGroup.fg_of_surjective
        (f := (ConcreteCategory.hom (groupCohomology.H1π M)).toAddMonoidHom)
        ((ModuleCat.epi_iff_surjective (groupCohomology.H1π M)).1 inferInstance)
    -- a `1`-cocycle is a derivation, so `|G|·f` is a coboundary
    have hderiv : ∀ f : ↥(groupCohomology.cocycles₁ M),
        (ConcreteCategory.hom (groupCohomology.H1π M)) (Fintype.card G • f) =
          Fintype.card G • (ConcreteCategory.hom (groupCohomology.H1π M)) f :=
      fun f => map_nsmul (ConcreteCategory.hom (groupCohomology.H1π M)) (Fintype.card G) f
    have htor : IsAddTorsion ↥(groupCohomology.H1 M) := by
      intro z
      rw [isOfFinAddOrder_iff_nsmul_eq_zero]
      refine ⟨Fintype.card G, Fintype.card_pos, ?_⟩
      refine groupCohomology.H1_induction_on z ?_
      intro f
      rw [← hderiv f, groupCohomology.H1π_eq_zero_iff]
      rw [groupCohomology.coboundaries₁, LinearMap.mem_range]
      refine ⟨-(∑ h : G, (f : G → M.V) h), ?_⟩
      have hkey : ∀ g : G, M.ρ g (∑ h : G, (f : G → M.V) h) =
          (∑ h : G, (f : G → M.V) h) - Fintype.card G • (f g : M.V) := by
        intro g
        rw [map_sum]
        simp_rw [show ∀ h : G, M.ρ g ((f : G → M.V) h) =
            (f : G → M.V) (g * h) - (f : G → M.V) g from fun h => by
          rw [(groupCohomology.mem_cocycles₁_iff (f : G → M.V)).1 f.2 g h,
            add_sub_cancel_right]]
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
        congr 1
        exact Equiv.sum_comp (Equiv.mulLeft g) (fun h => (f : G → M.V) h)
      have hfun : ⇑(Fintype.card G • f : ↥(groupCohomology.cocycles₁ M)) =
          Fintype.card G • (f : G → M.V) :=
        AddSubgroup.coe_nsmul (groupCohomology.cocycles₁ M).toAddSubgroup f (Fintype.card G)
      rw [hfun]
      funext g
      rw [groupCohomology.d₀₁_hom_apply, map_neg, hkey g]
      simp only [Pi.smul_apply]
      abel
    haveI hH1fin : Finite ↥(groupCohomology.H1 M) :=
      AddCommGroup.finite_of_fg_isAddTorsion _ htor
    haveI hGCfin : Finite ↥((groupCohomology.functor ℤ G 1).obj M) := hH1fin
    have e1 := (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 1).app M
    exact Finite.of_equiv _ (Iso.toLinearEquiv e1).toEquiv.symm

end NK.GlobalCFTdeep.Herbrand
