import Mathlib.RingTheory.TotallySplit
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ExtChain.FreeCover
import Submission.Work.SSGRoute.ExtChain.ext1_bot_and_natCard_smul
import Submission.Work.SSGRoute.ExtChain.ext1_p_divisible
import Submission.Work.SSGRoute.ExtChain.ext2_ptorsion_pgroup_vanish
import Submission.Work.SSGRoute.ExtChain.smul_eq_zero_of_sylow
import Submission.Work.SSGRoute.ext_two_iso_cohomology_of_presentation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ext²_G(M,U) = 0` for cohomologically trivial `U` and finitely generated `M`

This module proves `Work.SSGRoute.ExtChain.ext2_ct_vanish`: for a finite group `G`, a
`Rep Coeff G` `M` whose underlying `ℤ`-module is finitely generated, and a representation `U` whose
positive-degree `Ext`-cohomology vanishes for **every** subgroup of `G`
(`Subsingleton (Extⁿ_H(ℤ, U|_H))` for all `H ≤ G`, `n ≥ 1`), the second `Ext`-group
`Ext²_G(M,U)` vanishes.  Equivalently: `U` cohomologically trivial implies
`Ext^{≥2}_G(M,U) = 0` for finitely generated `M`.

## Proof outline

1. *Reduction to a lattice.*  By `Work.SSGRoute.repFG_free_cover` there is a surjection
   `π : ℤ[G]^n ⟶ M`, whose kernel `K` is a `ℤ`-lattice (`repFG_kernel`, `lattice_kernel_free`).
   The degree shift of `Work.SSGRoute.ext_two_iso_cohomology_of_presentation` gives
   `Ext²_G(M,U) ≃+ H¹(G, Hom_ℤ(K,U))`, so it suffices to show `Ext¹_G(K,U) = 0` for every lattice
   `K` (the *lattice theorem* `ext1_lattice_vanish`).
2. *`|G|` kills `Ext¹` of a lattice*: corestriction from the trivial subgroup
   (`Work.SSGRoute.ext_corestriction`) together with
   `Ext¹_{↥⊥}(K|_⊥, U|_⊥) = 0` (the `Ext ≅ H¹(Hom)` dictionary for lattices and the vanishing of
   `H¹` of the trivial group) shows `Nat.card G • x = 0`
   (`ext1_bot_and_natCard_smul`).
3. *Sylow reduction*: if `P ≤ G` is a Sylow `p`-subgroup, restriction to `P` is an isomorphism on
   the subsingleton `Ext¹_P(K|_P, U|_P)` (proved by 4), so `[G : P] • x = 0`; the Sylow indices
   have gcd one (`smul_eq_zero_of_sylow`), so `x = 0`.
4. *`p`-group case*: `p` divides `Ext¹_P(K|_P,U|_P)` because it is `p`-divisible
   (`ext1_p_divisible`: the cokernel `K/pK` is p-torsion and finitely generated, so
   `Ext²_P(K/pK,U) = 0` by `ext2_ptorsion_pgroup_vanish`) and `p`-power torsion.
-/

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

noncomputable section

/-- The kernel of a morphism from a free representation on a finite type is a `ℤ`-lattice. -/
theorem lattice_kernel_free {G : Type} [Group G] [Fintype G] {α : Type} [Finite α]
    (X : Rep.{0} SSGRoute.PTExt.Coeff G) (π : Rep.free SSGRoute.PTExt.Coeff G α ⟶ X) :
    Module.Free ℤ (Limits.kernel π).V := by
  letI : Module SSGRoute.PTExt.Coeff (Limits.kernel π).V := (Limits.kernel π).hV2
  letI : Module SSGRoute.PTExt.Coeff (Rep.free SSGRoute.PTExt.Coeff G α).V :=
    (Rep.free SSGRoute.PTExt.Coeff G α).hV2
  haveI hfin : Module.Finite ℤ (Limits.kernel π).V := Work.SSGRoute.repFG_kernel X π
  have hmono : Function.Injective
      (⇑(Rep.Hom.hom (CategoryTheory.Limits.kernel.ι π))) :=
    (Rep.mono_iff_injective _).mp inferInstance
  let iota : (Limits.kernel π).V →ₗ[ℤ]
      (Rep.free SSGRoute.PTExt.Coeff G α).V :=
    (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι π)).toLinearMap
      |>.toAddMonoidHom.toIntLinearMap
  have hcoe : ⇑iota = ⇑(Rep.Hom.hom (CategoryTheory.Limits.kernel.ι π)) := rfl
  haveI htf : Module.IsTorsionFree ℤ (Limits.kernel π).V :=
    Function.Injective.moduleIsTorsionFree (R := ℤ) (f := iota)
      (by rw [hcoe]; exact hmono) (fun r m => iota.map_smul r m)
  exact Module.free_of_finite_type_torsion_free'

/-- **The `p`-group case of the lattice theorem.**  For a finite `p`-group `G`, a `ℤ`-lattice `K`
and a representation `U` with `H¹(G,U) = H²(G,U) = 0`, the group `Ext¹_G(K,U)` vanishes: it is
`|G|`-torsion by `ext1_bot_and_natCard_smul` and `p`-divisible by `ext1_p_divisible` (whose
hypothesis is supplied by `ext2_ptorsion_pgroup_vanish`). -/
theorem pgroup_ext1_vanish {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    (hpG : IsPGroup p G) (K U : Rep.{0} SSGRoute.PTExt.Coeff G)
    [Module.Free ℤ K.V] [Module.Finite ℤ K.V]
    (hU1 : Subsingleton (CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.unitRep G) U 1))
    (hU2 : Subsingleton (CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.unitRep G) U 2)) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0} K U 1) := by
  classical
  have htor : ∀ x : CategoryTheory.Abelian.Ext.{0} K U 1, Nat.card G • x = 0 :=
    (ext1_bot_and_natCard_smul (G := G) K U).2
  have hA : ∀ (N : Rep.{0} SSGRoute.PTExt.Coeff G), Module.Finite ℤ N.V →
      (∀ x : N.V, p • x = 0) →
      Subsingleton (CategoryTheory.Abelian.Ext.{0} N U 2) := by
    intro N hfin hptor
    haveI := hfin
    exact ext2_ptorsion_pgroup_vanish hpG U N hptor hU1 hU2
  have hpd : ∀ x : CategoryTheory.Abelian.Ext.{0} K U 1, ∃ y, p • y = x :=
    ext1_p_divisible hpG K U hA
  obtain ⟨k, hk⟩ := hpG.exists_card_eq
  have hiter : ∀ n : ℕ, ∀ x : CategoryTheory.Abelian.Ext.{0} K U 1,
      ∃ y, (p ^ n) • y = x := by
    intro n
    induction n with
    | zero => intro x; exact ⟨x, by simp⟩
    | succ m ih =>
        intro x
        obtain ⟨y, hy⟩ := ih x
        obtain ⟨z, hz⟩ := hpd y
        exact ⟨z, by rw [pow_succ, mul_smul, hz, hy]⟩
  refine ⟨fun x y => ?_⟩
  have hx0 : x = 0 := by
    obtain ⟨z, hz⟩ := hiter k x
    have hz0 : (p ^ k) • z = 0 := by rw [← hk]; exact htor z
    rw [← hz, hz0]
  have hy0 : y = 0 := by
    obtain ⟨z, hz⟩ := hiter k y
    have hz0 : (p ^ k) • z = 0 := by rw [← hk]; exact htor z
    rw [← hz, hz0]
  rw [hx0, hy0]

/-- **The lattice theorem**: for a finite group `G`, a `ℤ`-lattice `K` and a representation `U` with
vanishing positive-degree `Ext`-cohomology for every subgroup of `G`, the group `Ext¹_G(K,U)`
vanishes.  The reduction to Sylow subgroups (`smul_eq_zero_of_sylow`) uses the `p`-group case
`pgroup_ext1_vanish` and corestriction (`Work.SSGRoute.ext_corestriction`). -/
theorem ext1_lattice_vanish {G : Type} [Group G] [Fintype G]
    (K U : Rep.{0} SSGRoute.PTExt.Coeff G) [Module.Free ℤ K.V] [Module.Finite ℤ K.V]
    (hU : ∀ (H : Subgroup G) [Fintype H] (n : ℕ), 1 ≤ n →
      Subsingleton (CategoryTheory.Abelian.Ext.{0}
        (SSGRoute.PTExt.unitRep H) (Rep.res H.subtype U) n)) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0} K U 1) := by
  classical
  obtain ⟨-, htor⟩ := ext1_bot_and_natCard_smul (G := G) K U
  have hzero : ∀ z : CategoryTheory.Abelian.Ext.{0} K U 1, z = 0 := by
    intro z
    refine smul_eq_zero_of_sylow (G := G) z (htor z) ?_
    intro p hp P
    haveI : Fact p.Prime := hp
    haveI : Fintype ↥(P : Subgroup G) := Fintype.ofFinite _
    obtain ⟨cor, hcor⟩ := ext_corestriction (G := G) (S := (P : Subgroup G))
    have hsub : Subsingleton (CategoryTheory.Abelian.Ext.{0}
        (Rep.res (P : Subgroup G).subtype K) (Rep.res (P : Subgroup G).subtype U) 1) :=
      pgroup_ext1_vanish (p := p) (G := ↥(P : Subgroup G)) P.isPGroup'
        (Rep.res (P : Subgroup G).subtype K) (Rep.res (P : Subgroup G).subtype U)
        (hU (P : Subgroup G) 1 le_rfl) (hU (P : Subgroup G) 2 (by norm_num))
    have h0 : extRes (P : Subgroup G).subtype z = 0 := Subsingleton.elim _ _
    rw [← hcor K U 1 z, h0, map_zero]
  exact ⟨fun x y => by rw [hzero x, hzero y]⟩

/-- **Shafarevich's `Ext`-vanishing for cohomologically trivial coefficients.**  For a finite group
`G`, a representation `M` that is finitely generated as a `ℤ`-module, and a representation `U`
whose positive-degree `Ext`-cohomology vanishes for every subgroup of `G`, the second `Ext`-group
`Ext²_G(M,U)` vanishes. -/
theorem ext2_ct_vanish {G : Type} [Group G] [Fintype G]
    (M U : Rep.{0} SSGRoute.PTExt.Coeff G) [Module.Finite ℤ M.V]
    (hU : ∀ (H : Subgroup G) [Fintype H] (n : ℕ), 1 ≤ n →
      Subsingleton (CategoryTheory.Abelian.Ext.{0}
        (SSGRoute.PTExt.unitRep H) (Rep.res H.subtype U) n)) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0} M U 2) := by
  classical
  obtain ⟨n, π, hπ⟩ := Work.SSGRoute.repFG_free_cover M
    (show Work.SSGRoute.RepFG M from ‹Module.Finite ℤ M.V›)
  haveI := hπ
  let S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G) :=
    ShortComplex.mk (Limits.kernel.ι π) π (Limits.kernel.condition π)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel π) inferInstance hπ
  haveI : Module.Finite ℤ (Limits.kernel π).V := Work.SSGRoute.repFG_kernel M π
  haveI : Module.Free ℤ (Limits.kernel π).V := lattice_kernel_free M π
  haveI : Projective S.X₂ := Rep.free_projective
  obtain ⟨e⟩ := Work.SSGRoute.ext_two_iso_cohomology_of_presentation G S hS U
  obtain ⟨e1⟩ := Work.SSGRoute.ext_one_iso_lattice_cohomology G S.X₁ U
  haveI hExt : Subsingleton (CategoryTheory.Abelian.Ext.{0} S.X₁ U 1) :=
    ext1_lattice_vanish S.X₁ U hU
  haveI : Subsingleton (Work.GroupCohomology.H1 G (S.X₁.V →ₗ[SSGRoute.PTExt.Coeff] U.V)) :=
    e1.symm.injective.subsingleton
  exact e.injective.subsingleton

end

end Work.SSGRoute.ExtChain
