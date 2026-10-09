import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_corestriction
import Submission.Work.CohomologicallyTrivial.SubQuotDefs
import Submission.Work.SSGRoute.ExtChain.pMulQuotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ext¹_G(K,U)` is `p`-divisible for a finite `p`-group `G` and a `ℤ`-lattice `K`

The main theorem of this file (`Work.SSGRoute.ExtChain.ext1_p_divisible`) is the elementary
`Ext`-theoretic step of Shafarevich's theorem on solvable Galois groups: for a finite `p`-group `G`
and a `G`-representation `K` whose underlying `ℤ`-module is a lattice (`Module.Free` and
`Module.Finite`), the group `Ext¹_G(K,U)` is `p`-divisible as soon as `Ext²_G(N,U)` vanishes for
every finitely generated `p`-torsion `G`-representation `N`.

The proof is the elementary half of the long exact sequence of the short exact sequence
`K --p--> K --> K ⧸ pK`:

* `p • 𝟙 K` is a monomorphism, because the carrier `K.V` of a lattice is `ℤ`-free, hence
  additively torsion-free;
* `K ⧸ pK` is the concrete quotient representation of `Work.SSGRoute.ExtChain.pMulQuotDefs`, whose
  carrier is literally `K.V ⧸ pMulSub p K`, so `Module.Finite` and `p`-torsion are immediate, and
  `hA` applies to it;
* the contravariant long exact sequence (`Abelian.Ext.contravariant_sequence_exact₁`) of the short
  exact sequence `K --p--> K --> K ⧸ pK` then exhibits every `x : Ext¹_G(K,U)` as `p • y`.

The short exactness of `K --p--> K --> K ⧸ pK` is the content of `quotRepProj_isCokernel_aux` below:
the quotient projection is a cokernel of `p • 𝟙 K` (the same argument as
`Work.CohomologicallyTrivial.coker_iso_quotRep`, which treats the case `W = im f`).
-/

open CategoryTheory CategoryTheory.Limits

-- The module structure on a carrier `X.V` which is carried by the representation `X` itself
-- (`Rep.hV2`) is preferred to the generic `ULift`-instance coming from `AddCommGroup.toIntModule`.
attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

namespace Work.SSGRoute.ExtChain

open SSGRoute.PTExt

noncomputable section

universe u v

section QuotRepProjCokernel

variable {k : Type u} [CommRing k] {Γ : Type v} [Group Γ]

/-- **The projection to a quotient is a cokernel of a map with image `W`.**  Let `W ≤ Y.V` be a
`G`-stable submodule, `f : X ⟶ Y` a morphism with `f ≫ quotRepProj Y W hW = 0` whose image is
exactly `W`.  Then the quotient projection `Y ⟶ Y ⧸ W` is a cokernel of `f`.

This is the general form of `Work.CohomologicallyTrivial.coker_iso_quotRep` (the case
`W = range f` over `ℤ`): a morphism `g : Y ⟶ Z` with `f ≫ g = 0` kills the image of `f`, hence
`W`, so it factors through `Submodule.liftQ`; the intertwining property of the factorisation follows
from that of `g`, and uniqueness from `quotRepProj` being an epimorphism. -/
def quotRepProj_isCokernel_aux {X Y : Rep.{0} k Γ} (W : Submodule k Y.V)
    (hW : ∀ g : Γ, W ≤ Submodule.comap (Y.ρ g) W) (f : X ⟶ Y)
    (hzero : f ≫ Work.CohomologicallyTrivial.quotRepProj Y W hW = 0)
    (hWrange : ∀ w : Y.V, w ∈ W → ∃ x : X.V, f.hom x = w) :
    IsColimit (CokernelCofork.ofπ (Work.CohomologicallyTrivial.quotRepProj Y W hW) hzero) := by
  letI : Module k Y.V := Y.hV2
  letI : Module k (Work.CohomologicallyTrivial.quotRep Y W hW).V :=
    (Work.CohomologicallyTrivial.quotRep Y W hW).hV2
  haveI : Epi (Work.CohomologicallyTrivial.quotRepProj Y W hW) := by
    rw [Rep.epi_iff_surjective]
    intro q
    exact Submodule.mkQ_surjective W q
  refine CokernelCofork.IsColimit.ofπ' _ hzero ?_
  intro Z g hg
  letI : Module k Z.V := Z.hV2
  have hker : W ≤ LinearMap.ker g.hom.toLinearMap := by
    intro y hy
    obtain ⟨x, rfl⟩ := hWrange y hy
    have h2 : g.hom.comp f.hom = 0 := by
      simpa [Rep.hom_comp] using congrArg Rep.Hom.hom hg
    have h3 := DFunLike.congr_fun h2 x
    simpa using h3
  have hint : ∀ (gg : Γ) (q : Y.V ⧸ W),
      W.liftQ g.hom.toLinearMap hker (((Y.ρ.quotient W hW) gg) q) =
        (Z.ρ gg) (W.liftQ g.hom.toLinearMap hker q) := by
    intro gg q
    refine Submodule.Quotient.induction_on W q ?_
    intro y
    simp only [Representation.quotient_apply, Submodule.mapQ_apply, Submodule.liftQ_apply]
    exact Representation.IntertwiningMap.isIntertwining Y.ρ Z.ρ g.hom gg y
  refine ⟨Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (f := W.liftQ g.hom.toLinearMap hker) (ρ := Y.ρ.quotient W hW) (σ := Z.ρ) hint), ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  show W.liftQ g.hom.toLinearMap hker ((Submodule.mkQ W) y) = g.hom.toLinearMap y
  exact DFunLike.congr_fun (Submodule.liftQ_mkQ (p := W) (f := g.hom.toLinearMap) hker) y

/-- The short complex `X --f--> Y --> Y ⧸ W` is exact in the middle when the image of `f` is
exactly `W`. -/
theorem quotRepProj_exact_aux {X Y : Rep.{0} k Γ} (W : Submodule k Y.V)
    (hW : ∀ g : Γ, W ≤ Submodule.comap (Y.ρ g) W) (f : X ⟶ Y)
    (hzero : f ≫ Work.CohomologicallyTrivial.quotRepProj Y W hW = 0)
    (hWrange : ∀ w : Y.V, w ∈ W → ∃ x : X.V, f.hom x = w) :
    (ShortComplex.mk f (Work.CohomologicallyTrivial.quotRepProj Y W hW) hzero).Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    (quotRepProj_isCokernel_aux W hW f hzero hWrange)

end QuotRepProjCokernel

section Main

variable {G : Type} [Group G]

/-- **`hA` applies to `K ⧸ pK`**: the quotient `K ⧸ pK` of a finitely generated representation is
finitely generated and killed by `p`. -/
theorem subsingleton_ext2_pMulQuot_aux (p : ℕ) (K U : Rep.{0} Coeff G) [Module.Finite ℤ K.V]
    (hA : ∀ (N : Rep.{0} Coeff G), Module.Finite ℤ N.V →
      (∀ x : N.V, p • x = 0) → Subsingleton (Abelian.Ext.{0} N U 2)) :
    Subsingleton (Abelian.Ext.{0} (pMulQuot p K) U 2) := by
  refine hA (pMulQuot p K) ?_ ?_
  · exact Module.Finite.quotient ℤ (pMulSub p K)
  · intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (pMulSub p K) x
    rw [← map_nsmul (Submodule.mkQ (pMulSub p K)) p y,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, pMulSub_mem_iff]
    exact ⟨y, rfl⟩

/-- **Multiplication by `p` on a `ℤ`-lattice is a monomorphism** (of representations): a free
`ℤ`-module is additively torsion-free, so `x ↦ p • x` is injective. -/
theorem mono_pMul_aux (p : ℕ) (hp : p ≠ 0) (K : Rep.{0} Coeff G) [Module.Free ℤ K.V] :
    Mono (p • 𝟙 K) := by
  rw [Rep.mono_iff_injective]
  intro x y hxy
  haveI : IsAddTorsionFree K.V := IsAddTorsionFree.of_isTorsionFree ℤ K.V
  have h : p • x = p • y := by
    have h2 := hxy
    simp only [Rep.nsmul_hom, Rep.hom_id, Representation.IntertwiningMap.coe_nsmul,
      Pi.smul_apply] at h2
    exact h2
  exact nsmul_right_injective hp h

/-- For a finite `p`-group `G` and a `ℤ`-lattice `K`, the group `Ext¹_G(K,U)` is `p`-divisible as
soon as `Ext²_G(K/pK, U) = 0`.

Proof route: `p : K ⟶ K` is a monomorphism (the carrier of `K` is `ℤ`-free), so
`S = 0 → K --p--> K → coker (p • 𝟙 K) → 0` is a short exact short complex
(`ShortComplex.ShortExact.mk'`, `ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero`,
`Limits.cokernel.condition`); in the contravariant long exact sequence,
`Ext¹(K,U) --(mk₀ (p • 𝟙 K))--> Ext¹(K,U) --δ--> Ext²(coker (p • 𝟙 K), U)` is exact, the map
`mk₀ (p • 𝟙 K)` is `p • ·` (`Work.SSGRoute.mk₀_nsmul_aux`, `Work.SSGRoute.nsmul_comp_aux`,
`Abelian.Ext.mk₀_id_comp`), and `δ = 0` because its target is a subsingleton, so
`Abelian.Ext.contravariant_sequence_exact₁` applies. -/
theorem ext1_p_divisible {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    (hpG : IsPGroup p G) (K U : Rep.{0} SSGRoute.PTExt.Coeff G)
    [Module.Free ℤ K.V] [Module.Finite ℤ K.V]
    (hA : ∀ (N : Rep.{0} SSGRoute.PTExt.Coeff G), Module.Finite ℤ N.V →
      (∀ x : N.V, p • x = 0) →
      Subsingleton (CategoryTheory.Abelian.Ext.{0} N U 2)) :
    ∀ x : CategoryTheory.Abelian.Ext.{0} K U 1, ∃ y, p • y = x := by
  intro x
  letI : Module SSGRoute.PTExt.Coeff K.V := K.hV2
  letI : Module SSGRoute.PTExt.Coeff (pMulQuot p K).V := (pMulQuot p K).hV2
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  -- `p • 𝟙 K` is a monomorphism and `K ⟶ K ⧸ pK` is its cokernel
  have hmono : Mono (p • 𝟙 K) := mono_pMul_aux p hp K
  have hzero : (p • 𝟙 K) ≫ pMulQuotProj p K = 0 := pMul_comp_pMulQuotProj p K
  have hWrange : ∀ w : K.V, w ∈ pMulSub p K → ∃ z : K.V, ((p • 𝟙 K).hom) z = w := by
    intro w hw
    obtain ⟨z, hz⟩ := (pMulSub_mem_iff p K w).mp hw
    exact ⟨z, (pMulSub_hom_apply p K z).trans hz⟩
  -- the short exact sequence `K --p--> K --> K ⧸ pK`
  let S : ShortComplex (Rep.{0} Coeff G) :=
    ShortComplex.mk (p • 𝟙 K) (pMulQuotProj p K) hzero
  have hExact : S.Exact := by
    show (ShortComplex.mk (p • 𝟙 K)
      (Work.CohomologicallyTrivial.quotRepProj K (pMulSub p K) (pMulSub_stable p K))
      hzero).Exact
    exact quotRepProj_exact_aux (pMulSub p K) (pMulSub_stable p K) (p • 𝟙 K) hzero hWrange
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' hExact ?_ ?_
    · show Mono (p • 𝟙 K)
      exact hmono
    · show Epi (pMulQuotProj p K)
      exact (Rep.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
  -- the connecting map `δ` vanishes because its target is a subsingleton
  have hsub : Subsingleton (CategoryTheory.Abelian.Ext.{0} S.X₃ U 2) := by
    show Subsingleton (CategoryTheory.Abelian.Ext.{0} (pMulQuot p K) U 2)
    exact subsingleton_ext2_pMulQuot_aux p K U hA
  haveI : Subsingleton (CategoryTheory.Abelian.Ext.{0} S.X₃ U 2) := hsub
  -- the contravariant long exact sequence: `Ext¹(K,U) --p--> Ext¹(K,U) --> Ext²(K⧸pK, U)`
  obtain ⟨y, hy⟩ := CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁
    (S := S) hS U x rfl (Subsingleton.elim _ _)
  refine ⟨y, ?_⟩
  have hy' : (CategoryTheory.Abelian.Ext.mk₀ S.f).comp y (zero_add 1) = p • y := by
    show (CategoryTheory.Abelian.Ext.mk₀ (p • 𝟙 K)).comp y (zero_add 1) = p • y
    rw [Work.SSGRoute.mk₀_nsmul_aux p (𝟙 K),
      Work.SSGRoute.nsmul_comp_aux p (CategoryTheory.Abelian.Ext.mk₀ (𝟙 K)) y (zero_add 1),
      CategoryTheory.Abelian.Ext.mk₀_id_comp]
  rw [← hy', hy]

end Main

end

end Work.SSGRoute.ExtChain
