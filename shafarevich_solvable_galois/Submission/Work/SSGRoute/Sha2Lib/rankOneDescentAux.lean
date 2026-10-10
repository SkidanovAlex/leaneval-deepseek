import Mathlib.GroupTheory.Nilpotent
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.Tactic.Have
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ExtChain.ext2_fn_two_helpers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for the equivariant multi-generator descent

These are the three elementary structural inputs of
`Work.SSGRoute.Sha2Lib.unramifiedDetector_indNormal_of_rankOne`, the reduction of the
rank-one (`W = 𝔽_p`) case of node `C6` to an arbitrary finite trivial `p`-torsion module `W`.

* `subsingleton_ind` — the base case of the induction: induction of a subsingleton representation is
  a subsingleton (via the coinduced model and `Rep.indCoindIso`).
* `exists_rankOne_functional_and_section` — peeling a rank-one summand: for `x₀ ≠ 0` there is a
  nonzero functional `π : W ⟶ 𝔽_p` with `π x₀ ≠ 0`, split by a section `s` (`s ≫ π = 𝟙`).
* `exists_kernelRep_shortExact` — the kernel of a nonzero surjection `π : W ⟶ 𝔽_p` is a
  subrepresentation with strictly smaller cardinality, and `0 → ker π → W → 𝔽_p → 0` is short
  exact.

The instance diamond for `Coeff = ULift ℤ` (the field `Rep.hV2` versus the global
`ULift.module`) is handled by a local instance-priority bump and by the explicitly-instance-taking
helpers of `Submission.Work.SSGRoute.ExtChain.ext2_fn_two_helpers`.
-/

namespace Work.SSGRoute.Sha2Lib

open CategoryTheory SSGRoute.PTExt

attribute [local instance 2000] Rep.hV2

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **The pullback along a section.**  If the class `φ` is the pullback of `w` along `u`
(`φ = u_* w`, i.e. `(mk₀ u).comp w = φ`) and `v` is a section of `u` (`v ≫ u = 𝟙`), then the
pullback of `φ` along `v` recovers `w`. -/
lemma mk0_comp_eq_of_comp_eq_id {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y Z : C} (u : X ⟶ Y) (v : Y ⟶ X) (hv : v ≫ u = 𝟙 Y) (φ : Abelian.Ext X Z 1)
    (w : Abelian.Ext Y Z 1) (hw : (Abelian.Ext.mk₀ u).comp w (zero_add 1) = φ) :
    (Abelian.Ext.mk₀ v).comp φ (zero_add 1) = w := by
  rw [← hw, Abelian.Ext.mk₀_comp_mk₀_assoc v u w, hv, Abelian.Ext.mk₀_id_comp]

/-- **Induction of a subsingleton representation.**  If the underlying type of `W : Rep Coeff N` is
a subsingleton then so is the underlying type of the induced `G`-representation. -/
theorem subsingleton_ind (G : Type) [Group G] (N : Subgroup G) [N.FiniteIndex]
    (W : Rep.{0} SSGRoute.PTExt.Coeff N)
    (h : Subsingleton ↥W) : Subsingleton ↥(Rep.ind N.subtype W) := by
  classical
  haveI hW : Subsingleton ↥W := h
  haveI hcoind : Subsingleton ↥(Rep.coind N.subtype W) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim a.1 b.1)⟩
  haveI : DecidableRel (QuotientGroup.rightRel N) := Classical.decRel _
  refine ⟨fun a b => ?_⟩
  have h1 : (Rep.indCoindIso W).hom.hom a = (Rep.indCoindIso W).hom.hom b :=
    Subsingleton.elim _ _
  have h2 : (Rep.indCoindIso W).inv.hom ((Rep.indCoindIso W).hom.hom a)
      = (Rep.indCoindIso W).inv.hom ((Rep.indCoindIso W).hom.hom b) := congrArg _ h1
  have h3 : ∀ x : ↥(Rep.ind N.subtype W),
      (Rep.indCoindIso W).inv.hom ((Rep.indCoindIso W).hom.hom x) = x := by
    intro x
    have h4 := congrArg (fun (f : Rep.ind N.subtype W ⟶ Rep.ind N.subtype W) =>
      (Rep.Hom.hom f) x) (Rep.indCoindIso W).hom_inv_id
    simpa using h4
  rw [h3 a, h3 b] at h2
  exact h2

/-- **The rank-one functional and its section.**  For a finite `p`-torsion trivial `N`-module `W`
and `x₀ ≠ 0`, there are `N`-equivariant `Coeff`-linear maps `π : W ⟶ 𝔽_p` (the trivial
`ZMod p`-representation) with `π x₀ ≠ 0` and `s : 𝔽_p ⟶ W` with `s ≫ π = 𝟙`, i.e.
`π (s n) = n` for all `n : ZMod p`. -/
theorem exists_rankOne_functional_and_section (p : ℕ) [Fact p.Prime] {N : Type} [Group N]
    (W : Rep.{0} SSGRoute.PTExt.Coeff N) [Finite W]
    (hWp : ∀ x : W, p • x = 0) (hWtriv : ∀ (g : N) (x : W), W.ρ g x = x)
    (x₀ : W) (hx₀ : x₀ ≠ 0) :
    ∃ (π : W ⟶ Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))
      (s : Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p) ⟶ W),
      ((Rep.Hom.hom π) x₀ ≠ 0) ∧
        (CategoryTheory.CategoryStruct.comp s π
          = CategoryTheory.CategoryStruct.id (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) := by
  classical
  haveI iW : Module (ZMod p) ↥W := AddCommGroup.zmodModule hWp
  haveI : Module.Finite (ZMod p) ↥W := Module.Finite.of_finite
  haveI : Module.Free (ZMod p) ↥W := Module.Free.of_divisionRing (ZMod p) ↥W
  haveI : StrongRankCondition (ZMod p) := inferInstance
  let b := Module.finBasis (ZMod p) ↥W
  have hb_inj : Function.Injective b.repr := b.repr.injective
  have hne : b.repr x₀ ≠ 0 := fun h => hx₀ (hb_inj (by rw [h, map_zero]))
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hne
  let w₀ : ↥W →ₗ[ZMod p] ZMod p := (Finsupp.lapply j).comp b.repr.toLinearMap
  have hw₀ : w₀ x₀ ≠ 0 := hj
  have hsurj : Function.Surjective w₀ := by
    have h1 : (1 : ZMod p) ∈ LinearMap.range w₀ := by
      have hmem : w₀ x₀ ∈ LinearMap.range w₀ := LinearMap.mem_range_self _ x₀
      have := Submodule.smul_mem (LinearMap.range w₀) (w₀ x₀)⁻¹ hmem
      simpa [inv_mul_cancel₀ hw₀] using this
    intro m
    have hm : m ∈ LinearMap.range w₀ := by
      simpa using Submodule.smul_mem (LinearMap.range w₀) m h1
    exact hm
  obtain ⟨y, hy⟩ := hsurj 1
  let π : W ⟶ Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p) :=
    Rep.ofHom (Work.SSGRoute.ExtChain.intertwiningMapOfAddHom W.hV2
      (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p)).hV2
      (w₀ : ↥W →+ ZMod p) (by intro g x; exact congrArg w₀ (hWtriv g x)))
  have hπx : (Rep.Hom.hom π) x₀ = w₀ x₀ := rfl
  let s₀ : ZMod p →ₗ[ZMod p] ↥W := LinearMap.toSpanSingleton (ZMod p) ↥W y
  have hs₀ : ∀ n : ZMod p, w₀ (s₀ n) = n := by
    intro n
    rw [LinearMap.toSpanSingleton_apply, map_smul, hy]
    simp
  let s : Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p) ⟶ W :=
    Rep.ofHom (Work.SSGRoute.ExtChain.intertwiningMapOfAddHom
      (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p)).hV2 W.hV2
      (s₀ : ZMod p →+ ↥W) (by intro g v; exact (hWtriv g (s₀ v)).symm))
  refine ⟨π, s, ?_, ?_⟩
  · rw [hπx]; exact hw₀
  · apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro n
    show w₀ (s₀ n) = n
    exact hs₀ n

/-- **The kernel of a nonzero functional as a subrepresentation, with its short exact sequence.**
For a finite `p`-torsion trivial `N`-module `W`, a surjective morphism `π : W ⟶ 𝔽_p` (`𝔽_p` the
trivial `ZMod p`-representation) with `π ≠ 0` has a kernel subrepresentation `V` with
`Nat.card V < Nat.card W`, and the sequence `0 ⟶ V ⟶ W --π--> 𝔽_p ⟶ 0` is short exact. -/
theorem exists_kernelRep_shortExact (p : ℕ) [Fact p.Prime] {N : Type} [Group N]
    (W : Rep.{0} SSGRoute.PTExt.Coeff N) [Finite W]
    (hWp : ∀ x : W, p • x = 0) (hWtriv : ∀ (g : N) (x : W), W.ρ g x = x)
    (π : W ⟶ Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))
    (hπ : Function.Surjective ⇑(Rep.Hom.hom π)) (hπ0 : π ≠ 0) :
    ∃ (V : Rep.{0} SSGRoute.PTExt.Coeff N) (_ : Finite V)
      (hVp : ∀ x : V, p • x = 0) (hVtriv : ∀ (g : N) (x : V), V.ρ g x = x)
      (ι : V ⟶ W) (h0 : CategoryTheory.CategoryStruct.comp ι π = 0),
      Nat.card V < Nat.card W ∧
        (CategoryTheory.ShortComplex.mk ι π h0).ShortExact := by
  classical
  let Vker : Submodule SSGRoute.PTExt.Coeff ↥W := LinearMap.ker (Rep.Hom.hom π).toLinearMap
  have hstab : ∀ g : N, Vker ≤ Submodule.comap (W.ρ g) Vker := by
    intro g x hx
    have hx0 : (Rep.Hom.hom π) x = 0 := hx
    have hg : (Rep.Hom.hom π) (W.ρ g x) = (Rep.Hom.hom π) x := by
      simpa [Rep.trivial_ρ] using
        LinearMap.congr_fun (Representation.IntertwiningMap.isIntertwining' (Rep.Hom.hom π) g) x
    show (Rep.Hom.hom π) (W.ρ g x) = 0
    rw [hg, hx0]
  let V : Rep.{0} SSGRoute.PTExt.Coeff N := Rep.subrepresentation W Vker hstab
  let ι : V ⟶ W := Rep.subtype W Vker hstab
  have h0 : ι ≫ π = 0 := by
    apply ConcreteCategory.hom_ext
    intro y
    show (Rep.Hom.hom π) ((Rep.Hom.hom ι) y) = 0
    exact y.2
  have hVker_ne_top : Vker ≠ ⊤ := by
    intro h
    apply hπ0
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have : x ∈ Vker := by rw [h]; trivial
    exact this
  have hcard : Nat.card V < Nat.card W := by
    haveI : Nontrivial (↥W ⧸ Vker) := Submodule.Quotient.nontrivial_iff.mpr hVker_ne_top
    haveI hfin : Finite (↥W ⧸ Vker) :=
      Finite.of_surjective (Submodule.mkQ Vker) (Submodule.mkQ_surjective Vker)
    haveI : Fintype (↥W ⧸ Vker) := Fintype.ofFinite _
    have hb : 1 < Nat.card (↥W ⧸ Vker) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
    have ha : 0 < Nat.card ↥Vker := Nat.card_pos
    have hmul : Nat.card ↥Vker * 1 < Nat.card ↥Vker * Nat.card (↥W ⧸ Vker) :=
      Nat.mul_lt_mul_of_pos_left hb ha
    rw [mul_one, ← Submodule.card_eq_card_quotient_mul_card Vker] at hmul
    exact hmul
  refine ⟨V, inferInstance, ?_, ?_, ι, h0, hcard, ?_⟩
  · intro x
    exact Subtype.ext (hWp x.1)
  · intro g x
    exact Subtype.ext (hWtriv g x.1)
  · refine Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise
      (k := SSGRoute.PTExt.Coeff) (G := N)
      (CategoryTheory.ShortComplex.mk ι π h0) ?_ ?_ ?_
    · rw [Rep.mono_iff_injective]
      intro a b hab
      exact Subtype.ext hab
    · rw [Rep.epi_iff_surjective]
      exact hπ
    · intro x hx
      exact ⟨⟨x, hx⟩, rfl⟩

end Work.SSGRoute.Sha2Lib
