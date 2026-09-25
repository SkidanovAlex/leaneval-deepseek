import Mathlib
import Submission.Work.CFT.ClassFormation.Defs
import Submission.Work.CFTLib.rankP_le_add_of_shortExact_of_finite
import Submission.Work.CFTLib.rankP_le_rankP_of_injective
import Submission.Work.CFTLib.rankP_h0_oUnits_le

/-!
# The `p`-rank of the middle term of a short exact sequence in Tate cohomology

Let `G` be a finite group, `p` a prime and `0 → X₁ → X₂ → X₃ → 0` a short exact sequence of
`ℤ[G]`-modules.  Then for every `n : ℤ` the long exact sequence in Tate cohomology
`… → Ĥⁿ(X₁) → Ĥⁿ(X₂) → Ĥⁿ(X₃) → Ĥⁿ⁺¹(X₁) → …` gives, at the middle term, an exact pair of
maps `f : Ĥⁿ(X₁) → Ĥⁿ(X₂)`, `g : Ĥⁿ(X₂) → Ĥⁿ(X₃)` with `range f = ker g`, and `g` is not
surjective in general (only its image is the kernel of the connecting map).

The main result of this file,

`Work.CFTLib.rankP_tate_middle_le`,

bounds the `p`-rank of the middle term by the sum of the outer ones, assuming only that
`𝔽_p ⊗ Ĥⁿ(X₁)` is finite dimensional (so that `rankP p Ĥⁿ(X₁)` is meaningful) and that
`Ĥⁿ(X₃)` is finite.

The proof is elementary.  Decomposing `Ĥⁿ(X₂)` along the two maps,
`0 → ker g → Ĥⁿ(X₂) → im g → 0` is a short exact sequence, so the subadditivity of `rankP`
along a short exact sequence (`Work.CFTLib.rankP_le_add_of_shortExact_of_finite`) gives

  `rankP p Ĥⁿ(X₂) ≤ rankP p (ker g) + rankP p (im g)`.

Now `ker g = range f` is a quotient of `Ĥⁿ(X₁)`, so `rankP p (ker g) ≤ rankP p Ĥⁿ(X₁)`;
and `im g` is a subgroup of the finite group `Ĥⁿ(X₃)`, so `rankP p (im g) ≤ rankP p Ĥⁿ(X₃)`.

## Main results

* `Work.CFTLib.moduleFinite_tensor_zmod_of_module_eq`
* `Work.CFTLib.rankP_le_add_of_range_eq_ker_of_finite`
* `Work.CFTLib.rankP_tate_middle_le`
-/

open CategoryTheory
open scoped TensorProduct

set_option linter.style.haveILetI false

namespace Work.CFTLib

/-! ### Moving between `ℤ`-module structures on an abelian group

The group `ℤ`-module structure on an abelian group is unique (`Subsingleton (Module ℤ A)`), so
the type `𝔽_p ⊗_ℤ A` is unaffected by which `Module ℤ A` instance is used.  The following
lemma is the transport of finiteness along this (propositional) equality, which is needed
because `Work.CFT.ClassFormation.rankP p A` unfolds to the `𝔽_p`-tensor product with the
*canonical* `ℤ`-module structure `AddCommGroup.toIntModule`, whereas the objects of
`ModuleCat ℤ` carry their own (equal) structure. -/
theorem moduleFinite_tensor_zmod_of_module_eq {p : ℕ} {A : Type} [AddCommGroup A] (i : Module ℤ A)
    (h : @Module.Finite (ZMod p) (@TensorProduct ℤ _ (ZMod p) A _ _ _ i) _ _ _) :
    @Module.Finite (ZMod p)
      (@TensorProduct ℤ _ (ZMod p) A _ _ _ (AddCommGroup.toIntModule A)) _ _ _ := by
  have hmod : i = AddCommGroup.toIntModule A := Subsingleton.elim i _
  cases hmod
  exact h

/-! ### The abstract rank inequality -/

/-- **Subadditivity of `rankP` for a pair of maps with `range f = ker g`.**

If `f : A →+ B` and `g : B →+ C` are additive homomorphisms with `f.range = g.ker`, if
`𝔽_p ⊗_ℤ A` is finite dimensional over `𝔽_p` and `C` is finite, then
`rankP p B ≤ rankP p A + rankP p C`.

Compared with `Work.CFTLib.rankP_le_add_of_shortExact_of_finite`, `g` is *not* assumed to be
surjective; instead the finiteness of `C` is used to control `g.range`, which is a subgroup of
`C`. -/
theorem rankP_le_add_of_range_eq_ker_of_finite {p : ℕ} [Fact p.Prime]
    {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : B →+ C)
    (hfg : f.range = g.ker)
    (hA : Module.Finite (ZMod p) (TensorProduct ℤ (ZMod p) A))
    (hC : Finite C) :
    Work.CFT.ClassFormation.rankP p B ≤
      Work.CFT.ClassFormation.rankP p A + Work.CFT.ClassFormation.rankP p C := by
  -- the short exact sequence `0 → ker g → B → im g → 0`
  have hsurjg : Function.Surjective
      (g.codRestrict g.range (fun x => AddMonoidHom.mem_range.mpr ⟨x, rfl⟩)) :=
    fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩
  have hinj : Function.Injective (AddSubgroup.subtype g.ker) := fun x y h => Subtype.ext h
  have hex : LinearMap.range ((AddSubgroup.subtype g.ker).toIntLinearMap)
      = LinearMap.ker
        ((g.codRestrict g.range (fun x => AddMonoidHom.mem_range.mpr ⟨x, rfl⟩)).toIntLinearMap) := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      have hy' : g x = 0 := by rw [← hy]; exact y.2
      simp only [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap,
        AddMonoidHom.codRestrict_apply]
      exact Subtype.ext hy'
    · intro hx
      have hx' : g x = 0 := by
        have h := hx
        simp only [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap,
          AddMonoidHom.codRestrict_apply] at h
        simpa using congrArg Subtype.val h
      simp only [LinearMap.mem_range, AddMonoidHom.coe_toIntLinearMap]
      exact ⟨⟨x, hx'⟩, rfl⟩
  -- `ker g = range f` is a quotient of `A`
  have hfker : ∀ a : A, f a ∈ g.ker := fun a => by
    rw [← hfg]; exact AddMonoidHom.mem_range.mpr ⟨a, rfl⟩
  have hesurj : Function.Surjective (f.codRestrict g.ker hfker) := by
    intro y
    have hy : y.1 ∈ f.range := by rw [hfg]; exact y.2
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hy
    exact ⟨a, Subtype.ext ha⟩
  have hA' : Module.Finite (ZMod p) (ZMod p ⊗[ℤ] A) := hA
  -- hence `𝔽_p ⊗ ker g` is finite dimensional
  have hsurjT : Function.Surjective
      ((f.codRestrict g.ker hfker).toIntLinearMap.baseChange (ZMod p)) :=
    LinearMap.baseChange_surjective (ZMod p) hesurj
  haveI hX' : Module.Finite (ZMod p) (ZMod p ⊗[ℤ] ↥(g.ker)) :=
    Module.Finite.of_surjective _ hsurjT
  have h1 := rankP_le_add_of_shortExact_of_finite (AddSubgroup.subtype g.ker)
      (g.codRestrict g.range (fun x => AddMonoidHom.mem_range.mpr ⟨x, rfl⟩)) hinj hsurjg hex hX'
  haveI : Module.Finite (ZMod p) (ZMod p ⊗[ℤ] A) := hA
  have h2 : Work.CFT.ClassFormation.rankP p ↥(g.ker) ≤
      Work.CFT.ClassFormation.rankP p A :=
    rankP_le_of_surjective (f.codRestrict g.ker hfker) hesurj
  have h3 : Work.CFT.ClassFormation.rankP p ↥(g.range) ≤
      Work.CFT.ClassFormation.rankP p C := by
    haveI : Finite ↥(g.range) := Subtype.finite
    haveI : Module.Finite ℤ ↥(g.range) := Module.Finite.of_finite
    haveI : Module.Finite ℤ C := Module.Finite.of_finite
    exact rankP_le_rankP_of_injective p (AddSubgroup.subtype g.range)
      (fun x y h => Subtype.ext h)
  linarith [h1, h2, h3]

/-! ### The Tate cohomology statement -/

/-- **The `p`-rank of the middle term of a short exact sequence in Tate cohomology.**

If `0 → X₁ → X₂ → X₃ → 0` is a short exact sequence of `ℤ[G]`-modules, `𝔽_p ⊗ Ĥⁿ(X₁)` is
finite dimensional and `Ĥⁿ(X₃)` is finite, then
`rankP p Ĥⁿ(X₂) ≤ rankP p Ĥⁿ(X₁) + rankP p Ĥⁿ(X₃)`.

The maps `f`, `g` of the long exact sequence are exact at the middle term, and
`rankP_le_add_of_range_eq_ker_of_finite` finishes the proof. -/
theorem rankP_tate_middle_le {G : Type} [Group G] [Fintype G] (p : ℕ) [Fact p.Prime]
    (S : CategoryTheory.ShortComplex (Rep ℤ G)) (hS : S.ShortExact) (n : ℤ)
    (hX : Module.Finite (ZMod p) (TensorProduct ℤ (ZMod p)
      ↑(tateCohomology S.X₁ n)))
    (hZ : Finite ↥(tateCohomology S.X₃ n)) :
    Work.CFT.ClassFormation.rankP p ↑(tateCohomology S.X₂ n)
      ≤ Work.CFT.ClassFormation.rankP p ↑(tateCohomology S.X₁ n)
        + Work.CFT.ClassFormation.rankP p ↑(tateCohomology S.X₃ n) := by
  classical
  haveI hP : (tateCohomologyFunctor (R := ℤ) (G := G) n).PreservesZeroMorphisms := by
    unfold tateCohomologyFunctor
    infer_instance
  -- exactness of the middle term of the long exact sequence
  have hSℂ := TateCohomology.map_tateComplexFunctor_shortExact hS
  have hexact := (CategoryTheory.ShortComplex.exact_iff_of_hasForget (C := ModuleCat ℤ) _).mp
    (hSℂ.homology_exact₂ n)
  -- the two maps of the long exact sequence, as additive homomorphisms
  let f : ↥(tateCohomology S.X₁ n) →+ ↥(tateCohomology S.X₂ n) :=
    ((tateCohomologyFunctor (R := ℤ) (G := G) n).map S.f).hom.toAddMonoidHom
  let g : ↥(tateCohomology S.X₂ n) →+ ↥(tateCohomology S.X₃ n) :=
    ((tateCohomologyFunctor (R := ℤ) (G := G) n).map S.g).hom.toAddMonoidHom
  -- `range f ≤ ker g`: the two maps compose to zero
  have hkey2 : ∀ x, g (f x) = 0 := by
    intro x
    have hzero : ((tateCohomologyFunctor (R := ℤ) (G := G) n).map S.f ≫
        (tateCohomologyFunctor (R := ℤ) (G := G) n).map S.g) = 0 := by
      rw [← CategoryTheory.Functor.map_comp, S.zero, CategoryTheory.Functor.map_zero]
    have h := congrArg
      (fun (φ : tateCohomology S.X₁ n ⟶ tateCohomology S.X₃ n) =>
        (ModuleCat.Hom.hom φ) x) hzero
    simpa [f, g] using h
  -- `ker g ≤ range f`: exactness at the middle term
  have hkey : ∀ y, g y = 0 → y ∈ f.range := by
    intro y hy
    obtain ⟨x, hx⟩ := hexact y hy
    exact AddMonoidHom.mem_range.mpr ⟨x, hx⟩
  have hfg : f.range = g.ker := le_antisymm
    (by rintro y ⟨x, rfl⟩; exact AddMonoidHom.mem_ker.mpr (hkey2 x))
    (by intro y hy; exact hkey y (AddMonoidHom.mem_ker.mp hy))
  -- the canonical `ℤ`-module structure on `Ĥⁿ(X₁)`
  have hXcanon := moduleFinite_tensor_zmod_of_module_eq (p := p)
    ((tateCohomology S.X₁ n).isModule) hX
  exact rankP_le_add_of_range_eq_ker_of_finite f g hfg hXcanon hZ

end Work.CFTLib
