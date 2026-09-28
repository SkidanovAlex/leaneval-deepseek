import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.Crux.CapSub
import Submission.Work.Cohomology.RelMVDefs
import Submission.Work.Cohomology.RelCap
import Submission.Work.Cohomology.relMV_shortExact

/-!
# The cap product against the Mayer–Vietoris short exact sequences

Chain-level compatibility squares for the comparison of the relative and absolute
Mayer–Vietoris short exact sequences by the cap product with a relative cocycle.

* `chainComplexMap_comp_f`, `chainComplexMap_comp` — functoriality of `SSet.chainComplexMap`;
* `mono_homOfLe_chainComplex_f` — inclusions of subcomplexes are degreewise injective;
* `capSub_comp_incl_sub` — the cap product commutes with the inclusion of subcomplexes;
* `exists_lift_of_range_subset` — a simplex with image in `A` is a pushforward from `A`;
* `genEval_eq_zero_of_isSmallIn` — a relative cochain vanishes on small simplices lying in `A`;
* `smallInToSmall_capSub_eq_zero` — the cap product kills the small chains lying in `A`;
* `subInclChain_capSub_eq_zero` — its mirror for the inclusion `subInclChain`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **Functoriality of the chain complex of a simplicial set** (degreewise form). -/
theorem chainComplexMap_comp_f {C : Type} [Category C] [HasCoproducts C] [Preadditive C]
    {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z) (R : C) (n : ℕ) :
    (SSet.chainComplexMap (f ≫ g) R).f n =
      (SSet.chainComplexMap f R).f n ≫ (SSet.chainComplexMap g R).f n := by
  apply SSet.chainComplex_hom_ext
  intro x
  rw [SSet.ι_chainComplexMap_f, ← Category.assoc, SSet.ι_chainComplexMap_f,
    SSet.ι_chainComplexMap_f]
  rfl

/-- **Functoriality of the chain complex of a simplicial set.** -/
theorem chainComplexMap_comp {C : Type} [Category C] [HasCoproducts C] [Preadditive C]
    {X Y Z : SSet} (f : X ⟶ Y) (g : Y ⟶ Z) (R : C) :
    SSet.chainComplexMap (f ≫ g) R = SSet.chainComplexMap f R ≫ SSet.chainComplexMap g R := by
  apply HomologicalComplex.hom_ext
  intro n
  exact chainComplexMap_comp_f f g R n

variable {Y : SSet}

/-- The chain map induced by the inclusion of subcomplexes is degreewise a monomorphism. -/
theorem mono_homOfLe_chainComplex_f (S S' : Y.Subcomplex) (h : S ≤ S') (n : ℕ) :
    Mono ((SSet.chainComplexMap (Subfunctor.homOfLe h) (ModuleCat.of ℤ ℤ)).f n) := by
  change Mono (coprodMap (R := ℤ) (fun σ : S _⦋n⦌ =>
    (Subfunctor.homOfLe h).app (Opposite.op ⦋n⦌) σ))
  refine mono_coprodMap _ (fun a b hab => ?_)
  exact Subtype.ext (by simpa using congrArg Subtype.val hab)

/-- **The cap product commutes with the inclusion of subcomplexes.** -/
theorem capSub_comp_incl_sub (S S' : Y.Subcomplex) (h : S ≤ S') (n m : ℕ) (α : Cochain ℤ Y n) :
    capSub S n m α ≫ (SSet.chainComplexMap (Subfunctor.homOfLe h) (ModuleCat.of ℤ ℤ)).f m =
      (SSet.chainComplexMap (Subfunctor.homOfLe h) (ModuleCat.of ℤ ℤ)).f (n + m) ≫
        capSub S' n m α := by
  have hι : ∀ k : ℕ,
      (SSet.chainComplexMap (Subfunctor.homOfLe h) (ModuleCat.of ℤ ℤ)).f k ≫
        (SSet.chainComplexMap S'.ι (ModuleCat.of ℤ ℤ)).f k =
      (SSet.chainComplexMap S.ι (ModuleCat.of ℤ ℤ)).f k := by
    intro k
    apply SSet.chainComplex_hom_ext
    intro x
    rw [← Category.assoc, SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f,
      SSet.ι_chainComplexMap_f]
    rfl
  haveI : Mono ((SSet.chainComplexMap S'.ι (ModuleCat.of ℤ ℤ)).f m) :=
    mono_subfunctor_incl_chainComplex_f S' m
  refine (cancel_mono ((SSet.chainComplexMap S'.ι (ModuleCat.of ℤ ℤ)).f m)).mp ?_
  rw [Category.assoc, hι, capSub_comp_incl S n m α]
  rw [Category.assoc, capSub_comp_incl S' n m α, ← Category.assoc, hι]

/-- **Lifting a simplex whose image lies in `A`.**  A singular simplex of `X` whose image is
contained in `A` is the pushforward of a singular simplex of the subspace `A`. -/
theorem exists_lift_of_range_subset {X : TopCat} (A : Set X) {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n)
    (hσ : Set.range (fun z : stdSimplex ℝ (Fin (n.unop.len + 1)) =>
      TopCat.toSSetObjEquivT X n σ z) ⊆ A) :
    ∃ τ : (TopCat.toSSet.obj (TopCat.of ↥A)).obj n,
      (TopCat.toSSet.map (subtypeIncl X A)).app n τ = σ := by
  let g : C(stdSimplex ℝ (Fin (n.unop.len + 1)), ↥A) :=
    ⟨fun z => ⟨TopCat.toSSetObjEquivT X n σ z, hσ ⟨z, rfl⟩⟩,
      (TopCat.toSSetObjEquivT X n σ).continuous.subtype_mk _⟩
  refine ⟨(TopCat.toSSetObjEquivT (TopCat.of ↥A) n).symm g, ?_⟩
  apply (TopCat.toSSetObjEquivT X n).injective
  ext z
  rfl

/-- **A relative cochain vanishes on every small simplex lying in `A`.** -/
theorem genEval_eq_zero_of_isSmallIn {X : TopCat} (U V A : Set X) {n : ℕ}
    (α : Cochain ℤ (TopCat.toSSet.obj X) n) (hα : α ∈ relKern ℤ X A n)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌))
    (hσ : IsSmallIn U V A σ) :
    genEval ℤ (TopCat.toSSet.obj X) α σ = 0 := by
  obtain ⟨τ, hτ⟩ := exists_lift_of_range_subset A σ hσ.2
  rw [← hτ]
  exact genEval_eq_zero_of_mem_relKern ℤ X A α hα τ

/-- **The cap product with a relative cocycle kills the chains lying in `A`.** -/
theorem smallInToSmall_capSub_eq_zero (X : TopCat) (U V A : Set X) (n m : ℕ)
    (α : Cochain ℤ (TopCat.toSSet.obj X) n) (hα : α ∈ relKern ℤ X A n) :
    (smallInToSmall U V A).f (n + m) ≫ capSub (smallSubcomplex U V) n m α = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [comp_zero, ← Category.assoc]
  rw [show (smallInToSmall U V A) = SSet.chainComplexMap
    (Subfunctor.homOfLe (smallInSubcomplex_le U V A)) (ModuleCat.of ℤ ℤ) from rfl]
  rw [SSet.ι_chainComplexMap_f]
  rw [ιChainComplex_capSub]
  have hfront : genEval ℤ (TopCat.toSSet.obj X) α
      (frontFace (TopCat.toSSet.obj X) n (n + m) (Nat.le_add_right n m)
        ((smallSubcomplex U V).ι.app (Opposite.op ⦋n + m⦌)
          ((Subfunctor.homOfLe (smallInSubcomplex_le U V A)).app
            (Opposite.op ⦋n + m⦌) σ))) = 0 :=
    genEval_eq_zero_of_isSmallIn U V A α hα _
      (IsSmallIn.map (frontIncl n (n + m) (Nat.le_add_right n m)).op
        (show IsSmallIn U V A
          ((smallSubcomplex U V).ι.app (Opposite.op ⦋n + m⦌)
            ((Subfunctor.homOfLe (smallInSubcomplex_le U V A)).app
              (Opposite.op ⦋n + m⦌) σ)) from σ.2))
  rw [hfront]
  simp

/-- **The cap product with a relative cocycle kills the `C`-chains inside the `B`-chains**, for
`C ⊆ B`: the mirror of `smallInToSmall_capSub_eq_zero` for the inclusion `subInclChain`. -/
theorem subInclChain_capSub_eq_zero (X : TopCat) (U V B C : Set X) (hCB : C ⊆ B) (n m : ℕ)
    (α : Cochain ℤ (TopCat.toSSet.obj X) n) (hα : α ∈ relKern ℤ X C n) :
    (subInclChain U V hCB).f (n + m) ≫ capSub (smallInSubcomplex U V B) n m α = 0 := by
  haveI hmono : Mono ((SSet.chainComplexMap
      (Subfunctor.homOfLe (smallInSubcomplex_le U V B)) (ModuleCat.of ℤ ℤ)).f m) :=
    mono_homOfLe_chainComplex_f _ _ (smallInSubcomplex_le U V B) m
  have hkey : (subInclChain U V hCB).f (n + m) ≫
      (SSet.chainComplexMap (Subfunctor.homOfLe (smallInSubcomplex_le U V B))
        (ModuleCat.of ℤ ℤ)).f (n + m) =
      (smallInToSmall U V C).f (n + m) := by
    rw [← HomologicalComplex.comp_f]
    exact congrArg (fun (g : smallInChains U V C ⟶ smallChains U V) => g.f (n + m))
      (subInclChain_smallInToSmall U V hCB)
  refine (cancel_mono ((SSet.chainComplexMap
      (Subfunctor.homOfLe (smallInSubcomplex_le U V B)) (ModuleCat.of ℤ ℤ)).f m)).mp ?_
  rw [zero_comp, Category.assoc, capSub_comp_incl_sub (smallInSubcomplex U V B)
    (smallSubcomplex U V) (smallInSubcomplex_le U V B) n m α, ← Category.assoc, hkey]
  exact smallInToSmall_capSub_eq_zero X U V C n m α hα

/-- **The inverse component iso against the first projection.**  The `m`-component of the
biproduct of chain complexes is the biproduct of the components, and the canonical comparison
`HomologicalComplex.biprodXIso` is compatible with `biprod.fst`. -/
theorem biprodXIso_inv_fst (K L : ChainComplex (ModuleCat ℤ) ℕ) (m : ℕ) :
    (HomologicalComplex.biprodXIso K L m).inv ≫ (biprod.fst : K ⊞ L ⟶ K).f m =
      (biprod.fst : K.X m ⊞ L.X m ⟶ K.X m) := by
  rw [← HomologicalComplex.biprodXIso_hom_fst K L m, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- The same for the second projection. -/
theorem biprodXIso_inv_snd (K L : ChainComplex (ModuleCat ℤ) ℕ) (m : ℕ) :
    (HomologicalComplex.biprodXIso K L m).inv ≫ (biprod.snd : K ⊞ L ⟶ L).f m =
      (biprod.snd : K.X m ⊞ L.X m ⟶ L.X m) := by
  rw [← HomologicalComplex.biprodXIso_hom_snd K L m, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

end

end Work.Cohomology
