import Mathlib
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.relIncl_relCupH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Naturality of the relative cup product on cohomology

`Work.Cohomology.relCupH'` is a chosen bilinear pairing on the relative cohomology `H^*(X,A;R)`
satisfying the defining computation rule `relCupH'_apply` on classes of relative cocycles.  This
file proves that this pairing is **natural** in the pair `(X,A)`: if `f : X₁ ⟶ X₂` is a continuous
map with `f '' A₁ ⊆ A₂`, then the induced map of pairs
`φ = relComplexMap R A₁ A₂ f h : C^*(X₂,A₂) ⟶ C^*(X₁,A₁)` satisfies

`φ*(x ⌣ y) = (φ* x) ⌣ (φ* y)`.

The proof reduces, via `exists_relClassOf`, to the case where `x` and `y` are the classes of
relative cocycles `a` and `b`:

* `relCupH'_apply` computes both products on the classes of the products of the cocycles;
* `homologyMap_relComplexMap_relClassOf` identifies the image of the class of a relative cocycle
  `a` under `φ*` with the class of the relative cocycle `relMapLM R A₁ A₂ f h a` (for which one
  needs `relDiffLM_relMapLM`, the statement that the pushforward of a relative cocycle along a map
  of pairs is again a relative cocycle);
* at the cochain level, `relCupNaturalMap` identifies the two products, by restricting the absolute
  naturality `cupNatural` of the Alexander–Whitney product.

## Main results

* `relCupNaturalMap` — naturality of the relative cup product on cochains;
* `relDiffLM_relMapLM` — a relative cocycle pushes forward along a map of pairs;
* `homologyMap_relComplexMap_relClassOf` — `φ*` on the class of a relative cocycle;
* `relClassOf_proof_irrel`, `relClassOf_congr` — the class of a relative cocycle does not depend on
  the proof of the cocycle condition;
* `relCupHNatural` — naturality of the relative cup product on cohomology.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-! ## Cochain-level naturality of the relative cup product -/

/-- **Naturality of the relative cup product on cochains.**  Since `relCup` is the restriction of
the absolute Alexander–Whitney cup product `cup` to the relative cochains, this is the absolute
naturality `cupNatural` restricted to submodules. -/
theorem relCupNaturalMap {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) {n m : ℕ} (a : relKern R X₂ A₂ n) (b : relKern R X₂ A₂ m) :
    relMapLM R A₁ A₂ f h (n + m) (relCup R X₂ A₂ n m a b) =
      relCup R X₁ A₁ n m (relMapLM R A₁ A₂ f h n a) (relMapLM R A₁ A₂ f h m b) := by
  apply Subtype.ext
  simp only [relMapLM_coe, relCup_coe]
  exact (cupNatural R (TopCat.toSSet.map f) a.1 b.1).symm

/-! ## A relative cocycle pushes forward along a map of pairs -/

/-- The pushforward of a relative cocycle along a map of pairs is again a relative cocycle: the
image under `iCycles` of the `cyclesMap` of the cycle associated with a relative cocycle is
`relMapLM` of the cocycle, which is therefore killed by the differential. -/
theorem relDiffLM_relMapLM {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) {n : ℕ} (a : relKern R X₂ A₂ n)
    (ha : relDiffLM R X₂ A₂ n a = 0) :
    relDiffLM R X₁ A₁ n (relMapLM R A₁ A₂ f h n a) = 0 := by
  rw [← relComplex_d_apply R X₁ A₁]
  have hci := congrArg
    (fun (g : (relComplex R X₂ A₂).cycles n ⟶ (relComplex R X₁ A₁).X n) =>
      g.hom (relCocycleOf R X₂ A₂ a ha))
    (HomologicalComplex.cyclesMap_i (relComplexMap R A₁ A₂ f h) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, relComplexMap_f, ModuleCat.hom_ofHom] at hci
  rw [iCycles_relCocycleOf R X₂ A₂ a ha] at hci
  have hh := iCycles_d_apply_K (relComplex R X₁ A₁) n
    ((HomologicalComplex.cyclesMap (relComplexMap R A₁ A₂ f h) n) (relCocycleOf R X₂ A₂ a ha))
  rw [hci] at hh
  exact hh

/-! ## The induced map of pairs on the class of a relative cocycle -/

/-- **`φ*` on the class of a relative cocycle.**  The image under the induced map of pairs of the
relative cohomology class of a relative cocycle `a` is the class of the relative cocycle
`relMapLM R A₁ A₂ f h a`. -/
theorem homologyMap_relComplexMap_relClassOf {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂) {n : ℕ} (a : relKern R X₂ A₂ n)
    (ha : relDiffLM R X₂ A₂ n a = 0) :
    (HomologicalComplex.homologyMap (relComplexMap R A₁ A₂ f h) n).hom (relClassOf R X₂ A₂ a ha) =
      relClassOf R X₁ A₁ (relMapLM R A₁ A₂ f h n a) (relDiffLM_relMapLM R A₁ A₂ f h a ha) := by
  have h1 : (HomologicalComplex.homologyMap (relComplexMap R A₁ A₂ f h) n).hom
        (relClassOf R X₂ A₂ a ha) =
      ((relComplex R X₁ A₁).homologyπ n).hom
        ((HomologicalComplex.cyclesMap (relComplexMap R A₁ A₂ f h) n).hom
          (relCocycleOf R X₂ A₂ a ha)) :=
    homologyMap_homologyπ R (relComplexMap R A₁ A₂ f h) n (relCocycleOf R X₂ A₂ a ha)
  have h2 : ((relComplex R X₁ A₁).homologyπ n).hom
        ((HomologicalComplex.cyclesMap (relComplexMap R A₁ A₂ f h) n).hom
          (relCocycleOf R X₂ A₂ a ha)) =
      relClassOf R X₁ A₁ (relMapLM R A₁ A₂ f h n a) (relDiffLM_relMapLM R A₁ A₂ f h a ha) := by
    apply congrArg ((relComplex R X₁ A₁).homologyπ n).hom
    apply iCycles_injective_K (relComplex R X₁ A₁) n
    have hci := congrArg
      (fun (g : (relComplex R X₂ A₂).cycles n ⟶ (relComplex R X₁ A₁).X n) =>
        g.hom (relCocycleOf R X₂ A₂ a ha))
      (HomologicalComplex.cyclesMap_i (relComplexMap R A₁ A₂ f h) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, relComplexMap_f,
      ModuleCat.hom_ofHom] at hci
    rw [hci, iCycles_relCocycleOf R X₂ A₂ a ha,
      iCycles_relCocycleOf R X₁ A₁ (relMapLM R A₁ A₂ f h n a)
        (relDiffLM_relMapLM R A₁ A₂ f h a ha)]
    rfl
  exact h1.trans h2

/-! ## Independence of the class of the proof of the cocycle condition -/

/-- The relative cohomology class of a relative cocycle does not depend on the proof that the
cochain is a cocycle. -/
theorem relClassOf_proof_irrel (X : TopCat) (A : Set X) {n : ℕ} (a : relKern R X A n)
    (ha ha' : relDiffLM R X A n a = 0) :
    relClassOf R X A a ha = relClassOf R X A a ha' :=
  congrArg (relClassOf R X A a) (Subsingleton.elim ha ha')

/-- The relative cohomology class of a relative cocycle depends only on the cocycle. -/
theorem relClassOf_congr (X : TopCat) (A : Set X) {n : ℕ} {a a' : relKern R X A n}
    (ha : relDiffLM R X A n a = 0) (ha' : relDiffLM R X A n a' = 0) (h : a = a') :
    relClassOf R X A a ha = relClassOf R X A a' ha' := by
  subst h
  exact relClassOf_proof_irrel R X A a ha ha'

/-! ## Naturality -/

theorem relCupHNatural (R : Type) [CommRing R] {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂)
    (f : X₁ ⟶ X₂) (h : ∀ x ∈ A₁, f x ∈ A₂) (n m : ℕ)
    (x : Work.Cohomology.relCohomology R X₂ A₂ n)
    (y : Work.Cohomology.relCohomology R X₂ A₂ m) :
    (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap R A₁ A₂ f h) (n + m)).hom
        (Work.Cohomology.relCupH' R X₂ A₂ n m x y) =
      Work.Cohomology.relCupH' R X₁ A₁ n m
        ((HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap R A₁ A₂ f h) n).hom x)
        ((HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap R A₁ A₂ f h) m).hom y) := by
  obtain ⟨a, ha, rfl⟩ := exists_relClassOf R X₂ A₂ n x
  obtain ⟨b, hb, rfl⟩ := exists_relClassOf R X₂ A₂ m y
  refine Eq.trans (congrArg (fun z => (HomologicalComplex.homologyMap (relComplexMap R A₁ A₂ f h)
      (n + m)).hom z) (relCupH'_apply R X₂ A₂ a b ha hb)) ?_
  refine Eq.trans (homologyMap_relComplexMap_relClassOf R A₁ A₂ f h
    (relCup R X₂ A₂ n m a b) (relDiffLM_relCup_of_cocycles R X₂ A₂ a b ha hb)) ?_
  refine Eq.trans (relClassOf_congr R X₁ A₁
    (relDiffLM_relMapLM R A₁ A₂ f h (relCup R X₂ A₂ n m a b)
      (relDiffLM_relCup_of_cocycles R X₂ A₂ a b ha hb))
    (relDiffLM_relCup_of_cocycles R X₁ A₁ (relMapLM R A₁ A₂ f h n a)
      (relMapLM R A₁ A₂ f h m b)
      (relDiffLM_relMapLM R A₁ A₂ f h a ha) (relDiffLM_relMapLM R A₁ A₂ f h b hb))
    (relCupNaturalMap R A₁ A₂ f h a b)) ?_
  refine Eq.trans (relCupH'_apply R X₁ A₁ (relMapLM R A₁ A₂ f h n a) (relMapLM R A₁ A₂ f h m b)
    (relDiffLM_relMapLM R A₁ A₂ f h a ha) (relDiffLM_relMapLM R A₁ A₂ f h b hb)).symm ?_
  exact ((congrArg (fun z => relCupH' R X₁ A₁ n m z
        ((HomologicalComplex.homologyMap (relComplexMap R A₁ A₂ f h) m).hom
          (relClassOf R X₂ A₂ b hb)))
      (homologyMap_relComplexMap_relClassOf R A₁ A₂ f h a ha)).trans
    (congrArg (fun w => relCupH' R X₁ A₁ n m
        (relClassOf R X₁ A₁ (relMapLM R A₁ A₂ f h n a) (relDiffLM_relMapLM R A₁ A₂ f h a ha)) w)
      (homologyMap_relComplexMap_relClassOf R A₁ A₂ f h b hb))).symm

end

end Work.Cohomology
