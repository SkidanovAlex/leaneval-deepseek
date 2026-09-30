import Mathlib
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.cupNatural

/-!
# The cup product on relative singular cochains

For a topological space `X` and a subset `A ⊆ X`, the relative cochains `C^n(X,A)` are the
cochains vanishing on chains lying in `A` (`Work.Cohomology.relKern`).  This file shows that the
Alexander–Whitney cup product restricts to the relative cochains (the faces of a simplex lying in
`A` also lie in `A`), giving the **relative cup product**

  `relCup : C^m(X,A) → C^n(X,A) → C^{m+n}(X,A)`,

together with

* `relCup_coe` — its underlying cochain;
* `relIncl_relCup` — the inclusion `C^*(X,A) ⟶ C^*(X)` is a ring homomorphism (compatibility with
  the absolute cup product);
* `relDiff_relCup` — the Leibniz rule for the relative differential, which is what makes the product
  descend to relative cohomology `H^*(X,A;R)`.

The proofs are short because `relCup` is, by construction, the *restriction* of the absolute cup
product to the kernel of the restriction map `C^*(X) ⟶ C^*(A)`, so all the algebraic identities
follow from the absolute ones (`cupLeibniz`) by restricting to the submodule.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-- **The relative singular cohomology** `H^n(X,A;R)`: the cohomology of the relative cochain
complex `C^*(X,A)` (`Work.Cohomology.relComplex`). -/
abbrev relCohomology (X : TopCat) (A : Set X) (n : ℕ) : ModuleCat R :=
  (relComplex R X A).homology n

/-- A cochain killed by the pullback along a simplicial map `f` stays killed after cupping with any
cochain on the right, since the pullback is a ring homomorphism for the Alexander–Whitney product
(`cupNatural`). -/
theorem cup_mem_ker_dualMap {X Y : SSet} (f : X ⟶ Y) {n m : ℕ}
    {α : Cochain R Y n}
    (hα : ((SSet.chainComplexMap f (ModuleCat.of R R)).f n).hom.dualMap α = 0)
    (β : Cochain R Y m) :
    ((SSet.chainComplexMap f (ModuleCat.of R R)).f (n + m)).hom.dualMap
        (cup R Y α β) = 0 := by
  rw [← cupNatural R f α β, hα, cup_zero_left']

/-- A cochain killed by a simplicial map stays killed after cupping with any cochain on the left. -/
theorem cup_mem_ker_dualMap_right {X Y : SSet} (f : X ⟶ Y) {n m : ℕ}
    (α : Cochain R Y n)
    {β : Cochain R Y m}
    (hβ : ((SSet.chainComplexMap f (ModuleCat.of R R)).f m).hom.dualMap β = 0) :
    ((SSet.chainComplexMap f (ModuleCat.of R R)).f (n + m)).hom.dualMap
        (cup R Y α β) = 0 := by
  rw [← cupNatural R f α β, hβ, cup_zero_right']

/-- A relative cochain cupped with an arbitrary cochain is relative: the front face of a simplex
lying in `A` also lies in `A`. -/
theorem cup_mem_relKern_left (X : TopCat) (A : Set X) {n m : ℕ}
    {α : Cochain R (TopCat.toSSet.obj X) n} (hα : α ∈ relKern R X A n)
    (β : Cochain R (TopCat.toSSet.obj X) m) :
    cup R (TopCat.toSSet.obj X) α β ∈ relKern R X A (n + m) := by
  have h := hα
  rw [relKern, LinearMap.mem_ker, restr, dualChainMap_f_hom, chainMap_f_eq] at h
  rw [relKern, LinearMap.mem_ker, restr, dualChainMap_f_hom, chainMap_f_eq]
  exact cup_mem_ker_dualMap R (TopCat.toSSet.map (subtypeIncl X A)) h β

/-- A cochain cupped with a relative cochain is relative: the back face of a simplex lying in `A`
also lies in `A`. -/
theorem cup_mem_relKern_right (X : TopCat) (A : Set X) {n m : ℕ}
    (α : Cochain R (TopCat.toSSet.obj X) n)
    {β : Cochain R (TopCat.toSSet.obj X) m} (hβ : β ∈ relKern R X A m) :
    cup R (TopCat.toSSet.obj X) α β ∈ relKern R X A (n + m) := by
  have h := hβ
  rw [relKern, LinearMap.mem_ker, restr, dualChainMap_f_hom, chainMap_f_eq] at h
  rw [relKern, LinearMap.mem_ker, restr, dualChainMap_f_hom, chainMap_f_eq]
  exact cup_mem_ker_dualMap_right R (TopCat.toSSet.map (subtypeIncl X A)) α h

/-! ## The relative cup product -/

/-- **The relative cup product** `C^m(X,A) → C^n(X,A) → C^{m+n}(X,A)`, the restriction of the
Alexander–Whitney cup product to the cochains vanishing on `A`. -/
noncomputable def relCup (X : TopCat) (A : Set X) (n m : ℕ) :
    relKern R X A n →ₗ[R] relKern R X A m →ₗ[R] relKern R X A (n + m) where
  toFun a :=
    { toFun := fun b =>
        ⟨cup R (TopCat.toSSet.obj X) a.1 b.1, cup_mem_relKern_left R X A a.2 b.1⟩
      map_add' := fun b b' => by
        apply Subtype.ext
        simp only [Submodule.coe_add]
        exact (cupBilinear R (TopCat.toSSet.obj X) n m).2.2.1 a.1 b.1 b'.1
      map_smul' := fun c b => by
        apply Subtype.ext
        simp only [Submodule.coe_smul]
        exact (cupBilinear R (TopCat.toSSet.obj X) n m).2.2.2 c a.1 b.1 }
  map_add' := fun a a' => by
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    simp only [LinearMap.add_apply, Submodule.coe_add]
    exact (cupBilinear R (TopCat.toSSet.obj X) n m).1 a.1 a'.1 b.1
  map_smul' := fun c a => by
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    simp only [LinearMap.smul_apply, Submodule.coe_smul]
    exact (cupBilinear R (TopCat.toSSet.obj X) n m).2.1 c a.1 b.1

/-- The underlying cochain of a relative cup product. -/
@[simp]
theorem relCup_coe (X : TopCat) (A : Set X) {n m : ℕ}
    (a : relKern R X A n) (b : relKern R X A m) :
    (relCup R X A n m a b).1 = cup R (TopCat.toSSet.obj X) a.1 b.1 := rfl

/-- **The inclusion `C^*(X,A) ⟶ C^*(X)` is a ring homomorphism**: the relative cup product
included into the absolute cochains is the absolute cup product of the inclusions. -/
theorem relIncl_relCup (X : TopCat) (A : Set X) {n m : ℕ}
    (a : relKern R X A n) (b : relKern R X A m) :
    (relIncl R X A).f (n + m) (relCup R X A n m a b) =
      cup R (TopCat.toSSet.obj X) ((relIncl R X A).f n a) ((relIncl R X A).f m b) := rfl

/-! ## The relative differential and cocycles -/

/-- The differential of the singular cochain complex of a space is the transposed differential of
the singular chains, i.e. `cochainDiff`. -/
theorem singularCochain_d_eq (X : TopCat) (k : ℕ) :
    ((singularCochainComplex R X).d k (k+1)).hom = cochainDiffLM R (TopCat.toSSet.obj X) k := by
  simp only [singularCochainComplex, CochainComplex.of_d, dualDifferential, ModuleCat.hom_ofHom]
  ext α
  rfl

/-- The value of the differential of the singular cochain complex of a space on a cochain. -/
theorem singularCochain_d_apply (X : TopCat) {k : ℕ} (x : Cochain R (TopCat.toSSet.obj X) k) :
    ((singularCochainComplex R X).d k (k+1)).hom x =
      cochainDiff R (TopCat.toSSet.obj X) x := by
  rw [singularCochain_d_eq R X k]
  rfl

/-- **The product of two relative cocycles is a relative cocycle.** -/
theorem relDiffLM_relCup_of_cocycles (X : TopCat) (A : Set X) {n m : ℕ}
    (a : relKern R X A n) (b : relKern R X A m)
    (ha : relDiffLM R X A n a = 0) (hb : relDiffLM R X A m b = 0) :
    relDiffLM R X A (n + m) (relCup R X A n m a b) = 0 := by
  have ha' : cochainDiff R (TopCat.toSSet.obj X) a.1 = 0 := by
    have h := congrArg Subtype.val ha
    simp only [relDiffLM_coe, Submodule.coe_zero] at h
    rw [singularCochain_d_apply R X a.1] at h
    exact h
  have hb' : cochainDiff R (TopCat.toSSet.obj X) b.1 = 0 := by
    have h := congrArg Subtype.val hb
    simp only [relDiffLM_coe, Submodule.coe_zero] at h
    rw [singularCochain_d_apply R X b.1] at h
    exact h
  apply Subtype.ext
  rw [relDiffLM_coe, relCup_coe, Submodule.coe_zero,
    singularCochain_d_apply R X (cup R (TopCat.toSSet.obj X) a.1 b.1)]
  exact cochainDiff_cup_of_cocycles R (TopCat.toSSet.obj X) a.1 b.1 ha' hb'

/-! ## The class of a relative cocycle -/

/-- The cycle of the relative cochain complex associated with a relative cocycle. -/
noncomputable def relCocycleOf (X : TopCat) (A : Set X) {n : ℕ} (a : relKern R X A n)
    (h : relDiffLM R X A n a = 0) : ↑((relComplex R X A).cycles n) :=
  ((relComplex R X A).liftCycles
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R (relKern R X A n) a))
    (n + 1) ((ComplexShape.up ℕ).next_eq' (i := n) (j := n + 1) rfl) (by
      rw [relComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      change relDiffLM R X A n ((LinearMap.toSpanSingleton R (relKern R X A n) a) r) = 0
      rw [LinearMap.toSpanSingleton_apply, map_smul, h, smul_zero])).hom 1

/-- **The relative cohomology class of a relative cocycle.** -/
noncomputable def relClassOf (X : TopCat) (A : Set X) {n : ℕ} (a : relKern R X A n)
    (h : relDiffLM R X A n a = 0) : (relCohomology R X A n) :=
  ((relComplex R X A).homologyπ n).hom (relCocycleOf R X A a h)

end

end Work.Cohomology
