import Mathlib
import Submission.Work.Cohomology.Pullback

/-!
# The Alexander–Whitney cup product on singular cochains

The *cup product* on the cohomology of a space is induced by the **Alexander–Whitney** map
`C_*(X) ⟶ C_*(X) ⊗ C_*(X)`, `σ ↦ Σ_{p+q=n} σ_front(p) ⊗ σ_back(q)`, where `σ_front(p)` is the
face of `σ` spanned by its first `p+1` vertices and `σ_back(q)` the face spanned by its last
`q+1` vertices.

This file sets up exactly that, on the level of the singular chain complex of a simplicial set
(hence, via `TopCat.toSSet`, of a topological space):

* `frontIncl`/`backIncl` — the inclusions of the first `p+1` (resp. last `q+1`) vertices in
  `⦋p+q⦌`, as morphisms of `SimplexCategory`;
* `frontFace`/`backFace` — the induced maps on simplices (`X.map (frontIncl _ _ _).op` etc.);
* `frontChain`/`backChain` — the induced maps on the chain complex
  `(X.chainComplex R).X (n+m) ⟶ (X.chainComplex R).X n` (resp. `⟶ .X m`), defined through the
  coproduct universal property (`SSet.isColimitChainComplexXCofan`);
* `genEval` — evaluation of a cochain on a generator (a singular simplex);
* `cupHom`/`cup` — the Alexander–Whitney cup product of cochains
  `(α ⌣ β)(σ) = α(σ_front) β(σ_back)`, a linear map
  `(X.chainComplex R).X (n+m) →ₗ[R] R`;
* `ιChainComplex_cupHom` and `cup_apply` — its value on generators.

The remaining ingredients of the cup product (associativity, the Leibniz rule
`δ (α ⌣ β) = δα ⌣ β + (-1)^n α ⌣ δβ`, and the descent to cohomology) are delegated; they
depend only on the definitions here.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- The inclusion `⦋p⦌ ⟶ ⦋n⦌` of the first `p+1` vertices, for `p ≤ n`. -/
def frontIncl (p n : ℕ) (h : p ≤ n) : ⦋p⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk
    ⟨fun j => ⟨j.1, by have := j.2; simp only [SimplexCategory.len_mk] at this ⊢; omega⟩,
      fun _ _ hab => hab⟩

/-- The inclusion `⦋q⦌ ⟶ ⦋p+q⦌` of the last `q+1` vertices. -/
def backIncl (p q : ℕ) : ⦋q⦌ ⟶ ⦋p + q⦌ :=
  SimplexCategory.Hom.mk
    ⟨fun j => ⟨p + j.1, by have := j.2; simp only [SimplexCategory.len_mk] at this ⊢; omega⟩,
      fun _ _ hab => by show p + _ ≤ p + _; omega⟩

/-- The **front `n`-face** of an `N`-simplex: the face spanned by the first `n+1` vertices. -/
def frontFace (X : SSet) (n N : ℕ) (h : n ≤ N) : X _⦋N⦌ → X _⦋n⦌ :=
  X.map (frontIncl n N h).op

/-- The **back `m`-face** of an `(n+m)`-simplex: the face spanned by the last `m+1` vertices. -/
def backFace (X : SSet) (n m : ℕ) : X _⦋n + m⦌ → X _⦋m⦌ :=
  X.map (backIncl n m).op

variable (R : Type) [CommRing R]

/-- The front `n`-chains of an `N`-simplex: the map
`(X.chainComplex R).X N ⟶ (X.chainComplex R).X n` sending a simplex to its front `n`-face. -/
def frontChain (X : SSet) (N n : ℕ) (h : n ≤ N) :
    (X.chainComplex (ModuleCat.of R R)).X N ⟶ (X.chainComplex (ModuleCat.of R R)).X n :=
  (X.isColimitChainComplexXCofan (ModuleCat.of R R) N).desc
    (Cofan.mk ((X.chainComplex (ModuleCat.of R R)).X n)
      (fun σ => X.ιChainComplex (frontFace X n N h σ)))

/-- The back `m`-chains of an `(n+m)`-simplex: the map
`(X.chainComplex R).X (n+m) ⟶ (X.chainComplex R).X m` sending a simplex to its back `m`-face. -/
def backChain (X : SSet) (n m : ℕ) :
    (X.chainComplex (ModuleCat.of R R)).X (n + m) ⟶ (X.chainComplex (ModuleCat.of R R)).X m :=
  (X.isColimitChainComplexXCofan (ModuleCat.of R R) (n + m)).desc
    (Cofan.mk ((X.chainComplex (ModuleCat.of R R)).X m)
      (fun σ => X.ιChainComplex (backFace X n m σ)))

@[simp]
theorem ιChainComplex_frontChain (X : SSet) (N n : ℕ) (h : n ≤ N) (σ : X _⦋N⦌) :
    X.ιChainComplex (R := ModuleCat.of R R) σ ≫ frontChain R X N n h
      = X.ιChainComplex (frontFace X n N h σ) :=
  Cofan.IsColimit.fac _ _ _

@[simp]
theorem ιChainComplex_backChain (X : SSet) (n m : ℕ) (σ : X _⦋n + m⦌) :
    X.ιChainComplex (R := ModuleCat.of R R) σ ≫ backChain R X n m
      = X.ιChainComplex (backFace X n m σ) :=
  Cofan.IsColimit.fac _ _ _

/-- Evaluation of a cochain on a generator (a singular simplex). -/
def genEval (X : SSet) {n : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) (σ : X _⦋n⦌) : R :=
  α ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)

/-- The transpose of the differential: the "coboundary" `dα` of a cochain `α` on a simplicial set,
`(dα)(σ) = α(∂σ)`.  This is `Work.Cohomology.dualDifferential` for `X.chainComplex R`. -/
def cochainDiff (X : SSet) {n : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) :
    (X.chainComplex (ModuleCat.of R R)).X (n + 1) →ₗ[R] R :=
  α.comp ((X.chainComplex (ModuleCat.of R R)).d (n + 1) n).hom

@[simp]
theorem cochainDiff_apply (X : SSet) {n : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) (σ : X _⦋n + 1⦌) :
    genEval R X (cochainDiff R X α) σ =
      α (((X.chainComplex (ModuleCat.of R R)).d (n + 1) n).hom
        ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)) := by
  simp [cochainDiff, genEval, LinearMap.comp_apply]

/-- The **Alexander–Whitney cup product** of cochains, as a morphism in `ModuleCat R`. -/
def cupHom (X : SSet) {n m : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R) :
    (X.chainComplex (ModuleCat.of R R)).X (n + m) ⟶ ModuleCat.of R R :=
  (X.isColimitChainComplexXCofan (ModuleCat.of R R) (n + m)).desc
    (Cofan.mk (ModuleCat.of R R)
      (fun σ : X _⦋n + m⦌ =>
        ModuleCat.ofHom (LinearMap.toSpanSingleton R R
          (genEval R X α (frontFace X n (n + m) (Nat.le_add_right n m) σ) *
           genEval R X β (backFace X n m σ)))))

/-- The **Alexander–Whitney cup product** of a degree `n` and a degree `m` cochain, as a
linear functional on the `(n+m)`-chains:
`(α ⌣ β)(σ) = α(σ_front) · β(σ_back)`. -/
def cup (X : SSet) {n m : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R) :
    (X.chainComplex (ModuleCat.of R R)).X (n + m) →ₗ[R] R :=
  (cupHom R X α β).hom

@[simp]
theorem ιChainComplex_cupHom (X : SSet) {n m : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R) (σ : X _⦋n + m⦌) :
    X.ιChainComplex (R := ModuleCat.of R R) σ ≫ cupHom R X α β =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R R
        (genEval R X α (frontFace X n (n + m) (Nat.le_add_right n m) σ) *
         genEval R X β (backFace X n m σ))) :=
  Cofan.IsColimit.fac _ _ _

/-- The cup product evaluated on a generator. -/
theorem cup_apply (X : SSet) {n m : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R) (σ : X _⦋n + m⦌) :
    genEval R X (cup R X α β) σ =
      genEval R X α (frontFace X n (n + m) (Nat.le_add_right n m) σ) *
        genEval R X β (backFace X n m σ) := by
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶ ModuleCat.of R R) => g.hom 1)
    (ιChainComplex_cupHom R X α β σ)
  simpa only [cup, genEval, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] using h2

/-- The transpose of the differential, as a linear map. -/
def cochainDiffLM (X : SSet) (n : ℕ) :
    ((X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) →ₗ[R]
      ((X.chainComplex (ModuleCat.of R R)).X (n + 1) →ₗ[R] R) where
  toFun := cochainDiff R X
  map_add' := fun α β => by ext x; simp [cochainDiff, LinearMap.add_comp]
  map_smul' := fun a α => by ext x; simp [cochainDiff, LinearMap.smul_comp]

@[simp]
theorem cochainDiffLM_apply (X : SSet) (n : ℕ)
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) :
    cochainDiffLM R X n α = cochainDiff R X α := rfl

/-- The **singular cochain complex** of a simplicial set: the degreewise `R`-dual of the singular
chains, with differential the transpose of the boundary (`cochainDiff`).  This is the object whose
homology is `H^*(X; R)` and on which the Alexander–Whitney cup product lives. -/
def SSetCochainComplex (X : SSet) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R ((X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R))
    (fun n => ModuleCat.ofHom (cochainDiffLM R X n))
    (fun n => by
      have hcomp : (cochainDiffLM R X (n + 1)).comp (cochainDiffLM R X n) = 0 := by
        apply LinearMap.ext
        intro α
        apply LinearMap.ext
        intro x
        have hd : ((X.chainComplex (ModuleCat.of R R)).d (n + 1) n).hom
            (((X.chainComplex (ModuleCat.of R R)).d (n + 2) (n + 1)).hom x) = 0 := by
          have h : ((X.chainComplex (ModuleCat.of R R)).d (n + 1) n).hom.comp
              ((X.chainComplex (ModuleCat.of R R)).d (n + 2) (n + 1)).hom = 0 := by
            rw [← ModuleCat.hom_comp, HomologicalComplex.d_comp_d, ModuleCat.hom_zero]
          exact LinearMap.congr_fun h x
        show cochainDiff R X (cochainDiff R X α) x = 0
        simp only [cochainDiff, LinearMap.comp_apply]
        rw [hd, map_zero]
      apply ModuleCat.hom_ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
      exact hcomp)

/-- The differential of the singular cochain complex of a simplicial set is `cochainDiff`. -/
@[simp]
theorem SSetCochainComplex_d (X : SSet) (n : ℕ) :
    (SSetCochainComplex R X).d n (n + 1) = ModuleCat.ofHom (cochainDiffLM R X n) := by
  simp only [SSetCochainComplex, CochainComplex.of_d]

/-- The cycle of the singular cochain complex of a simplicial set associated with a cocycle: a
cochain `α` with `cochainDiff α = 0`, viewed as an element of the cycles in degree `n`. -/
def cocycleOf (X : SSet) {n : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (h : cochainDiff R X α = 0) : ↑((SSetCochainComplex R X).cycles n) :=
  ((SSetCochainComplex R X).liftCycles
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R
      ((X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) α))
    (n + 1) ((ComplexShape.up ℕ).next_eq' (i := n) (j := n + 1) rfl) (by
      rw [SSetCochainComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      change cochainDiffLM R X n ((LinearMap.toSpanSingleton R
        ((X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) α) r) = 0
      rw [LinearMap.toSpanSingleton_apply]
      change cochainDiffLM R X n (r • α) = 0
      rw [map_smul, cochainDiffLM_apply, h, smul_zero])).hom 1

/-- The cohomology class of a cocycle cochain, as an element of `H^n`. -/
def cohomologyClassOf (X : SSet) {n : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (h : cochainDiff R X α = 0) : ↑((SSetCochainComplex R X).homology n) :=
  ((SSetCochainComplex R X).homologyπ n).hom (cocycleOf R X α h)


/-- The unit `0`-cochain: the functional which is `1` on every `0`-simplex (the augmentation). -/
def unitCochain (X : SSet) : (X.chainComplex (ModuleCat.of R R)).X 0 →ₗ[R] R :=
  ModuleCat.Hom.hom ((X.isColimitChainComplexXCofan (ModuleCat.of R R) 0).desc
    (Cofan.mk (ModuleCat.of R R) (fun _ => 𝟙 (ModuleCat.of R R))))

/-- The unit cochain takes the value `1` on every generator. -/
@[simp]
theorem genEval_unitCochain (X : SSet) (σ : X _⦋0⦌) :
    genEval R X (unitCochain R X) σ = 1 := by
  have h := Cofan.IsColimit.fac (X.isColimitChainComplexXCofan (ModuleCat.of R R) 0)
      (fun _ : X _⦋0⦌ => 𝟙 (ModuleCat.of R R)) σ
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶ ModuleCat.of R R) => g.hom 1) h
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h2
  rw [genEval]
  exact h2


/-- **Bridge.**  The singular cochain complex of a topological space *is* the cochain complex of
its singular simplicial set (definitionally, since `singularChains R X` is by definition the chain
complex of `TopCat.toSSet.obj X`).  Consequently every construction and theorem of this file
(the Alexander–Whitney cup product, the Leibniz rule, `SSetCochainComplex`, …) applies verbatim to
`singularCochainComplex R X` and `singularCohomology R n X`. -/
theorem singularCochainComplex_eq (R : Type) [CommRing R] (X : TopCat) :
    singularCochainComplex R X = SSetCochainComplex R (TopCat.toSSet.obj X) := rfl

/-- **Bridge**, cohomological form. -/
theorem singularCohomology_eq (R : Type) [CommRing R] (X : TopCat) (n : ℕ) :
    singularCohomology R n X = (SSetCochainComplex R (TopCat.toSSet.obj X)).homology n := rfl

end

end Work.Cohomology
