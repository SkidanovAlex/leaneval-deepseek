import Mathlib
import Submission.Work.Cohomology.AlexanderWhitney

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Associativity of the Alexander–Whitney cup product

The Alexander–Whitney cup product on singular cochains of a simplicial set
(`Work.Cohomology.cup`, defined in `Submission/Work/Cohomology/AlexanderWhitney.lean`) is
associative:

`(α ⌣ β) ⌣ γ = α ⌣ (β ⌣ γ)`,

where the two sides live in degrees `((n+m)+k)` and `(n+(m+k))` respectively; they are compared
after transporting the left-hand side along `Nat.add_assoc n m k`.

The proof is the standard computation on generators.  Both sides are linear functionals on the
`(n+m+k)`-chains, so by `cup_ext` it suffices to compare their values on every singular simplex
`σ`.  The left-hand side is a cast (in the grading) of a cup product to a different degree; the
key ingredient is `cupAssoc_genEval_cast`, which evaluates such a cast on `σ` by transporting `σ`
along the corresponding isomorphism `eqToHom (congrArg SimplexCategory.mk h)` of `SimplexCategory`
(the "identity on vertices").  The two products of `genEval`s that result are then matched face by
face using the vertex computations `cupAssoc_face_A`/`B`/`C`, and the conclusion is `mul_assoc`.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R] (X : SSet)

/-! ## Vertex computations in `SimplexCategory` -/

/-- The front inclusion is the identity on vertices. -/
private lemma cupAssoc_hom_frontIncl_val (p n : ℕ) (h : p ≤ n) (j : Fin (p+1)) :
    ((ConcreteCategory.hom (frontIncl p n h)) j).val = j.val := rfl

/-- The back inclusion shifts vertices by `p`. -/
private lemma cupAssoc_hom_backIncl_val (p q : ℕ) (j : Fin (q+1)) :
    ((ConcreteCategory.hom (backIncl p q)) j).val = p + j.val := rfl

/-- The identification of `⦋a⦌` with `⦋b⦌` induced by `a = b` is the identity on vertices. -/
private lemma cupAssoc_hom_eqToHom_val {a b : ℕ} (h : (⦋a⦌ : SimplexCategory) = ⦋b⦌)
    (i : Fin (⦋a⦌.len+1)) :
    ((ConcreteCategory.hom (eqToHom h)) i).val = i.val := by cases h; simp

/-- Composition of the contravariant action of a simplicial set on opposite morphisms. -/
private lemma cupAssoc_map_op_comp {a b c : ℕ} (φ : ⦋a⦌ ⟶ ⦋b⦌) (ψ : ⦋c⦌ ⟶ ⦋a⦌)
    (x : X _⦋b⦌) :
    X.map ψ.op (X.map φ.op x) = X.map (ψ ≫ φ).op x := by
  rw [← CategoryTheory.comp_apply (X.map φ.op) (X.map ψ.op) x, ← Functor.map_comp, ← op_comp]

/-! ## Transport of generators and of `genEval` along a degree equality -/

/-- The `R`-basis generator of the `b`-simplex `σ`, transported to degree `a` along `h : a = b`,
is the generator of the transported simplex. -/
private lemma cupAssoc_iota_transport {a b : ℕ} (h : a = b) (σ : X _⦋b⦌) :
    (eqToHom (congrArg (fun t => (X.chainComplex (ModuleCat.of R R)).X t) h.symm)).hom
        (((X.ιChainComplex (R := ModuleCat.of R R) σ)).hom 1) =
      ((X.ιChainComplex (R := ModuleCat.of R R)
        (X.map (eqToHom (congrArg SimplexCategory.mk h)).op σ)).hom 1) := by
  cases h
  simp [eqToHom_refl]

/-- `genEval` on the transport along a degree equality `h : a = b` of a cochain is `genEval` of
that cochain on the transported simplex. -/
private lemma cupAssoc_genEval_cast {a b : ℕ} (h : a = b)
    (F : (X.chainComplex (ModuleCat.of R R)).X a →ₗ[R] R) (σ : X _⦋b⦌) :
    genEval R X (h ▸ F) σ =
      genEval R X F (X.map (eqToHom (congrArg SimplexCategory.mk h)).op σ) := by
  rw [genEval, genEval]
  have h1 : (h ▸ F) =
      F.comp (eqToHom (congrArg (fun t => (X.chainComplex (ModuleCat.of R R)).X t) h.symm)).hom := by
    cases h; rfl
  rw [h1, LinearMap.comp_apply]
  congr 1
  exact cupAssoc_iota_transport R X h σ

/-! ## The three face comparisons

All three reduce, via the functoriality of `X`, to an identity of morphisms of `SimplexCategory`
that is checked vertexwise using `cupAssoc_hom_frontIncl_val`/`cupAssoc_hom_backIncl_val` and
`cupAssoc_hom_eqToHom_val`. -/

/-- The front `n`-face of the transported `(n+(m+k))`-simplex is the front `n`-face of `σ`. -/
private lemma cupAssoc_face_A (n m k : ℕ) (σ : X _⦋n+(m+k)⦌) :
    frontFace X n (n+m) (Nat.le_add_right n m)
        (frontFace X (n+m) ((n+m)+k) (Nat.le_add_right (n+m) k)
          (X.map (eqToHom (congrArg SimplexCategory.mk (Nat.add_assoc n m k))).op σ))
      = frontFace X n (n+(m+k)) (Nat.le_add_right n (m+k)) σ := by
  have hφ : (frontIncl n (n+m) (Nat.le_add_right n m) ≫
      frontIncl (n+m) ((n+m)+k) (Nat.le_add_right (n+m) k)) ≫
      eqToHom (congrArg SimplexCategory.mk (Nat.add_assoc n m k))
      = frontIncl n (n+(m+k)) (Nat.le_add_right n (m+k)) := by
    refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
    apply Fin.ext
    simp only [CategoryTheory.comp_apply, cupAssoc_hom_frontIncl_val, cupAssoc_hom_eqToHom_val]
  simp only [frontFace]
  rw [cupAssoc_map_op_comp, cupAssoc_map_op_comp, hφ]

/-- The back `m`-face of the front `(n+m)`-face of the transported simplex is the corresponding
front `m`-face of the back `(m+k)`-face of `σ`. -/
private lemma cupAssoc_face_B (n m k : ℕ) (σ : X _⦋n+(m+k)⦌) :
    backFace X n m
        (frontFace X (n+m) ((n+m)+k) (Nat.le_add_right (n+m) k)
          (X.map (eqToHom (congrArg SimplexCategory.mk (Nat.add_assoc n m k))).op σ))
      = frontFace X m (m+k) (Nat.le_add_right m k) (backFace X n (m+k) σ) := by
  have hφ : (backIncl n m ≫ frontIncl (n+m) ((n+m)+k) (Nat.le_add_right (n+m) k)) ≫
      eqToHom (congrArg SimplexCategory.mk (Nat.add_assoc n m k))
      = frontIncl m (m+k) (Nat.le_add_right m k) ≫ backIncl n (m+k) := by
    refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
    apply Fin.ext
    simp only [CategoryTheory.comp_apply, cupAssoc_hom_backIncl_val,
      cupAssoc_hom_frontIncl_val, cupAssoc_hom_eqToHom_val]
  simp only [backFace, frontFace]
  rw [cupAssoc_map_op_comp, cupAssoc_map_op_comp, cupAssoc_map_op_comp, hφ]

/-- The back `k`-face of the transported simplex is the iterated back `k`-face of `σ`. -/
private lemma cupAssoc_face_C (n m k : ℕ) (σ : X _⦋n+(m+k)⦌) :
    backFace X (n+m) k
        (X.map (eqToHom (congrArg SimplexCategory.mk (Nat.add_assoc n m k))).op σ)
      = backFace X m k (backFace X n (m+k) σ) := by
  have hφ : backIncl (n+m) k ≫ eqToHom (congrArg SimplexCategory.mk (Nat.add_assoc n m k))
      = backIncl m k ≫ backIncl n (m+k) := by
    refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
    apply Fin.ext
    simp only [CategoryTheory.comp_apply, cupAssoc_hom_backIncl_val, cupAssoc_hom_eqToHom_val]
    omega
  simp only [backFace]
  rw [cupAssoc_map_op_comp, cupAssoc_map_op_comp, hφ]

/-! ## Extensionality of cochains on generators -/

/-- A linear functional on the `n`-chains is determined by its values on the generators
`ιChainComplex σ`. -/
private lemma cupAssoc_cup_ext (X : SSet) {n : ℕ}
    {a b : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R}
    (h : ∀ σ : X _⦋n⦌, genEval R X a σ = genEval R X b σ) : a = b := by
  have hmor : ModuleCat.ofHom a = ModuleCat.ofHom b := by
    apply SSet.chainComplex_hom_ext (C := ModuleCat R)
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    exact h σ
  simpa using congrArg ModuleCat.Hom.hom hmor

/-! ## Associativity -/

theorem cupAssoc (R : Type) [CommRing R] (X : SSet) {n m k : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R)
    (γ : (X.chainComplex (ModuleCat.of R R)).X k →ₗ[R] R) :
    (Nat.add_assoc n m k ▸ Work.Cohomology.cup R X (Work.Cohomology.cup R X α β) γ) =
      Work.Cohomology.cup R X α (Work.Cohomology.cup R X β γ) := by
  apply cupAssoc_cup_ext R X
  intro σ
  rw [cupAssoc_genEval_cast R X (Nat.add_assoc n m k) (cup R X (cup R X α β) γ) σ]
  rw [cup_apply R X (cup R X α β) γ, cup_apply R X α β,
      cup_apply R X α (cup R X β γ), cup_apply R X β γ]
  rw [cupAssoc_face_A X n m k σ, cupAssoc_face_B X n m k σ, cupAssoc_face_C X n m k σ]
  ring

end

end Work.Cohomology
