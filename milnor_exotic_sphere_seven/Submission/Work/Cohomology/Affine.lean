import Mathlib
import Submission.Work.Cohomology.CupRing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Linear (affine) simplices of the standard simplex

This file begins the *subdivision* chapter: the geometric input needed for the
small-simplices/Mayer–Vietoris theorem (`Submission/NOTES.md`, "the road from here").

The standard topological `n`-simplex is `Delta n = TopCat.of (stdSimplex ℝ (Fin (n+1)))`, whose
underlying type is the subtype of `Fin (n+1) → ℝ` of nonnegative functions summing to `1`.  The
basic object here is the **linear simplex with a given vertex family**

`affineSimplex v : C(Δᵏ, Δⁿ)`,  `t ↦ ∑ j, t j • v j`   (`v : Fin (k+1) → Δⁿ`),

the affine map determined by the vertices `v`.  Singular simplices of `Δⁿ` which are affine maps
are the pieces into which the barycentric subdivision cuts `Δⁿ`.

## Main definitions

* `Delta n` — the standard topological `n`-simplex as a topological space;
* `affineSimplex v` — the affine map `C(Δᵏ, Δⁿ)` determined by the vertices `v`;
* `linSimplex v` — the same as a singular simplex of `Delta n`.

## Main results

* `affineSimplex_apply` — the coordinates of `affineSimplex v t`;
* `affineSimplex_vertex` — the value at a vertex of `Δᵏ`.

The functoriality of `affineSimplex` (`affineSimplex v (stdSimplex.map f t) = affineSimplex (v ∘ f) t`)
and the resulting boundary formula for `linSimplex` are delegated separately; they are what makes
the subdivision chain maps well defined.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- The standard topological `n`-simplex, as a topological space. -/
abbrev Delta (n : ℕ) : TopCat := TopCat.of (stdSimplex ℝ (Fin (n + 1)))

/-- **The linear simplex with vertices `v`**: the continuous map of standard simplices which sends
`t` to the convex combination `∑ⱼ tⱼ • vⱼ`. -/
def affineSimplex {n k : ℕ} (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))) :
    C(stdSimplex ℝ (Fin (k + 1)), stdSimplex ℝ (Fin (n + 1))) where
  toFun t :=
    ⟨fun i => ∑ j, t j * v j i, by
      constructor
      · intro i
        exact Finset.sum_nonneg fun j _ => mul_nonneg (t.2.1 j) ((v j).2.1 i)
      · have h1 : (∑ i, ∑ j, t j * v j i) = ∑ j, t j * (∑ i, v j i) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
        rw [h1]
        simp⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine continuous_finsetSum _ fun j _ => ?_
    exact ((continuous_apply j).comp continuous_subtype_val).mul continuous_const

/-- The coordinates of the affine simplex: `(affineSimplex v t) i = ∑ j, t j * v j i`. -/
@[simp]
theorem affineSimplex_apply {n k : ℕ} (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1)))
    (t : stdSimplex ℝ (Fin (k + 1))) (i : Fin (n + 1)) :
    affineSimplex v t i = ∑ j, t j * v j i := rfl

/-- The value of the affine simplex at a vertex. -/
theorem affineSimplex_vertex {n k : ℕ} (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1)))
    (i : Fin (k + 1)) : affineSimplex v (stdSimplex.vertex i) = v i := by
  ext j
  rw [affineSimplex_apply]
  simp [stdSimplex.vertex, Pi.single_apply]

/-- **Port bridge (Lean v4.35).**  Mathlib's singular simplices are now continuous maps out of
`Convexity.StdSimplex ℝ ι` (finitely supported probability weights); this identifies it with the
subset model `stdSimplex ℝ ι ⊆ ι → ℝ` used throughout this development. -/
def stdSimplexHomeomorph (ι : Type) [Fintype ι] :
    Convexity.StdSimplex ℝ ι ≃ₜ stdSimplex ℝ ι where
  toFun t := ⟨fun i => t.weights i, fun i => t.weights_nonneg i, by
    have h := t.total
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h⟩
  invFun t := ⟨Finsupp.equivFunOnFinite.symm t.1, fun i => t.2.1 i, by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]; exact t.2.2⟩
  left_inv t := by ext i; rfl
  right_inv t := by ext i; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk; apply continuous_pi; intro i
    exact Convexity.StdSimplex.continuous_weights_apply ℝ i
  continuous_invFun := by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous_iff]
    exact continuous_subtype_val

/-- Port bridge: the subset-model simplex on a subsingleton index type is a subsingleton (this
instance existed for `stdSimplex` before Lean v4.35). -/
instance stdSimplex_subsingleton {ι : Type} [Fintype ι] [Subsingleton ι] :
    Subsingleton (stdSimplex ℝ ι) :=
  (stdSimplexHomeomorph ι).symm.injective.subsingleton

instance stdSimplex_fin_one_subsingleton : Subsingleton (stdSimplex ℝ (Fin 1)) :=
  stdSimplex_subsingleton

instance stdSimplex_fin_zero_add_one_subsingleton : Subsingleton (stdSimplex ℝ (Fin (0 + 1))) :=
  stdSimplex_fin_one_subsingleton

/-- Port bridge: an `Inhabited` instance for the subset-model simplex (as before Lean v4.35). -/
instance stdSimplex_inhabited {ι : Type} [Fintype ι] [Inhabited ι] : Inhabited (stdSimplex ℝ ι) :=
  ⟨stdSimplexHomeomorph ι default⟩

instance stdSimplex_fin_zero_add_one_inhabited : Inhabited (stdSimplex ℝ (Fin (0 + 1))) :=
  ⟨stdSimplexHomeomorph (Fin 1) default⟩

theorem stdSimplexHomeomorph_apply (ι : Type) [Fintype ι] (t : Convexity.StdSimplex ℝ ι) (i : ι) :
    (stdSimplexHomeomorph ι t : ι → ℝ) i = t.weights i := rfl

theorem stdSimplexHomeomorph_single {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) :
    stdSimplexHomeomorph ι (Convexity.StdSimplex.single i) = stdSimplex.vertex i := by
  apply Subtype.ext; funext j
  show (Convexity.StdSimplex.single (R := ℝ) i).weights j = _
  simp [stdSimplex.vertex, Pi.single_apply, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

theorem stdSimplexHomeomorph_map {ι κ : Type} [Fintype ι] [Fintype κ] (f : ι → κ)
    (t : Convexity.StdSimplex ℝ ι) :
    stdSimplexHomeomorph κ (Convexity.StdSimplex.map f t)
      = stdSimplex.map f (stdSimplexHomeomorph ι t) := by
  classical
  apply Subtype.ext; funext j
  show (Convexity.StdSimplex.map f t).weights j = _
  show _ = FunOnFinite.linearMap ℝ ℝ f (stdSimplexHomeomorph ι t : ι → ℝ) j
  rw [Convexity.StdSimplex.weights_map, Finsupp.mapDomain_fintype, Finsupp.finset_sum_apply,
    FunOnFinite.linearMap_apply_apply]
  simp only [Finsupp.single_apply, Finset.sum_filter, stdSimplexHomeomorph_apply]

/-- **The affine simplex as a singular simplex of `Δⁿ`.** -/
def linSimplex {n k : ℕ} (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))) :
    (TopCat.toSSet.obj (Delta n)) _⦋k⦌ :=
  (TopCat.toSSetObjEquiv (Delta n) (Opposite.op ⦋k⦌)).symm
    ((affineSimplex v).comp (stdSimplexHomeomorph (Fin (k + 1)) :
        C(Convexity.StdSimplex ℝ (Fin (k + 1)), stdSimplex ℝ (Fin (k + 1)))))

/-- The affine point of `Δⁿ` with vertex family `v : Fin (k+1) → Δⁿ`, evaluated at a point: the
underlying continuous map of `linSimplex v`. -/
theorem toSSetObjEquiv_linSimplex {n k : ℕ} (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))) :
    TopCat.toSSetObjEquiv (Delta n) (Opposite.op ⦋k⦌) (linSimplex v) =
      (affineSimplex v).comp (stdSimplexHomeomorph (Fin (k + 1)) :
        C(Convexity.StdSimplex ℝ (Fin (k + 1)), stdSimplex ℝ (Fin (k + 1)))) := by
  rw [linSimplex, Equiv.apply_symm_apply]

/-- The affine simplex with the vertices of the standard simplex is the identity map (this is the
base case of the subdivision recursion). -/
theorem affineSimplex_id {n : ℕ} (t : stdSimplex ℝ (Fin (n + 1))) :
    affineSimplex (fun i : Fin (n + 1) => stdSimplex.vertex i) t = t := by
  apply Subtype.ext
  funext i
  show (∑ j, t j * (stdSimplex.vertex j : Fin (n + 1) → ℝ) i) = t i
  simp [stdSimplex.vertex, Pi.single_apply]

end

end Work.Cohomology

/-! ## Port bridge (Lean v4.35): singular simplices in the old subset model

Mathlib's `TopCat.toSSetObjEquiv` now identifies singular simplices with continuous maps out of
`Convexity.StdSimplex ℝ (Fin (n+1))`.  `TopCat.toSSetObjEquivOld` is the same identification
transported along `Work.Cohomology.stdSimplexHomeomorph` to the subset model
`stdSimplex ℝ (Fin (n+1))`, together with the old-model forms of its face/degeneracy/naturality
lemmas. -/

universe u

namespace TopCat

open CategoryTheory Simplicial Opposite Work.Cohomology

/-- Singular simplices as continuous maps out of the subset model `stdSimplex ℝ (Fin (n+1))`. -/
noncomputable def toSSetObjEquivOld (X : TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    (toSSet.obj X).obj n ≃ C(stdSimplex ℝ (Fin (n.unop.len + 1)), X) where
  toFun σ := (X.toSSetObjEquiv n σ).comp
    ((stdSimplexHomeomorph (Fin (n.unop.len + 1))).symm :
      C(stdSimplex ℝ (Fin (n.unop.len + 1)), Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))))
  invFun f := (X.toSSetObjEquiv n).symm (f.comp
    (stdSimplexHomeomorph (Fin (n.unop.len + 1)) :
      C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)), stdSimplex ℝ (Fin (n.unop.len + 1)))))
  left_inv σ := by
    apply (X.toSSetObjEquiv n).injective
    rw [Equiv.apply_symm_apply]
    ext z
    simp
  right_inv f := by
    ext z
    simp

lemma toSSetObjEquivOld_apply (X : TopCat.{u}) (n : SimplexCategoryᵒᵖ) (σ : (toSSet.obj X).obj n)
    (z : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    X.toSSetObjEquivOld n σ z
      = X.toSSetObjEquiv n σ ((stdSimplexHomeomorph (Fin (n.unop.len + 1))).symm z) := rfl

lemma toSSetObjEquivOld_eq_apply (X : TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (σ : (toSSet.obj X).obj n) (z : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    X.toSSetObjEquiv n σ z
      = X.toSSetObjEquivOld n σ (stdSimplexHomeomorph (Fin (n.unop.len + 1)) z) := by
  rw [toSSetObjEquivOld_apply, Homeomorph.symm_apply_apply]

/-- Naturality of `toSSetObjEquivOld` in the space: `toSSet.map f` is postcomposition. -/
lemma toSSetObjEquivOld_map_apply {X Y : TopCat.{u}} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
    (x : (toSSet.obj X).obj n) (z : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    Y.toSSetObjEquivOld n ((toSSet.map f).app n x) z = f (X.toSSetObjEquivOld n x z) := rfl

/-- The image of a singular simplex is the same in either model of the standard simplex. -/
lemma range_toSSetObjEquivOld (X : TopCat.{u}) (n : SimplexCategoryᵒᵖ) (σ : (toSSet.obj X).obj n) :
    Set.range (fun z : stdSimplex ℝ (Fin (n.unop.len + 1)) => X.toSSetObjEquivOld n σ z)
      = Set.range (fun z : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)) =>
          X.toSSetObjEquiv n σ z) :=
  (stdSimplexHomeomorph _).symm.surjective.range_comp (fun z => X.toSSetObjEquiv n σ z)

/-- `stdSimplex.map` in the old model corresponds to `Convexity.StdSimplex.map`. -/
lemma stdSimplexHomeomorph_symm_map {ι κ : Type} [Fintype ι] [Fintype κ] (f : ι → κ)
    (z : stdSimplex ℝ ι) :
    (stdSimplexHomeomorph κ).symm (stdSimplex.map f z)
      = Convexity.StdSimplex.map f ((stdSimplexHomeomorph ι).symm z) := by
  apply (stdSimplexHomeomorph κ).injective
  rw [Homeomorph.apply_symm_apply, stdSimplexHomeomorph_map, Homeomorph.apply_symm_apply]

lemma toSSetObjEquivOld_naturality_apply {X : TopCat.{u}} {n m : SimplexCategory} (f : n ⟶ m)
    (x : (toSSet.obj X).obj (op m)) (z : stdSimplex ℝ (Fin (n.len + 1))) :
    X.toSSetObjEquivOld (op n) ((toSSet.obj X).map f.op x) z =
      X.toSSetObjEquivOld (op m) x (stdSimplex.map f z) := by
  rw [toSSetObjEquivOld_apply, toSSetObjEquivOld_apply, stdSimplexHomeomorph_symm_map]
  rfl

lemma toSSetObjEquivOld_δ_apply {X : TopCat.{u}} {n : ℕ}
    (x : toSSet.obj X _⦋n + 1⦌) (i : Fin (n + 2)) (z : stdSimplex ℝ (Fin (n + 1))) :
    X.toSSetObjEquivOld _ ((toSSet.obj X).δ i x) z =
      X.toSSetObjEquivOld _ x (stdSimplex.map i.succAbove z) := by
  rw [toSSetObjEquivOld_apply, toSSetObjEquivOld_apply, stdSimplexHomeomorph_symm_map]
  exact TopCat.toSSetObjEquiv_δ_apply x i _

lemma toSSetObjEquivOld_σ_apply {X : TopCat.{u}} {n : ℕ}
    (x : toSSet.obj X _⦋n⦌) (i : Fin (n + 1)) (z : stdSimplex ℝ (Fin (n + 2))) :
    X.toSSetObjEquivOld _ ((toSSet.obj X).σ i x) z =
      X.toSSetObjEquivOld _ x (stdSimplex.map i.predAbove z) := by
  rw [toSSetObjEquivOld_apply, toSSetObjEquivOld_apply, stdSimplexHomeomorph_symm_map]
  exact TopCat.toSSetObjEquiv_σ_apply x i _

lemma toSSetObjEquivOld_symm_naturality {X : TopCat.{u}} {n m : SimplexCategory} (f : n ⟶ m)
    (g : C(stdSimplex ℝ (Fin (m.len + 1)), X)) :
    (toSSet.obj X).map f.op ((X.toSSetObjEquivOld _).symm g) =
      (X.toSSetObjEquivOld _).symm (g.comp ⟨stdSimplex.map f, stdSimplex.continuous_map _⟩) := by
  apply (X.toSSetObjEquivOld _).injective
  rw [Equiv.apply_symm_apply]
  ext z
  rw [toSSetObjEquivOld_naturality_apply, Equiv.apply_symm_apply]
  rfl

end TopCat
