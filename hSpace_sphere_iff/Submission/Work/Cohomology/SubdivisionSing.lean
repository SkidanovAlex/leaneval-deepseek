/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The barycentric subdivision operator on singular chains

`Submission.Work.Cohomology.SubdivisionChain` defines the subdivisions `Sd(Δⁿ)` and the
homotopy chains `T(Δⁿ)` as chains of *pieces* (vertex lists) of the standard simplex.
This file transports them to singular chains of the standard simplices, and then to the singular
chains of an arbitrary topological space.

* `pushSimplex`/`pushChain` — pushforward of simplices/chains along a continuous map, together with
  its compatibility with faces (`pushSimplex_δ`) and with the boundary (`pushChain_sbdry`);
* `simplexOfPiece q` — the singular simplex `Δ^m → Δ^N` with vertices `q`;
* `toSingChain` — the induced map from chains of pieces to singular chains of `Δ^N`, compatible with
  the boundary (`toSingChain_pieceBdry`) and with pushforwards (`toSingChain_pushPieces`);
* `sdUniv n`, `tUniv n` — the universal subdivision and homotopy chains, with the two identities
  `sbdry_sdUniv` and `sbdry_tUniv`;
* `sdFun`, `tFun` — the subdivision and homotopy operators on the singular chains of an arbitrary
  space `X`, with the chain-level identities `sdFun_chainMap`, `tFun_homotopy`, and the preservation
  of the submodule of chains lying in a subset (`sdFun_mem`, `tFun_mem`).
-/
import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.SubdivisionChain
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.Cohomology

open CategoryTheory Simplicial Opposite

namespace Submission.Cohomology

noncomputable section

/-! ## Pushforward of singular chains along a continuous map -/

/-- The pushforward of a simplex of the singular complex along a continuous map. -/
def pushSimplex {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) : (TopCat.toSSet.obj Y).obj (op ⦋n⦌) :=
  (TopCat.toSSetObjEquivT Y (op ⦋n⦌)).symm
    ((TopCat.Hom.equivContinuousMap X Y f).comp (TopCat.toSSetObjEquivT X (op ⦋n⦌) σ))

@[simp] lemma pushSimplex_apply {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    TopCat.toSSetObjEquivT Y (op ⦋n⦌) (pushSimplex f n σ)
      = (TopCat.Hom.equivContinuousMap X Y f).comp (TopCat.toSSetObjEquivT X (op ⦋n⦌) σ) := by
  rw [pushSimplex, Equiv.apply_symm_apply]

/-- The pushforward of simplices commutes with the face maps. -/
lemma pushSimplex_δ {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (i : Fin (n+2))
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n+1⦌)) :
    (TopCat.toSSet.obj Y).δ i (pushSimplex f (n+1) σ)
      = pushSimplex f n ((TopCat.toSSet.obj X).δ i σ) := by
  apply (TopCat.toSSetObjEquivT Y (op ⦋n⦌)).injective
  ext z
  rw [TopCat.toSSetObjEquivT_δ_apply, pushSimplex_apply, ContinuousMap.comp_apply,
    pushSimplex_apply, ContinuousMap.comp_apply, TopCat.toSSetObjEquivT_δ_apply]

/-- The pushforward of simplices is functorial. -/
lemma pushSimplex_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    pushSimplex (f ≫ g) n σ = pushSimplex g n (pushSimplex f n σ) := by
  apply (TopCat.toSSetObjEquivT Z (op ⦋n⦌)).injective
  rw [pushSimplex_apply, pushSimplex_apply, pushSimplex_apply,
    show TopCat.Hom.equivContinuousMap X Z (f ≫ g)
      = (TopCat.Hom.equivContinuousMap Y Z g).comp (TopCat.Hom.equivContinuousMap X Y f) from rfl,
    ContinuousMap.comp_assoc]

/-- The pushforward of singular chains along a continuous map. -/
def pushChain {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    SChain (TopCat.toSSet.obj X) ℚ n →ₗ[ℚ] SChain (TopCat.toSSet.obj Y) ℚ n :=
  Finsupp.lmapDomain ℚ ℚ (pushSimplex f n)

@[simp] lemma pushChain_single {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) (r : ℚ) :
    pushChain f n (Finsupp.single σ r)
      = Finsupp.single (pushSimplex f n σ) r := by
  rw [pushChain, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

lemma pushChain_id {X : TopCat.{0}} (n : ℕ) (c : SChain (TopCat.toSSet.obj X) ℚ n) :
    pushChain (𝟙 X) n c = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single σ r =>
      rw [pushChain_single]
      have h : pushSimplex (𝟙 X) n σ = σ := by
        apply (TopCat.toSSetObjEquivT X (op ⦋n⦌)).injective
        rw [pushSimplex_apply]
        rfl
      rw [h]

lemma pushChain_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (c : SChain (TopCat.toSSet.obj X) ℚ n) :
    pushChain (f ≫ g) n c = pushChain g n (pushChain f n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single σ r => rw [pushChain_single, pushChain_single, pushChain_single, pushSimplex_comp]

/-- **Pushforward is compatible with the boundary**: it is a chain map. -/
theorem pushChain_sbdry {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (c : SChain (TopCat.toSSet.obj X) ℚ (n+1)) :
    pushChain f n (sbdry (TopCat.toSSet.obj X) ℚ n c)
      = sbdry (TopCat.toSSet.obj Y) ℚ n (pushChain f (n+1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single σ r =>
      rw [pushChain_single, sbdry_single, sbdry_single, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pushChain_single, pushSimplex_δ]

/-! ## From chains of pieces of `Δ^N` to singular chains of `Δ^N` -/

/-- The standard topological `n`-simplex, as a topological space. -/
abbrev stdTopSimplex (n : ℕ) : TopCat.{0} := TopCat.of (TSimplex n)

/-- The `i`-th face inclusion of the standard simplices, as a continuous map. -/
def faceInclHom {n : ℕ} (i : Fin (n+2)) : stdTopSimplex n ⟶ stdTopSimplex (n+1) :=
  TopCat.ofHom (faceInclC i)

/-- The singular simplex of `Δ^N` with vertices the subdivision piece `q`. -/
def simplexOfPiece {N m : ℕ} (q : Piece N m) :
    (TopCat.toSSet.obj (stdTopSimplex N)).obj (op ⦋m⦌) :=
  (TopCat.toSSetObjEquivT (stdTopSimplex N) (op ⦋m⦌)).symm (affineSimplex q)

@[simp] lemma toSSetObjEquivT_simplexOfPiece {N m : ℕ} (q : Piece N m) :
    TopCat.toSSetObjEquivT (stdTopSimplex N) (op ⦋m⦌) (simplexOfPiece q) = affineSimplex q := by
  rw [simplexOfPiece, Equiv.apply_symm_apply]

/-- The vertex list of a pushed piece is the composition; in particular the simplex of a piece
pushed along the `i`-th face inclusion is the composite of the simplex with the inclusion. -/
lemma affineSimplex_pushPiece_faceIncl {n m : ℕ} (i : Fin (n+2)) (q : Piece n m) :
    affineSimplex (pushPiece (faceIncl i) q) = (faceInclC i).comp (affineSimplex q) := by
  ext t r
  simp only [affineSimplex_apply, affineSimplexFun, ContinuousMap.comp_apply, pushPiece,
    Function.comp_apply, faceInclC_apply, faceIncl_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ((Fin.succAbove i a : Fin (n+2)) = r)
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [if_pos h]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg h, mul_zero]

@[simp] lemma pushSimplex_faceIncl {N m : ℕ} (i : Fin (N+2)) (q : Piece N m) :
    pushSimplex (faceInclHom i) m (simplexOfPiece q)
      = simplexOfPiece (pushPiece (faceIncl i) q) := by
  apply (TopCat.toSSetObjEquivT (stdTopSimplex (N+1)) (op ⦋m⦌)).injective
  rw [pushSimplex_apply, toSSetObjEquivT_simplexOfPiece, toSSetObjEquivT_simplexOfPiece,
    show TopCat.Hom.equivContinuousMap (stdTopSimplex N) (stdTopSimplex (N+1)) (faceInclHom i)
      = faceInclC i from rfl]
  exact (affineSimplex_pushPiece_faceIncl i q).symm

/-- The `i`-th face of the simplex of a piece is the simplex of the `i`-th face of the piece. -/
lemma simplexOfPiece_face {N m : ℕ} (q : Piece N (m+1)) (i : Fin (m+2)) :
    (TopCat.toSSet.obj (stdTopSimplex N)).δ i (simplexOfPiece q)
      = simplexOfPiece (facePiece q i) := by
  apply (TopCat.toSSetObjEquivT (stdTopSimplex N) (op ⦋m⦌)).injective
  ext t r
  rw [TopCat.toSSetObjEquivT_δ_apply, toSSetObjEquivT_simplexOfPiece,
    toSSetObjEquivT_simplexOfPiece]
  have h1 : ((affineSimplex q) (faceIncl i t) : TSimplex N)
      = (affineSimplex (facePiece q i)) t := by
    simpa [ContinuousMap.comp_apply, faceInclC_apply, facePiece] using
      congrArg (fun φ : C(TSimplex m, TSimplex N) => φ t) (affineSimplex_comp_faceIncl q i)
  exact congrArg (fun y : TSimplex N => (y : Fin (N+1) → ℝ) r) h1

/-- The linear map sending a chain of pieces of `Δ^N` to the corresponding singular chain. -/
def toSingChainLM (N m : ℕ) :
    (Piece N m →₀ ℚ) →ₗ[ℚ] SChain (TopCat.toSSet.obj (stdTopSimplex N)) ℚ m :=
  Finsupp.linearCombination ℚ fun q : Piece N m => Finsupp.single (simplexOfPiece q) (1 : ℚ)

/-- The singular chain of `Δ^N` associated with a chain of pieces. -/
abbrev toSingChain {N m : ℕ} (z : Piece N m →₀ ℚ) := toSingChainLM N m z

@[simp] lemma toSingChain_single {N m : ℕ} (q : Piece N m) (r : ℚ) :
    toSingChain (Finsupp.single q r) = r • Finsupp.single (simplexOfPiece q) 1 := by
  rw [toSingChain, toSingChainLM, Finsupp.linearCombination_single]

lemma toSingChain_add {N m : ℕ} (x y : Piece N m →₀ ℚ) :
    toSingChain (x + y) = toSingChain x + toSingChain y := by
  rw [toSingChain, toSingChain, toSingChain, map_add]

lemma toSingChain_sum {N : ℕ} {m : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Piece N m →₀ ℚ) :
    toSingChain (∑ i ∈ s, f i) = ∑ i ∈ s, toSingChain (f i) := by
  simp only [toSingChain, toSingChainLM, map_sum]

/-- Pushing a chain of pieces along a face inclusion and converting to singular chains is the
same as pushing the singular chain along that face inclusion. -/
lemma toSingChain_smul {N m : ℕ} (c : ℚ) (z : Piece N m →₀ ℚ) :
    toSingChain (c • z) = c • toSingChain z := by
  simp only [toSingChain, toSingChainLM, map_smul]

lemma toSingChain_sub {N m : ℕ} (x y : Piece N m →₀ ℚ) :
    toSingChain (x - y) = toSingChain x - toSingChain y := by
  simp only [toSingChain, toSingChainLM, map_sub]

lemma toSingChain_sum_smul {N m : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℚ)
    (f : ι → Piece N m →₀ ℚ) :
    toSingChain (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • toSingChain (f i) := by
  rw [toSingChain_sum]
  exact Finset.sum_congr rfl fun i _ => toSingChain_smul (c i) (f i)

/-- The affine map of a pushed piece is the composite of the affine maps. -/
lemma affineSimplex_pushPiece_affine {N k m : ℕ} (q : Piece N k) (z : Piece k m) :
    affineSimplex (pushPiece (fun x => affineSimplex q x) z)
      = (affineSimplex q).comp (affineSimplex z) := by
  ext t r
  simp only [affineSimplex_apply, affineSimplexFun, ContinuousMap.comp_apply, pushPiece,
    Function.comp_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The general form of the pushforward of chains of pieces along the map of a piece. -/
lemma toSingChain_pushPieces_affine {N k m : ℕ} (q : Piece N k) (z : Piece k m →₀ ℚ) :
    toSingChainLM N m (pushPieces (fun x => affineSimplex q x) m z)
      = pushChain (TopCat.ofHom (affineSimplex q)) m (toSingChainLM k m z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single z' r =>
      rw [pushPieces_single, toSingChainLM, Finsupp.linearCombination_single, toSingChainLM,
        Finsupp.linearCombination_single, map_smul, pushChain_single]
      have h : simplexOfPiece (pushPiece (fun x => affineSimplex q x) z')
          = pushSimplex (TopCat.ofHom (affineSimplex q)) m (simplexOfPiece z') := by
        apply (TopCat.toSSetObjEquivT (stdTopSimplex N) (op ⦋m⦌)).injective
        rw [pushSimplex_apply, toSSetObjEquivT_simplexOfPiece, toSSetObjEquivT_simplexOfPiece,
          show TopCat.Hom.equivContinuousMap (stdTopSimplex k) (stdTopSimplex N)
              (TopCat.ofHom (affineSimplex q)) = affineSimplex q from TopCat.hom_ofHom _]
        exact affineSimplex_pushPiece_affine q z'
      rw [h]

lemma toSingChain_pushPieces {k m : ℕ} (i : Fin (k+2)) (z : Piece k m →₀ ℚ) :
    toSingChainLM (k+1) m (pushPieces (faceIncl i) m z)
      = pushChain (faceInclHom i) m (toSingChainLM k m z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single q r =>
      rw [pushPieces_single, toSingChainLM, Finsupp.linearCombination_single, toSingChainLM,
        Finsupp.linearCombination_single, map_smul, pushChain_single, pushSimplex_faceIncl]

/-- Conversion of piece chains to singular chains commutes with the boundary. -/
theorem toSingChain_pieceBdry {N m : ℕ} (z : Piece N (m+1) →₀ ℚ) :
    toSingChain (pieceBdry m z)
      = sbdry (TopCat.toSSet.obj (stdTopSimplex N)) ℚ m (toSingChain z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single q r =>
      rw [pieceBdry_single, toSingChain_single]
      simp only [toSingChain, toSingChainLM]
      rw [map_sum, Finsupp.smul_single, sbdry_single]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.linearCombination_single, Finsupp.smul_single]
      rw [← simplexOfPiece_face q i]
      congr 1
      rw [zsmul_eq_mul]
      push_cast
      ring


/-! ## The continuous map underlying a simplex; pushforward along it -/

/-- The continuous map `Δ^n → X` underlying a simplex `σ` of the singular complex of `X`. -/
def homOfSimplex {X : TopCat.{0}} {n : ℕ} (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    stdTopSimplex n ⟶ X :=
  TopCat.ofHom (TopCat.toSSetObjEquivT X (op ⦋n⦌) σ)

@[simp] lemma homOfSimplex_apply {X : TopCat.{0}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    TopCat.Hom.equivContinuousMap (stdTopSimplex n) X (homOfSimplex σ)
      = TopCat.toSSetObjEquivT X (op ⦋n⦌) σ := TopCat.hom_ofHom _

@[simp] lemma faceInclHom_apply {n : ℕ} (i : Fin (n+2)) :
    TopCat.Hom.equivContinuousMap (stdTopSimplex n) (stdTopSimplex (n+1)) (faceInclHom i)
      = faceInclC i := rfl

/-- The underlying continuous map of the `i`-th face of a simplex. -/
lemma toSSetObjEquivT_delta {X : TopCat.{0}} {n : ℕ} (i : Fin (n+2))
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n+1⦌)) :
    TopCat.toSSetObjEquivT X (op ⦋n⦌) ((TopCat.toSSet.obj X).δ i σ)
      = (TopCat.toSSetObjEquivT X (op ⦋n+1⦌) σ).comp (faceInclC i) := by
  ext z
  rw [TopCat.toSSetObjEquivT_δ_apply, ContinuousMap.comp_apply, faceInclC_apply]
  rfl

/-- The morphism of the `i`-th face of a simplex is the composite of the simplex with the `i`-th
face inclusion. -/
lemma homOfSimplex_delta {X : TopCat.{0}} {n : ℕ} (i : Fin (n+2))
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n+1⦌)) :
    homOfSimplex ((TopCat.toSSet.obj X).δ i σ) = faceInclHom i ≫ homOfSimplex σ := by
  apply (TopCat.Hom.equivContinuousMap (stdTopSimplex n) X).injective
  rw [homOfSimplex_apply,
    show TopCat.Hom.equivContinuousMap (stdTopSimplex n) X (faceInclHom i ≫ homOfSimplex σ)
      = (TopCat.Hom.equivContinuousMap (stdTopSimplex (n+1)) X (homOfSimplex σ)).comp
          (TopCat.Hom.equivContinuousMap (stdTopSimplex n) (stdTopSimplex (n+1)) (faceInclHom i))
      from rfl,
    homOfSimplex_apply, faceInclHom_apply, toSSetObjEquivT_delta]

lemma pushChain_homOfSimplex_delta {X : TopCat.{0}} {n : ℕ} (i : Fin (n+2))
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n+1⦌))
    (x : SChain (TopCat.toSSet.obj (stdTopSimplex n)) ℚ n) :
    pushChain (homOfSimplex ((TopCat.toSSet.obj X).δ i σ)) n x
      = pushChain (homOfSimplex σ) n (pushChain (faceInclHom i) n x) := by
  rw [homOfSimplex_delta, pushChain_comp]

/-- Pushing the simplex of the identity piece along the map of a simplex gives that simplex. -/
@[simp] lemma pushSimplex_homOfSimplex_idPiece {X : TopCat.{0}} {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    pushSimplex (homOfSimplex σ) n (simplexOfPiece (idPiece n)) = σ := by
  apply (TopCat.toSSetObjEquivT X (op ⦋n⦌)).injective
  rw [pushSimplex_apply, toSSetObjEquivT_simplexOfPiece, homOfSimplex_apply,
    affineSimplex_idPiece]
  simp

end

end Submission.Cohomology
