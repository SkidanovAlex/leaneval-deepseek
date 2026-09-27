/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The chain-level barycentric subdivision of the standard simplex

`Submission.Work.Cohomology.Subdivision` encodes a subdivision piece of `Δⁿ` by its list of
vertices (`Piece n m = Fin (m+1) → TSimplex n`) and converts it into a singular simplex by
`affineSimplex`.  This file carries out the *chain-level* constructions on such pieces:

* `pieceBdry` — the boundary `∂` of a chain of pieces, computed by the face operators
  `facePiece · i` (i.e. `q ↦ q ∘ Fin.succAbove i`);
* `pushPieces` — push a chain of pieces forward along a map of simplices (`f ∘ ·`);
* `conePieces` — coning with an apex (`concPiece b ·`), i.e. prepending a vertex;
* `SdPieces` — the barycentric subdivision chain of `Δⁿ`, defined by the classical recursion
  `Sd(Δ^{n+1}) = cone_{barycentre}(Sd(∂Δ^{n+1}))`;
* `TPieces` — the "prism" chain realising the chain homotopy from `Sd` to the identity,
  `T(Δ^{n+1}) = cone_{barycentre}(Δ^{n+1} - Sd(Δ^{n+1}) - T(∂Δ^{n+1}))`.

The two identities these satisfy are `pieceBdry_SdPieces` (the chain map property `∂ ∘ Sd = Sd ∘ ∂`
on the universal simplex) and `pieceBdry_TPieces` (`∂ ∘ T + T ∘ ∂ = id - Sd` on the universal
simplex).  Everything is then transported to singular chains of an arbitrary space in
`Submission.Work.Cohomology.SubdivisionSing`.
-/
import Mathlib
import Submission.Work.Cohomology.Subdivision
import Submission.Work.Cohomology.Chains

open CategoryTheory Simplicial Opposite

namespace Submission.Cohomology

noncomputable section

/-- The piece of dimension `0` consisting of the `i`-th vertex of `Δⁿ`. -/
def vertPiece {n : ℕ} (i : Fin (n+1)) : Piece n 0 := fun _ => vert i

/-- The identity piece of `Δⁿ`: the simplex whose vertices are all the vertices of `Δⁿ`. -/
def idPiece (n : ℕ) : Piece n n := fun i => vert i

/-- The barycentre of `Δⁿ`, used as the cone vertex of the barycentric subdivision. -/
def bary (n : ℕ) : TSimplex n := stdSimplex.barycenter

/-- Push the vertices of a piece forward along a map of standard simplices. -/
def pushPiece {n n' : ℕ} (f : TSimplex n → TSimplex n') {m : ℕ} (q : Piece n m) : Piece n' m :=
  f ∘ q

/-- Push a chain of pieces forward along a map of standard simplices. -/
def pushPieces {n n' : ℕ} (f : TSimplex n → TSimplex n') (m : ℕ) :
    (Piece n m →₀ ℚ) →ₗ[ℚ] (Piece n' m →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ fun q : Piece n m => pushPiece f q

/-- The cone over a chain of pieces with apex `b`: prepend `b` to every vertex list. -/
def conePieces {n : ℕ} (b : TSimplex n) (m : ℕ) :
    (Piece n m →₀ ℚ) →ₗ[ℚ] (Piece n (m+1) →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ fun q : Piece n m => conePiece b q

/-- The boundary of a chain of pieces: the alternating sum of the face operators. -/
def pieceBdry {n : ℕ} (m : ℕ) : (Piece n (m+1) →₀ ℚ) →ₗ[ℚ] (Piece n m →₀ ℚ) :=
  ∑ i : Fin (m+2), (-1 : ℚ) ^ (i : ℕ) •
    Finsupp.lmapDomain ℚ ℚ fun q : Piece n (m+1) => facePiece q i

@[simp] lemma pushPieces_single {n n' m : ℕ} (f : TSimplex n → TSimplex n')
    (q : Piece n m) (r : ℚ) :
    pushPieces f m (Finsupp.single q r) = Finsupp.single (pushPiece f q) r := by
  rw [pushPieces, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

@[simp] lemma conePieces_single {n m : ℕ} (b : TSimplex n) (q : Piece n m) (r : ℚ) :
    conePieces b m (Finsupp.single q r) = Finsupp.single (conePiece b q) r := by
  rw [conePieces, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

lemma pushPieces_add {n n' m : ℕ} (f : TSimplex n → TSimplex n')
    (x y : Piece n m →₀ ℚ) :
    pushPieces f m (x + y) = pushPieces f m x + pushPieces f m y := map_add _ _ _

@[simp] lemma pushPiece_id {n m : ℕ} (q : Piece n m) : pushPiece id q = q := rfl

lemma pushPieces_comp {n₁ n₂ n₃ : ℕ} (f : TSimplex n₂ → TSimplex n₃)
    (g : TSimplex n₁ → TSimplex n₂) (m : ℕ) (x : Piece n₁ m →₀ ℚ) :
    pushPieces f m (pushPieces g m x) = pushPieces (f ∘ g) m x := by
  rw [pushPieces, pushPieces, pushPieces, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply,
    Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  rfl

lemma pieceBdry_single {n m : ℕ} (q : Piece n (m+1)) (r : ℚ) :
    pieceBdry m (Finsupp.single q r)
      = ∑ i : Fin (m+2), Finsupp.single (facePiece q i) (((-1 : ℚ) ^ (i : ℕ)) * r) := by
  rw [pieceBdry, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    Finsupp.smul_single]
  rfl

/-- **The cone identity**: `∂(cone_b θ) = θ - cone_b(∂θ)` for chains of pieces. -/
lemma pieceBdry_conePieces {n : ℕ} (b : TSimplex n) (m : ℕ) (θ : Piece n (m+1) →₀ ℚ) :
    pieceBdry (m+1) (conePieces b (m+1) θ) = θ - conePieces b m (pieceBdry m θ) := by
  induction θ using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]; abel
  | single q r =>
      rw [conePieces_single, pieceBdry_single (conePiece b q) r, pieceBdry_single q r, map_sum]
      simp only [conePieces_single]
      conv_lhs => rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, facePiece_conePiece_zero]
      have hsum : (∑ j : Fin (m+2), Finsupp.single (facePiece (conePiece b q) j.succ)
            (((-1 : ℚ) ^ ((j.succ : Fin (m+3)) : ℕ)) * r))
          = -(∑ j : Fin (m+2), Finsupp.single (conePiece b (facePiece q j))
            (((-1 : ℚ) ^ ((j : Fin (m+2)) : ℕ)) * r)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finsupp.single_neg, facePiece_conePiece_succ, Fin.val_succ, pow_succ]
        congr 1
        ring
      rw [hsum]
      abel


/-- Pushforward commutes with the boundary of chains of pieces. -/
lemma pieceBdry_pushPieces {n n' m : ℕ} (f : TSimplex n → TSimplex n')
    (z : Piece n (m+1) →₀ ℚ) :
    pieceBdry m (pushPieces f (m+1) z) = pushPieces f m (pieceBdry m z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single q r =>
      rw [pushPieces_single, pieceBdry_single (pushPiece f q) r, pieceBdry_single q r, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pushPieces_single]
      rfl

/-- The `i`-th vertex of the affine simplex with vertices `q` is `q i`. -/
lemma affineSimplex_vert {n m : ℕ} (q : Fin (m+1) → TSimplex n) (i : Fin (m+1)) :
    affineSimplex q (vert i) = q i := by
  ext j
  rw [affineSimplex_apply, affineSimplexFun, Finset.sum_eq_single i]
  · rw [vert_apply]; simp
  · intro k _ hk; rw [vert_apply, if_neg (Ne.symm hk), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The affine simplex whose vertices are all the vertices of `Δⁿ` is the identity. -/
lemma affineSimplex_idPiece (m : ℕ) :
    affineSimplex (idPiece m) = ContinuousMap.id (TSimplex m) := by
  ext x j
  rw [affineSimplex_apply, affineSimplexFun]
  simp only [ContinuousMap.id_apply, idPiece, vert_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk; rw [if_neg hk]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Pushing the identity piece along the affine simplex with vertices `q` gives `q` back. -/
lemma pushPiece_affineSimplex_idPiece {N k : ℕ} (q : Piece N k) :
    pushPiece (fun x => affineSimplex q x) (idPiece k) = q := by
  funext i
  exact affineSimplex_vert q i

/-- Pushing a chain of pieces along `faceIncl i` and then along the affine simplex with
vertices `q` is pushing along the affine simplex with vertices the `i`-th face of `q`. -/
lemma pushPieces_affineSimplex_faceIncl {N k m : ℕ} (q : Piece N (k+1)) (i : Fin (k+2))
    (z : Piece k m →₀ ℚ) :
    pushPieces (fun x => affineSimplex q x) m (pushPieces (faceIncl i) m z)
      = pushPieces (fun x => affineSimplex (facePiece q i) x) m z := by
  rw [pushPieces_comp]
  have h : ((fun x => affineSimplex q x) ∘ faceIncl i)
      = fun x => affineSimplex (facePiece q i) x := by
    funext x
    have h1 := congrArg (fun φ : C(TSimplex k, TSimplex N) => φ x)
      (affineSimplex_comp_faceIncl q i)
    simpa [facePiece, ContinuousMap.comp_apply, faceInclC_apply, Function.comp_apply] using h1
  rw [h]

/-- **The barycentric subdivision chain of `Δⁿ`**: `Sd(Δⁿ)`, as a chain of pieces. -/
def SdPieces (n : ℕ) : (Piece n n →₀ ℚ) :=
  match n with
  | 0 => Finsupp.single (idPiece 0) 1
  | k+1 => ∑ i : Fin (k+2), (-1 : ℚ) ^ (i : ℕ) •
      conePieces (bary (k+1)) k (pushPieces (faceIncl i) k (SdPieces k))

/-- **The prism chain realising the chain homotopy from `Sd` to the identity**: `T(Δⁿ)`, as a
chain of pieces of `Δⁿ` of dimension `n+1`.  It is defined by
`T(Δ^{n+1}) = cone_{barycentre}(Δ^{n+1} - Sd(Δ^{n+1}) - T(∂Δ^{n+1}))`. -/
def TPieces (n : ℕ) : (Piece n (n+1) →₀ ℚ) :=
  match n with
  | 0 => 0
  | k+1 => conePieces (bary (k+1)) (k+1)
      (Finsupp.single (idPiece (k+1)) 1 - SdPieces (k+1) -
        ∑ i : Fin (k+2), (-1 : ℚ) ^ (i : ℕ) •
          pushPieces (faceIncl i) (k+1) (TPieces k))

/-- The chain `T(∂Δⁿ)` (zero for `n = 0`): the contribution of the boundary of the universal
simplex to the homotopy chain.  `T_{n-1}(∂Δⁿ) = ∑ᵢ (-1)ⁱ (∂ᵢ)_♯ T(Δⁿ⁻¹)`. -/
def TPrevPieces (n : ℕ) : (Piece n n →₀ ℚ) :=
  match n with
  | 0 => 0
  | k+1 => ∑ i : Fin (k+2), (-1 : ℚ) ^ (i : ℕ) •
      pushPieces (faceIncl i) (k+1) (TPieces k)


/-- One step of the barycentric subdivision applied to a single piece `q`: the subdivision of the
simplex with vertices `q`, transported into the ambient simplex by the affine map of `q`. -/
def subdividePiece {N m : ℕ} (q : Piece N m) : (Piece N m →₀ ℚ) :=
  pushPieces (fun x => affineSimplex q x) m (SdPieces m)

/-- The `N`-fold iterated barycentric subdivision of `Δⁿ`, as a chain of pieces of dimension `n`. -/
def SdPiecesPow (N : ℕ) : (n : ℕ) → (Piece n n →₀ ℚ) :=
  match N with
  | 0 => fun n => Finsupp.single (idPiece n) 1
  | K+1 => fun n => (SdPiecesPow K n).sum fun q r => r • subdividePiece q

@[simp] lemma SdPiecesPow_zero (n : ℕ) : SdPiecesPow 0 n = Finsupp.single (idPiece n) 1 := rfl

lemma SdPiecesPow_succ (N n : ℕ) :
    SdPiecesPow (N+1) n
      = (SdPiecesPow N n).sum (fun q r => r • subdividePiece q) := rfl

end

end Submission.Cohomology
