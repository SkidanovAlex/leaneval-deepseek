/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The prism chain `T` satisfies `∂ ∘ T + T ∘ ∂ = id - Sd` on the universal simplex

This file proves `Work.Cohomology.pieceBdry_TPieces`:
`∂ (T(Δⁿ)) = Δⁿ - Sd(Δⁿ) - T(∂ Δⁿ)`, the chain-level statement that the "prism" chain
`Submission.Cohomology.TPieces` is a chain homotopy from the barycentric subdivision
`Submission.Cohomology.SdPieces` to the identity.

The whole proof rests on the fact that the alternating sum of the coface inclusions
`Δᴺ → Δᴺ⁺¹` squares to zero (`faceOp_faceOp`), which is the simplicial identity `∂∂ = 0`
for the standard cosimplicial object; this is also what makes the subdivision chain a chain map
(`pieceBdry_SdPieces'`).  Both are proved here from the `Fin.succAbove` identity
`Fin.succAbove_succAbove_succAbove_predAbove` and the swapping involution of the index set.
-/
import Mathlib
import Submission.Work.Cohomology.SubdivisionChain

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

noncomputable section

open Submission.Cohomology

namespace TPAux

/-- The alternating sum of the face inclusions `Δᴺ → Δᴺ⁺¹`, acting on chains of `m`-pieces. -/
def faceOp (N m : ℕ) : (Piece N m →₀ ℚ) →ₗ[ℚ] (Piece (N+1) m →₀ ℚ) :=
  ∑ i : Fin (N+2), (-1:ℚ)^(i:ℕ) • pushPieces (faceIncl i) m

lemma faceOp_apply (N m : ℕ) (v : Piece N m →₀ ℚ) :
    faceOp N m v = ∑ i : Fin (N+2), (-1:ℚ)^(i:ℕ) • pushPieces (faceIncl i) m v := by
  rw [faceOp, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]

/-- The `i`-th face inclusion composed with the `j`-th face inclusion is the
`(i.succAbove j)`-th composed with the `(j.predAbove i)`-th (the simplicial identity
`δᵢδⱼ = δ_{j}δ_{i-1}`, in the `Fin.succAbove` presentation). -/
lemma faceIncl_comp_faceIncl {m : ℕ} (a : Fin (m+3)) (b : Fin (m+2)) :
    (faceIncl a) ∘ (faceIncl b)
      = (faceIncl (a.succAbove b)) ∘ (faceIncl (b.predAbove a)) := by
  funext x
  show faceIncl a (faceIncl b x) = faceIncl (a.succAbove b) (faceIncl (b.predAbove a) x)
  simp only [faceIncl]
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  congr 1
  funext k
  exact (Fin.succAbove_succAbove_succAbove_predAbove a b k).symm

/-- The sign in the swapping involution of the pairs of face indices. -/
lemma sign_swap {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    (-1:ℚ)^((i.succAbove j : ℕ) + (j.predAbove i : ℕ)) = -(-1:ℚ)^((i:ℕ)+(j:ℕ)) := by
  rcases le_or_gt i (Fin.castSucc j) with h | h
  · rw [Fin.succAbove_of_le_castSucc i j h, Fin.predAbove_of_le_castSucc j i h, Fin.coe_castPred]
    simp only [Fin.val_succ]
    rw [show j.val + 1 + i.val = (i.val + j.val) + 1 by omega, pow_succ]
    ring
  · rw [Fin.succAbove_of_castSucc_lt i j h, Fin.predAbove_of_castSucc_lt j i h,
      Fin.val_pred i (Fin.ne_zero_of_lt h), Fin.val_castSucc]
    rw [show i.val + j.val = (j.val + (i.val - 1)) + 1 by omega, pow_succ]
    ring

/-- **`∂∂ = 0` for the simplicial face operators**: two consecutive alternating sums of face
inclusions cancel. -/
lemma faceOp_faceOp (N m : ℕ) (z : Piece N m →₀ ℚ) :
    faceOp (N+1) m (faceOp N m z) = 0 := by
  rw [faceOp, faceOp]
  have key : (∑ i : Fin (N+3), (-1:ℚ)^(i:ℕ) • pushPieces (faceIncl i) m)
      ((∑ j : Fin (N+2), (-1:ℚ)^(j:ℕ) • pushPieces (faceIncl j) m) z)
      = ∑ p : Fin (N+3) × Fin (N+2),
          (-1:ℚ)^((p.1:ℕ)+(p.2:ℕ)) •
            (pushPieces (faceIncl p.1) m (pushPieces (faceIncl p.2) m z)) := by
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_sum, map_smul,
      smul_smul, ← pow_add]
    rw [← Finset.sum_product', Finset.univ_product_univ]
    apply Finset.sum_congr rfl
    intro x _
    rw [Nat.add_comm (x.2 : ℕ) (x.1 : ℕ)]
  rw [key]
  refine Finset.sum_ninvolution (s := Finset.univ)
    (f := fun p : Fin (N+3) × Fin (N+2) =>
      (-1:ℚ)^((p.1:ℕ)+(p.2:ℕ)) •
        (pushPieces (faceIncl p.1) m (pushPieces (faceIncl p.2) m z)))
    (fun p => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨i,j⟩
    rw [pushPieces_comp, pushPieces_comp, ← faceIncl_comp_faceIncl i j]
    rw [sign_swap i j, neg_smul, add_neg_cancel]
  · rintro ⟨i,j⟩ _ h
    exact absurd (congrArg Prod.fst h) (Fin.succAbove_ne i j)
  · intro p; exact Finset.mem_univ _
  · intro p
    obtain ⟨i,j⟩ := p
    simp only [Prod.mk.injEq]
    exact ⟨Fin.succAbove_succAbove_predAbove i j, Fin.predAbove_predAbove_succAbove i j⟩

/-- `faceOp` commutes with the piece boundary. -/
lemma pieceBdry_faceOp (k m : ℕ) (v : Piece k (m+1) →₀ ℚ) :
    pieceBdry m (faceOp k (m+1) v) = faceOp k m (pieceBdry m v) := by
  rw [faceOp_apply, map_sum]
  simp only [map_smul, pieceBdry_pushPieces]
  rw [faceOp_apply]

lemma faceIncl_vert {n : ℕ} (i : Fin (n+2)) (j : Fin (n+1)) :
    faceIncl i (vert j) = vert (i.succAbove j) := by
  simp only [faceIncl, vert, stdSimplex.map_vertex]

lemma pushPiece_faceIncl_idPiece {k : ℕ} (i : Fin (k+2)) :
    pushPiece (faceIncl i) (idPiece k) = facePiece (idPiece (k+1)) i := by
  funext j
  show faceIncl i (idPiece k j) = idPiece (k+1) ((Fin.succAbove i) j)
  simp only [idPiece]
  exact faceIncl_vert i j

/-- The boundary of `Δ^{k+1}` is the simplicial action of `faceOp` on `Δ^k`. -/
lemma pieceBdry_single_idPiece (k : ℕ) :
    pieceBdry k (Finsupp.single (idPiece (k+1)) 1) = faceOp k k (Finsupp.single (idPiece k) 1) := by
  rw [pieceBdry_single, faceOp, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, pushPieces_single, Finsupp.smul_single, smul_eq_mul, mul_one]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pushPiece_faceIncl_idPiece]

lemma SdPieces_zero : SdPieces 0 = Finsupp.single (idPiece 0) 1 := rfl
lemma TPrevPieces_zero : TPrevPieces 0 = 0 := rfl
lemma TPieces_zero : TPieces 0 = 0 := rfl

lemma TPieces_succ (k : ℕ) : TPieces (k+1) = conePieces (bary (k+1)) (k+1)
    (Finsupp.single (idPiece (k+1)) 1 - SdPieces (k+1) - TPrevPieces (k+1)) := rfl

/-- The zero-dimensional piece with value `b`. -/
def constPiece {n : ℕ} (b : TSimplex n) : Piece n 0 := fun _ => b

lemma facePiece_conePiece_zero_dim {n : ℕ} (b : TSimplex n) (q : Piece n 0) :
    facePiece (conePiece b q) (0 : Fin 2) = q := by
  funext j
  show conePiece b q ((Fin.succAbove (0 : Fin 2)) j) = q j
  rw [Fin.succAbove_zero]
  exact conePiece_succ b q j

lemma facePiece_conePiece_one_dim {n : ℕ} (b : TSimplex n) (q : Piece n 0) :
    facePiece (conePiece b q) (1 : Fin 2) = constPiece b := by
  funext j
  obtain rfl : j = 0 := Fin.eq_zero j
  show conePiece b q ((Fin.succAbove (1 : Fin 2)) (0 : Fin 1)) = b
  rw [Fin.succAbove_of_castSucc_lt (1 : Fin 2) (0 : Fin 1) (by decide)]
  exact conePiece_zero b q

/-- The boundary of a cone over a **zero-dimensional** chain: the cone identity in the bottom
dimension, where `cone b (∂θ)` is not available. -/
lemma pieceBdry_zero_conePieces_single {n : ℕ} (b : TSimplex n) (q : Piece n 0) (r : ℚ) :
    pieceBdry 0 (conePieces b 0 (Finsupp.single q r))
      = Finsupp.single q r - Finsupp.single (constPiece b) r := by
  rw [conePieces_single, pieceBdry_single, Fin.sum_univ_two]
  rw [facePiece_conePiece_zero_dim, facePiece_conePiece_one_dim]
  simp [sub_eq_add_neg]

lemma TPrevPieces_succ (k : ℕ) :
    TPrevPieces (k+1) = faceOp k (k+1) (TPieces k) := by
  rw [faceOp, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  rfl

lemma SdPieces_succ (k : ℕ) :
    SdPieces (k+1) = conePieces (bary (k+1)) k (faceOp k k (SdPieces k)) := by
  rw [SdPieces, faceOp, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]

/-- The chain-map property of the subdivision in the bottom dimension. -/
lemma pieceBdry_SdPieces_zero :
    pieceBdry 0 (SdPieces (0+1)) = faceOp 0 0 (SdPieces 0) := by
  rw [SdPieces_succ 0, faceOp_apply, SdPieces_zero]
  simp only [pushPieces_single]
  rw [map_sum]
  simp only [map_smul]
  rw [map_sum]
  simp only [map_smul, pieceBdry_zero_conePieces_single]
  simp only [smul_sub]
  rw [Finset.sum_sub_distrib]
  have hC : (∑ x : Fin 2, (-1:ℚ)^(x:ℕ) • Finsupp.single (constPiece (bary (0+1))) (1:ℚ))
      = (0 : Piece (0+1) 0 →₀ ℚ) := by
    rw [Fin.sum_univ_two]
    simp
  rw [hC, sub_zero]

/-- The chain-map property of the subdivision, inductive step. -/
lemma pieceBdry_SdPieces_succ (k : ℕ)
    (ih : pieceBdry k (SdPieces (k+1)) = faceOp k k (SdPieces k)) :
    pieceBdry (k+1) (SdPieces ((k+1)+1)) = faceOp (k+1) (k+1) (SdPieces (k+1)) := by
  rw [SdPieces_succ (k+1), pieceBdry_conePieces (bary ((k+1)+1)) k]
  have hθ : pieceBdry k (faceOp (k+1) (k+1) (SdPieces (k+1))) = 0 := by
    rw [faceOp_apply, map_sum]
    simp only [map_smul, pieceBdry_pushPieces, ih]
    have h2 := faceOp_faceOp k k (SdPieces k)
    rw [faceOp, LinearMap.sum_apply] at h2
    simpa only [LinearMap.smul_apply] using h2
  rw [hθ, map_zero, sub_zero]

/-- **The chain-map property of the barycentric subdivision**: `∂ ∘ Sd = Sd ∘ ∂` on the
universal simplex. -/
lemma pieceBdry_SdPieces' (n : ℕ) :
    pieceBdry n (SdPieces (n+1)) = faceOp n n (SdPieces n) := by
  induction n with
  | zero => exact pieceBdry_SdPieces_zero
  | succ k ih => exact pieceBdry_SdPieces_succ k ih

/-- `T(∂Δⁿ)` is a cycle for the simplicial face operator, i.e. `∂∂ = 0`. -/
lemma faceOp_TPrevPieces (k : ℕ) : faceOp k k (TPrevPieces k) = 0 := by
  cases k with
  | zero => rw [TPrevPieces_zero]; simp
  | succ l => rw [TPrevPieces_succ l]; exact faceOp_faceOp l (l+1) (TPieces l)

/-- The inductive step of `pieceBdry_TPieces`. -/
lemma pieceBdry_TPieces_succ (k : ℕ)
    (ih : pieceBdry k (TPieces k) = Finsupp.single (idPiece k) 1 - SdPieces k - TPrevPieces k) :
    pieceBdry (k+1) (TPieces (k+1))
      = Finsupp.single (idPiece (k+1)) 1 - SdPieces (k+1) - TPrevPieces (k+1) := by
  rw [TPieces_succ k, pieceBdry_conePieces (bary (k+1)) k]
  have hX : pieceBdry k (Finsupp.single (idPiece (k+1)) 1 - SdPieces (k+1) - TPrevPieces (k+1))
      = 0 := by
    rw [map_sub, map_sub, pieceBdry_single_idPiece, pieceBdry_SdPieces' k, TPrevPieces_succ k,
      pieceBdry_faceOp k k (TPieces k), ih, map_sub, map_sub, faceOp_TPrevPieces k]
    abel
  rw [hX]; simp

end TPAux

open TPAux

theorem pieceBdry_TPieces (n : ℕ) :
    Submission.Cohomology.pieceBdry n (Submission.Cohomology.TPieces n)
      = Finsupp.single (Submission.Cohomology.idPiece n) 1 - Submission.Cohomology.SdPieces n
        - Submission.Cohomology.TPrevPieces n := by
  induction n with
  | zero =>
    rw [TPieces_zero, SdPieces_zero, TPrevPieces_zero]
    simp
  | succ k ih =>
    exact pieceBdry_TPieces_succ k ih

end

end Work.Cohomology
