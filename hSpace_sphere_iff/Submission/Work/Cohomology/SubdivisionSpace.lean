/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The barycentric subdivision and the prism homotopy on the singular chains of a space

This file combines `Submission.Work.Cohomology.SubdivisionSing` (the transport of the piece-level
subdivision to singular chains of the standard simplices) with the two identities proved for the
piece-level chains (`pieceBdry_SdPieces`, `pieceBdry_TPieces`) to obtain

* the universal chains `sdUniv n`, `tUniv n`, `uUniv n`, `idUniv n` and the identities
  `sbdry_sdUniv`, `sbdry_tUniv`, `uUniv_succ`;
* the operators `sdFun X n` (subdivision) and `tFun X n` (the prism homotopy) on the singular
  chains of an arbitrary topological space `X`, and their chain-level identities
  `sdFun_chainMap` and `tFun_homotopy`.
-/
import Mathlib
import Submission.Work.Cohomology.SubdivisionSing
import Submission.Work.Cohomology.pieceBdry_SdPieces
import Submission.Work.Cohomology.pieceBdry_TPieces

open CategoryTheory Simplicial Opposite

namespace Submission.Cohomology

noncomputable section

/-- The universal subdivision chain: the barycentric subdivision of `Δⁿ`, as a singular chain. -/
abbrev sdUniv (n : ℕ) : SChain (TopCat.toSSet.obj (stdTopSimplex n)) ℚ n :=
  toSingChain (SdPieces n)

/-- The universal homotopy chain: the prism over `Δⁿ`. -/
abbrev tUniv (n : ℕ) : SChain (TopCat.toSSet.obj (stdTopSimplex n)) ℚ (n+1) :=
  toSingChain (TPieces n)

/-- The universal chain `T(∂Δⁿ)` (zero for `n = 0`). -/
abbrev uUniv (n : ℕ) : SChain (TopCat.toSSet.obj (stdTopSimplex n)) ℚ n :=
  toSingChain (TPrevPieces n)

/-- The identity simplex of `Δⁿ`, as a singular chain in degree `n`. -/
abbrev idUniv (n : ℕ) : SChain (TopCat.toSSet.obj (stdTopSimplex n)) ℚ n :=
  toSingChain (Finsupp.single (idPiece n) 1)

/-- **The chain map property of the subdivision on the universal simplex.** -/
theorem sbdry_sdUniv (n : ℕ) :
    sbdry (TopCat.toSSet.obj (stdTopSimplex (n+1))) ℚ n (sdUniv (n+1))
      = ∑ i : Fin (n+2), (-1 : ℚ) ^ (i : ℕ) • pushChain (faceInclHom i) n (sdUniv n) := by
  have hsum := toSingChain_sum_smul (N := n+1) (m := n) (ι := Fin (n+2)) Finset.univ
    (fun i => (-1 : ℚ) ^ (i : ℕ)) (fun i => pushPieces (faceIncl i) n (SdPieces n))
  simp only [sdUniv]
  rw [← toSingChain_pieceBdry, Work.Cohomology.pieceBdry_SdPieces, hsum]
  simp only [toSingChain]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact toSingChain_pushPieces i (SdPieces n)

/-- **The chain homotopy identity on the universal simplex**: `∂T = id - Sd - T∂` for `Δⁿ`. -/
theorem sbdry_tUniv (n : ℕ) :
    sbdry (TopCat.toSSet.obj (stdTopSimplex n)) ℚ n (tUniv n)
      = idUniv n - sdUniv n - uUniv n := by
  simp only [tUniv, sdUniv, uUniv, idUniv]
  rw [← toSingChain_pieceBdry, Work.Cohomology.pieceBdry_TPieces]
  simp only [toSingChain, toSingChainLM, map_sub]

/-- The universal chain `T(∂Δⁿ)` is the boundary contribution at the previous level. -/
theorem uUniv_succ (n : ℕ) :
    uUniv (n+1)
      = ∑ i : Fin (n+2), (-1 : ℚ) ^ (i : ℕ) • pushChain (faceInclHom i) (n+1) (tUniv n) := by
  simp only [uUniv, tUniv,
    show TPrevPieces (n+1) = ∑ i : Fin (n+2), (-1 : ℚ) ^ (i : ℕ) •
        pushPieces (faceIncl i) (n+1) (TPieces n) from rfl]
  have hsum := toSingChain_sum_smul (N := n+1) (m := n+1) (ι := Fin (n+2)) Finset.univ
    (fun i => (-1 : ℚ) ^ (i : ℕ)) (fun i => pushPieces (faceIncl i) (n+1) (TPieces n))
  simp only [toSingChain] at hsum ⊢
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact toSingChain_pushPieces i (TPieces n)

/-! ## The subdivision and homotopy operators on the singular chains of a space -/

/-- The barycentric subdivision operator on the singular chains of `X`: a simplex `σ` is replaced
by the subdivision of `Δⁿ` pushed forward along the map of `σ`. -/
def sdFun (X : TopCat.{0}) (n : ℕ) :
    SChain (TopCat.toSSet.obj X) ℚ n →ₗ[ℚ] SChain (TopCat.toSSet.obj X) ℚ n :=
  Finsupp.linearCombination ℚ fun σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌) =>
    pushChain (homOfSimplex σ) n (sdUniv n)

/-- The prism homotopy operator on the singular chains of `X`, in degree `n`: it raises the
dimension by one. -/
def tFun (X : TopCat.{0}) (n : ℕ) :
    SChain (TopCat.toSSet.obj X) ℚ n →ₗ[ℚ] SChain (TopCat.toSSet.obj X) ℚ (n+1) :=
  Finsupp.linearCombination ℚ fun σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌) =>
    pushChain (homOfSimplex σ) (n+1) (tUniv n)

/-- The `T(∂Δⁿ)` operator on the singular chains of `X`: the boundary contribution to the
homotopy in degree `n`. -/
def uFun (X : TopCat.{0}) (n : ℕ) :
    SChain (TopCat.toSSet.obj X) ℚ n →ₗ[ℚ] SChain (TopCat.toSSet.obj X) ℚ n :=
  Finsupp.linearCombination ℚ fun σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌) =>
    pushChain (homOfSimplex σ) n (uUniv n)

@[simp] lemma sdFun_single (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) (r : ℚ) :
    sdFun X n (Finsupp.single σ r) = r • pushChain (homOfSimplex σ) n (sdUniv n) := by
  rw [sdFun, Finsupp.linearCombination_single]

@[simp] lemma tFun_single (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) (r : ℚ) :
    tFun X n (Finsupp.single σ r) = r • pushChain (homOfSimplex σ) (n+1) (tUniv n) := by
  rw [tFun, Finsupp.linearCombination_single]

@[simp] lemma uFun_single (X : TopCat.{0}) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) (r : ℚ) :
    uFun X n (Finsupp.single σ r) = r • pushChain (homOfSimplex σ) n (uUniv n) := by
  rw [uFun, Finsupp.linearCombination_single]

end

end Submission.Cohomology
