/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Geometry of the standard simplex

Elementary geometry of the topological standard simplex `TSimplex n := stdSimplex ℝ (Fin (n+1))`,
used to build the barycentric subdivision of simplices and, through it, the small-simplex
(Mayer–Vietoris) theorem for singular cohomology:

* `faceIncl i` : the `i`-th face inclusion `Δⁿ → Δⁿ⁺¹`;
* `affineSimplex q` : the affine simplex with prescribed vertices `q : Fin (k+1) → Δⁿ`;
* the face formula `(affineSimplex q) ∘ faceIncl i = affineSimplex (q ∘ Fin.succAbove i)`,
  which is the source of all the chain-level identities of the subdivision
  (`∂ ∘ cone = id - cone ∘ ∂` and the chain-map property of the subdivision).
-/
import Mathlib

open CategoryTheory Simplicial Opposite

namespace Submission.Cohomology

noncomputable section

/-- The topological standard `n`-simplex. -/
abbrev TSimplex (n : ℕ) : Type := stdSimplex ℝ (Fin (n + 1))

/-- The `i`-th vertex of the standard simplex. -/
def vert {n : ℕ} (i : Fin (n+1)) : TSimplex n := stdSimplex.vertex i

@[simp] lemma vert_apply {n : ℕ} (i j : Fin (n+1)) :
    ((vert i : TSimplex n) : Fin (n+1) → ℝ) j = if i = j then 1 else 0 := by
  rw [vert, stdSimplex.vertex_coe]
  simp [Pi.single_apply, eq_comm]

/-- The `i`-th face inclusion `Δⁿ → Δⁿ⁺¹`. -/
def faceIncl {n : ℕ} (i : Fin (n+2)) (x : TSimplex n) : TSimplex (n+1) :=
  stdSimplex.map (Fin.succAbove i) x

@[simp] lemma faceIncl_coe {n : ℕ} (i : Fin (n+2)) (x : TSimplex n) :
    ((faceIncl i x : TSimplex (n+1)) : Fin (n+2) → ℝ)
      = FunOnFinite.linearMap ℝ ℝ (Fin.succAbove i) x := rfl

/-- The coordinate formula for the face inclusion: the coordinate `r` of `faceIncl i x` is the
sum of the coordinates of `x` over the preimage of `r` under `Fin.succAbove i`. -/
lemma faceIncl_apply {n : ℕ} (i : Fin (n+2)) (x : TSimplex n) (r : Fin (n+2)) :
    ((faceIncl i x : TSimplex (n+1)) : Fin (n+2) → ℝ) r
      = ∑ a : Fin (n+1), if (Fin.succAbove i a : Fin (n+2)) = r
          then (x : Fin (n+1) → ℝ) a else 0 := by
  rw [faceIncl_coe, FunOnFinite.linearMap_apply_apply, Finset.sum_filter]

lemma faceIncl_apply_succAbove {n : ℕ} (i : Fin (n+2)) (x : TSimplex n) (j : Fin (n+1)) :
    ((faceIncl i x : TSimplex (n+1)) : Fin (n+2) → ℝ) (i.succAbove j)
      = (x : Fin (n+1) → ℝ) j := by
  rw [faceIncl_apply, Finset.sum_eq_single j]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.succAbove_right_injective h)
  · intro h; exact absurd (Finset.mem_univ j) h

lemma faceIncl_apply_self {n : ℕ} (i : Fin (n+2)) (x : TSimplex n) :
    ((faceIncl i x : TSimplex (n+1)) : Fin (n+2) → ℝ) i = 0 := by
  rw [faceIncl_apply, Finset.sum_eq_zero]
  intro a _
  rw [if_neg]
  exact fun h => Fin.succAbove_ne i a h

lemma continuous_faceIncl {n : ℕ} (i : Fin (n+2)) : Continuous (faceIncl i) :=
  stdSimplex.continuous_map _

/-- The face inclusion as a continuous map. -/
def faceInclC {n : ℕ} (i : Fin (n+2)) : C(TSimplex n, TSimplex (n+1)) :=
  ⟨faceIncl i, continuous_faceIncl i⟩

@[simp] lemma faceInclC_apply {n : ℕ} (i : Fin (n+2)) (x : TSimplex n) :
    faceInclC i x = faceIncl i x := rfl

/-- The underlying function of the affine simplex with prescribed vertices. -/
def affineSimplexFun {n k : ℕ} (q : Fin (k+1) → TSimplex n) (t : TSimplex k) : Fin (n+1) → ℝ :=
  fun j => ∑ i, (t : Fin (k+1) → ℝ) i * ((q i : TSimplex n) : Fin (n+1) → ℝ) j

lemma affineSimplexFun_nonneg {n k : ℕ} (q : Fin (k+1) → TSimplex n) (t : TSimplex k) :
    ∀ j, 0 ≤ affineSimplexFun q t j := by
  intro j
  rw [affineSimplexFun]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (t.2.1 i) ((q i : TSimplex n).2.1 j)

lemma affineSimplexFun_sum {n k : ℕ} (q : Fin (k+1) → TSimplex n) (t : TSimplex k) :
    ∑ j, affineSimplexFun q t j = 1 := by
  have hpt : ∀ j, affineSimplexFun q t j
      = ∑ i, (t : Fin (k+1) → ℝ) i * ((q i : TSimplex n) : Fin (n+1) → ℝ) j := fun j => rfl
  rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_comm]
  simp only [← Finset.mul_sum, stdSimplex.sum_eq_one, mul_one]

lemma continuous_affineSimplexFun {n k : ℕ} (q : Fin (k+1) → TSimplex n) :
    Continuous (affineSimplexFun q) := by
  rw [continuous_pi_iff]
  intro j
  show Continuous fun t : TSimplex k =>
    ∑ i, (t : Fin (k+1) → ℝ) i * ((q i : TSimplex n) : Fin (n+1) → ℝ) j
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_subtype_val).mul continuous_const

/-- The affine simplex with prescribed vertices `q : Fin (k+1) → TSimplex n`. -/
def affineSimplex {n k : ℕ} (q : Fin (k+1) → TSimplex n) : C(TSimplex k, TSimplex n) where
  toFun t := ⟨affineSimplexFun q t, affineSimplexFun_nonneg q t, affineSimplexFun_sum q t⟩
  continuous_toFun := Continuous.subtype_mk (continuous_affineSimplexFun q) _

@[simp] lemma affineSimplex_apply {n k : ℕ} (q : Fin (k+1) → TSimplex n) (t : TSimplex k) :
    ((affineSimplex q t : TSimplex n) : Fin (n+1) → ℝ) = affineSimplexFun q t := rfl

/-- Summing a product of a sum over the fibres of an injective map. -/
lemma sum_ite_fiber {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (g : α → ℝ) (h : β → ℝ) :
    (∑ r, (∑ a, if f a = r then g a else 0) * h r) = ∑ a, g a * h (f a) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (f a)]
  · rw [if_pos rfl]
  · intro r _ hr
    rw [if_neg (fun hh => hr hh.symm), zero_mul]
  · intro hh; exact absurd (Finset.mem_univ _) hh

/-- **The face formula for affine simplices.**  The `i`-th face of the affine simplex with
vertices `q` is the affine simplex with vertices `q ∘ Fin.succAbove i`. -/
theorem affineSimplex_comp_faceIncl {n m : ℕ} (q : Fin (m+2) → TSimplex n) (i : Fin (m+2)) :
    (affineSimplex q).comp (faceInclC i) = affineSimplex (q ∘ Fin.succAbove i) := by
  ext t j
  simp only [ContinuousMap.comp_apply, faceInclC_apply, affineSimplex_apply,
    affineSimplexFun, Function.comp_apply, faceIncl_apply]
  exact sum_ite_fiber (Fin.succAbove i)
    (fun a => (t : Fin (m+1) → ℝ) a)
    (fun r => ((q r : TSimplex n) : Fin (n+1) → ℝ) j)

end

end Submission.Cohomology
