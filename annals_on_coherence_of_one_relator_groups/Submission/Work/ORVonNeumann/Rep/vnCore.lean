/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# Matrix operators on finite direct sums of `ℓ²(G)` and the von Neumann dimension

This module sets up the concrete model underlying the extended rank function `rk_G` of the
group von Neumann algebra `N(G)` (Jaikin-Zapirain–López-Álvarez, arXiv:1810.12135, §3.4;
Lück, *L²-Invariants*): a matrix `A` over `N(G)` acts as a bounded operator between finite
direct sums of copies of `ℓ²(G)`, and the von Neumann rank is the dimension of the kernel /
of the closure of the range, measured with the trace `τ a = ⟪δ₁, a δ₁⟫`.

## Main definitions

* `Work.ORVonNeumann.Rep.HSum n` — the `n`-fold `ℓ²`-direct sum `⊕_{i : Fin n} ℓ²(G)`;
* `Work.ORVonNeumann.Rep.hcoord n i` / `hinclude n i` — coordinate projection / inclusion;
* `Work.ORVonNeumann.Rep.hdelta n i` — the vector `e i ⊗ δ₁`;
* `Work.ORVonNeumann.Rep.matOp A` — the operator `HSum m →L HSum n` given by the matrix `A`;
* `Work.ORVonNeumann.Rep.hdim K` — the von Neumann dimension
  `∑ i, ‖K.starProjection (hdelta n i)‖ ^ 2` of a subspace `K ⊆ HSum n`;
* `Work.ORVonNeumann.Rep.mTrace n A` — the amplified trace `∑ i, τ (A i i)`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.SylvesterRank
import Submission.Work.ORVonNeumann.Rep.GroupVonNeumann
import Submission.Work.ORVonNeumann.Rep.Trace
import Submission.Work.ORVonNeumann.Rep.Dimension
import Submission.Work.Rep.exists_rangeProjection

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace
open scoped InnerProduct

namespace Work.ORVonNeumann.Rep

universe u

variable {G : Type u} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The `n`-fold `ℓ²`-direct sum `⊕_{i : Fin n} ℓ²(G)`, as a `PiLp`-space, so that it carries
the sum inner product `⟪x, y⟫ = ∑ i, ⟪x i, y i⟫`. -/
abbrev HSum (n : ℕ) : Type u := PiLp 2 (fun _ : Fin n => l2 G)

/-- The `i`-th coordinate projection `HSum n → ℓ²(G)`. -/
noncomputable def hcoord (n : ℕ) (i : Fin n) : HSum (G := G) n →L[ℂ] l2 G :=
  (ContinuousLinearMap.proj i).comp
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => l2 G)).toContinuousLinearMap

/-- The `i`-th coordinate inclusion `ℓ²(G) → HSum n`. -/
noncomputable def hinclude (n : ℕ) (i : Fin n) : l2 G →L[ℂ] HSum (G := G) n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => l2 G)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Fin n => l2 G) i)

/-- The vector which is `δ₁` in the `i`-th summand and `0` elsewhere. -/
noncomputable def hdelta (n : ℕ) (i : Fin n) : HSum (G := G) n :=
  hinclude (G := G) n i (delta1 G)

theorem hcoord_apply (n : ℕ) (i : Fin n) (x : HSum (G := G) n) :
    hcoord (G := G) n i x = x.ofLp i := rfl

@[simp]
theorem hcoord_hinclude (n : ℕ) (i j : Fin n) (x : l2 G) :
    hcoord (G := G) n i (hinclude (G := G) n j x) = if i = j then x else 0 := by
  by_cases h : i = j
  · subst h; simp [hcoord, hinclude]
  · simp [hcoord, hinclude, h]

theorem hdelta_apply (n : ℕ) (i : Fin n) :
    hdelta (G := G) n i = hinclude (G := G) n i (delta1 G) := rfl

@[simp]
theorem hcoord_hdelta (n : ℕ) (i j : Fin n) :
    hcoord (G := G) n i (hdelta (G := G) n j) = if i = j then delta1 G else 0 := by
  rw [hdelta_apply, hcoord_hinclude]

theorem hcoord_comp_hinclude (n : ℕ) (i j : Fin n) :
    (hcoord (G := G) n i).comp (hinclude (G := G) n j)
      = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    ext x
    simp [ContinuousLinearMap.comp_apply, hcoord_hinclude]
  · ext x
    simp [ContinuousLinearMap.comp_apply, hcoord_hinclude, h]

theorem hinclude_adjoint (n : ℕ) (i : Fin n) :
    (hinclude (G := G) n i)† = hcoord (G := G) n i := by
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [PiLp.inner_apply,
    Finset.sum_eq_single i (fun l _ hl => by simp [hinclude, hl])
      (fun h => absurd (Finset.mem_univ i) h)]
  simp [hcoord, hinclude]

theorem hcoord_adjoint (n : ℕ) (i : Fin n) :
    (hcoord (G := G) n i)† = hinclude (G := G) n i := by
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [PiLp.inner_apply,
    Finset.sum_eq_single i (fun l _ hl => by simp [hcoord, hinclude, hl])
      (fun h => absurd (Finset.mem_univ i) h)]
  simp [hcoord, hinclude]

/-- A matrix over `N(G)` acts on the finite direct sum `⊕_{j : Fin m} ℓ²(G)` as the operator
`x ↦ (∑ j, A i j (x j))_i`. -/
noncomputable def matOp {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G))) :
    HSum (G := G) m →L[ℂ] HSum (G := G) n :=
  ∑ i : Fin n, (hinclude n i).comp
    (∑ j : Fin m, (((A i j : ↥(groupVonNeumann G)) : boundedEnd G)).comp (hcoord m j))

theorem hcoord_matOp_apply {n m : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (x : HSum (G := G) m) (i : Fin n) :
    hcoord (G := G) n i (matOp (G := G) A x)
      = ∑ j : Fin m, (((A i j : ↥(groupVonNeumann G)) : boundedEnd G)) (hcoord m j x) := by
  classical
  rw [matOp, sum_apply, map_sum]
  rw [Finset.sum_eq_single i
    (by intro l _ hl
        rw [ContinuousLinearMap.comp_apply, hcoord_hinclude, if_neg (Ne.symm hl)])
    (by intro h; exact absurd (Finset.mem_univ i) h)]
  rw [ContinuousLinearMap.comp_apply, hcoord_hinclude, if_pos rfl, sum_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [ContinuousLinearMap.comp_apply]

theorem hcoord_matOp {n m : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G))) (i : Fin n) :
    (hcoord (G := G) n i).comp (matOp (G := G) A)
      = ∑ j : Fin m, (((A i j : ↥(groupVonNeumann G)) : boundedEnd G)).comp (hcoord m j) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, hcoord_matOp_apply,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.comp_apply]

/-- Extensionality of elements of `HSum n` through the coordinates. -/
theorem hsum_ext {n : ℕ} {x y : HSum (G := G) n}
    (h : ∀ i, hcoord (G := G) n i x = hcoord (G := G) n i y) : x = y := by
  apply PiLp.ext
  intro i
  exact h i

theorem matOp_ext {n m : ℕ} {T S : HSum (G := G) m →L[ℂ] HSum (G := G) n}
    (h : ∀ i, (hcoord (G := G) n i).comp T = (hcoord (G := G) n i).comp S) : T = S := by
  apply ContinuousLinearMap.ext
  intro x
  apply hsum_ext
  intro i
  have h' := congrArg (fun f : HSum (G := G) m →L[ℂ] l2 G => f x) (h i)
  simpa only [ContinuousLinearMap.comp_apply] using h'

theorem matOp_apply {n m : ℕ} (A : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    (x : HSum (G := G) m) (i : Fin n) :
    (matOp (G := G) A x).ofLp i
      = ∑ j : Fin m, ((A i j : ↥(groupVonNeumann G)) : boundedEnd G) (x.ofLp j) := by
  simpa only [hcoord_apply] using hcoord_matOp_apply (G := G) A x i

/-! ### The amplified trace -/

/-- The amplified trace on `Mat_n(N(G))`: `∑ i, τ (A i i)`. -/
noncomputable def mTrace (n : ℕ) (A : Matrix (Fin n) (Fin n) (↥(groupVonNeumann G))) : ℂ :=
  ∑ i : Fin n, tau (A i i)

@[simp]
theorem mTrace_apply (n : ℕ) (A : Matrix (Fin n) (Fin n) (↥(groupVonNeumann G))) :
    mTrace (G := G) n A = ∑ i : Fin n, tau (A i i) := rfl

/-- The von Neumann dimension of a closed subspace `K ⊆ ⊕_{i : Fin n} ℓ²(G)`, normalised so
that `hdim (⊤ : Submodule ℂ (HSum n)) = n`. -/
noncomputable def hdim {n : ℕ} (K : Submodule ℂ (HSum (G := G) n))
    [K.HasOrthogonalProjection] : ℝ :=
  ∑ i : Fin n, ‖K.starProjection (hdelta (G := G) n i)‖ ^ 2

end Work.ORVonNeumann.Rep
