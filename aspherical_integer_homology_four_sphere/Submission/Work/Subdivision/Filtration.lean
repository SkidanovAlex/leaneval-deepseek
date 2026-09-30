/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.SubComplex
import Submission.Work.Subdivision.SdChain
import Submission.Work.Subdivision.Subdiv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The skeletal filtrations of the cellular and subdivided chain complexes

The subdivision map `subdiv : cellChain P ⟶ sdChain P` is to be compared by
induction on the skeleta.  This file sets up the two filtrations as `SubData`s
(degreewise submodules closed under the differential):

* `PolyCW.cellSubMod P hdd n k ⊆ cellChain P k` is everything if `k ≤ n` and `0`
  otherwise — in degree `k` the cellular chains are spanned by the `k`-cells, so
  "cells of dimension `≤ n`" is exactly the naive truncation at `n`;
* `PolyCW.sdSubMod P n k ⊆ sdChain P k` is spanned by the `k`-simplices all of
  whose vertices are cells of dimension `≤ n`.
-/

namespace Work.Subdivision

universe u

namespace PolyCW

variable (P : PolyCW.{u})

/-! ### The filtration on the cellular side -/

/-- In degree `k` the cellular chain complex is free on the `k`-cells, so the
subcomplex of cells of dimension `≤ n` is the truncation at `n`. -/
noncomputable def cellSubMod (hdd : P.HasDdZero) (n k : ℕ) :
    Submodule ℤ ((cellChain P hdd).X k) :=
  if k ≤ n then ⊤ else ⊥

theorem mem_cellSubMod (hdd : P.HasDdZero) {n k : ℕ} {x : (cellChain P hdd).X k}
    (h : k ≤ n) : x ∈ cellSubMod P hdd n k := by
  rw [cellSubMod, if_pos h]
  exact Submodule.mem_top

theorem cellSubMod_eq_bot (hdd : P.HasDdZero) {n k : ℕ} (h : ¬ k ≤ n) :
    cellSubMod P hdd n k = ⊥ := by
  rw [cellSubMod, if_neg h]

theorem cellSubMod_mono (hdd : P.HasDdZero) {n n' : ℕ} (h : n ≤ n') (k : ℕ) :
    cellSubMod P hdd n k ≤ cellSubMod P hdd n' k := by
  by_cases hk : k ≤ n
  · rw [cellSubMod, if_pos hk, cellSubMod, if_pos (le_trans hk h)]
  · rw [cellSubMod, if_neg hk]
    exact bot_le

/-- The skeletal filtration of the cellular chain complex, as subcomplex data. -/
noncomputable def cellSub (hdd : P.HasDdZero) (n : ℕ) : SubData (cellChain P hdd) where
  sub k := cellSubMod P hdd n k
  d_mem k x hx := by
    by_cases h : k + 1 ≤ n
    · exact mem_cellSubMod P hdd (by omega)
    · rw [cellSubMod_eq_bot P hdd h, Submodule.mem_bot] at hx
      rw [hx, map_zero]
      exact Submodule.zero_mem _

/-! ### The filtration on the subdivided side -/

/-- The generator of the subdivision chain complex attached to a simplex, as an
element of the ambient `ModuleCat` carrier. -/
noncomputable def sdElem {k : ℕ} (σ : Simplex P.Cell k) : (sdChain P).X k :=
  Finsupp.single σ 1

/-- The `k`-chains of the subdivision spanned by the `k`-simplices whose vertices
are all cells of dimension `≤ n`. -/
noncomputable def sdSubMod (n k : ℕ) : Submodule ℤ ((sdChain P).X k) :=
  Submodule.span ℤ {x : (sdChain P).X k | ∃ σ : Simplex P.Cell k,
    (∀ i, P.dim (σ i) ≤ n) ∧ x = sdElem P σ}

theorem sdElem_mem_sdSubMod {n k : ℕ} {σ : Simplex P.Cell k}
    (h : ∀ i, P.dim (σ i) ≤ n) : sdElem P σ ∈ sdSubMod P n k :=
  Submodule.subset_span ⟨σ, h, rfl⟩

theorem sdSubMod_mono {n n' : ℕ} (h : n ≤ n') (k : ℕ) : sdSubMod P n k ≤ sdSubMod P n' k := by
  show Submodule.span ℤ {x : (sdChain P).X k | ∃ σ : Simplex P.Cell k,
      (∀ i, P.dim (σ i) ≤ n) ∧ x = sdElem P σ} ≤ sdSubMod P n' k
  rw [Submodule.span_le]
  rintro x ⟨σ, hσ, rfl⟩
  exact sdElem_mem_sdSubMod P fun i => le_trans (hσ i) h

/-- The differential of a generator of the subdivision. -/
theorem D_sdElem {k : ℕ} (σ : Simplex P.Cell (k + 1)) :
    D (α := P.Cell) k (sdElem P σ) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • sdElem P (Simplex.face i σ) :=
  D_single k σ

/-- The differential preserves the filtration on the subdivided side. -/
theorem D_mem_sdSubMod (n k : ℕ) :
    sdSubMod P n (k + 1) ≤
      Submodule.comap (((sdChain P).d (k + 1) k).hom) (sdSubMod P n k) := by
  show Submodule.span ℤ {x : (sdChain P).X (k + 1) | ∃ σ : Simplex P.Cell (k + 1),
      (∀ i, P.dim (σ i) ≤ n) ∧ x = sdElem P σ} ≤
    Submodule.comap (((sdChain P).d (k + 1) k).hom) (sdSubMod P n k)
  rw [Submodule.span_le]
  rintro x ⟨σ, hσ, rfl⟩
  refine Submodule.mem_comap.mpr ?_
  rw [sdChain_d P k]
  show (D (α := P.Cell) k (sdElem P σ)) ∈ sdSubMod P n k
  rw [D_sdElem]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact sdElem_mem_sdSubMod P fun j => hσ (i.succAbove j)

/-- The skeletal filtration of the subdivided chain complex, as subcomplex data. -/
noncomputable def sdSub (n : ℕ) : SubData (sdChain P) where
  sub k := sdSubMod P n k
  d_mem k x hx := D_mem_sdSubMod P n k hx

end PolyCW

end Work.Subdivision
