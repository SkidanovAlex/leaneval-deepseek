/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.Local

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The per-cell filtration of a skeletal level

The `n`-th skeletal level of the subdivision is the pair
`(cellSub (n+1)) ⊇ (cellSub n)`, whose quotient is the `n`-th graded piece
(`PolyCW.cellRel`/`PolyCW.sdRel`).  To split that graded piece into the
contributions of the individual `(n+1)`-cells we refine both filtrations by a
finset `E` of `(n+1)`-cells:

* `cellTop P hdd n E` — the `n`-skeleton together with the cells of `E`;
* `sdTop P n E` — the `n`-skeleton together with the simplices whose *top* vertex
  is a cell of `E`.

Both are `SubData`s of the ambient chain complexes (`cellChain P hdd`, `sdChain P`),
so that the relative-subcomplex machinery (`SubData.comapChain`,
`quasiIso_of_sub_quot`) applies verbatim.  With `E = ∅` they are the `n`-skeleta
and with `E = P.faces (n+1)` they are the `(n+1)`-skeleta (`cellTop_empty`,
`cellTop_faces`, `sdTop_empty`, `sdTop_faces`).

The successive quotient of `sdTop P n (insert a E)` by `sdTop P n E` is the local
complex `locCx P a` of the new cell, and the successive quotient on the cellular
side is the one-dimensional complex `unitCx (n+1)`; this is the sense in which the
graded piece is the direct sum of the local complexes, and it is what turns the
per-cell condition `LocallySpherical` into the quasi-isomorphism of the
subdivision (`PolyCW.subdiv_quasiIso_of_local`).
-/

namespace Work.Subdivision

open CategoryTheory

universe u

noncomputable section

namespace SubData

/-- Subcomplex data is determined by its degreewise submodules. -/
theorem ext {C : ChainComplex (ModuleCat ℤ) ℕ} {S T : SubData C}
    (h : ∀ k, S.sub k = T.sub k) : S = T := by
  obtain ⟨s, d⟩ := S
  obtain ⟨t, d'⟩ := T
  have hs : s = t := funext h
  subst hs
  have hd : d = d' := Subsingleton.elim d d'
  rw [hd]

end SubData

namespace PolyCW

variable (P : PolyCW.{u})

/-! ### The two refined filtrations -/

/-- The generator of the cellular chain module attached to a cell, in the degree
of the cell. -/
abbrev cellElem (hdd : P.HasDdZero) (k : ℕ) (e : {e : P.Cell // P.dim e = k}) :
    (cellChain P hdd).X k :=
  Finsupp.single e 1

/-- The `n`-skeleton together with the `(n+1)`-cells belonging to `E`, on the
cellular side. -/
def cellTopMod (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell) (k : ℕ) :
    Submodule ℤ ((cellChain P hdd).X k) :=
  cellSubMod P hdd n k ⊔ Submodule.span ℤ {y : (cellChain P hdd).X k |
    ∃ e : {e : P.Cell // P.dim e = k}, e.1 ∈ E ∧ P.dim e.1 = n + 1 ∧ y = cellElem P hdd k e}

/-- The `n`-skeleton together with the simplices whose top vertex is an
`(n+1)`-cell belonging to `E`, on the subdivided side. -/
def sdTopMod (n : ℕ) (E : Finset P.Cell) (k : ℕ) : Submodule ℤ ((sdChain P).X k) :=
  sdSubMod P n k ⊔ Submodule.span ℤ {y : (sdChain P).X k |
    ∃ σ : Simplex P.Cell k, σ (Fin.last k) ∈ E ∧ P.dim (σ (Fin.last k)) = n + 1 ∧
      y = sdElem P σ}

theorem cellElem_mem_cellTopMod (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell) (k : ℕ)
    (e : {e : P.Cell // P.dim e = k}) (he : e.1 ∈ E) (hd : P.dim e.1 = n + 1) :
    cellElem P hdd k e ∈ cellTopMod P hdd n E k :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨e, he, hd, rfl⟩)

theorem sdElem_mem_sdTopMod (n : ℕ) (E : Finset P.Cell) (k : ℕ) (σ : Simplex P.Cell k)
    (he : σ (Fin.last k) ∈ E) (hd : P.dim (σ (Fin.last k)) = n + 1) :
    sdElem P σ ∈ sdTopMod P n E k :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨σ, he, hd, rfl⟩)

theorem cellSubMod_le_cellTopMod (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell) (k : ℕ) :
    cellSubMod P hdd n k ≤ cellTopMod P hdd n E k :=
  le_sup_left

theorem sdSubMod_le_sdTopMod (n : ℕ) (E : Finset P.Cell) (k : ℕ) :
    sdSubMod P n k ≤ sdTopMod P n E k :=
  le_sup_left


/-! ### The filtrations are filtrations -/

/-- The differential of the subdivided complex, read on a generator. -/
theorem sdChain_d_sdElem (k : ℕ) (σ : Simplex P.Cell (k + 1)) :
    ((sdChain P).d (k + 1) k).hom (sdElem P σ)
      = ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • sdElem P (Simplex.face i σ) := by
  simp only [sdChain_d, ModuleCat.hom_ofHom]
  exact D_sdElem P σ

/-- The `n`-skeleton plus cells of `E` is closed under the cellular
differential: the boundary of an `(n+1)`-cell is an `n`-chain. -/
theorem cellTopMod_d_mem (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell) (k : ℕ) :
    cellTopMod P hdd n E (k + 1) ≤
      Submodule.comap (((cellChain P hdd).d (k + 1) k).hom) (cellTopMod P hdd n E k) := by
  rw [cellTopMod]
  refine sup_le ?_ ?_
  · intro x hx
    exact Submodule.mem_comap.mpr
      (cellSubMod_le_cellTopMod P hdd n E k ((cellSub P hdd n).d_mem k x hx))
  · rw [Submodule.span_le]
    rintro y ⟨e, he, hd, rfl⟩
    have hk : k ≤ n := by
      have h : P.dim e.1 = k + 1 := e.2
      omega
    have htop : cellTopMod P hdd n E k = ⊤ := by
      rw [cellTopMod, cellSubMod, if_pos hk]
      exact le_antisymm le_top le_sup_left
    rw [htop]
    exact Submodule.mem_top

/-- The refined filtration on the subdivided side is closed under the
differential: dropping a non-top vertex keeps the top vertex, dropping the top
vertex lands in the `n`-skeleton. -/
theorem sdTopMod_d_mem (n : ℕ) (E : Finset P.Cell) (k : ℕ) :
    sdTopMod P n E (k + 1) ≤
      Submodule.comap (((sdChain P).d (k + 1) k).hom) (sdTopMod P n E k) := by
  rw [sdTopMod]
  refine sup_le ?_ ?_
  · intro x hx
    exact Submodule.mem_comap.mpr
      (sdSubMod_le_sdTopMod P n E k (D_mem_sdSubMod P n k hx))
  · rw [Submodule.span_le]
    rintro y ⟨σ, he, hd, rfl⟩
    show ((sdChain P).d (k + 1) k).hom (sdElem P σ) ∈ sdTopMod P n E k
    rw [sdChain_d_sdElem]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rcases eq_or_ne i (Fin.last (k + 1)) with rfl | hi
    · refine Submodule.mem_sup_left (sdElem_mem_sdSubMod P fun j => ?_)
      rw [Simplex.face_apply]
      have hidx : Fin.succAbove (Fin.last (k + 1)) j < Fin.last (k + 1) := by
        rw [Fin.succAbove_last]
        exact Fin.castSucc_lt_last j
      have hlt : σ (Fin.succAbove (Fin.last (k + 1)) j) < σ (Fin.last (k + 1)) :=
        σ.strictMono hidx
      have hlt' : P.dim (σ (Fin.succAbove (Fin.last (k + 1)) j)) < n + 1 := by
        rw [← hd]
        exact P.dim_lt hlt.le (ne_of_lt hlt)
      omega
    · refine Submodule.mem_sup_right (Submodule.subset_span ⟨Simplex.face i σ, ?_, ?_, rfl⟩)
      · rw [Simplex.face_apply, Fin.succAbove_ne_last_last hi]
        exact he
      · rw [Simplex.face_apply, Fin.succAbove_ne_last_last hi]
        exact hd

/-! ### The refined filtrations as subcomplex data -/

/-- The refined filtration of the cellular chain complex: the `n`-skeleton plus
the cells of `E`. -/
def cellTop (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell) : SubData (cellChain P hdd) where
  sub k := cellTopMod P hdd n E k
  d_mem k x hx :=
    show ((cellChain P hdd).d (k + 1) k).hom x ∈ cellTopMod P hdd n E k from
      Submodule.mem_comap.mp (cellTopMod_d_mem P hdd n E k hx)

/-- The refined filtration of the subdivided chain complex: the `n`-skeleton
plus the simplices whose top vertex is an `(n+1)`-cell of `E`. -/
def sdTop (n : ℕ) (E : Finset P.Cell) : SubData (sdChain P) where
  sub k := sdTopMod P n E k
  d_mem k x hx :=
    show ((sdChain P).d (k + 1) k).hom x ∈ sdTopMod P n E k from
      Submodule.mem_comap.mp (sdTopMod_d_mem P n E k hx)

@[simp] theorem cellTop_sub (hdd : P.HasDdZero) (n : ℕ) (E : Finset P.Cell) (k : ℕ) :
    (cellTop P hdd n E).sub k = cellTopMod P hdd n E k := rfl

@[simp] theorem sdTop_sub (n : ℕ) (E : Finset P.Cell) (k : ℕ) :
    (sdTop P n E).sub k = sdTopMod P n E k := rfl

/-! ### Monotonicity in the set of cells -/

theorem cellTopMod_mono (hdd : P.HasDdZero) (n : ℕ) {E E' : Finset P.Cell} (h : E ⊆ E')
    (k : ℕ) : cellTopMod P hdd n E k ≤ cellTopMod P hdd n E' k := by
  refine sup_le le_sup_left ?_
  rw [Submodule.span_le]
  rintro y ⟨e, he, hd, rfl⟩
  exact Submodule.mem_sup_right (Submodule.subset_span ⟨e, h he, hd, rfl⟩)

theorem sdTopMod_mono (n : ℕ) {E E' : Finset P.Cell} (h : E ⊆ E') (k : ℕ) :
    sdTopMod P n E k ≤ sdTopMod P n E' k := by
  refine sup_le le_sup_left ?_
  rw [Submodule.span_le]
  rintro y ⟨σ, he, hd, rfl⟩
  exact Submodule.mem_sup_right (Submodule.subset_span ⟨σ, h he, hd, rfl⟩)

/-! ### The extreme cases -/

/-- The span of all cellular generators of a given degree is everything. -/
theorem cellSpan_gen_top (hdd : P.HasDdZero) (k : ℕ) :
    Submodule.span ℤ {y : (cellChain P hdd).X k |
      ∃ e : {e : P.Cell // P.dim e = k}, y = cellElem P hdd k e} = ⊤ := by
  have htop : Submodule.span ℤ {y : cellMod P k |
      ∃ e : {e : P.Cell // P.dim e = k}, y = Finsupp.single e (1 : ℤ)} = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    rw [show {y : cellMod P k | ∃ e : {e : P.Cell // P.dim e = k}, y = Finsupp.single e (1 : ℤ)}
        = {y : cellMod P k |
            ∃ b ∈ (Set.univ : Set {e : P.Cell // P.dim e = k}), y = Finsupp.single b 1} from by
      ext y
      constructor
      · rintro ⟨e, rfl⟩
        exact ⟨e, Set.mem_univ e, rfl⟩
      · rintro ⟨e, -, rfl⟩
        exact ⟨e, rfl⟩]
    rw [Finsupp.mem_span_single_one_iff (R := ℤ)]
    exact Set.subset_univ _
  exact htop

theorem cellSubMod_eq_top (hdd : P.HasDdZero) {n k : ℕ} (h : k ≤ n) :
    cellSubMod P hdd n k = ⊤ := by
  rw [cellSubMod, if_pos h]

theorem cellTopMod_empty (hdd : P.HasDdZero) (n : ℕ) (k : ℕ) :
    cellTopMod P hdd n ∅ k = cellSubMod P hdd n k := by
  rw [cellTopMod, show {y : (cellChain P hdd).X k |
      ∃ e : {e : P.Cell // P.dim e = k}, e.1 ∈ (∅ : Finset P.Cell) ∧ P.dim e.1 = n + 1 ∧
        y = cellElem P hdd k e} = (∅ : Set ((cellChain P hdd).X k)) from by
    ext y
    constructor <;> rintro ⟨e, he, -⟩ <;> exact absurd he (Finset.notMem_empty e.1),
    Submodule.span_empty, sup_bot_eq]

theorem sdTopMod_empty (n : ℕ) (k : ℕ) : sdTopMod P n ∅ k = sdSubMod P n k := by
  rw [sdTopMod, show {y : (sdChain P).X k |
      ∃ σ : Simplex P.Cell k, σ (Fin.last k) ∈ (∅ : Finset P.Cell) ∧
        P.dim (σ (Fin.last k)) = n + 1 ∧ y = sdElem P σ} = (∅ : Set ((sdChain P).X k)) from by
    ext y
    constructor <;> rintro ⟨σ, hσ, -⟩ <;> exact absurd hσ (Finset.notMem_empty (σ (Fin.last k))),
    Submodule.span_empty, sup_bot_eq]

theorem cellTopMod_faces (hdd : P.HasDdZero) (n : ℕ) (k : ℕ) :
    cellTopMod P hdd n (P.faces (n + 1)) k = cellSubMod P hdd (n + 1) k := by
  rcases lt_trichotomy k (n + 1) with hlt | heq | hgt
  · rw [cellSubMod_eq_top P hdd (by omega)]
    refine eq_top_iff.mpr ?_
    rw [cellTopMod, cellSubMod_eq_top P hdd (by omega)]
    exact le_sup_left
  · subst heq
    rw [cellTopMod, cellSubMod_eq_bot P hdd (by omega), bot_sup_eq,
      cellSubMod_eq_top P hdd le_rfl]
    refine eq_top_iff.mpr ?_
    rw [show {y : (cellChain P hdd).X (n + 1) |
        ∃ e : {e : P.Cell // P.dim e = n + 1}, e.1 ∈ P.faces (n + 1) ∧ P.dim e.1 = n + 1 ∧
          y = cellElem P hdd (n + 1) e}
        = {y : (cellChain P hdd).X (n + 1) |
            ∃ e : {e : P.Cell // P.dim e = n + 1}, y = cellElem P hdd (n + 1) e} from by
      ext y
      constructor
      · rintro ⟨e, -, -, rfl⟩; exact ⟨e, rfl⟩
      · rintro ⟨e, rfl⟩; exact ⟨e, (P.mem_faces (n + 1) e.1).2 e.2, e.2, rfl⟩]
    rw [cellSpan_gen_top P hdd (n + 1)]
  · rw [cellTopMod, cellSubMod_eq_bot P hdd (by omega), cellSubMod_eq_bot P hdd (by omega),
      bot_sup_eq]
    refine le_antisymm (Submodule.span_le.mpr fun y hy => by
      obtain ⟨e, -, hd, rfl⟩ := hy
      exact absurd hd (by omega)) bot_le

theorem sdTopMod_faces (n : ℕ) (k : ℕ) :
    sdTopMod P n (P.faces (n + 1)) k = sdSubMod P (n + 1) k := by
  refine le_antisymm ?_ ?_
  · refine sup_le (sdSubMod_mono P (Nat.le_succ n) k) ?_
    rw [Submodule.span_le]
    rintro y ⟨σ, -, hd, rfl⟩
    refine sdElem_mem_sdSubMod P fun i => ?_
    exact le_trans (P.dim_le (σ.strictMono.monotone (Fin.le_last i))) (le_of_eq hd)
  · rw [sdSubMod, Submodule.span_le]
    rintro y ⟨σ, hσ, rfl⟩
    by_cases hall : ∀ i, P.dim (σ i) ≤ n
    · exact Submodule.mem_sup_left (sdElem_mem_sdSubMod P hall)
    · push_neg at hall
      obtain ⟨i, hi⟩ := hall
      have hlast : P.dim (σ (Fin.last k)) = n + 1 := by
        have h1 : P.dim (σ i) ≤ P.dim (σ (Fin.last k)) :=
          P.dim_le (σ.strictMono.monotone (Fin.le_last i))
        have h2 : P.dim (σ (Fin.last k)) ≤ n + 1 := hσ (Fin.last k)
        omega
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨σ,
        (P.mem_faces (n + 1) (σ (Fin.last k))).2 hlast, hlast, rfl⟩)

theorem cellTop_empty (hdd : P.HasDdZero) (n : ℕ) :
    cellTop P hdd n ∅ = cellSub P hdd n :=
  SubData.ext fun k => cellTopMod_empty P hdd n k

theorem sdTop_empty (n : ℕ) : sdTop P n ∅ = sdSub P n :=
  SubData.ext fun k => sdTopMod_empty P n k

theorem cellTop_faces (hdd : P.HasDdZero) (n : ℕ) :
    cellTop P hdd n (P.faces (n + 1)) = cellSub P hdd (n + 1) :=
  SubData.ext fun k => cellTopMod_faces P hdd n k

theorem sdTop_faces (n : ℕ) : sdTop P n (P.faces (n + 1)) = sdSub P (n + 1) :=
  SubData.ext fun k => sdTopMod_faces P n k

end PolyCW

end

end Work.Subdivision
