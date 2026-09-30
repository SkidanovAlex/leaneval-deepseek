/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.BridgeSquare.CellChiADefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-
`Ψ_M(1_e)` as the two characteristic halves of a unit edge, `e = edgeCell v 0 k`.

Route: `PsiM_f_piSingle_eq_sum` (in `BridgeSquare/PsiM_truncCell_mem_range.lean`) writes the left
side as `∑_s chiSummand 1 _ e s` over the `1`-simplices `s` of the subdivision of `Q̄`.  Only the
two simplices with top cell the root face `R = eRoot v k` contribute: their flags are `eFlag0`,
`eFlag1` (`eRootI_eq_faceAct` shows the top cells match), and there the atlas coefficient
`rootCoeff` is the negated incidence `-qInc R U` — because the subdivision chain of a `1`-cell is
`-(∑_{U ⋖ R} qInc R U • [U,R])`, i.e. `PolyCW.subdivCell_succ` at `n = 0` together with
`PolyCW.coneLM_single`, `PolyCW.subdivCell_zero`.  (`QbarCW.inc = qInc` definitionally, and
`facets_eRoot` says `facets R = {eU0, eU1}`, so `eBeta v k = qInc R U0` and
`-qInc R U1 = -(-eBeta) = eBeta` by `qInc_eU1`.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Work.Subdivision

namespace Work.BridgeSquare

noncomputable section

open Work.MbarHomology

/-! ## §1  Combinatorics of the subdivision chain of a `1`-cell

`PolyCW.subdivCell P 1 e` is `-(cone_e (∑_{f ⋖ e} inc e f • [f]))`, so its only nonzero
coefficients are on the cones `[f, e]` of the facets `f` of `e`, where the value is `-inc e f`. -/

/-- Every simplex in the support of the subdivision chain of a cell has that cell as its last
vertex. -/
theorem subdivCell_last_mem_support (P : PolyCW) (n : ℕ) (e : {e : P.Cell // P.dim e = n}) :
    ∀ σ ∈ (PolyCW.subdivCell P n e).support, σ (Fin.last n) = e.1 := by
  induction n with
  | zero =>
    intro σ hσ
    rw [PolyCW.subdivCell_zero] at hσ
    rw [Finsupp.support_single _ (one_ne_zero : (1 : ℤ) ≠ 0)] at hσ
    rw [Finset.mem_singleton] at hσ
    rw [hσ]
    simp
  | succ n ih =>
    intro σ hσ
    rw [PolyCW.subdivCell_succ_eq] at hσ
    have hσ₁ := Finsupp.support_smul hσ
    obtain ⟨τ, hτ, hτe, hσeq⟩ := PolyCW.coneLM_mem_support hσ₁
    rw [hσeq, Simplex.snoc_apply_last]

/-- Off the top vertex, a subdivision chain coefficient vanishes. -/
theorem subdivCell_apply_eq_zero_of_last_ne (P : PolyCW) (n : ℕ)
    (e : {e : P.Cell // P.dim e = n}) {σ : Simplex P.Cell n} (h : σ (Fin.last n) ≠ e.1) :
    (PolyCW.subdivCell P n e) σ = 0 := by
  rw [← Finsupp.notMem_support_iff]
  intro hmem
  exact h (subdivCell_last_mem_support P n e σ hmem)

/-- The `0`-simplex at a vertex, evaluated at the first of the two indices of `Fin 2`. -/
theorem snoc_vertex_zero {α : Type*} [Preorder α] (a e : α)
    (h : ∀ i, (Simplex.vertex a : Simplex α 0) i < e) :
    (Simplex.snoc (Simplex.vertex a) e h) (0 : Fin 2) = a := by
  simpa using Simplex.snoc_apply_castSucc (Simplex.vertex a) e h (0 : Fin 1)

/-- The coefficient of the subdivision chain of a `1`-cell at the cone of a facet. -/
theorem subdivCell_one_snoc (P : PolyCW) (e : P.Cell) (hd : P.dim e = 1)
    (f : P.Cell) (hf : f ∈ P.facets e)
    (h : ∀ i, (Simplex.vertex f : Simplex P.Cell 0) i < e) :
    (PolyCW.subdivCell P 1 ⟨e, hd⟩) (Simplex.snoc (Simplex.vertex f) e h) = - P.inc e f := by
  rw [PolyCW.subdivCell_succ_eq (P := P) 0 ⟨e, hd⟩]
  simp only [zero_add, pow_one, PolyCW.subdivCell_zero, PolyCW.facetIndex]
  rw [map_sum]
  simp only [map_smul]
  have hcongr : (∑ x ∈ (P.facets e).attach,
        P.inc e ↑x • (P.coneLM e 0) (fun₀ | Simplex.vertex ↑x => 1))
      = (∑ x ∈ (P.facets e).attach,
        P.inc e ↑x • (Finsupp.single (Simplex.snoc (Simplex.vertex ↑x) e
          (fun i => by rw [Simplex.vertex_apply]; exact P.facet_lt x.2)) (1 : ℤ))) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [PolyCW.coneLM_single]
  rw [hcongr]
  rw [Finsupp.smul_apply, smul_eq_mul, neg_one_mul, neg_inj]
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single (⟨f, hf⟩ : {x // x ∈ P.facets e})]
  · rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_eq_same, mul_one]
  · intro b _ hb
    rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_eq_of_ne]
    · ring
    · intro hcon
      apply hb
      apply Subtype.ext
      have hf0 := snoc_vertex_zero f e h
      have hb0 := snoc_vertex_zero b.1 e (fun i => by rw [Simplex.vertex_apply]; exact P.facet_lt b.2)
      rw [← hcon, hf0] at hb0
      exact hb0.symm
  · intro habs; exact absurd (Finset.mem_attach _ _) habs

/-- A `1`-simplex is the cone of its first vertex with its last vertex. -/
theorem snoc_vertex_self {α : Type*} [Preorder α] (s : Simplex α 1) :
    s = Simplex.snoc (Simplex.vertex (s 0)) (s (Fin.last 1))
      (fun i => by rw [Simplex.vertex_apply]; exact s.strictMono (by decide +kernel)) := by
  apply Simplex.ext
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
    rw [hj, Simplex.snoc_toFun, Simplex.snocFun_castSucc, Simplex.vertex_apply]
    congr 1
  · rw [Simplex.snoc_toFun, Simplex.snocFun_last]

/-- A `1`-simplex is determined by its two vertices. -/
theorem Simplex.ext_fin2 {α : Type*} [Preorder α] {s t : Simplex α 1}
    (h0 : s 0 = t 0) (h1 : s (Fin.last 1) = t (Fin.last 1)) : s = t := by
  apply Simplex.ext
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
    subst hj
    simpa using h0
  · exact h1

/-! ## §2  The two characteristic simplices of a unit edge, as cones -/

/-- The sign change commutes with the cone construction. -/
theorem flagAct_snoc (g : Fin 4 → ZMod 2) {k : ℕ} (σ : Simplex QbarCW.Cell k)
    (e : QbarCW.Cell) (h : ∀ i, σ i < e) :
    Mbar.flagAct g (Simplex.snoc σ e h)
      = Simplex.snoc (Mbar.flagAct g σ) (Mbar.faceActCell g e) (fun i => by
          rw [Mbar.flagAct_apply]; exact Mbar.faceActCell_lt (h i)) := by
  apply Simplex.ext
  intro i
  rw [Mbar.flagAct_apply]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Simplex.snoc_apply_castSucc, Simplex.snoc_apply_castSucc, Mbar.flagAct_apply]
  · rw [Simplex.snoc_apply_last, Simplex.snoc_apply_last]

/-- The sign change on a `0`-simplex. -/
theorem flagAct_vertex (g : Fin 4 → ZMod 2) (a : QbarCW.Cell) :
    Mbar.flagAct g (Simplex.vertex a) = Simplex.vertex (Mbar.faceActCell g a) := by
  apply Simplex.ext
  intro i
  rw [Mbar.flagAct_apply, Simplex.vertex_apply, Simplex.vertex_apply]

/-- The lower characteristic simplex of a unit edge is the cone on the lower facet. -/
theorem eFlag0_snoc (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    eFlag0 v k hk
      = Simplex.snoc (Simplex.vertex (eU0 v k)) (eRoot v k)
          (fun i => by rw [Simplex.vertex_apply]; exact eU0_lt_eRoot v k hk) := by
  apply Simplex.ext
  intro i
  rw [eFlag0, eNice0, Mbar.flagAct_apply]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp only [Simplex.snoc_toFun, Simplex.snocFun_castSucc, Simplex.vertex_apply]
    rfl
  · simp only [Simplex.snoc_toFun, Simplex.snocFun_last]
    show (⟨faceAct (esig v k) (edgeFace v 0 k)⟩ : QbarCell) = eRoot v k
    rw [eRootI_eq_faceAct v k hk]
    rfl

/-- The upper characteristic simplex of a unit edge is the cone on the upper facet. -/
theorem eFlag1_snoc (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    eFlag1 v k hk
      = Simplex.snoc (Simplex.vertex (eU1 v k)) (eRoot v k)
          (fun i => by rw [Simplex.vertex_apply]; exact eU1_lt_eRoot v k hk) := by
  apply Simplex.ext
  intro i
  rw [eFlag1, eNice1, Mbar.flagAct_apply]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp only [Simplex.snoc_toFun, Simplex.snocFun_castSucc, Simplex.vertex_apply]
    rfl
  · simp only [Simplex.snoc_toFun, Simplex.snocFun_last]
    show (⟨faceAct (esig v k) (edgeFace v 0 k)⟩ : QbarCell) = eRoot v k
    rw [eRootI_eq_faceAct v k hk]
    rfl

/-- The lower characteristic simplex at its bottom vertex. -/
theorem eFlag0_zero (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    (eFlag0 v k hk) (0 : Fin 2) = eU0 v k := by
  rw [eFlag0_snoc v k hk]
  exact snoc_vertex_zero (eU0 v k) (eRoot v k)
    (fun i => by rw [Simplex.vertex_apply]; exact eU0_lt_eRoot v k hk)

/-- The upper characteristic simplex at its bottom vertex. -/
theorem eFlag1_zero (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < fibreLen v 0) :
    (eFlag1 v k hk) (0 : Fin 2) = eU1 v k := by
  rw [eFlag1_snoc v k hk]
  exact snoc_vertex_zero (eU1 v k) (eRoot v k)
    (fun i => by rw [Simplex.vertex_apply]; exact eU1_lt_eRoot v k hk)

/-! ## §3  The expansion -/

theorem PsiM_edgeCell_expand (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 0) :
    (Work.BridgeSquare.PsiM.f 1) (Pi.single (Work.BridgeSquare.edgeCell v 0 k) (1 : ℤ))
      = - Work.BridgeSquare.eBeta v k • Work.BridgeSquare.eChi0 v k hk
        - (Work.MbarHomology.qInc (Work.BridgeSquare.eRootI v k) (Work.BridgeSquare.eU1 v k).idx)
            • Work.BridgeSquare.eChi1 v k hk := by
  have hn' : (1 : ℕ) < 5 := by norm_num
  have hE := PsiM_f_piSingle_eq_sum 1 hn' (edgeCell v 0 k)
  rw [hE]
  -- the facets of the root face of the cell
  have hfacet : QbarCW.facets (Mbar.rootCx 1 (edgeCell v 0 k)) = {eU0 v k, eU1 v k} := by
    rw [show Mbar.rootCx 1 (edgeCell v 0 k) = eRoot v k from rfl]
    exact facets_eRoot v k hk
  have hf0 : eU0 v k ∈ QbarCW.facets (Mbar.rootCx 1 (edgeCell v 0 k)) := by
    rw [hfacet]; exact Finset.mem_insert_self _ _
  have hf1 : eU1 v k ∈ QbarCW.facets (Mbar.rootCx 1 (edgeCell v 0 k)) := by
    rw [hfacet]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  -- the top vertex of the two characteristic simplices
  have htop0 : eFlag0 v k hk (Fin.last 1) = Mbar.rootCx 1 (edgeCell v 0 k) := by
    rw [eFlag0_snoc v k hk, Simplex.snoc_apply_last]
    exact (show eRoot v k = Mbar.rootCx 1 (edgeCell v 0 k) from rfl)
  have htop1 : eFlag1 v k hk (Fin.last 1) = Mbar.rootCx 1 (edgeCell v 0 k) := by
    rw [eFlag1_snoc v k hk, Simplex.snoc_apply_last]
    exact (show eRoot v k = Mbar.rootCx 1 (edgeCell v 0 k) from rfl)
  -- any simplex whose top vertex is the root face is one of the two characteristic ones
  have htop_flag : ∀ s : Simplex QbarCW.Cell 1,
      s (Fin.last 1) = Mbar.rootCx 1 (edgeCell v 0 k) →
      s ∈ ({eFlag0 v k hk, eFlag1 v k hk} : Finset (Simplex QbarCW.Cell 1)) := by
    intro s hs
    have hlt : s 0 < Mbar.rootCx 1 (edgeCell v 0 k) := by
      rw [← hs]; exact s.strictMono (by decide +kernel)
    have hdim : QbarCW.dim (s 0) = 0 := by
      have h := QbarCW.dim_lt' hlt
      rw [Mbar.rootCx_dim 1 (edgeCell v 0 k)] at h
      omega
    have hmem : s 0 ∈ QbarCW.facets (Mbar.rootCx 1 (edgeCell v 0 k)) := by
      rw [QbarCW.mem_facets]
      exact ⟨hlt, by rw [Mbar.rootCx_dim 1 (edgeCell v 0 k), hdim]⟩
    rw [hfacet] at hmem
    rcases Finset.mem_insert.mp hmem with h0 | h1
    · refine Finset.mem_insert.mpr (Or.inl ?_)
      refine Simplex.ext_fin2 ?_ ?_
      · rw [h0, eFlag0_zero]
      · rw [hs, htop0]
    · refine Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr ?_))
      refine Simplex.ext_fin2 ?_ ?_
      · rw [Finset.mem_singleton.mp h1, eFlag1_zero]
      · rw [hs, htop1]
  -- the two characteristic simplices are distinct
  have hne : eFlag0 v k hk ≠ eFlag1 v k hk := by
    intro hcon
    exact eU0_ne_eU1 v k hk (by rw [← eFlag0_zero v k hk, hcon, eFlag1_zero v k hk])
  -- the sum reduces to the two characteristic simplices
  have hsum : (∑ s : Simplex QbarCW.Cell 1, chiSummand 1 hn' (edgeCell v 0 k) s)
      = chiSummand 1 hn' (edgeCell v 0 k) (eFlag0 v k hk)
        + chiSummand 1 hn' (edgeCell v 0 k) (eFlag1 v k hk) := by
    have h1 : (∑ s : Simplex QbarCW.Cell 1, chiSummand 1 hn' (edgeCell v 0 k) s)
        = ∑ s ∈ ({eFlag0 v k hk, eFlag1 v k hk} : Finset (Simplex QbarCW.Cell 1)),
            chiSummand 1 hn' (edgeCell v 0 k) s :=
      (Finset.sum_subset (Finset.subset_univ _) (fun s _ hs => by
        by_cases htop : s (Fin.last 1) = Mbar.rootCx 1 (edgeCell v 0 k)
        · exact absurd (htop_flag s htop) hs
        · exact chiSummand_neg 1 hn' (edgeCell v 0 k) s htop)).symm
    rw [h1, Finset.sum_pair hne]
  rw [hsum]
  rw [chiSummand_pos 1 hn' (edgeCell v 0 k) (eFlag0 v k hk) htop0,
    chiSummand_pos 1 hn' (edgeCell v 0 k) (eFlag1 v k hk) htop1]
  -- the atlas coefficients
  have hm0 : ∀ i, (Simplex.vertex (eU0 v k) : Simplex QbarCell 0) i
      < Mbar.rootCx 1 (edgeCell v 0 k) :=
    fun i => by rw [Simplex.vertex_apply]; exact eU0_lt_eRoot v k hk
  have hm1 : ∀ i, (Simplex.vertex (eU1 v k) : Simplex QbarCell 0) i
      < Mbar.rootCx 1 (edgeCell v 0 k) :=
    fun i => by rw [Simplex.vertex_apply]; exact eU1_lt_eRoot v k hk
  have hrc0 : Mbar.mbarAtlasOf.rootCoeff 1 (edgeCell v 0 k) (eFlag0 v k hk) = - eBeta v k := by
    show (PolyCW.subdivCell QbarCW 1
        ⟨Mbar.rootCx 1 (edgeCell v 0 k), Mbar.rootCx_dim 1 (edgeCell v 0 k)⟩)
      (eFlag0 v k hk) = - eBeta v k
    rw [eFlag0_snoc v k hk]
    exact subdivCell_one_snoc QbarCW (Mbar.rootCx 1 (edgeCell v 0 k))
      (Mbar.rootCx_dim 1 (edgeCell v 0 k)) (eU0 v k) hf0 hm0
  have hrc1 : Mbar.mbarAtlasOf.rootCoeff 1 (edgeCell v 0 k) (eFlag1 v k hk)
      = - qInc (eRootI v k) (eU1 v k).idx := by
    show (PolyCW.subdivCell QbarCW 1
        ⟨Mbar.rootCx 1 (edgeCell v 0 k), Mbar.rootCx_dim 1 (edgeCell v 0 k)⟩)
      (eFlag1 v k hk) = - qInc (eRootI v k) (eU1 v k).idx
    rw [eFlag1_snoc v k hk]
    exact subdivCell_one_snoc QbarCW (Mbar.rootCx 1 (edgeCell v 0 k))
      (Mbar.rootCx_dim 1 (edgeCell v 0 k)) (eU1 v k) hf1 hm1
  have hchi0 : singGen (Mbar.chi 1 (Mbar.rootSimplex 1 hn' (edgeCell v 0 k) (eFlag0 v k hk)))
      = eChi0 v k hk := rfl
  have hchi1 : singGen (Mbar.chi 1 (Mbar.rootSimplex 1 hn' (edgeCell v 0 k) (eFlag1 v k hk)))
      = eChi1 v k hk := rfl
  rw [hrc0, hrc1, hchi0, hchi1]
  -- `chiSummand` carries the `ℤ`-module `SMul` of `ModuleCat`; the statement of the
  -- theorem carries the canonical one.  `Int.cast_smul_eq_zsmul` relates them.
  rw [← Int.cast_smul_eq_zsmul ℤ, ← Int.cast_smul_eq_zsmul ℤ]
  simp only [Int.cast_id, neg_smul, sub_eq_add_neg]

end

end Work.BridgeSquare
