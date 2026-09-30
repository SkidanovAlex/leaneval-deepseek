/-
# `BridgeSquare/PsiM_edgeCell_eq.lean` — the `κ_{v,3}` per-edge identity

For every cusp `v` and every unit edge `k < fibreLen v 1` of the `κ_{v,3}`-longitude, the
`Ψ_M`-image of the cellular `1`-cell `edgeCell v 1 k` is an explicit combination of the two
halves of the cusp chart edge of the cube `edgeCube v 1 k`:

`Ψ_M(1_{edgeCell v 1 k}) = (edgeSign v 1 k * cpsi v) • (c1 (Yv k 1) (Yv k ½) - c1 (Yv k 0) (Yv k ½))`.

The proof has three inputs, all of which live in `BridgeSquare/Psi1Defs.lean` (`Psi1.*`) or in the
sibling modules of this file:

* `Psi1.rootCoeff_eq` — the atlas coefficient of the subdivision chain of the root face is the
  negated incidence `-qInc R U`;
* `Psi1L.eChi0_chart` and `Psi1U.eChi1_chart` — the two characteristic simplices of `edgeCell v 1 k`
  are the cusp chart simplices `[Yv k 0, Yv k ½]` and `[Yv k 1, Yv k ½]`;
* `Psi1.eBeta_eq` — the coefficient `eBeta = qInc R U0` is `edgeSign v 1 k * cpsi v`.
-/
import Mathlib
import Submission.Work.BridgeSquare.Psi1Defs
import Submission.Work.BridgeSquare.pieceDefs
import Submission.Work.BridgeSquare.CellChiADefs
import Submission.Work.BridgeSquare.Psi1L.eChi0_chart
import Submission.Work.BridgeSquare.Psi1U.eChi1_chart

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Work.Subdivision

set_option backward.isDefEq.respectTransparency false

namespace Work.BridgeSquare

noncomputable section

open Work.MbarHomology

/-! ## §1  The two characteristic simplices of the unit edge

`eFlag0` and `eFlag1` are the cones `[U0, R]`, `[U1, R]` of the two facets of the root face `R`
of the cell `edgeCell v 1 k`; they are the only `1`-simplices of the subdivision of `Q̄` whose
top vertex is `R`. -/

/-- A `1`-simplex is determined by its two vertices. -/
theorem psi1_Simplex_ext_fin2 {α : Type*} [Preorder α] {s t : Simplex α 1}
    (h0 : s 0 = t 0) (h1 : s (Fin.last 1) = t (Fin.last 1)) : s = t := by
  apply Simplex.ext
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
    subst hj
    simpa using h0
  · exact h1

theorem psi1_eFlag0_zero (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 1) :
    (Psi1.eFlag0 v k hk) (0 : Fin 2) = Psi1.eU0 v k := rfl

theorem psi1_eFlag1_zero (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 1) :
    (Psi1.eFlag1 v k hk) (0 : Fin 2) = Psi1.eU1 v k := rfl

theorem psi1_eFlag0_top (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 1) :
    Psi1.eFlag0 v k hk (Fin.last 1) = Mbar.rootCx 1 (edgeCell v 1 k) := by
  show (⟨faceAct (Psi1.esig v k) (edgeFace v 1 k)⟩ : QbarCell) = Mbar.rootCx 1 (edgeCell v 1 k)
  rw [Psi1.eRootI_eq_faceAct v k hk]
  rfl

theorem psi1_eFlag1_top (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 1) :
    Psi1.eFlag1 v k hk (Fin.last 1) = Mbar.rootCx 1 (edgeCell v 1 k) := by
  show (⟨faceAct (Psi1.esig v k) (edgeFace v 1 k)⟩ : QbarCell) = Mbar.rootCx 1 (edgeCell v 1 k)
  rw [Psi1.eRootI_eq_faceAct v k hk]
  rfl

/-! ## §2  The atlas coefficients of the two characteristic simplices -/

theorem psi1_rootCoeff_flag0 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 1) :
    Mbar.mbarAtlasOf.rootCoeff 1 (edgeCell v 1 k) (Psi1.eFlag0 v k hk)
      = -Psi1.eBeta v k := by
  rw [Psi1.rootCoeff_eq v k (Psi1.eFlag0 v k hk), if_pos (psi1_eFlag0_top v k hk)]
  show -(qInc (Psi1.eRootI v k) ((Psi1.eFlag0 v k hk) 0).idx) = -Psi1.eBeta v k
  rw [psi1_eFlag0_zero]
  rfl

theorem psi1_rootCoeff_flag1 (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 1) :
    Mbar.mbarAtlasOf.rootCoeff 1 (edgeCell v 1 k) (Psi1.eFlag1 v k hk)
      = -qInc (Psi1.eRootI v k) (Psi1.eU1 v k).idx := by
  rw [Psi1.rootCoeff_eq v k (Psi1.eFlag1 v k hk), if_pos (psi1_eFlag1_top v k hk)]
  show -(qInc (Psi1.eRootI v k) ((Psi1.eFlag1 v k hk) 0).idx)
    = -qInc (Psi1.eRootI v k) (Psi1.eU1 v k).idx
  rw [psi1_eFlag1_zero]

/-! ## §3  The expansion of `Ψ_M` on the basis cell -/

theorem PsiM_edge1_expand (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 1) :
    (PsiM.f 1) (Pi.single (edgeCell v 1 k) (1 : ℤ))
      = (-Psi1.eBeta v k) • Psi1.eChi0 v k hk + Psi1.eBeta v k • Psi1.eChi1 v k hk := by
  have hn' : (1 : ℕ) < 5 := by norm_num
  have hE := PsiM_f_piSingle_eq_sum 1 hn' (edgeCell v 1 k)
  rw [hE]
  -- the facets of the root face of the cell
  have hfacet : QbarCW.facets (Mbar.rootCx 1 (edgeCell v 1 k)) = {Psi1.eU0 v k, Psi1.eU1 v k} := by
    rw [show Mbar.rootCx 1 (edgeCell v 1 k) = Psi1.eRoot v k from rfl]
    exact Psi1.facets_eRoot v k hk
  have hf0 : Psi1.eU0 v k ∈ QbarCW.facets (Mbar.rootCx 1 (edgeCell v 1 k)) := by
    rw [hfacet]; exact Finset.mem_insert_self _ _
  have hf1 : Psi1.eU1 v k ∈ QbarCW.facets (Mbar.rootCx 1 (edgeCell v 1 k)) := by
    rw [hfacet]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have htop0 := psi1_eFlag0_top v k hk
  have htop1 := psi1_eFlag1_top v k hk
  -- any simplex whose top vertex is the root face is one of the two characteristic ones
  have htop_flag : ∀ s : Simplex QbarCW.Cell 1,
      s (Fin.last 1) = Mbar.rootCx 1 (edgeCell v 1 k) →
      s ∈ ({Psi1.eFlag0 v k hk, Psi1.eFlag1 v k hk} : Finset (Simplex QbarCW.Cell 1)) := by
    intro s hs
    have hlt : s 0 < Mbar.rootCx 1 (edgeCell v 1 k) := by
      rw [← hs]; exact s.strictMono (by decide +kernel)
    have hdim : QbarCW.dim (s 0) = 0 := by
      have h := QbarCW.dim_lt' hlt
      rw [Mbar.rootCx_dim 1 (edgeCell v 1 k)] at h
      omega
    have hmem : s 0 ∈ QbarCW.facets (Mbar.rootCx 1 (edgeCell v 1 k)) := by
      rw [QbarCW.mem_facets]
      exact ⟨hlt, by rw [Mbar.rootCx_dim 1 (edgeCell v 1 k), hdim]⟩
    rw [hfacet] at hmem
    rcases Finset.mem_insert.mp hmem with h0 | h1
    · refine Finset.mem_insert.mpr (Or.inl ?_)
      refine psi1_Simplex_ext_fin2 ?_ ?_
      · rw [h0, psi1_eFlag0_zero]
      · rw [hs, htop0]
    · refine Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr ?_))
      refine psi1_Simplex_ext_fin2 ?_ ?_
      · rw [Finset.mem_singleton.mp h1, psi1_eFlag1_zero]
      · rw [hs, htop1]
  -- the two characteristic simplices are distinct
  have hne : Psi1.eFlag0 v k hk ≠ Psi1.eFlag1 v k hk := by
    intro hcon
    exact Psi1.eU0_ne_eU1 v k hk (by rw [← psi1_eFlag0_zero v k hk, hcon, psi1_eFlag1_zero])
  -- the sum reduces to the two characteristic simplices
  have hsum : (∑ s : Simplex QbarCW.Cell 1, chiSummand 1 hn' (edgeCell v 1 k) s)
      = chiSummand 1 hn' (edgeCell v 1 k) (Psi1.eFlag0 v k hk)
        + chiSummand 1 hn' (edgeCell v 1 k) (Psi1.eFlag1 v k hk) := by
    have h1 : (∑ s : Simplex QbarCW.Cell 1, chiSummand 1 hn' (edgeCell v 1 k) s)
        = ∑ s ∈ ({Psi1.eFlag0 v k hk, Psi1.eFlag1 v k hk} : Finset (Simplex QbarCW.Cell 1)),
            chiSummand 1 hn' (edgeCell v 1 k) s :=
      (Finset.sum_subset (Finset.subset_univ _) (fun s _ hs => by
        by_cases htop : s (Fin.last 1) = Mbar.rootCx 1 (edgeCell v 1 k)
        · exact absurd (htop_flag s htop) hs
        · exact chiSummand_neg 1 hn' (edgeCell v 1 k) s htop)).symm
    rw [h1, Finset.sum_pair hne]
  rw [hsum]
  rw [chiSummand_pos 1 hn' (edgeCell v 1 k) (Psi1.eFlag0 v k hk) htop0,
    chiSummand_pos 1 hn' (edgeCell v 1 k) (Psi1.eFlag1 v k hk) htop1]
  rw [psi1_rootCoeff_flag0 v k hk, psi1_rootCoeff_flag1 v k hk]
  rw [show singGen (Mbar.chi 1 (Mbar.rootSimplex 1 hn' (edgeCell v 1 k) (Psi1.eFlag0 v k hk)))
        = Psi1.eChi0 v k hk from rfl,
      show singGen (Mbar.chi 1 (Mbar.rootSimplex 1 hn' (edgeCell v 1 k) (Psi1.eFlag1 v k hk)))
        = Psi1.eChi1 v k hk from rfl]
  -- the algebra of the coefficients
  have hq : qInc (Psi1.eRootI v k) (Psi1.eU1 v k).idx = -Psi1.eBeta v k := by
    rw [Psi1.qInc_eU1 v k hk]
    rfl
  rw [hq, neg_neg]
  -- The left-hand side carries the scalar action of the `Module ℤ` structure while the right-hand
  -- side carries the canonical `zsmul`; `int_smul_eq_zsmul` identifies the two.
  show (inferInstance : Module ℤ ↥((singCxFun.obj cMtop).X 1)).smul (-Psi1.eBeta v k)
        (Psi1.eChi0 v k hk)
      + (inferInstance : Module ℤ ↥((singCxFun.obj cMtop).X 1)).smul (Psi1.eBeta v k)
        (Psi1.eChi1 v k hk)
    = (-Psi1.eBeta v k) • Psi1.eChi0 v k hk + Psi1.eBeta v k • Psi1.eChi1 v k hk
  rw [int_smul_eq_zsmul (inferInstance : Module ℤ ↥((singCxFun.obj cMtop).X 1)),
    int_smul_eq_zsmul (inferInstance : Module ℤ ↥((singCxFun.obj cMtop).X 1))]

/-! ## §4  The per-edge identity -/

theorem psi1_psiM_edgeCell (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 1)
    (hc0 : Mbar.chi 1 (Psi1.eSimp0 v k hk)
      = cSimp v ![Yv v k 0, Yv v k (1/2)])
    (hc1 : Mbar.chi 1 (Psi1.eSimp1 v k hk)
      = cSimp v ![Yv v k 1, Yv v k (1/2)]) :
    (PsiM.f 1) (Pi.single (edgeCell v 1 k) (1 : ℤ))
      = (edgeSign v 1 k * cpsi v) •
          (c1 v (Yv v k 1) (Yv v k (1/2)) - c1 v (Yv v k 0) (Yv v k (1/2))) := by
  rw [PsiM_edge1_expand v k hk]
  have hc0' : Psi1.eChi0 v k hk = c1 v (Yv v k 0) (Yv v k (1/2)) := by
    show singGen (Mbar.chi 1 (Psi1.eSimp0 v k hk)) = _
    rw [hc0]
    rfl
  have hc1' : Psi1.eChi1 v k hk = c1 v (Yv v k 1) (Yv v k (1/2)) := by
    show singGen (Mbar.chi 1 (Psi1.eSimp1 v k hk)) = _
    rw [hc1]
    rfl
  rw [hc1', hc0', Psi1.eBeta_eq v k hk]
  rw [neg_zsmul, zsmul_sub, sub_eq_add_neg]
  abel

/-! ## §5  The per-edge identity, assembled from the two chart identifications -/

theorem PsiM_edgeCell_eq (v : Fin 5) (k : Fin 4) (hk : (k : ℕ) < Work.BridgeSquare.fibreLen v 1) :
    (Work.BridgeSquare.PsiM.f 1) (Pi.single (Work.BridgeSquare.edgeCell v 1 k) (1 : ℤ))
      = (Work.BridgeSquare.edgeSign v 1 k * Work.BridgeSquare.cpsi v) •
          (Work.BridgeSquare.c1 v (Work.BridgeSquare.Yv v k 1) (Work.BridgeSquare.Yv v k (1/2))
            - Work.BridgeSquare.c1 v (Work.BridgeSquare.Yv v k 0) (Work.BridgeSquare.Yv v k (1/2))) := by
  exact psi1_psiM_edgeCell v k hk (Psi1L.eChi0_chart v k hk) (Psi1U.eChi1_chart v k hk)

end

end Work.BridgeSquare
