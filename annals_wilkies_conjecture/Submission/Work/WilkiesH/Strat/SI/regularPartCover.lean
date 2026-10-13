import Mathlib
import Submission.Work.WilkiesH.Mfd.Defs
import Submission.Work.WilkiesH.Strat.Defs
import Submission.Work.WilkiesH.Strat.dimLE_iUnion_fin
import Submission.Work.WilkiesH.Strat.CellBand
import Submission.Work.WilkiesH.Strat.bandChart_of_cellBand
import Submission.Work.WilkiesH.Strat.SI.frontierThin
import Submission.Work.WilkiesH.Strat.poly_bound_rpc
import Submission.Work.WilkiesH.Strat.rp_aux

/-!
# The regular part of a semialgebraic `Ω`-set is complemented by a thin `Ω`-set

`Work.WilkiesH.Strat.SI.regularPartCover`: for every `F, n` there are a format `a` and a
two-variable polynomial `pm` such that for every `μ, D` and every semialgebraic `V ∈ S.Ω F D n`
of dimension `≤ μ` there is an `Ω`-set `Vlow ⊆ V` of dimension `≤ μ - 1` containing every
non-`μ`-regular point of `V`: outside `Vlow`, `V` is locally the graph of a continuous section
of a rank-`μ` coordinate projection (`Work.WilkiesH.IsGraphAt μ V x`).

The proof is the BNZ §2.3 stratification argument: a cylindrical decomposition of `ℝⁿ`
compatible with `V` (`SharpCD`); cells of band count `d ≤ μ - 1` are put into `Vlow`; for the
remaining cells the relative frontier `κ ∩ closure (V \ κ)` is covered by an `Ω`-set of
dimension `≤ μ - 1` (`SI.frontierThin`); a cell with band count `d ≥ μ` has `d = μ`
(the chart dimension is bounded by `DimLE V μ` through `RegAux.cell_chart_dim_le`), so a point
of `V` which is `V`-locally inside such a cell is a `μ`-regular point of `V`
(`RegAux.isGraphAt_of_chart`).
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Strat.SI

open WilkiesDesign WilkiesConjecture
open Work.WilkiesH

theorem regularPartCover {S : WilkiesDesign.SOMin} (hcd : S.SharpCD) :
    ∀ F n : ℕ, ∃ (a : ℕ) (pm : MvPolynomial (Fin 2) ℕ),
      ∀ (μ D : ℕ) (V : Set (Fin n → ℝ)),
        V ∈ S.Ω F D n → WilkiesConjecture.IsSemialgebraic V → WilkiesDesign.DimLE V μ →
        ∃ Vlow : Set (Fin n → ℝ),
          Vlow ∈ S.Ω a (MvPolynomial.eval ![(D : ℕ), (n + 1 : ℕ)] pm) n ∧
          Vlow ⊆ V ∧ WilkiesDesign.DimLE Vlow (μ - 1) ∧
          ∀ x : Fin n → ℝ, x ∈ V → x ∉ Vlow → Work.WilkiesH.IsGraphAt μ V x := by
  intro F n
  obtain ⟨a₁, b₁, c₁, H₁⟩ := hcd (F + 1) n
  obtain ⟨a₂, pm₂, H₂⟩ := frontierThin (S := S) hcd (max (F + 1) a₁) n
  obtain ⟨pm, hpm⟩ := Work.WilkiesH.Strat.poly_bound_rpc (b₁ + b₁) c₁ pm₂ n
  refine ⟨max (max (max a₁ a₂) F) (n + 6), pm, ?_⟩
  intro μ D V hV hVsem hVdim
  by_cases hthin : DimLE V (μ - 1)
  · -- `V` is already thin
    refine ⟨V, Work.WilG5.mem_mono hV _ _ (by omega) (by have := (hpm D).1; omega), subset_rfl,
      hthin, ?_⟩
    intro x hxV hx
    exact absurd hxV hx
  · -- the main case
    have hn0 : n ≠ 0 := by
      intro hn
      subst hn
      exact hthin (Dim.dimLE_mono (dimLE_top V) (Nat.zero_le _))
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    -- the cylindrical decomposition of `ℝ^{m+1}` compatible with `V`
    have hV' : V ∈ S.Ω (F + 1) D (m + 1) := Work.WilG5.mem_mono hV _ _ (by omega) le_rfl
    obtain ⟨CD, hcyl, hcomp, hcard, hmem⟩ := H₁ D 1 (fun _ : Fin 1 => V) (fun _ => hV')
    rw [WilkiesDesign.IsCylDecomp] at hcyl
    -- the cells contained in `V`, enumerated
    let CDv : Finset (Set (Fin (m + 1) → ℝ)) := CD.filter (fun κ => κ ⊆ V)
    let E : Fin CDv.card ≃ ↥CDv :=
      (finCongr (Fintype.card_coe CDv).symm).trans (Fintype.equivFin ↥CDv).symm
    let e : Fin CDv.card → Set (Fin (m + 1) → ℝ) := fun j => (E j).1
    have he_mem : ∀ j, e j ∈ CDv := fun j => (E j).2
    have he_cd : ∀ j, e j ∈ CD := fun j => (Finset.mem_filter.mp (he_mem j)).1
    have he_sub : ∀ j, e j ⊆ V := fun j => (Finset.mem_filter.mp (he_mem j)).2
    have he_surj : ∀ κ ∈ CDv, ∃ j, e j = κ := fun κ hκ => ⟨E.symm ⟨κ, hκ⟩, by simp [e]⟩
    have hcell : ∀ j, WilkiesDesign.IsCell (m + 1) (e j) := fun j => (hcyl.1 _ (he_cd j)).1
    have hne : ∀ j, (e j).Nonempty := fun j => (hcyl.1 _ (he_cd j)).2
    have hΩe : ∀ j, e j ∈ S.Ω a₁ (c₁.eval D) (m + 1) :=
      fun j => Work.WilG5.mem_mono (hmem _ (he_cd j)) _ _ (by omega) le_rfl
    have hcover : ∀ x : Fin (m + 1) → ℝ, ∃ κ ∈ CD, x ∈ κ := hcyl.2.2.1
    -- the band counts of the cells
    have hex : ∀ j, ∃ d : ℕ, CellBand (m + 1) (e j) d := fun j =>
      exists_cellBand_of_isCell (hcell j)
    let dd : Fin CDv.card → ℕ := fun j => Classical.choose (hex j)
    have hd : ∀ j, CellBand (m + 1) (e j) (dd j) := fun j => Classical.choose_spec (hex j)
    -- the format and degree common to all the pieces
    have hV'' : V ∈ S.Ω (max (F + 1) a₁) D (m + 1) :=
      Work.WilG5.mem_mono hV _ _ (le_trans (Nat.le_succ F) (le_max_left _ _)) le_rfl
    have hΩe' : ∀ j, e j ∈ S.Ω (max (F + 1) a₁) (c₁.eval D) (m + 1) :=
      fun j => Work.WilG5.mem_mono (hΩe j) _ _ (le_max_right _ _) le_rfl
    -- the cell-frontier covers
    let W : Fin CDv.card → Set (Fin (m + 1) → ℝ) := fun j =>
      Classical.choose (H₂ μ (c₁.eval D) D V (e j) hV'' hVsem hVdim (hΩe' j) (hcell j)
        (hne j) (he_sub j))
    have hWspec : ∀ j,
        W j ∈ S.Ω a₂ (MvPolynomial.eval ![((c₁.eval D) + D : ℕ), (m + 1 + 1 : ℕ)] pm₂)
            (m + 1) ∧
          W j ⊆ e j ∧ WilkiesDesign.DimLE (W j) (μ - 1) ∧
          e j ∩ closure (V \ e j) ⊆ W j := fun j =>
      Classical.choose_spec (H₂ μ (c₁.eval D) D V (e j) hV'' hVsem hVdim (hΩe' j) (hcell j)
        (hne j) (he_sub j))
    -- the two families of pieces
    let A : Fin CDv.card → Set (Fin (m + 1) → ℝ) := fun j => if dd j ≤ μ - 1 then e j else ∅
    let B : Fin CDv.card → Set (Fin (m + 1) → ℝ) := fun j => if dd j ≤ μ - 1 then ∅ else W j
    set FT : ℕ := max (max a₁ a₂) ((m + 1) + 6) with hFT
    set DG : ℕ := 4 + Polynomial.eval D c₁ +
      MvPolynomial.eval ![Polynomial.eval D c₁ + D, (m + 1 + 1 : ℕ)] pm₂ with hDG
    have hdeg1 : Polynomial.eval D c₁ ≤ DG := by rw [hDG]; omega
    have hdeg2 : MvPolynomial.eval ![Polynomial.eval D c₁ + D, (m + 1 + 1 : ℕ)] pm₂ ≤ DG := by
      rw [hDG]; omega
    have hdeg3 : 4 ≤ DG := by rw [hDG]; omega
    have hAΩ : ∀ j, A j ∈ S.Ω FT DG (m + 1) := by
      intro j
      by_cases hj : dd j ≤ μ - 1
      · have hAj : A j = e j := by
          show (if dd j ≤ μ - 1 then e j else (∅ : Set (Fin (m + 1) → ℝ))) = e j
          rw [if_pos hj]
        rw [hAj]
        exact Work.WilG5.mem_mono (hΩe j) _ _ (by omega) hdeg1
      · have hAj : A j = (∅ : Set (Fin (m + 1) → ℝ)) := by
          show (if dd j ≤ μ - 1 then e j else (∅ : Set (Fin (m + 1) → ℝ))) = ∅
          rw [if_neg hj]
        rw [hAj]
        exact Work.WilG5.mem_mono (Work.WilG5.empty_mem (S := S) (n := m + 1)) _ _
          (by omega) hdeg3
    have hBΩ : ∀ j, B j ∈ S.Ω FT DG (m + 1) := by
      intro j
      by_cases hj : dd j ≤ μ - 1
      · have hBj : B j = (∅ : Set (Fin (m + 1) → ℝ)) := by
          show (if dd j ≤ μ - 1 then (∅ : Set (Fin (m + 1) → ℝ)) else W j) = ∅
          rw [if_pos hj]
        rw [hBj]
        exact Work.WilG5.mem_mono (Work.WilG5.empty_mem (S := S) (n := m + 1)) _ _
          (by omega) hdeg3
      · have hBj : B j = W j := by
          show (if dd j ≤ μ - 1 then (∅ : Set (Fin (m + 1) → ℝ)) else W j) = W j
          rw [if_neg hj]
        rw [hBj]
        exact Work.WilG5.mem_mono (hWspec j).1 _ _ (by omega) hdeg2
    have hAdim : ∀ j, WilkiesDesign.DimLE (A j) (μ - 1) := by
      intro j
      by_cases hj : dd j ≤ μ - 1
      · have hAj : A j = e j := by
          show (if dd j ≤ μ - 1 then e j else (∅ : Set (Fin (m + 1) → ℝ))) = e j
          rw [if_pos hj]
        rw [hAj]
        exact Dim.dimLE_mono (RegAux.cellBand_dimLE (S := S) hcd (hd j) (hΩe j)) hj
      · have hAj : A j = (∅ : Set (Fin (m + 1) → ℝ)) := by
          show (if dd j ≤ μ - 1 then e j else (∅ : Set (Fin (m + 1) → ℝ))) = ∅
          rw [if_neg hj]
        rw [hAj]
        intro e'
        rw [Set.image_empty, interior_empty]
    have hBdim : ∀ j, WilkiesDesign.DimLE (B j) (μ - 1) := by
      intro j
      by_cases hj : dd j ≤ μ - 1
      · have hBj : B j = (∅ : Set (Fin (m + 1) → ℝ)) := by
          show (if dd j ≤ μ - 1 then (∅ : Set (Fin (m + 1) → ℝ)) else W j) = ∅
          rw [if_pos hj]
        rw [hBj]
        intro e'
        rw [Set.image_empty, interior_empty]
      · have hBj : B j = W j := by
          show (if dd j ≤ μ - 1 then (∅ : Set (Fin (m + 1) → ℝ)) else W j) = W j
          rw [if_neg hj]
        rw [hBj]
        exact (hWspec j).2.2.1
    -- the union and its `Ω`-membership
    have hUA : (⋃ j, A j) ∈ S.Ω FT (CDv.card * DG) (m + 1) := by
      have h := S.union (fun _ : Fin CDv.card => DG) A hAΩ
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h
    have hUB : (⋃ j, B j) ∈ S.Ω FT (CDv.card * DG) (m + 1) := by
      have h := S.union (fun _ : Fin CDv.card => DG) B hBΩ
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h
    have hUmem : (⋃ j, A j) ∪ (⋃ j, B j) ∈ S.Ω FT (2 * (CDv.card * DG)) (m + 1) := by
      have h := S.union (fun _ : Fin 2 => CDv.card * DG)
        (fun i : Fin 2 => ![⋃ j, A j, ⋃ j, B j] i)
        (by intro i; fin_cases i <;> simpa using (by first | exact hUA | exact hUB))
      rw [show (⋃ i : Fin 2, (![⋃ j, A j, ⋃ j, B j] : Fin 2 → Set (Fin (m + 1) → ℝ)) i) =
          (⋃ j, A j) ∪ (⋃ j, B j) from by
        ext y; simp [Fin.exists_fin_two]] at h
      simpa [Fin.sum_univ_two, two_mul] using h
    -- the degree bound
    have hcardCDv : CDv.card ≤ CD.card := Finset.card_filter_le _ _
    have hcard : CDv.card ≤ MvPolynomial.eval ![D, 1] b₁ := le_trans hcardCDv hcard
    have h5 : DG ≤ 4 + Polynomial.eval D c₁ +
        MvPolynomial.eval ![Polynomial.eval D c₁ + D, m + 1 + 1] pm₂ := by
      rw [hDG]
    have hone : CDv.card * DG ≤ MvPolynomial.eval ![D, 1] b₁ *
        (4 + Polynomial.eval D c₁ +
          MvPolynomial.eval ![Polynomial.eval D c₁ + D, m + 1 + 1] pm₂) :=
      Nat.mul_le_mul hcard h5
    have hkey : 2 * (CDv.card * DG) ≤ (b₁ + b₁).eval ![D, 1] *
        (4 + Polynomial.eval D c₁ +
          MvPolynomial.eval ![Polynomial.eval D c₁ + D, m + 1 + 1] pm₂) := by
      rw [MvPolynomial.eval_add, add_mul]
      calc 2 * (CDv.card * DG) = CDv.card * DG + CDv.card * DG := by ring
        _ ≤ MvPolynomial.eval ![D, 1] b₁ *
              (4 + Polynomial.eval D c₁ +
                MvPolynomial.eval ![Polynomial.eval D c₁ + D, m + 1 + 1] pm₂) +
            MvPolynomial.eval ![D, 1] b₁ *
              (4 + Polynomial.eval D c₁ +
                MvPolynomial.eval ![Polynomial.eval D c₁ + D, m + 1 + 1] pm₂) :=
            add_le_add hone hone
    have hdeg : 2 * (CDv.card * DG) ≤ MvPolynomial.eval ![D, m + 1 + 1] pm :=
      le_trans hkey (hpm D).2
    refine ⟨(⋃ j, A j) ∪ (⋃ j, B j), Work.WilG5.mem_mono hUmem _ _ (by omega) hdeg, ?_, ?_, ?_⟩
    · -- contained in `V`
      intro y hy
      rcases hy with hy | hy
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
        by_cases hjd : dd j ≤ μ - 1
        · have hAj : A j = e j := by
            show (if dd j ≤ μ - 1 then e j else (∅ : Set (Fin (m + 1) → ℝ))) = e j
            rw [if_pos hjd]
          rw [hAj] at hj
          exact he_sub j hj
        · have hAj : A j = (∅ : Set (Fin (m + 1) → ℝ)) := by
            show (if dd j ≤ μ - 1 then e j else (∅ : Set (Fin (m + 1) → ℝ))) = ∅
            rw [if_neg hjd]
          rw [hAj] at hj
          exact absurd hj (Set.notMem_empty y)
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
        by_cases hjd : dd j ≤ μ - 1
        · have hBj : B j = (∅ : Set (Fin (m + 1) → ℝ)) := by
            show (if dd j ≤ μ - 1 then (∅ : Set (Fin (m + 1) → ℝ)) else W j) = ∅
            rw [if_pos hjd]
          rw [hBj] at hj
          exact absurd hj (Set.notMem_empty y)
        · have hBj : B j = W j := by
            show (if dd j ≤ μ - 1 then (∅ : Set (Fin (m + 1) → ℝ)) else W j) = W j
            rw [if_neg hjd]
          rw [hBj] at hj
          exact he_sub j ((hWspec j).2.1 hj)
    · -- the dimension bound
      have hdA : WilkiesDesign.DimLE (⋃ j, A j) (μ - 1) :=
        dimLE_iUnion_fin (S := S) hcd A hAΩ hAdim
      have hdB : WilkiesDesign.DimLE (⋃ j, B j) (μ - 1) :=
        dimLE_iUnion_fin (S := S) hcd B hBΩ hBdim
      have h2 := dimLE_iUnion_fin (S := S) hcd (fun i : Fin 2 => ![⋃ j, A j, ⋃ j, B j] i)
        (fun i => by fin_cases i <;> simpa using (by first | exact hUA | exact hUB))
        (fun i => by fin_cases i <;> simpa using (by first | exact hdA | exact hdB))
      have hset : (⋃ i : Fin 2, (![⋃ j, A j, ⋃ j, B j] : Fin 2 → Set (Fin (m + 1) → ℝ)) i) =
          (⋃ j, A j) ∪ (⋃ j, B j) := by
        ext y; simp [Fin.exists_fin_two]
      rw [hset] at h2
      exact h2
    · -- regularity outside the cover
      intro x hxV hxlow
      obtain ⟨κ, hκCD, hxκ⟩ := hcover x
      have hκV : κ ⊆ V := by
        rcases hcomp 0 κ hκCD with h | h
        · simpa using h
        · exact absurd hxV (fun hxV => Set.disjoint_left.mp h hxκ hxV)
      obtain ⟨j, hj⟩ := he_surj κ (Finset.mem_filter.mpr ⟨hκCD, hκV⟩)
      have hxj : x ∈ e j := by rw [hj]; exact hxκ
      have hxA : x ∉ A j := fun hx => hxlow (Or.inl (Set.mem_iUnion.mpr ⟨j, hx⟩))
      have hxB : x ∉ B j := fun hx => hxlow (Or.inr (Set.mem_iUnion.mpr ⟨j, hx⟩))
      have hfat : ¬ (dd j ≤ μ - 1) := by
        intro hle
        have hAj : A j = e j := by
          show (if dd j ≤ μ - 1 then e j else (∅ : Set (Fin (m + 1) → ℝ))) = e j
          rw [if_pos hle]
        exact hxA (by rw [hAj]; exact hxj)
      have hxW : x ∉ W j := by
        intro hx
        have hBj : B j = W j := by
          show (if dd j ≤ μ - 1 then (∅ : Set (Fin (m + 1) → ℝ)) else W j) = W j
          rw [if_neg hfat]
        exact hxB (by rw [hBj]; exact hx)
      -- `V` is locally inside the cell at `x`
      have hcl : x ∉ closure (V \ e j) := by
        intro hcl
        exact hxW ((hWspec j).2.2.2 ⟨hxj, hcl⟩)
      have hUo : IsOpen ((closure (V \ e j))ᶜ) := isClosed_closure.isOpen_compl
      have hxU : x ∈ ((closure (V \ e j))ᶜ) := hcl
      have hUV : ((closure (V \ e j))ᶜ) ∩ V ⊆ e j := by
        intro y hy
        by_contra hyj
        exact hy.1 (subset_closure ⟨hy.2, hyj⟩)
      -- the chart of the cell
      obtain ⟨ec, Φc, hopen, hcont, hleft, hright⟩ := bandChart_of_cellBand (hd j)
      have hΦW : Φc '' Cell.ProjE ec (e j) = e j := by
        refine Set.Subset.antisymm ?_ ?_
        · rintro y ⟨u, hu, rfl⟩
          obtain ⟨z, hz, hzu⟩ := hu
          rw [← hzu, hleft z hz]
          exact hz
        · intro y hy
          exact ⟨y ∘ ec, ⟨y, hy, rfl⟩, hleft y hy⟩
      have hneU : (Cell.ProjE ec (e j)).Nonempty := (hne j).image (fun y => y ∘ ec)
      have hdle : dd j ≤ μ := RegAux.cell_chart_dim_le (he_sub j) hVdim ec hopen hneU
      have hdge : μ ≤ dd j := by omega
      have hdeq : dd j = μ := le_antisymm hdle hdge
      exact RegAux.isGraphAt_of_chart hdeq ec hopen Φc hcont hΦW (fun u hu => hright u hu)
        (he_sub j) hxj hUo hxU hUV

end Work.WilkiesH.Strat.SI
