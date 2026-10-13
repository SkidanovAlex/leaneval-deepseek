import Mathlib
import Submission.Work.WilE7.DecompDefs
import Submission.Work.WilE7.SheetData.multiStrata_cellsX_aux
import Submission.Work.WilE7.SheetData.graphCellSubPfX
import Submission.Work.WilE7.SheetData.aboveBandSubPfX
import Submission.Work.WilE7.SheetData.belowBandSubPfX
import Submission.Work.WilE7.CoreStep.subPf_inter
import Submission.Work.WilE7.SheetData.bandCell_bd
import Submission.Work.WilE7.SheetData.belowBandX
import Submission.Work.WilE7.SheetData.aboveBandX
import Submission.Work.WilE7.SheetData.graphCellStar_piece
import Submission.Work.WilE7.faceCell_bd
import Submission.Work.WilE7.faceCell_star
import Submission.Work.WilE7.cfs_graph_compat
import Submission.Work.WilE7.cylOpenBand
import Submission.Work.WilE7.sheetCells_cyl_proved

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Work.WilE7.SheetData

open WilkiesDesign WilkiesDesign.E
open Work.WilE7 (cfs lvl gr bd cyl mem_cfs lvl_zero lvl_last lvl_succ strictMono_lvl)

/-! ## The main theorem -/

theorem multiStrata_cellsX (F : ℕ) :
    ∃ (A : ℕ) (Cb : Polynomial ℕ),
      ∀ (p m r : ℕ) (X : Fin r → WilkiesDesign.E.SemiPf (p + (m + 1)))
        (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ)
        (hu₀ : u₀ ∈ Z.set)
        (C : Set (Fin p → ℝ))
        (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1))
          (connectedComponentIn Z.set u₀))
        (hCpf : WilkiesDesign.E.SubPf p C) (hCell : WilkiesDesign.IsCell p C)
        (k : Fin r → ℕ) (hk : ∀ t, 0 < k t)
        (s : ∀ t : Fin r, Fin (k t) → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
        (hcont : ∀ (t : Fin r) (j : Fin (k t)), ContinuousOn (s t j) C)
        (hinj : ∀ (t : Fin r) (x : Fin p → ℝ), x ∈ C →
          Function.Injective fun j : Fin (k t) => s t j x)
        (hsub : ∀ (t : Fin r) (j : Fin (k t)), ∀ x ∈ C, Fin.append x (s t j x) ∈ (X t).set)
        (hcov : ∀ (t : Fin r) (z : Fin (p + (m + 1)) → ℝ), z ∈ (X t).set →
          WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
          ∃ j : Fin (k t), s t j (WilkiesDesign.E.projFirst p (m + 1) z) =
            WilkiesDesign.E.projSnd p (m + 1) z)
        (hmono : ∀ (t : Fin r) (x : Fin p → ℝ), x ∈ C →
          Monotone fun j : Fin (k t) => (s t j x) (Fin.last m))
        (K : ℕ) (T : Fin K → (Fin p → ℝ) → ℝ)
        (hTcont : ∀ i, ContinuousOn (T i) C)
        (hTmono : ∀ x ∈ C, StrictMono fun i : Fin K => T i x)
        (hbnd : ∀ x ∈ C, ∀ i : Fin K, |T i x| < 1)
        (hcovT : ∀ (t : Fin r) (j : Fin (k t)), ∃ i : Fin K,
          ∀ x ∈ C, T i x = (s t j x) (Fin.last m))
        (hminT : ∀ hK : 0 < K, ∃ t : Fin r,
          ∀ x ∈ C, T ⟨0, hK⟩ x = (s t ⟨0, hk t⟩ x) (Fin.last m))
        (hmaxT : ∀ hK : 0 < K, ∃ t : Fin r,
          ∀ x ∈ C, T ⟨K - 1, Nat.sub_lt hK (by norm_num)⟩ x =
            (s t ⟨k t - 1, Nat.sub_lt (hk t) (by norm_num)⟩ x) (Fin.last m))
        (D : ℕ),
        (∀ t, (X t).fmt ≤ F ∧ (X t).deg ≤ D) → Z.fmt ≤ F → Z.deg ≤ D →
        ∃ C' : Finset (Set (Fin (p + 1) → ℝ)),
          WilkiesDesign.E.IsCylDecompOn (p + 1) (cyl C) C' ∧
          C'.card ≤ 2 * K + 3 ∧
          (∀ κ ∈ C', (∃ t : Fin r, κ ⊆ ⋃ j : Fin (k t),
              {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
                y (Fin.last p) = (s t j (Fin.init y)) (Fin.last m)}) ∨
            (∀ t : Fin r, Disjoint κ (⋃ j : Fin (k t),
              {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
                y (Fin.last p) = (s t j (Fin.init y)) (Fin.last m)}))) ∧
          (∀ κ ∈ C', (∃ P : WilkiesDesign.E.StarPiece (p + 1),
              P.set = κ ∧ P.X.fmt ≤ A ∧ P.X.deg ≤ Cb.eval D) ∧
            WilkiesDesign.E.SubPf (p + 1) κ) := by
  classical
  obtain ⟨Ag, Cg, hGraphBd⟩ := graphCellStarX F
  obtain ⟨Abd, Cbd, hBandBd⟩ := bandCell_bd F
  obtain ⟨Af, Cf, hFaceBd⟩ := faceCell_bd F
  obtain ⟨Al, Cl, hBelowBd⟩ := belowBandX F
  obtain ⟨Au, Cu, hAboveBd⟩ := aboveBandX F
  obtain ⟨Aop, Cop, hOpenBd⟩ := cylOpenBand F
  have hCbEval : ∀ D' : ℕ, (Cg + Cbd + Cf + Cl + Cu + Cop).eval D'
      = Cg.eval D' + Cbd.eval D' + Cf.eval D' + Cl.eval D' + Cu.eval D' + Cop.eval D' :=
    fun D' => by simp only [Polynomial.eval_add]
  refine ⟨Ag + Abd + Af + Al + Au + Aop, Cg + Cbd + Cf + Cl + Cu + Cop, ?_⟩
  intro p m r X Z u₀ hu₀ C hC hCpf hCell k hk s hcont hinj hsub hcov hmono K T hTcont hTmono
    hbnd hcovT hminT hmaxT D hS hZF hZD
  -- the base cell is nonempty
  have hCne : C.Nonempty :=
    ⟨projFirst p (m + 1) u₀, by rw [hC]; exact ⟨u₀, mem_connectedComponentIn hu₀, rfl⟩⟩
  -- the *used* levels of `T`: those that occur as the last fibre coordinate of a sheet
  let I : Finset (Fin K) := Finset.univ.filter fun i =>
    ∃ (t : Fin r) (j : Fin (k t)), ∀ x : Fin p → ℝ, x ∈ C → T i x = (s t j x) (Fin.last m)
  have hIex : ∀ i ∈ I, ∃ (t : Fin r) (j : Fin (k t)),
      ∀ x : Fin p → ℝ, x ∈ C → T i x = (s t j x) (Fin.last m) :=
    fun i hi => (Finset.mem_filter.mp hi).2
  have hIused : ∀ (t : Fin r) (j : Fin (k t)), ∃ i ∈ I,
      ∀ x : Fin p → ℝ, x ∈ C → T i x = (s t j x) (Fin.last m) := by
    intro t j
    obtain ⟨i, hi⟩ := hcovT t j
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, t, j, hi⟩, hi⟩
  -- the level family restricted to the used indices, in increasing order
  let e : Fin I.card ≃o ↥I := I.orderIsoOfFin rfl
  let TT : Fin I.card → (Fin p → ℝ) → ℝ := fun i x => T (e i : Fin K) x
  have hTTcont : ∀ i : Fin I.card, ContinuousOn (TT i) C := fun i => hTcont (e i)
  have hTTmono : ∀ x ∈ C, StrictMono fun i : Fin I.card => TT i x := fun x hx i i' hii =>
    hTmono x hx (e.strictMono hii)
  have hTTbnd : ∀ x ∈ C, ∀ i : Fin I.card, |TT i x| < 1 := fun x hx i => hbnd x hx (e i)
  have hIcard : I.card ≤ K := by simpa using Finset.card_le_univ I
  -- each used level is the last fibre coordinate of a sheet
  have hwit : ∀ ii : Fin I.card, ∃ (t : Fin r) (j : Fin (k t)),
      ∀ x ∈ C, TT ii x = (s t j x) (Fin.last m) := by
    intro ii
    obtain ⟨t, j, hw⟩ := hIex (e ii : Fin K) (e ii).2
    exact ⟨t, j, fun x hx => hw x hx⟩
  -- the lowest used level is the level of the first sheet of some stratum
  have hminLevel : ∀ (hpos : 0 < I.card), ∃ (t : Fin r),
      ∀ x ∈ C, TT ⟨0, hpos⟩ x = (s t ⟨0, hk t⟩ x) (Fin.last m) := by
    intro hpos
    have hK : 0 < K := by omega
    obtain ⟨t, hw⟩ := hminT hK
    have hmem0 : (⟨0, hK⟩ : Fin K) ∈ I :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ⟨0, hk t⟩, hw⟩
    have heq : (e ⟨0, hpos⟩ : Fin K) = ⟨0, hK⟩ := by
      apply Fin.ext
      have hminI : (e ⟨0, hpos⟩ : Fin K) ≤ ⟨0, hK⟩ := by
        have h0a : (⟨0, hpos⟩ : Fin I.card) ≤ e.symm (⟨⟨0, hK⟩, hmem0⟩ : ↥I) := by
          rw [Fin.le_iff_val_le_val]; exact Nat.zero_le _
        have hle := e.le_iff_le.mpr h0a
        rwa [e.apply_symm_apply] at hle
      have hv : (e ⟨0, hpos⟩ : Fin K).val = 0 :=
        Nat.le_zero.mp (Fin.le_iff_val_le_val.mp hminI)
      show (e ⟨0, hpos⟩ : Fin K).val = (⟨0, hK⟩ : Fin K).val
      rw [hv]
    refine ⟨t, fun x hx => ?_⟩
    calc TT ⟨0, hpos⟩ x = T (e ⟨0, hpos⟩ : Fin K) x := rfl
      _ = T ⟨0, hK⟩ x := by rw [heq]
      _ = (s t ⟨0, hk t⟩ x) (Fin.last m) := hw x hx
  -- the highest used level is the level of the last sheet of some stratum
  have hmaxLevel : ∀ (hpos : 0 < I.card), ∃ (t : Fin r),
      ∀ x ∈ C, TT ⟨I.card - 1, Nat.sub_lt hpos (by norm_num)⟩ x
        = (s t ⟨k t - 1, Nat.sub_lt (hk t) (by norm_num)⟩ x) (Fin.last m) := by
    intro hpos
    have hK : 0 < K := by omega
    obtain ⟨t, hw⟩ := hmaxT hK
    let hltI : I.card - 1 < I.card := Nat.sub_lt hpos (by norm_num)
    let hltK : K - 1 < K := Nat.sub_lt hK (by norm_num)
    have htop : (⟨K - 1, hltK⟩ : Fin K) ∈ I :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ⟨k t - 1, Nat.sub_lt (hk t) (by norm_num)⟩, hw⟩
    have heq : (e ⟨I.card - 1, hltI⟩ : Fin K) = ⟨K - 1, hltK⟩ := by
      apply le_antisymm
      · rw [Fin.le_iff_val_le_val]
        show (e ⟨I.card - 1, hltI⟩ : Fin K).val ≤ K - 1
        have := (e ⟨I.card - 1, hltI⟩ : Fin K).isLt
        omega
      · have hmaxI : ∀ i ∈ I, i ≤ (e ⟨I.card - 1, hltI⟩ : Fin K) := by
          intro i hi
          have ha : e.symm (⟨i, hi⟩ : ↥I) ≤ (⟨I.card - 1, hltI⟩ : Fin I.card) := by
            rw [Fin.le_iff_val_le_val]
            show (e.symm (⟨i, hi⟩ : ↥I)).val ≤ I.card - 1
            have := (e.symm (⟨i, hi⟩ : ↥I)).isLt
            omega
          have h := e.le_iff_le.mpr ha
          rwa [e.apply_symm_apply] at h
        exact hmaxI ⟨K - 1, hltK⟩ htop
    refine ⟨t, fun x hx => ?_⟩
    calc TT ⟨I.card - 1, Nat.sub_lt hpos (by norm_num)⟩ x
          = T (e ⟨I.card - 1, hltI⟩ : Fin K) x := rfl
      _ = T ⟨K - 1, hltK⟩ x := by rw [heq]
      _ = (s t ⟨k t - 1, Nat.sub_lt (hk t) (by norm_num)⟩ x) (Fin.last m) := hw x hx
  -- the decomposition into graphs and bands of the used levels
  obtain ⟨hdec, hcarddec⟩ :=
    cfs_isCylDecompOn (n := p) (q := I.card) hCell hCne hTTcont hTTmono hTTbnd
  refine ⟨cfs C TT, hdec, le_trans hcarddec (by omega), ?_, ?_⟩
  · -- compatibility with the graph unions of the strata
    intro κ hκ
    rw [mem_cfs] at hκ
    rcases hκ with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · -- graph cell of the level `lvl TT · i`
      by_cases hz : i.val = 0
      · -- the bottom face `y = -1`
        right
        intro t
        rw [Set.disjoint_left]
        intro y hy hyG
        rw [gr, Set.mem_ofPred_eq] at hy
        rw [Set.mem_iUnion] at hyG
        obtain ⟨j, hyj⟩ := hyG
        rw [Set.mem_ofPred_eq] at hyj
        obtain ⟨i'', hi''I, hi''eq⟩ := hIused t j
        obtain ⟨jj, hjj⟩ : ∃ jj : Fin I.card, (e jj : Fin K) = i'' :=
          ⟨e.symm ⟨i'', hi''I⟩, congrArg Subtype.val (e.apply_symm_apply ⟨i'', hi''I⟩)⟩
        have hidx : i = (0 : Fin (I.card + 2)) := Fin.ext hz
        have hlow : y (Fin.last p) = -1 := by rw [hy.2, hidx, lvl_zero]
        have h2 : y (Fin.last p) = TT jj (Fin.init y) := by
          have h3 : (s t j (Fin.init y)) (Fin.last m) = TT jj (Fin.init y) := by
            rw [show TT jj (Fin.init y) = T (e jj : Fin K) (Fin.init y) from rfl, hjj]
            exact (hi''eq (Fin.init y) hy.1).symm
          rw [hyj.2, h3]
        have hsm := strictMono_lvl (hTTmono (Fin.init y) hy.1) (hTTbnd (Fin.init y) hy.1)
        have heq : lvl TT (Fin.init y) i = lvl TT (Fin.init y) (Fin.succ (Fin.castSucc jj)) := by
          rw [hidx, lvl_zero, lvl_succ]
          exact hlow.symm.trans h2
        have hv := congrArg Fin.val (hsm.injective heq)
        simp only [Fin.val_succ, Fin.val_castSucc] at hv
        omega
      · by_cases htop : i.val = I.card + 1
        · -- the top face `y = 1`
          right
          intro t
          rw [Set.disjoint_left]
          intro y hy hyG
          rw [gr, Set.mem_ofPred_eq] at hy
          rw [Set.mem_iUnion] at hyG
          obtain ⟨j, hyj⟩ := hyG
          rw [Set.mem_ofPred_eq] at hyj
          obtain ⟨i'', hi''I, hi''eq⟩ := hIused t j
          obtain ⟨jj, hjj⟩ : ∃ jj : Fin I.card, (e jj : Fin K) = i'' :=
            ⟨e.symm ⟨i'', hi''I⟩, congrArg Subtype.val (e.apply_symm_apply ⟨i'', hi''I⟩)⟩
          have hidx : i = Fin.last (I.card + 1) := Fin.ext (by rw [Fin.val_last]; exact htop)
          have hup : y (Fin.last p) = 1 := by rw [hy.2, hidx, lvl_last]
          have h2 : y (Fin.last p) = TT jj (Fin.init y) := by
            have h3 : (s t j (Fin.init y)) (Fin.last m) = TT jj (Fin.init y) := by
              rw [show TT jj (Fin.init y) = T (e jj : Fin K) (Fin.init y) from rfl, hjj]
              exact (hi''eq (Fin.init y) hy.1).symm
            rw [hyj.2, h3]
          have hsm := strictMono_lvl (hTTmono (Fin.init y) hy.1) (hTTbnd (Fin.init y) hy.1)
          have heq : lvl TT (Fin.init y) i =
              lvl TT (Fin.init y) (Fin.succ (Fin.castSucc jj)) := by
            rw [hidx, lvl_last, lvl_succ]
            exact hup.symm.trans h2
          have hv := congrArg Fin.val (hsm.injective heq)
          simp only [Fin.val_succ, Fin.val_castSucc] at hv
          omega
        · -- the graph of the used level `TT jj`
          have hipos : 0 < i.val := Nat.pos_of_ne_zero hz
          let jj : Fin I.card := ⟨i.val - 1, by omega⟩
          have hij : i = Fin.succ (Fin.castSucc jj) := Fin.ext (by
            show i.val = jj.val + 1
            simp only [jj]
            omega)
          obtain ⟨t, j, hw⟩ := hwit jj
          left
          refine ⟨t, ?_⟩
          intro y hy
          rw [gr, Set.mem_ofPred_eq] at hy
          refine Set.mem_iUnion.mpr ⟨j, ?_⟩
          rw [Set.mem_ofPred_eq]
          refine ⟨hy.1, ?_⟩
          rw [hy.2, hij, lvl_succ]
          exact hw (Fin.init y) hy.1
    · -- band cells: disjoint from every stratum's graph union
      right
      intro t
      rw [Set.disjoint_left]
      intro y hy hyG
      rw [bd, Set.mem_ofPred_eq] at hy
      obtain ⟨hyC, hy1, hy2⟩ := hy
      rw [Set.mem_iUnion] at hyG
      obtain ⟨j, hyj⟩ := hyG
      rw [Set.mem_ofPred_eq] at hyj
      obtain ⟨i'', hi''I, hi''eq⟩ := hIused t j
      obtain ⟨jj, hjj⟩ : ∃ jj : Fin I.card, (e jj : Fin K) = i'' :=
        ⟨e.symm ⟨i'', hi''I⟩, congrArg Subtype.val (e.apply_symm_apply ⟨i'', hi''I⟩)⟩
      have hsm := strictMono_lvl (hTTmono (Fin.init y) hyC) (hTTbnd (Fin.init y) hyC)
      have heq : lvl TT (Fin.init y) (Fin.succ (Fin.castSucc jj)) = y (Fin.last p) := by
        rw [lvl_succ]
        rw [show TT jj (Fin.init y) = T (e jj : Fin K) (Fin.init y) from rfl]
        rw [hjj, hi''eq (Fin.init y) hyC]
        exact hyj.2.symm
      have h1 : Fin.castSucc i < Fin.succ (Fin.castSucc jj) :=
        hsm.lt_iff_lt.mp (by rw [heq]; exact hy1)
      have h2 : Fin.succ (Fin.castSucc jj) < i.succ :=
        hsm.lt_iff_lt.mp (by rw [heq]; exact hy2)
      have hv1 := Fin.lt_def.mp h1
      have hv2 := Fin.lt_def.mp h2
      simp only [Fin.val_castSucc, Fin.val_succ] at hv1 hv2
      omega
  · -- presentation of each cell as a single `*`-piece, and sub-Pfaffian
    intro κ hκ
    rw [mem_cfs] at hκ
    rcases hκ with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · -- graph cells
      by_cases hz : i.val = 0
      · -- the bottom face `y = -1`
        have hidx : i = (0 : Fin (I.card + 2)) := Fin.ext hz
        rw [hidx]
        have hgr : gr C (fun x => lvl TT x (0 : Fin (I.card + 2)))
            = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = (-1 : ℝ)} := by
          rw [gr_congr (f := fun x => lvl TT x (0 : Fin (I.card + 2))) (f' := fun _ => (-1 : ℝ))
            (fun x _ => lvl_zero TT x)]
          rfl
        rw [hgr]
        obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
          hFaceBd p m Z u₀ hu₀ C hC hCpf (-1) (by norm_num) D hZF hZD
        refine ⟨⟨P, hPset, ?_, ?_⟩, ?_⟩
        · exact le_trans hPfmt (by omega)
        · rw [hCbEval]; omega
        · obtain ⟨a, c, hfc⟩ := faceCell_star Z u₀ hu₀ C hC hCpf (-1) (by norm_num)
          exact (hfc D F hZF hZD).2
      · by_cases htop : i.val = I.card + 1
        · -- the top face `y = 1`
          have hidx : i = Fin.last (I.card + 1) := Fin.ext (by rw [Fin.val_last]; exact htop)
          rw [hidx]
          have hgr : gr C (fun x => lvl TT x (Fin.last (I.card + 1)))
              = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = (1 : ℝ)} := by
            rw [gr_congr (f := fun x => lvl TT x (Fin.last (I.card + 1))) (f' := fun _ => (1 : ℝ))
              (fun x _ => lvl_last TT x)]
            rfl
          rw [hgr]
          obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
            hFaceBd p m Z u₀ hu₀ C hC hCpf (1) (by norm_num) D hZF hZD
          refine ⟨⟨P, hPset, ?_, ?_⟩, ?_⟩
          · exact le_trans hPfmt (by omega)
          · rw [hCbEval]; omega
          · obtain ⟨a, c, hfc⟩ := faceCell_star Z u₀ hu₀ C hC hCpf (1) (by norm_num)
            exact (hfc D F hZF hZD).2
        · -- the graph of the used level `TT jj`
          have hipos : 0 < i.val := Nat.pos_of_ne_zero hz
          let jj : Fin I.card := ⟨i.val - 1, by omega⟩
          have hij : i = Fin.succ (Fin.castSucc jj) := Fin.ext (by
            show i.val = jj.val + 1
            simp only [jj]
            omega)
          obtain ⟨t, j, hw⟩ := hwit jj
          rw [hij]
          have hgr : gr C (fun x => lvl TT x (Fin.succ (Fin.castSucc jj)))
              = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
                  y (Fin.last p) = (s t j (Fin.init y)) (Fin.last m)} := by
            rw [gr_congr (f := fun x => lvl TT x (Fin.succ (Fin.castSucc jj)))
              (f' := fun x => (s t j x) (Fin.last m)) (fun x hx => by
                rw [lvl_succ]
                rw [show TT jj x = T (e jj : Fin K) x from rfl]
                exact hw x hx)]
            rfl
          rw [hgr]
          obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
            hGraphBd p m (X t) Z u₀ hu₀ C hC hCpf (k t) (s t) (hcont t)
              (hinj t) (hsub t) (hcov t) j D (hS t).1 hZF (hS t).2 hZD
          refine ⟨⟨P, hPset, ?_, ?_⟩, ?_⟩
          · exact le_trans hPfmt (by omega)
          · rw [hCbEval]; omega
          · exact graphCellSubPfX (X t) C hCpf (k t) (s t) (hinj t) (hsub t) (hcov t)
              (fun x hx => fiber_ncard_eq_of_sheets (hinj t) (hsub t) (hcov t) x hx) (hmono t) j
    · -- band cells
      by_cases hz : i.val = 0
      · -- the lowest band
        rcases Nat.eq_zero_or_pos I.card with hI0 | hIpos
        · -- no used level at all: the band is the whole open cylinder `(-1,1)`
          have hlower : (Fin.castSucc i : Fin (I.card + 2)) = (0 : Fin (I.card + 2)) :=
            Fin.ext (by simp only [Fin.val_castSucc]; exact hz)
          have hupper : (i.succ : Fin (I.card + 2)) = Fin.last (I.card + 1) :=
            Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
          have hset : bd C (fun x => lvl TT x (Fin.castSucc i)) (fun x => lvl TT x i.succ)
              = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
                  y (Fin.last p) < 1} := by
            rw [bd_congr (a := fun x => lvl TT x (Fin.castSucc i)) (a' := fun _ => (-1 : ℝ))
              (b := fun x => lvl TT x i.succ) (b' := fun _ => (1 : ℝ))
              (fun x _ => by rw [hlower, lvl_zero])
              (fun x _ => by rw [hupper, lvl_last])]
            rfl
          rw [hset]
          obtain ⟨⟨P, hPset, hPfmt, hPdeg⟩, hsubpf⟩ := hOpenBd p (m + 1) Z u₀ hu₀ C hC hCpf D hZF hZD
          refine ⟨⟨P, hPset, ?_, ?_⟩, hsubpf⟩
          · exact le_trans hPfmt (by omega)
          · rw [hCbEval]; omega
        · -- the band below the lowest used level
          have hlower : (Fin.castSucc i : Fin (I.card + 2)) = (0 : Fin (I.card + 2)) :=
            Fin.ext (by simp only [Fin.val_castSucc]; exact hz)
          have hupper : (i.succ : Fin (I.card + 2))
              = (Fin.succ (Fin.castSucc (⟨0, hIpos⟩ : Fin I.card)) : Fin (I.card + 2)) :=
            Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)
          obtain ⟨t, hw⟩ := hminLevel hIpos
          have hset : bd C (fun x => lvl TT x (Fin.castSucc i)) (fun x => lvl TT x i.succ)
              = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
                  y (Fin.last p) < (s t ⟨0, hk t⟩ (Fin.init y)) (Fin.last m)} := by
            rw [bd_congr (a := fun x => lvl TT x (Fin.castSucc i)) (a' := fun _ => (-1 : ℝ))
              (b := fun x => lvl TT x i.succ) (b' := fun x => (s t ⟨0, hk t⟩ x) (Fin.last m))
              (fun x _ => by rw [hlower, lvl_zero])
              (fun x hx => by rw [hupper, lvl_succ]; exact hw x hx)]
            rfl
          rw [hset]
          have hlt : ∀ x ∈ C, -1 < (s t ⟨0, hk t⟩ x) (Fin.last m) := by
            intro x hx
            have h1 := hw x hx
            have h2 := hbnd x hx (e ⟨0, hIpos⟩)
            rw [← h1]
            change -1 < T (e ⟨0, hIpos⟩) x
            exact (abs_lt.mp h2).1
          obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
            hBelowBd p m (X t) Z u₀ hu₀ C hC hCpf (k t) (hk t) (s t) (hcont t)
              (hinj t) (hsub t) (hcov t) hlt D (hS t).1 (hS t).2 hZF hZD
          refine ⟨⟨P, hPset, ?_, ?_⟩, ?_⟩
          · exact le_trans hPfmt (by omega)
          · rw [hCbEval]; omega
          · exact belowBandSubPfX p m (X t) C hCpf (k t) (s t) (hinj t) (hsub t) (hcov t)
              (hmono t) ⟨0, hk t⟩
      · by_cases htop : i.val = I.card
        · -- the band above the highest used level
          have hipos : 0 < I.card := by have := i.isLt; omega
          let jtop : Fin I.card := ⟨I.card - 1, Nat.sub_lt hipos (by norm_num)⟩
          have hlower : (Fin.castSucc i : Fin (I.card + 2)) = Fin.succ (Fin.castSucc jtop) :=
            Fin.ext (by
              show i.val = jtop.val + 1
              simp only [jtop]
              omega)
          have hupper : (i.succ : Fin (I.card + 2)) = Fin.last (I.card + 1) :=
            Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
          obtain ⟨t, hw⟩ := hmaxLevel hipos
          have hset : bd C (fun x => lvl TT x (Fin.castSucc i)) (fun x => lvl TT x i.succ)
              = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
                  (s t ⟨k t - 1, Nat.sub_lt (hk t) (by norm_num)⟩ (Fin.init y)) (Fin.last m)
                    < y (Fin.last p) ∧ y (Fin.last p) < 1} := by
            rw [bd_congr (a := fun x => lvl TT x (Fin.castSucc i))
              (a' := fun x => (s t ⟨k t - 1, Nat.sub_lt (hk t) (by norm_num)⟩ x) (Fin.last m))
              (b := fun x => lvl TT x i.succ) (b' := fun _ => (1 : ℝ))
              (fun x hx => by rw [hlower, lvl_succ]; exact hw x hx)
              (fun x _ => by rw [hupper, lvl_last])]
            rfl
          rw [hset]
          have hgt : ∀ x ∈ C, (s t ⟨k t - 1, Nat.sub_lt (hk t) (by norm_num)⟩ x) (Fin.last m) < 1 := by
            intro x hx
            have h1 := hw x hx
            have h2 := hbnd x hx (e jtop)
            rw [← h1]
            change T (e jtop : Fin K) x < 1
            exact (abs_lt.mp h2).2
          obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
            hAboveBd p m (X t) Z u₀ hu₀ C hC hCpf (k t) (hk t) (s t) (hcont t)
              (hinj t) (hsub t) (hcov t) hgt D (hS t).1 (hS t).2 hZF hZD
          refine ⟨⟨P, hPset, ?_, ?_⟩, ?_⟩
          · exact le_trans hPfmt (by omega)
          · rw [hCbEval]; omega
          · exact aboveBandSubPfX p m (X t) C hCpf (k t) (s t) (hinj t) (hsub t) (hcov t)
              (hmono t) ⟨k t - 1, Nat.sub_lt (hk t) (by norm_num)⟩
        · -- an interior band between two consecutive used levels
          have hipos : 0 < i.val := Nat.pos_of_ne_zero hz
          have hilt : i.val < I.card := by have := i.isLt; omega
          let jlo : Fin I.card := ⟨i.val - 1, by omega⟩
          let jhi : Fin I.card := ⟨i.val, by omega⟩
          have hlower : (Fin.castSucc i : Fin (I.card + 2)) = Fin.succ (Fin.castSucc jlo) :=
            Fin.ext (by
              show i.val = jlo.val + 1
              simp only [jlo]
              omega)
          have hupper : (i.succ : Fin (I.card + 2)) = Fin.succ (Fin.castSucc jhi) :=
            Fin.ext (by
              show i.val + 1 = jhi.val + 1
              simp only [jhi])
          obtain ⟨t₁, j₁, hw₁⟩ := hwit jlo
          obtain ⟨t₂, j₂, hw₂⟩ := hwit jhi
          have hle : ∀ x ∈ C, (s t₁ j₁ x) (Fin.last m) < (s t₂ j₂ x) (Fin.last m) := by
            intro x hx
            have hlt' : (e jlo : Fin K) < (e jhi : Fin K) := by
              refine e.strictMono ?_
              show jlo.val < jhi.val
              simp only [jlo, jhi]
              omega
            have hmono' : TT jlo x < TT jhi x := hTmono x hx hlt'
            rwa [hw₁ x hx, hw₂ x hx] at hmono'
          have hset : bd C (fun x => lvl TT x (Fin.castSucc i)) (fun x => lvl TT x i.succ)
              = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
                  (s t₁ j₁ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
                  y (Fin.last p) < (s t₂ j₂ (Fin.init y)) (Fin.last m)} := by
            rw [bd_congr (a := fun x => lvl TT x (Fin.castSucc i))
              (a' := fun x => (s t₁ j₁ x) (Fin.last m))
              (b := fun x => lvl TT x i.succ) (b' := fun x => (s t₂ j₂ x) (Fin.last m))
              (fun x hx => by rw [hlower, lvl_succ]; exact hw₁ x hx)
              (fun x hx => by rw [hupper, lvl_succ]; exact hw₂ x hx)]
            rfl
          rw [hset]
          obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
            hBandBd p m (X t₁) (X t₂) Z u₀ hu₀ C hC hCpf
              (k t₁) (s t₁) (hcont t₁) (hinj t₁) (hsub t₁) (hcov t₁)
              (k t₂) (s t₂) (hcont t₂) (hinj t₂) (hsub t₂) (hcov t₂)
              j₁ j₂ hle D (hS t₁).1 (hS t₂).1 hZF (hS t₁).2 (hS t₂).2 hZD
          refine ⟨⟨P, hPset, ?_, ?_⟩, ?_⟩
          · exact le_trans hPfmt (by omega)
          · rw [hCbEval]; omega
          · exact bandSubPfX (X t₁) (X t₂) C hCpf (hinj t₁) (hsub t₁) (hcov t₁) (hmono t₁)
              (hinj t₂) (hsub t₂) (hcov t₂) (hmono t₂) j₁ j₂

end Work.WilE7.SheetData
