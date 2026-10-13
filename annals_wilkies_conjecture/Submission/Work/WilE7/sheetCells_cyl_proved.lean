/-
  Area E7 (`Work.WilE7.sheetCells_cyl_proved`): the corrected **sheet lemma decomposition**.

  This is the `hCell`-corrected form of `Work.WilE7.sheetCells_cyl` (which is FALSE, see
  `NOTES_S25_sheetCells_cyl_refuted.md`: without `IsCell p C` the base cell can be the whole
  interval and no `2k+3`-cell cylindrical decomposition exists).

  Under the sheet data of `Work.WilE7.sheetAssembly` (`S : Stratum p (m+1)` with `S.j = m+1`, a
  `SemiPf` base `Z` cutting out `C = π_p (connectedComponentIn Z.set u₀)`, continuous sheets
  `s j : C → ℝ^{m+1}` that cover `S.X.set` over `C`, pointwise strictly ordered in `j` and with
  the extreme levels in `(-1,1)`), and with `C` a cell, the cylinder `C × [-1,1]` admits the
  cylindrical decomposition into the `k+2` graphs of the levels `-1, s 0, …, s (k-1), 1` and the
  `k+1` bands between consecutive levels (`Work.WilE7.cfs` + `Work.WilE7.decomp_of_sections`),
  each of whose `2k+3` cells is a `*`-set and sub-Pfaffian with format and `*`-degree bounded
  uniformly in the format and degree bounds of `S.X` and `Z`, and each of which is compatible
  (contained in or disjoint from) the union of the sheet graphs.

  The `IsCylDecompOn`/card/cell-shape part is `decomp_of_sections`.  The `*`/`SubPf` part
  splits into four kinds of cells: the sheet graphs (`graphCell_star_proved`), the interior bands
  (`bandCell_star`), the two bottom/top boundary faces and the two outer bands, which are the
  four extra inputs of the assembly below.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.Wilkies.Defs
import Submission.Work.WilE7.sheetAssembly
import Submission.Work.WilE7.sheetLevels
import Submission.Work.WilE7.graphCell_star_proved
import Submission.Work.WilE7.bandCell_star
import Submission.Work.WilE7.belowCell_star_proved
import Submission.Work.WilE7.aboveCell_star_proved
import Submission.Work.WilE7.isCell_localPreconnected
import Submission.Work.WilE7.decomp_of_sections
import Submission.Work.WilE7.cells_select
import Submission.Work.WilE7.s_union_tools
import Submission.Work.WilE7.BelowAux.belowBand_star
import Submission.Work.WilE7.AboveAux.aboveBand_star
import Submission.Work.WilE7.FaceAux.faceBot_star
import Submission.Work.WilE7.FaceAux.faceTop_star

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

/-! ## Auxiliary: `cfs` is a cylindrical decomposition of the cylinder -/

/-- The family `cfs C s` of graph and band cells is a cylindrical decomposition of `cyl C`,
of cardinality at most `2q+3`.  (The ingredients are the ones used for
`Work.WilE7.decomp_of_sections`, here with the witness `cfs C s` exposed.) -/
theorem cfs_isCylDecompOn {n q : ℕ} {C : Set (Fin n → ℝ)} (hC : WilkiesDesign.IsCell n C)
    (hCne : C.Nonempty) {s : Fin q → (Fin n → ℝ) → ℝ} (hs : ∀ j, ContinuousOn (s j) C)
    (hmono : ∀ x ∈ C, StrictMono fun j : Fin q => s j x)
    (hbnd : ∀ x ∈ C, ∀ j, |s j x| < 1) :
    WilkiesDesign.E.IsCylDecompOn (n+1) (cyl C) (cfs C s) ∧ (cfs C s).card ≤ 2 * q + 3 := by
  have hcell := decomp_isCell hC hCne hs hmono hbnd
  refine ⟨⟨hcell, ?_, ?_, ?_⟩, ?_⟩
  · intro a ha b hb hab
    show Disjoint a b
    rw [Set.disjoint_left]
    intro z hza hzb
    exact hab (decomp_cell_eq_of_mem hmono hbnd ha hb hza hzb)
  · exact sUnion_cfs hmono hbnd
  · have hinit : Fin.init '' cyl C = C := by
      ext x; constructor
      · rintro ⟨z, hz, rfl⟩; exact hz.1
      · intro hx
        exact ⟨Fin.snoc x 0, ⟨by simpa using hx, by simp⟩, by simp⟩
    have himg : (cfs C s).image (fun c => Fin.init '' c) = {C} := by
      ext κ; constructor
      · intro h
        rw [Finset.mem_image] at h
        obtain ⟨c, hc, rfl⟩ := h
        rw [Finset.mem_singleton]
        exact decomp_initImage hmono hbnd c hc
      · intro h
        rw [Finset.mem_singleton] at h
        rw [h]
        have hcg : gr C (fun x => lvl s x 0) ∈ cfs C s := by
          rw [cfs, Finset.mem_union]; left; rw [mem_gcs]; exact ⟨0, rfl⟩
        rw [Finset.mem_image]
        exact ⟨gr C (fun x => lvl s x 0), hcg, decomp_initImage hmono hbnd _ hcg⟩
    rw [hinit, himg]
    exact singleton_cylDecomp.1 C hC hCne
  · rw [cfs]
    calc (gcs C s ∪ bcs C s).card ≤ (gcs C s).card + (bcs C s).card := Finset.card_union_le _ _
      _ ≤ (Finset.univ : Finset (Fin (q+2))).card + (Finset.univ : Finset (Fin (q+1))).card :=
          Nat.add_le_add (by rw [gcs]; exact Finset.card_image_le)
            (by rw [bcs]; exact Finset.card_image_le)
      _ = 2 * q + 3 := by
          simp only [Finset.card_univ, Fintype.card_fin]; omega

/-! ## Auxiliary: monotonicity of the format/degree bounds -/

/-- A bound obtained as a supremum of a finite set of formats. -/
theorem le_sup_id_of_mem {s : Finset ℕ} {b : ℕ} (h : b ∈ s) : b ≤ s.sup id :=
  Finset.le_sup (f := id) h

/-- A bound obtained as a sum of a finite set of polynomials. -/
theorem eval_le_sum_id_of_mem {s : Finset (Polynomial ℕ)} {p : Polynomial ℕ} (h : p ∈ s) (D : ℕ) :
    p.eval D ≤ (s.sum id).eval D := by
  have h2 : (s.sum id).eval D = s.sum (fun q => q.eval D) := Polynomial.eval_finsetSum s id D
  rw [h2]
  exact Finset.single_le_sum (fun q _ => Nat.zero_le _) h

/-! ## The assembly -/

/-- The sheet-cell decomposition, with the four boundary pieces (the two faces `y = ±1` and the
two outer bands between `±1` and the extreme sheets) supplied as hypotheses. -/
theorem sheetCells_cyl_assembly
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1)) (hGood : S.Good) (hj : S.j = m + 1)
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (hCell : WilkiesDesign.IsCell p C)
    (hCpf : WilkiesDesign.E.SubPf p C)
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hcomp : ∀ {n : ℕ} (X : WilkiesDesign.E.SemiPf n) (x : Fin n → ℝ),
      WilkiesDesign.E.SubPf n (connectedComponentIn X.set x))
    (hlvl : ∀ x ∈ C, StrictMono fun j : Fin k => (s j x) (Fin.last m))
    (hlt : ∀ x ∈ C, -1 < (s ⟨0, hk⟩ x) (Fin.last m))
    (hgt : ∀ x ∈ C, (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ x) (Fin.last m) < 1)
    (hFaceBot : ∃ (a : ℕ) (c : Polynomial ℕ), ∀ (D F : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      WilkiesDesign.E.Star a (c.eval D) (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = -1})
    (hFaceTop : ∃ (a : ℕ) (c : Polynomial ℕ), ∀ (D F : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      WilkiesDesign.E.Star a (c.eval D) (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = 1})
    (hBelowBand : ∃ (a : ℕ) (c : Polynomial ℕ), ∀ (D F : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      WilkiesDesign.E.Star a (c.eval D) (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
          y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)})
    (hAboveBand : ∃ (a : ℕ) (c : Polynomial ℕ), ∀ (D F : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      WilkiesDesign.E.Star a (c.eval D) (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
          (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
          y (Fin.last p) < 1}) :
    ∃ (a : ℕ) (c : Polynomial ℕ), ∀ (D F : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      ∃ C' : Finset (Set (Fin (p + 1) → ℝ)),
        WilkiesDesign.E.IsCylDecompOn (p + 1)
          {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ |y (Fin.last p)| ≤ 1} C' ∧
        C'.card ≤ 2 * k + 3 ∧
        (∀ κ ∈ C', κ ⊆ (⋃ j : Fin k, {y : Fin (p + 1) → ℝ |
            Fin.init y ∈ C ∧ y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)}) ∨
          Disjoint κ (⋃ j : Fin k, {y : Fin (p + 1) → ℝ |
            Fin.init y ∈ C ∧ y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)})) ∧
        (∀ κ ∈ C', WilkiesDesign.E.Star a (c.eval D) (p + 1) κ ∧
          WilkiesDesign.E.SubPf (p + 1) κ) := by
  classical
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
  -- from here on `k` has been replaced by `k'.succ`
  have hCne : C.Nonempty :=
    ⟨WilkiesDesign.E.projFirst p (m + 1) u₀,
      by rw [hC]; exact ⟨u₀, mem_connectedComponentIn hu₀, rfl⟩⟩
  let T : Fin (k'.succ) → (Fin p → ℝ) → ℝ := fun j x => (s j x) (Fin.last m)
  have hmonoT : ∀ x ∈ C, StrictMono fun j : Fin (k'.succ) => T j x := hlvl
  have hbndT : ∀ x ∈ C, ∀ j : Fin (k'.succ), |T j x| < 1 := by
    intro x hx j
    have hmono := hmonoT x hx
    have htop : (⟨0, hk⟩ : Fin (k'.succ)) ≤ j :=
      Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
    have hbot : j ≤ (⟨k'.succ - 1, Nat.sub_lt hk (by norm_num)⟩ : Fin (k'.succ)) :=
      Fin.le_iff_val_le_val.mpr (by show j.val ≤ k'; omega)
    exact abs_lt.mpr ⟨lt_of_lt_of_le (hlt x hx) (hmono.monotone htop),
      lt_of_le_of_lt (hmono.monotone hbot) (hgt x hx)⟩
  have hsT : ∀ j : Fin (k'.succ), ContinuousOn (T j) C := fun j =>
    (continuous_apply (Fin.last m)).comp_continuousOn (hcont j)
  obtain ⟨hdec, hcard⟩ := cfs_isCylDecompOn (n := p) (q := k'.succ) hCell hCne hsT hmonoT hbndT
  -- the four boundary bounds
  obtain ⟨aFB, cFB, hFB⟩ := hFaceBot
  obtain ⟨aFT, cFT, hFT⟩ := hFaceTop
  obtain ⟨aBB, cBB, hBB⟩ := hBelowBand
  obtain ⟨aAB, cAB, hAB⟩ := hAboveBand
  -- the sheet graphs
  choose aG cG hG using fun j : Fin (k'.succ) =>
    graphCell_star_proved S hGood hj Z u₀ hu₀ C hC hCpf (k'.succ) s hcont hinj hsub hcov hcomp j
  -- the interior bands
  choose aB cB hB using fun i : Fin k' =>
    bandCell_star S hGood hj Z u₀ hu₀ C hC hCpf (k'.succ) s hcont hinj hsub hcov hcomp hlvl
      i.castSucc i.succ Fin.castSucc_lt_succ
  -- combine the bounds
  let Af : Finset ℕ := (Finset.univ : Finset (Fin (k'.succ))).image aG ∪
      ((Finset.univ : Finset (Fin k')).image aB ∪ ({aFB, aFT, aBB, aAB} : Finset ℕ))
  let Cf : Finset (Polynomial ℕ) := (Finset.univ : Finset (Fin (k'.succ))).image cG ∪
      ((Finset.univ : Finset (Fin k')).image cB ∪ ({cFB, cFT, cBB, cAB} : Finset (Polynomial ℕ)))
  let a : ℕ := Af.sup id
  let c : Polynomial ℕ := Cf.sum id
  have memAfG : ∀ j : Fin (k'.succ), aG j ∈ Af := by
    intro j
    simp only [Af]
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩))
  have memAfB : ∀ i : Fin k', aB i ∈ Af := by
    intro i
    simp only [Af]
    exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))))
  have memAfS : ∀ {x : ℕ}, x ∈ ({aFB, aFT, aBB, aAB} : Finset ℕ) → x ∈ Af := by
    intro x hx
    simp only [Af]
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr hx)))
  have memCfG : ∀ j : Fin (k'.succ), cG j ∈ Cf := by
    intro j
    simp only [Cf]
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩))
  have memCfB : ∀ i : Fin k', cB i ∈ Cf := by
    intro i
    simp only [Cf]
    exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))))
  have memCfS : ∀ {x : Polynomial ℕ}, x ∈ ({cFB, cFT, cBB, cAB} : Finset (Polynomial ℕ)) → x ∈ Cf := by
    intro x hx
    simp only [Cf]
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr hx)))
  refine ⟨a, c, fun D F hSF hSD hZF hZD => ?_⟩
  refine ⟨cfs C T, hdec, hcard, ?_, ?_⟩
  · -- compatibility with the union of the sheet graphs
    intro κ hκ
    rw [mem_cfs] at hκ
    rcases hκ with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · -- graph cell
      rcases Fin.eq_zero_or_eq_succ i with hz | ⟨i', rfl⟩
      · -- the bottom face `y = -1`
        rw [hz]
        right
        rw [Set.disjoint_left]
        intro y hy hyΓ
        rw [gr, Set.mem_ofPred_eq] at hy
        rw [Set.mem_iUnion] at hyΓ
        obtain ⟨j, hyj⟩ := hyΓ
        have hlc : y (Fin.last p) = (-1 : ℝ) := by simpa only [lvl_zero] using hy.2
        have hsm := strictMono_lvl (hmonoT (Fin.init y) hy.1) (hbndT (Fin.init y) hy.1)
        have heq : lvl T (Fin.init y) (0 : Fin ((k'.succ)+2)) =
            lvl T (Fin.init y) (Fin.succ (Fin.castSucc j)) := by
          rw [lvl_zero, lvl_succ]
          exact hlc.symm.trans hyj.2
        have hcontra : (0 : Fin ((k'.succ)+2)) = Fin.succ (Fin.castSucc j) := hsm.injective heq
        have hv := congrArg Fin.val hcontra
        simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc] at hv
        omega
      · rcases Fin.eq_castSucc_or_eq_last i' with ⟨jj, hjj⟩ | hlast
        · -- the sheet graph of `s jj`
          rw [hjj]
          left
          intro y hy
          rw [gr, Set.mem_ofPred_eq] at hy
          refine Set.mem_iUnion.mpr ⟨jj, ⟨hy.1, ?_⟩⟩
          rw [hy.2]
          rw [show (jj.castSucc).succ = (Fin.succ (Fin.castSucc jj) : Fin _) from
            Fin.ext (by simp), lvl_succ]
        · -- the top face `y = 1`
          rw [hlast]
          right
          rw [Set.disjoint_left]
          intro y hy hyΓ
          rw [gr, Set.mem_ofPred_eq] at hy
          rw [Set.mem_iUnion] at hyΓ
          obtain ⟨j, hyj⟩ := hyΓ
          rw [show (Fin.last (k'.succ)).succ = (Fin.last (k'.succ + 1) : Fin _) from
            Fin.ext (by simp)] at hy
          have hlc : y (Fin.last p) = (1 : ℝ) := by simpa only [lvl_last] using hy.2
          have hsm := strictMono_lvl (hmonoT (Fin.init y) hy.1) (hbndT (Fin.init y) hy.1)
          have heq : lvl T (Fin.init y) (Fin.last (k'.succ + 1)) =
              lvl T (Fin.init y) (Fin.succ (Fin.castSucc j)) := by
            rw [lvl_last, lvl_succ]
            exact hlc.symm.trans hyj.2
          have hcontra : (Fin.last (k'.succ + 1)) = Fin.succ (Fin.castSucc j) := hsm.injective heq
          have hv := congrArg Fin.val hcontra
          simp only [Fin.val_last, Fin.val_succ, Fin.val_castSucc] at hv
          omega
    · -- band cell: always disjoint from the sheet graphs
      right
      rw [Set.disjoint_left]
      intro y hy hyΓ
      rw [bd, Set.mem_ofPred_eq] at hy
      obtain ⟨hyC, hy1, hy2⟩ := hy
      rw [Set.mem_iUnion] at hyΓ
      obtain ⟨j, hyj⟩ := hyΓ
      have hsm := strictMono_lvl (hmonoT (Fin.init y) hyC) (hbndT (Fin.init y) hyC)
      have h1raw : lvl T (Fin.init y) (Fin.castSucc i) < (s j (Fin.init y)) (Fin.last m) :=
        lt_of_lt_of_le hy1 (le_of_eq hyj.2)
      have h2raw : (s j (Fin.init y)) (Fin.last m) < lvl T (Fin.init y) i.succ :=
        lt_of_le_of_lt (le_of_eq hyj.2.symm) hy2
      have h1 : Fin.castSucc i < Fin.succ (Fin.castSucc j) :=
        hsm.lt_iff_lt.mp (by rw [lvl_succ]; exact h1raw)
      have h2 : Fin.succ (Fin.castSucc j) < i.succ :=
        hsm.lt_iff_lt.mp (by rw [lvl_succ]; exact h2raw)
      have hv1 := Fin.lt_def.mp h1
      have hv2 := Fin.lt_def.mp h2
      simp only [Fin.val_castSucc, Fin.val_succ] at hv1 hv2
      omega
  · -- each cell is a `*`-set and sub-Pfaffian
    intro κ hκ
    rw [mem_cfs] at hκ
    rcases hκ with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · -- graph cells
      have hstar : WilkiesDesign.E.Star a (c.eval D) (p + 1) (gr C (fun x => lvl T x i)) := by
        rcases Fin.eq_zero_or_eq_succ i with hz | ⟨i', rfl⟩
        · rw [hz]
          rw [show (fun x : Fin p → ℝ => lvl T x (0 : Fin ((k'.succ)+2))) = fun _ => (-1 : ℝ) from
            funext fun x => lvl_zero T x]
          exact Work.WilE8.Star.mono (hFB D F hSF hSD hZF hZD)
            (le_sup_id_of_mem (memAfS (by simp)))
            (eval_le_sum_id_of_mem (memCfS (by simp)) D)
        · rcases Fin.eq_castSucc_or_eq_last i' with ⟨jj, hjj⟩ | hlast
          · rw [hjj]
            rw [show (fun x : Fin p → ℝ => lvl T x ((jj.castSucc).succ)) = fun x => T jj x from
              funext fun x => by
                rw [show (jj.castSucc).succ = (Fin.succ (Fin.castSucc jj) : Fin _) from
                  Fin.ext (by simp), lvl_succ]]
            exact Work.WilE8.Star.mono (hG jj D F hSF hSD hZF hZD).1
              (le_sup_id_of_mem (memAfG jj))
              (eval_le_sum_id_of_mem (memCfG jj) D)
          · rw [hlast]
            rw [show (fun x : Fin p → ℝ => lvl T x ((Fin.last (k'.succ)).succ)) = fun _ => (1 : ℝ) from
              funext fun x => by
                rw [show (Fin.last (k'.succ)).succ = (Fin.last (k'.succ + 1) : Fin _) from
                  Fin.ext (by simp), lvl_last]]
            exact Work.WilE8.Star.mono (hFT D F hSF hSD hZF hZD)
              (le_sup_id_of_mem (memAfS (by simp)))
              (eval_le_sum_id_of_mem (memCfS (by simp)) D)
      exact ⟨hstar, BandAux.subPf_of_star_of_comp hstar hcomp⟩
    · -- band cells
      have hstar : WilkiesDesign.E.Star a (c.eval D) (p + 1)
          (bd C (fun x => lvl T x (Fin.castSucc i)) (fun x => lvl T x i.succ)) := by
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hlast
        · rw [hj]
          rcases Fin.eq_zero_or_eq_succ j with hz | ⟨jj, rfl⟩
          · rw [hz]
            rw [show (fun x : Fin p → ℝ => lvl T x (Fin.castSucc ((0 : Fin (k'.succ)).castSucc))) =
                fun _ => (-1 : ℝ) from
              funext fun x => by
                rw [show Fin.castSucc ((0 : Fin (k'.succ)).castSucc) = (0 : Fin _) from
                  Fin.ext (by simp), lvl_zero]]
            rw [show (fun x : Fin p → ℝ => lvl T x (((0 : Fin (k'.succ)).castSucc).succ)) =
                fun x => (s (⟨0, hk⟩ : Fin (k'.succ)) x) (Fin.last m) from
              funext fun x => by
                rw [show ((0 : Fin (k'.succ)).castSucc).succ =
                    (Fin.succ (Fin.castSucc (⟨0, hk⟩ : Fin (k'.succ))) : Fin _) from
                  Fin.ext (by simp), lvl_succ]]
            exact Work.WilE8.Star.mono (hBB D F hSF hSD hZF hZD)
              (le_sup_id_of_mem (memAfS (by simp)))
              (eval_le_sum_id_of_mem (memCfS (by simp)) D)
          · rw [show (fun x : Fin p → ℝ => lvl T x (Fin.castSucc ((jj.succ).castSucc))) =
                fun x => T (jj.castSucc) x from
              funext fun x => by
                rw [show Fin.castSucc ((jj.succ).castSucc) =
                    (Fin.succ (Fin.castSucc (jj.castSucc)) : Fin _) from Fin.ext (by simp), lvl_succ]]
            rw [show (fun x : Fin p → ℝ => lvl T x (((jj.succ).castSucc).succ)) =
                fun x => T (jj.succ) x from
              funext fun x => by
                rw [show ((jj.succ).castSucc).succ =
                    (Fin.succ (Fin.castSucc (jj.succ)) : Fin _) from Fin.ext (by simp), lvl_succ]]
            exact Work.WilE8.Star.mono (hB jj D F hSF hSD hZF hZD).1
              (le_sup_id_of_mem (memAfB jj))
              (eval_le_sum_id_of_mem (memCfB jj) D)
        · rw [hlast]
          rw [show (fun x : Fin p → ℝ => lvl T x (Fin.castSucc (Fin.last (k'.succ)))) =
              fun x => (s (⟨k'.succ - 1, Nat.sub_lt hk (by norm_num)⟩ : Fin (k'.succ)) x) (Fin.last m) from
            funext fun x => by
              rw [show Fin.castSucc (Fin.last (k'.succ)) =
                  (Fin.succ (Fin.castSucc (⟨k'.succ - 1, Nat.sub_lt hk (by norm_num)⟩ : Fin (k'.succ))) : Fin _) from
                Fin.ext (by simp), lvl_succ]]
          rw [show (fun x : Fin p → ℝ => lvl T x ((Fin.last (k'.succ)).succ)) = fun _ => (1 : ℝ) from
            funext fun x => by
              rw [show (Fin.last (k'.succ)).succ = (Fin.last (k'.succ + 1) : Fin _) from
                Fin.ext (by simp), lvl_last]]
          exact Work.WilE8.Star.mono (hAB D F hSF hSD hZF hZD)
            (le_sup_id_of_mem (memAfS (by simp)))
            (eval_le_sum_id_of_mem (memCfS (by simp)) D)
      exact ⟨hstar, BandAux.subPf_of_star_of_comp hstar hcomp⟩

/-! ## The target theorem -/

theorem sheetCells_cyl_proved
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1)) (hGood : S.Good) (hj : S.j = m + 1)
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (hCell : WilkiesDesign.IsCell p C)
    (hCpf : WilkiesDesign.E.SubPf p C)
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hcomp : ∀ {n : ℕ} (X : WilkiesDesign.E.SemiPf n) (x : Fin n → ℝ),
      WilkiesDesign.E.SubPf n (connectedComponentIn X.set x))
    (hlvl : ∀ x ∈ C, StrictMono fun j : Fin k => (s j x) (Fin.last m))
    (hlt : ∀ x ∈ C, -1 < (s ⟨0, hk⟩ x) (Fin.last m))
    (hgt : ∀ x ∈ C, (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ x) (Fin.last m) < 1) :
    ∃ (a : ℕ) (c : Polynomial ℕ), ∀ (D F : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      ∃ C' : Finset (Set (Fin (p + 1) → ℝ)),
        WilkiesDesign.E.IsCylDecompOn (p + 1)
          {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ |y (Fin.last p)| ≤ 1} C' ∧
        C'.card ≤ 2 * k + 3 ∧
        (∀ κ ∈ C', κ ⊆ (⋃ j : Fin k, {y : Fin (p + 1) → ℝ |
            Fin.init y ∈ C ∧ y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)}) ∨
          Disjoint κ (⋃ j : Fin k, {y : Fin (p + 1) → ℝ |
            Fin.init y ∈ C ∧ y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)})) ∧
        (∀ κ ∈ C', WilkiesDesign.E.Star a (c.eval D) (p + 1) κ ∧
          WilkiesDesign.E.SubPf (p + 1) κ) :=
  sheetCells_cyl_assembly S hGood hj Z u₀ hu₀ C hC hCell hCpf k hk s hcont hinj hsub hcov hcomp
    hlvl hlt hgt
    (FaceAux.faceBot_star S Z u₀ hu₀ C hC k hk s hcont hsub hlt)
    (FaceAux.faceTop_star S Z u₀ hu₀ C hC k hk s hcont hsub hgt)
    (BelowAux.belowBand_star S Z u₀ hu₀ C hC k hk s hcont hinj hsub hcov hlt)
    (AboveAux.aboveBand_star S Z u₀ hu₀ C hC k hk s hcont hinj hsub hcov hgt)

end Work.WilE7
