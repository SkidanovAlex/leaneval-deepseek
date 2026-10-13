import Mathlib
import Submission.Work.WilE7.SheetData.multiStrata_cellsX
import Submission.Work.WilE7.SheetData.levels_trichotomy_order
import Submission.Work.WilE7.SheetData.belowExtremeCell
import Submission.Work.WilE7.SheetData.aboveExtremeCell
import Submission.Work.WilE7.SheetData.graphCellTT
import Submission.Work.WilE7.SheetData.bandCellTT

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Work.WilE7.SheetData

open WilkiesDesign WilkiesDesign.E
open Work.WilE7 (cfs lvl gr bd cyl mem_cfs lvl_zero lvl_last lvl_succ strictMono_lvl)


theorem gcase_cfs (F : ℕ) :
    ∃ (A : ℕ) (Cb : Polynomial ℕ),
      ∀ (p m r : ℕ) (X : Fin r → WilkiesDesign.E.SemiPf (p + (m + 1)))
        (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ)
        (hu₀ : u₀ ∈ Z.set) (C : Set (Fin p → ℝ))
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
        (hbnd_le : ∀ (t : Fin r) (j : Fin (k t)), ∀ x ∈ C,
          |(s t j x) (Fin.last m)| ≤ 1)
        (hcls : ∀ (t : Fin r) (j : Fin (k t)),
          (∀ x ∈ C, (s t j x) (Fin.last m) = 1) ∨
          (∀ x ∈ C, (s t j x) (Fin.last m) = -1) ∨
          (∀ x ∈ C, |(s t j x) (Fin.last m)| < 1))
        (hdich : ∀ (t t' : Fin r) (j : Fin (k t)) (j' : Fin (k t')),
          (∃ x ∈ C, (s t j x) (Fin.last m) = (s t' j' x) (Fin.last m)) →
          ∀ x ∈ C, (s t j x) (Fin.last m) = (s t' j' x) (Fin.last m))
        (D : ℕ)
        (hS : ∀ t : Fin r, (X t).fmt ≤ F ∧ (X t).deg ≤ D)
        (hZF : Z.fmt ≤ F) (hZD : Z.deg ≤ D),
      ∃ (K : ℕ) (TT : Fin K → (Fin p → ℝ) → ℝ),
        (∀ i : Fin K, ContinuousOn (TT i) C) ∧
        (∀ x ∈ C, StrictMono fun i : Fin K => TT i x) ∧
        (∀ x ∈ C, ∀ i : Fin K, |TT i x| < 1) ∧
        (∀ (t : Fin r) (j : Fin (k t)),
          (∃ i : Fin K, ∀ x ∈ C, TT i x = (s t j x) (Fin.last m)) ∨
          (∀ x ∈ C, (s t j x) (Fin.last m) = 1) ∨
          (∀ x ∈ C, (s t j x) (Fin.last m) = -1)) ∧
        (∀ i : Fin K, ∃ (t : Fin r) (j : Fin (k t)),
          ∀ x ∈ C, TT i x = (s t j x) (Fin.last m)) ∧
        K ≤ (∑ t, k t) ∧
        (∀ κ ∈ Work.WilE7.cfs C TT, Fin.init '' κ = C) ∧
        WilkiesDesign.E.IsCylDecompOn (p + 1) (Work.WilE7.cyl C) (Work.WilE7.cfs C TT) ∧
        (Work.WilE7.cfs C TT).card ≤ 2 * (∑ t, k t) + 3 ∧
        (∀ κ ∈ Work.WilE7.cfs C TT, (∃ P : WilkiesDesign.E.StarPiece (p + 1),
            P.set = κ ∧ P.X.fmt ≤ A ∧ P.X.deg ≤ Cb.eval D) ∧
          WilkiesDesign.E.SubPf (p + 1) κ) := by
  obtain ⟨Ag, Cg, hGraph⟩ := graphCellTT F
  obtain ⟨Ain, Cin, hInt⟩ := bandCellTT F
  obtain ⟨Ae, Ce, hBelow⟩ := belowExtremeCell F
  obtain ⟨Au, Cu, hAbove⟩ := aboveExtremeCell F
  obtain ⟨Af, Cf, hFace⟩ := faceCell_bd F
  obtain ⟨Aop, Cop, hOpen⟩ := cylOpenBand F
  refine ⟨Ag + Ain + Ae + Au + Af + Aop, Cg + Cin + Ce + Cu + Cf + Cop, ?_⟩
  intro p m r X Z u₀ hu₀ C hC hCpf hCell k hk s hcont hinj hsub hcov hbnd_le hcls hdich D
    hS hZF hZD
  have hCbEval : ∀ D' : ℕ, (Cg + Cin + Ce + Cu + Cf + Cop).eval D'
      = Cg.eval D' + Cin.eval D' + Ce.eval D' + Cu.eval D' + Cf.eval D' + Cop.eval D' :=
    fun D' => by simp only [Polynomial.eval_add]
  -- the base cell is nonempty and preconnected
  have hCne : C.Nonempty :=
    ⟨WilkiesDesign.E.projFirst p (m + 1) u₀,
      by rw [hC]; exact ⟨u₀, mem_connectedComponentIn hu₀, rfl⟩⟩
  have hCpre : IsPreconnected C := Work.WilE7.isPreconnected_of_isCell hCell
  -- the level functions of the sheets are continuous
  have hcontL : ∀ (t : Fin r) (j : Fin (k t)),
      ContinuousOn (fun x : Fin p → ℝ => (s t j x) (Fin.last m)) C :=
    fun t j => (continuous_apply (Fin.last m)).comp_continuousOn (hcont t j)
  obtain ⟨K, TT, σ, hKle, hTTcont, hTTmono, hTTbnd, hTTwit, hσmono, hTcov⟩ :=
    levels_trichotomy_order hCne hCpre r k (fun t j x => (s t j x) (Fin.last m)) hcontL hcls
      (fun t j t' j' => hdich t t' j j')
  -- the transported sheet data for the reordered families `fun j => s t (σ t j)`
  have hs'cont : ∀ (t : Fin r) (j : Fin (k t)),
      ContinuousOn (fun x : Fin p → ℝ => s t (σ t j) x) C := fun t j => hcont t (σ t j)
  have hs'inj : ∀ (t : Fin r) (x : Fin p → ℝ), x ∈ C →
      Function.Injective fun j : Fin (k t) => s t (σ t j) x := fun t x hx =>
    (hinj t x hx).comp (σ t).injective
  have hs'sub : ∀ (t : Fin r) (j : Fin (k t)), ∀ x ∈ C,
      Fin.append x (s t (σ t j) x) ∈ (X t).set := fun t j x hx => hsub t (σ t j) x hx
  have hs'cov : ∀ (t : Fin r) (z : Fin (p + (m + 1)) → ℝ), z ∈ (X t).set →
      WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin (k t), s t (σ t j) (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z := by
    intro t z hz hzC
    obtain ⟨j, hj⟩ := hcov t z hz hzC
    exact ⟨(σ t).symm j, by rw [Equiv.apply_symm_apply]; exact hj⟩
  have hs'mono : ∀ (t : Fin r) (x : Fin p → ℝ), x ∈ C →
      Monotone fun j : Fin (k t) => (s t (σ t j) x) (Fin.last m) := fun t x hx => hσmono t x hx
  -- the decomposition facts
  have hdec := cfs_isCylDecompOn (n := p) (q := K) hCell hCne hTTcont hTTmono hTTbnd
  have hinit : ∀ κ ∈ cfs C TT, Fin.init '' κ = C := decomp_initImage hTTmono hTTbnd
  have hcard : (cfs C TT).card ≤ 2 * (∑ t, k t) + 3 := le_trans hdec.2 (by omega)
  -- the two faces are presented once and for all
  obtain ⟨a1, c1, hfc1⟩ := faceCell_star Z u₀ hu₀ C hC hCpf (-1) (by norm_num)
  obtain ⟨a2, c2, hfc2⟩ := faceCell_star Z u₀ hu₀ C hC hCpf (1) (by norm_num)
  refine ⟨K, TT, hTTcont, hTTmono, hTTbnd, hTcov, ?_, hKle, hinit, hdec.1, hcard, ?_⟩
  · -- every used level is the level of an actual sheet
    intro i
    obtain ⟨t, j, hw⟩ := hTTwit i
    exact ⟨t, σ t j, hw⟩
  · -- the presentation of every cell of `cfs C TT`
    intro κ hκ
    rw [mem_cfs] at hκ
    rcases hκ with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · -- graph cells `gr C (lvl TT · i)`, `i : Fin (K+2)`
      by_cases hz : i.val = 0
      · -- the bottom face `y = -1`
        have hidx : i = (0 : Fin (K + 2)) := Fin.ext hz
        rw [hidx]
        have hgr : gr C (fun x => lvl TT x (0 : Fin (K + 2)))
            = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = (-1 : ℝ)} := by
          rw [gr_congr (f := fun x => lvl TT x (0 : Fin (K + 2))) (f' := fun _ => (-1 : ℝ))
            (fun x _ => lvl_zero TT x)]
          rfl
        rw [hgr]
        obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
          hFace p m Z u₀ hu₀ C hC hCpf (-1) (by norm_num) D hZF hZD
        refine ⟨⟨P, hPset, le_trans hPfmt (by omega), ?_⟩, (hfc1 D F hZF hZD).2⟩
        rw [hCbEval]; omega
      · by_cases htop : i.val = K + 1
        · -- the top face `y = 1`
          have hidx : i = Fin.last (K + 1) := Fin.ext (by rw [Fin.val_last]; exact htop)
          rw [hidx]
          have hgr : gr C (fun x => lvl TT x (Fin.last (K + 1)))
              = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = (1 : ℝ)} := by
            rw [gr_congr (f := fun x => lvl TT x (Fin.last (K + 1))) (f' := fun _ => (1 : ℝ))
              (fun x _ => lvl_last TT x)]
            rfl
          rw [hgr]
          obtain ⟨P, hPset, hPfmt, hPdeg⟩ :=
            hFace p m Z u₀ hu₀ C hC hCpf (1) (by norm_num) D hZF hZD
          refine ⟨⟨P, hPset, le_trans hPfmt (by omega), ?_⟩, (hfc2 D F hZF hZD).2⟩
          rw [hCbEval]; omega
        · -- the graph of the used level `TT ii`
          have hKpos : 0 < K := by omega
          let ii : Fin K := ⟨i.val - 1, by omega⟩
          have hij : i = Fin.succ (Fin.castSucc ii) := Fin.ext (by
            show i.val = ii.val + 1
            simp only [ii]
            omega)
          obtain ⟨t, j, hw⟩ := hTTwit ii
          have hgr : gr C (fun x => lvl TT x i)
              = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = TT ii (Fin.init y)} := by
            rw [hij, gr_congr (f := fun x => lvl TT x (Fin.succ (Fin.castSucc ii)))
              (f' := TT ii) (fun x _ => lvl_succ TT x ii)]
            rfl
          rw [hgr]
          obtain ⟨⟨P, hPset, hPfmt, hPdeg⟩, hSub⟩ :=
            hGraph p m (X t) Z u₀ hu₀ C hC hCpf (k t) (fun jj => s t (σ t jj))
              (hs'cont t) (hs'inj t) (hs'sub t) (hs'cov t) (hs'mono t) (TT ii) ⟨j, hw⟩ D
              (hS t).1 (hS t).2 hZF hZD
          refine ⟨⟨P, hPset, le_trans hPfmt (by omega), ?_⟩, hSub⟩
          rw [hCbEval]; omega
    · -- band cells `bd C (lvl TT · (castSucc i)) (lvl TT · i.succ)`, `i : Fin (K+1)`
      rcases Nat.eq_zero_or_pos K with hK0 | hKpos
      · -- no used level: the single band is the open cylinder `(-1,1)`
        subst hK0
        have hz : i.val = 0 := by omega
        have hlower : (Fin.castSucc i : Fin (0 + 2)) = (0 : Fin (0 + 2)) := Fin.ext (by
          simp only [Fin.val_castSucc]; exact hz)
        have hupper : (i.succ : Fin (0 + 2)) = Fin.last (0 + 1) := Fin.ext (by
          simp only [Fin.val_succ, Fin.val_last]; omega)
        have hset : bd C (fun x => lvl TT x (Fin.castSucc i)) (fun x => lvl TT x i.succ)
            = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
                y (Fin.last p) < 1} := by
          rw [bd_congr (a := fun x => lvl TT x (Fin.castSucc i)) (a' := fun _ => (-1 : ℝ))
            (b := fun x => lvl TT x i.succ) (b' := fun _ => (1 : ℝ))
            (fun x _ => by rw [hlower, lvl_zero]) (fun x _ => by rw [hupper, lvl_last])]
          rfl
        rw [hset]
        obtain ⟨⟨P, hPset, hPfmt, hPdeg⟩, hsubpf⟩ := hOpen p (m + 1) Z u₀ hu₀ C hC hCpf D hZF hZD
        refine ⟨⟨P, hPset, le_trans hPfmt (by omega), ?_⟩, hsubpf⟩
        rw [hCbEval]; omega
      · by_cases hz : i.val = 0
        · -- the band below the lowest used level: `(-1, TT 0)`
          let i0 : Fin K := ⟨0, hKpos⟩
          have hidx : (Fin.castSucc i : Fin (K + 2)) = (0 : Fin (K + 2)) :=
            Fin.ext (by simp only [Fin.val_castSucc]; exact hz)
          have hupper : (i.succ : Fin (K + 2)) = (Fin.succ (Fin.castSucc i0) : Fin (K + 2)) :=
            Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc, i0]; omega)
          obtain ⟨t, j, hw⟩ := hTTwit i0
          have hset : bd C (fun x => lvl TT x (Fin.castSucc i)) (fun x => lvl TT x i.succ)
              = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
                  y (Fin.last p) < TT i0 (Fin.init y)} := by
            rw [bd_congr (a := fun x => lvl TT x (Fin.castSucc i)) (a' := fun _ => (-1 : ℝ))
              (b := fun x => lvl TT x i.succ) (b' := TT i0)
              (fun x _ => by rw [hidx, lvl_zero])
              (fun x _ => by rw [hupper, lvl_succ])]
            rfl
          rw [hset]
          have hlt : ∀ x ∈ C, -1 < TT i0 x := fun x hx => (abs_lt.mp (hTTbnd x hx i0)).1
          have hmin : ∀ j' : Fin (k t),
              (∀ x ∈ C, TT i0 x ≤ s t (σ t j') x (Fin.last m)) ∨
              (∀ x ∈ C, s t (σ t j') x (Fin.last m) = -1) := by
            intro j'
            rcases hTcov t (σ t j') with ⟨i', hi'⟩ | h1 | hneg
            · left
              intro x hx
              have hle : i0 ≤ i' := Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
              have hm := (hTTmono x hx).monotone hle
              rw [hi' x hx] at hm
              exact hm
            · left
              intro x hx
              rw [h1 x hx]
              exact le_of_lt (abs_lt.mp (hTTbnd x hx i0)).2
            · right
              exact hneg
          obtain ⟨⟨P, hPset, hPfmt, hPdeg⟩, hsubpf⟩ :=
            hBelow p m (X t) Z u₀ hu₀ C hC hCpf (k t) (hk t) (fun jj => s t (σ t jj))
              (hs'cont t) (hs'inj t) (hs'sub t) (hs'cov t) (hs'mono t) (TT i0) ⟨j, hw⟩ hlt hmin D
              (hS t).1 (hS t).2 hZF hZD
          refine ⟨⟨P, hPset, le_trans hPfmt (by omega), ?_⟩, hsubpf⟩
          rw [hCbEval]; omega
        · by_cases htop : i.val = K
          · -- the band above the highest used level: `(TT (K-1), 1)`
            let ilast : Fin K := ⟨K - 1, Nat.sub_lt hKpos (by norm_num)⟩
            have hlower : (Fin.castSucc i : Fin (K + 2)) =
                (Fin.succ (Fin.castSucc ilast) : Fin (K + 2)) := Fin.ext (by
              show i.val = ilast.val + 1
              simp only [ilast]
              omega)
            have hidx : (i.succ : Fin (K + 2)) = Fin.last (K + 1) := Fin.ext (by
              simp only [Fin.val_succ, Fin.val_last]; omega)
            obtain ⟨t, j, hw⟩ := hTTwit ilast
            have hset : bd C (fun x => lvl TT x (Fin.castSucc i)) (fun x => lvl TT x i.succ)
                = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ TT ilast (Fin.init y) < y (Fin.last p) ∧
                    y (Fin.last p) < 1} := by
              rw [bd_congr (a := fun x => lvl TT x (Fin.castSucc i)) (a' := TT ilast)
                (b := fun x => lvl TT x i.succ) (b' := fun _ => (1 : ℝ))
                (fun x _ => by rw [hlower, lvl_succ])
                (fun x _ => by rw [hidx, lvl_last])]
              rfl
            rw [hset]
            have hgt : ∀ x ∈ C, TT ilast x < 1 := fun x hx => (abs_lt.mp (hTTbnd x hx ilast)).2
            have hmax : ∀ j' : Fin (k t),
                (∀ x ∈ C, s t (σ t j') x (Fin.last m) ≤ TT ilast x) ∨
                (∀ x ∈ C, s t (σ t j') x (Fin.last m) = 1) := by
              intro j'
              rcases hTcov t (σ t j') with ⟨i', hi'⟩ | h1 | hneg
              · left
                intro x hx
                have hle : i' ≤ ilast :=
                  Fin.le_iff_val_le_val.mpr (Nat.le_sub_one_of_lt i'.isLt)
                have hm := (hTTmono x hx).monotone hle
                rw [hi' x hx] at hm
                exact hm
              · right
                exact h1
              · left
                intro x hx
                rw [hneg x hx]
                exact le_of_lt (abs_lt.mp (hTTbnd x hx ilast)).1
            obtain ⟨⟨P, hPset, hPfmt, hPdeg⟩, hsubpf⟩ :=
              hAbove p m (X t) Z u₀ hu₀ C hC hCpf (k t) (hk t) (fun jj => s t (σ t jj))
                (hs'cont t) (hs'inj t) (hs'sub t) (hs'cov t) (hs'mono t) (TT ilast) ⟨j, hw⟩ hgt
                hmax D (hS t).1 (hS t).2 hZF hZD
            refine ⟨⟨P, hPset, le_trans hPfmt (by omega), ?_⟩, hsubpf⟩
            rw [hCbEval]; omega
          · -- an interior band between consecutive levels
            have hipos : 0 < i.val := Nat.pos_of_ne_zero hz
            have hilt : i.val < K := by have := i.isLt; omega
            let jlo : Fin K := ⟨i.val - 1, by omega⟩
            let jhi : Fin K := ⟨i.val, by omega⟩
            have hlower : (Fin.castSucc i : Fin (K + 2)) =
                (Fin.succ (Fin.castSucc jlo) : Fin (K + 2)) := Fin.ext (by
              show i.val = jlo.val + 1
              simp only [jlo]
              omega)
            have hupper : (i.succ : Fin (K + 2)) =
                (Fin.succ (Fin.castSucc jhi) : Fin (K + 2)) := Fin.ext (by
              show i.val + 1 = jhi.val + 1
              simp only [jhi])
            obtain ⟨t₁, j₁, hw₁⟩ := hTTwit jlo
            obtain ⟨t₂, j₂, hw₂⟩ := hTTwit jhi
            have hset : bd C (fun x => lvl TT x (Fin.castSucc i)) (fun x => lvl TT x i.succ)
                = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ TT jlo (Fin.init y) < y (Fin.last p) ∧
                    y (Fin.last p) < TT jhi (Fin.init y)} := by
              rw [bd_congr (a := fun x => lvl TT x (Fin.castSucc i)) (a' := TT jlo)
                (b := fun x => lvl TT x i.succ) (b' := TT jhi)
                (fun x _ => by rw [hlower, lvl_succ])
                (fun x _ => by rw [hupper, lvl_succ])]
              rfl
            rw [hset]
            have hlt' : ∀ x ∈ C, TT jlo x < TT jhi x := by
              intro x hx
              exact hTTmono x hx (Fin.lt_def.mpr (by simp only [jlo, jhi]; omega))
            obtain ⟨⟨P, hPset, hPfmt, hPdeg⟩, hsubpf⟩ :=
              hInt p m (X t₁) (X t₂) Z u₀ hu₀ C hC hCpf
                (k t₁) (fun jj => s t₁ (σ t₁ jj)) (hs'cont t₁) (hs'inj t₁) (hs'sub t₁)
                (hs'cov t₁) (hs'mono t₁)
                (k t₂) (fun jj => s t₂ (σ t₂ jj)) (hs'cont t₂) (hs'inj t₂) (hs'sub t₂)
                (hs'cov t₂) (hs'mono t₂)
                (TT jlo) (TT jhi) ⟨j₁, hw₁⟩ ⟨j₂, hw₂⟩ hlt' D
                (hS t₁).1 (hS t₂).1 hZF (hS t₁).2 (hS t₂).2 hZD
            refine ⟨⟨P, hPset, le_trans hPfmt (by omega), ?_⟩, hsubpf⟩
            rw [hCbEval]; omega

end Work.WilE7.SheetData
