/-
  WilG4c — `Work.WilG4c.CellParamMain` (BNZ §2.2, cell parametrisation).

  Given a cell `κ` of a cylindrical decomposition of `ℝ^{p+N}` lying in the open cube in its
  `N` fibre coordinates, we parametrise the fibre of `κ` over a set `Λ` of parameters by the
  open cube `I^N`, with `Ω`-bounded coordinate graphs of a format independent of `D` and a
  degree polynomial in `D`.

  The construction is the tower of `CellParamDefs`: at level `m+1` the new coordinate
  interpolates between the fibre ends `L m`, `H m` of the level-`m+1` projection
  `lvl p N κ (m+1)` of `κ`, which are `Ω`-definable by `Work.WilG4c.StepFiberEnds`.  The `Ω`
  bookkeeping is done level by level, using the composition and combination lemmas
  `Work.WilG4c.graphOfCompGen` and `Work.WilG4c.graphOfLinComb_mem`.
-/
import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.FiberEndsDefs
import Submission.Work.WilG4c.StepFiberEnds
import Submission.Work.WilG4c.YbddAux
import Submission.Work.WilG4c.CellParamAux
import Submission.Work.WilG4c.graphOfCompGen
import Submission.Work.WilG4c.lvl_omega
import Submission.Work.WilG4c.lvl_isCell
import Submission.Work.WilG4c.append_eq_gluePt
import Submission.Work.WilG4c.cellFibre_param
import Submission.Work.WilG4c.graphOfLinComb_mem
import Submission.Work.WilG4c.lvl_mem_iff
import Submission.Work.WilG1.Cell.isCell_of_mem_cylDecomp
import Submission.Work.WilG0.API
import Submission.Work.WilG0.Main
import Submission.Work.WilG0.projLastIter_mem
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.snocIt_surjective

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1

/-! ## 3. The main theorem -/

theorem CellParamMain (S : SOMin) (p N F0 : ℕ) : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
    ∀ (D : ℕ) (C : Finset (Set (Fin (p + N) → ℝ))), IsCylDecomp (p + N) C →
      (∀ κ ∈ C, κ ∈ S.Ω F0 D (p + N)) →
      ∀ (κ : Set (Fin (p + N) → ℝ)), κ ∈ C → κ ⊆ Work.WilG4c.inCubeSet p N →
      ∀ (Λ : Set (Fin p → ℝ)), (∀ l ∈ Λ, ∃ y : Fin N → ℝ, Fin.append l y ∈ κ) →
        ∃ Ψ : (Fin p → ℝ) → (Fin N → ℝ) → (Fin N → ℝ),
          (∀ j : Fin N,
            famGraph (fun l t => Ψ l t j) ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) (p + N + 1)) ∧
          (∀ l ∈ Λ, ∀ t ∈ openCube N, Ψ l t ∈ openCube N) ∧
          (∀ l ∈ Λ, ∀ t ∈ openCube N, Fin.append l (Ψ l t) ∈ κ) ∧
          (∀ l ∈ Λ, ∀ y : Fin N → ℝ, Fin.append l y ∈ κ → ∃ t ∈ openCube N, Ψ l t = y) := by
  classical
  -- (1) The fibre-end data of the levels.
  have hFE : ∀ m : Fin N, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) (Z : Set (Fin (p + m.val + 1) → ℝ)),
        Z ∈ S.Ω (F0 + (N - (m.val + 1))) D (p + m.val + 1) →
        (∀ z ∈ Z, z (Fin.last (p + m.val)) ∈ Set.Ioo (0 : ℝ) 1) →
        ∃ (lo hi : (Fin (p + m.val) → ℝ) → ℝ),
          graphOf lo ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + m.val + 1) ∧
          graphOf hi ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + m.val + 1) ∧
          ∀ x : Fin (p + m.val) → ℝ, (∃ y : ℝ, Fin.snoc x y ∈ Z) →
            (∀ y : ℝ, Fin.snoc x y ∈ Z → lo x ≤ y ∧ y ≤ hi x) ∧
            (∀ u : ℝ, lo x < u → ∃ y : ℝ, Fin.snoc x y ∈ Z ∧ y < u) ∧
            (∀ u : ℝ, u < hi x → ∃ y : ℝ, Fin.snoc x y ∈ Z ∧ u < y) :=
    fun m => StepFiberEnds S (p + m.val) (F0 + (N - (m.val + 1)))
  choose FAa FBb hFE' using hFE
  -- (2) The constants of the composition lemma, per level.
  have hCG : ∀ m : Fin N, ∃ (C₁ C₂ : ℕ),
      ∀ (F₁ F₂ D₁ D₂ : ℕ) (g : (Fin (p + m.val) → ℝ) → ℝ)
        (φ : (Fin (p + N) → ℝ) → (Fin (p + m.val) → ℝ)),
        graphOf g ∈ S.Ω F₁ D₁ (p + m.val + 1) →
        (∀ j : Fin (p + m.val),
          graphOf (fun x : Fin (p + N) → ℝ => φ x j) ∈ S.Ω F₂ D₂ (p + N + 1)) →
        graphOf (g ∘ φ) ∈ S.Ω (F₁ + F₂ + C₁) (D₁ + (p + m.val) * D₂ + C₂) (p + N + 1) :=
    fun m => graphOfCompGen S (p + m.val) (p + N)
  choose Cg1 Cg2 hCG' using hCG
  -- (3) The constants of the combination lemma.
  obtain ⟨CL1, CL2, hLC⟩ : ∃ (C₁ C₂ : ℕ),
      ∀ (F₁ F₂ F₃ D₁ D₂ D₃ : ℕ) (A B T : (Fin (p + N) → ℝ) → ℝ),
        graphOf A ∈ S.Ω F₁ D₁ (p + N + 1) → graphOf B ∈ S.Ω F₂ D₂ (p + N + 1) →
        graphOf T ∈ S.Ω F₃ D₃ (p + N + 1) →
        graphOf (fun x => A x + T x * (B x - A x)) ∈
          S.Ω (F₁ + F₂ + F₃ + C₁) (D₁ + D₂ + D₃ + C₂) (p + N + 1) :=
    graphOfLinComb_mem S (p+N)
  -- (4) The format and degree sequences.
  let FA0 : ℕ := (∑ m : Fin N, FAa m) + (∑ m : Fin N, Cg1 m) + (∑ m : Fin N, Cg2 m)
    + CL1 + (p + N + 1) + 1
  let Fbig : ℕ := 3 * FA0 + 3 * (∑ m : Fin N, Cg1 m) + CL1 + (p + N + 1) + 1
  let Aseq : ℕ → ℕ := fun j => Nat.rec FA0 (fun _ ih => 3 * ih + Fbig) j
  let FAfun : ℕ → ℕ := fun i => if h : i < N then FAa ⟨i, h⟩ else 0
  let FBfun : ℕ → MvPolynomial (Fin 2) ℕ := fun i => if h : i < N then FBb ⟨i, h⟩ else 0
  let BD0 : ℕ := 3 * (∑ m : Fin N, Cg2 m) + CL2 + 3 + 1
  let Bseq : ℕ → MvPolynomial (Fin 2) ℕ := fun j =>
    Nat.rec (MvPolynomial.C 1)
      (fun i ih => MvPolynomial.C 3 * FBfun i + MvPolynomial.C (3 * (p + N) + 3) * ih
        + MvPolynomial.C BD0) j
  have Aseq_succ : ∀ j, Aseq (j+1) = 3 * Aseq j + Fbig := fun j => rfl
  have Bseq_succ : ∀ i, Bseq (i+1) = MvPolynomial.C 3 * FBfun i
      + MvPolynomial.C (3 * (p + N) + 3) * Bseq i + MvPolynomial.C BD0 := fun i => rfl
  have hFA0_le : ∀ m : Fin N, FAa m ≤ FA0 ∧ Cg1 m ≤ FA0 ∧ Cg2 m ≤ FA0 := by
    intro m
    have h1 : FAa m ≤ ∑ m : Fin N, FAa m :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
    have h2 : Cg1 m ≤ ∑ m : Fin N, Cg1 m :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
    have h3 : Cg2 m ≤ ∑ m : Fin N, Cg2 m :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
    refine ⟨by simp only [FA0]; omega, by simp only [FA0]; omega, by simp only [FA0]; omega⟩
  have hFAfun_le : ∀ i, FAfun i ≤ FA0 := by
    intro i
    by_cases h : i < N
    · simp only [FAfun, dif_pos h]; exact (hFA0_le ⟨i, h⟩).1
    · simp only [FAfun, dif_neg h]; exact Nat.zero_le _
  have Aseq_step : ∀ j, 3 * Aseq j + (3 * FA0 + 3 * (∑ m : Fin N, Cg1 m) + CL1) ≤
      Aseq (j+1) := by
    intro j
    rw [Aseq_succ]
    simp only [Fbig]
    omega
  have Aseq_mono : ∀ j, Aseq j ≤ Aseq (j+1) := by
    intro j
    have h := Aseq_step j
    omega
  have Aseq_ge : ∀ j, FA0 ≤ Aseq j := by
    intro j
    induction j with
    | zero => rw [show Aseq 0 = FA0 from rfl]
    | succ j ih => exact le_trans ih (Aseq_mono j)
  refine ⟨Aseq N, Bseq N, ?_⟩
  intro D C hcd hΩ κ hκ hcube Λ hΛ
  have Bseq_eval : ∀ i, (Bseq (i+1)).eval ![D, 1] =
      3 * (FBfun i).eval ![D, 1] + (3 * (p + N) + 3) * (Bseq i).eval ![D, 1] + BD0 := by
    intro i
    rw [Bseq_succ]
    simp [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  have Bseq_mono : ∀ i, (Bseq i).eval ![D, 1] ≤ (Bseq (i+1)).eval ![D, 1] := by
    intro i
    rw [Bseq_eval]
    have hmul : (Bseq i).eval ![D, 1] ≤ (3 * (p + N) + 3) * (Bseq i).eval ![D, 1] :=
      Nat.le_mul_of_pos_left _ (by omega)
    simp only [BD0]
    omega
  -- the level/gluePt description
  have hlvlMem_iff : ∀ (m : ℕ) (hm : m ≤ N) (x : Fin (p+m) → ℝ),
      x ∈ lvl p N κ m ↔ ∃ w : Fin (N-m) → ℝ, gluePt p N m hm x w ∈ κ :=
    fun m hm x => lvl_mem_iff p N κ m hm x
  -- (5) `κ` is a cell, and its levels are cells and `Ω`-sets.
  have hcellK : IsCell (p+N) κ := Work.WilG1.Cell.isCell_of_mem_cylDecomp hcd hκ
  have hlvlOm : ∀ m (hm : m ≤ N), lvl p N κ m ∈ S.Ω (F0 + (N-m)) D (p+m) :=
    fun m hm => lvl_omega S p N F0 D κ m hm (hΩ κ hκ)
  have hlvlCell : ∀ m (hm : m ≤ N), IsCell (p+m) (lvl p N κ m) :=
    fun m hm => lvl_isCell p N hcellK m hm
  -- the fibre coordinates of every level lie in the open unit interval
  have h01 : ∀ m (hm : m+1 ≤ N), ∀ z : Fin (p+m+1) → ℝ, z ∈ lvl p N κ (m+1) →
      z (Fin.last (p+m)) ∈ Set.Ioo (0:ℝ) 1 := by
    intro m hm z hz
    rw [hlvlMem_iff (m+1) hm z] at hz
    obtain ⟨w, hw⟩ := hz
    have hcoord := gluePt_idxL p N (m+1) hm z w (Fin.last (p+m))
    rw [← hcoord]
    have h2 := hcube hw
    have hidx : idxL p N (m+1) hm (Fin.last (p+m)) = Fin.natAdd p ⟨m, by omega⟩ :=
      Fin.ext (by simp [idxL, Fin.natAdd, Fin.last])
    rw [hidx]
    exact h2 ⟨m, by omega⟩
  -- (6) The fibre-end functions of the levels.
  have hLend : ∀ m : Fin N, ∃ (lo hi : (Fin (p + m.val) → ℝ) → ℝ),
      graphOf lo ∈ S.Ω (FAa m) ((FBb m).eval ![D, 1]) (p + m.val + 1) ∧
      graphOf hi ∈ S.Ω (FAa m) ((FBb m).eval ![D, 1]) (p + m.val + 1) ∧
      ∀ x : Fin (p + m.val) → ℝ, (∃ y : ℝ, Fin.snoc x y ∈ lvl p N κ (m.val+1)) →
        (∀ y : ℝ, Fin.snoc x y ∈ lvl p N κ (m.val+1) → lo x ≤ y ∧ y ≤ hi x) ∧
        (∀ u : ℝ, lo x < u → ∃ y : ℝ, Fin.snoc x y ∈ lvl p N κ (m.val+1) ∧ y < u) ∧
        (∀ u : ℝ, u < hi x → ∃ y : ℝ, Fin.snoc x y ∈ lvl p N κ (m.val+1) ∧ u < y) := by
    intro m
    have hmN : m.val + 1 ≤ N := by omega
    obtain ⟨lo, hi, h1, h2, h3⟩ :=
      hFE' m D 1 (lvl p N κ (m.val+1)) (hlvlOm (m.val+1) hmN) (h01 m.val hmN)
    exact ⟨lo, hi, h1, h2, h3⟩
  choose Lend Hend hLH using hLend
  -- (7) The geometry: the tower points lie in the levels of `κ`.
  have hgeom : ∀ m, m ≤ N → ∀ l ∈ Λ, ∀ t : Fin N → ℝ,
      (∀ i : Fin N, i.val < m → t i ∈ Set.Ioo (0:ℝ) 1) →
      towerPt p N Lend Hend m l t ∈ lvl p N κ m := by
    intro m
    induction m with
    | zero =>
        intro hm l hl t ht
        rw [towerPt_zero]
        rw [hlvlMem_iff 0 (Nat.zero_le N) l]
        obtain ⟨y, hy⟩ := hΛ l hl
        exact ⟨y, by rw [← append_eq_gluePt]; exact hy⟩
    | succ m ih =>
        intro hm l hl t ht
        have hmN : m < N := by omega
        have hx : towerPt p N Lend Hend m l t ∈ lvl p N κ m :=
          ih (by omega) l hl t (fun i hi => ht i (by omega))
        have hne : ∃ y : ℝ, Fin.snoc (towerPt p N Lend Hend m l t) y ∈ lvl p N κ (m+1) := by
          have h := hx
          rw [lvl_succ κ hmN] at h
          exact h
        obtain ⟨-, him, -⟩ :=
          cellFibre_param (n := p+m) (Z := lvl p N κ (m+1)) (lo := Lend ⟨m, hmN⟩)
            (hi := Hend ⟨m, hmN⟩) (hlvlCell (m+1) hm)
            (fun x hx => (hLH ⟨m, hmN⟩).2.2 x hx) (towerPt p N Lend Hend m l t) hne
        rw [towerPt_succ, tval_eq hmN]
        exact him (t ⟨m, hmN⟩) (ht ⟨m, hmN⟩ (Nat.lt_succ_self m))
  -- (8) The definability induction.
  have hdef : ∀ m, m ≤ N → ∀ i : Fin (p+m),
      graphOf (fun z : Fin (p+N) → ℝ => ptFlat p N Lend Hend m z i) ∈
        S.Ω (Aseq m) ((Bseq m).eval ![D, 1]) (p+N+1) := by
    intro m
    induction m with
    | zero =>
        intro hm i
        have h0 : graphOf (fun z : Fin (p+N) → ℝ => z (Fin.castAdd N i)) ∈
            S.Ω (p+N+1) 1 (p+N+1) := Work.WilkG4c.graphOf_coord_mem S (Fin.castAdd N i)
        refine Omega.mono h0 ?_ ?_
        · rw [show Aseq 0 = FA0 from rfl]
          have h1 := Nat.zero_le (∑ m : Fin N, FAa m)
          have h2 := Nat.zero_le (∑ m : Fin N, Cg1 m)
          have h3 := Nat.zero_le (∑ m : Fin N, Cg2 m)
          simp only [FA0]
          omega
        · rw [show Bseq 0 = MvPolynomial.C 1 from rfl]
          simp
    | succ m ih =>
        intro hm i
        have hmN : m < N := by omega
        have hIH := ih (by omega)
        have hg : graphOf (Lend ⟨m, hmN⟩) ∈ S.Ω (FAfun m) ((FBfun m).eval ![D, 1]) (p+m+1) := by
          have h1 := (hLH ⟨m, hmN⟩).1
          simpa only [FAfun, dif_pos hmN, FBfun] using h1
        have hH' : graphOf (Hend ⟨m, hmN⟩) ∈ S.Ω (FAfun m) ((FBfun m).eval ![D, 1]) (p+m+1) := by
          have h1 := (hLH ⟨m, hmN⟩).2.1
          simpa only [FAfun, dif_pos hmN, FBfun] using h1
        have hcompA := hCG' ⟨m, hmN⟩ (FAfun m) (Aseq m) ((FBfun m).eval ![D, 1])
          ((Bseq m).eval ![D, 1]) (Lend ⟨m, hmN⟩) (ptFlat p N Lend Hend m) hg hIH
        have hcompB := hCG' ⟨m, hmN⟩ (FAfun m) (Aseq m) ((FBfun m).eval ![D, 1])
          ((Bseq m).eval ![D, 1]) (Hend ⟨m, hmN⟩) (ptFlat p N Lend Hend m) hH' hIH
        -- the common format and degree of the three blocks
        have hA : graphOf (fun z : Fin (p+N) → ℝ => Lend ⟨m, hmN⟩ (ptFlat p N Lend Hend m z)) ∈
            S.Ω (FAfun m + Aseq m + Cg1 ⟨m, hmN⟩)
              ((FBfun m).eval ![D, 1] + (p+m) * (Bseq m).eval ![D, 1] + Cg2 ⟨m, hmN⟩ + 1)
              (p+N+1) :=
          Omega.mono hcompA le_rfl (Nat.le_succ _)
        have hB : graphOf (fun z : Fin (p+N) → ℝ => Hend ⟨m, hmN⟩ (ptFlat p N Lend Hend m z)) ∈
            S.Ω (FAfun m + Aseq m + Cg1 ⟨m, hmN⟩)
              ((FBfun m).eval ![D, 1] + (p+m) * (Bseq m).eval ![D, 1] + Cg2 ⟨m, hmN⟩ + 1)
              (p+N+1) :=
          Omega.mono hcompB le_rfl (Nat.le_succ _)
        have hT : graphOf (fun z : Fin (p+N) → ℝ => z (Fin.natAdd p ⟨m, hmN⟩)) ∈
            S.Ω (FAfun m + Aseq m + Cg1 ⟨m, hmN⟩)
              ((FBfun m).eval ![D, 1] + (p+m) * (Bseq m).eval ![D, 1] + Cg2 ⟨m, hmN⟩ + 1)
              (p+N+1) := by
          refine Omega.mono (Work.WilkG4c.graphOf_coord_mem S (Fin.natAdd p ⟨m, hmN⟩)) ?_ ?_
          · have h1 : FAfun m ≤ FA0 := hFAfun_le m
            have h2 : Cg1 ⟨m, hmN⟩ ≤ ∑ i : Fin N, Cg1 i :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
            have h4 : FA0 ≤ Aseq m := Aseq_ge m
            omega
          · omega
        have hnew := hLC (FAfun m + Aseq m + Cg1 ⟨m, hmN⟩) (FAfun m + Aseq m + Cg1 ⟨m, hmN⟩)
          (FAfun m + Aseq m + Cg1 ⟨m, hmN⟩)
          ((FBfun m).eval ![D, 1] + (p+m) * (Bseq m).eval ![D, 1] + Cg2 ⟨m, hmN⟩ + 1)
          ((FBfun m).eval ![D, 1] + (p+m) * (Bseq m).eval ![D, 1] + Cg2 ⟨m, hmN⟩ + 1)
          ((FBfun m).eval ![D, 1] + (p+m) * (Bseq m).eval ![D, 1] + Cg2 ⟨m, hmN⟩ + 1)
          (fun z : Fin (p+N) → ℝ => Lend ⟨m, hmN⟩ (ptFlat p N Lend Hend m z))
          (fun z : Fin (p+N) → ℝ => Hend ⟨m, hmN⟩ (ptFlat p N Lend Hend m z))
          (fun z : Fin (p+N) → ℝ => z (Fin.natAdd p ⟨m, hmN⟩)) hA hB hT
        have hfun : (fun z : Fin (p+N) → ℝ => ptFlat p N Lend Hend (m+1) z (Fin.last (p+m))) =
            (fun x : Fin (p+N) → ℝ =>
              Lend ⟨m, hmN⟩ (ptFlat p N Lend Hend m x)
              + (x (Fin.natAdd p ⟨m, hmN⟩))
                * (Hend ⟨m, hmN⟩ (ptFlat p N Lend Hend m x)
                  - Lend ⟨m, hmN⟩ (ptFlat p N Lend Hend m x))) := by
          funext z
          rw [ptFlat_last, tval_eq hmN]
          try rfl
        rw [← hfun] at hnew
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · -- the old coordinates
          have hval : (fun z : Fin (p+N) → ℝ => ptFlat p N Lend Hend (m+1) z (Fin.castSucc j)) =
              (fun z : Fin (p+N) → ℝ => ptFlat p N Lend Hend m z j) := by
            funext z
            rw [ptFlat_succ, Fin.snoc_castSucc]
          rw [hval]
          exact Omega.mono (hIH j) (Aseq_mono m) (Bseq_mono m)
        · -- the new coordinate
          refine Omega.mono hnew ?_ ?_
          · rw [Aseq_succ]
            have h1 : FAfun m ≤ FA0 := hFAfun_le m
            have h2 : Cg1 ⟨m, hmN⟩ ≤ ∑ i : Fin N, Cg1 i :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
            simp only [Fbig]
            omega
          · rw [Bseq_eval]
            have h1 : Cg2 ⟨m, hmN⟩ ≤ ∑ i : Fin N, Cg2 i :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
            have h2 : 3 * (FBfun m).eval ![D, 1] ≤ 3 * (FBfun m).eval ![D, 1] := le_rfl
            simp only [BD0]
            have h2 : 3 * ((p+m) * (Bseq m).eval ![D, 1]) ≤
                (3 * (p+N) + 3) * (Bseq m).eval ![D, 1] := by
              have h3 : 3 * (p+m) ≤ 3 * (p+N) + 3 := by omega
              calc 3 * ((p+m) * (Bseq m).eval ![D, 1])
                  = (3 * (p+m)) * (Bseq m).eval ![D, 1] := by ring
                _ ≤ (3 * (p+N) + 3) * (Bseq m).eval ![D, 1] := Nat.mul_le_mul_right _ h3
            omega
  -- (9) The parametrisation.
  refine ⟨fun l t j => towerPt p N Lend Hend N l t (Fin.natAdd p j), ?_, ?_, ?_, ?_⟩
  · intro j
    have h := hdef N le_rfl (Fin.natAdd p j)
    change famGraph (fun l t => towerPt p N Lend Hend N l t (Fin.natAdd p j)) ∈
      S.Ω (Aseq N) ((Bseq N).eval ![D, 1]) (p + N + 1)
    rw [Work.WilkG4c.famGraph_eq_graphOf_flatFun]
    exact h
  · intro l hl t ht
    have hz : towerPt p N Lend Hend N l t ∈ κ := by
      have h := hgeom N le_rfl l hl t (fun i hi => ht i)
      rwa [lvl_self] at h
    exact hcube hz
  · intro l hl t ht
    have hz : towerPt p N Lend Hend N l t ∈ κ := by
      have h := hgeom N le_rfl l hl t (fun i hi => ht i)
      rwa [lvl_self] at h
    rw [← towerPt_append]
    exact hz
  · intro l hl y hy
    have htarg : ∀ m, m ≤ N → targ p N m l y ∈ lvl p N κ m := by
      have key : ∀ d, ∀ m, m + d = N → targ p N m l y ∈ lvl p N κ m := by
        intro d
        induction d with
        | zero =>
            intro m hm
            have hm' : m = N := by omega
            subst hm'
            rw [lvl_self, targ_append]
            exact hy
        | succ d ih =>
            intro m hm
            have hlt : m < N := by omega
            rw [lvl_succ κ hlt]
            refine ⟨y ⟨m, hlt⟩, ?_⟩
            rw [← targ_succ hlt]
            exact ih (m+1) (by omega)
      intro m hm
      exact key (N - m) m (by omega)
    have key : ∀ m, m ≤ N → ∃ t : Fin N → ℝ,
        (∀ i : Fin N, i.val < m → t i ∈ Set.Ioo (0:ℝ) 1) ∧
        towerPt p N Lend Hend m l t = targ p N m l y := by
      intro m
      induction m with
      | zero =>
          intro hm
          exact ⟨fun _ => 1/2, fun i hi => by omega, rfl⟩
      | succ m ih =>
          intro hm
          have hmN : m < N := by omega
          obtain ⟨t, ht01, htpre⟩ := ih (by omega)
          have hmem : Fin.snoc (towerPt p N Lend Hend m l t) (y ⟨m, hmN⟩) ∈ lvl p N κ (m+1) := by
            have h1 : targ p N (m+1) l y ∈ lvl p N κ (m+1) := htarg (m+1) hm
            have h2 : targ p N (m+1) l y =
                Fin.snoc (towerPt p N Lend Hend m l t) (y ⟨m, hmN⟩) := by
              rw [targ_succ hmN, htpre]
            rwa [h2] at h1
          have hne : ∃ y : ℝ, Fin.snoc (towerPt p N Lend Hend m l t) y ∈ lvl p N κ (m+1) :=
            ⟨y ⟨m, hmN⟩, hmem⟩
          obtain ⟨-, -, hsurj⟩ :=
            cellFibre_param (n := p+m) (Z := lvl p N κ (m+1)) (lo := Lend ⟨m, hmN⟩)
              (hi := Hend ⟨m, hmN⟩) (hlvlCell (m+1) hm)
              (fun x hx => (hLH ⟨m, hmN⟩).2.2 x hx) (towerPt p N Lend Hend m l t) hne
          obtain ⟨τ, hτ01, hτeq⟩ := hsurj (y ⟨m, hmN⟩) hmem
          refine ⟨Function.update t ⟨m, hmN⟩ τ, ?_, ?_⟩
          · intro i hi
            by_cases h : i = ⟨m, hmN⟩
            · subst h
              rw [Function.update_self]
              exact hτ01
            · rw [Function.update_of_ne h]
              have hne : i.val ≠ m := fun h' => h (Fin.ext h')
              exact ht01 i (by omega)
          · rw [towerPt_succ]
            have hcongr : towerPt p N Lend Hend m l (Function.update t ⟨m, hmN⟩ τ) =
                towerPt p N Lend Hend m l t := by
              apply towerPt_congr
              intro i hi
              have hne : i ≠ ⟨m, hmN⟩ := fun h' =>
                absurd (show i.val = m from congrArg Fin.val h') (by omega)
              exact Function.update_of_ne hne τ t
            rw [hcongr]
            rw [show tval p N Lend Hend m (towerPt p N Lend Hend m l t)
                (Function.update t ⟨m, hmN⟩ τ) =
                Lend ⟨m, hmN⟩ (towerPt p N Lend Hend m l t)
                + τ * (Hend ⟨m, hmN⟩ (towerPt p N Lend Hend m l t)
                  - Lend ⟨m, hmN⟩ (towerPt p N Lend Hend m l t)) from by
              rw [tval_eq hmN, Function.update_self]]
            rw [← hτeq, targ_succ hmN, htpre]
    obtain ⟨t, ht01, htpre⟩ := key N le_rfl
    refine ⟨t, ?_, ?_⟩
    · intro i
      exact ht01 i i.isLt
    · funext j
      change towerPt p N Lend Hend N l t (Fin.natAdd p j) = y j
      have h1 : towerPt p N Lend Hend N l t (Fin.natAdd p j) =
          targ p N N l y (Fin.natAdd p j) := by rw [htpre]
      rw [h1]
      have h2 : targ p N N l y (Fin.natAdd p j) = y j := by
        have h3 := targ_tail N l y (⟨j.val, j.isLt⟩ : Fin N) j.isLt
        simpa using h3
      rw [h2]

end Work.WilG4c
