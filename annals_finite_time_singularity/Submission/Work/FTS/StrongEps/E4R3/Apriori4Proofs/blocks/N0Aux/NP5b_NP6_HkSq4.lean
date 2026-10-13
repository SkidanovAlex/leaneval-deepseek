import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.Maj4
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.NP5b_NP6_HkSq6
import Submission.Work.FTS.StrongPersist.L3Rhs.c2m_mul_HkSq_le
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.EllipticEst.UopHk.hkMemDzPth_of_shifted
import Submission.Work.FTS.EllipticEst.UopHk.L12_contDiffOn_reg
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

set_option maxHeartbeats 3200000

-- Level-four `HkSq` bounds for the two pieces
-- `NP5b α w = (-1)·(c2m θ · L₁₂(w) z · D_z w z θ)` and
-- `NP6 α w = (-1)·(c2m θ · L₁₂(F_* α) z · D_z w z θ)`
-- of the `N₀`-row (`Work.FTS.StrongPersist.H6Pair6Aux`), priced by `HkSq α 5 w`.
-- Route: verbatim the route of the level-six sibling
-- `...blocks.N0Aux.NP5b_NP6_HkSq6`, with the level-six radial engine `radialMaj6_split`
-- replaced by the level-four `Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj4`.
-- Write `NP5b α w = L₁₂(w) z · g z θ` with `g := fun z θ => -c2m θ * D_z w z θ`
-- (transfer by `HkSq_congr_open`), then
-- * `L3Rhs.ang_mul_HkSq_le 4` with `a := c2m`, `B := Cc` (hypotheses: `c2mJets`) gives
--   `HkMem α 4 g` and `HkSq α 4 g ≤ Cang·Cc²·HkSq α 4 (Dz w) ≤ Cang·Cc²·HkSq α 5 w`
--   (`H6Aux.HkSq_Dz_le_succ'`; `HkMem α 5 w` from `ClassC`);
-- * `radialMaj4` with `X := L₁₂w`, `B := CL·Xn α w` (`H6Pair6Aux.L12Sup4`,
--   `ContDiffOn ℝ 6 (L₁₂w) (Ioi 0)` from `UopHk.contDiffOn_L12_k`) gives
--   `HkSq α 4 (NP5b α w) ≤ (Maj4C+1)·(CL·Xn α w)²·HkSq α 4 g ≤ (Maj4C+1)CL²C₀²α⁴·Cang Cc²·HkSq α 5 w`.
-- * For `NP6`: the same `g`, but `X := fun z => L₁₂(F_* α) z`, whose `D_z`-jets of order `≤ 4`
--   are bounded either by the `α`-free constant `Kφ` of
--   `...blocks.N0Aux.NP5b_NP6_HkSq6.l12Fstar_dzdIter_uniform` (import that module) or by
--   `H6Pair6Aux.L12Sup4` with `B := CL·Xn α w`; `ContDiffOn ℝ 6 (L₁₂(F_* α)) (Ioi 0)` follows
--   from `Construction.L12_Fstar_eq` (`L₁₂(F_*) y = 2α/(1+y)` for `y > -1`) by
--   `ContDiffOn.congr`.
-- The "w vanishes off the open quadrant" hypothesis is NOT needed here.
theorem NP5b_NP6_HkSq4 (C₀ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 4 (Work.FTS.StrongPersist.H6Pair6Aux.NP5b α w)
        ≤ K * (1 + Work.Spaces.HkSq α 5 w) ∧
    Work.Spaces.HkSq α 4 (Work.FTS.StrongPersist.H6Pair6Aux.NP6 α w)
        ≤ K * (1 + Work.Spaces.HkSq α 5 w) := by
  obtain ⟨Cang, hCangpos, hCang⟩ := Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le 4
  obtain ⟨Cc, hCcpos, hCcsm, hCcabs, hCcjet⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.c2mJets
  obtain ⟨CL, hCLpos, hCL⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
  obtain ⟨Kφ, hKφpos, hKφ⟩ := l12Fstar_dzdIter_uniform
  have hMajpos : 0 < Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1 := by
    have := Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C_pos
    linarith
  have hK1pos : 0 < (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
      * CL ^ 2 * C₀ ^ 2 * Cang * Cc ^ 2 + 1 := by positivity
  have hK2pos : 0 < (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
      * Kφ ^ 2 * Cang * Cc ^ 2 + 1 := by positivity
  refine ⟨max ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
      * CL ^ 2 * C₀ ^ 2 * Cang * Cc ^ 2 + 1)
      ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
        * Kφ ^ 2 * Cang * Cc ^ 2 + 1), lt_max_of_lt_left hK1pos, ?_⟩
  intro α hαI w hcls hXw
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hcls.reg
  have hm7 : Work.Spaces.HkMem α 7 w := hcls.mem
  have hm6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 6 (by norm_num) hm7
  have hm5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 5 (by norm_num) hm7
  have hsmDz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz w) := hsmw.Dz
  have hm4Dz : Work.Spaces.HkMem α 4 (Work.Spaces.Dz w) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hsmw hm5
  have hDz4 : Work.Spaces.HkSq α 4 (Work.Spaces.Dz w) ≤ Work.Spaces.HkSq α 5 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_Dz_le_succ' α 4 hsmw hm5
  have hCsq : (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ C₀ ^ 2 * α ^ 4 := by
    calc (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ (C₀ * α ^ 2) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 w) hXw 2
      _ = C₀ ^ 2 * α ^ 4 := by ring
  have h5w : (0 : ℝ) ≤ Work.Spaces.HkSq α 5 w := Work.Spaces.HkSq_nonneg α 5 w
  have hH : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by linarith
  have hα4le : α ^ 4 ≤ 1 := pow_le_one₀ hα0.le hα1
  -- ## the angular multiplier `c₂ₘ` at level `4`
  have hCcjet4 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun x (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
        ≤ Cc * Real.sin (2 * θ) :=
    fun i hi1 hi4 θ hθ => hCcjet i hi1 (by omega) 0 θ hθ
  obtain ⟨hfa_mem, hfa_bd⟩ := hCang α hα0 hα1 Work.Construction.c2m Cc hCcpos hCcsm hCcabs
    hCcjet4 (Work.Spaces.Dz w) hsmDz hm4Dz
  -- ## the honest field `f = -c₂ₘ · D_z w`
  set f : ℝ → ℝ → ℝ := fun z θ => (-1) * (Work.Construction.c2m θ * Work.Spaces.Dz w z θ)
    with hfdef
  have hfsm : Work.FTS.EllipticEst.SmoothOpen f := by
    rw [hfdef]
    exact Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (-1)
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_snd
          Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m) hsmDz)
  have hfmem : Work.Spaces.HkMem α 4 f := by
    rw [hfdef]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-1) hfa_mem
  have hS4f : Work.Spaces.HkSq α 4 f ≤ Cang * Cc ^ 2 * Work.Spaces.HkSq α 5 w := by
    have hval : Work.Spaces.HkSq α 4 f
        = Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.c2m θ * Work.Spaces.Dz w z θ) := by
      rw [hfdef, Work.FTS.StrongEps.HkSq_const_mul]
      ring
    rw [hval]
    exact hfa_bd.trans (mul_le_mul_of_nonneg_left hDz4 (by positivity))
  -- ## the radial data of `radialMaj4`
  have hLcd : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 w z) (Set.Ioi 0) := by
    have h10 : ContDiffOn ℝ 10 (fun z => Work.Construction.L12 w z) (Set.Ioi 0) := by
      have h := Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 10 w hα0 hα1 hsmw hcls.mem10
        (by norm_num)
      refine h.congr (fun z _ => ?_)
      exact congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 w) z
    exact h10.of_le (by exact_mod_cast (by norm_num : 6 ≤ 10))
  have hjet : ∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 w z) z|
        ≤ CL * Work.FTS.Nonlin.Xn α w :=
    fun j hj z hz => hCL α w hα0 hα1 hsmw hm6 hcls.l12 j hj z hz
  have hCB : (0 : ℝ) ≤ CL * Work.FTS.Nonlin.Xn α w :=
    mul_nonneg hCLpos.le (Work.Spaces.HkNorm_nonneg α 4 w)
  have hsqCL : (CL * Work.FTS.Nonlin.Xn α w) ^ 2 ≤ CL ^ 2 * (C₀ ^ 2 * α ^ 4) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hCsq (sq_nonneg CL)
  -- ## `NP5b`
  have heq5b : Work.FTS.StrongPersist.H6Pair6Aux.NP5b α w
      = fun z θ => (fun z => Work.Construction.L12 w z) z * f z θ := by
    rw [hfdef]
    funext z θ
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP5b]
    ring
  have hmain5b :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj4 (α := α)
      (B := CL * Work.FTS.Nonlin.Xn α w) (X := fun z => Work.Construction.L12 w z)
      (f := f) hCB hLcd hfsm hfmem hjet
  have hbnd5b : Work.Spaces.HkSq α 4 (Work.FTS.StrongPersist.H6Pair6Aux.NP5b α w)
      ≤ ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
          * CL ^ 2 * C₀ ^ 2 * Cang * Cc ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
    rw [heq5b]
    calc Work.Spaces.HkSq α 4 (fun z θ => (fun z => Work.Construction.L12 w z) z * f z θ)
        ≤ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * (CL * Work.FTS.Nonlin.Xn α w) ^ 2 * Work.Spaces.HkSq α 4 f := hmain5b
      _ ≤ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * (CL ^ 2 * (C₀ ^ 2 * α ^ 4)) * (Cang * Cc ^ 2 * Work.Spaces.HkSq α 5 w) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsqCL hMajpos.le) hS4f
            (Work.Spaces.HkSq_nonneg α 4 f) (by positivity)
      _ = (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * CL ^ 2 * C₀ ^ 2 * Cang * Cc ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 5 w) := by ring
      _ ≤ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * CL ^ 2 * C₀ ^ 2 * Cang * Cc ^ 2 * (1 + Work.Spaces.HkSq α 5 w) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h1 : α ^ 4 * Work.Spaces.HkSq α 5 w ≤ 1 * Work.Spaces.HkSq α 5 w :=
            mul_le_mul_of_nonneg_right hα4le h5w
          linarith
      _ ≤ ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * CL ^ 2 * C₀ ^ 2 * Cang * Cc ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
          have hc : (0 : ℝ) ≤ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
              * CL ^ 2 * C₀ ^ 2 * Cang * Cc ^ 2 := by positivity
          nlinarith [hc, hH]
  -- ## `NP6`
  have hL12Fcd : ContDiffOn ℝ 6
      (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) (Set.Ioi 0) := by
    have hnum : ContDiffOn ℝ 6 (fun _ : ℝ => 2 * α) (Set.Ioi 0) := contDiffOn_const
    have hden : ContDiffOn ℝ 6 (fun z : ℝ => 1 + z) (Set.Ioi 0) :=
      (contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi 0)).add contDiffOn_id
    have hbase : ContDiffOn ℝ 6 (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi 0) :=
      hnum.div hden (fun z hz => by
        have hz' : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
        positivity)
    exact hbase.congr (fun z hz =>
      Work.Construction.L12_Fstar_eq hα0 hα1 (le_of_lt (Set.mem_Ioi.mp hz)))
  have hFjet : ∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j
        (fun y => Work.Construction.L12 (Work.Construction.Fstar α) y) z| ≤ Kφ :=
    fun j hj z hz => hKφ α hαI j (by omega) z hz
  have heq6 : Work.FTS.StrongPersist.H6Pair6Aux.NP6 α w
      = fun z θ => (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z
          * f z θ := by
    rw [hfdef]
    funext z θ
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP6, Work.FTS.StrongPersist.H6Pair6Aux.NA6]
    ring
  have hmain6 :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj4 (α := α) (B := Kφ)
      (X := fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
      (f := f) hKφpos.le hL12Fcd hfsm hfmem hFjet
  have hbnd6 : Work.Spaces.HkSq α 4 (Work.FTS.StrongPersist.H6Pair6Aux.NP6 α w)
      ≤ ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
          * Kφ ^ 2 * Cang * Cc ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
    rw [heq6]
    calc Work.Spaces.HkSq α 4 (fun z θ =>
            (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z * f z θ)
        ≤ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * Kφ ^ 2 * Work.Spaces.HkSq α 4 f := hmain6
      _ ≤ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * Kφ ^ 2 * (Cang * Cc ^ 2 * Work.Spaces.HkSq α 5 w) :=
          mul_le_mul_of_nonneg_left hS4f (by positivity)
      _ = (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * Kφ ^ 2 * Cang * Cc ^ 2 * Work.Spaces.HkSq α 5 w := by ring
      _ ≤ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * Kφ ^ 2 * Cang * Cc ^ 2 * (1 + Work.Spaces.HkSq α 5 w) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ ((Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
            * Kφ ^ 2 * Cang * Cc ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
          have hc : (0 : ℝ) ≤ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.Maj4C + 1)
              * Kφ ^ 2 * Cang * Cc ^ 2 := by positivity
          nlinarith [hc, hH]
  exact ⟨hbnd5b.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hH),
    hbnd6.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hH)⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
