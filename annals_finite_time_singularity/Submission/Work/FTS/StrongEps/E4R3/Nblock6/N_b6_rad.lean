import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Route
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.Defs
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNDefs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.N_b4
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.RadCoeffJets
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.RadPer
import Submission.Work.FTS.StrongPersist.H6Row6.fkFacts7
import Submission.Work.FTS.StrongPersist.H6Row6.fkH6_norm_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.hknorm_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.piecesC6
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.Maj6Split
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNAux
import Submission.Work.FTS.StrongEps.HkSq_const_mul
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dth_le
import Submission.Work.FTS.StrongLWP.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Nblock6.N_b6_rad` — the four radial pieces `NBlk α w Φs Φg k`, `k ∈ {12,13,14,15}`, at level 6

The four pieces are

* `k = 12`: `-½ · (FK w · D_θ w)` (both factors `w`-derived),
* `k = 13`: `-½ · (D_θ F_* · FK w)`,
* `k = 14`: `-½ · ((-2α) hKer · D_θ w)`,
* `k = 15`: `-½ · (FK F_* · D_θ F_*)`.

See `Route.lean` and `NOTES_N_b6_route.md` for the place of these four pieces in the level-6
semi-tame estimate of the `N`-block.  All four bounds are linear in `1 + HkSq α 7 w` (with a
coefficient depending only on `α`, `C₀`, `Ce`, `Cs`), which is stronger than the stated
`K(1+HkSq α 7 w) + K(1+HkSq α 6 w)²`.
-/

namespace Work.FTS.StrongEps.E4R3.Nblock6

open Work.FTS.Galerkin (Fn)
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Small helpers -/

/-- `HkSq α k F` is the square of `HkNorm α k F`. -/
private theorem hkSq_eq_norm_sq (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k F = (Work.Spaces.HkNorm α k F) ^ 2 := by
  rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k F)]

/-- `HkSq α 4 w = (Xn α w)²`, definitionally in `Xn`. -/
private theorem hkSq_four_eq_Xn_sq (α : ℝ) (w : Fn) :
    Work.Spaces.HkSq α 4 w = (Work.FTS.Nonlin.Xn α w) ^ 2 := by
  have h : Work.FTS.Nonlin.Xn α w = Work.Spaces.HkNorm α 4 w := rfl
  rw [h, ← hkSq_eq_norm_sq]

/-- `(HkNorm α 6 w)² = HkSq α 6 w`. -/
private theorem hkN_six_sq (α : ℝ) (w : Fn) :
    (Work.Spaces.HkNorm α 6 w) ^ 2 = Work.Spaces.HkSq α 6 w :=
  (hkSq_eq_norm_sq α 6 w).symm

/-- For `m ≤ 4` the `ℋ^m`-energy of `w` is `α`-small: `HkSq α m w ≤ C₀'²α⁴`. -/
private theorem hkSq_le_four {α C₀ : ℝ} {w : Fn}
    (hXw : Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2) {m : ℕ} (hm : m ≤ 4)
    (hmem : Work.Spaces.HkMem α 4 w) :
    Work.Spaces.HkSq α m w ≤ (max C₀ 0) ^ 2 * α ^ 4 := by
  have h1 : Work.Spaces.HkSq α m w ≤ Work.Spaces.HkSq α 4 w :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α hm hmem
  have h2 : Work.Spaces.HkSq α 4 w ≤ (max C₀ 0 * α ^ 2) ^ 2 := by
    rw [hkSq_four_eq_Xn_sq α w]
    refine pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 w) ?_ 2
    exact le_trans hXw (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg α))
  refine le_trans h1 (le_trans h2 (le_of_eq ?_))
  ring

/-- Absorbing a piece bound `x ≤ Kx (1 + H7)` into the statement's shape. -/
private theorem absorb {Ksum Kx H7 H6 x : ℝ} (hKx : Kx ≤ Ksum) (hKs : 0 ≤ Ksum) (h7 : 0 ≤ H7)
    (h6 : 0 ≤ H6) (hx : x ≤ Kx * (1 + H7)) :
    x ≤ Ksum * (1 + H7) + Ksum * (1 + H6) ^ 2 := by
  have h1 : 0 ≤ 1 + H7 := by linarith
  have h3 : Kx * (1 + H7) ≤ Ksum * (1 + H7) := mul_le_mul_of_nonneg_right hKx h1
  have h2 : 0 ≤ Ksum * (1 + H6) ^ 2 := mul_nonneg hKs (sq_nonneg _)
  linarith

/-- The `𝒲^{6,∞}`-priced level-6 product rule `hknorm_mul_of_WlInf6_cd6`, with the (proved but
hidden) threshold made explicit: it holds for every `0 < α ≤ 1`. -/
private theorem mulWl :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {f g : ℝ → ℝ → ℝ}, 0 < α → α ≤ 1 →
      ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.WlInfMem α 6 f →
      ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 6 g →
      Work.Spaces.HkMem α 6 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g := by
  obtain ⟨Cz, hCz, hZ⟩ := Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.zslot_le_winf6_cd6
  obtain ⟨CB, _hCB, hCBmean⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_w_mean_le6_cd6
  obtain ⟨Cm, hCm, hMx⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mslot_le_winf6_cd6 CB
  refine ⟨Real.sqrt ((7 * Cz + 49 * Cm) * 42701), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro α f g hα hα1 hfs hfw hgs hgm
  exact Work.FTS.StrongPersist.H6Rows.Npair6SupAux.hknorm_mul_aux6 hα hα1 hfs hfw hgs hgm
    hCz hCm
    (fun i hi z θ hz hθ0 hθ1 => hZ α f g hα hα1 hfs hfw hgs i hi z θ hz hθ0 hθ1)
    (fun I J hI hIJ z θ hz hθ0 hθ1 => hMx α f g hα hα1 hfs hfw hgs hgm
      (fun d hd z' θ' hz' hθ0' hθ1' => hCBmean α g d hα hα1 hgs hgm hd z' θ' hz' hθ0' hθ1')
      I J hI hIJ z θ hz hθ0 hθ1)

/-! ## The piece `k = 13`: `-½ · (D_θ F_* · FK w)` -/

private theorem b13 {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {w Φs Φg : Fn}, Work.FTS.ClassC.ClassC α w →
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 13)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) := by
  obtain ⟨Cmul, hCmulpos, hmul⟩ := mulWl
  obtain ⟨Cd, hCdpos, hDth⟩ := Work.FTS.StrongPersist.DthFstar_W6
  obtain ⟨C6, hC6pos, hFK6⟩ := Work.FTS.StrongPersist.H6Row6.fkH6_norm_le
  obtain ⟨Cfp, Xi, Cpow, hCfppos, hXipos, hCpownn, hFpfacts⟩ :=
    Work.FTS.StrongPersist.H6Row6.fkFacts7
  -- the smoothness and `𝒲^{6,∞}`-data of `D_θF_*`
  have hDthCD : ContDiffOn ℝ 6
      (Function.uncurry (Work.Spaces.Dth (Work.Construction.Fstar α)))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dth.of_le
      (by simp [Work.Stability.smoothOrder])
  obtain ⟨hDthMemW, hDthW⟩ := hDth α hα0 hα1
  set B : ℝ := Cmul * α ^ (-(1 / 2 : ℝ)) * (Cd * α ^ 2) * C6 with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCmulpos.le (Real.rpow_nonneg hα0.le _))
      (mul_nonneg hCdpos.le (sq_nonneg α))) hC6pos.le
  refine ⟨(1 / 4) * B ^ 2 + 1, by positivity, ?_⟩
  intro w Φs Φg hw
  have hmem6w : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 6 (by norm_num) hw.mem
  obtain ⟨hFKCD, hFKmem4, hFKn4, hFKmem6, hFKn6, hFKpt⟩ :=
    hFpfacts hα0 hα1 w ⟨hw.reg, hmem6w⟩ hw.mem hw.l12
  have hFK6b : Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK w z)
      ≤ C6 * Work.Spaces.HkNorm α 6 w := hFK6 α hα0 hα1 w hw.reg hmem6w
  obtain ⟨hmemProd, hProd⟩ := hmul hα0 hα1 hDthCD hDthMemW hFKCD hFKmem6
  have hmain : Work.Spaces.HkNorm α 6
      (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        * Work.Construction.FK w z) ≤ B * Work.Spaces.HkNorm α 6 w := by
    refine le_trans hProd ?_
    have h1 : Work.Spaces.WlInf α 6 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ Cd * α ^ 2 :=
      hDthW
    have hnn : 0 ≤ Cmul * α ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg hCmulpos.le (Real.rpow_nonneg hα0.le _)
    have hstep : Cmul * α ^ (-(1 / 2 : ℝ))
          * Work.Spaces.WlInf α 6 (Work.Spaces.Dth (Work.Construction.Fstar α))
          * Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK w z)
        ≤ Cmul * α ^ (-(1 / 2 : ℝ)) * (Cd * α ^ 2) * (C6 * Work.Spaces.HkNorm α 6 w) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left h1 hnn) hFK6b
        (Work.Spaces.HkNorm_nonneg α 6 _) ?_
      exact mul_nonneg (mul_nonneg hCmulpos.le (Real.rpow_nonneg hα0.le _))
        (mul_nonneg hCdpos.le (sq_nonneg α))
    calc Cmul * α ^ (-(1 / 2 : ℝ))
          * Work.Spaces.WlInf α 6 (Work.Spaces.Dth (Work.Construction.Fstar α))
          * Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK w z)
        ≤ Cmul * α ^ (-(1 / 2 : ℝ)) * (Cd * α ^ 2) * (C6 * Work.Spaces.HkNorm α 6 w) := hstep
      _ = B * Work.Spaces.HkNorm α 6 w := by rw [hBdef]; ring_nf
  have hsq : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 13)
      = (1 / 4) * (Work.Spaces.HkNorm α 6
          (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
            * Work.Construction.FK w z)) ^ 2 := by
    rw [show Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 13
        = fun z θ => (-(1 / 2)) * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ
            * Work.Construction.FK w z) from rfl]
    rw [Work.FTS.StrongEps.HkSq_const_mul,
      hkSq_eq_norm_sq α 6 (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        * Work.Construction.FK w z)]
    ring
  rw [hsq]
  have h7nn : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hb2 : (B * Work.Spaces.HkNorm α 6 w) ^ 2 = B ^ 2 * Work.Spaces.HkSq α 6 w := by
    rw [mul_pow, hkN_six_sq α w]
  have h1 : (1 / 4) * (Work.Spaces.HkNorm α 6
        (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * Work.Construction.FK w z)) ^ 2 ≤ (1 / 4) * (B * Work.Spaces.HkNorm α 6 w) ^ 2 := by
    have h := pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 _) hmain 2
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  have h2 : (1 / 4) * (B * Work.Spaces.HkNorm α 6 w) ^ 2
      = (1 / 4) * B ^ 2 * Work.Spaces.HkSq α 6 w := by rw [hb2]; ring
  have h67 : Work.Spaces.HkSq α 6 w ≤ Work.Spaces.HkSq α 7 w :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hw.mem
  have h3 : (1 / 4) * B ^ 2 * Work.Spaces.HkSq α 6 w ≤ (1 / 4) * B ^ 2 * (1 + Work.Spaces.HkSq α 7 w) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have h4 : (1 / 4) * B ^ 2 * (1 + Work.Spaces.HkSq α 7 w)
      ≤ ((1 / 4) * B ^ 2 + 1) * (1 + Work.Spaces.HkSq α 7 w) := by
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    linarith
  calc (1 / 4) * (Work.Spaces.HkNorm α 6
        (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * Work.Construction.FK w z)) ^ 2
      ≤ (1 / 4) * (B * Work.Spaces.HkNorm α 6 w) ^ 2 := h1
    _ = (1 / 4) * B ^ 2 * Work.Spaces.HkSq α 6 w := h2
    _ ≤ (1 / 4) * B ^ 2 * (1 + Work.Spaces.HkSq α 7 w) := h3
    _ ≤ ((1 / 4) * B ^ 2 + 1) * (1 + Work.Spaces.HkSq α 7 w) := h4

/-! ## The piece `k = 14`: `-½ · ((-2α) hKer · D_θ w)` -/

private theorem b14 {α C₀ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {w Φs Φg : Fn}, Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 14)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) := by
  obtain ⟨Cmag, hCmagpos, hmaj⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj6_split
  obtain ⟨Cc, hCcpos, hCc⟩ := Work.FTS.StrongEps.E4R3.Nblock6.RadCoeffJets
  set Bc : ℝ := Cc * (2 * α) with hBcdef
  have hBcnn : 0 ≤ Bc := by rw [hBcdef]; positivity
  set C4 : ℝ := (max C₀ 0) ^ 2 * α ^ 4 with hC4def
  have hC4nn : 0 ≤ C4 := by rw [hC4def]; positivity
  refine ⟨(1 / 4) * Cmag * (Bc ^ 2 * (1 + C4)) + 1, by positivity, ?_⟩
  intro w Φs Φg hw hXw
  set X : ℝ → ℝ := fun z => (-(2 * α)) * Work.Spaces.hKer z with hXdef
  set f : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.Dth w z θ with hfdef
  have hmem4w : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have hXcd : ContDiffOn ℝ 6 X (Set.Ioi 0) := by
    rw [hXdef]; exact hCc.2.2.2 (-(2 * α))
  have hXjet : ∀ j : ℕ, j ≤ 6 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j X z| ≤ Bc := by
    intro j hj z hz
    have h := hCc.2.2.1 (-(2 * α)) j hj z hz
    have habs : |(-(2 * α))| = 2 * α := by
      rw [abs_neg, abs_of_pos (by positivity)]
    rw [habs] at h
    rw [hXdef, hBcdef]
    exact h
  have hsmf : Work.FTS.EllipticEst.SmoothOpen f := by rw [hfdef]; exact hw.reg.Dth
  have hmf : Work.Spaces.HkMem α 6 f := by
    rw [hfdef]
    exact Work.FTS.IPGen.HkMem_Dth_le (by linarith) hw.reg hw.mem
  have hmain := hmaj α X f Bc Bc hXcd hsmf hmf hBcnn hBcnn
    (fun j hj z hz => hXjet j (by omega) z hz)
    (fun j hj z hz => hXjet j hj z hz)
  have h6 : Work.Spaces.HkSq α 6 f ≤ Work.Spaces.HkSq α 7 w := by
    rw [hfdef]
    exact Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα0 6 hw.mem
  have h2 : Work.Spaces.HkSq α 2 f ≤ C4 := by
    rw [hfdef, hC4def]
    refine le_trans (Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα0 2
      (Work.FTS.OpenPkg.HkMem_mono_open hw.reg 3 (by norm_num) hw.mem)) ?_
    exact hkSq_le_four hXw (m := 3) (by norm_num) hmem4w
  have hsq : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 14)
      = (1 / 4) * Work.Spaces.HkSq α 6 (fun z θ => X z * f z θ) := by
    rw [show Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 14
        = fun z θ => (1 / 2) * (X z * f z θ) from rfl]
    rw [Work.FTS.StrongEps.HkSq_const_mul]
    ring
  rw [hsq]
  have h7nn : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hB2 : (0 : ℝ) ≤ Bc ^ 2 := sq_nonneg Bc
  have hb1 : Bc ^ 2 * Work.Spaces.HkSq α 6 f ≤ Bc ^ 2 * Work.Spaces.HkSq α 7 w :=
    mul_le_mul_of_nonneg_left h6 hB2
  have hb2 : Bc ^ 2 * Work.Spaces.HkSq α 2 f ≤ Bc ^ 2 * C4 := mul_le_mul_of_nonneg_left h2 hB2
  have hstep1 : (1 / 4) * Work.Spaces.HkSq α 6 (fun z θ => X z * f z θ)
      ≤ (1 / 4) * (Cmag * (Bc ^ 2 * (Work.Spaces.HkSq α 7 w + C4))) := by
    have hsum : Bc ^ 2 * Work.Spaces.HkSq α 6 f + Bc ^ 2 * Work.Spaces.HkSq α 2 f
        ≤ Bc ^ 2 * (Work.Spaces.HkSq α 7 w + C4) := by linarith
    have h1 : Cmag * (Bc ^ 2 * Work.Spaces.HkSq α 6 f + Bc ^ 2 * Work.Spaces.HkSq α 2 f)
        ≤ Cmag * (Bc ^ 2 * (Work.Spaces.HkSq α 7 w + C4)) :=
      mul_le_mul_of_nonneg_left hsum hCmagpos.le
    refine le_trans (le_trans (mul_le_mul_of_nonneg_left hmain (by norm_num)) ?_) le_rfl
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  have hstep2 : (1 / 4) * (Cmag * (Bc ^ 2 * (Work.Spaces.HkSq α 7 w + C4)))
      ≤ (1 / 4) * Cmag * (Bc ^ 2 * ((1 + C4) * (1 + Work.Spaces.HkSq α 7 w))) := by
    have hkey : Bc ^ 2 * (Work.Spaces.HkSq α 7 w + C4)
        ≤ Bc ^ 2 * ((1 + C4) * (1 + Work.Spaces.HkSq α 7 w)) := by
      refine mul_le_mul_of_nonneg_left ?_ hB2
      nlinarith [h7nn, hC4nn]
    calc (1 / 4) * (Cmag * (Bc ^ 2 * (Work.Spaces.HkSq α 7 w + C4)))
        = (1 / 4 * Cmag) * (Bc ^ 2 * (Work.Spaces.HkSq α 7 w + C4)) := by ring
      _ ≤ (1 / 4 * Cmag) * (Bc ^ 2 * ((1 + C4) * (1 + Work.Spaces.HkSq α 7 w))) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (1 / 4) * Cmag * (Bc ^ 2 * ((1 + C4) * (1 + Work.Spaces.HkSq α 7 w))) := by ring
  have hstep3 : (1 / 4) * Cmag * (Bc ^ 2 * ((1 + C4) * (1 + Work.Spaces.HkSq α 7 w)))
      = ((1 / 4) * Cmag * (Bc ^ 2 * (1 + C4))) * (1 + Work.Spaces.HkSq α 7 w) := by ring
  have hstep4 : ((1 / 4) * Cmag * (Bc ^ 2 * (1 + C4))) * (1 + Work.Spaces.HkSq α 7 w)
      ≤ ((1 / 4) * Cmag * (Bc ^ 2 * (1 + C4)) + 1) * (1 + Work.Spaces.HkSq α 7 w) := by
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    linarith
  calc (1 / 4) * Work.Spaces.HkSq α 6 (fun z θ => X z * f z θ)
      ≤ (1 / 4) * (Cmag * (Bc ^ 2 * (Work.Spaces.HkSq α 7 w + C4))) := hstep1
    _ ≤ (1 / 4) * Cmag * (Bc ^ 2 * ((1 + C4) * (1 + Work.Spaces.HkSq α 7 w))) := hstep2
    _ = ((1 / 4) * Cmag * (Bc ^ 2 * (1 + C4))) * (1 + Work.Spaces.HkSq α 7 w) := hstep3
    _ ≤ ((1 / 4) * Cmag * (Bc ^ 2 * (1 + C4)) + 1) * (1 + Work.Spaces.HkSq α 7 w) := hstep4

/-! ## The piece `k = 15`: `-½ · (FK F_* · D_θ F_*)` -/

private theorem b15 {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {w Φs Φg : Fn},
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 15)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) := by
  obtain ⟨Cmag, hCmagpos, hmaj⟩ :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.radialMaj6_split
  obtain ⟨Cc, hCcpos, hCc⟩ := Work.FTS.StrongEps.E4R3.Nblock6.RadCoeffJets
  obtain ⟨Cslot, hCslotpos, hslot⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6SupAux.starSlotShift
  obtain ⟨-, hDthSlot, -⟩ := hslot α ⟨hα0, hα1⟩
  obtain ⟨hfsm, hfmem, hfnorm⟩ := hDthSlot
  set X : ℝ → ℝ := fun z => -α / (1 + z) with hXdef
  set f : ℝ → ℝ → ℝ :=
    fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ with hfdef
  set Bc : ℝ := Cc * α with hBcdef
  set P : ℝ := (Cslot * α ^ (-(1 : ℝ))) ^ 2 with hPdef
  have hBcnn : 0 ≤ Bc := by rw [hBcdef]; positivity
  have hPnn : 0 ≤ P := by rw [hPdef]; positivity
  refine ⟨Cmag * (Bc ^ 2 * (2 * P)) + 1, by positivity, ?_⟩
  intro w Φs Φg
  have hXcd : ContDiffOn ℝ 6 X (Set.Ioi 0) := by
    rw [hXdef]; exact hCc.2.1 (-α)
  have hXjet : ∀ j : ℕ, j ≤ 6 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j X z| ≤ Bc := by
    intro j hj z hz
    have h := hCc.1 (-α) j hj z hz
    rw [abs_neg, abs_of_pos hα0] at h
    rw [hXdef, hBcdef]
    exact h
  have hmain := hmaj α X f Bc Bc hXcd hfsm hfmem hBcnn hBcnn
    (fun j hj z hz => hXjet j (by omega) z hz)
    (fun j hj z hz => hXjet j hj z hz)
  have h6f : Work.Spaces.HkSq α 6 f ≤ P := by
    rw [hPdef, hkSq_eq_norm_sq α 6 f]
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 f) hfnorm 2
  have h2f : Work.Spaces.HkSq α 2 f ≤ P :=
    le_trans (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hfmem) h6f
  have heq : Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 15
      = fun z θ => X z * f z θ := by
    funext z θ
    simp only [Work.FTS.StrongEps.ClassCRHS.NBlk, hXdef, hfdef]
    rw [Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα0 hα1]
    by_cases hz : (1 : ℝ) + z = 0
    · have hz1 : z = -1 := by linarith
      subst hz1
      norm_num
    · field_simp <;> ring
  rw [heq]
  have h7nn : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hB2 : (0 : ℝ) ≤ Bc ^ 2 := sq_nonneg Bc
  have hb1 : Bc ^ 2 * Work.Spaces.HkSq α 6 f ≤ Bc ^ 2 * P := mul_le_mul_of_nonneg_left h6f hB2
  have hb2 : Bc ^ 2 * Work.Spaces.HkSq α 2 f ≤ Bc ^ 2 * P := mul_le_mul_of_nonneg_left h2f hB2
  have hstep1 : Work.Spaces.HkSq α 6 (fun z θ => X z * f z θ)
      ≤ Cmag * (Bc ^ 2 * (2 * P)) := by
    have hsum : Bc ^ 2 * Work.Spaces.HkSq α 6 f + Bc ^ 2 * Work.Spaces.HkSq α 2 f
        ≤ Bc ^ 2 * (2 * P) := by linarith
    exact le_trans hmain (mul_le_mul_of_nonneg_left hsum hCmagpos.le)
  have hstep2 : Cmag * (Bc ^ 2 * (2 * P)) ≤ (Cmag * (Bc ^ 2 * (2 * P)) + 1)
      * (1 + Work.Spaces.HkSq α 7 w) := by
    have h1 : Cmag * (Bc ^ 2 * (2 * P)) ≤ Cmag * (Bc ^ 2 * (2 * P)) + 1 := by linarith
    have h2 : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 7 w := by linarith
    calc Cmag * (Bc ^ 2 * (2 * P)) ≤ Cmag * (Bc ^ 2 * (2 * P)) + 1 := h1
      _ ≤ (Cmag * (Bc ^ 2 * (2 * P)) + 1) * (1 + Work.Spaces.HkSq α 7 w) := by
          nth_rewrite 1 [show Cmag * (Bc ^ 2 * (2 * P)) + 1
              = (Cmag * (Bc ^ 2 * (2 * P)) + 1) * 1 from (mul_one _).symm]
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
  exact le_trans hstep1 hstep2

/-! ## The piece `k = 12`: `-½ · (FK w · D_θ w)` -/

private theorem b12 {α C₀ : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {w Φs Φg : Fn}, Work.FTS.ClassC.ClassC α w →
      Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 12)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) := by
  obtain ⟨Cper, hCperpos, hper⟩ := Work.FTS.StrongEps.E4R3.Nblock6.RadPer
  obtain ⟨Cj, hCjpos, hjet⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
  set C0m : ℝ := max C₀ 0 with hC0mdef
  have hC0mnn : 0 ≤ C0m := by rw [hC0mdef]; exact le_max_right _ _
  set Q : ℝ := C0m ^ 2 * α ^ 4 with hQdef
  have hQnn : 0 ≤ Q := by rw [hQdef]; positivity
  refine ⟨(1 / 4) * Cper * (7 * (Cj * Q)) + 1, by positivity, ?_⟩
  intro w Φs Φg hw hXw
  -- the datum `f = D_θ w`
  have hsmf : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth w) := hw.reg.Dth
  have hm6f : Work.Spaces.HkMem α 6 (Work.Spaces.Dth w) :=
    Work.FTS.IPGen.HkMem_Dth_le (by linarith) hw.reg hw.mem
  -- the radial factor `FK w` is `C⁶` on `(0,∞)`
  have hCD2 : ContDiffOn ℝ 6
      (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK w z))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Rows.co6_FK_radial hα0 hα1 hw.reg hw.mem
  have hXcd : ContDiffOn ℝ 6 (fun z => Work.Construction.FK w z) (Set.Ioi 0) := by
    have hφ : ContDiffOn ℝ 6 (fun z : ℝ => (z, (1 : ℝ))) (Set.Ioi (0 : ℝ)) :=
      (contDiff_id.prodMk contDiff_const).contDiffOn
    have hmap : Set.MapsTo (fun z : ℝ => (z, (1 : ℝ))) (Set.Ioi (0 : ℝ))
        Work.FTS.EllipticEst.Q0 := fun z hz =>
      ⟨hz, by norm_num, by linarith [Real.pi_gt_three]⟩
    exact (hCD2.comp hφ hmap).congr (fun z _ => rfl)
  -- the a.e. jet bounds
  have hjet' : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), ∀ b : ℕ, b ≤ 6 →
      (Work.Elliptic.DzdIter b (fun z => Work.Construction.FK w z) z) ^ 2
        ≤ Cj * Work.Spaces.HkSq α (b + 1) w := by
    have h1 : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        ∀ b ∈ Finset.range 7,
        (Work.Elliptic.DzdIter b (fun z => Work.Construction.FK w z) z) ^ 2
          ≤ Cj * Work.Spaces.HkSq α (b + 1) w := by
      rw [Finset.eventually_all]
      intro b hb7
      have hb6 : b ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp hb7)
      have h := hjet hα0 hw.reg
        (Work.FTS.OpenPkg.HkMem_mono_open hw.reg 6 (by norm_num) hw.mem) hw.mem b hb6
      simpa only [Work.Elliptic.DzIter_rad] using h
    refine h1.mono (fun z hz b hb6 => hz b (Finset.mem_range.mpr (by omega)))
  have hB0 : ∀ b : ℕ, 0 ≤ Cj * Work.Spaces.HkSq α (b + 1) w := fun b =>
    mul_nonneg hCjpos.le (Work.Spaces.HkSq_nonneg α (b + 1) w)
  have hmain := hper hXcd hsmf hm6f hB0 hjet'
  -- the per-`b` bound
  have hterm : ∀ b ∈ Finset.range 7,
      (Cj * Work.Spaces.HkSq α (b + 1) w) * Work.Spaces.HkSq α (6 - b) (Work.Spaces.Dth w)
        ≤ Cj * Q * (1 + Work.Spaces.HkSq α 7 w) := by
    intro b hb7
    have hb6 : b ≤ 6 := Nat.le_of_lt_succ (Finset.mem_range.mp hb7)
    have hD : Work.Spaces.HkSq α (6 - b) (Work.Spaces.Dth w) ≤ Work.Spaces.HkSq α (7 - b) w := by
      have h := Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα0 (6 - b)
        (Work.FTS.OpenPkg.HkMem_mono_open hw.reg (6 - b + 1) (by omega) hw.mem)
      rwa [show 6 - b + 1 = 7 - b from by omega] at h
    have hDnn : 0 ≤ Work.Spaces.HkSq α (6 - b) (Work.Spaces.Dth w) :=
      Work.Spaces.HkSq_nonneg α (6 - b) _
    have hleft : (0 : ℝ) ≤ Cj * Work.Spaces.HkSq α (b + 1) w :=
      mul_nonneg hCjpos.le (Work.Spaces.HkSq_nonneg α (b + 1) w)
    have step1 : (Cj * Work.Spaces.HkSq α (b + 1) w) * Work.Spaces.HkSq α (6 - b) (Work.Spaces.Dth w)
        ≤ (Cj * Work.Spaces.HkSq α (b + 1) w) * Work.Spaces.HkSq α (7 - b) w :=
      mul_le_mul_of_nonneg_left hD hleft
    by_cases hb3 : b ≤ 3
    · -- `b ≤ 3`: the `ℋ^{b+1}`-factor is `α`-small
      have hS : Work.Spaces.HkSq α (b + 1) w ≤ Q := by
        rw [hQdef]
        exact hkSq_le_four hXw (m := b + 1) (by omega)
          (Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem)
      have hT : Work.Spaces.HkSq α (7 - b) w ≤ 1 + Work.Spaces.HkSq α 7 w := by
        have h := Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (show 7 - b ≤ 7 by omega) hw.mem
        linarith [Work.Spaces.HkSq_nonneg α 7 w]
      have h1 : (Cj * Work.Spaces.HkSq α (b + 1) w) * Work.Spaces.HkSq α (7 - b) w
          ≤ (Cj * Q) * (1 + Work.Spaces.HkSq α 7 w) := by
        refine mul_le_mul ?_ hT (Work.Spaces.HkSq_nonneg α (7 - b) w) ?_
        · exact mul_le_mul_of_nonneg_left hS hCjpos.le
        · exact mul_nonneg hCjpos.le hQnn
      exact le_trans step1 h1
    · -- `4 ≤ b`: the `ℋ^{7-b}`-factor is `α`-small
      have hS : Work.Spaces.HkSq α (7 - b) w ≤ Q := by
        rw [hQdef]
        exact hkSq_le_four hXw (m := 7 - b) (by omega)
          (Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem)
      have hT : Work.Spaces.HkSq α (b + 1) w ≤ 1 + Work.Spaces.HkSq α 7 w := by
        have h := Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (show b + 1 ≤ 7 by omega) hw.mem
        linarith [Work.Spaces.HkSq_nonneg α 7 w]
      have h1 : (Cj * Work.Spaces.HkSq α (b + 1) w) * Work.Spaces.HkSq α (7 - b) w
          ≤ (Cj * Q) * (1 + Work.Spaces.HkSq α 7 w) := by
        calc (Cj * Work.Spaces.HkSq α (b + 1) w) * Work.Spaces.HkSq α (7 - b) w
            ≤ (Cj * (1 + Work.Spaces.HkSq α 7 w)) * Q := by
              exact mul_le_mul (mul_le_mul_of_nonneg_left hT hCjpos.le) hS
                (Work.Spaces.HkSq_nonneg α (7 - b) w)
                (mul_nonneg hCjpos.le (by linarith [Work.Spaces.HkSq_nonneg α 7 w]))
          _ = (Cj * Q) * (1 + Work.Spaces.HkSq α 7 w) := by ring
      exact le_trans step1 h1
  have hsum : (∑ b ∈ Finset.range 7,
        (Cj * Work.Spaces.HkSq α (b + 1) w) * Work.Spaces.HkSq α (6 - b) (Work.Spaces.Dth w))
      ≤ 7 * (Cj * Q * (1 + Work.Spaces.HkSq α 7 w)) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_num
  have hsq : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 12)
      = (1 / 4) * Work.Spaces.HkSq α 6
          (fun z θ => Work.Construction.FK w z * Work.Spaces.Dth w z θ) := by
    rw [show Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 12
        = fun z θ => (-(1 / 2)) * (Work.Construction.FK w z * Work.Spaces.Dth w z θ) from rfl]
    rw [Work.FTS.StrongEps.HkSq_const_mul]
    ring
  rw [hsq]
  have h7nn : 0 ≤ Work.Spaces.HkSq α 7 w := Work.Spaces.HkSq_nonneg α 7 w
  have hbig : Work.Spaces.HkSq α 6
        (fun z θ => Work.Construction.FK w z * Work.Spaces.Dth w z θ)
      ≤ Cper * (7 * (Cj * Q * (1 + Work.Spaces.HkSq α 7 w))) := by
    refine le_trans hmain (mul_le_mul_of_nonneg_left hsum hCperpos.le)
  calc (1 / 4) * Work.Spaces.HkSq α 6
        (fun z θ => Work.Construction.FK w z * Work.Spaces.Dth w z θ)
      ≤ (1 / 4) * (Cper * (7 * (Cj * Q * (1 + Work.Spaces.HkSq α 7 w)))) :=
        mul_le_mul_of_nonneg_left hbig (by norm_num)
    _ = ((1 / 4) * Cper * (7 * (Cj * Q))) * (1 + Work.Spaces.HkSq α 7 w) := by ring
    _ ≤ ((1 / 4) * Cper * (7 * (Cj * Q)) + 1) * (1 + Work.Spaces.HkSq α 7 w) := by
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        linarith

/-! ## The target -/

theorem N_b6_rad : ∀ C₀ Ce Cs : ℝ, ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∃ K : ℝ, 0 < K ∧
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
    Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    (∀ k ∈ ({12, 13, 14, 15} : Finset ℕ),
      Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
        ≤ K * (1 + Work.Spaces.HkSq α 7 w) + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2) := by
  intro C₀ Ce Cs α hαIoc
  obtain ⟨hα0, hα1⟩ := Set.mem_Ioc.mp hαIoc
  obtain ⟨K12, hK12pos, hb12⟩ := b12 (C₀ := C₀) hα0 hα1
  obtain ⟨K13, hK13pos, hb13⟩ := b13 hα0 hα1
  obtain ⟨K14, hK14pos, hb14⟩ := b14 (C₀ := C₀) hα0 hα1
  obtain ⟨K15, hK15pos, hb15⟩ := b15 hα0 hα1
  have hKsum : 0 ≤ K12 + K13 + K14 + K15 + 1 := by linarith
  refine ⟨K12 + K13 + K14 + K15 + 1, by linarith, ?_⟩
  intro Φs w Φg hw hXw hz hell hK6 hstar k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact absorb (Kx := K12) (hKs := hKsum) (H6 := Work.Spaces.HkSq α 6 w) (by linarith)
      (Work.Spaces.HkSq_nonneg α 7 w) (Work.Spaces.HkSq_nonneg α 6 w) (hb12 hw hXw)
  · exact absorb (Kx := K13) (hKs := hKsum) (H6 := Work.Spaces.HkSq α 6 w) (by linarith)
      (Work.Spaces.HkSq_nonneg α 7 w) (Work.Spaces.HkSq_nonneg α 6 w) (hb13 hw)
  · exact absorb (Kx := K14) (hKs := hKsum) (H6 := Work.Spaces.HkSq α 6 w) (by linarith)
      (Work.Spaces.HkSq_nonneg α 7 w) (Work.Spaces.HkSq_nonneg α 6 w) (hb14 hw hXw)
  · exact absorb (Kx := K15) (hKs := hKsum) (H6 := Work.Spaces.HkSq α 6 w) (by linarith)
      (Work.Spaces.HkSq_nonneg α 7 w) (Work.Spaces.HkSq_nonneg α 6 w) (hb15)

end Work.FTS.StrongEps.E4R3.Nblock6
