/-
# `E4R3/N4C/rows/rowsN2a` — rows 12 and 13 of the honest (class-`C`) §8 table

This module proves the two `N₂`-rows of the honest row table `VocabO2.NRows2` in the class-`C`
context `N4C.CtxT`, with the honest clause bundle `N4C.N4ExtraH`:

* **row 12** (`N₂^{gg} = -2·𝒰(Φ̃_g)·∂_θg`): `|⟨N₂^{gg}, g⟩| ≤ K α^{-1/2} |g|_{ℋ⁴}³`;
* **row 13** (`N₂^{g*} = -2·𝒰(Φ̃_g)·∂_θF_*`): `|N₂^{g*}|_{ℋ⁴} ≤ K α^{3/2} |g|_{ℋ⁴}`.

The proofs are the honest counterparts of the frozen (`GalClass`) rows
`Work.FTS.NonlinRows.NRow12`/`NRow13`.  The only structural change is where the data comes from:

* row 12: the coefficient `coef = -2·(𝒰(Φ̃_g)/sin 2θ)` is `ℋ⁴` by `EllPkgGo.U`; the transport
  clause `t1` of `N4ExtraH` needs (in place of `RegQ α 4 g`) the three honest facts
  `SmoothOpen g`, `HkMem α 4 g`, `DecayAll 4 g`, all supplied by the projections of `CtxT`;
  the identification of `N₂^{gg}` with `coef·D_θg` is fed to `N4ExtraH.congr` *and* used to
  transfer the `ℋ⁴`-honesty (`HkMem_congr_Ioi`) and the `SmoothOpen`-honesty
  (`EllipticEst.SmoothOpen.congr`) — the latter is needed because `N4ExtraH.congr` asks for
  `HQo`, unlike the frozen `N4Extra'.congr` which takes bare `HkMem`;
* row 13: the coefficient is again `EllPkgGo.U`, but the slot `∂_θF_*` is priced by the
  `𝒲^{4,∞}`-clause `N4Norm'.wprod` (`DthFstar_W`), with the norm transferred along the open
  quadrant (`HkSq_congr_open`).

Everything is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.Hon
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.HonDecay
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.Coercivity.HkMem_congr_Ioi
import Submission.Work.FTS.Nonlinear.Pieces.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C.rows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
-- row 13 does not use the clause bundle `hE`; the hypothesis is kept for uniformity with row 12
-- (and with the frozen `NonlinRows.NRow13`).
set_option linter.unusedVariables false

/-! ## Two closure lemmas for `SmoothOpen` -/

private theorem smoothOpen_mul {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  have h : Function.uncurry (fun z θ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.mul hg

private theorem smoothOpen_const_mul (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  have h : Function.uncurry (fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact contDiffOn_const.mul hf

/-! ## Row 12 — the pairing bound for `N₂^{gg}` -/

private theorem rowsN2aRow12 (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N2gg α g Φg) g|
          ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
  obtain ⟨hCt, _hα₂⟩ := hE.pos
  have hmax : 0 < max Ce 1 := lt_of_lt_of_le zero_lt_one (le_max_right Ce 1)
  refine ⟨2 * Ct * max Ce 1 + 1, ?_, ?_⟩
  · have : 0 < 2 * Ct * max Ce 1 := mul_pos (mul_pos (by norm_num) hCt) hmax
    linarith
  · intro α g Φs Φg hctx
    have hα : 0 < α := hctx.hα
    have hαα₂ : α ≤ α₂ := hctx.hαα₂
    have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
    have hsoG : Work.FTS.EllipticEst.SmoothOpen g := hctx.hSmoothOpen
    have hmem4G : Work.Spaces.HkMem α 4 g := hctx.hkMem4
    have hdecG : Work.Spaces.DecayAll 4 g := hctx.hdecay
    have hqoDth : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dth g) := hctx.hqoDth
    have hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg := hctx.hell
    -- the coefficient `coef = -2·(𝒰(Φ̃_g)/sin 2θ)` of the transport clause `t1`
    set coef : Fn := fun z θ => -2 * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg)
      z θ / Work.Construction.s2 θ) with hcoef
    have hcoefSm : Work.FTS.EllipticEst.SmoothOpen coef := by
      rw [hcoef]; exact smoothOpen_const_mul (-2) hell.U.1.1
    have hcoefHQo : Work.FTS.VocabO.HQo α 4 coef := by
      refine ⟨hcoefSm, ?_⟩
      rw [hcoef]
      exact Work.FTS.LocData.HkMem_const_mul α 4 (-2) hell.U.1.2
    -- the honest product `coef · D_θ g`, by the `ℋ⁴`-product rule
    have hprod := hN.prod α hIoc coef (Work.Spaces.Dth g) hcoefHQo hqoDth
    have hprodSm : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => coef z θ * Work.Spaces.Dth g z θ) :=
      smoothOpen_mul hcoefSm hsoG.Dth
    -- the two functions agree on `(0,∞) × [0,π/2]`
    have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
        (fun z θ => coef z θ * Work.Spaces.Dth g z θ) z θ
          = Work.FTS.Nonlin.N2gg α g Φg z θ := by
      intro z _hz θ hθ
      have hv1 : Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z 0 = 0 :=
        hell.vanishU.1 z
      have hv2 : Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z (π / 2) = 0 :=
        hell.vanishU.2 z
      have hsin : Real.sin (2 * (π / 2)) = 0 := by
        rw [show 2 * (π / 2) = Real.pi by ring, Real.sin_pi]
      simp only [hcoef, Work.FTS.Nonlin.N2gg, Work.FTS.Nonlin.PhiTg, Work.Spaces.Dth,
        Work.Spaces.pth, Work.Construction.s2_eq]
      rcases eq_or_lt_of_le hθ.1 with h0 | hpos
      · -- `θ = 0`: both sides are `0`
        subst h0
        simp [hv1]
      · rcases eq_or_lt_of_le hθ.2 with hpi | hlt
        · -- `θ = π/2`: both sides are `0`
          subst hpi
          simp [hv2, hsin]
        · -- interior: cancel `sin 2θ`
          have hs : Real.sin (2 * θ) ≠ 0 :=
            ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
          field_simp
    -- the `ℋ⁴`-honesty of `N₂^{gg}`, transferred from the honest product
    have hmemN2 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2gg α g Φg) :=
      Work.Coercivity.HkMem_congr_Ioi α 4 hprod.1 hpt
    -- and the `SmoothOpen`-honesty, likewise
    have hsoN2 : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2gg α g Φg) :=
      Work.FTS.EllipticEst.SmoothOpen.congr hprodSm
        (fun z θ hz hθ0 hθ1 =>
          hpt z (Set.mem_Ioi.mpr hz) θ ⟨le_of_lt hθ0, le_of_lt hθ1⟩)
    -- `IP` only depends on the values on the open quadrant
    have hIPeq : IP α (Work.FTS.Nonlin.N2gg α g Φg) g
        = IP α (fun z θ => coef z θ * Work.Spaces.Dth g z θ) g := by
      refine hE.congr α hIoc _ _ g ⟨hsoN2, hmemN2⟩ ⟨hprodSm, hprod.1⟩ ⟨hsoG, hmem4G⟩ ?_
      intro z θ hQd
      exact (hpt z hQd.1 θ ⟨le_of_lt hQd.2.1, le_of_lt hQd.2.2⟩).symm
    rw [hIPeq]
    -- the transport clause `t1`
    have ht1 := hE.t1 α hIoc coef g hcoefHQo hsoG hmem4G hdecG
    have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hrp : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    -- the norm of the coefficient
    have hXnCoef : Work.FTS.Nonlin.Xn α coef
        = 2 * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.Uop α
            (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ) := by
      rw [hcoef, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul]
      norm_num
    have hXc : Work.FTS.Nonlin.Xn α coef ≤ 2 * (max Ce 1 * Work.FTS.Nonlin.Xn α g) := by
      rw [hXnCoef]
      have hU2 : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ)
          ≤ Ce * Work.FTS.Nonlin.Xn α g := hell.U.2
      have hmaxle : Ce * Work.FTS.Nonlin.Xn α g ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g :=
        mul_le_mul_of_nonneg_right (le_max_left Ce 1) hXg
      linarith [hU2, hmaxle]
    have hXc0 : 0 ≤ Work.FTS.Nonlin.Xn α coef := Work.Spaces.HkNorm_nonneg α 4 coef
    have hCt0 : 0 ≤ Ct := hCt.le
    have hmax0 : 0 ≤ max Ce 1 := hmax.le
    calc |IP α (fun z θ => coef z θ * Work.Spaces.Dth g z θ) g|
        ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α coef
            * Work.FTS.Nonlin.Xn α g ^ 2 := ht1
      _ ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (2 * (max Ce 1 * Work.FTS.Nonlin.Xn α g))
            * Work.FTS.Nonlin.Xn α g ^ 2 := by
          have h1 : 0 ≤ Ct * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCt0 hrp
          have h2 : 0 ≤ Work.FTS.Nonlin.Xn α g ^ 2 := sq_nonneg _
          have h3 : 0 ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (2 * (max Ce 1 * Work.FTS.Nonlin.Xn α g)) :=
            mul_nonneg h1 (mul_nonneg (by norm_num) (mul_nonneg hmax0 hXg))
          exact mul_le_mul (mul_le_mul_of_nonneg_left hXc h1) le_rfl h2 h3
      _ = (2 * Ct * max Ce 1) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
          ring
      _ ≤ (2 * Ct * max Ce 1 + 1) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
          exact mul_le_mul_of_nonneg_right (by linarith)
            (mul_nonneg hrp (by positivity))

/-! ## Row 13 — the `ℋ⁴`-norm bound for `N₂^{g*}` -/

private theorem rowsN2aRow13 (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2gs α g Φg)
          ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCi, _⟩ := hN.pos
  obtain ⟨CF, hCF, hF⟩ := Work.FTS.Nonlin.DthFstar_W
  have hmax : 0 < max Ce 1 := lt_of_lt_of_le zero_lt_one (le_max_right Ce 1)
  refine ⟨2 * Ci * CF * max Ce 1 + 1, ?_, ?_⟩
  · have hpos : 0 < 2 * Ci * CF * max Ce 1 :=
      mul_pos (mul_pos (mul_pos (by norm_num) hCi) hCF) hmax
    linarith
  · intro α g Φs Φg hctx
    have hα : 0 < α := hctx.hα
    have hα1 : α ≤ 1 := hctx.hα1
    have hαα₂ : α ≤ α₂ := hctx.hαα₂
    have hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg := hctx.hell
    have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
    -- the `ℋ⁴`-coefficient `c = U(Φ̃_g)/sin 2θ` of the elliptic package
    set c : Fn := fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
      / Work.Construction.s2 θ with hc
    have hcHQo : Work.FTS.VocabO.HQo α 4 c := by
      rw [hc]
      simpa only [Work.FTS.Nonlin.PhiTg] using hell.U.1
    have hcB : Work.FTS.Nonlin.Xn α c ≤ Ce * Work.FTS.Nonlin.Xn α g := by
      rw [hc]
      simpa only [Work.FTS.Nonlin.PhiTg] using hell.U.2
    -- `D_θF_*` is smooth on the open quadrant and in `𝒲^{4,∞}` with norm `≤ CF·α²`
    have hFsmooth : Work.FTS.EllipticEst.SmoothOpen
        (Work.Spaces.Dth (Work.Construction.Fstar α)) :=
      (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)).Dth
    obtain ⟨hFWmem, hFWle⟩ := hF α hα hα1
    -- the `𝒲^{4,∞}`-priced product rule
    have hprod := hN.wprod α hIoc (Work.Spaces.Dth (Work.Construction.Fstar α)) c
      hFsmooth hFWmem hcHQo
    -- the honest representative `P = D_θF_* · c`
    set P : Fn := fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ * c z θ with hP
    have hPmem : Work.Spaces.HkMem α 4 P := by
      rw [hP]
      exact hprod.1
    -- `N₂^{g*} = -2·P` on `(0,∞) × [0,π/2]`
    have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
        Work.FTS.Nonlin.N2gs α g Φg z θ = -2 * P z θ := by
      intro z _hz θ hθ
      rcases eq_or_lt_of_le hθ.1 with h0 | hpos
      · -- `θ = 0`: both sides vanish, `U(Φ̃_g)(·,0) = 0`
        subst h0
        simp only [hP, hc, Work.FTS.Nonlin.N2gs, Work.FTS.Nonlin.PhiTg, Work.Spaces.Dth,
          Work.Construction.s2_eq]
        simp [hell.vanishU.1 z]
      · rcases eq_or_lt_of_le hθ.2 with hpi | hlt
        · -- `θ = π/2`: both sides vanish, `U(Φ̃_g)(·,π/2) = 0`
          subst hpi
          simp only [hP, hc, Work.FTS.Nonlin.N2gs, Work.FTS.Nonlin.PhiTg, Work.Spaces.Dth,
            Work.Construction.s2_eq]
          simp [hell.vanishU.2 z]
        · -- interior: cancel `sin 2θ`
          have hsin2 : Real.sin (2 * θ) ≠ 0 := by
            intro hzero
            have hsinpos : 0 < Real.sin θ :=
              Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [Real.pi_pos])
            have hcospos : 0 < Real.cos θ :=
              Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩
            rw [Real.sin_two_mul] at hzero
            nlinarith [mul_pos hsinpos hcospos]
          simp only [hP, hc, Work.FTS.Nonlin.N2gs, Work.FTS.Nonlin.PhiTg, Work.Spaces.Dth,
            Work.Construction.s2_eq]
          field_simp
    -- the `ℋ⁴`-honesty of `N₂^{g*}`, transferred from the honest representative
    have hmem : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N2gs α g Φg) :=
      Work.Coercivity.HkMem_congr_Ioi α 4
        (Work.FTS.LocData.HkMem_const_mul α 4 (-2) hPmem)
        (fun z hz θ hθ => (hpt z hz θ hθ).symm)
    -- the norm only sees the open quadrant, so `|N₂^{g*}| = 2·|P|`
    have hXn_eq : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2gs α g Φg)
        = 2 * Work.FTS.Nonlin.Xn α P := by
      have hcong : Work.FTS.Nonlin.Xn α (fun z θ => -2 * P z θ)
          = Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2gs α g Φg) := by
        change Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => -2 * P z θ))
          = Real.sqrt (Work.Spaces.HkSq α 4 (Work.FTS.Nonlin.N2gs α g Φg))
        rw [Work.FTS.EllipticEst.HkSq_congr_open α 4
            (fun z θ hz hθ hlt =>
              (hpt z (Set.mem_Ioi.mpr hz) θ ⟨le_of_lt hθ, le_of_lt hlt⟩).symm)]
      have htwo : Work.FTS.Nonlin.Xn α (fun z θ => -2 * P z θ)
          = 2 * Work.FTS.Nonlin.Xn α P := by
        rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α (-2) P,
          abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
        norm_num
      exact hcong.symm.trans htwo
    rw [hXn_eq]
    have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hXc : 0 ≤ Work.FTS.Nonlin.Xn α c := Work.Spaces.HkNorm_nonneg α 4 c
    have hrp : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    have hCnn : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCi.le hrp
    have hcB' : Work.FTS.Nonlin.Xn α c ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g :=
      le_trans hcB (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hXg)
    have hXnP : Work.FTS.Nonlin.Xn α P
        ≤ Ci * α ^ (-(1 / 2 : ℝ))
          * Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α))
          * Work.FTS.Nonlin.Xn α c := by
      rw [hP]
      exact hprod.2
    have hstep : Work.FTS.Nonlin.Xn α P
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
          * (max Ce 1 * Work.FTS.Nonlin.Xn α g) := by
      refine le_trans hXnP (mul_le_mul ?_ hcB' hXc ?_)
      · exact mul_le_mul_of_nonneg_left hFWle hCnn
      · exact mul_nonneg hCnn (mul_nonneg hCF.le (sq_nonneg α))
    have hrpow : α ^ (-(1 / 2 : ℝ)) * α ^ 2 = α ^ (3 / 2 : ℝ) := by
      rw [show α ^ 2 = α ^ (2 : ℝ) by norm_num]
      have h := Real.rpow_add hα (-(1 / 2 : ℝ)) (2 : ℝ)
      rw [show -(1 / 2 : ℝ) + 2 = 3 / 2 by norm_num] at h
      exact h.symm
    calc 2 * Work.FTS.Nonlin.Xn α P
        ≤ 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
            * (max Ce 1 * Work.FTS.Nonlin.Xn α g)) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = (2 * Ci * CF * max Ce 1) * (α ^ (-(1 / 2 : ℝ)) * α ^ 2)
            * Work.FTS.Nonlin.Xn α g := by ring
      _ = (2 * Ci * CF * max Ce 1)
            * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
          rw [hrpow]
          ring
      _ ≤ (2 * Ci * CF * max Ce 1 + 1)
            * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
          refine mul_le_mul_of_nonneg_right (by linarith) ?_
          exact mul_nonneg (Real.rpow_nonneg hα.le _) hXg

/-! ## The two rows, with a single constant -/

theorem rowsN2a (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N2gg α g Φg) g|
          ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2gs α g Φg)
          ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨K1, hK1, h1⟩ := rowsN2aRow12 IP hN hE
  obtain ⟨K2, hK2, h2⟩ := rowsN2aRow13 IP hN hE
  refine ⟨K1 + K2 + 1, by linarith, ?_⟩
  intro α g Φs Φg hctx
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA1 : 0 ≤ α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3 :=
    mul_nonneg (Real.rpow_nonneg hctx.hα.le _) (by positivity)
  have hA2 : 0 ≤ α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g :=
    mul_nonneg (Real.rpow_nonneg hctx.hα.le _) hX
  exact ⟨(h1 hctx).trans (mul_le_mul_of_nonneg_right (by linarith) hA1),
    (h2 hctx).trans (mul_le_mul_of_nonneg_right (by linarith) hA2)⟩

end Work.FTS.StrongEps.E4R3.N4C.rows
