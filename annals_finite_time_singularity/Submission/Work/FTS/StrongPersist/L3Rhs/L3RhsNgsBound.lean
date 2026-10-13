/-
# `Work.FTS.StrongPersist.L3Rhs.L3RhsNgsBound` — the `ℋ³` bound for the `N^{gs}` block

This is the `gs`-block of the level-three right-hand side of the modulated `g`-equation
(`Work.FTS.StrongPersist.L3RhsPriced`): the block in which the *perturbation* elliptic
residual is advected by the *star* profile `F_*`,

`NGsSum α g Φg = N₁^{gs} + N₂^{gs} + N₃^{gs}`,

with (rows 9, 13, 17 of the table of `Work.FTS.Nonlin.Defs`)

* `N₁^{gs} =  2 ℛ(Φ̃_g) · F_*`,
* `N₂^{gs} = -2 U(Φ̃_g) · ∂_θF_*`,
* `N₃^{gs} = -2α V(Φ̃_g) · D_zF_*`.

## Mathematics

The elliptic package `EllPkgK α 6 Ce g Φg` prices the three transported coefficients

`ℛ(Φ̃_g)`,  `U(Φ̃_g)/sin 2θ`,  `V(Φ̃_g)`

by `Ce · |g|_{ℋ⁶}`, and each is `C^∞` on the open quadrant.  The three *profile* factors are
the `D`-derivatives of the star profile in the two directions,

`F_*`,  `D_θF_* = sin 2θ · ∂_θF_*`,  `D_zF_*`,

and each of them lies in the `𝒲^{4,∞}`-class with an `α`-independent constant:
`Fstar_W` (`|F_*|_{𝒲^{4,∞}} ≤ C α`), `DthFstar_W` (`≤ C α²`) and `DzFstar_W` (`≤ C α`).
The level-four `𝒲^{4,∞}`-priced product rule `Work.FTS.OpenPkg.wprod_field_winf`

`|f · g|_{ℋ⁴} ≤ C α^{-1/2} |f|_{𝒲^{4,∞}} |g|_{ℋ⁴}`  (`f` smooth and `𝒲^{4,∞}`, `g ∈ ℋ⁴`)

therefore turns each summand into a bounded multiple of `Ce · |g|_{ℋ⁶}`, and the
`ℋ³`-bound follows by monotonicity of the weighted norm in the order (`ℋ³ ⊂ ℋ⁴ ⊂ ℋ⁶`).

The one identification that is *not* a pointwise ring identity is `N₂^{gs}`: the elliptic
package packages `U(Φ̃_g) / sin 2θ`, so

`N₂^{gs} = -2 · (U(Φ̃_g)/sin 2θ) · D_θF_*`  **on the open quadrant only**

(at `θ = 0, π/2` the totalised division gives `0`, but the two weights
`w / sin(2θ)^{η/2}` and `Wt` vanish there, so the `ℋ³`-integrand is insensitive to the
difference — `HkSq_congr_open`, `HkMem_congr_Q0`).

The constant produced is `16 Cw (CF + CD + CZ) + 1`; the `α`-power is `0` (the estimate is
uniform in `α → 0⁺`), and the factors `(1+|Ce|)⁴`, `(1+M)⁴`, `(1+Xn₆)²` are the generous
polynomial form of the statement.  Everything rests on `[propext, Classical.choice,
Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.OpenPkg.wprod_field_winf
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.Nonlinear.FstarPkg.Fstar_W
import Submission.Work.FTS.Nonlinear.FstarPkg.DthFstar_W
import Submission.Work.FTS.Nonlinear.FstarPkg.DzFstar_W
import Submission.Work.FTS.StrongPersist.HkAddFin
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.EllipticEst.ScaleAPI
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.EggBound
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.H2.WPQ.Interior

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (N1gs N2gs N3gs Xn)
open Work.Spaces (HkMem HkSq HkNorm WlInf WlInfMem)
open Work.FTS.EllipticEst (SmoothOpen)
open Work.FTS.VocabO (HQo)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-! ## Elementary `rpow` facts at the half-integer exponent `-1/2` -/

private lemma rpow_neg_half_mul_le_one (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    α ^ (-(1 / 2 : ℝ)) * α ≤ 1 := by
  have h1 : α ^ (-(1 / 2 : ℝ)) * α ^ (1 : ℝ) ≤ 1 := by
    rw [← Real.rpow_add hα0 (-(1 / 2 : ℝ)) 1,
      show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
    exact Real.rpow_le_one hα0.le hα1 (by norm_num)
  rwa [Real.rpow_one] at h1

private lemma rpow_neg_half_mul_sq_le_one (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    α ^ (-(1 / 2 : ℝ)) * α ^ 2 ≤ 1 := by
  have hcast : (α : ℝ) ^ 2 = α ^ (2 : ℝ) := (Real.rpow_natCast α 2).symm
  rw [hcast, ← Real.rpow_add hα0 (-(1 / 2 : ℝ)) 2,
    show -(1 / 2 : ℝ) + 2 = 3 / 2 by norm_num]
  exact Real.rpow_le_one hα0.le hα1 (by norm_num)

/-! ## The generic piece bound -/

/-- **The level-three product bound.**  Given the level-four `𝒲^{4,∞}`-priced product rule
with constant `Cw`, a multiplier `m` that is `SmoothOpen` and of class `𝒲^{4,∞}` with
`|m|_{𝒲^{4,∞}} ≤ Bm`, and an `ℋ⁶`-function `hh` with `|hh|_{ℋ⁶} ≤ Bh`, the product
`c · (m · hh)` lies in `ℋ³` and

`|c · (m·hh)|_{ℋ³} ≤ |c| · Cw · α^{-1/2} · Bm · Bh`.

The proof is the chain `ℋ³ ⊂ ℋ⁴` (`HkNorm_mono_of_mem`), the product rule at level four, and
`ℋ⁴ ⊂ ℋ⁶` for the second factor. -/
private theorem ngs_piece_bound (Cw : ℝ) (hCw : 0 < Cw)
    (hwprod : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f g : Fn,
      SmoothOpen f → WlInfMem α 4 f → HQo α 4 g →
      HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Xn α (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * WlInf α 4 f * Xn α g)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {m hh : Fn} {Bm Bh : ℝ}
    (hmsm : SmoothOpen m) (hmW : WlInfMem α 4 m) (hmB : WlInf α 4 m ≤ Bm)
    (hhsm : SmoothOpen hh) (hhmem6 : HkMem α 6 hh) (hhbd : HkNorm α 6 hh ≤ Bh)
    (c : ℝ) :
    SmoothOpen (fun z θ => c * (m z θ * hh z θ)) ∧
    HkMem α 3 (fun z θ => c * (m z θ * hh z θ)) ∧
    HkNorm α 3 (fun z θ => c * (m z θ * hh z θ))
      ≤ |c| * (Cw * α ^ (-(1 / 2 : ℝ)) * Bm * Bh) := by
  have hmm4 : HkMem α 4 hh := HkMem_of_le_of_smoothOpen α (by norm_num) hhsm hhmem6
  obtain ⟨hmem4, hbd4⟩ := hwprod α hα0 hα1 m hh hmsm hmW ⟨hhsm, hmm4⟩
  have hbd6 : HkNorm α 4 hh ≤ Bh :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 6) (k' := 4)
      (by norm_num) hhmem6) hhbd
  have hWnn : 0 ≤ WlInf α 4 m := Work.FTS.H2.WPQ.WlInf_nonneg' hmW
  have hBm0 : 0 ≤ Bm := le_trans hWnn hmB
  have hkey : Xn α (fun z θ => m z θ * hh z θ) ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Bm * Bh := by
    refine le_trans hbd4 ?_
    have h1 : WlInf α 4 m * Xn α hh ≤ Bm * Bh :=
      mul_le_mul hmB hbd6 (Work.Spaces.HkNorm_nonneg α 4 hh) hBm0
    have h2 : (0 : ℝ) ≤ Cw * α ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg hCw.le (Real.rpow_nonneg hα0.le _)
    calc Cw * α ^ (-(1 / 2 : ℝ)) * WlInf α 4 m * Xn α hh
        = Cw * α ^ (-(1 / 2 : ℝ)) * (WlInf α 4 m * Xn α hh) := by ring
      _ ≤ Cw * α ^ (-(1 / 2 : ℝ)) * (Bm * Bh) := mul_le_mul_of_nonneg_left h1 h2
      _ = Cw * α ^ (-(1 / 2 : ℝ)) * Bm * Bh := by ring
  have h3mem : HkMem α 3 (fun z θ => m z θ * hh z θ) :=
    HkMem_of_le_of_smoothOpen α (by norm_num) (hmsm.mul hhsm) hmem4
  have h34 : HkNorm α 3 (fun z θ => m z θ * hh z θ)
      ≤ HkNorm α 4 (fun z θ => m z θ * hh z θ) :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 4) (k' := 3) (by norm_num) hmem4
  refine ⟨?_, ?_, ?_⟩
  · exact Work.FTS.EllipticEst.SmoothOpen.const_mul' c (hmsm.mul hhsm)
  · exact Work.FTS.Nonlinear.Pieces.Rl1.HkMem_const_mul_of c h3mem
  · have heq : (fun z θ => c * (m z θ * hh z θ))
        = c • (fun z θ => m z θ * hh z θ) := by funext z θ; rfl
    rw [heq, Work.FTS.EllipticEst.HkNorm_smul]
    exact mul_le_mul_of_nonneg_left (le_trans h34 hkey) (abs_nonneg c)

theorem L3RhsNgsBound : ∃ C Cpow α₂ : ℝ, 0 < C ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (Ce M : ℝ) (f Φg : Work.FTS.Galerkin.Fn),
      Work.FTS.StrongPersist.EllPkgK α 6 Ce f Φg → Work.FTS.StrongPersist.H6Adm α f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.StrongPersist.L3Rhs.NGsSum α f Φg)) Work.FTS.EllipticEst.Q0 ∧
      Work.Spaces.HkMem α 3 (Work.FTS.StrongPersist.L3Rhs.NGsSum α f Φg) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.StrongPersist.L3Rhs.NGsSum α f Φg)
        ≤ C * (1 + |Ce|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by
  obtain ⟨Cw, hCw, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨CF, hCF, hFstar⟩ := Work.FTS.Nonlinear.FstarPkg.Fstar_W
  obtain ⟨CD, hCD, hDthFstar⟩ := Work.FTS.Nonlinear.FstarPkg.DthFstar_W
  obtain ⟨CZ, hCZ, hDzFstar⟩ := Work.FTS.Nonlinear.FstarPkg.DzFstar_W
  have hS0 : (0 : ℝ) < Cw * (CF + CD + CZ) := by
    have h1 : 0 < CF + CD + CZ := by linarith
    exact mul_pos hCw h1
  set Cc : ℝ := 16 * (Cw * (CF + CD + CZ)) + 1 with hCc
  have hCcpos : 0 < Cc := by rw [hCc]; linarith
  refine ⟨Cc, 0, 1, hCcpos, le_refl 0, one_pos, ?_⟩
  intro α hα Ce M f Φg hell hadm hM
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- ### the three transported coefficients
  set RG : Fn := Work.Construction.Rop α (Work.Construction.PhiTil α f Φg) with hRG
  set UG : Fn := fun z θ =>
    Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ / Work.Construction.s2 θ with hUG
  set VG : Fn := Work.Construction.Vop (Work.Construction.PhiTil α f Φg) with hVG
  have hRsm : SmoothOpen RG := by rw [hRG]; exact hell.R.1.1
  have hRmem6 : HkMem α 6 RG := by rw [hRG]; exact hell.R.1.2
  have hRbd : HkNorm α 6 RG ≤ Ce * HkNorm α 6 f := by rw [hRG]; exact hell.R.2
  have hUsm : SmoothOpen UG := by rw [hUG]; exact hell.U.1.1
  have hUmem6 : HkMem α 6 UG := by rw [hUG]; exact hell.U.1.2
  have hUbd : HkNorm α 6 UG ≤ Ce * HkNorm α 6 f := by rw [hUG]; exact hell.U.2
  have hVsm : SmoothOpen VG := by rw [hVG]; exact hell.V.1.1
  have hVmem6 : HkMem α 6 VG := by rw [hVG]; exact hell.V.1.2
  have hVbd : HkNorm α 6 VG ≤ Ce * HkNorm α 6 f := by rw [hVG]; exact hell.V.2
  -- ### the `max Ce 0`-priced version (`Ce` may be negative)
  have hRbdc : HkNorm α 6 RG ≤ max Ce 0 * HkNorm α 6 f :=
    le_trans hRbd (mul_le_mul_of_nonneg_right (le_max_left Ce 0)
      (Work.Spaces.HkNorm_nonneg α 6 f))
  have hUbdc : HkNorm α 6 UG ≤ max Ce 0 * HkNorm α 6 f :=
    le_trans hUbd (mul_le_mul_of_nonneg_right (le_max_left Ce 0)
      (Work.Spaces.HkNorm_nonneg α 6 f))
  have hVbdc : HkNorm α 6 VG ≤ max Ce 0 * HkNorm α 6 f :=
    le_trans hVbd (mul_le_mul_of_nonneg_right (le_max_left Ce 0)
      (Work.Spaces.HkNorm_nonneg α 6 f))
  set Bh : ℝ := max Ce 0 * Work.Spaces.HkNorm α 6 f with hBh
  have hBh0 : 0 ≤ Bh := by
    rw [hBh]; exact mul_nonneg (le_max_right _ _) (Work.Spaces.HkNorm_nonneg α 6 f)
  -- ### the profile factors
  have hFsm : SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hFW := hFstar α hα0 hα1
  have hDW := hDthFstar α hα0 hα1
  have hZW := hDzFstar α hα0 hα1
  have hDthsm : SmoothOpen (Work.Spaces.Dth (Work.Construction.Fstar α)) := hFsm.Dth
  have hDzsm : SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α)) := hFsm.Dz
  -- ### the three summands, in the shape of `ngs_piece_bound`
  set P1 : Fn := fun z θ => (2 : ℝ) * (Work.Construction.Fstar α z θ * RG z θ) with hP1
  set P2 : Fn := fun z θ => (-2 : ℝ) *
    (Work.Spaces.Dth (Work.Construction.Fstar α) z θ * UG z θ) with hP2
  set P3 : Fn := fun z θ => (-2 * α) *
    (Work.Spaces.Dz (Work.Construction.Fstar α) z θ * VG z θ) with hP3
  have hres1 := ngs_piece_bound Cw hCw hwprod hα0 hα1 hFsm hFW.1 hFW.2 hRsm hRmem6 hRbdc 2
  rw [← hP1] at hres1
  have hres2 := ngs_piece_bound Cw hCw hwprod hα0 hα1 hDthsm hDW.1 hDW.2 hUsm hUmem6 hUbdc (-2)
  rw [← hP2] at hres2
  have hres3 := ngs_piece_bound Cw hCw hwprod hα0 hα1 hDzsm hZW.1 hZW.2 hVsm hVmem6 hVbdc (-2 * α)
  rw [← hP3] at hres3
  have hP1sm : SmoothOpen P1 := hres1.1
  have hP1mem : HkMem α 3 P1 := hres1.2.1
  have hP1bd : HkNorm α 3 P1 ≤ 2 * (Cw * α ^ (-(1 / 2 : ℝ)) * (CF * α) * Bh) := by
    have h := hres1.2.2
    rw [show |(2 : ℝ)| = 2 by norm_num] at h
    exact h
  have hP2sm : SmoothOpen P2 := hres2.1
  have hP2mem : HkMem α 3 P2 := hres2.2.1
  have hP2bd : HkNorm α 3 P2 ≤ 2 * (Cw * α ^ (-(1 / 2 : ℝ)) * (CD * α ^ 2) * Bh) := by
    have h := hres2.2.2
    rw [show |(-2 : ℝ)| = 2 by norm_num] at h
    exact h
  have hP3sm : SmoothOpen P3 := hres3.1
  have hP3mem : HkMem α 3 P3 := hres3.2.1
  have hP3bd : HkNorm α 3 P3 ≤ 2 * α * (Cw * α ^ (-(1 / 2 : ℝ)) * (CZ * α) * Bh) := by
    have h := hres3.2.2
    rw [show |(-2 : ℝ) * α| = 2 * α by
      rw [abs_of_neg (by linarith : (-2 : ℝ) * α < 0)]
      ring] at h
    exact h
  -- ### identification of the three summands with `P1`, `P2`, `P3`
  have hN1 : N1gs α f Φg = P1 := by
    funext z θ
    simp only [Work.FTS.Nonlin.N1gs, Work.FTS.Nonlin.PhiTg, hRG, hP1]
    ring
  have hN2eq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      N2gs α f Φg z θ = P2 z θ := by
    intro z θ _ hθ hθ2
    have hs2 : Work.Construction.s2 θ ≠ 0 := by
      rw [Work.Construction.s2]
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
        (by linarith [Real.pi_pos]))
    have h1 : Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        = Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ := rfl
    simp only [Work.FTS.Nonlin.N2gs, Work.FTS.Nonlin.PhiTg, hUG, hP2, h1]
    field_simp
  have hN3 : N3gs α f Φg = P3 := by
    funext z θ
    simp only [Work.FTS.Nonlin.N3gs, Work.FTS.Nonlin.PhiTg, hVG, hP3]
    ring
  -- ### smoothness of the three summands on the open quadrant
  have hN1sm3 : ContDiffOn ℝ 3
      (Function.uncurry (N1gs α f Φg)) Work.FTS.EllipticEst.Q0 := by
    rw [hN1]; exact hP1sm.forall 3
  have hN2sm3 : ContDiffOn ℝ 3
      (Function.uncurry (N2gs α f Φg)) Work.FTS.EllipticEst.Q0 := by
    refine ContDiffOn.congr (hP2sm.forall 3) ?_
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact hN2eq p.1 p.2 hz hθ0 hθ1
  have hN3sm3 : ContDiffOn ℝ 3
      (Function.uncurry (N3gs α f Φg)) Work.FTS.EllipticEst.Q0 := by
    rw [hN3]; exact hP3sm.forall 3
  -- ### `ℋ³`-membership of the three summands
  have hN1mem : HkMem α 3 (N1gs α f Φg) := by rw [hN1]; exact hP1mem
  have hN2mem : HkMem α 3 (N2gs α f Φg) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 3 hP2mem
      (fun z hz θ hθ => (hN2eq z θ hz hθ.1 hθ.2).symm)
  have hN3mem : HkMem α 3 (N3gs α f Φg) := by rw [hN3]; exact hP3mem
  -- ### the three bounds, in the common shape `2 Cw Cᵢ Bh`
  have hb1 : HkNorm α 3 (N1gs α f Φg) ≤ 2 * (Cw * CF) * Bh := by
    rw [hN1]
    refine le_trans hP1bd ?_
    have h1 : α ^ (-(1 / 2 : ℝ)) * α ≤ 1 := rpow_neg_half_mul_le_one α hα0 hα1
    have h2 : (0 : ℝ) ≤ Cw * CF := mul_nonneg hCw.le hCF.le
    have h3 : 0 ≤ (Cw * CF) * Bh := mul_nonneg h2 hBh0
    have h4 : Cw * α ^ (-(1 / 2 : ℝ)) * (CF * α) * Bh ≤ Cw * CF * Bh := by
      rw [show Cw * α ^ (-(1 / 2 : ℝ)) * (CF * α) * Bh
            = (Cw * CF) * (α ^ (-(1 / 2 : ℝ)) * α) * Bh by ring]
      calc (Cw * CF) * (α ^ (-(1 / 2 : ℝ)) * α) * Bh
          ≤ (Cw * CF) * 1 * Bh :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) hBh0
        _ = Cw * CF * Bh := by ring
    calc 2 * (Cw * α ^ (-(1 / 2 : ℝ)) * (CF * α) * Bh)
        ≤ 2 * (Cw * CF * Bh) := mul_le_mul_of_nonneg_left h4 (by norm_num)
      _ = 2 * (Cw * CF) * Bh := by ring
  have hb2 : HkNorm α 3 (N2gs α f Φg) ≤ 2 * (Cw * CD) * Bh := by
    have hsq : HkSq α 3 (N2gs α f Φg) = HkSq α 3 P2 :=
      Work.FTS.EllipticEst.HkSq_congr_open α 3
        (fun z θ hz hθ hθ2 => hN2eq z θ hz hθ hθ2)
    have hnorm : HkNorm α 3 (N2gs α f Φg) = HkNorm α 3 P2 := by
      simp only [HkNorm]
      rw [hsq]
    rw [hnorm]
    refine le_trans hP2bd ?_
    have h1 : α ^ (-(1 / 2 : ℝ)) * α ^ 2 ≤ 1 := rpow_neg_half_mul_sq_le_one α hα0 hα1
    have h2 : (0 : ℝ) ≤ Cw * CD := mul_nonneg hCw.le hCD.le
    have h3 : 0 ≤ (Cw * CD) * Bh := mul_nonneg h2 hBh0
    have h4 : Cw * α ^ (-(1 / 2 : ℝ)) * (CD * α ^ 2) * Bh ≤ Cw * CD * Bh := by
      rw [show Cw * α ^ (-(1 / 2 : ℝ)) * (CD * α ^ 2) * Bh
            = (Cw * CD) * (α ^ (-(1 / 2 : ℝ)) * α ^ 2) * Bh by ring]
      calc (Cw * CD) * (α ^ (-(1 / 2 : ℝ)) * α ^ 2) * Bh
          ≤ (Cw * CD) * 1 * Bh :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) hBh0
        _ = Cw * CD * Bh := by ring
    calc 2 * (Cw * α ^ (-(1 / 2 : ℝ)) * (CD * α ^ 2) * Bh)
        ≤ 2 * (Cw * CD * Bh) := mul_le_mul_of_nonneg_left h4 (by norm_num)
      _ = 2 * (Cw * CD) * Bh := by ring
  have hb3 : HkNorm α 3 (N3gs α f Φg) ≤ 2 * (Cw * CZ) * Bh := by
    rw [hN3]
    refine le_trans hP3bd ?_
    have h1 : α ^ (-(1 / 2 : ℝ)) * α ≤ 1 := rpow_neg_half_mul_le_one α hα0 hα1
    have h2 : (0 : ℝ) ≤ Cw * CZ := mul_nonneg hCw.le hCZ.le
    have h3 : 0 ≤ (2 * (Cw * CZ)) * Bh := mul_nonneg (by positivity) hBh0
    have h4 : 2 * α * (Cw * α ^ (-(1 / 2 : ℝ)) * (CZ * α) * Bh) ≤ 2 * (Cw * CZ) * Bh := by
      have h5 : α * (α ^ (-(1 / 2 : ℝ)) * α) ≤ 1 := by
        have h6 : 0 ≤ α ^ (-(1 / 2 : ℝ)) * α :=
          mul_nonneg (Real.rpow_nonneg hα0.le _) hα0.le
        exact le_trans (mul_le_mul hα1 h1 h6 (by norm_num : (0 : ℝ) ≤ 1)) (by norm_num)
      calc 2 * α * (Cw * α ^ (-(1 / 2 : ℝ)) * (CZ * α) * Bh)
          = (2 * (Cw * CZ) * Bh) * (α * (α ^ (-(1 / 2 : ℝ)) * α)) := by ring
        _ ≤ (2 * (Cw * CZ) * Bh) * 1 := mul_le_mul_of_nonneg_left h5 h3
        _ = 2 * (Cw * CZ) * Bh := by ring
    exact h4
  -- ### assembly
  have h12 := HkAddFin (α := α) (k := 3) hN1sm3 hN2sm3 hN1mem hN2mem
  have h12sm3 : ContDiffOn ℝ 3
      (Function.uncurry (fun z θ => N1gs α f Φg z θ + N2gs α f Φg z θ))
      Work.FTS.EllipticEst.Q0 := hN1sm3.add hN2sm3
  have h123 := HkAddFin (α := α) (k := 3) h12sm3 hN3sm3 h12.1 hN3mem
  -- ### the common scale `S`
  have hSnn : 0 ≤ Cw * (CF + CD + CZ) * Bh :=
    mul_nonneg (mul_nonneg hCw.le (by linarith)) hBh0
  have hb1' : HkNorm α 3 (N1gs α f Φg) ≤ 2 * (Cw * (CF + CD + CZ) * Bh) := by
    refine le_trans hb1 ?_
    have hle : Cw * CF * Bh ≤ Cw * (CF + CD + CZ) * Bh := by
      have h2 : 0 ≤ Cw * Bh := mul_nonneg hCw.le hBh0
      calc Cw * CF * Bh = (Cw * Bh) * CF := by ring
        _ ≤ (Cw * Bh) * (CF + CD + CZ) :=
            mul_le_mul_of_nonneg_left (by linarith) h2
        _ = Cw * (CF + CD + CZ) * Bh := by ring
    nlinarith [hle]
  have hb2' : HkNorm α 3 (N2gs α f Φg) ≤ 2 * (Cw * (CF + CD + CZ) * Bh) := by
    refine le_trans hb2 ?_
    have hle : Cw * CD * Bh ≤ Cw * (CF + CD + CZ) * Bh := by
      have h2 : 0 ≤ Cw * Bh := mul_nonneg hCw.le hBh0
      calc Cw * CD * Bh = (Cw * Bh) * CD := by ring
        _ ≤ (Cw * Bh) * (CF + CD + CZ) :=
            mul_le_mul_of_nonneg_left (by linarith) h2
        _ = Cw * (CF + CD + CZ) * Bh := by ring
    nlinarith [hle]
  have hb3' : HkNorm α 3 (N3gs α f Φg) ≤ 2 * (Cw * (CF + CD + CZ) * Bh) := by
    refine le_trans hb3 ?_
    have hle : Cw * CZ * Bh ≤ Cw * (CF + CD + CZ) * Bh := by
      have h2 : 0 ≤ Cw * Bh := mul_nonneg hCw.le hBh0
      calc Cw * CZ * Bh = (Cw * Bh) * CZ := by ring
        _ ≤ (Cw * Bh) * (CF + CD + CZ) :=
            mul_le_mul_of_nonneg_left (by linarith) h2
        _ = Cw * (CF + CD + CZ) * Bh := by ring
    nlinarith [hle]
  -- ### the `ℋ³` bound of the block
  have hnorm : HkNorm α 3 (NGsSum α f Φg) ≤ 16 * (Cw * (CF + CD + CZ) * Bh) := by
    refine le_trans h123.2 ?_
    have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hS4 : HkNorm α 3 (fun z θ => N1gs α f Φg z θ + N2gs α f Φg z θ)
        ≤ 6 * (Cw * (CF + CD + CZ) * Bh) := by
      refine le_trans h12.2 ?_
      have h2 : Real.sqrt 2 * (2 * (Cw * (CF + CD + CZ) * Bh)
          + 2 * (Cw * (CF + CD + CZ) * Bh)) ≤ 6 * (Cw * (CF + CD + CZ) * Bh) := by
        have hX : 0 ≤ Cw * (CF + CD + CZ) * Bh := hSnn
        nlinarith [hs2, hX, Real.sqrt_nonneg 2]
      exact le_trans (mul_le_mul_of_nonneg_left (by linarith [hb1', hb2'])
        (Real.sqrt_nonneg 2)) h2
    have hAB : HkNorm α 3 (fun z θ => N1gs α f Φg z θ + N2gs α f Φg z θ)
        + HkNorm α 3 (N3gs α f Φg)
        ≤ 6 * (Cw * (CF + CD + CZ) * Bh) + 2 * (Cw * (CF + CD + CZ) * Bh) := by
      linarith [hS4, hb3']
    have h3 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    refine le_trans (mul_le_mul_of_nonneg_left hAB h3) ?_
    nlinarith [hs2, hSnn, Real.sqrt_nonneg 2]
  -- ### the final constant bookkeeping
  have hfin : 16 * (Cw * (CF + CD + CZ) * Bh)
      ≤ Cc * (1 + |Ce|) ^ 4 * α ^ (-(0 : ℝ)) * (1 + M) ^ 4
          * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by
    have hKc_le : max Ce 0 ≤ (1 + |Ce|) ^ 4 := by
      have h1 : max Ce 0 ≤ |Ce| := max_le (le_abs_self Ce) (abs_nonneg Ce)
      have h3 : (1 : ℝ) ≤ 1 + |Ce| := by linarith [abs_nonneg Ce]
      have h4 : 1 + |Ce| ≤ (1 + |Ce|) ^ 4 := by
        have h5 : (1 : ℝ) ≤ (1 + |Ce|) ^ 3 := one_le_pow₀ h3 (n := 3)
        nlinarith [h3, h5]
      linarith
    have hXn_le : Work.FTS.StrongPersist.Xn6 α f
        ≤ (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by
      have h0 : 0 ≤ Work.FTS.StrongPersist.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
      nlinarith [h0]
    have hM1 : (1 : ℝ) ≤ (1 + M) ^ 4 :=
      one_le_pow₀ (by have h0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hM
                      linarith) (n := 4)
    have hCc0 : 0 ≤ Cc := hCcpos.le
    have hCc_le : 16 * (Cw * (CF + CD + CZ)) ≤ Cc := by rw [hCc]; linarith
    have hKc0 : 0 ≤ max Ce 0 := le_max_right _ _
    have hXn0 : 0 ≤ Work.FTS.StrongPersist.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
    have hU0 : 0 ≤ α ^ (-(0 : ℝ)) := Real.rpow_nonneg hα0.le _
    have ha0 : α ^ (-(0 : ℝ)) = 1 := by rw [neg_zero, Real.rpow_zero]
    -- step 1: pull `Bh` apart, bound the numeric factor by `Cc`
    have hs1 : 16 * (Cw * (CF + CD + CZ) * Bh)
        = 16 * (Cw * (CF + CD + CZ)) * (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f := by
      rw [hBh]; ring
    rw [hs1]
    have hA : 16 * (Cw * (CF + CD + CZ)) * (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f
        ≤ Cc * (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f := by
      have h1 : 0 ≤ (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f := mul_nonneg hKc0 hXn0
      calc 16 * (Cw * (CF + CD + CZ)) * (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f
          = (16 * (Cw * (CF + CD + CZ))) * ((max Ce 0)
              * Work.FTS.StrongPersist.Xn6 α f) := by ring
        _ ≤ Cc * ((max Ce 0) * Work.FTS.StrongPersist.Xn6 α f) :=
            mul_le_mul_of_nonneg_right hCc_le h1
        _ = Cc * (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f := by ring
    refine le_trans hA ?_
    have hB : Cc * (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f
        ≤ Cc * (1 + |Ce|) ^ 4 * Work.FTS.StrongPersist.Xn6 α f := by
      have h1 : (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f
          ≤ (1 + |Ce|) ^ 4 * Work.FTS.StrongPersist.Xn6 α f :=
        mul_le_mul_of_nonneg_right hKc_le hXn0
      calc Cc * (max Ce 0) * Work.FTS.StrongPersist.Xn6 α f
          = Cc * ((max Ce 0) * Work.FTS.StrongPersist.Xn6 α f) := by ring
        _ ≤ Cc * ((1 + |Ce|) ^ 4 * Work.FTS.StrongPersist.Xn6 α f) :=
            mul_le_mul_of_nonneg_left h1 hCc0
        _ = Cc * (1 + |Ce|) ^ 4 * Work.FTS.StrongPersist.Xn6 α f := by ring
    refine le_trans hB ?_
    have hC : Cc * (1 + |Ce|) ^ 4 * Work.FTS.StrongPersist.Xn6 α f
        ≤ Cc * (1 + |Ce|) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 :=
      mul_le_mul_of_nonneg_left hXn_le
        (mul_nonneg hCc0 (by positivity))
    refine le_trans hC ?_
    rw [ha0]
    have hD0 : 0 ≤ Cc * (1 + |Ce|) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 :=
      mul_nonneg (mul_nonneg hCc0 (by positivity)) (by positivity)
    calc Cc * (1 + |Ce|) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2
        = (Cc * (1 + |Ce|) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2) * 1 := by ring
      _ ≤ (Cc * (1 + |Ce|) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2) * (1 + M) ^ 4 :=
          mul_le_mul_of_nonneg_left hM1 hD0
      _ = Cc * (1 + |Ce|) ^ 4 * 1 * (1 + M) ^ 4
            * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by ring
  exact ⟨h12sm3.add hN3sm3, h123.1, le_trans hnorm hfin⟩

end Work.FTS.StrongPersist.L3Rhs
