/-
# `E4R3/N4C/rowsHkT` — the honest (class-`C`) `ℋ⁴`-honesty table of the §8 pieces

`Work.FTS.OpenPkg.PiecesHk α g Φs Φg` is the 31-conjunct table consumed by the primed
`IP`-interface: the `HkMem α 4`-honesty of the 27 pieces `N_i^{ab}` of the split of `N`, of
the `N₀`-block, of `N` itself, of `AK α` and of `D_z g`.

This module proves it in the row context of the honest chapter
(`N4C.CtxT Cs Ce α₂ α g Φs Φg`: `ClassC α g`, the open coercivity class, `StarPkgo2 α Cs Φs`
and `EllPkgGo α Ce g Φg`), i.e. with open-quadrant smoothness and `ℋ^k`-honesty only.  No
`IP`-level clause is needed — neither `N4Norm'` nor `N4ExtraH` is used.

All the mathematical content is already in the tree, in the class-`C` honesty modules of
`StrongEps/ClassCRHS` and `StrongEps/EpsZero/ClassCHk`:

* `N0fix α`           — `NonlinRows.HkMem_N0fix` (unconditional);
* `N03g` … `N06F`     — the seven product rows, as proved inside
  `StrongEps.EpsZero.ClassCHk.N0Mem` (adapted here to return the individual conjuncts);
* `N_i^{ab}` (`i=1..5`) — `EpsZero.ClassCHk.good_N*` (`Good.hk`);
* `N₀`, `N`           — `EpsZero.ClassCHk.N0Mem`, `.NMem`;
* `AK α`              — `NonlinRows.HkMem_AK`;
* `D_z g`             — `EllipticEst.UopHk.HkMem_Dz_of_smoothOpen` (level-`5` honesty of `g`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.Nonlinear.Open.PiecesHkOpen
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.NMem
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.NMemAux
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.NMemAux2
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.N0Mem
import Submission.Work.FTS.NonlinRows.NAux3
import Submission.Work.FTS.NonlinRows.NRow1
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.OpenPkg.wprod_field_winf
import Submission.Work.FTS.OpenPkg.angmul_field
import Submission.Work.FTS.OpenPkg.l12H_field
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.StrongEps.ClassCRHS.N0_split_open
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0Aux
import Submission.Work.FTS.EllipticEst.UopHk.hkMemDzPth_of_shifted
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## The seven rows of the `N₀`-block

The individual conjuncts of the proof of `EpsZero.ClassCHk.N0Mem`, exposed as a single
private lemma (the union of the seven product rows, each transferred from its open-quadrant
form). -/
private theorem hkMem_N0_rows {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : Fn}
    (hg : Work.FTS.ClassC.ClassC α g) :
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N0fix α) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N03g α g) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04aF α g) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04bF α g) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05aF α g) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05bF α g) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N06F α g) := by
  -- ## the universal product rules
  obtain ⟨_Cp, _hCp, hprod⟩ := Work.FTS.OpenPkg.prod_field
  obtain ⟨_Cw, _hCw, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨_Cang, _hCang, hang⟩ := Work.FTS.OpenPkg.angmul_field
  obtain ⟨_C1, _hC1, hl12⟩ := Work.FTS.OpenPkg.l12H_field
  obtain ⟨_CF, _hCF, hDthFstarW⟩ := Work.FTS.Nonlinear.FstarPkg.DthFstar_W
  obtain ⟨_Cdz, _hCdz, hDzFstarW⟩ := Work.FTS.Nonlinear.FstarPkg.DzFstar_W
  obtain ⟨_Cw0, _hCw0, hc2mL12FstarW⟩ := Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W
  -- ## the class-`C` data
  have hsmw : Work.FTS.EllipticEst.SmoothOpen g := hg.reg
  have hm7 : Work.Spaces.HkMem α 7 g := hg.mem
  have hm5 : Work.Spaces.HkMem α 5 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 5 (by norm_num) hm7
  have hm4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 4 (by norm_num) hm7
  have hQw : Work.FTS.VocabO.HQo α 4 g := ⟨hsmw, hm4⟩
  have hL12 := hl12 α hα hα1 g hQw hg.l12
  have hL12mem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z) := hL12.1
  have hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.L12 g z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_aux hα hg
  have hDthw_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth g) :=
    Work.FTS.StrongEps.ClassCRHS.hkMem_Dth_of_smoothOpen hα 4 hsmw hm5
  have hDzw_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hsmw hm5
  -- ## the factor `A = (3/(2α))·L₁₂(g)`
  have hAsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α)) hL12sm
  have hAmem : Work.Spaces.HkMem α 4
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hL12mem
  -- ## the factor `B = c2m·L₁₂(g)`
  have hc2msm : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) :=
    Work.FTS.GalFields.RHS.smoothOpen_c2m_ang
  have hc2mb : ∀ θ ∈ Work.Spaces.Iθ, |Work.Construction.c2m θ| ≤ 1000 := by
    intro θ hθ
    have h := Work.FTS.Nonlinear.Pieces.abs_c2m_le_two hθ
    linarith
  have hc2mIt : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
        ≤ 1000 * Real.sin (2 * θ) := by
    intro i hi hi4 θ hθ
    have h := Work.FTS.Nonlinear.Pieces.DthIter_c2m_le i hi hi4 θ
    rw [show (Real.sin (2 * θ)) ^ (2 : ℝ) = (Real.sin (2 * θ)) ^ (2 : ℕ) from
      Real.rpow_natCast _ 2] at h
    have h0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hsq : Real.sin (2 * θ) ^ 2 ≤ Real.sin (2 * θ) := by nlinarith
    linarith
  have hBmem : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z) :=
    (hang α hα hα1 (fun θ => Work.Construction.c2m θ)
      (fun z θ => Work.Construction.L12 g z) 1000 hc2msm hc2mb hc2mIt hL12sm hL12mem).1
  have hBsmt : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_mul hc2msm hL12sm
  have hnegBmem : Work.Spaces.HkMem α 4
      (fun z θ => (-1) * (Work.Construction.c2m θ * Work.Construction.L12 g z)) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (-1) hBmem
  -- ## the fixed profile atoms
  have hFstarsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hDthFsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Construction.Fstar α)) := hFstarsm.Dth
  have hDzFsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (Work.Construction.Fstar α)) := hFstarsm.Dz
  have hc2mL12Fsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.NonlinRows.smoothOpen_mul hc2msm
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_L12_Fstar α)
  -- ## row 0: the fixed block
  have hp0 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.NonlinRows.HkMem_N0fix α hα hα1
  -- ## row 1: `N₀₃ᵍ = (1/α)·L₁₂(g)·g`
  have h1eq : Work.FTS.Nonlin.N03g α g
      = fun z θ => (1 / α) * (Work.Construction.L12 g z * g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N03g, Work.Construction.N03]
    ring
  have hp1 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N03g α g) := by
    rw [h1eq]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (1 / α)
      (hprod α hα hα1 (fun z θ => Work.Construction.L12 g z) g
        ⟨hL12sm, hL12mem⟩ ⟨hsmw, hm4⟩).1
  -- ## row 2: `N₀₄ᵃ = D_θF_* · A`
  have h2eq : Work.FTS.Nonlin.N04aF α g
      = fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * ((3 / (2 * α)) * Work.Construction.L12 g z) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04aF, Work.Construction.N04a, Work.Construction.s2,
      Work.Spaces.Dth]
    ring
  have hp2 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04aF α g) := by
    rw [h2eq]
    exact (hwprod α hα hα1 (Work.Spaces.Dth (Work.Construction.Fstar α))
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      hDthFsm (hDthFstarW α hα hα1).1 ⟨hAsm, hAmem⟩).1
  -- ## row 3: `N₀₄ᵇ = D_θg · A`
  have h3eq : Work.FTS.Nonlin.N04bF α g
      = fun z θ => Work.Spaces.Dth g z θ
          * ((3 / (2 * α)) * Work.Construction.L12 g z) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04bF, Work.Construction.N04b, Work.Construction.s2,
      Work.Spaces.Dth]
    ring
  have hp3 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04bF α g) := by
    rw [h3eq]
    exact (hprod α hα hα1 (Work.Spaces.Dth g)
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      ⟨hsmw.Dth, hDthw_mem⟩ ⟨hAsm, hAmem⟩).1
  -- ## row 4: `N₀₅ᵃ = D_zF_* · (-B)`
  have h4eq : Work.FTS.Nonlin.N05aF α g
      = fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          * ((-1) * (Work.Construction.c2m θ * Work.Construction.L12 g z)) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05aF, Work.Construction.N05a]
    ring
  have hp4 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05aF α g) := by
    rw [h4eq]
    exact (hwprod α hα hα1 (Work.Spaces.Dz (Work.Construction.Fstar α))
      (fun z θ => (-1) * (Work.Construction.c2m θ * Work.Construction.L12 g z))
      hDzFsm (hDzFstarW α hα hα1).1
      ⟨Work.FTS.NonlinRows.smoothOpen_const_mul (-1) hBsmt, hnegBmem⟩).1
  -- ## row 5: `N₀₅ᵇ = -B·D_zg`
  have h5eq : Work.FTS.Nonlin.N05bF α g
      = fun z θ => (-1) * ((Work.Construction.c2m θ * Work.Construction.L12 g z)
          * Work.Spaces.Dz g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05bF, Work.Construction.N05b]
    ring
  have hp5 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05bF α g) := by
    rw [h5eq]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-1)
      (hprod α hα hα1
        (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z)
        (Work.Spaces.Dz g) ⟨hBsmt, hBmem⟩ ⟨hsmw.Dz, hDzw_mem⟩).1
  -- ## row 6: `N₀₆ = -c2m·L₁₂(F_*)·D_zg`
  have h6eq : Work.FTS.Nonlin.N06F α g
      = fun z θ => (-1) * ((Work.Construction.c2m θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z)
          * Work.Spaces.Dz g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N06F, Work.Construction.N06]
    ring
  have hp6 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N06F α g) := by
    rw [h6eq]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-1)
      (hwprod α hα hα1
        (fun z θ => Work.Construction.c2m θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z)
        (Work.Spaces.Dz g) hc2mL12Fsm (hc2mL12FstarW α hα hα1).1
        ⟨hsmw.Dz, hDzw_mem⟩).1
  exact ⟨hp0, hp1, hp2, hp3, hp4, hp5, hp6⟩

/-- Every one of the 31 conjuncts of `Work.FTS.OpenPkg.PiecesHk` is `ℋ⁴`-honest on the
class-`C` row context.  Nothing here uses the `IP`-level clauses (`N4Norm'`, `N4ExtraH`). -/
private theorem piecesHk_of_ctx {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {g Φs Φg : Fn} (hg : Work.FTS.ClassC.ClassC α g)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.OpenPkg.PiecesHk α g Φs Φg := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hkMem_N0_rows hα hα1 hg
  have hm7 : Work.Spaces.HkMem α 7 g := hg.mem
  have hm5 : Work.Spaces.HkMem α 5 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hg.reg 5 (by norm_num) hm7
  have hDz : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hg.reg hm5
  exact
    { p1 := h1
      p2 := h2
      p3 := h3
      p4 := h4
      p5 := h5
      p6 := h6
      p7 := h7
      p8 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N1gg hα hα1 hg hell).hk
      p9 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N1gs hα hα1 hg hell).hk
      p10 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N1sg hα hα1 hg hstar).hk
      p11 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N1ss hα hα1 hstar).hk
      p12 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N2gg hα hα1 hg hell).hk
      p13 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N2gs hα hα1 hell).hk
      p14 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N2sg hα hα1 hg hstar).hk
      p15 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N2ss hα hα1 hstar).hk
      p16 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N3gg hα hα1 hg hell).hk
      p17 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N3gs hα hα1 hell).hk
      p18 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N3sg hα hα1 hg hstar).hk
      p19 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N3ss hα hα1 hstar).hk
      p20 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N4gg hα hα1 hg).hk
      p21 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N4gs hα hα1 hg).hk
      p22 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N4sg hα hα1 hg).hk
      p23 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N4ss hα hα1).hk
      p24 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N5gg hα hα1 hg).hk
      p25 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N5gs hα hα1 hg).hk
      p26 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N5sg hα hα1 hg).hk
      p27 := (Work.FTS.StrongEps.EpsZero.ClassCHk.good_N5ss hα hα1).hk
      pAK := Work.FTS.NonlinRows.HkMem_AK α hα hα1
      pN0 := Work.FTS.StrongEps.EpsZero.ClassCHk.N0Mem hα hα1 hg hell
      pN := Work.FTS.StrongEps.EpsZero.ClassCHk.NMem hα hα1 hg hell hstar
      pDz := hDz }

theorem rowsHkT (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.OpenPkg.PiecesHk α g Φs Φg := by
  intro α g Φs Φg hctx
  exact piecesHk_of_ctx hctx.hα hctx.hα1 hctx.hg hctx.hell hctx.hs

end Work.FTS.StrongEps.E4R3.N4C
