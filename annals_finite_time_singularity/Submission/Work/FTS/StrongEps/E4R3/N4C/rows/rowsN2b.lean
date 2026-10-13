/-
# `E4R3/N4C/rows/rowsN2b` — rows 14 and 15 of the honest §8 table

The target `Work.FTS.StrongEps.E4R3.N4C.rows.rowsN2b` proves, from the two interfaces
(`hN : OpenPkg.N4Norm' Ci α₂`, `hE : N4C.N4ExtraH IP α₂ Ct`) and for every honest row context
`CtxT Cs Ce α₂ α g Φs Φg`, the two **`N₂`-rows with the star stream function `Φs`**:

* row 14: `|IP α (N₂^{sg}) g| ≤ K √α X²` with `N₂^{sg} = -2·𝒰(Φ̃_*)·∂_θg`, `X = Xn α g`;
* row 15: `Xn α (N₂^{ss}) ≤ K α²` with `N₂^{ss} = -2·𝒰(Φ̃_*)·∂_θF_*`.

Both are the honest (class-`C`) counterparts of `Work.FTS.Nonlinear.Open.Row14` /
`Open.Row15`, whose *frozen* statements carry `GalClass α g` (with `SmoothQuad`) and the frozen
interface `OpenPkg.N4Extra'`.  The only differences are:

* the `N4Extra'` clauses `t4`/`smul`/`congr` are replaced by the honest `N4ExtraH` clauses, whose
  first-argument hypotheses are the honest class `HQo α 4 = SmoothOpen ∧ HkMem α 4` (and whose
  `t4` additionally asks for `SmoothOpen g`, `HkMem α 4/5 g`, `DecayAll 4 g`), all supplied by
  the `CtxT` projections of `rows/Hon.lean` and `rows/HonDecay.lean`;
* `GalClass`/`RegQ` are never used: the star coefficients are priced by `StarPkgo2.UsW`
  (`Ǔ = 𝒰(Φ̃_*)/sin 2θ` with `WlInf α 4 Ǔ ≤ Cs α`) resp. `StarPkgo2.UszW`.

Row 15's proof (`rowN2ssHon`) never touches `hgal` in the frozen file, so it is copied verbatim;
only the context is unpacked through `CtxT`.  Row 14's proof (`rowN2sgHon`) needs the honest
replacement of the three algebraic clauses: the pointwise identification
`N₂^{sg} = -2·(Ǔ · D_θg)` on the open quadrant is transferred by `N4ExtraH.congr` (both
representatives in `HQo α 4`, using `N4C.goodO_of_eqOn_Qd` and the honest product rule
`N4Norm'.wprod`), and the `-2` is pulled out by `N4ExtraH.smul`.  The rest is the frozen chain
`WDp 4 Ǔ ≤ CW·WlInf α 4 Ǔ ≤ CW·(max Cs 0)·α` and `α^{-1/2}·α = √α`.

Every declaration below is fully proved.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.Hon
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.HonDecay
import Submission.Work.FTS.Nonlinear.Open.Row14
import Submission.Work.FTS.Nonlinear.Open.Row15
import Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.Atoms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.StrongEps.E4R3.N4C.rows

open Work.FTS.Galerkin (Fn)
open Work.FTS.VocabO (HQo)
open Work.FTS.Nonlinear.Open

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Row 14: `N₂^{sg} = -2·𝒰(Φ̃_*)·∂_θg` -/

/-- **Row 14 of the honest §8 table** (pairing bound only): for every honest context,

  `|IP α (N₂^{sg} α Φs g) g| ≤ K·√α·(Xn α g)²`.

Constant `K = 2·(CW·(Ct·max Cs 0)) + 1`, with `CW` the constant of
`OpenPkg.WDp_le_WlInf`. -/
theorem rowN2sgHon (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α Ce : ℝ} {g Φs Φg : Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N2sg α Φs g) g|
        ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨CW, hCW0, hCW⟩ := Work.FTS.OpenPkg.WDp_le_WlInf
  obtain ⟨hCt, _hα₂⟩ := hE.pos
  refine ⟨2 * (CW * (Ct * max Cs 0)) + 1, ?_, ?_⟩
  · have h1 : 0 ≤ CW * (Ct * max Cs 0) :=
      mul_nonneg hCW0.le (mul_nonneg hCt.le (le_max_right Cs 0))
    linarith
  · intro α Ce g Φs Φg hctx
    have hα : 0 < α := hctx.hα
    have hα1 : α ≤ 1 := hctx.hα1
    have hαα₂ : α ≤ α₂ := hctx.hαα₂
    have hαIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
    have hs2 : Work.FTS.VocabO2.StarPkgo2 α Cs Φs := hctx.hs
    have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hs2.toStarPkgo
    have hSmG : Work.FTS.EllipticEst.SmoothOpen g := hctx.hSmoothOpen
    have hqo4 : HQo α 4 g := hctx.hqo4
    have hmem4 : Work.Spaces.HkMem α 4 g := hctx.hkMem4
    have hmem5 : Work.Spaces.HkMem α 5 g := hctx.hkMem5
    have hdec : Work.Spaces.DecayAll 4 g := hctx.hdecay
    -- the coefficient `Ǔ = 𝒰(Φ̃_*)/sin 2θ` priced by `StarPkgo2.UsW`
    set Uv : Fn := fun z θ =>
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ with hUv
    have hUvmem : Work.Spaces.WlInfMem α 4 Uv := by
      rw [hUv]; exact hs2.UsW.1
    have hUvle : Work.Spaces.WlInf α 4 Uv ≤ Cs * α := by
      rw [hUv]; exact hs2.UsW.2
    have hΦ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
      Work.FTS.NonlinRows.NRow10aux.smoothOpen_PhiTs hα hα1 hs
    have hUopsm : Work.FTS.EllipticEst.SmoothOpen
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) := by
      rw [Work.FTS.EllipticEst.Uop_eq]
      exact Work.FTS.EllipticEst.smoothOpen_Uop hΦ
    have hUvsm : Work.FTS.EllipticEst.SmoothOpen Uv := by
      rw [hUv]
      exact Work.FTS.EllipticEst.RPFresh.smoothOpen_div_sin hUopsm
    -- `D_θg` is honest
    have hDthSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth g) := hSmG.Dth
    have hDthMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth g) := hctx.hkMemDth
    have hDthHQo : HQo α 4 (Work.Spaces.Dth g) := ⟨hDthSm, hDthMem⟩
    -- the honest product `Ǔ · D_θg`, by the `𝒲^{4,∞}`-product rule
    have hprod := hN.wprod α hαIoc Uv (Work.Spaces.Dth g) hUvsm hUvmem hDthHQo
    have hUvDth : HQo α 4 (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) :=
      ⟨Work.FTS.StrongPersist.H6Pair6Aux.so_mul hUvsm hDthSm, hprod.1⟩
    have hUvDth2 : HQo α 4 (fun z θ => -2 * (Uv z θ * Work.Spaces.Dth g z θ)) :=
      Work.FTS.StrongEps.E4R3.N4C.goodO_const_mul (-2) hUvDth
    -- `Ǔ·D_θg = 𝒰(Φ̃_*)·∂_θg` on the open quadrant (both sides vanish at `θ = 0, π/2`)
    have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
        (fun z θ => -2 * (Uv z θ * Work.Spaces.Dth g z θ)) z θ
          = Work.FTS.Nonlin.N2sg α Φs g z θ := by
      intro z _hz θ hθ
      have hv1 : Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z 0 = 0 := hs.vanishU.1 z
      have hv2 : Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z (Real.pi / 2) = 0 :=
        hs.vanishU.2 z
      have hsin : Real.sin (2 * (Real.pi / 2)) = 0 := by
        rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      simp only [hUv, Work.FTS.Nonlin.N2sg, Work.Spaces.Dth, Work.Spaces.pth,
        Work.Construction.s2]
      rcases eq_or_lt_of_le hθ.1 with h0 | hpos
      · subst h0
        simp [hv1]
      · rcases eq_or_lt_of_le hθ.2 with hpi | hlt
        · subst hpi
          simp [hv2, hsin]
        · have hsne : Real.sin (2 * θ) ≠ 0 :=
            ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
              (by linarith [Real.pi_pos]))
          field_simp
    -- the honest class of `N₂^{sg}`
    have hN2sgQo : HQo α 4 (Work.FTS.Nonlin.N2sg α Φs g) :=
      Work.FTS.StrongEps.E4R3.N4C.goodO_of_eqOn_Qd hUvDth2
        (fun z θ hQd => hpt z hQd.1 θ ⟨le_of_lt hQd.2.1, le_of_lt hQd.2.2⟩)
    -- `WlInfMem` gives the `D`-sup membership, with the pointwise constant `200`
    have hWdMem : Work.FTS.VocabO.WDMem 4 Uv := by
      intro b j hbj
      refine ⟨200 * Work.Spaces.WlInf α 4 Uv, ?_⟩
      intro z θ hz hθ hθ2
      exact Work.FTS.OpenPkg.mixed_le_WlInf_200 hα hα1 hUvsm hUvmem hbj hz ⟨hθ, hθ2⟩
    -- the honest transport clause for a `D`-sup coefficient
    have ht4 := hE.t4 α hαIoc Uv g hUvsm hWdMem hSmG hmem4 hmem5 hdec
    have hWDp : Work.FTS.VocabO.WDp 4 Uv ≤ CW * Work.Spaces.WlInf α 4 Uv :=
      hCW α Uv hα hα1 hUvsm hUvmem
    have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hsqrt : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
      rw [Real.sqrt_eq_rpow]
      have h := Real.rpow_add hα (-(1 / 2 : ℝ)) (1 : ℝ)
      rw [Real.rpow_one, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
      exact h.symm
    -- the pairing at the honest representative
    have hIPval : IP α (Work.FTS.Nonlin.N2sg α Φs g) g
        = -2 * IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g := by
      have hsm := hE.smul α hαIoc (-2) (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g
        hUvDth hqo4
      have hcg := hE.congr α hαIoc (Work.FTS.Nonlin.N2sg α Φs g)
        (fun z θ => -2 * (Uv z θ * Work.Spaces.Dth g z θ)) g hN2sgQo hUvDth2 hqo4
        (fun z θ hQd => (hpt z hQd.1 θ ⟨le_of_lt hQd.2.1, le_of_lt hQd.2.2⟩).symm)
      rw [hcg, hsm]
    have hWlL : Work.Spaces.WlInf α 4 Uv ≤ max Cs 0 * α :=
      le_trans hUvle (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
    have hWDpL : Work.FTS.VocabO.WDp 4 Uv ≤ CW * (max Cs 0 * α) :=
      le_trans hWDp (mul_le_mul_of_nonneg_left hWlL hCW0.le)
    have hIPb : |IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g|
        ≤ CW * Ct * max Cs 0 * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
      refine le_trans ht4 ?_
      have hA : 0 ≤ Ct * α ^ (-(1 / 2 : ℝ)) :=
        mul_nonneg hCt.le (Real.rpow_nonneg hα.le _)
      have hstep : Ct * α ^ (-(1 / 2 : ℝ)) * Work.FTS.VocabO.WDp 4 Uv
            * Work.FTS.Nonlin.Xn α g ^ 2
          ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (CW * (max Cs 0 * α))
            * Work.FTS.Nonlin.Xn α g ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWDpL hA) (sq_nonneg _)
      refine le_trans hstep (le_of_eq ?_)
      rw [show Ct * α ^ (-(1 / 2 : ℝ)) * (CW * (max Cs 0 * α)) * Work.FTS.Nonlin.Xn α g ^ 2
          = CW * Ct * max Cs 0 * (α ^ (-(1 / 2 : ℝ)) * α)
            * Work.FTS.Nonlin.Xn α g ^ 2 from by ring, hsqrt]
      ring
    have hfin : 2 * |IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g|
        ≤ (2 * (CW * (Ct * max Cs 0)) + 1)
          * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
      have hX2nn : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2 :=
        mul_nonneg (Real.sqrt_nonneg α) (sq_nonneg _)
      calc 2 * |IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g|
          ≤ 2 * (CW * Ct * max Cs 0 * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2)) :=
            mul_le_mul_of_nonneg_left hIPb (by norm_num)
        _ = 2 * (CW * (Ct * max Cs 0)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by ring
        _ ≤ (2 * (CW * (Ct * max Cs 0)) + 1)
              * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
            refine mul_le_mul_of_nonneg_right ?_ hX2nn
            linarith
    calc |IP α (Work.FTS.Nonlin.N2sg α Φs g) g|
        = |(-2) * IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g| := by rw [hIPval]
      _ = 2 * |IP α (fun z θ => Uv z θ * Work.Spaces.Dth g z θ) g| := by
            rw [abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]; ring
      _ ≤ _ := hfin

/-! ## Row 15: `N₂^{ss} = -2·𝒰(Φ̃_*)·∂_θF_*` -/

/-- **Row 15 of the honest §8 table** (norm bound only): for every honest context,

  `Xn α (N₂^{ss} α Φs) ≤ K·α²`.

The proof is that of `Work.FTS.Nonlinear.Open.Row15` verbatim (the frozen proof never uses the
Galerkin class of `g` nor the `N4Extra'` clauses): it factors the piece as
`ψ(z)·(2·C15 α θ·G15 α Φs z θ)` and feeds the two pointwise families of
`Nonlinear.Open.Row15Aux.Bound` into `NonlinRows.wtoHQ_of_pointwise_open`, with the
`𝒲^{4,∞}`-coefficient `G15 α Φs` priced by the field `StarPkgo2.UszW`. -/
theorem rowN2ssHon (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α Ce : ℝ} {g Φs Φg : Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs) ≤ K * α ^ 2 := by
  obtain ⟨Cw, hCw, hwto⟩ := Work.FTS.NonlinRows.wtoHQ_of_pointwise_open
  obtain ⟨Cpsi, hCpsipos, hpsib⟩ := Work.FTS.NonlinRows.pzIter_psi15_le
  obtain ⟨KA, hKApos, hKAb0⟩ := dthU_iter_A15_flat_le
  obtain ⟨KB, hKBpos, hKBb0⟩ := dthU_iter_A15_weight_le
  refine ⟨Cw * (10 ^ 7 * Cpsi * (KA + KB + 1) + 1) * (max Cs 0) + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) < 10 ^ 7 * Cpsi * (KA + KB + 1) + 1 := by positivity
    have h2 : 0 ≤ Cw * (10 ^ 7 * Cpsi * (KA + KB + 1) + 1) * max Cs 0 :=
      mul_nonneg (mul_nonneg hCw.le h1.le) (le_max_right Cs 0)
    linarith
  · intro α Ce g Φs Φg hctx
    have hα : 0 < α := hctx.hα
    have hα1 : α ≤ 1 := hctx.hα1
    have hs2 : Work.FTS.VocabO2.StarPkgo2 α Cs Φs := hctx.hs
    have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hs2.toStarPkgo
    have hGm : Work.Spaces.WlInfMem α 4 (Work.FTS.NonlinRows.G15 α Φs) := hs2.UszW.1
    have hGle : Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) ≤ Cs * α := hs2.UszW.2
    have hΛ : 0 ≤ Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) :=
      Work.FTS.H2.WlInf_nonneg hGm
    have hΛle : Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) ≤ max Cs 0 * α :=
      le_trans hGle (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
    obtain ⟨hSO, hAfam, hBfam⟩ := row15_pointwise hα hα1 hs hKApos.le hKBpos.le hCpsipos
      (fun c m hcm hm z hz θ => hpsib c m hcm hm z hz θ)
      (fun a ha θ hθ => hKAb0 α hα hα1 a ha θ hθ)
      (fun a ha θ hθ => hKBb0 α hα hα1 a ha θ hθ)
      (Work.FTS.NonlinRows.smoothOpen_G15 hα hα1 hs) hGm
    set CW : ℝ := 10 ^ 7 * Cpsi * (KA + KB + 1) + 1 with hCW
    set Λ : ℝ := Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) with hΛdef
    set W : ℝ := CW * α * Λ with hWdef
    have hCW0 : 0 < CW := by rw [hCW]; positivity
    have hW0 : 0 ≤ W := by
      rw [hWdef]; exact mul_nonneg (mul_nonneg hCW0.le hα.le) hΛ
    obtain ⟨_hmem, hxn⟩ := hwto α (Work.FTS.Nonlin.N2ss α Φs) W hα hα1 hW0 hSO
      (fun m hm z hz θ hθ => by
        have := hAfam m hm z hz θ hθ
        rwa [hWdef, hCW, hΛdef] at this)
      (fun i l hi hli z hz θ hθ => by
        have := hBfam i l hi hli z hz θ hθ
        rwa [hWdef, hCW, hΛdef] at this)
    have hX : W ≤ CW * (max Cs 0) * α ^ 2 := by
      rw [hWdef, hΛdef]
      have hstep : α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
          ≤ α * (max Cs 0 * α) := mul_le_mul_of_nonneg_left hΛle hα.le
      calc CW * α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
          = CW * (α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)) := by ring
        _ ≤ CW * (α * (max Cs 0 * α)) := mul_le_mul_of_nonneg_left hstep hCW0.le
        _ = CW * (max Cs 0) * α ^ 2 := by ring
    have h1 : Cw * W ≤ Cw * (CW * (max Cs 0) * α ^ 2) :=
      mul_le_mul_of_nonneg_left hX hCw.le
    have h2 : Cw * (CW * (max Cs 0) * α ^ 2)
        ≤ (Cw * (10 ^ 7 * Cpsi * (KA + KB + 1) + 1) * (max Cs 0) + 1) * α ^ 2 := by
      rw [hCW]
      have h4 : (0 : ℝ) ≤ Cw * (10 ^ 7 * Cpsi * (KA + KB + 1) + 1) * max Cs 0 :=
        mul_nonneg (mul_nonneg hCw.le (by positivity)) (le_max_right Cs 0)
      have h5 : 0 ≤ α ^ 2 := sq_nonneg α
      nlinarith
    exact hxn.trans (h1.trans h2)

/-! ## The target -/

theorem rowsN2b (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N2sg α Φs g) g| ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs) ≤ K * α ^ 2 := by
  obtain ⟨K1, hK1, h1⟩ := rowN2sgHon IP hN hE
  obtain ⟨K2, hK2, h2⟩ := rowN2ssHon IP hN hE
  refine ⟨max K1 K2, lt_of_lt_of_le hK1 (le_max_left K1 K2), ?_⟩
  intro α g Φs Φg hctx
  refine ⟨?_, ?_⟩
  · refine (h1 hctx).trans (mul_le_mul_of_nonneg_right (le_max_left K1 K2) ?_)
    exact mul_nonneg (Real.sqrt_nonneg α) (sq_nonneg _)
  · exact (h2 hctx).trans (mul_le_mul_of_nonneg_right (le_max_right K1 K2) (sq_nonneg α))

end Work.FTS.StrongEps.E4R3.N4C.rows
