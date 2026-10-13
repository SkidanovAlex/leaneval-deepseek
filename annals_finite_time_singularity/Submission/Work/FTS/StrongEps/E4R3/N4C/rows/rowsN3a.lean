/-
# `E4R3/N4C/rows/rowsN3a` — rows 16 and 17 of the honest §8 table

The target `Work.FTS.StrongEps.E4R3.N4C.rows.rowsN3a` proves, from the two interfaces
(`hN : OpenPkg.N4Norm' Ci α₂`, `hE : N4C.N4ExtraH IP α₂ Ct`) and for every honest row context
`CtxT Cs Ce α₂ α g Φs Φg`, the two rows

* row 16: `|IP α (N₃^{gg}) g| ≤ K X³` with `N₃^{gg} = -2α·V(Φ̃_g)·D_z g`, `X = Xn α g`;
* row 17: `Xn α (N₃^{gs}) ≤ K α^{3/2} X` with `N₃^{gs} = -2α·V(Φ̃_g)·D_z F_*`.

Both are the honest (class-`C`) counterparts of `Work.FTS.Nonlinear.Open.Row16` /
`Open.Row17`, whose *frozen* statements carry `GalClass α g` (with `SmoothQuad`) and the frozen
interface `OpenPkg.N4Extra'`.  The differences are only the substitutions listed in
`rows/NOTES_rowsNT.md`:

* `GalClass`/`RegQ` is never used: the `g`-side hypotheses of the honest clauses
  (`SmoothOpen`, `HkMem α 4/5`, `DecayAll 4`) come from the `CtxT` projections of
  `rows/Hon.lean` and `rows/HonDecay.lean`;
* the frozen `N4Extra'.t2` clause is replaced by the honest `N4ExtraH.t2`, whose first-argument
  hypotheses are the honest class `HQo α 4 = SmoothOpen ∧ HkMem α 4` (supplied by
  `EllPkgGo.V`), and whose `g`-side asks for `SmoothOpen g`, `HkMem α 4 g`, `HkMem α 5 g` and
  `DecayAll 4 g` instead of `RegQ α 4 g`;
* the frozen `N4Extra'.smul` is replaced by `N4ExtraH.smul`, which needs `HQo α 4` of both
  arguments — the product `V(Φ̃_g)·D_z g` is put in `ℋ⁴` by `N4Norm'.prod` (using
  `HkMem α 5 g` for `D_z g`);
* row 17 prices the radial coefficient `D_z F_*` by `Nonlin.DzFstar_W`
  (`WlInf α 4 (D_zF_*) ≤ Cα`) through `N4Norm'.wprod`.

Nothing here uses the `Ce`-clause of `StarPkgo2` (`Φs` is untouched), and the sign of `Ce`/`Cs`
is absorbed by `max Ce 1` at the few places where it matters.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.Hon
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.HonDecay
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.Nonlinear.Pieces.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C.rows

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `SmoothOpen` is closed under products (interior `C^∞` on the open quadrant). -/
theorem so_mul_rowsN3a {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen
  convert hf.mul hg using 1
  ext p
  rfl

/-- **Rows 16 and 17 of the honest §8 table.**

Constant `K = max (8·Ct·max Ce 1 + 1) (2·Ci·(CF + 1)·max Ce 1 + 1)`, where `CF` is the constant
of `Nonlin.DzFstar_W`; the two summands are the constants of the two rows. -/
theorem rowsN3a (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N3gg α g Φg) g| ≤ K * Work.FTS.Nonlin.Xn α g ^ 3 ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3gs α g Φg)
          ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
  have hCt : 0 < Ct := hE.pos.1
  obtain ⟨hCi, _hα₂pos⟩ := hN.pos
  obtain ⟨CF, _hCF, hDzF⟩ := Work.FTS.Nonlin.DzFstar_W
  have hCmax : 0 ≤ max Ce 1 := le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_right Ce 1))
  refine ⟨max (8 * Ct * max Ce 1 + 1) (2 * Ci * (CF + 1) * max Ce 1 + 1),
    lt_max_of_lt_left (by positivity), ?_⟩
  intro α g Φs Φg hctx
  have hα : 0 < α := hctx.hα
  have hα1 : α ≤ 1 := hctx.hα1
  have hαα₂ : α ≤ α₂ := hctx.hαα₂
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  constructor
  · -- ---------- row 16 : `|(N₃^{gg}, g)| ≤ K X³` ----------
    have hVnorm : Work.FTS.Nonlin.Xn α
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) ≤ Ce * Work.FTS.Nonlin.Xn α g :=
      hctx.hell.V.2
    have hVthb : Work.FTS.VocabO.CoefTh 1
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
        ≤ Ce * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g := hctx.hell.Vth.2
    -- the `g`-side slot `D_z g ∈ ℋ⁴`
    have hDzMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g) := hctx.hkMemDz
    have hDzSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz g) := hctx.hSmoothOpen.Dz
    -- the product `V(Φ̃_g)·D_z g` is in `ℋ⁴`
    have hprod := (hN.prod α hIoc (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
      (Work.Spaces.Dz g) hctx.hell.V.1 ⟨hDzSm, hDzMem⟩).1
    have hprodQ : Work.FTS.VocabO.HQo α 4 (fun z θ =>
        Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ * Work.Spaces.Dz g z θ) :=
      ⟨so_mul_rowsN3a hctx.hell.V.1.1 hDzSm, hprod⟩
    -- `N₃^{gg}` is `-2α` times that product
    have hN3 : Work.FTS.Nonlin.N3gg α g Φg
        = fun z θ => (-2 * α) * (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ
            * Work.Spaces.Dz g z θ) := by
      funext z θ
      simp only [Work.FTS.Nonlin.N3gg]
      ring
    have hIPeq : IP α (Work.FTS.Nonlin.N3gg α g Φg) g
        = (-2 * α) * IP α (fun z θ =>
            Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ
              * Work.Spaces.Dz g z θ) g := by
      rw [hN3]
      exact hE.smul α hIoc (-2 * α) _ g hprodQ hctx.hqo4
    rw [hIPeq]
    have habs : |(-2 : ℝ) * α| = 2 * α := by
      rw [abs_of_neg (by linarith : (-2 : ℝ) * α < 0)]
      ring
    rw [abs_mul, habs]
    -- the `D_z`-transport estimate for the coefficient `V(Φ̃_g)`
    have ht2 := hE.t2 α hIoc (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) g
      hctx.hell.V.1.1 hctx.hell.V.1.2 hctx.hell.Vth.1
      hctx.hSmoothOpen hctx.hkMem4 hctx.hkMem5 hctx.hdecay
    refine (mul_le_mul_of_nonneg_left ht2 (by linarith : (0 : ℝ) ≤ 2 * α)).trans ?_
    -- the two coefficient norms, in terms of `X = |g|_{ℋ⁴}`
    have h1 : Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
        ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g :=
      hVnorm.trans (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hX0)
    have h2 : Work.FTS.VocabO.CoefTh 1
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
        ≤ max Ce 1 * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g :=
      hVthb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hA0) hX0)
    -- `α·α^{-1/2} ≤ 1` and `α·α^{-1/2}·α^{-1/2} = 1`
    have hαhalf : α * α ^ (-(1 / 2 : ℝ)) = α ^ (1 / 2 : ℝ) := by
      calc α * α ^ (-(1 / 2 : ℝ)) = α ^ (1 : ℝ) * α ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
        _ = α ^ ((1 : ℝ) + -(1 / 2)) := (Real.rpow_add hα 1 (-(1 / 2))).symm
        _ = α ^ (1 / 2 : ℝ) := by norm_num
    have hhalf_le : α ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hα.le hα1 (by norm_num)
    have hA1 : α ^ (1 / 2 : ℝ) * α ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hα (1 / 2) (-(1 / 2)),
        show (1 / 2 : ℝ) + -(1 / 2) = 0 by norm_num, Real.rpow_zero]
    have hAA : α * α ^ (-(1 / 2 : ℝ)) * α ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [hαhalf, hA1]
    -- the weighted sum of the two coefficient norms
    have hsum_bound : α * α ^ (-(1 / 2 : ℝ))
        * (Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
          + Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)))
        ≤ 2 * (max Ce 1) * Work.FTS.Nonlin.Xn α g := by
      have e1 : α * α ^ (-(1 / 2 : ℝ))
          * Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
          ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g := by
        calc α * α ^ (-(1 / 2 : ℝ))
              * Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
            ≤ α * α ^ (-(1 / 2 : ℝ)) * (max Ce 1 * Work.FTS.Nonlin.Xn α g) :=
              mul_le_mul_of_nonneg_left h1 (mul_nonneg hα.le hA0)
          _ = max Ce 1 * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g := by
              rw [hαhalf]
              ring
          _ ≤ max Ce 1 * 1 * Work.FTS.Nonlin.Xn α g := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhalf_le hCmax) hX0
          _ = max Ce 1 * Work.FTS.Nonlin.Xn α g := by ring
      have e2 : α * α ^ (-(1 / 2 : ℝ))
          * Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
          ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g := by
        calc α * α ^ (-(1 / 2 : ℝ))
              * Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
            ≤ α * α ^ (-(1 / 2 : ℝ))
              * (max Ce 1 * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g) :=
              mul_le_mul_of_nonneg_left h2 (mul_nonneg hα.le hA0)
          _ = max Ce 1 * (α * α ^ (-(1 / 2 : ℝ)) * α ^ (-(1 / 2 : ℝ)))
              * Work.FTS.Nonlin.Xn α g := by ring
          _ = max Ce 1 * 1 * Work.FTS.Nonlin.Xn α g := by rw [hAA]
          _ = max Ce 1 * Work.FTS.Nonlin.Xn α g := by ring
      linarith [add_le_add e1 e2]
    -- the final arithmetic
    have hkey : 2 * α * (Ct * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
            + Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)))
          * Work.FTS.Nonlin.Xn α g ^ 2)
        ≤ (8 * Ct * max Ce 1 + 1) * Work.FTS.Nonlin.Xn α g ^ 3 := by
      have hre : 2 * α * (Ct * α ^ (-(1 / 2 : ℝ))
            * (Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
              + Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)))
            * Work.FTS.Nonlin.Xn α g ^ 2)
          = 2 * Ct * (α * α ^ (-(1 / 2 : ℝ))
              * (Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
                + Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))))
            * Work.FTS.Nonlin.Xn α g ^ 2 := by ring
      rw [hre]
      calc 2 * Ct * (α * α ^ (-(1 / 2 : ℝ))
              * (Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
                + Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))))
            * Work.FTS.Nonlin.Xn α g ^ 2
          ≤ 2 * Ct * (2 * (max Ce 1) * Work.FTS.Nonlin.Xn α g) * Work.FTS.Nonlin.Xn α g ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hX0 2)
            exact mul_le_mul_of_nonneg_left hsum_bound (mul_nonneg (by norm_num) hCt.le)
        _ = 4 * Ct * max Ce 1 * Work.FTS.Nonlin.Xn α g ^ 3 := by ring
        _ ≤ (8 * Ct * max Ce 1 + 1) * Work.FTS.Nonlin.Xn α g ^ 3 := by
            refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hX0 3)
            linarith [mul_nonneg hCt.le hCmax]
    exact hkey.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hX0 3))
  · -- ---------- row 17 : `|N₃^{gs}|_{ℋ⁴} ≤ K α^{3/2} X` ----------
    -- the `𝒲^{4,∞}`-factor `D_z F_*`, with norm `≤ C α`
    obtain ⟨hDzWmem, hDzWle⟩ := hDzF α hα hα1
    have hDzsmooth : Work.FTS.EllipticEst.SmoothOpen
        (Work.Spaces.Dz (Work.Construction.Fstar α)) :=
      Work.FTS.OpenPkg.smoothOpen_of_smoothQuad
        (Work.FTS.LocData.SmoothQuad.DzIter (Work.FTS.LocData.SmoothQuad_Fstar α) 1)
    have hW' : Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α))
        ≤ (CF + 1) * α :=
      le_trans hDzWle (mul_le_mul_of_nonneg_right (by linarith) hα.le)
    -- the `ℋ⁴`-factor `V(Φ̃_g)`, with norm `≤ Ce X`
    have hVreg : Work.FTS.VocabO.HQo α 4
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) := hctx.hell.V.1
    have hVB : Work.FTS.Nonlin.Xn α
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) ≤ Ce * Work.FTS.Nonlin.Xn α g :=
      hctx.hell.V.2
    have hV' : Work.FTS.Nonlin.Xn α
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
        ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g :=
      le_trans hVB (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hX0)
    -- the mixed product rule
    have hprod := (hN.wprod α hIoc (Work.Spaces.Dz (Work.Construction.Fstar α))
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) hDzsmooth hDzWmem hVreg).2
    have hbound : Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Spaces.Dz (Work.Construction.Fstar α) z θ
            * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * ((CF + 1) * α)
          * (max Ce 1 * Work.FTS.Nonlin.Xn α g) := by
      refine hprod.trans ?_
      refine mul_le_mul ?_ hV' (Work.Spaces.HkNorm_nonneg α 4 _) ?_
      · exact mul_le_mul_of_nonneg_left hW' (mul_nonneg hCi.le hA0)
      · exact mul_nonneg (mul_nonneg hCi.le hA0) (mul_nonneg (by linarith) hα.le)
    -- `N₃^{gs}` is `(-2α)` times that product
    have hN3 : Work.FTS.Nonlin.N3gs α g Φg = fun z θ => (-2 * α) *
        (Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ) := by
      funext z θ
      simp only [Work.FTS.Nonlin.N3gs]
      ring
    have hXeq : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3gs α g Φg)
        = 2 * α * Work.FTS.Nonlin.Xn α (fun z θ =>
            Work.Spaces.Dz (Work.Construction.Fstar α) z θ
              * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ) := by
      rw [hN3, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α (-2 * α)
        (fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ),
        abs_of_neg (by linarith : (-2 : ℝ) * α < 0)]
      ring
    rw [hXeq]
    refine le_trans (mul_le_mul_of_nonneg_left hbound (by linarith)) ?_
    -- `α · α^{-1/2} · α = α^{3/2}`
    have hpow : α * α ^ (-(1 / 2 : ℝ)) * α = α ^ (3 / 2 : ℝ) := by
      have hz : α * α ^ (-(1 / 2 : ℝ)) = Real.sqrt α := by
        rw [Real.sqrt_eq_rpow]
        have h := Real.rpow_add hα (1 : ℝ) (-(1 / 2))
        rw [Real.rpow_one, show (1 : ℝ) + -(1 / 2) = 1 / 2 by norm_num] at h
        exact h.symm
      have h32 : α ^ (3 / 2 : ℝ) = α * Real.sqrt α := by
        rw [show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num, Real.rpow_add hα 1 (1 / 2),
          Real.rpow_one, Real.sqrt_eq_rpow]
      rw [h32, hz]; ring
    have harith : 2 * α * (Ci * α ^ (-(1 / 2 : ℝ)) * ((CF + 1) * α)
          * (max Ce 1 * Work.FTS.Nonlin.Xn α g))
        = 2 * Ci * (CF + 1) * max Ce 1 * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
      rw [← hpow]
      ring
    rw [harith]
    refine le_trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
      (mul_nonneg (Real.rpow_nonneg hα.le _) hX0)) ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _)
      (mul_nonneg (Real.rpow_nonneg hα.le _) hX0)

end Work.FTS.StrongEps.E4R3.N4C.rows
