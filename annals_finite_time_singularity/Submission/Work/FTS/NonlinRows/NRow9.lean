import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false

/-- **Row 9 of the §8 table, in the open-quadrant (primed) vocabulary**: the `ℋ⁴`-honesty and the
bound of the piece `N₁^{g*} = 2·ℛ(Φ̃_g)·F_*`.

The coefficient `F_*` is **not** in `ℋ⁴` (`HkSq α 4 F_* = ∞`), so the honest form `wprod` of the
product rule cannot be used; the correct clause is the `𝒲^{4,∞}`-form `N4Norm'.wprodW`, priced by
`WlInf α 4 F_* ≤ Cα` (`Work.FTS.Nonlin.Fstar_W`) and applied to the `ℋ⁴`-coefficient
`ℛ(Φ̃_g)` of `EllPkgGo.R` (`Xn α ℛ(Φ̃_g) ≤ Ce·Xn α g`).  The exponents combine as
`α^{-1/2}·α = √α`, which is exactly the rate of the row. -/
theorem NRow9 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N1gs α g Φg) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gs α g Φg)
          ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCi, _⟩ := hN.pos
  obtain ⟨CF, hCF, hF⟩ := Work.FTS.Nonlin.Fstar_W
  have hmax : 0 < max Ce 1 := lt_of_lt_of_le zero_lt_one (le_max_right Ce 1)
  refine ⟨2 * (Ci * (CF + 1)) * max Ce 1 + 1, by positivity, ?_⟩
  intro α g Φs Φg hα hα1 hαα₂ hgal hstar hell
  -- positivity of the pieces
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hαIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  -- `F_*` is `SmoothOpen` and in `𝒲^{4,∞}` with norm `≤ Cα`
  have hFsmooth : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  obtain ⟨hFmem, hFle⟩ := hF α hα hα1
  have hFle' : Work.Spaces.WlInf α 4 (Work.Construction.Fstar α) ≤ (CF + 1) * α :=
    le_trans hFle (mul_le_mul_of_nonneg_right (by linarith) hα.le)
  have hFnn : 0 ≤ Work.Spaces.WlInf α 4 (Work.Construction.Fstar α) := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 _ hFmem)
      (Work.Spaces.wlThSum_nonneg α 4 _ hFmem)
  -- the coefficient `R = ℛ(Φ̃_g)` of `EllPkgGo`
  have hRreg : Work.FTS.VocabO.HQo α 4
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) := hell.R.1
  have hRB : Work.FTS.Nonlin.Xn α
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg))
      ≤ Ce * Work.FTS.Nonlin.Xn α g := hell.R.2
  have hRB' : Work.FTS.Nonlin.Xn α
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg))
      ≤ max Ce 1 * Work.FTS.Nonlin.Xn α g :=
    le_trans hRB (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hXg)
  have hRnn : 0 ≤ Work.FTS.Nonlin.Xn α
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) :=
    Work.Spaces.HkNorm_nonneg α 4 _
  -- the `𝒲^{4,∞}`-form of the product rule
  have hprod := hN.wprod α hαIoc (Work.Construction.Fstar α)
    (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) hFsmooth hFmem hRreg
  -- `N₁^{g*}` is `2` times the product `F_* · R`
  have heq : Work.FTS.Nonlin.N1gs α g Φg = fun z θ =>
      2 * (Work.Construction.Fstar α z θ
        * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N1gs]
    ring
  constructor
  · rw [heq]
    exact Work.FTS.LocData.HkMem_const_mul α 4 2 hprod.1
  · rw [heq, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    -- the chain of bounds
    have hstep1 : Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Construction.Fstar α z θ
            * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * ((CF + 1) * α)
          * (max Ce 1 * Work.FTS.Nonlin.Xn α g) := by
      refine le_trans hprod.2 ?_
      refine mul_le_mul ?_ hRB' hRnn ?_
      · exact mul_le_mul_of_nonneg_left hFle' (mul_nonneg hCi.le hA)
      · exact mul_nonneg (mul_nonneg hCi.le hA) (mul_nonneg (by linarith) hα.le)
    have hsqrt : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
      rw [Real.sqrt_eq_rpow]
      have h := Real.rpow_add hα (-(1 / 2 : ℝ)) (1 : ℝ)
      rw [Real.rpow_one, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
      exact h.symm
    have hkey : Ci * α ^ (-(1 / 2 : ℝ)) * ((CF + 1) * α)
          * (max Ce 1 * Work.FTS.Nonlin.Xn α g)
        = (Ci * (CF + 1)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) * max Ce 1 := by
      rw [show Ci * α ^ (-(1 / 2 : ℝ)) * ((CF + 1) * α)
            * (max Ce 1 * Work.FTS.Nonlin.Xn α g)
          = (Ci * (CF + 1)) * (α ^ (-(1 / 2 : ℝ)) * α)
            * Work.FTS.Nonlin.Xn α g * max Ce 1 from by ring, hsqrt]
      ring
    have hS : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
      mul_nonneg (Real.sqrt_nonneg α) hXg
    have hfin : 2 * ((Ci * (CF + 1)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) * max Ce 1)
        ≤ (2 * (Ci * (CF + 1)) * max Ce 1 + 1)
            * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
      have hle : 2 * ((Ci * (CF + 1)) * max Ce 1)
          ≤ 2 * (Ci * (CF + 1)) * max Ce 1 + 1 := by linarith
      calc 2 * ((Ci * (CF + 1)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) * max Ce 1)
          = (2 * ((Ci * (CF + 1)) * max Ce 1))
              * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by ring
        _ ≤ (2 * (Ci * (CF + 1)) * max Ce 1 + 1)
              * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) :=
            mul_le_mul_of_nonneg_right hle hS
    calc 2 * Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Construction.Fstar α z θ
            * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ)
        ≤ 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * ((CF + 1) * α)
            * (max Ce 1 * Work.FTS.Nonlin.Xn α g)) :=
          mul_le_mul_of_nonneg_left hstep1 (by norm_num)
      _ = 2 * ((Ci * (CF + 1)) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) * max Ce 1) := by
          rw [hkey]
      _ ≤ (2 * (Ci * (CF + 1)) * max Ce 1 + 1)
            * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := hfin

end Work.FTS.NonlinRows
