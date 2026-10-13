import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.GalFields.RHS.sharpN0_defs
import Submission.Work.FTS.GalFields.RHS.sharpN0_sums
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0Aux
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0Rows
import Submission.Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.OpenPkg.wprod_field_winf
import Submission.Work.FTS.OpenPkg.angmul_field
import Submission.Work.FTS.OpenPkg.l12H_field
import Submission.Work.FTS.StrongEps.EpsRLX.ClassCDiffDefs
import Submission.Work.FTS.StrongEps.EpsRLX.ClassCDiffData
import Submission.Work.FTS.StrongEps.EpsRLX.PiecesAClassC
import Submission.Work.FTS.StrongEps.EpsRLX.PiecesBClassCRow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

/-- **The `ℋ⁴`-honesty and the sharp (linear-in-the-difference) `ℋ⁴`-bound for the nine
telescoped pieces of the `N₀`-difference, on the class `ClassC`.**

With `h := fun z θ => W₁ z θ - W₂ z θ`, `HkMem α 4 (Rsum α W₁ W₂ h)` holds and
`Xn α (Rsum α W₁ W₂ h) ≤ K·(1 + Xn5 α W₁ + Xn5 α W₂)·Xn5 α h` with a constant `K` that may
depend on `α` (it does: the pieces carry `α^{-1}`, `α^{-1/2}` and `α^{+1}` factors) but not on
`W₁, W₂`.

Route. `Rsum α W₁ W₂ h = P1 + (P2 + (P3 + (P4 + (P5 + (P6 + (P7 + (P8 + P9)))))))`
(`Work.FTS.GalFields.RHS`, `sharpN0_defs.lean`), with, writing `𝓛X := fun z _ => L₁₂ X z`,
`Dth := Work.Spaces.Dth`, `Dz := Work.Spaces.Dz`, `c2m := Work.Construction.c2m`:
`P1 = (1/α)·(𝓛W₁·h)`, `P2 = (1/α)·(𝓛h·W₂)`, `P3 = (3/2α)·(Dth F_* · 𝓛h)`,
`P4 = (3/2α)·(𝓛W₁·Dth h)`, `P5 = (3/2α)·(𝓛h·Dth W₂)`, `P6 = -c2m·(Dz F_* · 𝓛h)`,
`P7 = -c2m·(𝓛W₁·Dz h)`, `P8 = -c2m·(𝓛h·Dz W₂)`, `P9 = -(c2m·𝓛F_*)·Dz h`.

Available universal (package-free) tools:
* `Work.FTS.OpenPkg.prod_field`: for `HQo α 4 f`, `HQo α 4 g` (i.e. `SmoothOpen` + `HkMem α 4`),
  `HkMem α 4 (f·g)` and `Xn α (f·g) ≤ C·α^(-1/2)·Xn α f · Xn α g`;
* `Work.FTS.OpenPkg.wprod_field_winf`: for `SmoothOpen f` with `WlInfMem α 4 f` and `HQo α 4 g`,
  `HkMem α 4 (f·g)` and `Xn α (f·g) ≤ C·α^(-1/2)·WlInf α 4 f·Xn α g`;
* `Work.FTS.OpenPkg.angmul_field`: for an angular factor `a` with `|a θ| ≤ Ca` and the `DthIter`
  bounds `≤ Ca·sin 2θ` on `Iθ` (both hold for `a = c2m` with `Ca = 1000`, see
  `abs_c2m_le_thousand`, `DthIter_c2m_le_sin`), `HkMem α 4 (a·f)` and `Xn α (a·f) ≤ C·Ca·Xn α f`;
* `Work.FTS.OpenPkg.l12H_field`: `HQo α 4 g` and `L₁₂ g 0 = 0` give `HkMem α 4 𝓛g` and
  `Xn α 𝓛g ≤ C·Xn α g`;
* `Work.FTS.GalFields.RHS.c2m_mul_HkSq_le` (with `HkSq α 4` monotonicity) for multiplying by
  `c2m` inside a product;
* the fixed-profile atoms: `Work.FTS.GalFields.RHS.CFdef_spec` (`Dth F_*`: `WlInfMem α 4`,
  `WlInf ≤ CF·α²`), `Cdzdef_spec` (`Dz F_*`: `WlInf ≤ Cdz·α`), `Cwdef_spec`
  (`c2m·𝓛F_*`: `WlInf ≤ Cw·α`), plus `smoothOpen_c2m_ang`, `Work.FTS.StrongPersist.H6Pair6Aux`
  for the smoothness of the `F_*`-atoms.

Derived facts to obtain from `ClassC α W` (`hW : ClassC α W`):
`hW.reg : SmoothOpen W`, `hW.mem` (`HkMem α 7`, hence `HkMem α k` for `k ≤ 7` via
`HkMem_mono_open hW.reg`), `hW.l12 : L₁₂ W 0 = 0`,
`Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_aux hα hW : SmoothOpen 𝓛W`, and the
monotonicity `Xn α W ≤ Xn5 α W` (`Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4)`,
needs `HkMem α 5 W`), `Xn α (Dth W) ≤ Xn5 α W` (`Work.FTS.GalFields.Xn_Dth_le_Xn5`),
`Xn α (Dz W) ≤ Xn5 α W` (`Work.FTS.GalFields.Xn_Dz_le_Xn5`, needs `SmoothOpen`).

For the difference `h` itself: `SmoothOpen h` is `Work.FTS.EllipticEst.smoothOpen_sub`;
`HkMem α k h` comes from `HkMem_add_open` + `Work.FTS.StrongEps.ClassCRHS.mem_neg` +
`Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0` (pointwise `W₁ - W₂ = W₁ + (-W₂)` on `Qd`);
`L₁₂ h 0 = 0` and the *identities* `𝓛h = 𝓛W₁ - 𝓛W₂` (for `z ≥ 0`) come from
`Work.FTS.GalFields.RHS.L12_sub_eq_of_smoothOpen`, from which `SmoothOpen 𝓛h`, `HkMem α 4 𝓛h`
and `Xn α 𝓛h ≤ C·Xn α h ≤ C·Xn5 α h` follow (the last by `l12H_field` applied to `h`).

Every piece bound must end in a factor `Xn5 α h`, and the remaining factors are
`1`, `Xn5 α W₁`, `Xn5 α W₂`; assemble the nine bounds with
`Work.FTS.GalFields.RHS.HkNorm_finset_sum_le` (or `HkNorm_add_le_open`). -/
theorem RsumClassC {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Rsum α W₁ W₂
        (fun z θ => W₁ z θ - W₂ z θ)) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Rsum α W₁ W₂
        (fun z θ => W₁ z θ - W₂ z θ))
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
  -- ## the universal constants of the three product rules
  obtain ⟨Cp, hCp, hprod0⟩ := Work.FTS.OpenPkg.prod_field
  obtain ⟨Cw, hCw, hwprod0⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨C1, hC1, hl120⟩ := Work.FTS.OpenPkg.l12H_field
  -- the single constant dominating all three
  set Ci : ℝ := max Cp (max Cw (max C1 1)) with hCidef
  have hCp_le : Cp ≤ Ci := by rw [hCidef]; exact le_max_left _ _
  have hCw_le : Cw ≤ Ci := by
    rw [hCidef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hC1_le : C1 ≤ Ci := by
    rw [hCidef]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have h1_le : (1 : ℝ) ≤ Ci := by
    rw [hCidef]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCi : 0 < Ci := lt_of_lt_of_le one_pos h1_le
  -- ## the two product rules, weakened to the single constant `Ci`
  have hprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g := by
    intro f g hf hg
    obtain ⟨hm, hb⟩ := hprod0 α hα hα1 f g hf hg
    refine ⟨hm, le_trans hb ?_⟩
    have hA : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    have h0f : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
    have h0g : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCp_le hA) h0f) h0g
  have hwprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g := by
    intro f g hf hfm hg
    obtain ⟨hm, hb⟩ := hwprod0 α hα hα1 f g hf hfm hg
    refine ⟨hm, le_trans hb ?_⟩
    have hA : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    have h0g : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCw_le hA)
        (Work.FTS.H2.WPQ.WlInf_nonneg' hfm)) h0g
  have hl12 : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 4 g →
      Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
        ≤ Ci * Work.FTS.Nonlin.Xn α g := by
    intro g hg h0
    obtain ⟨hm, hb⟩ := hl120 α hα hα1 g hg h0
    refine ⟨hm, le_trans hb ?_⟩
    exact mul_le_mul_of_nonneg_right hC1_le (Work.Spaces.HkNorm_nonneg α 4 g)
  refine ⟨1024 * Work.FTS.GalFields.RHS.ksum α Ci Work.FTS.GalFields.RHS.CFdef
      Work.FTS.GalFields.RHS.Cdzdef Work.FTS.GalFields.RHS.Cwdef, ?_, ?_⟩
  · -- ## positivity of the constant
    have hksum : 0 < Work.FTS.GalFields.RHS.ksum α Ci Work.FTS.GalFields.RHS.CFdef
        Work.FTS.GalFields.RHS.Cdzdef Work.FTS.GalFields.RHS.Cwdef := by
      refine lt_of_lt_of_le ?_ (Work.FTS.GalFields.RHS.kA1_le_ksum hα hCi
        Work.FTS.GalFields.RHS.CFdef_pos Work.FTS.GalFields.RHS.Cdzdef_pos
        Work.FTS.GalFields.RHS.Cwdef_pos)
      rw [Work.FTS.GalFields.RHS.kA1]
      exact mul_pos (mul_pos (mul_pos (by positivity) hCi)
        (Real.rpow_pos_of_pos hα (-(1 / 2 : ℝ)))) hCi
    positivity
  · -- ## the estimate
    intro W₁ W₂ hW₁ hW₂
    let h : ℝ → ℝ → ℝ := fun z θ => W₁ z θ - W₂ z θ
    have hD := ClassCDiffData (α := α) hα hα1 hW₁ hW₂
    have hm4₁ : Work.Spaces.HkMem α 4 W₁ :=
      Work.FTS.OpenPkg.HkMem_mono_open hW₁.reg 4 (by norm_num) hW₁.mem
    have hm4₂ : Work.Spaces.HkMem α 4 W₂ :=
      Work.FTS.OpenPkg.HkMem_mono_open hW₂.reg 4 (by norm_num) hW₂.mem
    have hm4h : Work.Spaces.HkMem α 4 h :=
      Work.FTS.OpenPkg.HkMem_mono_open hD.hsm 4 (by norm_num) hD.hmem
    have hL1 := hl12 W₁ ⟨hW₁.reg, hm4₁⟩ hW₁.l12
    have hLh := hl12 h ⟨hD.hsm, hm4h⟩ hD.hLh0
    have hLhXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
        ≤ Ci * Work.FTS.GalFields.Xn5 α h :=
      le_trans hLh.2 (mul_le_mul_of_nonneg_left hD.hXh hCi.le)
    have hA := PiecesAClassC (α := α) (Ci := Ci) (g := W₁) (g' := W₂) (h := h)
      hα hα1 hCi hprod hwprod
      hW₁.reg hW₂.reg hD.hsm hm4₂ hm4h
      hD.hLW₁Sm hD.hLhSm hL1.1 hLh.1 hL1.2 hLhXn
      hD.hXW₁ hD.hXh hD.hXW₂
      hD.hDthSm hD.hDthMem hD.hDthXn
      hD.hDthW₂Sm hD.hDthW₂Mem hD.hDthW₂Xn
      Work.FTS.GalFields.RHS.CFdef Work.FTS.GalFields.RHS.CFdef_pos
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dth
      (Work.FTS.GalFields.RHS.CFdef_spec.2 α hα hα1)
      (Work.Spaces.HkNorm_nonneg α 5 h)
    have hB := PiecesBClassCRow (α := α) (Ci := Ci) (g := W₁) (g' := W₂) (h := h)
      hα hα1 hCi hprod hwprod
      hD.hLW₁Sm hD.hLhSm hL1.1 hLh.1 hL1.2 hLhXn
      hD.hXW₁ hD.hXW₂
      hD.hDzSm hD.hDzMem hD.hDzXn
      hD.hDzW₂Sm hD.hDzW₂Mem hD.hDzW₂Xn
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_L12_Fstar α)
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dz
      Work.FTS.GalFields.RHS.smoothOpen_c2m_ang
      Work.FTS.GalFields.RHS.Cdzdef Work.FTS.GalFields.RHS.Cwdef
      Work.FTS.GalFields.RHS.Cdzdef_pos Work.FTS.GalFields.RHS.Cwdef_pos
      (Work.FTS.GalFields.RHS.Cdzdef_spec.2 α hα hα1)
      (Work.FTS.GalFields.RHS.Cwdef_spec.2 α hα hα1)
      (Work.Spaces.HkNorm_nonneg α 5 h)
    obtain ⟨A1, A2, A3, A4, A5, sA1, sA2, sA3, sA4, sA5⟩ := hA
    obtain ⟨B6, B7, B8, B9, sB6, sB7, sB8, sB9⟩ := hB
    have hsum := Work.FTS.GalFields.RHS.sharpN0_sums (α := α) (Ci := Ci)
      (g := W₁) (g' := W₂) (h := h) hα hCi
      Work.FTS.GalFields.RHS.CFdef Work.FTS.GalFields.RHS.Cdzdef Work.FTS.GalFields.RHS.Cwdef
      Work.FTS.GalFields.RHS.CFdef_pos Work.FTS.GalFields.RHS.Cdzdef_pos
      Work.FTS.GalFields.RHS.Cwdef_pos
      A1 A2 A3 A4 A5 B6 B7 B8 B9 sA1 sA2 sA3 sA4 sA5 sB6 sB7 sB8 sB9
    refine ⟨hsum.1, ?_⟩
    have hTOF : Work.FTS.GalFields.RHS.TOf α W₁ W₂ h
        = (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
          * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := rfl
    have heq : 1024 * Work.FTS.GalFields.RHS.ksum α Ci Work.FTS.GalFields.RHS.CFdef
          Work.FTS.GalFields.RHS.Cdzdef Work.FTS.GalFields.RHS.Cwdef
          * Work.FTS.GalFields.RHS.TOf α W₁ W₂ h
        = 1024 * Work.FTS.GalFields.RHS.ksum α Ci Work.FTS.GalFields.RHS.CFdef
          Work.FTS.GalFields.RHS.Cdzdef Work.FTS.GalFields.RHS.Cwdef
          * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
          * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
      rw [hTOF]; ring
    exact le_trans hsum.2.2 (le_of_eq heq)

end Work.FTS.StrongEps.EpsRLX
