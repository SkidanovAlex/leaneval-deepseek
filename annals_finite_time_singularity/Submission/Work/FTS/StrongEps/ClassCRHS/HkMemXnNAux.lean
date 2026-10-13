/-
# `HkMemXnNAux` — the product-rule wrappers and the generic regularity/bound atoms of `HkMemXnN`

Contents:

* `mulHQo`, `mulW`: the two product rules (`ℋ⁴ × ℋ⁴` and `𝒲^{4,∞} × ℋ⁴`) with an explicit
  scalar and explicit constants, so that the universal constants are obtained once;
* the generic smoothness facts (`z/(1+z)`, `φ·f`, `FK w`, `(-2α)hKer`, and the three
  `(z+1)/z`-weighted star coefficients);
* the generic bound atoms (the three coefficient bounds of `EllPkgGo`, the three `𝒲^{4,∞}`-bounds
  of `StarPkgo2`, the `FK`-bound, the `hKer`-bound, and the `φ`-multiplication facts).
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.OpenPkg.wprod_field_winf
import Submission.Work.FTS.OpenPkg.fkH_field
import Submission.Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row22
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.StrongEps.EComparison.EllPkgClsVop
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.EllipticEst.RPFresh.DivSinOpen.Defs
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS_RegExport.RXT.velPert
import Submission.Work.FTS.Nonlinear.Open.Row25Aux
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.ClassCRHS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## The two product-rule wrappers -/

/-- **Product of two `ℋ⁴`-honest factors with a scalar.** -/
theorem mulHQo {α Cprod : ℝ} (hα : 0 < α) (hCprod : 0 < Cprod)
    (hfield : ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)
    {C G : Fn} {c a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC : Work.FTS.VocabO.HQo α 4 C) (hG : Work.FTS.VocabO.HQo α 4 G)
    (hCa : Work.FTS.Nonlin.Xn α C ≤ a) (hGb : Work.FTS.Nonlin.Xn α G ≤ b) :
    Work.Spaces.HkMem α 4 (fun z θ => c * (C z θ * G z θ)) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => c * (C z θ * G z θ))
        ≤ |c| * Cprod * α ^ (-(1 / 2 : ℝ)) * a * b := by
  obtain ⟨hm, hbnd⟩ := hfield C G hC hG
  have hAr : 0 ≤ Cprod * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCprod.le (Real.rpow_nonneg hα.le _)
  have hXnC : 0 ≤ Work.FTS.Nonlin.Xn α C := Real.sqrt_nonneg _
  have hXnG : 0 ≤ Work.FTS.Nonlin.Xn α G := Real.sqrt_nonneg _
  refine ⟨Work.FTS.LocData.HkMem_const_mul α 4 c hm, ?_⟩
  rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α c (fun z θ => C z θ * G z θ)]
  calc |c| * Work.FTS.Nonlin.Xn α (fun z θ => C z θ * G z θ)
      ≤ |c| * (Cprod * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α C * Work.FTS.Nonlin.Xn α G) :=
        mul_le_mul_of_nonneg_left hbnd (abs_nonneg c)
    _ ≤ |c| * (Cprod * α ^ (-(1 / 2 : ℝ)) * a * b) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
        calc Cprod * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α C * Work.FTS.Nonlin.Xn α G
            ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * a * Work.FTS.Nonlin.Xn α G :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCa hAr) hXnG
          _ ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * a * b :=
              mul_le_mul_of_nonneg_left hGb (mul_nonneg hAr ha)
    _ = |c| * Cprod * α ^ (-(1 / 2 : ℝ)) * a * b := by ring

/-- **Product of a `𝒲^{4,∞}`-factor with an `ℋ⁴`-honest factor, with a scalar.** -/
theorem mulW {α Cw : ℝ} (hα : 0 < α) (hCw : 0 < Cw)
    (hfield : ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g)
    {F G : Fn} {c a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hFs : Work.FTS.EllipticEst.SmoothOpen F) (hFm : Work.Spaces.WlInfMem α 4 F)
    (hFa : Work.Spaces.WlInf α 4 F ≤ a)
    (hG : Work.FTS.VocabO.HQo α 4 G) (hGb : Work.FTS.Nonlin.Xn α G ≤ b) :
    Work.Spaces.HkMem α 4 (fun z θ => c * (F z θ * G z θ)) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => c * (F z θ * G z θ))
        ≤ |c| * Cw * α ^ (-(1 / 2 : ℝ)) * a * b := by
  obtain ⟨hm, hbnd⟩ := hfield F G hFs hFm hG
  have hAr : 0 ≤ Cw * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCw.le (Real.rpow_nonneg hα.le _)
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 F := Work.Spaces.WlInf_nonneg α 4 F hFm
  have hXnG : 0 ≤ Work.FTS.Nonlin.Xn α G := Real.sqrt_nonneg _
  refine ⟨Work.FTS.LocData.HkMem_const_mul α 4 c hm, ?_⟩
  rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α c (fun z θ => F z θ * G z θ)]
  calc |c| * Work.FTS.Nonlin.Xn α (fun z θ => F z θ * G z θ)
      ≤ |c| * (Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 F * Work.FTS.Nonlin.Xn α G) :=
        mul_le_mul_of_nonneg_left hbnd (abs_nonneg c)
    _ ≤ |c| * (Cw * α ^ (-(1 / 2 : ℝ)) * a * b) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
        calc Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 F * Work.FTS.Nonlin.Xn α G
            ≤ Cw * α ^ (-(1 / 2 : ℝ)) * a * Work.FTS.Nonlin.Xn α G :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFa hAr) hXnG
          _ ≤ Cw * α ^ (-(1 / 2 : ℝ)) * a * b :=
              mul_le_mul_of_nonneg_left hGb (mul_nonneg hAr ha)
    _ = |c| * Cw * α ^ (-(1 / 2 : ℝ)) * a * b := by ring

/-! ## Generic smoothness atoms -/

theorem smoothOpen_zdiv : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)) := by
  refine Work.FTS.NonlinRows.smoothOpen_radial (r := fun z : ℝ => z / (1 + z)) ?_
  intro n
  refine ContDiffOn.div contDiffOn_id (contDiffOn_const.add contDiffOn_id) ?_
  intro z hz
  have hz' : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
  positivity

theorem smoothOpen_phi_mul {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * f z θ) :=
  Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl smoothOpen_zdiv hf

theorem smoothOpen_FKw_of_classC {α : ℝ} {w : Fn} (hw : Work.FTS.ClassC.ClassC α w) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK w z) := by
  have hr : ∀ n : ℕ, ContDiffOn ℝ n (fun z : ℝ => 3 * Work.Elliptic.Fstar w z)
      (Set.Ioi 0) := fun n => contDiffOn_const.mul (hw.fsm n)
  have hmain := Work.FTS.NonlinRows.smoothOpen_radial
    (r := fun z : ℝ => 3 * Work.Elliptic.Fstar w z) hr
  refine hmain.congr ?_
  rintro z θ _ _ _
  exact (Work.FTS_RegExport.RXT.velPert_FK_eq w z).symm

theorem smoothOpen_FKneg (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (-(2 * α)) * Work.Spaces.hKer z) := by
  refine Work.FTS.NonlinRows.smoothOpen_radial
    (r := fun z : ℝ => (-(2 * α)) * Work.Spaces.hKer z) ?_
  intro n
  have hker : ContDiffOn ℝ n (fun z : ℝ => Work.Spaces.hKer z) (Set.Ioi 0) := by
    simp only [Work.Spaces.hKer_apply]
    refine ContDiffOn.div contDiffOn_id ((contDiffOn_const.add contDiffOn_id).pow 2) ?_
    intro z hz
    have hz' : (0 : ℝ) < z := hz
    positivity
  exact contDiffOn_const.mul hker

theorem smoothOpen_Rs_of_star {α Cs : ℝ} {Φs : Fn} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hsw : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
  Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen hα0 hα1 hsw

theorem smoothOpen_Us_of_star {α Cs : ℝ} {Φs : Fn} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hsw : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)) :=
  Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_zPlusOne_div_z
    (Work.FTS.EllipticEst.RPFresh.smoothOpen_div_sin
      (Work.FTS.EllipticEst.smoothOpen_Uop
        (Work.FTS.NonlinRows.NRow10aux.smoothOpen_PhiTs hα0 hα1 hsw)))

theorem smoothOpen_Vs_of_star {α Cs : ℝ} {Φs : Fn} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hsw : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
  Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul
    Work.FTS.NonlinRows.NRow10aux.smoothOpen_zPlusOne_div_z
    (Work.FTS.StrongEps.EComparison.smoothOpen_Vop
      (Work.FTS.NonlinRows.NRow10aux.smoothOpen_PhiTs hα0 hα1 hsw))

/-! ## Generic bound atoms

The three coefficients of `EllPkgGo` (paired with `F_*` or with `w`) are bounded by
`max Ce 0 · max C₀ 0 · α²` on the smallness ball. -/

theorem Xn_Rop_le {α C₀ Ce : ℝ} {w Φg : Fn} (hw : Work.FTS.ClassC.ClassC α w)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg) (hXw : Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2) :
    Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg))
      ≤ max Ce 0 * max C₀ 0 * α ^ 2 := by
  have h1 : Work.FTS.Nonlin.Xn α w ≤ max C₀ 0 * α ^ 2 :=
    le_trans hXw (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (by positivity))
  refine le_trans hell.R.2 ?_
  calc Ce * Work.FTS.Nonlin.Xn α w ≤ max Ce 0 * (max C₀ 0 * α ^ 2) :=
        mul_le_mul (le_max_left Ce 0) h1 (Real.sqrt_nonneg _) (by positivity)
    _ = max Ce 0 * max C₀ 0 * α ^ 2 := by ring

theorem Xn_UopDiv_le {α C₀ Ce : ℝ} {w Φg : Fn} (hw : Work.FTS.ClassC.ClassC α w)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg) (hXw : Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2) :
    Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ
        / Work.Construction.s2 θ) ≤ max Ce 0 * max C₀ 0 * α ^ 2 := by
  have h1 : Work.FTS.Nonlin.Xn α w ≤ max C₀ 0 * α ^ 2 :=
    le_trans hXw (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (by positivity))
  refine le_trans hell.U.2 ?_
  calc Ce * Work.FTS.Nonlin.Xn α w ≤ max Ce 0 * (max C₀ 0 * α ^ 2) :=
        mul_le_mul (le_max_left Ce 0) h1 (Real.sqrt_nonneg _) (by positivity)
    _ = max Ce 0 * max C₀ 0 * α ^ 2 := by ring

theorem Xn_Vop_le {α C₀ Ce : ℝ} {w Φg : Fn} (hw : Work.FTS.ClassC.ClassC α w)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg) (hXw : Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2) :
    Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg))
      ≤ max Ce 0 * max C₀ 0 * α ^ 2 := by
  have h1 : Work.FTS.Nonlin.Xn α w ≤ max C₀ 0 * α ^ 2 :=
    le_trans hXw (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (by positivity))
  refine le_trans hell.V.2 ?_
  calc Ce * Work.FTS.Nonlin.Xn α w ≤ max Ce 0 * (max C₀ 0 * α ^ 2) :=
        mul_le_mul (le_max_left Ce 0) h1 (Real.sqrt_nonneg _) (by positivity)
    _ = max Ce 0 * max C₀ 0 * α ^ 2 := by ring

/-- The `𝒲^{4,∞}`-bounds of the three `(z+1)/z`-weighted star coefficients. -/
theorem WlInf_Rs_le {α Cs : ℝ} {Φs : Fn} (hα0 : 0 < α) (hs : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.Spaces.WlInf α 4
      (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
      ≤ max Cs 0 * α :=
  le_trans hs.RW.2 (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα0.le)

theorem WlInf_Us_le {α Cs : ℝ} {Φs : Fn} (hα0 : 0 < α) (hs : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ))
      ≤ max Cs 0 * α :=
  le_trans hs.UszW.2 (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα0.le)

theorem WlInf_Vs_le {α Cs : ℝ} {Φs : Fn} (hα0 : 0 < α) (hs : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.Spaces.WlInf α 4
      (fun z θ => (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
      ≤ max Cs 0 * α :=
  le_trans hs.VzW.2 (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα0.le)

/-- The `FK`-atom of the perturbation: honest in `ℋ⁴`, bounded by `Cfk · max C₀ 0 · α²`. -/
theorem FKw_data {α C₀ Cfk : ℝ} {w : Fn} (hXw : Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2)
    (hfk : ∀ g : Fn, Work.FTS.VocabO.HQo α 4 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK g z) ∧
      Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z) ≤ Cfk * Work.FTS.Nonlin.Xn α g)
    (hqow : Work.FTS.VocabO.HQo α 4 w) (hl12 : Work.Construction.L12 w 0 = 0)
    (hCfk : 0 < Cfk) :
    Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK w z) ∧
      Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK w z) ≤ Cfk * max C₀ 0 * α ^ 2 := by
  have h1 : Work.FTS.Nonlin.Xn α w ≤ max C₀ 0 * α ^ 2 :=
    le_trans hXw (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (by positivity))
  obtain ⟨hm, hb⟩ := hfk w hqow hl12
  refine ⟨hm, ?_⟩
  calc Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK w z)
      ≤ Cfk * Work.FTS.Nonlin.Xn α w := hb
    _ ≤ Cfk * (max C₀ 0 * α ^ 2) := mul_le_mul_of_nonneg_left h1 hCfk.le
    _ = Cfk * max C₀ 0 * α ^ 2 := by ring

/-- The `hKer`-atom: `𝒲^{4,∞}` with the explicit bound `200·(2α)`. -/
theorem hKerNeg_data (α : ℝ) (hα0 : 0 < α) :
    Work.Spaces.WlInfMem α 4 (fun z _ : ℝ => (-(2 * α)) * Work.Spaces.hKer z) ∧
      Work.Spaces.WlInf α 4 (fun z _ : ℝ => (-(2 * α)) * Work.Spaces.hKer z) ≤ 200 * (2 * α) := by
  obtain ⟨hm, hb⟩ := Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α (-(2 * α))
  refine ⟨hm, le_trans hb ?_⟩
  rw [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * α)]

/-- Multiplication by `z/(1+z)` in `ℋ⁴`, with an explicit constant. -/
theorem phi_mul_data {α Cphi : ℝ} (hCphi : 0 < Cphi)
    (hphi : ∀ g : Fn, Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => z / (1 + z) * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * g z θ) ≤ Cphi * Work.FTS.Nonlin.Xn α g)
    {X : Fn} {b : ℝ} (hX : Work.FTS.VocabO.HQo α 4 X) (hXb : Work.FTS.Nonlin.Xn α X ≤ b) :
    Work.Spaces.HkMem α 4 (fun z θ => z / (1 + z) * X z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * X z θ) ≤ Cphi * b := by
  obtain ⟨hm, hb⟩ := hphi X hX
  exact ⟨hm, le_trans hb (mul_le_mul_of_nonneg_left hXb hCphi.le)⟩


/-! ## Smoothness of the twenty product forms -/

theorem NBlk_smooth {α Cs Ce : ℝ} {w Φs Φg : Fn} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w) (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∀ k ∈ Finset.range 20, Work.FTS.EllipticEst.SmoothOpen (NBlk α w Φs Φg k) := by
  have hsw : Work.FTS.VocabO.StarPkgo α Cs Φs := hstar.toStarPkgo
  have hRsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) := hell.R.1.1
  have hUcsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) :=
    hell.U.1.1
  have hVcsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) := hell.V.1.1
  have hRssm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    smoothOpen_Rs_of_star hα0 hα1 hsw
  have hUssm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z *
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ / Work.Construction.s2 θ)) :=
    smoothOpen_Us_of_star hα0 hα1 hsw
  have hVssm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (z + 1) / z * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) :=
    smoothOpen_Vs_of_star hα0 hα1 hsw
  have hFWsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.Fstar α z θ) :=
    Work.FTS.EllipticEst.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hDthFssm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Construction.Fstar α)) := hFWsm.Dth
  have hDzFssm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (Work.Construction.Fstar α)) := hFWsm.Dz
  have hDthwsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth w) := hw.reg.Dth
  have hDzwsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz w) := hw.reg.Dz
  have hFKesm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα0 hα1
  have hFKws : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK w z) :=
    smoothOpen_FKw_of_classC hw
  have hFKnegsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ : ℝ => (-(2 * α)) * Work.Spaces.hKer z) := smoothOpen_FKneg α
  have hSinSq : Work.FTS.EllipticEst.SmoothOpen (fun x θ : ℝ => -Real.sin θ ^ 2) :=
    Work.FTS.Nonlinear.Open.row25_smoothOpen_neg_sinSq
  have hG : ∀ (A B : Fn), Work.FTS.EllipticEst.SmoothOpen A →
      Work.FTS.EllipticEst.SmoothOpen B →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => A z θ * B z θ) :=
    fun A B hA hB => Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hA hB
  have hC : ∀ (c : ℝ) (A : Fn), Work.FTS.EllipticEst.SmoothOpen A →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * A z θ) :=
    fun c A hA => Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl c hA
  have hpw := hG (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) w hRsm hw.reg
  have hps := hG (fun z θ => Work.Construction.Fstar α z θ)
    (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) hFWsm hRsm
  have hphiw : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * w z θ) :=
    smoothOpen_phi_mul hw.reg
  have hphiFs : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) :=
    smoothOpen_phi_mul hFWsm
  have hphiDthw : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) :=
    smoothOpen_phi_mul (hw.reg.Dth)
  have hphiDzw : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) :=
    smoothOpen_phi_mul (hw.reg.Dz)
  have hphiDthFs : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) :=
    smoothOpen_phi_mul hFWsm.Dth
  have hphiDzFs : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) :=
    smoothOpen_phi_mul hFWsm.Dz
  intro k hk
  have hk20 : k < 20 := Finset.mem_range.mp hk
  interval_cases k
  · simp only [NBlk]; exact hC 2 _ hpw
  · simp only [NBlk]; exact hC 2 _ hps
  · simp only [NBlk]; exact hC 2 _ (hG _ _ hRssm hphiw)
  · simp only [NBlk]; exact hC 2 _ (hG _ _ hRssm hphiFs)
  · simp only [NBlk]; exact hC (-2) _ (hG _ _ hUcsm hDthwsm)
  · simp only [NBlk]; exact hC (-2) _ (hG _ _ hDthFssm hUcsm)
  · simp only [NBlk]; exact hC (-2) _ (hG _ _ hUssm hphiDthw)
  · simp only [NBlk]; exact hC (-2) _ (hG _ _ hUssm hphiDthFs)
  · simp only [NBlk]; exact hC (-(2 * α)) _ (hG _ _ hVcsm hDzwsm)
  · simp only [NBlk]; exact hC (-(2 * α)) _ (hG _ _ hDzFssm hVcsm)
  · simp only [NBlk]; exact hC (-(2 * α)) _ (hG _ _ hVssm hphiDzw)
  · simp only [NBlk]; exact hC (-(2 * α)) _ (hG _ _ hVssm hphiDzFs)
  · simp only [NBlk]; exact hC (-(1 / 2)) _ (hG _ _ hFKws hDthwsm)
  · simp only [NBlk]; exact hC (-(1 / 2)) _ (hG _ _ hDthFssm hFKws)
  · simp only [NBlk]; exact hC (1 / 2) _ (hG _ _ hFKnegsm hDthwsm)
  · simp only [NBlk]; exact hC (-(1 / 2)) _ (hG _ _ hFKesm hDthFssm)
  · simp only [NBlk]; exact hG _ _ hSinSq (hG _ _ hFKws hw.reg)
  · simp only [NBlk]; exact hG _ _ hSinSq (hG _ _ hFWsm hFKws)
  · simp only [NBlk]; exact hG _ _ hSinSq (hG _ _ hFKesm hw.reg)
  · simp only [NBlk]; exact hG _ _ hSinSq (hG _ _ hFKesm hFWsm)

end Work.FTS.StrongEps.ClassCRHS
