import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen
import Submission.Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
import Submission.Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# Row 10 of the §8 table, in the `StarPkgo2` vocabulary (open quadrant)

`N1sg α Φs g = 2·ℛ(Φ̃_*)·g`, with `ℛ := Rop`, `Φ̃_* := PhiTs α Φs`.  Writing
`H := ((z+1)/z)·ℛ(Φ̃_*)` for the weighted star coefficient, the row is the product rule for
`H · ((z/(1+z))·g)`:

* `RW` of `VocabO2.StarPkgo2` prices `H` by the `𝒲^{4,∞}`-norm, `WlInf α 4 H ≤ Cs·α`
  (the paper's `PhiStarRegularity2`);
* `N4Norm'.wprod` is exactly the multiplication rule for a `𝒲^{4,∞}`-coefficient, with the
  loss `Ci·α^{-1/2}`, and `NRow10aux.mul_phi_Hk` disposes of the bounded radial factor
  `z/(1+z)`;
* `α^{-1/2}·α = √α` gives the rate.

The `StarH` here is the coefficient of `NRow10.StarH`; it is redeclared locally only so that
this file does not depend on the unfinished module `NonlinRows.NRow10`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The weighted star coefficient `H = ((z+1)/z)·ℛ(Φ̃_*)` of the `Φ_*` node. -/
def Row10StarH (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ

theorem Row10 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N1sg α Φs g) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1sg α Φs g) ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hCi, _⟩ := hN.pos
  obtain ⟨Cφ, hCφ, hφb⟩ := Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
  refine ⟨2 * Ci * (Cφ * Cφ + 1) * max Cs 0 + 1, by positivity, ?_⟩
  intro α g Φs Φg hα hα1 hαα₂ hgal hs2 hell
  -- the frozen star package underlying `StarPkgo2`, and the `𝒲`-pricing of `H`
  have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hs2.toStarPkgo
  obtain ⟨hHmem, hHle⟩ := hs2.RW
  have hHle' : Work.Spaces.WlInf α 4 (Row10StarH α Φs) ≤ max Cs 0 * α :=
    le_trans hHle (mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le)
  have hHsm : Work.FTS.EllipticEst.SmoothOpen (Row10StarH α Φs) :=
    Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen hα hα1 hs
  -- the two factors of the product rule
  have hg4 : Work.FTS.VocabO.HQo α 4 g := Work.FTS.OpenPkg.galClass_HQo4 hgal
  obtain ⟨hφmem, hφbnd⟩ := hφb hα hα1 hg4
  have hφsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * g z θ) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => p.1 / (1 + p.1)) Work.FTS.EllipticEst.Q0 := by
      refine ContDiffOn.div ?_ ?_ ?_
      · exact contDiffOn_fst
      · exact contDiffOn_const.add contDiffOn_fst
      · intro p hp
        have hp1 : (0 : ℝ) < 1 + p.1 := by
          have := Set.mem_Ioi.mp hp.1
          linarith
        positivity
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => g p.1 p.2) Work.FTS.EllipticEst.Q0 := hg4.1
    exact h1.mul h2
  -- the product rule of the primed interface, priced by the weighted norm
  have hprod := hN.wprod α ⟨hα, hαα₂⟩ (Row10StarH α Φs)
    (fun z θ => z / (1 + z) * g z θ) hHsm hHmem ⟨hφsm, hφmem⟩
  -- the row-10 piece is `2` times that product on the open quadrant
  have hagree : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.Nonlin.N1sg α Φs g z θ
        = 2 * (Row10StarH α Φs z θ * (z / (1 + z) * g z θ)) := by
    intro z θ hz hθ0 hθ1
    have hz0 : z ≠ 0 := ne_of_gt hz
    have h1z : (1 : ℝ) + z ≠ 0 := by positivity
    simp only [Work.FTS.Nonlin.N1sg, Row10StarH]
    field_simp
    ring
  have hSeq : Work.Spaces.HkSq α 4 (Work.FTS.Nonlin.N1sg α Φs g)
      = Work.Spaces.HkSq α 4
          (fun z θ => 2 * (Row10StarH α Φs z θ * (z / (1 + z) * g z θ))) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 4 hagree
  constructor
  · -- `ℋ⁴`-honesty of the row-10 piece: transfer along the open-quadrant agreement
    have hNsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1sg α Φs g) := by
      have hc2 : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => fun _ : ℝ => (2 : ℝ)) := by
        show ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => (2 : ℝ))
          Work.FTS.EllipticEst.Q0
        exact contDiffOn_const
      have hR := Work.FTS.NonlinRows.NRow10aux.smoothOpen_Rop (α := α)
        (Work.FTS.NonlinRows.NRow10aux.smoothOpen_PhiTs (α := α) (Cs := Cs) hα hα1 hs)
      have h2R := Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul hc2 hR
      have hfin := Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul h2R hg4.1
      exact hfin
    have hmaj : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Work.Spaces.HkIntegrand α 4 (Work.FTS.Nonlin.N1sg α Φs g) z θ
          ≤ 1 * Work.Spaces.HkIntegrand α 4
              (fun z θ => 2 * (Row10StarH α Φs z θ * (z / (1 + z) * g z θ))) z θ := by
      intro z hz θ hθ
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h | h
      · rw [← h, one_mul, Work.FTS.NonlinRows.NRow10aux.HkIntegrand_zero α 4 _ θ,
          Work.FTS.NonlinRows.NRow10aux.HkIntegrand_zero α 4 _ θ]
      · rw [one_mul,
          ← Work.FTS.EllipticEst.HkIntegrand_congr (α := α) (k := 4) hagree z θ h hθ.1 hθ.2]
    have hmem2 : Work.Spaces.HkMem α 4
        (fun z θ => 2 * (Row10StarH α Φs z θ * (z / (1 + z) * g z θ))) :=
      Work.FTS.LocData.HkMem_const_mul α 4 2 hprod.1
    exact (Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant α 4
      (show (0 : ℝ) ≤ 1 by norm_num) hNsm hmem2 hmaj).1
  · -- the bound
    have hXn : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1sg α Φs g)
        = 2 * Work.FTS.Nonlin.Xn α
            (fun z θ => Row10StarH α Φs z θ * (z / (1 + z) * g z θ)) := by
      rw [show Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1sg α Φs g)
            = Work.FTS.Nonlin.Xn α
                (fun z θ => 2 * (Row10StarH α Φs z θ * (z / (1 + z) * g z θ))) from by
          simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, hSeq],
        Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α 2
          (fun z θ => Row10StarH α Φs z θ * (z / (1 + z) * g z θ)),
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [hXn]
    have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hS : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
      mul_nonneg (Real.sqrt_nonneg α) hXg
    have hsqrt : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
      rw [Real.sqrt_eq_rpow]
      have h := Real.rpow_add hα (-(1 / 2 : ℝ)) (1 : ℝ)
      rw [Real.rpow_one, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
      exact h.symm
    have hbnd1 : Work.FTS.Nonlin.Xn α
          (fun z θ => Row10StarH α Φs z θ * (z / (1 + z) * g z θ))
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α) * (Cφ * Work.FTS.Nonlin.Xn α g) := by
      refine le_trans hprod.2 ?_
      have hWnn : 0 ≤ Work.Spaces.WlInf α 4 (Row10StarH α Φs) :=
        Work.Spaces.WlInf_nonneg α 4 _ hHmem
      have hA : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) :=
        mul_nonneg hCi.le (Real.rpow_nonneg hα.le _)
      have hB : 0 ≤ Cφ * Work.FTS.Nonlin.Xn α g := mul_nonneg hCφ.le hXg
      calc Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 (Row10StarH α Φs)
            * Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * g z θ)
          ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 (Row10StarH α Φs)
              * (Cφ * Work.FTS.Nonlin.Xn α g) :=
            mul_le_mul_of_nonneg_left hφbnd (mul_nonneg hA hWnn)
        _ = Ci * α ^ (-(1 / 2 : ℝ)) * (Cφ * Work.FTS.Nonlin.Xn α g)
              * Work.Spaces.WlInf α 4 (Row10StarH α Φs) := by ring
        _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cφ * Work.FTS.Nonlin.Xn α g)
              * (max Cs 0 * α) := mul_le_mul_of_nonneg_left hHle' (mul_nonneg hA hB)
        _ = Ci * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α)
              * (Cφ * Work.FTS.Nonlin.Xn α g) := by ring
    have hbnd2 : 2 * Work.FTS.Nonlin.Xn α
          (fun z θ => Row10StarH α Φs z θ * (z / (1 + z) * g z θ))
        ≤ (2 * Ci * Cφ * max Cs 0) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
      refine le_trans (mul_le_mul_of_nonneg_left hbnd1 (by norm_num)) ?_
      rw [show 2 * (Ci * α ^ (-(1 / 2 : ℝ)) * (max Cs 0 * α)
            * (Cφ * Work.FTS.Nonlin.Xn α g))
          = 2 * Ci * Cφ * max Cs 0 * (α ^ (-(1 / 2 : ℝ)) * α)
              * Work.FTS.Nonlin.Xn α g from by ring, hsqrt]
      exact le_of_eq (by ring)
    refine le_trans hbnd2 ?_
    have hCs : 0 ≤ max Cs 0 := le_max_right Cs 0
    have hle : 2 * Ci * Cφ * max Cs 0 ≤ 2 * Ci * (Cφ * Cφ + 1) * max Cs 0 + 1 := by
      have hφ' : Cφ ≤ Cφ * Cφ + 1 := by nlinarith [hCφ.le]
      nlinarith [hCi.le, hCs, hφ', mul_nonneg hCi.le hCs, sq_nonneg Cφ]
    exact mul_le_mul_of_nonneg_right hle hS

end Work.FTS.Nonlinear.Open
