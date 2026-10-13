import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.NonlinRows.NRow1
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

/-!
# The `N₀`-fixed block of the level-three right-hand side

`N0fix α = N₀₁ + N₀₂` depends on the profile `F_*` alone, and on the open quadrant it is the
separable datum `Kfac α · rhoR · psiA α`, whose `ℋ⁴`-norm is `O(α²)`
(`Work.FTS.Nonlinear.Pieces.RowsN0Aux.N0fix_bound`,
`Work.FTS.NonlinRows.HkMem_N0fix`).  Since `ℋ³ ⊂ ℋ⁴` (both for the membership and for the
norm, `Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen` /
`Work.FTS.StrongLWP.HkNorm_mono_of_mem`), the same block satisfies the level-three clauses of
the level-three right-hand side with the same constant, **provided** one records that it is
`C^∞` on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen`).

The one ingredient that is not a direct citation is that smoothness: on the open quadrant
`L₁₂(F_*(α))(z) = 2α/(1+z)` (`Work.Construction.L12_Fstar_eq`) is an explicit rational
function of `z`, `F_*` is `SmoothOpen` (`Work.FTS.LocData.SmoothQuad_Fstar`), and the angular
factors `sin 2θ`, `cos 2θ - sin²θ` are smooth everywhere, so `N0fix α` is a sum of products of
smooth functions on the quadrant.
-/

/-- **`L₁₂(F_*(α))` is `C^∞` on `(0,∞)`**: on that set it equals the explicit function
`z ↦ 2α/(1+z)` (`Work.Construction.L12_Fstar_eq`). -/
theorem contDiffOn_L12_Fstar_L3 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) :
    ContDiffOn ℝ m (fun z : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) z)
      (Set.Ioi 0) := by
  have hbase : ContDiffOn ℝ m (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ m (fun z : ℝ => (1 : ℝ) + z) (Set.Ioi 0) :=
      contDiffOn_const.add contDiffOn_id
    have h2 := (contDiffOn_const (c := 2 * α) :
      ContDiffOn ℝ m (fun _ : ℝ => 2 * α) (Set.Ioi 0)).div h1
      (fun z hz => by
        have hz' : (0 : ℝ) < z := hz
        have : (0 : ℝ) < 1 + z := by linarith
        linarith)
    exact h2
  refine ContDiffOn.congr hbase ?_
  intro z hz
  exact Work.Construction.L12_Fstar_eq hα hα1 hz.le

/-- **`N0fix α` is `C^∞` on the open quadrant.**  Unfolding `N0fix = N₀₁ + N₀₂`, the block is
the sum of the two products

`((3/(2α)) sin 2θ L₁₂(F_*(α))) · ∂_θF_*(α)` and `(-(cos 2θ - sin²θ) L₁₂(F_*(α))) · D_zF_*(α)`,

each a product of an angular factor (smooth everywhere), the radial factor `L₁₂(F_*(α))`
(smooth on `(0,∞)` by `contDiffOn_L12_Fstar_L3`) and a derivative of the `SmoothOpen` profile
`F_*(α)`. -/
theorem smoothOpen_N0fix (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N0fix α) := by
  have hL12 : ∀ m : ℕ, ContDiffOn ℝ m
      (fun z : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) z) (Set.Ioi 0) :=
    contDiffOn_L12_Fstar_L3 α hα hα1
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * Real.sin (2 * θ)
        * Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul_swap hL12
      (by fun_prop : ContDiff ℝ ⊤ (fun θ : ℝ => (3 / (2 * α)) * Real.sin (2 * θ)))
  have hB : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(Real.cos (2 * θ) - Real.sin θ ^ 2))
        * Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul_swap hL12
      (by fun_prop : ContDiff ℝ ⊤ (fun θ : ℝ => (-(Real.cos (2 * θ) - Real.sin θ ^ 2))))
  have hT1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      ((3 / (2 * α)) * Real.sin (2 * θ) * Work.Construction.L12 (Work.Construction.Fstar α) z)
        * Work.Spaces.pth (Work.Construction.Fstar α) z θ) := hA.mul hFsm.pth
  have hT2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      ((-(Real.cos (2 * θ) - Real.sin θ ^ 2))
        * Work.Construction.L12 (Work.Construction.Fstar α) z)
        * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) := hB.mul hFsm.Dz
  have hsum : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      ((3 / (2 * α)) * Real.sin (2 * θ) * Work.Construction.L12 (Work.Construction.Fstar α) z)
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        + ((-(Real.cos (2 * θ) - Real.sin θ ^ 2))
            * Work.Construction.L12 (Work.Construction.Fstar α) z)
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) := hT1.add hT2
  refine Work.FTS.EllipticEst.SmoothOpen.congr hsum ?_
  intro z θ hz hθ hθ2
  simp only [Work.FTS.Nonlin.N0fix, Work.Construction.N01, Work.Construction.N02,
    Work.Construction.s2_eq, Work.Construction.c2m_eq]

theorem L3RhsN0FixBlock : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N0fix α) ∧
    Work.Spaces.HkMem α 3 (Work.FTS.Nonlin.N0fix α) ∧
    Work.Spaces.HkNorm α 3 (Work.FTS.Nonlin.N0fix α) ≤ C * α ^ 2 := by
  obtain ⟨K, hK, hbnd⟩ := Work.FTS.Nonlinear.Pieces.RowsN0Aux.N0fix_bound
  refine ⟨K, hK, fun α hα => ?_⟩
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hso : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N0fix α) :=
    smoothOpen_N0fix α hα0 hα1
  have h4 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.NonlinRows.HkMem_N0fix α hα0 hα1
  have h3 : Work.Spaces.HkMem α 3 (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen (α := α) (k := 3) (k' := 4)
      (by norm_num) hso h4
  have hnorm : Work.Spaces.HkNorm α 3 (Work.FTS.Nonlin.N0fix α)
      ≤ Work.Spaces.HkNorm α 4 (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 4) (k' := 3) (by norm_num) h4
  exact ⟨hso, h3, le_trans hnorm (hbnd α hα0 hα1)⟩

end Work.FTS.StrongPersist.L3Rhs
