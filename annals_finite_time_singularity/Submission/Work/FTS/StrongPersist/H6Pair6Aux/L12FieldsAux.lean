import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RadialMul6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12slotLe7
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.Blocks.HkMul_ang_le
import Submission.Work.FTS.CoercivityFix.Assembly.RegQAux
import Submission.Work.Coercivity.HkMem_congr_Ioi
import Submission.Work.FTS.IPGen.OpenBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `ContDiffOn ℝ 6` of a radial function which is `SmoothOpen`. -/
theorem curry_six {Λ : ℝ → ℝ}
    (hΛ : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Λ z)) :
    ContDiffOn ℝ 6 Λ (Set.Ioi 0) :=
  (hΛ.curry_z (θ := 1/2) (by constructor <;> linarith [Real.pi_gt_three])).of_le
    (by simp [Work.Stability.smoothOrder])

/-- `SmoothOpen` is closed under negation. -/
theorem so_neg {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => - g z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hg ⊢
  have h : Function.uncurry (fun z θ => - g z θ) = - Function.uncurry g := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]
  exact hg.neg

/-- `SmoothOpen` of the angular profile `qfun·Γ`.  (`Γ` is only `C^∞` on the open quadrant,
so this must be proved at the finite orders via `contDiffOn_Gam_Qd`.) -/
theorem smoothOpen_qfunGam (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Spaces.qfun θ * Work.Spaces.Gam α θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have h : Function.uncurry (fun _ (θ : ℝ) => Work.Spaces.qfun θ * Work.Spaces.Gam α θ)
      = fun p : ℝ × ℝ => Work.Spaces.qfun p.2 * Work.Spaces.Gam α p.2 := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]
  exact ContDiffOn.mul ((((Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).sub
      contDiff_const).contDiffOn).comp contDiffOn_snd (fun p _ => Set.mem_univ _))
    (Work.FTS.CoercivityFix.Transfer.contDiffOn_Gam_Qd α n)

/-- **The `f`-family of the `N₀`-pieces**: the three products of `L₁₂ f` with the fields
`f`, `D_θ f` and `-c2m(θ)·D_zf` are honest in `ℋ⁶`. -/
theorem L12_mul_fields {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z))
    (h0 : Work.Construction.L12 f 0 = 0)
    (m6 : Work.Spaces.HkMem α 6 f) (m7 : Work.Spaces.HkMem α 7 f) :
    Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.L12 f z * f z θ) ∧
    Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) ∧
    Work.Spaces.HkMem α 6 (fun z θ =>
      Work.Construction.L12 f z * (-(Work.Construction.c2m θ) * Work.Spaces.Dz f z θ)) := by
  obtain ⟨C₆, hC₆pos, hC₆⟩ := L12Sup6
  set Λ : ℝ → ℝ := fun z => Work.Construction.L12 f z with hΛdef
  have hΛsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Λ z) := hL
  have hXn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hM0 : 0 ≤ C₆ * Work.Spaces.HkNorm α 6 f := mul_nonneg hC₆pos.le hXn
  have hΛb : ∀ b ≤ 6, ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b Λ z| ≤ C₆ * Work.Spaces.HkNorm α 6 f :=
    fun b hb z hz => hC₆ α f hα hα1 hf m6 m7 h0 b hb z hz
  have hDthmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (by linarith) hf m7
  have hDzmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dz f) :=
    Work.FTS.IPGen.HkMem_Dz_le hf m7
  -- the `-c2m·D_zf` field
  have hsin2sm : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Real.sin θ ^ 2) :=
    so_snd ((Real.contDiff_sin).pow 2)
  obtain ⟨_, _, hmul⟩ := Work.Blocks.HkMul_ang_le 6
  obtain ⟨-, -, hmain⟩ := hmul α (Work.Spaces.Dz f) hα hα1 hf.Dz
  obtain ⟨-, -, hs2mem, -⟩ := hmain hDzmem
  have hψmem : Work.Spaces.HkMem α 6
      (fun z θ => -(Work.Construction.c2m θ) * Work.Spaces.Dz f z θ) := by
    have h1 : Work.Spaces.HkMem α 6 (fun z θ => (-1 : ℝ) * Work.Spaces.Dz f z θ) :=
      Work.FTS.LocData.HkMem_const_mul α 6 (-1) hDzmem
    have h2 : Work.Spaces.HkMem α 6
        (fun z θ => (3 : ℝ) * (Real.sin θ ^ 2 * Work.Spaces.Dz f z θ)) :=
      Work.FTS.LocData.HkMem_const_mul α 6 3 hs2mem
    have hsm1 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-1 : ℝ) * Work.Spaces.Dz f z θ) :=
      so_const_mul (-1) hf.Dz
    have hsm2 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (3 : ℝ) * (Real.sin θ ^ 2 * Work.Spaces.Dz f z θ)) :=
      so_const_mul 3 (so_mul hsin2sm hf.Dz)
    have hsum := Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 6 hsm1 hsm2 h1 h2
    refine Work.Coercivity.HkMem_congr_Ioi α 6 hsum ?_
    intro z hz θ hθ
    rw [Work.Construction.c2m_eq, Real.cos_two_mul, Real.sin_sq]
    ring
  have hψsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(Work.Construction.c2m θ) * Work.Spaces.Dz f z θ) :=
    so_mul (so_neg (so_snd contDiff_c2m)) hf.Dz
  exact ⟨RadialMul6 hM0 hΛsm hΛb hf m6,
    RadialMul6 hM0 hΛsm hΛb hf.Dth hDthmem,
    RadialMul6 hM0 hΛsm hΛb hψsm hψmem⟩

end Work.FTS.StrongPersist.H6Pair6Aux
