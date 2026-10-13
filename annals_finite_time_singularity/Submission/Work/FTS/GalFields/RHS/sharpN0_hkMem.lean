import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.GalFields.RHS.sharpN0_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The `ℋ⁴`-honesty of the `N₀`-block**, assembled from the split (rows 1--7) and the
per-piece honesty of the seven summands.  The smoothness of the pieces is read off from the
smoothness of `F_*`, `L₁₂(F_*)` and `g`, `L₁₂(g)`. -/
theorem hkMem_N0_of_rows {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hLgSm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z))
    (hm1 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N0fix α))
    (hm2 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N03g α g))
    (hm3 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04aF α g))
    (hm4 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04bF α g))
    (hm5 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05aF α g))
    (hm6 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05bF α g))
    (hm7 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N06F α g))
    (hsplit : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
        = Work.FTS.Nonlin.N0fix α z θ + (Work.FTS.Nonlin.N03g α g z θ
          + Work.FTS.Nonlin.N04aF α g z θ + Work.FTS.Nonlin.N04bF α g z θ
          + Work.FTS.Nonlin.N05aF α g z θ + Work.FTS.Nonlin.N05bF α g z θ
          + Work.FTS.Nonlin.N06F α g z θ)) :
    Work.Spaces.HkMem α 4 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) := by
  have hFstarSm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hLFstarSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_L12_Fstar α
  have hc2mSm : Work.FTS.EllipticEst.SmoothOpen
      (fun _ (θ : ℝ) => Work.Construction.c2m θ) := smoothOpen_c2m_ang
  have hs2Sm : Work.FTS.EllipticEst.SmoothOpen
      (fun _ (θ : ℝ) => Work.Construction.s2 θ) := smoothOpen_sin_two_ang
  have h1sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N0fix α) := by
    show Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.Construction.N01 α (Work.Construction.Ftot α (fun _ _ => (0 : ℝ))) (fun _ _ => (0 : ℝ)) z θ
        + Work.Construction.N02 α (Work.Construction.Ftot α (fun _ _ => (0 : ℝ)))
            (fun _ _ => (0 : ℝ)) z θ)
    refine Work.FTS.NonlinRows.smoothOpen_add ?_ ?_
    · show Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ)
      exact Work.FTS.NonlinRows.smoothOpen_mul (Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α)) hs2Sm) hLFstarSm) hFstarSm.pth
    · show Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        -Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
      exact Work.FTS.NonlinRows.smoothOpen_mul (Work.FTS.NonlinRows.smoothOpen_mul
        (smoothOpen_neg' hc2mSm) hLFstarSm) hFstarSm.Dz
  have h2sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N03g α g) := by
    show Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (1 / α) * Work.Construction.L12 g z * g z θ)
    exact Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_const_mul (1 / α) hLgSm) hgsm
  have h3sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04aF α g) := by
    show Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g z
        * Work.Spaces.pth (Work.Construction.Fstar α) z θ)
    exact Work.FTS.NonlinRows.smoothOpen_mul (Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α)) hs2Sm) hLgSm) hFstarSm.pth
  have h4sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04bF α g) := by
    show Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g z
        * Work.Spaces.pth g z θ)
    exact Work.FTS.NonlinRows.smoothOpen_mul (Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α)) hs2Sm) hLgSm) hgsm.pth
  have h5sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05aF α g) := by
    show Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      -Work.Construction.c2m θ * Work.Construction.L12 g z
        * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
    exact Work.FTS.NonlinRows.smoothOpen_mul (Work.FTS.NonlinRows.smoothOpen_mul
      (smoothOpen_neg' hc2mSm) hLgSm) hFstarSm.Dz
  have h6sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05bF α g) := by
    show Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      -Work.Construction.c2m θ * Work.Construction.L12 g z * Work.Spaces.Dz g z θ)
    exact Work.FTS.NonlinRows.smoothOpen_mul (Work.FTS.NonlinRows.smoothOpen_mul
      (smoothOpen_neg' hc2mSm) hLgSm) hgsm.Dz
  have h7sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N06F α g) := by
    show Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      -Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
        * Work.Spaces.Dz g z θ)
    exact Work.FTS.NonlinRows.smoothOpen_mul (Work.FTS.NonlinRows.smoothOpen_mul
      (smoothOpen_neg' hc2mSm) hLFstarSm) hgsm.Dz
  have hAsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.FTS.Nonlin.N03g α g z θ + Work.FTS.Nonlin.N04aF α g z θ) :=
    Work.FTS.NonlinRows.smoothOpen_add h2sm h3sm
  have hAmem : Work.Spaces.HkMem α 4 (fun z θ =>
      Work.FTS.Nonlin.N03g α g z θ + Work.FTS.Nonlin.N04aF α g z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open h2sm h3sm hm2 hm3
  have hBsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (Work.FTS.Nonlin.N03g α g z θ + Work.FTS.Nonlin.N04aF α g z θ)
        + Work.FTS.Nonlin.N04bF α g z θ) :=
    Work.FTS.NonlinRows.smoothOpen_add hAsm h4sm
  have hBmem : Work.Spaces.HkMem α 4 (fun z θ =>
      (Work.FTS.Nonlin.N03g α g z θ + Work.FTS.Nonlin.N04aF α g z θ)
        + Work.FTS.Nonlin.N04bF α g z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hAsm h4sm hAmem hm4
  have hCsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      ((Work.FTS.Nonlin.N03g α g z θ + Work.FTS.Nonlin.N04aF α g z θ)
        + Work.FTS.Nonlin.N04bF α g z θ) + Work.FTS.Nonlin.N05aF α g z θ) :=
    Work.FTS.NonlinRows.smoothOpen_add hBsm h5sm
  have hCmem : Work.Spaces.HkMem α 4 (fun z θ =>
      ((Work.FTS.Nonlin.N03g α g z θ + Work.FTS.Nonlin.N04aF α g z θ)
        + Work.FTS.Nonlin.N04bF α g z θ) + Work.FTS.Nonlin.N05aF α g z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hBsm h5sm hBmem hm5
  have hDsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (((Work.FTS.Nonlin.N03g α g z θ + Work.FTS.Nonlin.N04aF α g z θ)
        + Work.FTS.Nonlin.N04bF α g z θ) + Work.FTS.Nonlin.N05aF α g z θ)
          + Work.FTS.Nonlin.N05bF α g z θ) :=
    Work.FTS.NonlinRows.smoothOpen_add hCsm h6sm
  have hDmem : Work.Spaces.HkMem α 4 (fun z θ =>
      (((Work.FTS.Nonlin.N03g α g z θ + Work.FTS.Nonlin.N04aF α g z θ)
        + Work.FTS.Nonlin.N04bF α g z θ) + Work.FTS.Nonlin.N05aF α g z θ)
          + Work.FTS.Nonlin.N05bF α g z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hCsm h6sm hCmem hm6
  have hEsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      ((((Work.FTS.Nonlin.N03g α g z θ + Work.FTS.Nonlin.N04aF α g z θ)
        + Work.FTS.Nonlin.N04bF α g z θ) + Work.FTS.Nonlin.N05aF α g z θ)
          + Work.FTS.Nonlin.N05bF α g z θ) + Work.FTS.Nonlin.N06F α g z θ) :=
    Work.FTS.NonlinRows.smoothOpen_add hDsm h7sm
  have hEmem : Work.Spaces.HkMem α 4 (fun z θ =>
      ((((Work.FTS.Nonlin.N03g α g z θ + Work.FTS.Nonlin.N04aF α g z θ)
        + Work.FTS.Nonlin.N04bF α g z θ) + Work.FTS.Nonlin.N05aF α g z θ)
          + Work.FTS.Nonlin.N05bF α g z θ) + Work.FTS.Nonlin.N06F α g z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hDsm h7sm hDmem hm7
  have hTotmem : Work.Spaces.HkMem α 4 (fun z θ =>
      Work.FTS.Nonlin.N0fix α z θ + (((((Work.FTS.Nonlin.N03g α g z θ
        + Work.FTS.Nonlin.N04aF α g z θ) + Work.FTS.Nonlin.N04bF α g z θ)
          + Work.FTS.Nonlin.N05aF α g z θ) + Work.FTS.Nonlin.N05bF α g z θ)
            + Work.FTS.Nonlin.N06F α g z θ)) :=
    Work.FTS.EllipticEst.HkMem_add_open h1sm hEsm hm1 hEmem
  exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hTotmem
    (fun z hz θ hθ => by
      rw [hsplit z θ ⟨hz, hθ⟩])


end Work.FTS.GalFields.RHS
