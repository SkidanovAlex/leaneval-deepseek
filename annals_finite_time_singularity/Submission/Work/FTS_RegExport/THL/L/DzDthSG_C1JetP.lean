import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_RegExport.THL.L.DzG_theta_mod
import Submission.Work.FTS_RegExport.THL.L.DthG_theta_mod
import Submission.Work.FTS_RegExport.THL.L.DzDthG_bound_zderiv
import Submission.Work.FTS_RegExport.THL.L.DzDthG_tau_mod
import Submission.Work.FTS_RegExport.RXR5.zhmod_of
import Submission.Work.FTS.RegPkgGal.R3d.jet_g

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.THL.L

theorem DzDthSG_C1JetP {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S K : ℝ} (hS : 0 < S) (hK0 : 0 ≤ K) (hw : Work.FTS_RegExport.THL.WSys α S K g) :
    ∃ N₂ N₃ : ℝ, 0 ≤ N₂ ∧ 0 ≤ N₃ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₂ (Work.FTS_RegExport.THL.DzG α g) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₃ (Work.FTS_RegExport.THL.DthG α g) := by
  have hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g := hOK.1.1
  have hα1 : α ≤ 1 := by linarith
  -- **B3**: uniform value bounds, continuity at `z = 0` and bounded `z`-derivatives on `z > 0`.
  obtain ⟨N, hN0, hb3⟩ := DzDthG_bound_zderiv hα hα13 hmin hS hK0 hw
  -- **B1**, **B2**: the `z`-uniform `θ`-moduli of `D_z g̃` and `D_θ g̃`.
  obtain ⟨Lθ₂, hLθ₂0, hθ₂⟩ := DzG_theta_mod hα hα13 hmin hS hK0 hw
  obtain ⟨Lθ₃, hLθ₃0, hθ₃⟩ := DthG_theta_mod hα hα13 hmin hS hK0 hw
  -- **B4**: the `τ`-moduli of both families.
  obtain ⟨Lτ, hLτ0, hτmod⟩ := DzDthG_tau_mod hα hα13 hOK hS
  -- **the `z`-moduli**, from B3 through the half-line interpolation `RXR5.zhmod_of`.
  have hz₂ : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |Work.FTS_RegExport.THL.DzG α g z θ τ - Work.FTS_RegExport.THL.DzG α g z' θ τ|
        ≤ max N (2 * N) * |z - z'| ^ α := by
    refine Work.FTS_RegExport.RXR5.zhmod_of hα hα1 hN0 hN0 ?_ ?_ ?_ ?_
    · intro τ hτ θ hθ x hx
      obtain ⟨d, hd, -⟩ := ((hb3 τ hτ θ hθ).2.2.2 x hx).1
      exact hd.differentiableAt
    · intro τ hτ θ hθ x hx
      obtain ⟨d, hd, hdb⟩ := ((hb3 τ hτ θ hθ).2.2.2 x hx).1
      rw [hd.deriv]
      exact hdb
    · intro τ hτ θ hθ
      exact (hb3 τ hτ θ hθ).2.1
    · intro τ hτ θ hθ z hz
      exact ((hb3 τ hτ θ hθ).1 z hz).1
  have hz₃ : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |Work.FTS_RegExport.THL.DthG α g z θ τ - Work.FTS_RegExport.THL.DthG α g z' θ τ|
        ≤ max N (2 * N) * |z - z'| ^ α := by
    refine Work.FTS_RegExport.RXR5.zhmod_of hα hα1 hN0 hN0 ?_ ?_ ?_ ?_
    · intro τ hτ θ hθ x hx
      obtain ⟨d, hd, -⟩ := ((hb3 τ hτ θ hθ).2.2.2 x hx).2
      exact hd.differentiableAt
    · intro τ hτ θ hθ x hx
      obtain ⟨d, hd, hdb⟩ := ((hb3 τ hτ θ hθ).2.2.2 x hx).2
      rw [hd.deriv]
      exact hdb
    · intro τ hτ θ hθ
      exact (hb3 τ hτ θ hθ).2.2.1
    · intro τ hτ θ hθ z hz
      exact ((hb3 τ hτ θ hθ).1 z hz).2
  -- **the `Jet`s**, by the one-variable-Hölder upgrade `R3d.jet_of_bounded_holder`.
  obtain ⟨J₂, hJ₂⟩ := Work.FTS.RegPkgGal.R3d.jet_of_bounded_holder
    (α := α) (S := S) (M := N) (Lz := max N (2 * N)) (Lθ := Lθ₂) (Lt := Lτ)
    hα hN0 (le_trans hN0 (le_max_left N (2 * N))) hLθ₂0 hLτ0
    (fun τ hτ z θ hz hθ => ((hb3 τ hτ θ hθ).1 z hz).1)
    (fun τ hτ z z' hz hz' θ hθ => hz₂ τ hτ θ hθ z z' hz hz')
    (fun τ hτ z hz θ hθ θ' hθ' => hθ₂ τ hτ z hz θ hθ θ' hθ')
    (fun τ hτ τ' hτ' z hz θ hθ => (hτmod τ hτ τ' hτ' z hz θ hθ).1)
  obtain ⟨J₃, hJ₃⟩ := Work.FTS.RegPkgGal.R3d.jet_of_bounded_holder
    (α := α) (S := S) (M := N) (Lz := max N (2 * N)) (Lθ := Lθ₃) (Lt := Lτ)
    hα hN0 (le_trans hN0 (le_max_left N (2 * N))) hLθ₃0 hLτ0
    (fun τ hτ z θ hz hθ => ((hb3 τ hτ θ hθ).1 z hz).2)
    (fun τ hτ z z' hz hz' θ hθ => hz₃ τ hτ θ hθ z z' hz hz')
    (fun τ hτ z hz θ hθ θ' hθ' => hθ₃ τ hτ z hz θ hθ θ' hθ')
    (fun τ hτ τ' hτ' z hz θ hθ => (hτmod τ hτ τ' hτ' z hz θ hθ).2)
  refine ⟨max J₂ N, max J₃ N, le_trans hN0 (le_max_right J₂ N),
    le_trans hN0 (le_max_right J₃ N), ?_, ?_⟩
  · -- `D_z g̃`: the `Jet` at the larger constant `max J₂ N`, and the `z`-derivative half from B3
    refine ⟨⟨le_trans hJ₂.1 (le_max_left J₂ N), ?_, ?_⟩, ?_⟩
    · intro z θ τ hz hθ hτ
      exact le_trans (hJ₂.2.1 z θ τ hz hθ hτ) (le_max_left J₂ N)
    · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
      exact le_trans (hJ₂.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ')
        (mul_le_mul_of_nonneg_right (le_max_left J₂ N)
          (Real.rpow_nonneg (by positivity) α))
    · intro τ hτ θ hθ z hz
      obtain ⟨d, hd, hdb⟩ := ((hb3 τ hτ θ hθ).2.2.2 z hz).1
      exact ⟨d, hd, le_trans hdb (le_max_right J₂ N)⟩
  · -- `D_θ g̃`: same, at `max J₃ N`
    refine ⟨⟨le_trans hJ₃.1 (le_max_left J₃ N), ?_, ?_⟩, ?_⟩
    · intro z θ τ hz hθ hτ
      exact le_trans (hJ₃.2.1 z θ τ hz hθ hτ) (le_max_left J₃ N)
    · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
      exact le_trans (hJ₃.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ')
        (mul_le_mul_of_nonneg_right (le_max_left J₃ N)
          (Real.rpow_nonneg (by positivity) α))
    · intro τ hτ θ hθ z hz
      obtain ⟨d, hd, hdb⟩ := ((hb3 τ hτ θ hθ).2.2.2 z hz).2
      exact ⟨d, hd, le_trans hdb (le_max_right J₃ N)⟩

end Work.FTS_RegExport.THL.L
