import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.Inputs.SliceTr
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.Inputs

theorem ftau_Dz_le {a : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {C₀ : ℝ} {g G : Work.FTS.Galerkin.Fam} {A B : ℝ → ℝ}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g)
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ τ : ℝ, 0 ≤ τ → ∃ M : ℝ, 0 ≤ M ∧ ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z θ| ≤ M := by
  intro τ hτ
  -- The uniform bound on the open quadrant, for the *sanitised* family `GR a g`.
  obtain ⟨C, hC0, hC⟩ :=
    Work.FTS_RegExport.RXT.Ftau_bounds (α := a) ha ha13 hOK τ hτ
  refine ⟨C, hC0, ?_⟩
  intro z θ hz hθ
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ2 : θ ≤ π / 2 := hθ.2
  rcases lt_or_eq_of_le hθ0 with h0 | h0
  · rcases lt_or_eq_of_le hθ2 with h2 | h2
    · -- `0 < θ < π/2`: transfer the bound from the sanitised family, which agrees with `g` there.
      have hev : (fun z' => Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Construction.Ftau (Work.FTS.Regularity.pExp a)
              (Work.FTS.RegExportIface.RXT.GR a g) τ z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        show Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z' θ + g z' θ τ
          = Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z' θ
            + Work.FTS.RegExportIface.RXT.GR a g z' θ τ
        rw [Work.FTS_RegExport.RXT.ftau_GR_of_quad hτ hz' h0.le h2.le]
      have hDz : Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z θ
          = Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp a)
              (Work.FTS.RegExportIface.RXT.GR a g) τ) z θ := by
        simp only [Work.Spaces.Dz, Work.Spaces.pz]
        rw [hev.deriv_eq]
      rw [hDz]
      exact (hC z θ hz h0 h2).2.1
    · -- `θ = π/2`: the whole profile vanishes on the angular boundary, hence so does `D_z`.
      subst h2
      have hzero : Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z
          (π / 2) = 0 := by
        have hev : (fun z' => Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z' (π / 2))
            =ᶠ[𝓝 z] fun _ => 0 := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
          exact (ftau_vanish (a := a) (ne_of_gt ha) hτ hreg hG z' hz').2
        simp only [Work.Spaces.Dz, Work.Spaces.pz]
        rw [hev.deriv_eq]
        simp
      rw [hzero]
      simpa using hC0
  · -- `θ = 0`: same vanishing argument.
    subst h0
    have hzero : Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z 0
        = 0 := by
      have hev : (fun z' => Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z' 0)
          =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact (ftau_vanish (a := a) (ne_of_gt ha) hτ hreg hG z' hz').1
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [hev.deriv_eq]
      simp
    rw [hzero]
    simpa using hC0

end Work.FTS_StreamBdry.Inputs
