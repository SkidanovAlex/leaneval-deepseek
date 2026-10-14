import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.StrongEps.EComparison.E_slots_diff_le
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongEps.EpsRLX.ConjTwo
import Submission.Work.FTS.StrongEps.TenOfEight.GainAll
import Submission.Work.FTS.StrongPersist.StarPkg6Fields
import Submission.Work.FTS_RegExport.RXR1.mixed_abs_le_weighted
import Submission.Work.FTS_RegExport.RXVP.thLip

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

theorem EpsRHSPLipX {α C₀ Ce Cs B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hB : 0 ≤ B) :
    ∃ L : ℝ, 0 < L ∧
      (∀ (τ : ℝ) (u : Work.FTS.Galerkin.Fn),
        Work.FTS.EllipticEst.SmoothOpen u → Work.Spaces.HkMem α 6 u →
        Work.Spaces.HkNorm α 6 u ≤ B →
        Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)) →
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)) ≤ C₀ * α ^ 2 →
        Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E τ u) ∧
        Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E τ u) ≤ L) ∧
      (∀ (τ : ℝ) (u v : Work.FTS.Galerkin.Fn),
        Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.EllipticEst.SmoothOpen v →
        Work.Spaces.HkMem α 6 u → Work.Spaces.HkMem α 6 v →
        Work.Spaces.HkNorm α 6 u ≤ B → Work.Spaces.HkNorm α 6 v ≤ B →
        Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)) →
        Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε v)) →
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)) ≤ C₀ * α ^ 2 →
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε v)) ≤ C₀ * α ^ 2 →
        Work.FTS.StrongEps.EpsSq α (fun z θ => Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E τ u z θ
            - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E τ v z θ)
          ≤ L * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
  -- The two halves of the gate, with their own constants.
  obtain ⟨L₁, hL₁pos, hL₁⟩ :=
    Work.FTS.StrongEps.EpsRLX.ConjOne (ρ := ρ) (Φs := Φs) (E := E)
      hα hρ hε hε1 hEll hstar hml hB
  obtain ⟨L₂, hL₂pos, hL₂⟩ :=
    Work.FTS.StrongEps.EpsRLX.ConjTwo (ρ := ρ) (Φs := Φs) (E := E)
      hα hρ hε hε1 hEll hstar hml hB
  -- `Wp ρ ε u` is `Pz (Jeps ρ ε u)` by definition, so `ConjOne`/`ConjTwo` apply with the
  -- hypotheses of the target at face value.
  refine ⟨max L₁ L₂, lt_of_lt_of_le hL₁pos (le_max_left L₁ L₂), ?_, ?_⟩
  · intro τ u hu hmu hnu hcl hxn
    obtain ⟨hmem, hbd⟩ := hL₁ τ u hu hmu hnu hcl hxn
    exact ⟨hmem, le_trans hbd (le_max_left L₁ L₂)⟩
  · intro τ u v hu hv hmu hmv hnu hnv hclu hclv hxnu hxnv
    refine le_trans (hL₂ τ u v hu hv hmu hmv hnu hnv hclu hclv hxnu hxnv) ?_
    exact mul_le_mul_of_nonneg_right (le_max_right L₁ L₂)
      (Work.FTS.StrongEps.EpsSq_nonneg α (fun z θ => u z θ - v z θ))

end Work.FTS.StrongEps.EpsLocalPStar
