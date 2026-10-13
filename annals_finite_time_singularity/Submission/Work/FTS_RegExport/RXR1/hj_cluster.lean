import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXR1.HJ.HJDefs
import Submission.Work.FTS_RegExport.RXR1.HJ.HJBounds
import Submission.Work.FTS_RegExport.RXR1.HJ.HJTriple

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open Filter Set
open scoped Topology

namespace Work.FTS_RegExport.RXR1

theorem hj_cluster {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ,
      g z θ 0 = Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hSt1 : ∀ S > 0,
      Work.FTS.RegPkgGal.St1Class α S (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))) :
    ∀ S > 0,
      (∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
        Filter.Tendsto (fun p : ℝ × ℝ => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) p.1 θ p.2)
          (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)) ∧
      (∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
        Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) p.1 θ p.2)
          (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)) ∧
      (∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
        Filter.Tendsto (fun p : ℝ × ℝ =>
            deriv (fun z => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ p.2) p.1)
          (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)) := by
  intro S hS
  have hS2 : (0 : ℝ) < S + 2 := by linarith
  -- the two hypotheses, restated about the abbreviations `Gs`/`Ps`
  have hSt1' : ∀ S' > 0, Work.FTS.RegPkgGal.St1Class α S' (Gs α g) := hSt1
  have H5' : ∀ S' > 0, Work.FTS.RegPkgGal.R5Parts α S' (Gs α g) (Ps α Φs E g) := H5
  obtain ⟨K, Q, hK, hQ, hquad⟩ := (hSt1' (S + 2) hS2).quad
  obtain ⟨NZ, hNZ, hRbd, hRder⟩ :=
    exists_RHS_bound (S := S + 2) hα hα13 hS2 (H5' (S + 2) hS2)
  have H : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
      (Tendsto (fun p : ℝ × ℝ => Gs α g p.1 θ p.2) (Filt τ₀) (nhds 0)) ∧
      (Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * Gs α g p.1 θ p.2) (Filt τ₀) (nhds 0)) ∧
      (Tendsto (fun p : ℝ × ℝ => deriv (fun z => Gs α g z θ p.2) p.1) (Filt τ₀) (nhds 0)) := by
    intro θ hθ τ₀ hτ₀
    by_cases hends : θ = 0 ∨ θ = Real.pi / 2
    · have hz : ∀ z τ : ℝ, Gs α g z θ τ = 0 :=
        Gs_eq_zero_of_ends (hOK.1.1).vanish hθ hends
      refine ⟨?_, ?_, ?_⟩
      · exact tendsto_const_nhds.congr' (Eventually.of_forall fun p => (hz p.1 p.2).symm)
      · refine tendsto_const_nhds.congr' (Eventually.of_forall fun p => ?_)
        show (0 : ℝ) = p.1⁻¹ * Gs α g p.1 θ p.2
        rw [hz p.1 p.2]
        ring
      · refine tendsto_const_nhds.congr' (Eventually.of_forall fun p => ?_)
        show (0 : ℝ) = deriv (fun z : ℝ => Gs α g z θ p.2) p.1
        rw [show (fun z : ℝ => Gs α g z θ p.2) = fun _ => (0 : ℝ) from
          funext fun z => hz z p.2]
        simp
    · have hθIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_of_le_of_ne hθ.1 (fun h => hends (Or.inl h.symm)),
          lt_of_le_of_ne hθ.2 (fun h => hends (Or.inr h))⟩
      have hquadv : ∀ τ ∈ Set.Icc 0 (S + 2), ∀ z ∈ Set.Ioo (0 : ℝ) 2,
          |Gs α g z θ τ| ≤ K * z ^ 2 := by
        intro τ hτ z hz
        have h := (hquad τ hτ θ hθ).1 z hz.1.le hz.2.le
        rwa [Work.FTS.RegPkgGal.extG_of_pos hz.1 hτ.1] at h
      have hquadd : ∀ τ ∈ Set.Icc 0 (S + 2), ∀ z ∈ Set.Ioo (0 : ℝ) 2,
          |deriv (fun z' => Gs α g z' θ τ) z| ≤ Q * z := by
        intro τ hτ z hz
        have h := (hquad τ hτ θ hθ).2 z hz.1.le hz.2.le
        have hcongr : Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG (Gs α g)) τ) z θ
            = deriv (fun z' => Gs α g z' θ τ) z := by
          simp only [Work.Spaces.pz]
          exact (Filter.EventuallyEq.deriv_eq (by
            filter_upwards [isOpen_Ioi.mem_nhds hz.1] with z' hz'
            show Gs α g z' θ τ
              = Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG (Gs α g)) τ z' θ
            rw [show Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG (Gs α g)) τ z' θ
                = Work.FTS.RegPkgGal.extG (Gs α g) z' θ τ from rfl,
              Work.FTS.RegPkgGal.extG_of_pos hz' hτ.1])).symm
        rwa [hcongr] at h
      have hneg : ∀ z ∈ Set.Ioo (0 : ℝ) 2, ∀ τ < 0,
          Gs α g z θ τ = g z θ 0 + τ * RHSo α (Gs α g) (Ps α Φs E g) z θ := by
        intro z hz τ hτ
        rw [Gs_of_neg hz.1 hθ hτ, derivWithin_g_eq hz.1 hθ,
          derivWithin_eq_RHS (H5 (S + 2) hS2) hθIoo hz.1]
      have hdat0 : ∀ z ∈ Set.Ioo (0 : ℝ) 2, |g z θ 0| ≤ K * z ^ 2 := by
        intro z hz
        have h := hquadv 0 ⟨le_rfl, by linarith⟩ z hz
        rwa [Gs_of_nonneg hz.1 hθ le_rfl] at h
      have hA : ∀ z ∈ Set.Ioo (0 : ℝ) 2,
          ∃ A : ℝ, HasDerivAt (fun z' => g z' θ 0) A z ∧ |A| ≤ Q * z := by
        intro z hz
        have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz.1, hθIoo⟩
        have hsm : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g 0))
            Work.FTS.EllipticEst.Q0 := (hOK.1.1).c4 0 le_rfl
        have hdiff : DifferentiableAt ℝ (Function.uncurry (Work.FTS.Galerkin.slice g 0)) (z, θ) :=
          (hsm.differentiableOn (by norm_num)).differentiableAt
            (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
        have hcomp : HasFDerivAt
            (fun z' : ℝ => Function.uncurry (Work.FTS.Galerkin.slice g 0) (z', θ))
            ((fderiv ℝ (Function.uncurry (Work.FTS.Galerkin.slice g 0)) (z, θ))
              ∘SL ContinuousLinearMap.inl ℝ ℝ ℝ) z :=
          HasFDerivAt.comp z (g := Function.uncurry (Work.FTS.Galerkin.slice g 0))
            (f := fun z' : ℝ => (z', θ)) hdiff.hasFDerivAt (hasFDerivAt_prodMk_left z θ)
        have hAd : HasDerivAt (fun z' => g z' θ 0)
            ((fderiv ℝ (Function.uncurry (Work.FTS.Galerkin.slice g 0)) (z, θ)) (1, 0)) z := by
          have h := hcomp.hasDerivAt
          simpa only [Function.uncurry, Work.FTS.Galerkin.slice_apply,
            ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] using h
        refine ⟨_, hAd, ?_⟩
        rw [← hAd.deriv]
        have hcongr2 : deriv (fun z' => g z' θ 0) z = deriv (fun z' => Gs α g z' θ 0) z :=
          Filter.EventuallyEq.deriv_eq (by
            filter_upwards [isOpen_Ioi.mem_nhds hz.1] with z' hz'
            exact (Gs_of_nonneg hz' hθ le_rfl).symm)
        rw [hcongr2]
        exact hquadd 0 ⟨le_rfl, by linarith⟩ z hz
      rcases lt_or_eq_of_le hτ₀.1 with hτpos | hτzero
      · exact hj_triple_pos (G := Gs α g) hτpos (by linarith [hτ₀.2]) hquadv hquadd
      · subst hτzero
        exact hj_triple_zero (G := Gs α g)
          (R := fun z θ => RHSo α (Gs α g) (Ps α Φs E g) z θ) (gd := fun z => g z θ 0)
          hK hNZ hS2 hdat0 hquadv hquadd hneg (fun z hz => hRbd θ hθ z hz.1)
          (fun z hz => hRder θ hθ z hz.1) hA
  exact ⟨fun θ hθ τ₀ hτ₀ => (H θ hθ τ₀ hτ₀).1,
    fun θ hθ τ₀ hτ₀ => (H θ hθ τ₀ hτ₀).2.1,
    fun θ hθ τ₀ hτ₀ => (H θ hθ τ₀ hτ₀).2.2⟩

end Work.FTS_RegExport.RXR1
