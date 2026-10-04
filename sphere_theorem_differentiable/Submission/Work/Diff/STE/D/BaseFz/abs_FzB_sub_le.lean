import Mathlib
import Submission.Work.Diff.STE.D.Base.Defs
import Submission.Work.Diff.STE.D.Base.Jet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open Classical
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Work.Diff.STE.D.psi

namespace Work.Diff.STE.D.BaseFz

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

theorem abs_FzB_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (a₀ : Work.Diff.STE.Bil (I := I) (M := M))
    (ha₀ : Work.Diff.STE.D.ChartData (I := I) (M := M) a₀)
    (hs : Work.Diff.STE.D.IsSymm (I := I) a₀)
    (hball : ∃ δp : ℝ, 0 < δp ∧ ∀ c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ,
      ‖c‖ < δp → Work.Diff.STE.D.Base.IsPosF (I := I) (M := M) a₀ D ε c)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    ∃ (δ C : ℝ), 0 < δ ∧ 0 ≤ C ∧
      ∀ (c₀ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
        ‖c₀‖ < δ → Work.Diff.STE.D.Base.IsPosF (I := I) (M := M) a₀ D ε c₀ →
        ∀ (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
          ‖c - c₀‖ < δ → Work.Diff.STE.D.Base.IsPosF (I := I) (M := M) a₀ D ε c →
          ∀ y : Fin (Module.finrank ℝ E) → ℝ,
            |Work.Diff.STE.D.Base.FzB (I := I) (M := M) a₀ D ε z c y
              - Work.Diff.STE.D.Base.FzB (I := I) (M := M) a₀ D ε z c₀ y
              - ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
                  (c z' - c₀ z') *
                    Work.Diff.STE.D.Base.UfunB (I := I) (M := M) a₀ D ε z z' c₀ y|
              ≤ C * ‖c - c₀‖ ^ 2 := by
  classical
  obtain ⟨δp, hδp, hIsPos⟩ := hball
  obtain ⟨Bpref, hBpref0, hBpref⟩ := abs_pref_le (I := I) (M := M) D z.1
  obtain ⟨Ba, hBa0, hBa⟩ := Fz_coord_factor_le (I := I) (M := M) D z.1 z.2.1
  obtain ⟨Bb, hBb0, hBb⟩ := Fz_coord_factor_le (I := I) (M := M) D z.1 z.2.2.1
  have hn0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hPhi := Work.Diff.STE.D.Base.contDiffOn_PhiB (I := I) (M := M) hg a₀ ha₀ D ε (D.x₀ z.1)
  have hDom := Work.Diff.STE.D.Base.isOpen_DomB (I := I) (M := M) hg a₀ ha₀ D ε (D.x₀ z.1)
  have hK : IsCompact (Metric.closedBall (0 : FzCoef ι₀ (Module.finrank ℝ E) ε) (δp / 2) ×ˢ
      Metric.closedBall (0 : FzFlat (Module.finrank ℝ E)) (D.σ z.1)) :=
    (isCompact_closedBall (0 : FzCoef ι₀ (Module.finrank ℝ E) ε) (δp / 2)).prod
      (isCompact_closedBall (0 : FzFlat (Module.finrank ℝ E)) (D.σ z.1))
  have hKs : (Metric.closedBall (0 : FzCoef ι₀ (Module.finrank ℝ E) ε) (δp / 2) ×ˢ
      Metric.closedBall (0 : FzFlat (Module.finrank ℝ E)) (D.σ z.1))
      ⊆ Work.Diff.STE.D.Base.DomB (I := I) (M := M) a₀ D ε (D.x₀ z.1) := by
    rintro q hq
    obtain ⟨hq1, hq2⟩ := hq
    have hq1' : ‖q.1‖ ≤ δp / 2 := by
      rwa [Metric.mem_closedBall, dist_zero_right] at hq1
    have hq2' : ‖q.2‖ ≤ D.σ z.1 := by
      rwa [Metric.mem_closedBall, dist_zero_right] at hq2
    have htarget : flatToE (I := I) (D.x₀ z.1) q.2 ∈ (extChartAt I (D.x₀ z.1)).target :=
      D.htarget z.1 q.2 (by linarith [D.hσ z.1, hq2'])
    exact ⟨htarget, Work.Diff.STE.D.Base.jetPB_mem_pPhiDom (I := I) (M := M) hg D (D.x₀ z.1) a₀ hs q.1
      (hIsPos q.1 (by linarith)) htarget⟩
  obtain ⟨δt, Mt, hδt, hMt0, hMt⟩ :=
    Work.Diff.Calc.taylor_bound_on_compact (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1))
      (Work.Diff.STE.D.Base.DomB (I := I) (M := M) a₀ D ε (D.x₀ z.1))
      (Metric.closedBall (0 : FzCoef ι₀ (Module.finrank ℝ E) ε) (δp / 2) ×ˢ
        Metric.closedBall (0 : FzFlat (Module.finrank ℝ E)) (D.σ z.1))
      hDom hK hKs hPhi
  have hC0 : 0 ≤ Bpref * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * Mt :=
    mul_nonneg (mul_nonneg hBpref0
      (mul_nonneg (mul_nonneg (mul_nonneg hn0 hn0) hBa0) hBb0)) hMt0
  refine ⟨min (δp / 2) δt,
    Bpref * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * Mt,
    lt_min (by linarith) hδt, hC0, ?_⟩
  intro c₀ hc₀ hp₀ c hc hp y
  by_cases hψ : D.psi z.1 y = 0
  · -- the localised weight vanishes, so do all three terms
    have hFz : ∀ c' : FzCoef ι₀ (Module.finrank ℝ E) ε,
        Work.Diff.STE.D.Base.FzB (I := I) (M := M) a₀ D ε z c' y = 0 := by
      intro c'
      rw [Work.Diff.STE.D.Base.FzB, Work.Diff.STE.B3Data.R, hψ, zero_mul, zero_mul]
    have hU : (∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        (c z' - c₀ z') * Work.Diff.STE.D.Base.UfunB (I := I) (M := M) a₀ D ε z z' c₀ y) = 0 := by
      refine Finset.sum_eq_zero fun z' _ => ?_
      rw [Work.Diff.STE.D.Base.UfunB, hψ, zero_mul, zero_mul, mul_zero]
    rw [hFz c, hFz c₀, hU]
    simp only [sub_zero, abs_zero]
    exact mul_nonneg hC0 (sq_nonneg _)
  · -- the localised weight can be nonzero: the compact Taylor region applies
    have hyT : flatToE (I := I) (D.x₀ z.1) y ∈ (extChartAt I (D.x₀ z.1)).target :=
      Work.Diff.STE.B3.target_of_psi_ne_zero (I := I) (M := M) (D := D) hψ
    have hyσ : ‖y‖ ≤ D.σ z.1 :=
      le_of_lt (Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero (I := I) (M := M) (D := D) hψ)
    have hyK : y ∈ FzKreg (I := I) (M := M) D z.1 :=
      mem_FzKreg_of_psi_ne_zero (I := I) (M := M) D hψ
    have hc₀' : ‖c₀‖ ≤ δp / 2 := le_of_lt (lt_of_lt_of_le hc₀ (min_le_left _ _))
    have hxK : (c₀, y) ∈ Metric.closedBall (0 : FzCoef ι₀ (Module.finrank ℝ E) ε) (δp / 2) ×ˢ
        Metric.closedBall (0 : FzFlat (Module.finrank ℝ E)) (D.σ z.1) := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]; exact hc₀'
      · rw [Metric.mem_closedBall, dist_zero_right]; exact hyσ
    have hc' : ‖c - c₀‖ ≤ δt := le_of_lt (lt_of_lt_of_le hc (min_le_right _ _))
    have hstep : ‖Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1) (c, y)
        - Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1) (c₀, y)
        - (fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₀, y))
            (c - c₀, (0 : FzFlat (Module.finrank ℝ E)))‖ ≤ Mt * ‖c - c₀‖ ^ 2 := by
      have h := hMt (c₀, y) hxK (c - c₀, (0 : FzFlat (Module.finrank ℝ E))) (by
        rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
        exact hc')
      have hpt : (c₀, y) + (c - c₀, (0 : FzFlat (Module.finrank ℝ E))) = (c, y) := by
        rw [Prod.mk_add_mk, add_sub_cancel, add_zero]
      have hnorm : ‖(c - c₀, (0 : FzFlat (Module.finrank ℝ E)))‖ = ‖c - c₀‖ := by
        rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
      rw [hpt, hnorm] at h
      exact h
    have hdom₀ : Work.Diff.STE.D.Base.jetPB (I := I) (M := M) a₀ D ε (D.x₀ z.1) c₀
        (flatToE (I := I) (D.x₀ z.1) y) ∈ Work.Diff.STE.deTurck.pPhiDom (E := E) :=
      Work.Diff.STE.D.Base.jetPB_mem_pPhiDom (I := I) (M := M) hg D (D.x₀ z.1) a₀ hs c₀ hp₀ hyT
    -- the identification of the sum of `Ufun` with the derivative
    have hsum : (∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          (c z' - c₀ z') * Work.Diff.STE.D.Base.UfunB (I := I) (M := M) a₀ D ε z z' c₀ y)
        = (D.psi z.1 y * Real.sqrt (D.dens z.1 y)) *
            LamFun (I := I) (M := M) D ε z y
              ((fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₀, y))
                (c - c₀, (0 : FzFlat (Module.finrank ℝ E)))) := by
      have hper : ∀ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          Work.Diff.STE.D.Base.UfunB (I := I) (M := M) a₀ D ε z z' c₀ y
            = (D.psi z.1 y * Real.sqrt (D.dens z.1 y)) *
              LamFun (I := I) (M := M) D ε z y
                (Work.Diff.STE.D.pPhiFunD (E := E)
                  (Work.Diff.STE.D.Base.jetPB (I := I) (M := M) a₀ D ε (D.x₀ z.1) c₀
                    (flatToE (I := I) (D.x₀ z.1) y))
                  (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε (D.x₀ z.1) z'
                    (flatToE (I := I) (D.x₀ z.1) y))) :=
        fun z' => Work.Diff.STE.D.Base.UfunB_eq_LamFun (I := I) (M := M) a₀ D ε z z' c₀ y
      calc (∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
            (c z' - c₀ z') * Work.Diff.STE.D.Base.UfunB (I := I) (M := M) a₀ D ε z z' c₀ y)
          = ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
              (c z' - c₀ z') *
                ((D.psi z.1 y * Real.sqrt (D.dens z.1 y)) *
                  LamFun (I := I) (M := M) D ε z y
                    (Work.Diff.STE.D.pPhiFunD (E := E)
                      (Work.Diff.STE.D.Base.jetPB (I := I) (M := M) a₀ D ε (D.x₀ z.1) c₀
                        (flatToE (I := I) (D.x₀ z.1) y))
                      (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε (D.x₀ z.1) z'
                        (flatToE (I := I) (D.x₀ z.1) y)))) := by
            refine Finset.sum_congr rfl fun z' _ => ?_
            rw [hper z']
        _ = (D.psi z.1 y * Real.sqrt (D.dens z.1 y)) *
              (∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
                (c z' - c₀ z') *
                  LamFun (I := I) (M := M) D ε z y
                    (Work.Diff.STE.D.pPhiFunD (E := E)
                      (Work.Diff.STE.D.Base.jetPB (I := I) (M := M) a₀ D ε (D.x₀ z.1) c₀
                        (flatToE (I := I) (D.x₀ z.1) y))
                      (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε (D.x₀ z.1) z'
                        (flatToE (I := I) (D.x₀ z.1) y)))) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun z' _ => by ring
        _ = (D.psi z.1 y * Real.sqrt (D.dens z.1 y)) *
              LamFun (I := I) (M := M) D ε z y
                ((fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₀, y))
                  (c - c₀, (0 : FzFlat (Module.finrank ℝ E)))) := by
            congr 1
            rw [Work.Diff.STE.D.Base.Fz_fderiv_PhiB (I := I) (M := M) hg a₀ ha₀ D ε (D.x₀ z.1) c₀ hyT hdom₀ (c - c₀),
              FzJetLin_apply]
            rw [map_sum, map_sum]
            refine Finset.sum_congr rfl fun z' _ => ?_
            rw [map_smul, map_smul, smul_eq_mul, Pi.sub_apply]
    -- the localised component in the `PhiB` shape
    have hFzLam : ∀ c' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ,
        Work.Diff.STE.D.Base.FzB (I := I) (M := M) a₀ D ε z c' y
          = (D.psi z.1 y * Real.sqrt (D.dens z.1 y)) *
            LamFun (I := I) (M := M) D ε z y
              (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1) (c', y)) := by
      intro c'
      rw [Work.Diff.STE.D.Base.FzB_eq_LamFun (I := I) (M := M) a₀ D ε z c' hyT]
      rfl
    -- the identification of the left hand side
    have hLHS : Work.Diff.STE.D.Base.FzB (I := I) (M := M) a₀ D ε z c y
        - Work.Diff.STE.D.Base.FzB (I := I) (M := M) a₀ D ε z c₀ y
        - ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
            (c z' - c₀ z') * Work.Diff.STE.D.Base.UfunB (I := I) (M := M) a₀ D ε z z' c₀ y
        = (D.psi z.1 y * Real.sqrt (D.dens z.1 y)) *
            LamFun (I := I) (M := M) D ε z y
              (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1) (c, y)
                - Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1) (c₀, y)
                - (fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₀, y))
                    (c - c₀, (0 : FzFlat (Module.finrank ℝ E)))) := by
      rw [hFzLam c, hFzLam c₀, hsum, map_sub, map_sub]
      ring
    rw [hLHS, abs_mul]
    have hWtb := hBpref y
    have hLamb := abs_LamFun_le (I := I) (M := M) D ε z y hBa0 hBb0
      (fun j => hBa y hyK j) (fun k => hBb y hyK k)
      (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1) (c, y)
        - Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1) (c₀, y)
        - (fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₀, y))
            (c - c₀, (0 : FzFlat (Module.finrank ℝ E))))
    calc |D.psi z.1 y * Real.sqrt (D.dens z.1 y)|
          * |LamFun (I := I) (M := M) D ε z y
              (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1) (c, y)
                - Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1) (c₀, y)
                - (fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₀, y))
                    (c - c₀, (0 : FzFlat (Module.finrank ℝ E))))|
        ≤ Bpref * (((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb)
            * (Mt * ‖c - c₀‖ ^ 2)) :=
          mul_le_mul hWtb (le_trans hLamb (mul_le_mul_of_nonneg_left hstep
            (mul_nonneg (mul_nonneg (mul_nonneg hn0 hn0) hBa0) hBb0))) (abs_nonneg _) hBpref0
      _ = (Bpref * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * Mt)
            * ‖c - c₀‖ ^ 2 := by ring

end Work.Diff.STE.D.BaseFz
