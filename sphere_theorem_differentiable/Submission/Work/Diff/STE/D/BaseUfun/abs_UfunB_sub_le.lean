/-
# Layer D: Lipschitz bound for the base-generalised directional integrand `UfunB`

This module proves that the base-generalised directional integrand `UfunB a₀ D ε z z' c y` is
Lipschitz in the coefficient vector `c`, uniformly in `y`, on the positivity ball of the foreground
`fore a₀ D ε c = a₀ + genMap D ε c`.

The proof follows the shape of `Work.Diff.STE.D.psi.abs_Ufun_sub_le` (the case `a₀ = g₀.inner`):
`UfunB` is the weight `ψ · √dens` against the linearisation `pPhiFunD` of the chart DeTurck
operator, evaluated on the direction vector; the coefficient dependence enters only through the
joint chart DeTurck expression `PhiB`, whose second derivative is bounded on the compact set
`closedBall 0 (δp/2) ×ˢ Ky`.  A two-point mean value estimate for `fderiv (PhiB)` plus the
domination of the coefficient contractions then yields the bound.
-/
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

namespace Work.Diff.STE.D.BaseUfun

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 8000000
set_option linter.unusedSectionVars false

noncomputable section

/-- The coefficient space of the Galerkin scheme. -/
abbrev Coef (ι₀ : Type*) [Fintype ι₀] (n : ℕ) (ε : ℝ) : Type _ :=
  Work.Diff.STE.B3.JIdx ι₀ n ε → ℝ

/-- The flat coordinate space. -/
abbrev Flat (n : ℕ) : Type _ := Fin n → ℝ

theorem abs_UfunB_sub_le
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
    (z z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    ∃ (δ C : ℝ), 0 < δ ∧ 0 ≤ C ∧
      ∀ (c₀ c₁ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
        ‖c₀‖ < δ → ‖c₁‖ < δ →
        Work.Diff.STE.D.Base.IsPosF (I := I) (M := M) a₀ D ε c₀ →
        Work.Diff.STE.D.Base.IsPosF (I := I) (M := M) a₀ D ε c₁ →
        ∀ y : Fin (Module.finrank ℝ E) → ℝ,
          |Work.Diff.STE.D.Base.UfunB (I := I) (M := M) a₀ D ε z z' c₀ y
            - Work.Diff.STE.D.Base.UfunB (I := I) (M := M) a₀ D ε z z' c₁ y|
          ≤ C * ‖c₀ - c₁‖ := by
  classical
  obtain ⟨δp, hδp, hIsPos⟩ := hball
  obtain ⟨Bpref, hBpref0, hBpref⟩ :=
    Work.Diff.STE.D.psi.abs_pref_le (I := I) (M := M) D z.1
  obtain ⟨Ba, hBa0, hBa⟩ :=
    Work.Diff.STE.D.psi.abs_coord_factor_le (I := I) (M := M) D z.1 z.2.1
  obtain ⟨Bb, hBb0, hBb⟩ :=
    Work.Diff.STE.D.psi.abs_coord_factor_le (I := I) (M := M) D z.1 z.2.2.1
  have hn0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  -- smoothness of the joint expression and of its first derivative
  have hPhi := Work.Diff.STE.D.Base.contDiffOn_PhiB (I := I) (M := M) hg a₀ ha₀ D ε (D.x₀ z.1)
  have hDom_open := Work.Diff.STE.D.Base.isOpen_DomB (I := I) (M := M) hg a₀ ha₀ D ε (D.x₀ z.1)
  have hderiv1 : ContDiffOn ℝ 1
      (fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)))
      (Work.Diff.STE.D.Base.DomB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) :=
    hPhi.fderiv_of_isOpen hDom_open (by norm_num)
  have hderiv2 : ContDiffOn ℝ 0
      (fderiv ℝ (fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1))))
      (Work.Diff.STE.D.Base.DomB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) :=
    hderiv1.fderiv_of_isOpen hDom_open (m := 0) (by simp)
  -- the compact set on which the second derivative is bounded
  have h0Ky : (0 : Flat (Module.finrank ℝ E))
      ∈ Work.Diff.STE.D.psi.Ky (I := I) (M := M) D z.1 := by
    refine ⟨?_, subset_closure ?_⟩
    · rw [Metric.mem_closedBall, dist_self]
      exact le_of_lt (D.hσ z.1)
    · rw [Function.mem_support, D.hχ1 z.1 (0 : Flat (Module.finrank ℝ E))
        (by simpa using le_of_lt (D.hσ z.1))]
      exact one_ne_zero
  have hKX : IsCompact (Metric.closedBall (0 : Coef ι₀ (Module.finrank ℝ E) ε) (δp / 2) ×ˢ
      Work.Diff.STE.D.psi.Ky (I := I) (M := M) D z.1) := by
    have h1 : IsCompact (Metric.closedBall (0 : Coef ι₀ (Module.finrank ℝ E) ε) (δp / 2)) :=
      isCompact_closedBall _ _
    exact h1.prod (Work.Diff.STE.D.psi.isCompact_Ky (I := I) (M := M) D z.1)
  have hKXs : ∀ q ∈ Metric.closedBall (0 : Coef ι₀ (Module.finrank ℝ E) ε) (δp / 2) ×ˢ
      Work.Diff.STE.D.psi.Ky (I := I) (M := M) D z.1,
      q ∈ Work.Diff.STE.D.Base.DomB (I := I) (M := M) a₀ D ε (D.x₀ z.1) := by
    rintro q hq
    obtain ⟨hq1, hq2⟩ := hq
    have hq1' : ‖q.1‖ ≤ δp / 2 := by
      rwa [Metric.mem_closedBall, dist_zero_right] at hq1
    have hq2' : Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) q.2
        ∈ (extChartAt I (D.x₀ z.1)).target :=
      Work.Diff.STE.D.psi.flatToE_mem_target_of_mem_Ky (I := I) (M := M) D hq2
    exact ⟨hq2', Work.Diff.STE.D.Base.jetPB_mem_pPhiDom (I := I) (M := M) hg D (D.x₀ z.1) a₀ hs
      q.1 (hIsPos q.1 (by linarith)) hq2'⟩
  obtain ⟨B₂, hB₂⟩ := hKX.exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1))))
    (hderiv2.continuousOn.mono hKXs)
  have hB₂0 : 0 ≤ B₂ := le_trans (norm_nonneg _)
    (hB₂ (0, 0) ⟨by rw [Metric.mem_closedBall, dist_zero_right, norm_zero]; linarith, h0Ky⟩)
  have hC0 : 0 ≤ Bpref * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * B₂ :=
    mul_nonneg (mul_nonneg hBpref0
      (mul_nonneg (mul_nonneg (mul_nonneg hn0 hn0) hBa0) hBb0)) hB₂0
  refine ⟨δp / 2,
    Bpref * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * B₂,
    by linarith, hC0, ?_⟩
  intro c₀ c₁ hc₀ hc₁ hp₀ hp₁ y
  by_cases hy : y ∈ Work.Diff.STE.D.psi.Ky (I := I) (M := M) D z.1
  · -- the case where the localised weight can be nonzero
    have hy' : Work.Diff.STE.flatToE (I := I) (D.x₀ z.1) y
        ∈ (extChartAt I (D.x₀ z.1)).target :=
      Work.Diff.STE.D.psi.flatToE_mem_target_of_mem_Ky (I := I) (M := M) D hy
    have hc₀le : ‖c₀‖ ≤ δp / 2 := le_of_lt hc₀
    have hc₁le : ‖c₁‖ ≤ δp / 2 := le_of_lt hc₁
    have hmem₀ : (c₀, y) ∈ Work.Diff.STE.D.Base.DomB (I := I) (M := M) a₀ D ε (D.x₀ z.1) :=
      hKXs _ ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hc₀le, hy⟩
    have hmem₁ : (c₁, y) ∈ Work.Diff.STE.D.Base.DomB (I := I) (M := M) a₀ D ε (D.x₀ z.1) :=
      hKXs _ ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hc₁le, hy⟩
    -- the two-point mean value estimate for the derivative
    have hMVT : ‖fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₀, y)
        - fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₁, y)‖
        ≤ B₂ * ‖c₀ - c₁‖ := by
      have hsegKX : segment ℝ (c₁, y) (c₀, y)
          ⊆ Metric.closedBall (0 : Coef ι₀ (Module.finrank ℝ E) ε) (δp / 2) ×ˢ
              Work.Diff.STE.D.psi.Ky (I := I) (M := M) D z.1 := by
        intro q hq
        obtain ⟨a, b, ha, hb, hab, hz⟩ := hq
        rw [← hz]
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_closedBall, dist_zero_right]
          have hfst : (a • (c₁, y) + b • (c₀, y)).1 = a • c₁ + b • c₀ := by
            simp only [Prod.smul_mk, Prod.mk_add_mk]
          rw [hfst]
          calc ‖a • c₁ + b • c₀‖ ≤ ‖a • c₁‖ + ‖b • c₀‖ := norm_add_le _ _
            _ = a * ‖c₁‖ + b * ‖c₀‖ := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_of_nonneg ha, abs_of_nonneg hb]
            _ ≤ a * (δp / 2) + b * (δp / 2) :=
                add_le_add (mul_le_mul_of_nonneg_left hc₁le ha)
                  (mul_le_mul_of_nonneg_left hc₀le hb)
            _ = δp / 2 := by rw [← add_mul, hab, one_mul]
        · have hsnd : (a • (c₁, y) + b • (c₀, y)).2 = y := by
            simp only [Prod.smul_mk, Prod.mk_add_mk]
            rw [← add_smul, hab, one_smul]
          rw [hsnd]
          exact hy
      have hseg : segment ℝ (c₁, y) (c₀, y)
          ⊆ Work.Diff.STE.D.Base.DomB (I := I) (M := M) a₀ D ε (D.x₀ z.1) :=
        fun q hq => hKXs q (hsegKX hq)
      have hbound : ∀ v ∈ segment ℝ (c₁, y) (c₀, y),
          ‖fderiv ℝ (fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε
            (D.x₀ z.1))) v‖ ≤ B₂ :=
        fun v hv => hB₂ v (hsegKX hv)
      have hdiff : ∀ v ∈ segment ℝ (c₁, y) (c₀, y),
          HasFDerivWithinAt
            (fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)))
            (fderiv ℝ (fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε
              (D.x₀ z.1))) v)
            (segment ℝ (c₁, y) (c₀, y)) v := by
        intro v hv
        have hvD : v ∈ Work.Diff.STE.D.Base.DomB (I := I) (M := M) a₀ D ε (D.x₀ z.1) := hseg hv
        exact (((hderiv1.differentiableOn (by simp)).differentiableAt
          (hDom_open.mem_nhds hvD)).hasFDerivAt).hasFDerivWithinAt
      have hmain := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hdiff hbound
        (convex_segment (c₁, y) (c₀, y))
        (left_mem_segment ℝ (c₁, y) (c₀, y)) (right_mem_segment ℝ (c₁, y) (c₀, y))
      have hsub : (c₀, y) - (c₁, y) = (c₀ - c₁, (0 : Flat (Module.finrank ℝ E))) :=
        Prod.ext rfl (by simp)
      rw [hsub, Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)] at hmain
      exact hmain
    -- the bound on the coefficients of the jet matrix
    have hentry : ∀ X : Work.Diff.EXT.MatE (E := E),
        |∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
              (D.e z.1 z.2.1 (D.pt z.1 y))
            * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
              (D.e z.1 z.2.2.1 (D.pt z.1 y))
            * X j k|
        ≤ ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * ‖X‖ := by
      intro X
      calc |∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
                (D.e z.1 z.2.1 (D.pt z.1 y))
              * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
                (D.e z.1 z.2.2.1 (D.pt z.1 y))
              * X j k|
          ≤ ∑ j : Fin (Module.finrank ℝ E), |∑ k : Fin (Module.finrank ℝ E),
              Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
                  (D.e z.1 z.2.1 (D.pt z.1 y))
                * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
                  (D.e z.1 z.2.2.1 (D.pt z.1 y))
                * X j k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
                  (D.e z.1 z.2.1 (D.pt z.1 y))
                * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
                  (D.e z.1 z.2.2.1 (D.pt z.1 y))
                * X j k| :=
            Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin (Module.finrank ℝ E), ∑ _k : Fin (Module.finrank ℝ E),
              Ba * Bb * ‖X‖ := by
            refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
            rw [abs_mul, abs_mul]
            exact mul_le_mul (mul_le_mul (hBa y hy j) (hBb y hy k) (abs_nonneg _) hBa0)
              (le_trans (norm_le_pi_norm (X j) k) (norm_le_pi_norm X j)) (abs_nonneg _)
              (mul_nonneg hBa0 hBb0)
        _ = ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * ‖X‖ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    -- the bound on the derivative of the joint expression
    have hX : ‖((fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₀, y))
        - (fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₁, y)))
        ((Pi.single z' (1 : ℝ) : Coef ι₀ (Module.finrank ℝ E) ε), (0 : Flat (Module.finrank ℝ E)))‖ ≤ B₂ * ‖c₀ - c₁‖ := by
      have he' : ‖(Pi.single z' (1 : ℝ) : Coef ι₀ (Module.finrank ℝ E) ε)‖ ≤ 1 := by
        rw [pi_norm_le_iff_of_nonneg zero_le_one]
        intro j
        by_cases hj : j = z'
        · rw [hj, Pi.single_eq_same]
          norm_num
        · rw [Pi.single_eq_of_ne hj]
          simp
      have hε0 : (0 : ℝ) ≤ B₂ * ‖c₀ - c₁‖ := mul_nonneg hB₂0 (norm_nonneg _)
      calc ‖((fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₀, y))
            - (fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₁, y)))
            ((Pi.single z' (1 : ℝ) : Coef ι₀ (Module.finrank ℝ E) ε), (0 : Flat (Module.finrank ℝ E)))‖
          ≤ ‖(fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₀, y))
              - (fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₁, y))‖
            * ‖((Pi.single z' (1 : ℝ) : Coef ι₀ (Module.finrank ℝ E) ε), (0 : Flat (Module.finrank ℝ E)))‖ :=
              (fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₀, y)
                - fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₁, y)).le_opNorm
                  ((Pi.single z' (1 : ℝ) : Coef ι₀ (Module.finrank ℝ E) ε),
                    (0 : Flat (Module.finrank ℝ E)))
        _ ≤ (B₂ * ‖c₀ - c₁‖) * 1 := by
            refine mul_le_mul hMVT ?_
              (norm_nonneg ((Pi.single z' (1 : ℝ) : Coef ι₀ (Module.finrank ℝ E) ε),
                (0 : Flat (Module.finrank ℝ E)))) hε0
            have hnorm : ‖((Pi.single z' (1 : ℝ) : Coef ι₀ (Module.finrank ℝ E) ε),
                  (0 : Flat (Module.finrank ℝ E)))‖
                = ‖(Pi.single z' (1 : ℝ) : Coef ι₀ (Module.finrank ℝ E) ε)‖ := by
              rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
            rw [hnorm]
            exact he'
        _ = B₂ * ‖c₀ - c₁‖ := by ring
    -- the representation of `UfunB` through the derivative
    have hU₀ := Work.Diff.STE.D.Base.UfunB_eq_fderiv (I := I) (M := M) hg a₀ ha₀ hs
      D ε z z' c₀ (y := y) hy' hp₀
    have hU₁ := Work.Diff.STE.D.Base.UfunB_eq_fderiv (I := I) (M := M) hg a₀ ha₀ hs
      D ε z z' c₁ (y := y) hy' hp₁
    -- the difference of the two coefficient sums
    have hKey :
        (∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
                (D.e z.1 z.2.1 (D.pt z.1 y))
              * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
                (D.e z.1 z.2.2.1 (D.pt z.1 y))
              * ((fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₀, y))
                  ((Pi.single z' (1 : ℝ) : Coef ι₀ (Module.finrank ℝ E) ε),
                    (0 : Flat (Module.finrank ℝ E)))) j k)
          - (∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
                (D.e z.1 z.2.1 (D.pt z.1 y))
              * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
                (D.e z.1 z.2.2.1 (D.pt z.1 y))
              * ((fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₁, y))
                  ((Pi.single z' (1 : ℝ) : Coef ι₀ (Module.finrank ℝ E) ε),
                    (0 : Flat (Module.finrank ℝ E)))) j k)
          = ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
                (D.e z.1 z.2.1 (D.pt z.1 y))
              * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
                (D.e z.1 z.2.2.1 (D.pt z.1 y))
              * (((fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₀, y))
                    - (fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₁, y)))
                  ((Pi.single z' (1 : ℝ) : Coef ι₀ (Module.finrank ℝ E) ε),
                    (0 : Flat (Module.finrank ℝ E)))) j k := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [sub_apply, Pi.sub_apply]
      ring_nf
    have hfin : |Work.Diff.STE.D.Base.UfunB (I := I) (M := M) a₀ D ε z z' c₀ y
        - Work.Diff.STE.D.Base.UfunB (I := I) (M := M) a₀ D ε z z' c₁ y|
        ≤ Bpref * (((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb)
            * (B₂ * ‖c₀ - c₁‖)) := by
      rw [hU₀, hU₁, ← mul_sub, abs_mul]
      refine mul_le_mul (hBpref y) ?_ (abs_nonneg _) hBpref0
      rw [hKey]
      calc |∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) j
                (D.e z.1 z.2.1 (D.pt z.1 y))
              * Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ z.1) (D.pt z.1 y) k
                (D.e z.1 z.2.2.1 (D.pt z.1 y))
              * (((fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₀, y))
                    - (fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₁, y)))
                  ((Pi.single z' (1 : ℝ) : Coef ι₀ (Module.finrank ℝ E) ε),
                    (0 : Flat (Module.finrank ℝ E)))) j k|
          ≤ ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb)
              * ‖((fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₀, y))
                    - (fderiv ℝ (Work.Diff.STE.D.Base.PhiB (I := I) (M := M) a₀ D ε (D.x₀ z.1)) (c₁, y)))
                  ((Pi.single z' (1 : ℝ) : Coef ι₀ (Module.finrank ℝ E) ε),
                    (0 : Flat (Module.finrank ℝ E)))‖ := hentry _
        _ ≤ ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb)
              * (B₂ * ‖c₀ - c₁‖) :=
            mul_le_mul_of_nonneg_left hX (mul_nonneg (mul_nonneg (mul_nonneg hn0 hn0) hBa0) hBb0)
    calc |Work.Diff.STE.D.Base.UfunB (I := I) (M := M) a₀ D ε z z' c₀ y
          - Work.Diff.STE.D.Base.UfunB (I := I) (M := M) a₀ D ε z z' c₁ y|
        ≤ Bpref * (((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb)
            * (B₂ * ‖c₀ - c₁‖)) := hfin
      _ = (Bpref * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * Ba * Bb) * B₂)
            * ‖c₀ - c₁‖ := by ring
  · -- the case where the localised weight vanishes
    have hψ : Work.Diff.STE.B3Data.psi (I := I) (M := M) D z.1 y = 0 := by
      by_contra hne
      exact hy (Work.Diff.STE.D.psi.mem_Ky_of_psi_ne_zero (I := I) (M := M) D hne)
    have h0 : ∀ c : Coef ι₀ (Module.finrank ℝ E) ε,
        Work.Diff.STE.D.Base.UfunB (I := I) (M := M) a₀ D ε z z' c y = 0 := by
      intro c
      rw [Work.Diff.STE.D.Base.UfunB, hψ, zero_mul, zero_mul]
    rw [h0 c₀, h0 c₁, sub_zero, abs_zero]
    exact mul_nonneg hC0 (norm_nonneg _)

end

end Work.Diff.STE.D.BaseUfun
