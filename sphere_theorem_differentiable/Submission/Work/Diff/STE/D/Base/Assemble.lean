/-
# Layer D: assembly of `ContDiffAt ℝ 1 (psiConcB a₀) 0`

This module assembles the base-generalised smoothness of the concrete Galerkin vector field
`psiConcB a₀`: it is `C¹` at `0` as soon as the foreground `a₀ + genMap D ε c` is positive definite
on a neighbourhood of `0` in the coefficient space (`hball`).

The two ingredients are the second-order Taylor estimate for the localised component
(`Work.Diff.STE.D.BaseFz.abs_FzB_sub_le`) and the Lipschitz estimate for the directional integrand
(`Work.Diff.STE.D.BaseUfun.abs_UfunB_sub_le`), together with the continuity of the two localised
pieces (`Work.Diff.STE.D.BaseCont.continuous_FzB`, `continuous_UfunB`) which makes the Fourier
coefficient `scoeff` additive on the difference.
-/
import Mathlib
import Submission.Work.Diff.STE.D.Base.Defs
import Submission.Work.Diff.STE.D.Base.Jet
import Submission.Work.Diff.STE.D.BaseFz.abs_FzB_sub_le
import Submission.Work.Diff.STE.D.BaseUfun.abs_UfunB_sub_le
import Submission.Work.Diff.STE.D.BaseCont.continuous_FzB
import Submission.Work.Diff.STE.D.BaseCont.continuous_UfunB
import Submission.Work.Diff.STE.B3.abs_scoeff_le
import Submission.Work.Diff.STE.B3.scoeff_add_of_support
import Submission.Work.Diff.STE.B3.scoeff_smul_of_support
import Submission.Work.Diff.STE.B3.scoeff_finset_sum_smul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open Classical
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.D.Base

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M} {ε : ℝ}

noncomputable section

abbrev CoefB (ι₀ : Type*) [Fintype ι₀] (n : ℕ) (ε : ℝ) : Type _ :=
  Work.Diff.STE.B3.JIdx ι₀ n ε → ℝ

abbrev FlatB (n : ℕ) : Type _ := Fin n → ℝ

/-! ## 1. The linearised perturbation, the remainder and the candidate derivative -/

/-- The linearised perturbation of the localised component along `c - c₀`. -/
noncomputable def psiLinB (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c₀ c : CoefB ι₀ (Module.finrank ℝ E) ε) :
    FlatB (Module.finrank ℝ E) → ℝ :=
  fun y => ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
    (c z' - c₀ z') * UfunB (I := I) (M := M) a₀ D ε z z' c₀ y

/-- The second order Taylor remainder of the localised component. -/
noncomputable def psiRemB (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c₀ c : CoefB ι₀ (Module.finrank ℝ E) ε) :
    FlatB (Module.finrank ℝ E) → ℝ :=
  fun y => FzB (I := I) (M := M) a₀ D ε z c y - FzB (I := I) (M := M) a₀ D ε z c₀ y
    - ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        (c z' - c₀ z') * UfunB (I := I) (M := M) a₀ D ε z z' c₀ y

@[simp] lemma psiLinB_apply (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c₀ c : CoefB ι₀ (Module.finrank ℝ E) ε) (y : FlatB (Module.finrank ℝ E)) :
    psiLinB (I := I) (M := M) a₀ D ε z c₀ c y =
      ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        (c z' - c₀ z') * UfunB (I := I) (M := M) a₀ D ε z z' c₀ y := rfl

@[simp] lemma psiRemB_apply (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c₀ c : CoefB ι₀ (Module.finrank ℝ E) ε) (y : FlatB (Module.finrank ℝ E)) :
    psiRemB (I := I) (M := M) a₀ D ε z c₀ c y =
      FzB (I := I) (M := M) a₀ D ε z c y - FzB (I := I) (M := M) a₀ D ε z c₀ y
        - ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
            (c z' - c₀ z') * UfunB (I := I) (M := M) a₀ D ε z z' c₀ y := rfl

/-- **The candidate derivative of the `z`-th coefficient of `psiConcB`.** -/
noncomputable def psiConcDerivB (a₀ : Bil (I := I) (M := M))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (c₀ : CoefB ι₀ (Module.finrank ℝ E) ε) :
    CoefB ι₀ (Module.finrank ℝ E) ε →L[ℝ] ℝ :=
  ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
    (ContinuousLinearMap.proj z').smulRight
      ((1 / 2 : ℝ) * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
        (UfunB (I := I) (M := M) a₀ D ε z z' c₀) z.2.2.2)

/-! ## 2. Step 1: differentiability of the coefficients -/

theorem hasFDerivAt_psiConcB_z (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (hg : ChartData (I := I) (M := M) g₀.inner)
    (a₀ : Bil (I := I) (M := M))
    (ha₀ : ChartData (I := I) (M := M) a₀)
    (hs : IsSymm (I := I) a₀)
    (hball : ∃ δp : ℝ, 0 < δp ∧ ∀ c : CoefB ι₀ (Module.finrank ℝ E) ε,
      ‖c‖ < δp → IsPosF (I := I) (M := M) a₀ D ε c)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c₀ : CoefB ι₀ (Module.finrank ℝ E) ε,
      ‖c₀‖ < δ →
      HasFDerivAt (fun c => psiConcB (I := I) (M := M) a₀ D ρ ε c z)
        (psiConcDerivB (I := I) (M := M) a₀ D ρ ε z c₀) c₀ := by
  classical
  obtain ⟨δ₂, C₂, hδ₂, hC₂, hTay⟩ :=
    Work.Diff.STE.D.BaseFz.abs_FzB_sub_le (I := I) (M := M) D ε hg a₀ ha₀ hs hball z
  obtain ⟨δ₀, hδ₀, hpos⟩ := hball
  refine ⟨min δ₂ δ₀, lt_min hδ₂ hδ₀, fun c₀ hc₀ => ?_⟩
  have hc₀₂ : ‖c₀‖ < δ₂ := lt_of_lt_of_le hc₀ (min_le_left _ _)
  have hc₀₀ : ‖c₀‖ < δ₀ := lt_of_lt_of_le hc₀ (min_le_right _ _)
  have hp₀ : IsPosF (I := I) (M := M) a₀ D ε c₀ := hpos c₀ hc₀₀
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro ε' hε'
  set P : ℝ := |ρ (ε • fun i => ((z.2.2.2.1.1 i : ℤ) : ℝ))| with hP
  have hPnn : 0 ≤ P := by rw [hP]; exact abs_nonneg _
  have hPC : 0 < P * C₂ + 1 := by nlinarith [hPnn, hC₂]
  set δ : ℝ := min (min (δ₂ - ‖c₀‖) (δ₀ - ‖c₀‖)) (2 * ε' / (P * C₂ + 1)) with hδ
  have hδle : δ ≤ 2 * ε' / (P * C₂ + 1) := by rw [hδ]; exact min_le_right _ _
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min (lt_min (sub_pos.mpr hc₀₂) (sub_pos.mpr hc₀₀))
      (div_pos (by linarith) hPC)
  refine Filter.mem_of_superset
    (Metric.ball_mem_nhds (0 : CoefB ι₀ (Module.finrank ℝ E) ε) hδpos)
    (fun d hd => ?_)
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hd
  have hd₁ : ‖d‖ < δ₂ - ‖c₀‖ :=
    lt_of_lt_of_le hd (le_trans (min_le_left _ _) (min_le_left _ _))
  have hd₂ : ‖d‖ < δ₀ - ‖c₀‖ :=
    lt_of_lt_of_le hd (le_trans (min_le_left _ _) (min_le_right _ _))
  set c : CoefB ι₀ (Module.finrank ℝ E) ε := c₀ + d with hc
  have hsub : c - c₀ = d := by rw [hc]; simp
  have hcd : ‖c - c₀‖ = ‖d‖ := by rw [hsub]
  have hcn : ‖c‖ < δ₀ := by
    rw [hc]
    calc ‖c₀ + d‖ ≤ ‖c₀‖ + ‖d‖ := norm_add_le _ _
      _ < δ₀ := by linarith
  have hpc : IsPosF (I := I) (M := M) a₀ D ε c := hpos c hcn
  have hc₂ : ‖c - c₀‖ < δ₂ := by
    rw [hcd]
    exact lt_of_lt_of_le hd₁ (by linarith [norm_nonneg c₀])
  have hR : ∀ y : FlatB (Module.finrank ℝ E),
      |psiRemB (I := I) (M := M) a₀ D ε z c₀ c y| ≤ C₂ * ‖c - c₀‖ ^ 2 := by
    intro y
    simp only [psiRemB_apply]
    exact hTay c₀ hc₀₂ hp₀ c hc₂ hpc y
  have hcont_c : Continuous (FzB (I := I) (M := M) a₀ D ε z c) :=
    Work.Diff.STE.D.BaseCont.continuous_FzB (I := I) (M := M) D ε hg a₀ ha₀ hs z c hpc
  have hcont_c₀ : Continuous (FzB (I := I) (M := M) a₀ D ε z c₀) :=
    Work.Diff.STE.D.BaseCont.continuous_FzB (I := I) (M := M) D ε hg a₀ ha₀ hs z c₀ hp₀
  have hcont_Slam : Continuous (fun y : FlatB (Module.finrank ℝ E) =>
      ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        (c z' - c₀ z') * UfunB (I := I) (M := M) a₀ D ε z z' c₀ y) := by
    refine continuous_finsetSum Finset.univ (fun z' _ => ?_)
    exact continuous_const.mul
      (Work.Diff.STE.D.BaseCont.continuous_UfunB (I := I) (M := M) D ε hg a₀ ha₀ hs z z' c₀ hp₀)
  have hcont_S : Continuous (psiLinB (I := I) (M := M) a₀ D ε z c₀ c) := by
    rw [show psiLinB (I := I) (M := M) a₀ D ε z c₀ c = fun y =>
        ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          (c z' - c₀ z') * UfunB (I := I) (M := M) a₀ D ε z z' c₀ y from rfl]
    exact hcont_Slam
  have hcont_R : Continuous (psiRemB (I := I) (M := M) a₀ D ε z c₀ c) := by
    rw [show psiRemB (I := I) (M := M) a₀ D ε z c₀ c = fun y =>
        FzB (I := I) (M := M) a₀ D ε z c y - FzB (I := I) (M := M) a₀ D ε z c₀ y
          - ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
              (c z' - c₀ z') * UfunB (I := I) (M := M) a₀ D ε z z' c₀ y from rfl]
    exact (hcont_c.sub hcont_c₀).sub hcont_Slam
  have hsupp_c : Function.support (FzB (I := I) (M := M) a₀ D ε z c) ⊆
      halfCube (Module.finrank ℝ E) := support_FzB_subset (I := I) (M := M) a₀ D ε z c
  have hsupp_c₀ : Function.support (FzB (I := I) (M := M) a₀ D ε z c₀) ⊆
      halfCube (Module.finrank ℝ E) := support_FzB_subset (I := I) (M := M) a₀ D ε z c₀
  have hsupp_Slam : Function.support (fun y : FlatB (Module.finrank ℝ E) =>
      ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        (c z' - c₀ z') * UfunB (I := I) (M := M) a₀ D ε z z' c₀ y)
      ⊆ halfCube (Module.finrank ℝ E) := by
    refine support_finset_sum_subset Finset.univ _ (fun z' _ => ?_)
    refine subset_trans ?_ (support_UfunB_subset (I := I) (M := M) a₀ D ε z z' c₀)
    intro y hy h0
    exact hy (by simp only [h0, mul_zero])
  have hsupp_S : Function.support (psiLinB (I := I) (M := M) a₀ D ε z c₀ c) ⊆
      halfCube (Module.finrank ℝ E) := by
    rw [show psiLinB (I := I) (M := M) a₀ D ε z c₀ c = fun y =>
        ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          (c z' - c₀ z') * UfunB (I := I) (M := M) a₀ D ε z z' c₀ y from rfl]
    exact hsupp_Slam
  have hsupp_R : Function.support (psiRemB (I := I) (M := M) a₀ D ε z c₀ c) ⊆
      halfCube (Module.finrank ℝ E) := by
    rw [show psiRemB (I := I) (M := M) a₀ D ε z c₀ c = fun y =>
        FzB (I := I) (M := M) a₀ D ε z c y - FzB (I := I) (M := M) a₀ D ε z c₀ y
          - ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
              (c z' - c₀ z') * UfunB (I := I) (M := M) a₀ D ε z z' c₀ y from rfl]
    exact support_sub_subset hsupp_c hsupp_c₀ hsupp_Slam
  have hFz_add : FzB (I := I) (M := M) a₀ D ε z c
      = FzB (I := I) (M := M) a₀ D ε z c₀
        + (psiLinB (I := I) (M := M) a₀ D ε z c₀ c
          + psiRemB (I := I) (M := M) a₀ D ε z c₀ c) := by
    funext y
    simp only [psiLinB_apply, psiRemB_apply, Pi.add_apply]
    ring
  have hS : Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
        (psiLinB (I := I) (M := M) a₀ D ε z c₀ c) z.2.2.2
      = ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          (c z' - c₀ z') * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (UfunB (I := I) (M := M) a₀ D ε z z' c₀) z.2.2.2 := by
    have heq : psiLinB (I := I) (M := M) a₀ D ε z c₀ c
        = ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
            (c z' - c₀ z') • UfunB (I := I) (M := M) a₀ D ε z z' c₀ := by
      funext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, psiLinB_apply]
    rw [heq]
    exact Work.Diff.STE.B3.scoeff_finset_sum_smul Finset.univ ρ ε z.2.2.2
      (fun z' => c z' - c₀ z') (fun z' => UfunB (I := I) (M := M) a₀ D ε z z' c₀)
      (fun z' _ => Work.Diff.STE.D.BaseCont.continuous_UfunB (I := I) (M := M) D ε hg a₀ ha₀ hs
        z z' c₀ hp₀)
      (fun z' _ => support_UfunB_subset (I := I) (M := M) a₀ D ε z z' c₀)
  have hA : Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
        (FzB (I := I) (M := M) a₀ D ε z c) z.2.2.2
      = Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
          (FzB (I := I) (M := M) a₀ D ε z c₀) z.2.2.2
        + Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (psiLinB (I := I) (M := M) a₀ D ε z c₀ c) z.2.2.2
        + Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (psiRemB (I := I) (M := M) a₀ D ε z c₀ c) z.2.2.2 := by
    have h1 := Work.Diff.STE.B3.scoeff_add_of_support ρ ε
      (FzB (I := I) (M := M) a₀ D ε z c₀)
      (psiLinB (I := I) (M := M) a₀ D ε z c₀ c
        + psiRemB (I := I) (M := M) a₀ D ε z c₀ c)
      hcont_c₀ (hcont_S.add hcont_R) hsupp_c₀ (support_add_subset hsupp_S hsupp_R) z.2.2.2
    have h2 := Work.Diff.STE.B3.scoeff_add_of_support ρ ε
      (psiLinB (I := I) (M := M) a₀ D ε z c₀ c)
      (psiRemB (I := I) (M := M) a₀ D ε z c₀ c)
      hcont_S hcont_R hsupp_S hsupp_R z.2.2.2
    rw [hFz_add, h1, h2]
    ring
  have hderiv : psiConcDerivB (I := I) (M := M) a₀ D ρ ε z c₀ (c - c₀)
      = (1 / 2 : ℝ) * ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          (c z' - c₀ z') * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (UfunB (I := I) (M := M) a₀ D ε z z' c₀) z.2.2.2 := by
    simp only [psiConcDerivB, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, Pi.sub_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z' _ => ?_)
    ring
  have hjFC : ∀ c : CoefB ι₀ (Module.finrank ℝ E) ε,
      Work.Diff.STE.B3.jFamilyCoeff D ρ ε
        (secChart (I := I) (M := M) g₀ (fore (I := I) (M := M) a₀ D ε c) (D.x₀ z.1)) z
      = Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
          (FzB (I := I) (M := M) a₀ D ε z c) z.2.2.2 := fun c => rfl
  have hbody : psiConcB (I := I) (M := M) a₀ D ρ ε c z
        - psiConcB (I := I) (M := M) a₀ D ρ ε c₀ z
        - psiConcDerivB (I := I) (M := M) a₀ D ρ ε z c₀ (c - c₀)
      = (1 / 2 : ℝ) * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
          (psiRemB (I := I) (M := M) a₀ D ε z c₀ c) z.2.2.2 := by
    rw [psiConcB_apply, psiConcB_apply, hjFC c, hjFC c₀, hA, hS, hderiv]
    ring
  have hSD : |Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
      (psiRemB (I := I) (M := M) a₀ D ε z c₀ c) z.2.2.2| ≤ P * (C₂ * ‖c - c₀‖ ^ 2) := by
    rw [hP]
    exact Work.Diff.STE.B3.abs_scoeff_le ρ ε (psiRemB (I := I) (M := M) a₀ D ε z c₀ c)
      hcont_R hsupp_R z.2.2.2 (C₂ * ‖c - c₀‖ ^ 2) (mul_nonneg hC₂ (sq_nonneg _)) hR
  have hfac : 0 ≤ (1 / 2 : ℝ) * P * C₂ := mul_nonneg (mul_nonneg (by norm_num) hPnn) hC₂
  have hε'' : (1 / 2 : ℝ) * P * C₂ * δ ≤ ε' := by
    have h1 : (1 / 2 : ℝ) * P * C₂ * δ ≤
        (1 / 2 : ℝ) * P * C₂ * (2 * ε' / (P * C₂ + 1)) :=
      mul_le_mul_of_nonneg_left hδle hfac
    have h2 : (1 / 2 : ℝ) * P * C₂ * (2 * ε' / (P * C₂ + 1))
        = (P * C₂) * ε' / (P * C₂ + 1) := by ring
    have h3 : (P * C₂) * ε' / (P * C₂ + 1) ≤ ε' := by
      rw [div_le_iff₀ hPC]
      nlinarith [hPnn, hC₂, hε'.le, mul_nonneg hPnn hC₂]
    linarith [h1, h2, h3]
  have hgoal : psiConcB (I := I) (M := M) a₀ D ρ ε c z
        - psiConcB (I := I) (M := M) a₀ D ρ ε c₀ z
        - psiConcDerivB (I := I) (M := M) a₀ D ρ ε z c₀ d
      = (1 / 2 : ℝ) * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
          (psiRemB (I := I) (M := M) a₀ D ε z c₀ c) z.2.2.2 := by
    rw [← hsub]
    exact hbody
  change ‖psiConcB (I := I) (M := M) a₀ D ρ ε c z
      - psiConcB (I := I) (M := M) a₀ D ρ ε c₀ z
      - psiConcDerivB (I := I) (M := M) a₀ D ρ ε z c₀ d‖ ≤ ε' * ‖d‖
  rw [hgoal, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2)), Real.norm_eq_abs]
  calc (1 / 2 : ℝ) * |Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
        (psiRemB (I := I) (M := M) a₀ D ε z c₀ c) z.2.2.2|
      ≤ (1 / 2 : ℝ) * (P * (C₂ * ‖c - c₀‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hSD (by norm_num)
    _ = (1 / 2 : ℝ) * P * C₂ * ‖d‖ ^ 2 := by rw [hcd]; ring
    _ ≤ (1 / 2 : ℝ) * P * C₂ * (δ * ‖d‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hfac
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (le_of_lt hd) (norm_nonneg _)
    _ = ((1 / 2 : ℝ) * P * C₂ * δ) * ‖d‖ := by ring
    _ ≤ ε' * ‖d‖ := mul_le_mul_of_nonneg_right hε'' (norm_nonneg _)

/-! ## 3. Step 2: continuity of the candidate derivative -/

theorem continuousAt_psiConcBDeriv_z (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (hg : ChartData (I := I) (M := M) g₀.inner)
    (a₀ : Bil (I := I) (M := M))
    (ha₀ : ChartData (I := I) (M := M) a₀)
    (hs : IsSymm (I := I) a₀)
    (hball : ∃ δp : ℝ, 0 < δp ∧ ∀ c : CoefB ι₀ (Module.finrank ℝ E) ε,
      ‖c‖ < δp → IsPosF (I := I) (M := M) a₀ D ε c)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c₀ : CoefB ι₀ (Module.finrank ℝ E) ε,
      ‖c₀‖ < δ →
      ContinuousAt (fun c => psiConcDerivB (I := I) (M := M) a₀ D ρ ε z c) c₀ := by
  classical
  have hstep : ∀ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 ≤ p.2 ∧
        ∀ (c₀ c₁ : CoefB ι₀ (Module.finrank ℝ E) ε),
          ‖c₀‖ < p.1 → ‖c₁‖ < p.1 → IsPosF (I := I) (M := M) a₀ D ε c₀ →
          IsPosF (I := I) (M := M) a₀ D ε c₁ →
          ∀ y : FlatB (Module.finrank ℝ E),
            |UfunB (I := I) (M := M) a₀ D ε z z' c₀ y
              - UfunB (I := I) (M := M) a₀ D ε z z' c₁ y| ≤ p.2 * ‖c₀ - c₁‖ := by
    intro z'
    obtain ⟨δ, C, h1, h2, h3⟩ :=
      Work.Diff.STE.D.BaseUfun.abs_UfunB_sub_le (I := I) (M := M) D ε hg a₀ ha₀ hs hball z z'
    exact ⟨(δ, C), h1, h2, h3⟩
  choose p hp using hstep
  obtain ⟨δ₀, hδ₀, hpos⟩ := hball
  have hex : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ∀ z', δ ≤ (p z').1 := by
    by_cases hne : (Finset.univ : Finset (Work.Diff.STE.B3.JIdx ι₀
        (Module.finrank ℝ E) ε)).Nonempty
    · refine ⟨min ((Finset.univ : Finset (Work.Diff.STE.B3.JIdx ι₀
          (Module.finrank ℝ E) ε)).inf' hne (fun z' => (p z').1)) δ₀,
        lt_min ?_ hδ₀, min_le_right _ _, fun z' => ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro z' _
        exact (hp z').1
      · exact le_trans (min_le_left _ _) (Finset.inf'_le (fun z' => (p z').1)
          (Finset.mem_univ z'))
    · refine ⟨δ₀, hδ₀, le_refl _, fun z' => absurd ⟨z', Finset.mem_univ z'⟩ hne⟩
  obtain ⟨δ₁, hδ₁pos, hδ₁δ₀, hδ₁le⟩ := hex
  set Q : ℝ := |ρ (ε • fun i => ((z.2.2.2.1.1 i : ℤ) : ℝ))| with hQ
  have hQnn : 0 ≤ Q := by rw [hQ]; exact abs_nonneg _
  refine ⟨δ₁, hδ₁pos, fun c₀ hc₀ => ?_⟩
  have hp₀c₀ : IsPosF (I := I) (M := M) a₀ D ε c₀ := hpos c₀ (lt_of_lt_of_le hc₀ hδ₁δ₀)
  have hscal : ∀ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ContinuousAt (fun c => Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
        (UfunB (I := I) (M := M) a₀ D ε z z' c) z.2.2.2) c₀ := by
    intro z'
    rw [Metric.continuousAt_iff]
    intro ε'' hε''
    refine ⟨min (δ₁ - ‖c₀‖) (ε'' / (Q * (p z').2 + 1)), lt_min (sub_pos.mpr hc₀) ?_, ?_⟩
    · have hp2 : 0 ≤ Q * (p z').2 := mul_nonneg hQnn (hp z').2.1
      exact div_pos hε'' (by linarith)
    · intro c hc
      rw [dist_eq_norm] at hc
      rw [Real.dist_eq]
      have hc₁ : ‖c - c₀‖ < δ₁ - ‖c₀‖ := lt_of_lt_of_le hc (min_le_left _ _)
      have hc₂ : ‖c - c₀‖ < ε'' / (Q * (p z').2 + 1) := lt_of_lt_of_le hc (min_le_right _ _)
      have hcn : ‖c‖ < δ₁ := by
        calc ‖c‖ = ‖c₀ + (c - c₀)‖ := by rw [add_sub_cancel]
          _ ≤ ‖c₀‖ + ‖c - c₀‖ := norm_add_le _ _
          _ < δ₁ := by linarith
      have hpc : IsPosF (I := I) (M := M) a₀ D ε c := hpos c (lt_of_lt_of_le hcn hδ₁δ₀)
      have hcn' : ‖c‖ < (p z').1 := lt_of_lt_of_le hcn (hδ₁le z')
      have hc₀' : ‖c₀‖ < (p z').1 := lt_of_lt_of_le hc₀ (hδ₁le z')
      have hcontUc : Continuous (UfunB (I := I) (M := M) a₀ D ε z z' c) :=
        Work.Diff.STE.D.BaseCont.continuous_UfunB (I := I) (M := M) D ε hg a₀ ha₀ hs z z' c hpc
      have hcontUc₀ : Continuous (UfunB (I := I) (M := M) a₀ D ε z z' c₀) :=
        Work.Diff.STE.D.BaseCont.continuous_UfunB (I := I) (M := M) D ε hg a₀ ha₀ hs z z' c₀ hp₀c₀
      have hdiff : Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (UfunB (I := I) (M := M) a₀ D ε z z' c) z.2.2.2
          - Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (UfunB (I := I) (M := M) a₀ D ε z z' c₀) z.2.2.2
          = Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (UfunB (I := I) (M := M) a₀ D ε z z' c
              - UfunB (I := I) (M := M) a₀ D ε z z' c₀) z.2.2.2 := by
        have h1 := Work.Diff.STE.B3.scoeff_add_of_support ρ ε
          (UfunB (I := I) (M := M) a₀ D ε z z' c₀)
          (UfunB (I := I) (M := M) a₀ D ε z z' c - UfunB (I := I) (M := M) a₀ D ε z z' c₀)
          hcontUc₀ (hcontUc.sub hcontUc₀)
          (support_UfunB_subset (I := I) (M := M) a₀ D ε z z' c₀)
          (support_sub_subset₂ (support_UfunB_subset (I := I) (M := M) a₀ D ε z z' c)
            (support_UfunB_subset (I := I) (M := M) a₀ D ε z z' c₀)) z.2.2.2
        rw [show UfunB (I := I) (M := M) a₀ D ε z z' c₀
              + (UfunB (I := I) (M := M) a₀ D ε z z' c
                - UfunB (I := I) (M := M) a₀ D ε z z' c₀)
              = UfunB (I := I) (M := M) a₀ D ε z z' c from by
            funext y; simp only [Pi.add_apply, Pi.sub_apply]; ring] at h1
        linarith [h1]
      have hbound : |Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (UfunB (I := I) (M := M) a₀ D ε z z' c
              - UfunB (I := I) (M := M) a₀ D ε z z' c₀) z.2.2.2|
          ≤ Q * ((p z').2 * ‖c - c₀‖) := by
        rw [hQ]
        refine Work.Diff.STE.B3.abs_scoeff_le ρ ε
          (UfunB (I := I) (M := M) a₀ D ε z z' c - UfunB (I := I) (M := M) a₀ D ε z z' c₀)
          (hcontUc.sub hcontUc₀)
          (support_sub_subset₂ (support_UfunB_subset (I := I) (M := M) a₀ D ε z z' c)
            (support_UfunB_subset (I := I) (M := M) a₀ D ε z z' c₀))
          z.2.2.2 ((p z').2 * ‖c - c₀‖) (mul_nonneg (hp z').2.1 (norm_nonneg _))
          (fun y => by
            simp only [Pi.sub_apply]
            rw [abs_sub_comm, norm_sub_rev]
            exact (hp z').2.2 c₀ c hc₀' hcn' hp₀c₀ hpc y)
      rw [hdiff]
      have hfac : 0 ≤ Q * (p z').2 := mul_nonneg hQnn (hp z').2.1
      calc |Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (UfunB (I := I) (M := M) a₀ D ε z z' c
              - UfunB (I := I) (M := M) a₀ D ε z z' c₀) z.2.2.2|
          ≤ Q * ((p z').2 * ‖c - c₀‖) := hbound
        _ = (Q * (p z').2) * ‖c - c₀‖ := by ring
        _ < ε'' := by
            have h3 : (Q * (p z').2) * (ε'' / (Q * (p z').2 + 1)) < ε'' := by
              rw [mul_div_assoc']
              rw [div_lt_iff₀ (by linarith : 0 < Q * (p z').2 + 1)]
              nlinarith [hfac, hε'']
            exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_of_lt hc₂) hfac) h3
  have hterm : ∀ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      ContinuousAt (fun c : CoefB ι₀ (Module.finrank ℝ E) ε =>
        ((ContinuousLinearMap.proj z' :
          CoefB ι₀ (Module.finrank ℝ E) ε →L[ℝ] ℝ)).smulRight
        ((1 / 2 : ℝ) * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
          (UfunB (I := I) (M := M) a₀ D ε z z' c) z.2.2.2)) c₀ := by
    intro z'
    have h1 : (fun c => ((ContinuousLinearMap.proj z' :
          CoefB ι₀ (Module.finrank ℝ E) ε →L[ℝ] ℝ)).smulRight
          ((1 / 2 : ℝ) * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (UfunB (I := I) (M := M) a₀ D ε z z' c) z.2.2.2))
        = fun c => ((1 / 2 : ℝ) * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
            (UfunB (I := I) (M := M) a₀ D ε z z' c) z.2.2.2)
          • (((ContinuousLinearMap.proj z' :
              CoefB ι₀ (Module.finrank ℝ E) ε →L[ℝ] ℝ)).smulRight 1) := by
      funext c
      ext v
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply]
      ring
    rw [h1]
    exact ((hscal z').const_mul (1 / 2)).smul continuousAt_const
  have hsum : (fun c => psiConcDerivB (I := I) (M := M) a₀ D ρ ε z c)
      = fun c => ∑ z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          (ContinuousLinearMap.proj z').smulRight
            ((1 / 2 : ℝ) * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
              (UfunB (I := I) (M := M) a₀ D ε z z' c) z.2.2.2) := by
    funext c
    rw [psiConcDerivB]
  rw [hsum]
  exact tendsto_finsetSum Finset.univ (fun z' _ => (hterm z').tendsto)

/-! ## 4. Step 3: assembly -/

theorem contDiffAt_psiConcB (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (hg : ChartData (I := I) (M := M) g₀.inner)
    (a₀ : Bil (I := I) (M := M))
    (ha₀ : ChartData (I := I) (M := M) a₀)
    (hs : IsSymm (I := I) a₀)
    (hball : ∃ δp : ℝ, 0 < δp ∧ ∀ c : CoefB ι₀ (Module.finrank ℝ E) ε,
      ‖c‖ < δp → IsPosF (I := I) (M := M) a₀ D ε c)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) :
    ContDiffAt ℝ 1 (psiConcB (I := I) (M := M) a₀ D ρ ε) 0 := by
  rw [contDiffAt_pi]
  intro z
  obtain ⟨δ₁, hδ₁, h1⟩ := hasFDerivAt_psiConcB_z (I := I) (M := M) D ε hg a₀ ha₀ hs hball ρ z
  obtain ⟨δ₂, hδ₂, h2⟩ := continuousAt_psiConcBDeriv_z (I := I) (M := M) D ε hg a₀ ha₀ hs hball ρ z
  refine contDiffAt_one_iff.mpr ⟨fun c => psiConcDerivB (I := I) (M := M) a₀ D ρ ε z c,
    {c : CoefB ι₀ (Module.finrank ℝ E) ε | ‖c‖ < min δ₁ δ₂}, ?_, ?_, ?_⟩
  · refine Metric.mem_nhds_iff.mpr ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun c hc => ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hc
    exact hc
  · intro c hc
    exact (h2 c (lt_of_lt_of_le hc (min_le_right _ _))).continuousWithinAt
  · intro c hc
    exact h1 c (lt_of_lt_of_le hc (min_le_left _ _))

end

end Work.Diff.STE.D.Base
