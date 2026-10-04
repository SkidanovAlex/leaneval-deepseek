import Mathlib
import Submission.Work.Diff.STE.Lead.Gal.Span
import Submission.Work.Diff.STE.B3.BPair_J_self
import Submission.Work.Diff.STE.D.psi.Assemble

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Linearity of the Galerkin coefficients on the span, and the Lipschitz bound for `Fcoef`

The foreground `u~(c) = J ρ ε (galState D ε c)` of the span-form scheme is the span element
`genMap D ε (Fcoef c)` with `Fcoef c = galCoeff D ρ ε (galState D ε c)`.  This module proves the
linearity of the Galerkin coefficient map `galCoeff` in the *section* argument (on sections with
smooth chart data), the resulting *affine* description of `Fcoef`, and the Lipschitz bound

  `‖Fcoef c - Fcoef c'‖ ≤ C ‖c - c'‖`

with the explicit constant `C = √♯ · Σ_z ‖galCoeff D ρ ε (jSym D ε z)‖`.
-/

namespace Work.Diff.STE.Lead.Gal

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## Linearity of the localised components -/

/-- The localised component `D.R i · a b` is additive in the section. -/
lemma R_add (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (h k : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    D.R i (h + k) a b = D.R i h a b + D.R i k a b := by
  funext z
  simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Pi.add_apply,
    ContinuousLinearMap.add_apply]
  ring

/-- The localised component `D.R i · a b` is homogeneous in the section. -/
lemma R_smul (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) (r : ℝ)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    D.R i (r • h) a b = r • D.R i h a b := by
  funext z
  simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The support of the localised component in the half-open cube. -/
lemma support_R_subset_ioc (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    Function.support (D.R i h a b) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) := by
  intro z hz j _
  exact ⟨(Work.Diff.STE.B3.support_R_subset D i h a b hz j (Set.mem_univ j)).1,
    le_of_lt (Work.Diff.STE.B3.support_R_subset D i h a b hz j (Set.mem_univ j)).2⟩

/-- **Additivity of the Galerkin coefficient family in the section argument.** -/
theorem galCoeff_add (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (h k : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (hk : Work.Diff.STE.D.ChartData (I := I) (M := M) k) :
    Work.Diff.STE.Lead.galCoeff D ρ ε (h + k)
      = Work.Diff.STE.Lead.galCoeff D ρ ε h + Work.Diff.STE.Lead.galCoeff D ρ ε k := by
  funext z
  have h1 : Work.Diff.STE.B3.jFamilyCoeff D ρ ε (h + k) z
      = Work.Diff.STE.B3.jFamilyCoeff D ρ ε h z + Work.Diff.STE.B3.jFamilyCoeff D ρ ε k z := by
    show Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
        (D.R z.1 (h + k) z.2.1 z.2.2.1) z.2.2.2 = _
    rw [R_add]
    exact Work.Diff.STE.B3.scoeff_add_of_support ρ ε (D.R z.1 h z.2.1 z.2.2.1)
      (D.R z.1 k z.2.1 z.2.2.1)
      ((Work.Diff.STE.B3.R_contDiff_of_chartData D h hh z.1 z.2.1 z.2.2.1).continuous)
      ((Work.Diff.STE.B3.R_contDiff_of_chartData D k hk z.1 z.2.1 z.2.2.1).continuous)
      (support_R_subset_ioc D z.1 h z.2.1 z.2.2.1)
      (support_R_subset_ioc D z.1 k z.2.1 z.2.2.1) z.2.2.2
  simp only [Work.Diff.STE.Lead.galCoeff, h1, Pi.add_apply]
  ring

/-- **Homogeneity of the Galerkin coefficient family in the section argument.** -/
theorem galCoeff_smul (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (r : ℝ)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) :
    Work.Diff.STE.Lead.galCoeff D ρ ε (r • h)
      = r • Work.Diff.STE.Lead.galCoeff D ρ ε h := by
  funext z
  have h1 : Work.Diff.STE.B3.jFamilyCoeff D ρ ε (r • h) z
      = r * Work.Diff.STE.B3.jFamilyCoeff D ρ ε h z := by
    show Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
        (D.R z.1 (r • h) z.2.1 z.2.2.1) z.2.2.2 = _
    rw [R_smul]
    exact Work.Diff.STE.B3.scoeff_smul_of_support ρ ε r (D.R z.1 h z.2.1 z.2.2.1)
      ((Work.Diff.STE.B3.R_contDiff_of_chartData D h hh z.1 z.2.1 z.2.2.1).continuous)
      (support_R_subset_ioc D z.1 h z.2.1 z.2.2.1) z.2.2.2
  simp only [Work.Diff.STE.Lead.galCoeff, h1, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The Galerkin coefficients of a span element**: the coefficients of `genMap D ε c` are the
corresponding linear combination of the coefficient vectors of the spanning family. -/
theorem galCoeff_genMap_eq_sum (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (c : Coef ι₀ (Module.finrank ℝ E) ε) :
    Work.Diff.STE.Lead.galCoeff D ρ ε (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c)
      = ∑ z, c z • Work.Diff.STE.Lead.galCoeff D ρ ε
          (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) := by
  funext z₀
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hlin : D.R z₀.1 (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c) z₀.2.1 z₀.2.2.1
      = ∑ z, c z • D.R z₀.1 (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
          z₀.2.1 z₀.2.2.1 := by
    funext y
    simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Work.Diff.STE.D.genMap,
      Finset.sum_apply,
      Pi.smul_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z _ => by ring)
  show (1 / 2 : ℝ) * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
      (D.R z₀.1 (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c) z₀.2.1 z₀.2.2.1)
      z₀.2.2.2
    = ∑ z, c z * ((1 / 2 : ℝ) * Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
        (D.R z₀.1 (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) z₀.2.1 z₀.2.2.1)
        z₀.2.2.2)
  rw [hlin]
  rw [Work.Diff.STE.B3.scoeff_finset_sum_smul Finset.univ ρ ε z₀.2.2.2 (fun z => c z)
    (fun z => D.R z₀.1 (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) z₀.2.1 z₀.2.2.1)
    (fun z _ => (Work.Diff.STE.B3.R_contDiff_of_chartData D
      (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
      (Work.Diff.STE.D.psi.jSym_chartData (I := I) (M := M) D ε z)
      z₀.1 z₀.2.1 z₀.2.2.1).continuous)
    (fun z _ => support_R_subset_ioc D z₀.1 (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)
      z₀.2.1 z₀.2.2.1)]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun z _ => by ring)

/-! ## The affine description of `Fcoef` and its Lipschitz bound -/

/-- **`Fcoef` is the background coefficient plus the linear combination of the spanning
coefficients.** -/
theorem Fcoef_eq_sum (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (c : Coef ι₀ (Module.finrank ℝ E) ε) :
    Fcoef D ρ ε c = Work.Diff.STE.Lead.galCoeff D ρ ε g₀.inner
      + ∑ z, c z • Work.Diff.STE.Lead.galCoeff D ρ ε
          (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) := by
  have h : Submission.Diff.STEGal.galState D ε c
      = g₀.inner + Work.Diff.STE.D.genMap (I := I) (M := M) D ε c := rfl
  rw [Fcoef, h, galCoeff_add D ρ ε _ _
    hg
    (Work.Diff.STE.D.ChartData_genMap (I := I) (M := M) D ε c)]
  rw [galCoeff_genMap_eq_sum]

/-! ## The Lipschitz bound for `Fcoef` -/

/-- **`Fcoef` is Lipschitz in the coefficients.**  `Fcoef c = Fcoef c' + Σ_z (c z - c' z) • F_z`
where `F_z = galCoeff D ρ ε (jSym D ε z)`; hence
`‖Fcoef c - Fcoef c'‖ ≤ (♯JIdx + 1) (Σ_z ‖F_z‖ + 1) ‖c - c'‖`. -/
theorem Fcoef_lipschitz (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c c' : Coef ι₀ (Module.finrank ℝ E) ε,
      ‖Fcoef D ρ ε c - Fcoef D ρ ε c'‖ ≤ C * ‖c - c'‖ := by
  classical
  refine ⟨((Fintype.card (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) : ℝ) + 1) *
    ((∑ z, ‖Work.Diff.STE.Lead.galCoeff D ρ ε (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)‖) + 1),
    by positivity, fun c c' => ?_⟩
  have hsub : Fcoef D ρ ε c - Fcoef D ρ ε c'
      = ∑ z, (c z - c' z) • Work.Diff.STE.Lead.galCoeff D ρ ε
          (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) := by
    rw [Fcoef_eq_sum hg D ρ ε c, Fcoef_eq_sum hg D ρ ε c']
    rw [add_sub_add_left_eq_sub]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun z _ => by rw [sub_smul])
  rw [hsub]
  have hS : 0 ≤ ∑ z, ‖Work.Diff.STE.Lead.galCoeff D ρ ε
      (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)‖ :=
    Finset.sum_nonneg (fun z _ => norm_nonneg _)
  have hN : 0 ≤ (Fintype.card (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) : ℝ) :=
    Nat.cast_nonneg _
  calc ‖∑ z, (c z - c' z) • Work.Diff.STE.Lead.galCoeff D ρ ε
        (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)‖
      ≤ ∑ z, ‖(c z - c' z) • Work.Diff.STE.Lead.galCoeff D ρ ε
          (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)‖ := norm_sum_le _ _
    _ = ∑ z, |c z - c' z| * ‖Work.Diff.STE.Lead.galCoeff D ρ ε
          (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)‖ := by
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ z, ‖c - c'‖ * ‖Work.Diff.STE.Lead.galCoeff D ρ ε
          (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)‖ := by
        refine Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        rw [← Real.norm_eq_abs]
        exact norm_le_pi_norm (c - c') z
    _ = ‖c - c'‖ * (∑ z, ‖Work.Diff.STE.Lead.galCoeff D ρ ε
          (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)‖) := by
        rw [Finset.mul_sum]
    _ ≤ ((Fintype.card (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) : ℝ) + 1) *
          ((∑ z, ‖Work.Diff.STE.Lead.galCoeff D ρ ε
            (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)‖) + 1) * ‖c - c'‖ := by
        have h1 : (∑ z, ‖Work.Diff.STE.Lead.galCoeff D ρ ε
            (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)‖)
            ≤ ((Fintype.card (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) : ℝ) + 1) *
              ((∑ z, ‖Work.Diff.STE.Lead.galCoeff D ρ ε
                (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)‖) + 1) := by
          nlinarith [hS, hN]
        calc ‖c - c'‖ * (∑ z, ‖Work.Diff.STE.Lead.galCoeff D ρ ε
              (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)‖)
            ≤ ‖c - c'‖ * (((Fintype.card (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) : ℝ) + 1) *
              ((∑ z, ‖Work.Diff.STE.Lead.galCoeff D ρ ε
                (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z)‖) + 1)) :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = _ := by ring

end

end Work.Diff.STE.Lead.Gal
