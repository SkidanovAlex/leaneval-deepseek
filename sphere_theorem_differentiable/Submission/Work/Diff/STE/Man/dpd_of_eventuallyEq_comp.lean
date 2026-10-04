import Mathlib
import Submission.Work.Diff.STE.Man.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart jets of a function that agrees with `F ∘ chartCoordSymm` near a point

`Work.Diff.STE.Man.dpd c f z` is the `c`-th partial derivative (in the torus coordinate
`Fin (dim E) → ℝ`) of a family `f` of matrices, evaluated at `z`.  The lemma proved here computes the
value and the first two partial derivatives at `z` of a family `bg` which agrees *near* `z` with the
composition of a smooth map `F` on the model space `E` with the inverse chart coordinate
`chartCoordSymm I x₀`.

The point is that `chartCoordSymm I x₀` is an *affine* map with linear part `chartLin`, whose values
on the canonical basis vectors `Pi.single c 1` are the basis vectors `bB c` of `E`; hence the chain
rule turns `∂_c (F ∘ chartCoordSymm) (z)` into `D F (chartCoordSymm I x₀ z) (bB c)` and the second
derivatives into `D²F (chartCoordSymm I x₀ z) (bB c) (bB d)`.

`F` is only assumed `C^∞` *at one point*; the (harmless) consequence needed for the second order is
that `F` is differentiable in a neighbourhood of that point, which follows from the fact that
`ContDiffAt ℝ ∞` at a point implies `ContDiffAt ℝ m` for every `m : ℕ`, and this is a neighbourhood
property for finite `m`.
-/

open Filter

set_option linter.unusedSectionVars false

namespace Work.Diff.STE.Man

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The linear part of the inverse chart coordinate** `chartCoordSymm I x₀ z
= chartCentre I x₀ + chartLin z`.  It is the continuous linear map attached to the linear
equivalence `(finBasis ℝ E).equivFun.symm : (Fin (dim E) → ℝ) ≃ₗ[ℝ] E`. -/
noncomputable def chartLin : (Fin (dim E) → ℝ) →L[ℝ] E :=
  ((Module.finBasis ℝ E).equivFun.symm : (Fin (dim E) → ℝ) →ₗ[ℝ] E).toContinuousLinearMap

/-- The basis vector `bB c` of `E` is the image of the `c`-th basis vector `Pi.single c 1` of the
torus coordinate under `chartLin`. -/
lemma chartLin_single (c : Fin (dim E)) :
    chartLin (E := E) (Pi.single c 1) = Work.Diff.EXT.bB (E := E) c := by
  show (Module.finBasis ℝ E).equivFun.symm (Pi.single c 1) = Module.finBasis ℝ E c
  rw [Module.Basis.equivFun_symm_apply, Fintype.sum_eq_single c]
  · simp
  · intro b hb
    rw [Pi.single_eq_of_ne hb]
    simp

lemma chartCoordSymm_eq (x₀ : M) :
    chartCoordSymm I x₀ = fun z => chartCentre I x₀ + chartLin (E := E) z := rfl

/-- The inverse chart coordinate is differentiable, with derivative `chartLin`. -/
lemma hasFDerivAt_chartCoordSymm (x₀ : M) (z : Fin (dim E) → ℝ) :
    HasFDerivAt (chartCoordSymm I x₀) (chartLin (E := E)) z :=
  (ContinuousLinearMap.hasFDerivAt (chartLin (E := E)) (x := z)).const_add (chartCentre I x₀)

lemma fderiv_chartCoordSymm (x₀ : M) (z : Fin (dim E) → ℝ) :
    fderiv ℝ (chartCoordSymm I x₀) z = chartLin (E := E) :=
  (hasFDerivAt_chartCoordSymm (I := I) x₀ z).fderiv

lemma differentiableAt_chartCoordSymm (x₀ : M) (z : Fin (dim E) → ℝ) :
    DifferentiableAt ℝ (chartCoordSymm I x₀) z :=
  (hasFDerivAt_chartCoordSymm (I := I) x₀ z).differentiableAt

/-- A function which is `C^∞` at a point is differentiable in a neighbourhood of it. -/
lemma eventually_differentiableAt_of_contDiffAt {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {F : E → W} {y : E} (hF : ContDiffAt ℝ (⊤ : ℕ∞) F y) :
    ∀ᶠ y' in nhds y, DifferentiableAt ℝ F y' := by
  have h1 : ContDiffAt ℝ 1 F y := hF.of_le (by simp)
  exact (h1.eventually (by simp)).mono (fun y' hy' => hy'.differentiableAt (by simp))

/-- The same statement, pulled back along the (continuous) inverse chart coordinate. -/
lemma eventually_differentiableAt_comp_chartCoordSymm {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {F : E → W} {x₀ : M} {z : Fin (dim E) → ℝ}
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F (chartCoordSymm I x₀ z)) :
    ∀ᶠ z' in nhds z, DifferentiableAt ℝ F (chartCoordSymm I x₀ z') :=
  (differentiableAt_chartCoordSymm (I := I) x₀ z).continuousAt.tendsto.eventually
    (eventually_differentiableAt_of_contDiffAt hF)

/-- **The second chain rule for an affine change of variables.**  For `F` smooth at `c₀ + L z`,

`D (z' ↦ D F (c₀ + L z') w) z v = D² F (c₀ + L z) (L v) w`.

(Everything is evaluated in `ℝ`-normed spaces; `E →L[ℝ] (E →L[ℝ] W)` is the space of second
derivatives, and the two arguments `L v`, `w` are applied in that order.) -/
lemma fderiv_fderiv_comp_apply {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : E → W} {c₀ : E} {L : (Fin (dim E) → ℝ) →L[ℝ] E} {z : Fin (dim E) → ℝ}
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F (c₀ + L z)) (w : E) (v : Fin (dim E) → ℝ) :
    fderiv ℝ (fun z' => (fderiv ℝ F (c₀ + L z')) w) z v
      = fderiv ℝ (fderiv ℝ F) (c₀ + L z) (L v) w := by
  have hF' : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ F) (c₀ + L z) :=
    hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hdF' : DifferentiableAt ℝ (fderiv ℝ F) (c₀ + L z) := hF'.differentiableAt (by simp)
  have hdL : DifferentiableAt ℝ (fun z' : Fin (dim E) → ℝ => c₀ + L z') z :=
    ((ContinuousLinearMap.hasFDerivAt L (x := z)).const_add c₀).differentiableAt
  have hderL : fderiv ℝ (fun z' : Fin (dim E) → ℝ => c₀ + L z') z = L :=
    ((ContinuousLinearMap.hasFDerivAt L (x := z)).const_add c₀).fderiv
  have hΘ : fderiv ℝ (fun z' => fderiv ℝ F (c₀ + L z')) z
      = (fderiv ℝ (fderiv ℝ F) (c₀ + L z)).comp L := by
    rw [show (fun z' : Fin (dim E) → ℝ => fderiv ℝ F (c₀ + L z'))
        = (fderiv ℝ F) ∘ (fun z' => c₀ + L z') from rfl,
      fderiv_comp (x := z) hdF' hdL, hderL]
  have hc : DifferentiableAt ℝ (fun z' => fderiv ℝ F (c₀ + L z')) z := hdF'.comp z hdL
  have hu : DifferentiableAt ℝ (fun _ : Fin (dim E) → ℝ => w) z := differentiableAt_const w
  have hz : fderiv ℝ (fun _ : Fin (dim E) → ℝ => w) z = 0 := by
    simp
  rw [fderiv_clm_apply hc hu, hz]
  simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply, hΘ,
    ContinuousLinearMap.comp_apply]

/-- The specialised form of `fderiv_fderiv_comp_apply` for the inverse chart coordinate. -/
lemma fderiv_fderiv_chartCoordSymm_apply
    {F : E → Work.Diff.EXT.MatE (E := E)} {x₀ : M} {z : Fin (dim E) → ℝ}
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F (chartCoordSymm I x₀ z)) (c d : Fin (dim E)) :
    fderiv ℝ (fun z' => (fderiv ℝ F (chartCoordSymm I x₀ z'))
        (Work.Diff.EXT.bB (E := E) d)) z (Pi.single c 1)
      = fderiv ℝ (fderiv ℝ F) (chartCoordSymm I x₀ z)
          (Work.Diff.EXT.bB (E := E) c) (Work.Diff.EXT.bB (E := E) d) := by
  have h := fderiv_fderiv_comp_apply (L := chartLin (E := E)) (c₀ := chartCentre I x₀)
    (F := F) (z := z) (w := Work.Diff.EXT.bB (E := E) d) (v := Pi.single c 1) hF
  rw [chartLin_single c] at h
  exact h

theorem dpd_of_eventuallyEq_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (x₀ : M) (F : E → Work.Diff.EXT.MatE (E := E)) (z : Fin (Work.Diff.STE.Man.dim E) → ℝ)
    (bg : (Fin (Work.Diff.STE.Man.dim E) → ℝ) → Work.Diff.EXT.MatE (E := E))
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F (Work.Diff.STE.Man.chartCoordSymm I x₀ z))
    (hbg : bg =ᶠ[nhds z] fun z' => F (Work.Diff.STE.Man.chartCoordSymm I x₀ z')) :
    (bg z = F (Work.Diff.STE.Man.chartCoordSymm I x₀ z)) ∧
    (∀ c, Work.Diff.STE.Man.dpd (E := E) c bg z
      = fderiv ℝ F (Work.Diff.STE.Man.chartCoordSymm I x₀ z)
          (Work.Diff.EXT.bB (E := E) c)) ∧
    (∀ c d, Work.Diff.STE.Man.dpd (E := E) c (Work.Diff.STE.Man.dpd (E := E) d bg) z
      = fderiv ℝ (fderiv ℝ F) (Work.Diff.STE.Man.chartCoordSymm I x₀ z)
          (Work.Diff.EXT.bB (E := E) c) (Work.Diff.EXT.bB (E := E) d)) := by
  have hFd : DifferentiableAt ℝ F (chartCoordSymm I x₀ z) := hF.differentiableAt (by simp)
  have hcsd : DifferentiableAt ℝ (chartCoordSymm I x₀) z :=
    differentiableAt_chartCoordSymm (I := I) x₀ z
  refine ⟨hbg.eq_of_nhds, ?_, ?_⟩
  · intro c
    show fderiv ℝ bg z (Pi.single c 1)
      = fderiv ℝ F (chartCoordSymm I x₀ z) (Work.Diff.EXT.bB (E := E) c)
    rw [Filter.EventuallyEq.fderiv_eq hbg]
    rw [show (fun z' : Fin (dim E) → ℝ => F (chartCoordSymm I x₀ z'))
        = F ∘ chartCoordSymm I x₀ from rfl]
    rw [fderiv_comp (x := z) (g := F) (f := chartCoordSymm I x₀) hFd hcsd]
    rw [fderiv_chartCoordSymm (I := I) x₀ z, ContinuousLinearMap.comp_apply]
    exact congrArg (fun A => fderiv ℝ F (chartCoordSymm I x₀ z) A) (chartLin_single c)
  · intro c d
    have hEv := eventually_differentiableAt_comp_chartCoordSymm (I := I) (x₀ := x₀) (z := z) hF
    have hA : (fun z' => fderiv ℝ bg z' (Pi.single d 1)) =ᶠ[nhds z]
        (fun z' => (fderiv ℝ F (chartCoordSymm I x₀ z'))
          (Work.Diff.EXT.bB (E := E) d)) := by
      filter_upwards [Filter.EventuallyEq.fderiv (𝕜 := ℝ) hbg, hEv] with z' hz' hz'F
      rw [hz']
      rw [show (fun z'' : Fin (dim E) → ℝ => F (chartCoordSymm I x₀ z''))
          = F ∘ chartCoordSymm I x₀ from rfl]
      rw [fderiv_comp (x := z') (g := F) (f := chartCoordSymm I x₀) hz'F
        (differentiableAt_chartCoordSymm (I := I) x₀ z')]
      rw [fderiv_chartCoordSymm (I := I) x₀ z', ContinuousLinearMap.comp_apply]
      exact congrArg (fun A => fderiv ℝ F (chartCoordSymm I x₀ z') A) (chartLin_single d)
    show fderiv ℝ (fun z' => fderiv ℝ bg z' (Pi.single d 1)) z (Pi.single c 1)
      = fderiv ℝ (fderiv ℝ F) (chartCoordSymm I x₀ z)
          (Work.Diff.EXT.bB (E := E) c) (Work.Diff.EXT.bB (E := E) d)
    rw [Filter.EventuallyEq.fderiv_eq hA]
    exact fderiv_fderiv_chartCoordSymm_apply (I := I) (x₀ := x₀) (z := z) hF c d

end Work.Diff.STE.Man
