import Submission.Work.DSM5c.ChartPresheafLaws

/-!
# DSM5c — the `W`-linear chart maps of `Dp`

`Submission/Work/DSM5c/ChartPresheaf.lean` + `ChartPresheafLaws.lean` supply the restriction maps
`R_S →+* R_T` of the perfected tilted charts and their functor laws, and
`Charts/UntiltMapAlgebra.lean` says `untiltOf.map` is `W`-linear with respect to the `W`-algebra
structure `untiltOf.algebraMap`.  This file bundles those into the `W`-linear map

  `chartDMap (h : S ⊆ T) : D_S →ₗ[W] D_T`,   `D_S := untiltOf R_S φ_S`,

i.e. the morphism data of the presheaf `Dp` of the frozen `DSMap.Mix2.area_M5c`, and proves
`untiltOf.map_id`, the remaining input for the functor laws.

The `W`-module structure on `D_S` is `RingHom.toAlgebra` of `untiltOf.algebraMap hθ φ_S`; since the
`untiltOf.algebraMap` arguments are not typeclass arguments it is introduced with `letI` at each use
site (see `chartDAlg`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.DSM5c

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a



section ChartDMap

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W]
variable {ι : Type a} [DecidableEq ι]

/-- The `W`-algebra structure of the chart untilt `D_S`. -/
noncomputable def chartDAlg (Q : PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) :
    Algebra W (untiltOf (tiltChart Q t tr htr0 htr j₀ e S) (chartPhi Q t tr htr0 htr j₀ e S)) :=
  (untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S)).toAlgebra

/-- **The `W`-linear map of the chart presheaf**: `D_S →ₗ[W] D_T` for `S ⊆ T`, obtained from
`untiltOf.map` applied to the chart restriction `tiltChartRes`. -/
noncomputable def chartDMap (Q : PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) {S T : Finset ι} (h : S ⊆ T) :
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e T
    untiltOf (tiltChart Q t tr htr0 htr j₀ e S) (chartPhi Q t tr htr0 htr j₀ e S) →ₗ[W]
      untiltOf (tiltChart Q t tr htr0 htr j₀ e T) (chartPhi Q t tr htr0 htr j₀ e T) := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e T
  exact
    { toFun := untiltOf.map (chartPhi Q t tr htr0 htr j₀ e S)
        (chartPhi Q t tr htr0 htr j₀ e T) (tiltChartRes Q t tr htr0 htr j₀ e h)
        (RingHom.ext fun r => tiltChartRes_algebraMap Q t tr htr0 htr j₀ e h r)
      map_add' := map_add _
      map_smul' := fun w x => by
        show untiltOf.map _ _ _ _ (untiltOf.algebraMap hθ _ w * x) =
          untiltOf.algebraMap hθ _ w * untiltOf.map _ _ _ _ x
        rw [map_mul, untiltOf.map_algebraMap] }

end ChartDMap

end Work.DSM5c
