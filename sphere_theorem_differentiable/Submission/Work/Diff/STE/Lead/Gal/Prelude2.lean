import Mathlib
import Submission.Diff.STEGal
import Submission.Work.Diff.STE.Lead.Gal.Prelude

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bridge lemmas between the span-form Galerkin scheme and the definition `IsGalSol`

These three lemmas used to live in `Submission/Work/Diff/STE/Lead/gal_uniform_v2.lean`.  They are
moved here **verbatim** (same fully-qualified names) because the target module
`Submission.Work.Diff.STE.Lead.gal_uniform_v2` must be able to *import* the trapping theorem
(`Diff/STE/Lead/GalTame/galerkin_trapped_solution_clean`, and the a priori estimate modules) while
those modules need `hasDerivWithinAt_galState` / `isGalSol_of_galVF2`.  Keeping the lemmas in the
target module would create an import cycle; keeping them here breaks it without renaming anything.

* `deTurckSec_congr` — proof irrelevance of the DeTurck section in the proof arguments (needed
  because `IsGalSol` quantifies over the proofs of symmetry/positivity/chart-smoothness);
* `hasDerivWithinAt_galState` — the pointwise chain rule for `galState` in the
  `HasDerivWithinAt`-on-`Icc 0 τ` form used by `IsGalSol`;
* `isGalSol_of_galVF2` — the span-form Galerkin ODE `c' = galVF2 … c` implies `IsGalSol`.
-/

namespace Work.Diff.STE.Lead

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}

/-- **The DeTurck section does not depend on the *proofs* of symmetry, positivity and smooth chart
data** (proof irrelevance: the underlying `smetOf` has `inner := h` and all its other fields are
propositions).  This is what allows a curve produced by the span-form Galerkin equation (whose
steps are stated with the canonical proofs) to satisfy the definition `IsGalSol`, which quantifies
over all proof arguments. -/
lemma deTurckSec_congr (hLC : LCSmooth I M) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hsym' : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hpos' : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (hsm' : Work.Diff.STE.D.ChartData (I := I) (M := M) h) :
    Work.Diff.STE.D.deTurckSec hLC g₀ h hsym hpos hsm
      = Work.Diff.STE.D.deTurckSec hLC g₀ h hsym' hpos' hsm' := by
  have hs : Work.Diff.STE.D.smetOf (I := I) h hsym hpos hsm
      = Work.Diff.STE.D.smetOf (I := I) h hsym' hpos' hsm' := by congr 1
  ext x u v
  simp only [Work.Diff.STE.D.deTurckSec_apply, hs]

/-- **The pointwise chain rule for `galState` in the `HasDerivWithinAt` form** (the version used by
`IsGalSol`, whose derivatives are taken within `Icc 0 τ`). -/
lemma hasDerivWithinAt_galState (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    {s : Set ℝ} {c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)}
    {c' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ} {t : ℝ}
    (h : HasDerivWithinAt c c' s t) :
    ∀ (x : M) (u v : TangentSpace I x),
      HasDerivWithinAt (fun σ => galState D ε (c σ) x u v)
        (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c' x u v) s t := by
  intro x u v
  have h1 : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      HasDerivWithinAt
        (fun σ => (c σ) z * (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z x u v))
        ((c' z) * (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z x u v)) s t :=
    fun z => (((ContinuousLinearMap.proj z).hasFDerivAt).comp_hasDerivWithinAt t h)
      |>.mul_const (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z x u v)
  have h2 := HasDerivWithinAt.sum (u := Finset.univ) (fun z _ => h1 z)
  have hfun : (fun σ => ∑ z, (c σ) z * (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z x u v))
      = (∑ z, fun σ => (c σ) z * (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z x u v)) := by
    funext σ; rw [Finset.sum_apply]
  have h3 : HasDerivWithinAt
      (fun σ => ∑ z, (c σ) z * (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z x u v))
      (∑ z, (c' z) * (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z x u v)) s t := by
    simpa only [hfun] using h2
  have h4 := h3.const_add (g₀.inner x u v)
  simpa only [galState, Work.Diff.STE.D.addSec_apply, Work.Diff.STE.D.genMap,
    Finset.sum_apply, sum_apply, Pi.smul_apply, smul_apply, smul_eq_mul] using h4

/-- **The span-form Galerkin ODE satisfies `IsGalSol`.**  If `c 0 = 0`, the foreground
`u~(c) = J ρ ε (galState D ε c)` is positive definite along `[0, τ]`, and `c` solves
`c' = galVF2 hLC D ρ ε hε hρ0 c` (the Galerkin approximant of `u' = J ρ ε (P (J ρ ε u))`), then `c`
satisfies the definition `IsGalSol hLC D ρ ε τ c`.  The two ingredients are
`genMap_galVF2` (the field realises `J ρ ε (P (u~(c)))` in the spanning family) and
`deTurckSec_congr` (proof irrelevance, since `IsGalSol` quantifies over the proof arguments). -/
lemma isGalSol_of_galVF2 (hLC : LCSmooth I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (τ : ℝ) {c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)}
    (hc0 : c 0 = 0)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) τ, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < (D.J ρ ε (galState D ε (c t))) x v v)
    (hode : ∀ t ∈ Set.Icc (0 : ℝ) τ,
      HasDerivWithinAt c (galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t))
        (Set.Icc (0 : ℝ) τ) t) :
    IsGalSol hLC D ρ ε τ c := by
  refine ⟨hc0, hpos, fun t ht hsym hsm hpos' x u v => ?_⟩
  have h1 : ∀ (hsym₀ : ∀ (x : M) (u v : TangentSpace I x),
        (D.J ρ ε (galState D ε (c t))) x u v = (D.J ρ ε (galState D ε (c t))) x v u)
      (hpos₀ : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ ε (galState D ε (c t))) x v v)
      (hsm₀ : Work.Diff.STE.D.ChartData (I := I) (M := M)
        (D.J ρ ε (galState D ε (c t)))),
      Work.Diff.STE.D.genMap (I := I) (M := M) D ε
          (galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) x u v
        = (D.J ρ ε (Work.Diff.STE.D.deTurckSec hLC g₀ (D.J ρ ε (galState D ε (c t)))
            hsym₀ hpos₀ hsm₀)) x u v := by
    intro hsym₀ hpos₀ hsm₀
    rw [genMap_galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t) (hpos t ht),
      deTurckSec_congr (g₀ := g₀) hLC (D.J ρ ε (galState D ε (c t)))
        (isSymm_J D ρ ε hε hρ0 (galState D ε (c t)) (isSymm_galState D ε (c t))) hsym₀
        (hpos t ht) hpos₀
        (chartData_J D ρ ε hε hρ0 (galState D ε (c t)) (isSymm_galState D ε (c t))) hsm₀]
  have h2 := hasDerivWithinAt_galState (D := D) (ε := ε) (hode t ht) x u v
  rw [h1 hsym hpos' hsm] at h2
  exact h2

end

end Work.Diff.STE.Lead
