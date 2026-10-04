import Mathlib
import Submission.Work.Diff.STE.B3.J_finite_rank
import Submission.Work.Diff.STE.Lead.Gal.SpanLin
import Submission.Work.Diff.STE.B3.scoeff_finset_sum_smul
import Submission.Work.Diff.STE.Lead.Gal.Prelude
import Submission.Work.Diff.STE.D.chartData_metric

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

/-! `pinched_closed`: the set of coefficient vectors at which the Friedrichs mollifier of the Galerkin
state dominates `lam • g₀` is *closed*.

ROUTE (both reviewers confirmed the statement).  `Work.Diff.STE.B3.J_eq_sum_index` (needs `hε` and
`hρ0`) writes `D.J ρ ε (galState D ε c) = Σ_z (jFamilyCoeff D ρ ε (galState D ε c) z) • jSym D ε z`,
a *finite* sum; evaluating at `(x, v, v)` gives
`Σ_z (jFamilyCoeff D ρ ε (galState D ε c) z) * (jSym D ε z x v v)`.  Each coefficient is *affine* in
`c`: `galState D ε c = g₀.inner + genMap D ε c` (`Submission.Diff.STEGal.galState`), and
`jFamilyCoeff D ρ ε · z` (equivalently `Work.Diff.STE.Lead.galCoeff = (1/2) • jFamilyCoeff`) is
additive and homogeneous in the section — `Work.Diff.STE.Lead.Gal.R_add` / `R_smul` /
`support_R_subset_ioc` together with `Work.Diff.STE.B3.scoeff_add_of_support` /
`scoeff_smul_of_support` / `scoeff_finset_sum_smul` (or `Work.Diff.STE.Lead.Gal.galCoeff_add`,
`galCoeff_smul` for `genMap`).  Hence `c ↦ (D.J ρ ε (galState D ε c)) x v v` is an explicit affine
function of `c` on the finite-dimensional space, so it is continuous, and the set is the intersection
over `(x, v)` of the preimages of the closed rays `[lam * g₀.inner x v v, ∞)`.  Note
`Work.Diff.STE.D.ChartData (g₀.inner)` is the theorem `Work.Diff.STE.D.chartData_metric g₀`
(`Diff/STE/D/chartData_metric.lean`), and `ChartData (genMap D ε c)` is
`Work.Diff.STE.D.ChartData_genMap`.

The proof below follows exactly this route, in the *span* form of the scheme (module
`Submission.Work.Diff.STE.Lead.Gal.SpanLin`), which packages the affinity of the coefficient family
in one lemma `Fcoef_eq_sum`: the mollifier of the Galerkin state is the span element whose
coefficient vector is

  `Fcoef D ρ ε c = galCoeff D ρ ε g₀.inner + Σ_z c z • galCoeff D ρ ε (jSym D ε z)`,

so the evaluated form is the (finite, hence manifestly continuous) affine function

  `Σ_{z₀} (galCoeff D ρ ε g₀.inner z₀ + Σ_z c z * galCoeff D ρ ε (jSym D ε z) z₀)
      * (jSym D ε z₀ x v v)`.

This is `J_galState_eval` below.  The remainder is the elementary `continuous_affine_eval` and the
closedness of an arbitrary intersection of closed sets. -/

/-! ### Evaluating the span form at a fixed tangent vector -/

/-- The coefficient-to-section map `genMap D ε δ = Σ_z δ z • jSym D ε z` evaluated at a pair of
vectors is the corresponding finite linear combination of the evaluations. -/
lemma genMap_eval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ)
    (δ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (x : M) (v : TangentSpace I x) :
    Work.Diff.STE.D.genMap (I := I) (M := M) D ε δ x v v
      = ∑ z, δ z * (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z x v v) := by
  rw [Work.Diff.STE.D.genMap]
  simp only [Finset.sum_apply, Pi.smul_apply, sum_apply, smul_apply, smul_eq_mul]

/-- **The evaluated mollifier of the Galerkin state, as an explicit affine function of `c`.**

`D.J ρ ε (galState D ε c)` is the span element `genMap D ε (Fcoef c)` (the mollifier of a symmetric
section is `genMap` of its Galerkin coefficients, `Work.Diff.STE.Lead.J_eq_genMap_galCoeff`), and
`Fcoef c = galCoeff D ρ ε g₀.inner + Σ_z c z • galCoeff D ρ ε (jSym D ε z)` by
`Work.Diff.STE.Lead.Gal.Fcoef_eq_sum` (which uses the smooth chart data of the *metric* `g₀`,
`Work.Diff.STE.D.chartData_metric`).  Evaluating at `(x, v, v)` gives the displayed finite sum. -/
lemma J_galState_eval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
    (x : M) (v : TangentSpace I x) :
    (D.J ρ ε (Submission.Diff.STEGal.galState D ε c)) x v v
      = ∑ z₀, (Work.Diff.STE.Lead.galCoeff D ρ ε (g₀.inner) z₀
          + ∑ z, c z * Work.Diff.STE.Lead.galCoeff D ρ ε
              (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) z₀)
        * (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z₀ x v v) := by
  rw [Work.Diff.STE.Lead.J_eq_genMap_galCoeff D ρ ε hε hρ0 _
    (Work.Diff.STE.Lead.isSymm_galState D ε c)]
  rw [show Work.Diff.STE.Lead.galCoeff D ρ ε (Submission.Diff.STEGal.galState D ε c)
      = Work.Diff.STE.Lead.Gal.Fcoef D ρ ε c from rfl]
  rw [Work.Diff.STE.Lead.Gal.Fcoef_eq_sum (Work.Diff.STE.D.chartData_metric g₀) D ρ ε c]
  simp only [Work.Diff.STE.D.genMap, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_apply,
    sum_apply, smul_eq_mul]

/-- An explicit affine function of `c` on a finite-dimensional coordinate space is continuous. -/
lemma continuous_affine_eval {ι : Type*} [Fintype ι] (A : ι → ℝ) (B : ι → ι → ℝ) (S : ι → ℝ) :
    Continuous (fun c : ι → ℝ => ∑ z₀, (A z₀ + ∑ z, c z * B z z₀) * S z₀) := by
  rw [show (fun c : ι → ℝ => ∑ z₀, (A z₀ + ∑ z, c z * B z z₀) * S z₀)
      = (fun c : ι → ℝ => ∑ z₀ ∈ (Finset.univ : Finset ι),
          (A z₀ + ∑ z ∈ (Finset.univ : Finset ι), c z * B z z₀) * S z₀) from rfl]
  refine continuous_finsetSum _ (fun z₀ _ => ?_)
  refine Continuous.mul ?_ continuous_const
  refine Continuous.add continuous_const ?_
  exact continuous_finsetSum _ (fun z _ => Continuous.mul (continuous_apply z) continuous_const)

/-- **The evaluated mollifier of the Galerkin state is continuous in the coefficients.** -/
lemma continuous_galJ_eval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (x : M) (v : TangentSpace I x) :
    Continuous (fun c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ =>
      (D.J ρ ε (Submission.Diff.STEGal.galState D ε c)) x v v) := by
  have h : (fun c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ =>
        (D.J ρ ε (Submission.Diff.STEGal.galState D ε c)) x v v)
      = (fun c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ =>
          ∑ z₀, (Work.Diff.STE.Lead.galCoeff D ρ ε (g₀.inner) z₀
              + ∑ z, c z * Work.Diff.STE.Lead.galCoeff D ρ ε
                  (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) z₀)
            * (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z₀ x v v)) :=
    funext (fun c => J_galState_eval D ρ ε hε hρ0 c x v)
  rw [h]
  exact continuous_affine_eval _ _ _

theorem pinched_closed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (lam ε : ℝ) (hε : 0 < ε)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0) :
    IsClosed {c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ |
      ∀ (x : M) (v : TangentSpace I x),
        lam * g₀.inner x v v
          ≤ (D.J ρ ε (Submission.Diff.STEGal.galState D ε c)) x v v} := by
  rw [show {c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ |
        ∀ (x : M) (v : TangentSpace I x),
          lam * g₀.inner x v v
            ≤ (D.J ρ ε (Submission.Diff.STEGal.galState D ε c)) x v v}
      = ⋂ (x : M), ⋂ (v : TangentSpace I x),
          {c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ |
            lam * g₀.inner x v v
              ≤ (D.J ρ ε (Submission.Diff.STEGal.galState D ε c)) x v v} from by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iInter]]
  refine isClosed_iInter (fun x => isClosed_iInter (fun v => ?_))
  exact isClosed_Ici.preimage (continuous_galJ_eval D ρ ε hε hρ0 x v)

end Work.Diff.STE.Lead.GalTame
