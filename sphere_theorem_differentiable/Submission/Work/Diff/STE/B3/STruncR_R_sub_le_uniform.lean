import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.Recon
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.Lead.truncDiff_tendsto_uniform

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-- **Uniform convergence of the Friedrichs truncation of the B3 components of the seed metric.**
For every `δ > 0`, for all `ε` close enough to `0` from the right, the truncated component
`B3Data.STruncR ρ ε (D.R i g₀.inner a b)` differs from the component `D.R i g₀.inner a b` itself by
at most `δ` *uniformly over the whole open unit cube*, hence uniformly over all `(i,a,b)`.

ROUTE.  `f := D.R i g₀.inner a b` is `C^∞` and supported in the open cube: smoothness from
`Work.Diff.STE.B3Data.R_contDiff` with the hypotheses `hdg i` and `hmat i a b`, support from
`Work.Diff.STE.B3Data.R_support`.  The truncation estimate is the *proved* and `T2Space`-free
`Work.Diff.STE.Lead.truncDiff_tendsto_uniform` (module
`Submission.Work.Diff.STE.Lead.truncDiff_tendsto_uniform`, sorry-free), applied with
`ι := Fin (Module.finrank ℝ E)`, `ρ`, the hypotheses `hρ0`, `hρb`, `hρc`, `hρ1`, `f` and the two
hypotheses on `f`; it gives
`∀ᶠ ε in nhdsWithin 0 (Ioi 0), ∀ y, ‖STruncC ρ ε f y − ∑' m, ((f (y + iVec m) : ℝ) : ℂ)‖ ≤ δ`.
Combine the finitely many `(i,a,b)` with `Filter.eventually_all` (twice; `ι₀` and the two `Fin`s are
finite).  For `y` in the open cube, `∑' m, ((f (y + iVec m) : ℝ) : ℂ) = ((f y : ℝ) : ℂ)` because
`f` is supported in the open cube — `Work.Diff.STE.B3Data.Rper_eq_R` states exactly that for the
periodisation `D.Rper i g₀.inner a b`, which is *definitionally* `∑' m, ↑(f (y + iVec m))`.  Finally
`(STruncC ρ ε f y).re = STruncR ρ ε f y` definitionally (`STruncC` is
`Complex.ofReal (Complex.re (seriesFun …))`, `STruncR` is the real part of the same series), and
`|(z).re − r| = |(z − ↑r).re| ≤ ‖z − ↑r‖` for `r : ℝ` (`Complex.abs_re_le_norm`). -/
theorem STruncR_R_sub_le_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρb : ∀ y : Fin (Module.finrank ℝ E) → ℝ, ‖ρ y‖ ≤ 1)
    (hρc : ContinuousAt ρ 0) (hρ1 : ρ 0 = 1)
    (hdg : ∀ i : ι₀, D.DensGood i)
    (hmat : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞) (D.matChart i g₀.inner a b) (extChartAt I (D.x₀ i)).target)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (y : Fin (Module.finrank ℝ E) → ℝ),
        (∀ j : Fin (Module.finrank ℝ E), y j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
          |Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b) y - D.R i g₀.inner a b y| ≤ δ := by
  classical
  -- The estimate for one fixed component `f = D.R i g₀.inner a b`.
  have hpt : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ y : Fin (Module.finrank ℝ E) → ℝ,
          (∀ j : Fin (Module.finrank ℝ E), y j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
            |Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b) y - D.R i g₀.inner a b y| ≤ δ := by
    intro i a b
    -- The uniform truncation estimate, applied to the smooth, compactly supported component.
    have hconv := Work.Diff.STE.Lead.truncDiff_tendsto_uniform
      (ι := Fin (Module.finrank ℝ E)) ρ hρ0 hρb hρc hρ1
      (D.R i g₀.inner a b)
      (D.R_contDiff i g₀.inner a b (hdg i) (hmat i a b))
      (D.R_support i g₀.inner a b) δ hδ
    filter_upwards [hconv] with ε hε y hy
    -- On the open cube the periodisation of the component is the component itself.
    have hper : (∑' m : Fin (Module.finrank ℝ E) → ℤ,
        ((D.R i g₀.inner a b (y + Work.Diff.STE.iVec m) : ℝ) : ℂ))
        = ((D.R i g₀.inner a b y : ℝ) : ℂ) := D.Rper_eq_R i g₀.inner a b hy
    have hnorm : ‖Work.Diff.STE.STruncC ρ ε (D.R i g₀.inner a b) y
        - ((D.R i g₀.inner a b y : ℝ) : ℂ)‖ ≤ δ := by
      have h := hε y
      rwa [hper] at h
    -- `STruncR` is the real part of `STruncC`, and the real part is `1`-Lipschitz.
    have hre : Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b) y
        = (Work.Diff.STE.STruncC ρ ε (D.R i g₀.inner a b) y).re := rfl
    rw [hre]
    calc |(Work.Diff.STE.STruncC ρ ε (D.R i g₀.inner a b) y).re - D.R i g₀.inner a b y|
        = |(Work.Diff.STE.STruncC ρ ε (D.R i g₀.inner a b) y
            - ((D.R i g₀.inner a b y : ℝ) : ℂ)).re| := by
          rw [Complex.sub_re, Complex.ofReal_re]
      _ ≤ ‖Work.Diff.STE.STruncC ρ ε (D.R i g₀.inner a b) y
            - ((D.R i g₀.inner a b y : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
      _ ≤ δ := hnorm
  -- Combine the finitely many components.
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro a
  rw [Filter.eventually_all]
  intro b
  exact hpt i a b

end Work.Diff.STE.B3
