import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.hdistBasic
import Submission.Work.Mostow.minkLineDecomp

/-!
# `geodDetTwo`: the hyperboloid lift of a unit-speed geodesic

If `γ : ℝ → E n` is the arclength parametrisation of a geodesic line, i.e.
`hdist (γ s) (γ t) = |s - t|` for all `s t`, then its hyperboloid lift is the affine
combination of `hlift (γ 0)` and `hlift (γ 1)` given by the `cosh`-frame at the two points:

`hlift (γ s) = cosh s • hlift (γ 0) + sinh s • ((sinh 1)⁻¹ • (hlift (γ 1) - cosh 1 • hlift (γ 0)))`.

The argument is in two steps.
* Geometric input: the Minkowski pairing of two hyperboloid lifts is the `cosh`-kernel of the
  hyperbolic distance, `⟨hlift u, hlift v⟩ = -cosh (hdist u v)`.  Hence the hypothesis says that
  `X = hlift ∘ γ` has the two-point function `⟨X s, X t⟩ = -cosh (s - t)` which characterises the
  unit-speed line of the hyperboloid.
* The linear-algebra input `Work.Mostow.minkLineDecomp` (proved from the fact that a Minkowski
  null vector orthogonal to a timelike vector vanishes, and the `cosh`-frame computation
  `minkCoshFrame`) then identifies `X` with that line.
-/

namespace Work.Mostow

open Submission.Mostow

/-- The Minkowski form of `QIDefs` agrees with the `Hyper` version used for the chart. -/
private lemma mink_eq_hyperMink {n : ℕ} (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink x y = Hyper.mink x y := by
  rw [mink, Hyper.mink_apply]

/-- The `cosh`-kernel of the hyperbolic distance is the exponentiated distance,
`cc u v = cosh (hdist u v)` (in the chart, `cc u v = tpart u * tpart v - ⟪u,v⟫`). -/
private lemma cc_eq_cosh_hdist {n : ℕ} (u v : E n) : Hyper.cc u v = Real.cosh (hdist u v) := by
  rw [← Real.cosh_arcosh (one_le_cc u v), Hyper.hdist_eq_cc]

/-- The two-point function of the lifted geodesic: `⟨hlift (γ s), hlift (γ t)⟩ = -cosh (s - t)`. -/
private lemma mink_hlift_geod {n : ℕ} (γ : ℝ → E n)
    (hγ : ∀ s t : ℝ, hdist (γ s) (γ t) = |s - t|) (s t : ℝ) :
    Work.Mostow.mink (hlift (γ s)) (hlift (γ t)) = -Real.cosh (s - t) := by
  rw [mink_eq_hyperMink, Hyper.mink_eq_neg_cc, cc_eq_cosh_hdist, hγ s t, Real.cosh_abs]

theorem geodDetTwo {n : ℕ} (γ : ℝ → Submission.Mostow.E n)
    (hγ : ∀ s t : ℝ, Submission.Mostow.hdist (γ s) (γ t) = |s - t|) (s : ℝ) :
    Submission.Mostow.hlift (γ s) =
      Real.cosh s • Submission.Mostow.hlift (γ 0) +
        Real.sinh s • ((Real.sinh 1)⁻¹ •
          (Submission.Mostow.hlift (γ 1) - Real.cosh 1 • Submission.Mostow.hlift (γ 0))) :=
  minkLineDecomp n (fun u : ℝ => hlift (γ u)) (fun s t => mink_hlift_geod γ hγ s t) s

end Work.Mostow
