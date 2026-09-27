import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.hptOfLevelYc
import Submission.Work.Mostow.isCompactHdistThickening

/-!
# Cusp cocompactness holds at *every* level as soon as it holds at one level

`CuspCocompact Γ ξ` says that the stabiliser `Γ_ξ` of the boundary point `ξ` acts on each
horosphere `busemann ξ · = t` with a compact fundamental set, i.e. that the quotient of each
horosphere by `Γ_ξ` is compact.  This file proves that it suffices to know this for a *single*
level `τ` (that is the form in which the geometric-finiteness chapters produce it): the
cocompactness at one level propagates to all levels.

## The geometry behind the proof

Write `lev ξ u = tpart u - ⟪u,ξ⟫ = exp (busemann ξ u)` for the horospherical level of `u`, and
`yc ξ u` for its flat coordinate on the horosphere (`QIDefs`).  For a level `D > 0` the point
`hptOf ξ y D` is the point of the horosphere of level `D` with flat coordinate `y`; in
particular `π_τ(u) := hptOf ξ (yc ξ u) (exp τ)` is the point of the level-`τ` horosphere which
lies on the geodesic through `u` towards `ξ`, with the *same* flat coordinate as `u`.

Two facts make the argument work:

* `hdist u (hptOf ξ (yc ξ u) D) = |log (lev ξ u) - log D|` — the "vertical" distance between
  the horospheres through `u` and through `π_τ(u)` (`hdist_hptOf_yc`, from the horospherical
  law of cosines `levYcFormula`);
* the `r`-neighbourhood of a compact set is compact (`isCompactHdistThickening`).

Given `u` with `busemann ξ u = t`, the hypothesis at level `τ` moves `π_τ(u)` into a fixed
compact `K` by an element `γ ∈ Γ_ξ`; since `γ` is an isometry preserving distances, `γ • u` is
within distance `|t - τ|` of `γ • π_τ(u) ∈ K`.  Hence every point of level `t` is
`Γ_ξ`-equivalent to a point of the *fixed* compact set
`{w | ∃ v ∈ K, hdist w v ≤ |t - τ|}`, which is what `CuspCocompact` requires.

No control on the Busemann cocycle of the stabiliser is needed: the constants
`|t - τ|` are allowed to depend on the level `t`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The normalised flat coordinate of `u` at `ξ` is orthogonal to `ξ`. -/
lemma inner_yc {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) : inner ℝ (yc ξ u) ξ = 0 := by
  have h1 : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have h : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
    rw [h, one_pow]
  simp only [yc, wc, real_inner_smul_left, inner_sub_left, h1, mul_one, sub_self, mul_zero]

/-- The point of the horosphere of `ξ` of level `D` whose flat coordinate equals that of `u`
lies on the geodesic from `u` to `ξ`, at distance `|log (lev ξ u) - log D|` from `u`. -/
lemma hdist_hptOf_yc {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) {D : ℝ} (hD : 0 < D) :
    hdist u (hptOf ξ (yc ξ u) D) = |Real.log (lev ξ u) - Real.log D| := by
  have hy : inner ℝ (yc ξ u) ξ = 0 := inner_yc hξ u
  obtain ⟨hlev, hyc, -⟩ := hptOfLevelYc ξ hξ hy hD
  have h1 : Real.cosh (hdist u (hptOf ξ (yc ξ u) D)) =
      Real.cosh (Real.log (lev ξ u) - Real.log D) := by
    rw [levYcFormula hξ u (hptOf ξ (yc ξ u) D), hlev, hyc, sub_self, norm_zero,
      zero_pow (by norm_num), mul_zero, add_zero,
      Real.log_div (ne_of_gt (lev_pos ξ hξ u)) (ne_of_gt hD)]
  calc hdist u (hptOf ξ (yc ξ u) D)
      = Real.arcosh (tpart u * tpart (hptOf ξ (yc ξ u) D) - inner ℝ u (hptOf ξ (yc ξ u) D)) := rfl
    _ = Real.arcosh (Real.cosh (hdist u (hptOf ξ (yc ξ u) D))) := by
          rw [← Work.Mostow.BdExt.cosh_hdist u (hptOf ξ (yc ξ u) D)]
    _ = Real.arcosh (Real.cosh (Real.log (lev ξ u) - Real.log D)) := by rw [h1]
    _ = Real.arcosh (Real.cosh |Real.log (lev ξ u) - Real.log D|) := by rw [← Real.cosh_abs]
    _ = |Real.log (lev ξ u) - Real.log D| := Real.arcosh_cosh (abs_nonneg _)

theorem cuspCocompactAllLevels (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (ξ : Submission.Mostow.E n)
    (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hstab : ∀ (γ : Γ), Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (τ : ℝ) (hτ : ∃ K : Set (Submission.Mostow.E n), IsCompact K ∧ ∀ u : Submission.Mostow.E n,
      Submission.Mostow.busemann ξ u = τ → ∃ γ : Γ,
        Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
          (γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u ∈ K) :
    Work.Mostow.CuspCocompact Γ ξ := by
  intro t
  obtain ⟨K, hKc, hK⟩ := hτ
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  refine ⟨{w : E n | ∃ v ∈ K, hdist w v ≤ |t - τ|},
    isCompactHdistThickening hI K hKc _, ?_⟩
  intro u hu
  have hbusπ : busemann ξ (hptOf ξ (yc ξ u) (Real.exp τ)) = τ := by
    have h := (hptOfLevelYc ξ hξ (inner_yc hξ u) (Real.exp_pos τ)).2.2
    rw [h, Real.log_exp]
  obtain ⟨γ, hγbd, hγK⟩ := hK _ hbusπ
  refine ⟨γ, hγbd, (γ : PO n 1) • hptOf ξ (yc ξ u) (Real.exp τ), hγK, ?_⟩
  rw [hI'.isom_smul, hdist_hptOf_yc hξ u (Real.exp_pos τ), lev_eq_exp hξ u, Real.log_exp,
    Real.log_exp, hu]

end

end Work.Mostow
