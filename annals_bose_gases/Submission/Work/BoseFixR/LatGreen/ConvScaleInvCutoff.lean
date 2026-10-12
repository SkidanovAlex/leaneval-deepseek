import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

open Metric
open scoped Topology ContDiff

/-!
# `Work.BoseFixR.LatGreen.ConvScaleInvCutoff`

The smooth cutoff of the reciprocal of the renormalisation factor `c := convScale ℓ`, i.e. of
`(χ ⋆ χ)(·/ℓ)`.

`c ≥ 1/2` on `closedBall 0 R` (`Submission.BoseGases.convScale_ge_half_ball`, which uses
`R ≤ ℓ·chiR0`).  Continuity of `c` upgrades this to `c > 1/4` on a slightly larger closed ball
(`exists_add_pos_lt_of_closedBall`, by compactness), and then a smooth bump `φ` equal to `1` on
`closedBall 0 R` with support in that larger ball produces the globally `C¹` function
`F := φ · c⁻¹`, which agrees with `c⁻¹` on `closedBall 0 R` and satisfies `|F| ≤ 2` there.

This is the *smooth factor* fed into `Work.BoseFixR.LatGreen.RadialSmoothCosDecay` in the proof of
`Work.BoseFixR.LatGreen.W1funDecay`.
-/

/-- `Submission.BoseGases.convScale ℓ = (χ ⋆ χ)(·/ℓ)` is `C^∞`: it is the smooth `χ ⋆ χ`
(`Submission.BoseGases.conv_contDiff`) composed with the linear substitution `x ↦ ℓ⁻¹ • x`. -/
lemma convScale_contDiff (ℓ : ℝ) :
    ContDiff ℝ ∞ (Submission.BoseGases.convScale ℓ) := by
  unfold Submission.BoseGases.convScale
  exact Submission.BoseGases.conv_contDiff.comp (by fun_prop)

/-- **The `(R + δ)`-ball sits inside the closed `δ`-thickening of the `R`-ball** (`R ≥ 0`, `δ > 0`).
The nearest point of `closedBall 0 R` to `x` is the radial projection `x ↦ (R/‖x‖) • x`, at
distance `max (‖x‖ − R) 0 ≤ δ` from `x`. -/
lemma closedBall_add_subset_cthickening {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) :
    closedBall (0 : EuclideanSpace ℝ (Fin 3)) (R + δ) ⊆
      cthickening δ (closedBall (0 : EuclideanSpace ℝ (Fin 3)) R) := by
  intro x hx
  have hx' : ‖x‖ ≤ R + δ := by simpa [mem_closedBall, dist_eq_norm] using hx
  rcases le_or_gt ‖x‖ R with hle | hlt
  · exact mem_cthickening_of_dist_le x x δ _
      (by simpa [mem_closedBall, dist_eq_norm] using hle) (by rw [dist_self]; exact hδ.le)
  · -- radial projection onto the sphere of radius `R`
    have hxpos : 0 < ‖x‖ := lt_of_le_of_lt hR hlt
    have hy_mem : ((R / ‖x‖) • x) ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) R := by
      have hnorm : ‖(R / ‖x‖) • x‖ = R := by
        rw [norm_smul, Real.norm_of_nonneg (div_nonneg hR hxpos.le),
          div_mul_cancel₀ _ hxpos.ne']
      rw [mem_closedBall, dist_eq_norm, sub_zero, hnorm]
    refine mem_cthickening_of_dist_le x ((R / ‖x‖) • x) δ _ hy_mem ?_
    rw [dist_eq_norm]
    have hsplit : x - (R / ‖x‖) • x = (1 - R / ‖x‖) • x := by module
    rw [hsplit, norm_smul,
      Real.norm_of_nonneg (by
        have : R / ‖x‖ ≤ 1 := (div_le_one hxpos).2 hlt.le
        linarith)]
    have hmul : (1 - R / ‖x‖) * ‖x‖ = ‖x‖ - R := by
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hxpos.ne']
    rw [hmul]
    linarith

/-- **A strict lower bound on a closed ball extends to a slightly larger closed ball.**
If `f` is continuous and `a < f x` for `‖x‖ ≤ R` (`R ≥ 0`), then `a < f x` for `‖x‖ ≤ R + δ` for
some `δ > 0`: `{a < f}` is open and contains the compact ball `closedBall 0 R`, hence contains a
closed thickening of it (`IsCompact.exists_cthickening_subset_open`), which in turn contains the
slightly larger ball by `closedBall_add_subset_cthickening`. -/
lemma exists_add_pos_lt_of_closedBall {f : EuclideanSpace ℝ (Fin 3) → ℝ} {a R : ℝ}
    (hR : 0 ≤ R) (hf : Continuous f) (h : ∀ x, ‖x‖ ≤ R → a < f x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, ‖x‖ ≤ R + δ → a < f x := by
  have hK : closedBall (0 : EuclideanSpace ℝ (Fin 3)) R ⊆ {x | a < f x} :=
    fun x hx => h x (by simpa [mem_closedBall, dist_eq_norm] using hx)
  obtain ⟨δ, hδpos, hδsub⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) R).exists_cthickening_subset_open
      (isOpen_lt continuous_const hf) hK
  exact ⟨δ, hδpos, fun x hx => hδsub (closedBall_add_subset_cthickening hR hδpos
    (by simpa [mem_closedBall, dist_eq_norm] using hx))⟩

/-- **`φ · c⁻¹` is globally `C¹` if `c` is `C¹` and nonvanishing on the closed support of a smooth
bump `φ`.**  At a point `x` either `c x ≠ 0`, and then `φ · c⁻¹` is `C¹` there as a product of the
smooth `φ` with `c⁻¹` (`ContDiffAt.inv`), or `c x = 0`, and then `x` lies outside the closed support
of `φ`, on a neighbourhood of which `φ` vanishes identically, so that `φ · c⁻¹` is locally `0`. -/
lemma contDiff_one_mul_inv_of_tsupport_ne_zero {c : EuclideanSpace ℝ (Fin 3) → ℝ}
    {φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3))} (hc : ContDiff ℝ 1 c)
    (hφ : ∀ x ∈ tsupport (φ : EuclideanSpace ℝ (Fin 3) → ℝ), c x ≠ 0) :
    ContDiff ℝ 1 (fun x => (φ : EuclideanSpace ℝ (Fin 3) → ℝ) x * (c x)⁻¹) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : c x = 0
  · have hxnot : x ∉ tsupport (φ : EuclideanSpace ℝ (Fin 3) → ℝ) := fun h => hφ x h hx
    have hopen : IsOpen (tsupport (φ : EuclideanSpace ℝ (Fin 3) → ℝ))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    refine (contDiffAt_const (c := (0 : ℝ)) (x := x) (n := (1 : ℕ∞))).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hxnot] with y hy
    have hy0 : (φ : EuclideanSpace ℝ (Fin 3) → ℝ) y = 0 := by
      by_contra hne
      exact hy (subset_tsupport _ hne)
    simp [hy0]
  · exact (ContDiffBump.contDiff φ).contDiffAt.mul (hc.contDiffAt.inv hx)

/-- **A globally `C¹` function agreeing with `1/(χ⋆χ)(·/ℓ)` on `ball 0 R`.**

With `0 < ℓ` and `R ≤ ℓ·chiR0` (`Submission.BoseGases.chiR0`), there is
`F : ℝ³ → ℝ` with

* `ContDiff ℝ 1 F` (globally), and
* `F x = (Submission.BoseGases.convScale ℓ x)⁻¹` and `|F x| ≤ 2` for `‖x‖ ≤ R`.

This is the *smooth factor* fed into `Work.BoseFixR.LatGreen.RadialSmoothCosDecay`
in the proof of `Work.BoseFixR.LatGreen.W1funDecay`: `W₁ = g₀/(χ⋆χ)(·/ℓ)`, and
`g₀` is supported in `ball 0 R`, so replacing `1/(χ⋆χ)(·/ℓ)` by `F` does not
change `W₁` pointwise, while `F` is globally `C¹` even though
`1/(χ⋆χ)(·/ℓ)` is not (it blows up at the boundary of the support of `χ⋆χ`).

Route: `c := Submission.BoseGases.convScale ℓ = (conv3 χ χ) ∘ (ℓ⁻¹ • ·)` is
`C^∞` (`Submission.CubicChi.conv_contDiff`), and `c ≥ 1/2` on `closedBall 0 R`
(`Submission.BoseGases.convScale_ge_half_ball`, using `R ≤ ℓ·chiR0`); hence by
continuity `c ≥ 1/4` on some `closedBall 0 (R + δ)` (`δ > 0`; compactness).
Take a smooth bump `φ` with `φ ≡ 1` on `closedBall 0 R` and support in
`ball 0 (R + δ)` (a `ContDiffBump`), and set `F := φ · c⁻¹`. Then `F` agrees
with `c⁻¹` on `closedBall 0 R`, is globally `C¹` (at a point of `support φ` use
`c ≥ 1/4` there and smoothness of `c⁻¹` on `{c ≠ 0}`; outside `support φ` the
function vanishes on a neighbourhood), and `|F x| ≤ 2` on `closedBall 0 R`
because `c x ≥ 1/2` there. -/
theorem ConvScaleInvCutoff {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    ∃ F : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 F ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ R → F x = (Submission.BoseGases.convScale ℓ x)⁻¹) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ R → |F x| ≤ 2) := by
  have hc : ContDiff ℝ ∞ (Submission.BoseGases.convScale ℓ) := convScale_contDiff ℓ
  -- `c ≥ 1/2` on the ball, hence `c > 1/4` on a slightly larger ball
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin 3),
      ‖x‖ ≤ R + δ → (1 : ℝ)/4 < Submission.BoseGases.convScale ℓ x :=
    exists_add_pos_lt_of_closedBall hR.le hc.continuous
      (fun x hx => lt_of_lt_of_le (by norm_num : (1 : ℝ)/4 < 1/2)
        (Submission.BoseGases.convScale_ge_half_ball hℓ hR.le hRℓ hx))
  -- the smooth bump `φ ≡ 1` on `closedBall 0 R`, supported in `closedBall 0 (R + δ)`
  let φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) := ⟨R, R + δ, hR, by linarith⟩
  have hφrIn : φ.rIn = R := rfl
  have hφrOut : φ.rOut = R + δ := rfl
  have hφ_one : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ R →
      (φ : EuclideanSpace ℝ (Fin 3) → ℝ) x = 1 := by
    intro x hx
    exact ContDiffBump.one_of_mem_closedBall φ
      (by simpa [hφrIn, mem_closedBall, dist_eq_norm] using hx)
  have hφ_nz : ∀ x ∈ tsupport (φ : EuclideanSpace ℝ (Fin 3) → ℝ),
      Submission.BoseGases.convScale ℓ x ≠ 0 := by
    intro x hx
    rw [ContDiffBump.tsupport_eq φ, hφrOut] at hx
    exact ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1/4)
      (hδ x (by simpa [mem_closedBall, dist_eq_norm] using hx)))
  refine ⟨fun x => (φ : EuclideanSpace ℝ (Fin 3) → ℝ) x * (Submission.BoseGases.convScale ℓ x)⁻¹,
    contDiff_one_mul_inv_of_tsupport_ne_zero (hc.of_le (by simp)) hφ_nz, ?_, ?_⟩
  · intro x hx
    simp only [hφ_one x hx, one_mul]
  · intro x hx
    have hc1 : (1 : ℝ)/2 ≤ Submission.BoseGases.convScale ℓ x :=
      Submission.BoseGases.convScale_ge_half_ball hℓ hR.le hRℓ hx
    have hcpos : 0 < Submission.BoseGases.convScale ℓ x := by linarith
    have hinv : (Submission.BoseGases.convScale ℓ x)⁻¹ ≤ 2 := by
      have h := (inv_le_inv₀ hcpos (by norm_num : (0 : ℝ) < 1/2)).2 hc1
      simpa using h
    change |(φ : EuclideanSpace ℝ (Fin 3) → ℝ) x * (Submission.BoseGases.convScale ℓ x)⁻¹| ≤ 2
    rw [hφ_one x hx, one_mul, abs_of_nonneg (inv_nonneg.mpr hcpos.le)]
    exact hinv

end Work.BoseFixR.LatGreen
