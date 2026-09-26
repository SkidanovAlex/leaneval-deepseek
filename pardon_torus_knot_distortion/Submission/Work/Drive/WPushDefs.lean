import Submission.Work.Bicollar.StdTorusTube
import Submission.Work.Drive.Interfaces

/-!
# The collar push of a torus of the challenge

For the tori `F = ψ(F_std)` of the challenge we need an explicit way of moving a point of `ℝ³`
transversely across `F` while fixing `F` pointwise on "one side of the level": this is the
`push-off` used in the weak cut-and-paste of Pardon's Lemma 2.

The meridian radius `R x = ‖meridVec x‖` (with `meridVec x = ⟨r - 2, x 2⟩`, `r = √(x₀² + x₁²)`)
has level set `{R = 1}` equal to the standard torus (`norm_meridVec_eq_one_iff`) and is a genuine
normal coordinate on the tube region `tubeU = {0 < R < 2}`
(`Work.Bicollar.tubePt_reconstruct`).  We push a point at tube coordinates `(u, v, s)` to
`(u, v, s + δ)`:

* `stdPush x δ` — the push for the standard torus (identity outside the tube region, with a
  cutoff so that the push is continuous and small);
* `pushP ψ x δ` and `levP ψ x` — the transport of these to the torus `ψ(F_std)`.

The main facts are `levP_pushP` (the level changes by `δ`) and `levP_eq_one_iff`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive

open Classical
open Work.CoreTopology

noncomputable section

/-! ## The cutoff -/

/-- A continuous cutoff, `1` on `[1/2, 5/4]` and `0` outside `(1/4, 3/2)`. -/
def stdCut (t : ℝ) : ℝ := max 0 (min 1 (min (4 * t - 1) (6 - 4 * t)))

theorem stdCut_nonneg (t : ℝ) : 0 ≤ stdCut t := le_max_left _ _

theorem stdCut_le_one (t : ℝ) : stdCut t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem stdCut_eq_one {t : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 5 / 4) : stdCut t = 1 := by
  have ha : (1 : ℝ) ≤ 4 * t - 1 := by linarith
  have hb : (1 : ℝ) ≤ 6 - 4 * t := by linarith
  have hc : (1 : ℝ) ≤ min (4 * t - 1) (6 - 4 * t) := le_min ha hb
  rw [stdCut, min_eq_left hc, max_eq_right zero_le_one]

theorem stdCut_eq_zero_of_le {t : ℝ} (h : t ≤ 1 / 4) : stdCut t = 0 := by
  have ha : 4 * t - 1 ≤ 0 := by linarith
  have h1 : min 1 (min (4 * t - 1) (6 - 4 * t)) ≤ min (4 * t - 1) (6 - 4 * t) := min_le_right _ _
  have h2 : min (4 * t - 1) (6 - 4 * t) ≤ 4 * t - 1 := min_le_left _ _
  have : min 1 (min (4 * t - 1) (6 - 4 * t)) ≤ 0 := le_trans h1 (le_trans h2 ha)
  rw [stdCut, max_eq_left this]

theorem stdCut_eq_zero_of_ge {t : ℝ} (h : 3 / 2 ≤ t) : stdCut t = 0 := by
  have hb : 6 - 4 * t ≤ 0 := by linarith
  have h1 : min 1 (min (4 * t - 1) (6 - 4 * t)) ≤ min (4 * t - 1) (6 - 4 * t) := min_le_right _ _
  have h2 : min (4 * t - 1) (6 - 4 * t) ≤ 6 - 4 * t := min_le_right _ _
  have : min 1 (min (4 * t - 1) (6 - 4 * t)) ≤ 0 := le_trans h1 (le_trans h2 hb)
  rw [stdCut, max_eq_left this]

theorem continuous_stdCut : Continuous stdCut := by
  unfold stdCut
  fun_prop

/-! ## The push of the standard torus -/

/-- **The push-off of the standard torus**, in the tube coordinates: the point whose horizontal
projection is `(2 + t (r-2)/s) · (x₀,x₁)/r` and whose third coordinate is `t x₂/s`, where
`r = horizRadius x`, `s = ‖meridVec x‖` and `t = s + δ·stdCut s`.  Outside the tube region the
point is left alone. -/
noncomputable def stdPush (x : R3) (δ : ℝ) : R3 :=
  if x ∈ Work.Bicollar.tubeU then
    let s := ‖meridVec x‖
    let r := horizRadius x
    let t := s + δ * stdCut s
    WithLp.toLp 2 (fun i : Fin 3 =>
      if i.val = 0 then (2 + t * (r - 2) / s) * (x 0 / r)
      else if i.val = 1 then (2 + t * (r - 2) / s) * (x 1 / r)
      else t * (x 2 / s))
  else x

theorem stdPush_of_mem {x : R3} (hx : x ∈ Work.Bicollar.tubeU) (δ : ℝ) :
    stdPush x δ = WithLp.toLp 2 (fun i : Fin 3 =>
      if i.val = 0 then (2 + (‖meridVec x‖ + δ * stdCut ‖meridVec x‖) * (horizRadius x - 2) /
          ‖meridVec x‖) * (x 0 / horizRadius x)
      else if i.val = 1 then (2 + (‖meridVec x‖ + δ * stdCut ‖meridVec x‖) * (horizRadius x - 2) /
          ‖meridVec x‖) * (x 1 / horizRadius x)
      else (‖meridVec x‖ + δ * stdCut ‖meridVec x‖) * (x 2 / ‖meridVec x‖)) := by
  rw [stdPush]
  rw [if_pos hx]

theorem stdPush_of_notMem {x : R3} (hx : x ∉ Work.Bicollar.tubeU) (δ : ℝ) : stdPush x δ = x := by
  rw [stdPush]
  rw [if_neg hx]

theorem stdPush_apply_zero {x : R3} (hx : x ∈ Work.Bicollar.tubeU) (δ : ℝ) :
    stdPush x δ 0 =
      (2 + (‖meridVec x‖ + δ * stdCut ‖meridVec x‖) * (horizRadius x - 2) / ‖meridVec x‖) *
        (x 0 / horizRadius x) := by
  rw [stdPush_of_mem hx]
  simp

theorem stdPush_apply_one {x : R3} (hx : x ∈ Work.Bicollar.tubeU) (δ : ℝ) :
    stdPush x δ 1 =
      (2 + (‖meridVec x‖ + δ * stdCut ‖meridVec x‖) * (horizRadius x - 2) / ‖meridVec x‖) *
        (x 1 / horizRadius x) := by
  rw [stdPush_of_mem hx]
  simp

theorem stdPush_apply_two {x : R3} (hx : x ∈ Work.Bicollar.tubeU) (δ : ℝ) :
    stdPush x δ 2 = (‖meridVec x‖ + δ * stdCut ‖meridVec x‖) * (x 2 / ‖meridVec x‖) := by
  rw [stdPush_of_mem hx]
  simp

end

end Work.Drive
