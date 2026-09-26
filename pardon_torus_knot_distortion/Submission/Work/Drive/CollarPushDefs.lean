import Mathlib
import Submission.Work.Bicollar.StdTorusTube
import Submission.Work.CoreTopology.pardonsI_mapHomeomorph
import Submission.Work.Drive.WPushDefs

/-!
# The collar push of a torus `ψ (F_std)`: definitions

For the standard torus of revolution `Σ = standard.carrier` of `ℝ³` we build an explicit
*level function* and an explicit *push*:

* `pushStd x δ` — a point near `x`, obtained by shifting the meridian radius of `x` by `δ`
  (through the tube coordinates of `Work.Bicollar`), damped so that the map is continuous on
  all of `ℝ³ × ℝ`;
* `levP ψ x = ‖meridVec (ψ.symm x)‖` — the meridian radius of the pull-back of `x`, whose
  level set `{1}` is exactly `ψ '' Σ`;
* `pushP ψ x δ = ψ (pushStd (ψ.symm x) δ)`.

The two damping functions

* `capF`, `capDamp r = capF r / r` — kill the horizontal displacement near the axis `{r = 0}`
  (where the longitude is not defined), and are `1` and `1/r` on `[1/2, 9/2]`;
* `cutDamp s = stdCut s / s` — the ratio of the cutoff `stdCut` of `Work.Drive.WPushDefs` to
  the meridian radius, killing the displacement near the core circle `{s = 0}`;

are all continuous, and every displacement is supported in the region where the meridian radius
lies in `(1/4, 3/2)`, so that the push is the exact flow of `∂/∂s` there.

The mathematical content (the level set, the continuity, and the four level properties) is
proved in the companion files.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive

open Work.CoreTopology

noncomputable section

/-! ## The horizontal damping

`capF r` is a continuous ramp which is `1` on `[1/2, 9/2]` and `0` for `r ≤ 1/4`; `capDamp r` is
`capF r / r`, i.e. `1 / r` on `[1/2, 9/2]` and `0` near `r = 0`. -/

/-- A continuous ramp in the horizontal radius, `1` on `[1/2, 9/2]`, `0` for `r ≤ 1/4`. -/
def capF (r : ℝ) : ℝ := max 0 (min 1 (min (4 * r - 1) (10 - 2 * r)))

theorem capF_nonneg (r : ℝ) : 0 ≤ capF r := le_max_left _ _

theorem capF_le_one (r : ℝ) : capF r ≤ 1 := max_le zero_le_one (min_le_left _ _)

@[fun_prop] theorem continuous_capF : Continuous capF := by
  unfold capF; fun_prop

theorem capF_eq_one {r : ℝ} (h1 : 1 / 2 ≤ r) (h2 : r ≤ 9 / 2) : capF r = 1 := by
  have ha : (1 : ℝ) ≤ 4 * r - 1 := by linarith
  have hb : (1 : ℝ) ≤ 10 - 2 * r := by linarith
  have hc : (1 : ℝ) ≤ min (4 * r - 1) (10 - 2 * r) := le_min ha hb
  rw [capF, min_eq_left hc, max_eq_right zero_le_one]

/-- `capDamp r = capF r / r`, extended by `0` at `r ≤ 1/4`: a continuous replacement for `1/r`
which vanishes near the axis. -/
def capDamp (r : ℝ) : ℝ := if r ≤ 1 / 4 then 0 else capF r / r

theorem capDamp_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ capDamp r := by
  rw [capDamp]; split_ifs with h
  · exact le_rfl
  · exact div_nonneg (capF_nonneg r) (by linarith)

theorem capDamp_le (r : ℝ) : capDamp r ≤ 4 := by
  rw [capDamp]; split_ifs with h
  · norm_num
  · rw [div_le_iff₀ (by linarith : (0 : ℝ) < r)]
    nlinarith [capF_le_one r, not_le.mp h]

theorem capDamp_eq_inv {r : ℝ} (h1 : 1 / 2 ≤ r) (h2 : r ≤ 9 / 2) : capDamp r = 1 / r := by
  rw [capDamp, if_neg (by linarith : ¬ r ≤ 1 / 4), capF_eq_one h1 h2, one_div]

theorem capDamp_eq_zero_of_le {r : ℝ} (hr : r ≤ 1 / 4) : capDamp r = 0 := by
  rw [capDamp, if_pos hr]

@[fun_prop] theorem continuous_capDamp : Continuous capDamp := by
  rw [show capDamp = fun r : ℝ => if r ≤ 1 / 4 then (0 : ℝ) else capF r / r from rfl]
  refine continuous_if ?_ continuousOn_const ?_
  · have hfr : frontier {r : ℝ | r ≤ 1 / 4} = {1 / 4} := by
      rw [show {r : ℝ | r ≤ 1 / 4} = Set.Iic (1 / 4) from rfl, frontier_Iic]
    rw [hfr]
    rintro r rfl
    norm_num [capF]
  · have hcl : closure {r : ℝ | ¬r ≤ 1 / 4} = Set.Ici (1 / 4) := by
      rw [show {r : ℝ | ¬r ≤ 1 / 4} = Set.Ioi (1 / 4) from by ext r; simp [not_le]]
      exact closure_Ioi _
    rw [hcl]
    exact continuous_capF.continuousOn.div continuousOn_id
      (fun r hr => by rw [Set.mem_Ici] at hr; linarith)

/-! ## The meridian damping

`cutDamp s = stdCut s / s`, extended by `0` at `s ≤ 1/4`. -/

/-- `stdCut s / s`, extended by `0` at `s ≤ 1/4`: a continuous replacement for `stdCut s / s`
valid also at the core circle `s = 0`. -/
def cutDamp (s : ℝ) : ℝ := if s ≤ 1 / 4 then 0 else stdCut s / s

theorem cutDamp_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ cutDamp s := by
  rw [cutDamp]; split_ifs with h
  · exact le_rfl
  · exact div_nonneg (stdCut_nonneg s) (by linarith)

theorem cutDamp_eq_div {s : ℝ} (hs : 0 < s) : cutDamp s = stdCut s / s := by
  rw [cutDamp]; split_ifs with h
  · rw [stdCut_eq_zero_of_le h, zero_div]
  · rfl

theorem cutDamp_eq_zero_of_le {s : ℝ} (hs : s ≤ 1 / 4) : cutDamp s = 0 := by
  rw [cutDamp, if_pos hs]

theorem cutDamp_eq_zero_of_ge {s : ℝ} (hs : 3 / 2 ≤ s) : cutDamp s = 0 := by
  rw [cutDamp]; split_ifs with h
  · rfl
  · rw [stdCut_eq_zero_of_ge hs, zero_div]

theorem cutDamp_eq_inv {s : ℝ} (h1 : 1 / 2 ≤ s) (h2 : s ≤ 5 / 4) : cutDamp s = 1 / s := by
  rw [cutDamp_eq_div (by linarith), stdCut_eq_one h1 h2, one_div]

@[fun_prop] theorem continuous_cutDamp : Continuous cutDamp := by
  rw [show cutDamp = fun s : ℝ => if s ≤ 1 / 4 then (0 : ℝ) else stdCut s / s from rfl]
  refine continuous_if ?_ continuousOn_const ?_
  · have hfr : frontier {s : ℝ | s ≤ 1 / 4} = {1 / 4} := by
      rw [show {s : ℝ | s ≤ 1 / 4} = Set.Iic (1 / 4) from rfl, frontier_Iic]
    rw [hfr]
    rintro s rfl
    rw [stdCut_eq_zero_of_le (le_refl _), zero_div]
  · have hcl : closure {s : ℝ | ¬s ≤ 1 / 4} = Set.Ici (1 / 4) := by
      rw [show {s : ℝ | ¬s ≤ 1 / 4} = Set.Ioi (1 / 4) from by ext s; simp [not_le]]
      exact closure_Ioi _
    rw [hcl]
    exact continuous_stdCut.continuousOn.div continuousOn_id
      (fun s hs => by rw [Set.mem_Ici] at hs; linarith)

/-! ## The standard push -/

/-- **The push of the standard torus**, in the explicit form used for continuity: the point whose
horizontal projection is `x` scaled by `λ = 1 + δ · cutDamp s · (1 - 2 capDamp r)` and whose
`z`-coordinate is scaled by `1 + δ · cutDamp s`, where `s = ‖meridVec x‖` and `r = horizRadius x`.

On the tube region with `1/4 < s < 3/2` this is exactly the point obtained by shifting the
meridian radius `s` by `δ · stdCut s`: its meridian vector is `(s + δ stdCut s)/s` times that
of `x`, and its longitude is unchanged. -/
def pushStd (x : R3) (δ : ℝ) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i.val = 0 then
      (1 + δ * cutDamp ‖meridVec x‖ * (1 - 2 * capDamp (horizRadius x))) * x 0
    else if i.val = 1 then
      (1 + δ * cutDamp ‖meridVec x‖ * (1 - 2 * capDamp (horizRadius x))) * x 1
    else (1 + δ * cutDamp ‖meridVec x‖) * x 2)

@[simp] theorem pushStd_apply_zero (x : R3) (δ : ℝ) :
    pushStd x δ 0 = (1 + δ * cutDamp ‖meridVec x‖ * (1 - 2 * capDamp (horizRadius x))) * x 0 := by
  rw [pushStd]; simp

@[simp] theorem pushStd_apply_one (x : R3) (δ : ℝ) :
    pushStd x δ 1 = (1 + δ * cutDamp ‖meridVec x‖ * (1 - 2 * capDamp (horizRadius x))) * x 1 := by
  rw [pushStd]; simp

@[simp] theorem pushStd_apply_two (x : R3) (δ : ℝ) :
    pushStd x δ 2 = (1 + δ * cutDamp ‖meridVec x‖) * x 2 := by
  rw [pushStd]; simp

theorem pushStd_zero (x : R3) : pushStd x 0 = x := by
  rw [WithLp.ext_iff]
  funext i
  fin_cases i <;> simp

/-- The push does nothing when the meridian radius is at most `1/4`. -/
theorem pushStd_eq_self_of_le {x : R3} {δ : ℝ} (h : ‖meridVec x‖ ≤ 1 / 4) : pushStd x δ = x := by
  rw [pushStd, WithLp.ext_iff]
  funext i
  fin_cases i <;> simp [cutDamp_eq_zero_of_le h]

/-- The push does nothing when the meridian radius is at least `3/2`. -/
theorem pushStd_eq_self_of_ge {x : R3} {δ : ℝ} (h : 3 / 2 ≤ ‖meridVec x‖) : pushStd x δ = x := by
  rw [pushStd, WithLp.ext_iff]
  funext i
  fin_cases i <;> simp [cutDamp_eq_zero_of_ge h]

/-! ## The transport to a torus `ψ (Σ)` -/

/-- The level function of the standard torus: the meridian radius. -/
def levStd (x : R3) : ℝ := ‖meridVec x‖

/-- The level function of the torus `ψ '' Σ`: the meridian radius of the pull-back. -/
def levP (ψ : R3 ≃ₜ R3) (x : R3) : ℝ := levStd (ψ.symm x)

/-- The push of the torus `ψ '' Σ`, transported from the standard push by `ψ`. -/
def pushP (ψ : R3 ≃ₜ R3) (x : R3) (δ : ℝ) : R3 := ψ (pushStd (ψ.symm x) δ)

theorem levP_eq_one_iff (ψ : R3 ≃ₜ R3) (x : R3) :
    levP ψ x = 1 ↔ x ∈ (ParamTorus.mapHomeomorph ψ).carrier := by
  have hΨ : ∀ Y : R3, Y ∈ standard.carrier ↔ ψ Y ∈ (ParamTorus.mapHomeomorph ψ).carrier :=
    fun Y => (mem_carrier_mapHomeomorph_iff ψ Y).symm
  rw [levP, levStd, norm_meridVec_eq_one_iff, hΨ]
  exact ⟨fun h => by simpa using h, fun h => by simpa using h⟩

theorem continuous_levP (ψ : R3 ≃ₜ R3) : Continuous (levP ψ) :=
  continuous_meridVec.norm.comp ψ.symm.continuous

theorem pushP_zero (ψ : R3 ≃ₜ R3) (x : R3) : pushP ψ x 0 = x := by
  rw [pushP, pushStd_zero, Homeomorph.apply_symm_apply]

theorem levP_pushP (ψ : R3 ≃ₜ R3) (x : R3) (δ : ℝ) :
    levP ψ (pushP ψ x δ) = levStd (pushStd (ψ.symm x) δ) := by
  rw [pushP, levP, Homeomorph.symm_apply_apply]

end

end Work.Drive
