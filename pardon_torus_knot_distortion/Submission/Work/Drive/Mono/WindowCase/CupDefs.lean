import Mathlib
import Submission.Work.Drive.Mono.CylRegionDefs
import Submission.Work.CoreTopology.Disk

/-!
# The cup over a plane disc: vocabulary

Given a plane disc `K = range e` (parametrised by the closed unit disc `𝔻 ⊆ ℂ`) and a continuous
nonnegative function `g` on `K`, this file sets up the *direction dependent* parametrisation of the
cup

`{P : ℝ³ | cproj P ∈ K ∧ clast P = 0} ∪ {P : ℝ³ | cproj P ∈ frontier K ∧ 0 ≤ clast P ∧
clast P ≤ g (cproj P)}`

by the closed unit disc.  The naive collar-aligned map fails to be injective where `g` vanishes on
the frontier (the whole collar fibre collapses onto the base point and collides with the inner
disc), so the threshold between the "bottom" branch and the "wall" branch is made **direction
dependent**:

* `cupDir z` is the radial projection of `z` onto the unit circle (a point of the disc; `0` at the
  origin);
* `cupG e g z = 1/2 + 1/(2 * (1 + g (e (cupDir z))))` is the threshold, which equals `1` exactly
  when `g` vanishes at the boundary point `e (cupDir z)`;
* `cupE e g z` is the bottom point `e (z / max (G z) ‖z‖)` at height `0` when `‖z‖ ≤ cupG e g z`,
  and otherwise the wall point `e (cupDir z)` at height
  `g (e (cupDir z)) * ((‖z‖ - G z) / (1 - G z)) ∈ [0, g (e (cupDir z))]`.

The two branches agree on the switch `‖z‖ = cupG e g z`, because there `z / max (G z) ‖z‖ =
cupDir z` and the height is `0`.
-/

namespace Work.Drive.Mono.WindowCase

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

local notation "𝔻" => Metric.closedBall (0 : ℂ) 1

/-! ## Elementary real facts -/

theorem div_self_le_one {r : ℝ} (hr : 0 ≤ r) : r / r ≤ 1 := by
  rcases eq_or_lt_of_le hr with h | h
  · rw [← h, zero_div]; norm_num
  · rw [div_self (ne_of_gt h)]

theorem div_max_le_one {r G : ℝ} (hr : 0 ≤ r) : r / max G r ≤ 1 := by
  rcases eq_or_lt_of_le (le_max_right G r : r ≤ max G r) with h | h
  · rw [← h]
    exact div_self_le_one hr
  · rw [div_le_one (lt_of_le_of_lt hr h)]
    exact le_max_right G r

/-! ## The radial direction -/

/-- The radial projection of a point of the closed unit disc onto the unit circle, regarded again
as a point of the disc (i.e. `z / ‖z‖`; the value at the origin is `0`). -/
def cupDir (z : 𝔻) : 𝔻 :=
  ⟨(z : ℂ) / ‖(z : ℂ)‖, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_div,
      Complex.norm_of_nonneg (norm_nonneg _)]
    exact div_self_le_one (norm_nonneg _)⟩

@[simp] theorem cupDir_coe (z : 𝔻) : (cupDir z : ℂ) = (z : ℂ) / ‖(z : ℂ)‖ := rfl

theorem norm_cupDir_of_ne_zero {z : 𝔻} (hz : (z : ℂ) ≠ 0) : ‖(cupDir z : ℂ)‖ = 1 := by
  rw [cupDir_coe, norm_div, Complex.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr hz)]

theorem cupDir_eq_self {z : 𝔻} (hz : ‖(z : ℂ)‖ = 1) : cupDir z = z := by
  refine Subtype.ext ?_
  rw [cupDir_coe, hz]
  simp

/-! ## The direction dependent threshold -/

/-- The direction dependent threshold `G z = 1/2 + 1/(2 * (1 + g (e (cupDir z))))`.  It lies in
`(1/2, 1]` as soon as `g ≥ 0` on the image of `e`, and it equals `1` exactly where `g` vanishes at
the boundary point `e (cupDir z)`. -/
def cupG (e : C(𝔻, EuclideanSpace ℝ (Fin 2))) (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (z : 𝔻) : ℝ :=
  1 / 2 + 1 / (2 * (1 + g (e (cupDir z))))

theorem cupG_half_lt {e : C(𝔻, EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    {z : 𝔻} (hm : 0 ≤ g (e (cupDir z))) : 1 / 2 < cupG e g z := by
  have hpos : 0 < 1 / (2 * (1 + g (e (cupDir z)))) := by positivity
  simp only [cupG]
  linarith

theorem cupG_pos {e : C(𝔻, EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    {z : 𝔻} (hm : 0 ≤ g (e (cupDir z))) : 0 < cupG e g z :=
  lt_trans (by norm_num) (cupG_half_lt hm)

theorem cupG_le_one {e : C(𝔻, EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    {z : 𝔻} (hm : 0 ≤ g (e (cupDir z))) : cupG e g z ≤ 1 := by
  have h2 : (2 : ℝ) ≤ 2 * (1 + g (e (cupDir z))) := by linarith
  have hpos : 0 < 2 * (1 + g (e (cupDir z))) := by linarith
  have hle : 1 / (2 * (1 + g (e (cupDir z)))) ≤ 1 / 2 := by
    have := one_div_le_one_div_of_le (show (0:ℝ) < 2 by norm_num) h2
    linarith
  simp only [cupG]
  linarith

theorem cupG_eq_one_iff {e : C(𝔻, EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    {z : 𝔻} (hm : 0 ≤ g (e (cupDir z))) : cupG e g z = 1 ↔ g (e (cupDir z)) = 0 := by
  have hpos : 0 < 2 * (1 + g (e (cupDir z))) := by linarith
  constructor
  · intro h
    have h' : 1 / (2 * (1 + g (e (cupDir z)))) = 1 / 2 := by
      simp only [cupG] at h; linarith
    rw [div_eq_div_iff (ne_of_gt hpos) (by norm_num)] at h'
    linarith
  · intro h
    simp only [cupG, h]
    norm_num

/-! ## The two branches -/

/-- The point of the disc used by the bottom branch: `z / max (G z) ‖z‖` (the clamping by `‖z‖`
keeps it inside the disc for *every* `z`, which makes the bottom branch globally continuous). -/
def cupScaled (e : C(𝔻, EuclideanSpace ℝ (Fin 2))) (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (z : 𝔻) : 𝔻 :=
  ⟨(z : ℂ) / max (cupG e g z) ‖(z : ℂ)‖, by
    have hM : (0 : ℝ) ≤ max (cupG e g z) ‖(z : ℂ)‖ :=
      le_trans (norm_nonneg _) (le_max_right _ _)
    rw [Metric.mem_closedBall, dist_zero_right, norm_div, Complex.norm_of_nonneg hM]
    exact div_max_le_one (norm_nonneg _)⟩

@[simp] theorem cupScaled_coe (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → ℝ) (z : 𝔻) :
    (cupScaled e g z : ℂ) = (z : ℂ) / max (cupG e g z) ‖(z : ℂ)‖ := rfl

theorem cupScaled_of_le {e : C(𝔻, EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} {z : 𝔻} (h : ‖(z : ℂ)‖ ≤ cupG e g z) :
    (cupScaled e g z : ℂ) = (z : ℂ) / cupG e g z := by
  rw [cupScaled_coe, max_eq_left h]

/-- The bottom branch: the point `e (cupScaled e g z)` of `K` at height `0`. -/
def cupBottom (e : C(𝔻, EuclideanSpace ℝ (Fin 2))) (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (z : 𝔻) : EuclideanSpace ℝ (Fin 3) :=
  cmk (e (cupScaled e g z)) 0

/-- The wall branch: the boundary point `e (cupDir z)` at the height
`g (e (cupDir z)) * ((‖z‖ - G z) / (1 - G z))`. -/
def cupWall (e : C(𝔻, EuclideanSpace ℝ (Fin 2))) (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (z : 𝔻) : EuclideanSpace ℝ (Fin 3) :=
  cmk (e (cupDir z))
    (g (e (cupDir z)) * ((‖(z : ℂ)‖ - cupG e g z) / (1 - cupG e g z)))

/-- **The collapse-aware parametrisation of the cup.** -/
def cupE (e : C(𝔻, EuclideanSpace ℝ (Fin 2))) (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (z : 𝔻) : EuclideanSpace ℝ (Fin 3) :=
  if ‖(z : ℂ)‖ ≤ cupG e g z then cupBottom e g z else cupWall e g z

theorem cupE_of_le {e : C(𝔻, EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    {z : 𝔻} (h : ‖(z : ℂ)‖ ≤ cupG e g z) : cupE e g z = cupBottom e g z := if_pos h

theorem cupE_of_gt {e : C(𝔻, EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    {z : 𝔻} (h : cupG e g z < ‖(z : ℂ)‖) : cupE e g z = cupWall e g z :=
  if_neg (not_le.mpr h)

@[simp] theorem cproj_cupBottom (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → ℝ) (z : 𝔻) :
    cproj (cupBottom e g z) = e (cupScaled e g z) := cproj_cmk _ _

@[simp] theorem clast_cupBottom (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → ℝ) (z : 𝔻) : clast (cupBottom e g z) = 0 := clast_cmk _ _

@[simp] theorem cproj_cupWall (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → ℝ) (z : 𝔻) :
    cproj (cupWall e g z) = e (cupDir z) := cproj_cmk _ _

@[simp] theorem clast_cupWall (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → ℝ) (z : 𝔻) :
    clast (cupWall e g z) =
      g (e (cupDir z)) * ((‖(z : ℂ)‖ - cupG e g z) / (1 - cupG e g z)) := clast_cmk _ _

theorem cupE_eq_cmk_bottom {e : C(𝔻, EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} {z : 𝔻} (h : ‖(z : ℂ)‖ ≤ cupG e g z) :
    cupE e g z = cmk (e (cupScaled e g z)) 0 := by
  rw [cupE_of_le h]; rfl

theorem cupE_eq_cmk_wall {e : C(𝔻, EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} {z : 𝔻} (h : cupG e g z < ‖(z : ℂ)‖) :
    cupE e g z = cmk (e (cupDir z))
      (g (e (cupDir z)) * ((‖(z : ℂ)‖ - cupG e g z) / (1 - cupG e g z))) := by
  rw [cupE_of_gt h]; rfl

/-- On the switch `‖z‖ = G z` the two branches agree: both give `e (cupDir z)` at height `0`. -/
theorem cupBottom_eq_cupWall_of_eq {e : C(𝔻, EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → ℝ} {z : 𝔻} (h : ‖(z : ℂ)‖ = cupG e g z) :
    cupBottom e g z = cupWall e g z := by
  refine (cmk_eq_cmk_iff _ _ _ _).mpr ⟨?_, ?_⟩
  · refine congrArg e (Subtype.ext ?_)
    rw [cupScaled_coe, cupDir_coe, max_eq_left (le_of_eq h), ← h]
  · simp [h]

end

end Work.Drive.Mono.WindowCase
