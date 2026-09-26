import Mathlib
import Submission.Work.Drive.EpsForm.WaypointDesign
import Submission.Work.Drive.EpsForm.WaypointDesign2
import Submission.Work.CoreTopology.Disk
import Submission.Work.CoreTopology.standardCurve_one_one_simple

/-!
# The curve `κ` of `Work.Drive.EpsForm.DatumCore`

The curve `κ` is parametrised through its lift to the parameter plane.  With the
`2π`-periodic triangular wave `kapLam s = |sin (s/2)|`, which takes `[0,π]` increasingly
onto `[0,1]` and `[π,2π]` decreasingly back to `0`, the longitude parameter is
`kapTheta s = u0 + (v0-u0) * kapLam s` and the meridian parameter is
`kapPhi s = phLift (kapTheta s)` when `sin s > 0` and `phLift (kapTheta s) + dlt (kapTheta s)`
when `sin s ≤ 0`.  The two branches differ by `dlt`, which vanishes exactly at the critical
points `s ∈ πℤ` of the wave, so `kapPhi` is continuous (and `2π`-periodic).  The curve
`kapGamma s = torusMap (kapTheta s) (kapPhi s)` therefore traverses, for `s ∈ [0,π]`, the
*lower* chord `t ↦ eFunX t (sig1 t)` and, for `s ∈ [π,2π]`, the *upper* chord
`t ↦ eFunX t (sig2 t)` backwards; it is a simple inessential closed curve of the standard
torus (proved in the separate files `kapGamma_injOn` and `kapCurve_not_essential`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.EpsForm

noncomputable section

def kapLam (s : ℝ) : ℝ := |Real.sin (s / 2)|
def kapTheta (s : ℝ) : ℝ := u0 + (v0 - u0) * kapLam s
def kapPhi (s : ℝ) : ℝ :=
  if 0 < Real.sin s then phLift (kapTheta s) else phLift (kapTheta s) + dlt (kapTheta s)
def kapGamma (s : ℝ) : R3 := Work.Core.torusMap (kapTheta s) (kapPhi s)

theorem eFun_apply_zero (t s : ℝ) : eFun t s 0 = (2 + (profW t s).1) * Real.cos t := by
  simp only [eFun, WithLp.ofLp_toLp]; simp
theorem eFun_apply_one (t s : ℝ) : eFun t s 1 = (2 + (profW t s).1) * Real.sin t := by
  simp only [eFun, WithLp.ofLp_toLp]; simp
theorem eFun_apply_two (t s : ℝ) : eFun t s 2 = (profW t s).2 := by
  simp only [eFun, WithLp.ofLp_toLp]; simp

theorem eFun_eq_iff (t s t' s' : ℝ) :
    eFun t s = eFun t' s' ↔
      (2 + (profW t s).1) * Real.cos t = (2 + (profW t' s').1) * Real.cos t' ∧
      (2 + (profW t s).1) * Real.sin t = (2 + (profW t' s').1) * Real.sin t' ∧
      (profW t s).2 = (profW t' s').2 := by
  constructor
  · intro h
    exact ⟨by rw [← eFun_apply_zero t s, ← eFun_apply_zero t' s', h],
      by rw [← eFun_apply_one t s, ← eFun_apply_one t' s', h],
      by rw [← eFun_apply_two t s, ← eFun_apply_two t' s', h]⟩
  · rintro ⟨h0, h1, h2⟩
    exact WithLp.ofLp_injective 2 (by
      funext i
      fin_cases i
      · simpa [eFun, WithLp.ofLp_toLp] using h0
      · simpa [eFun, WithLp.ofLp_toLp] using h1
      · simpa [eFun, WithLp.ofLp_toLp] using h2)

theorem continuous_kapLam : Continuous kapLam := by unfold kapLam; fun_prop
theorem kapLam_nonneg (s : ℝ) : 0 ≤ kapLam s := abs_nonneg _
theorem kapLam_le_one (s : ℝ) : kapLam s ≤ 1 :=
  abs_le.mpr ⟨by linarith [Real.neg_one_le_sin (s / 2)], Real.sin_le_one (s / 2)⟩
theorem kapLam_periodic (s : ℝ) : kapLam (s + 2 * Real.pi) = kapLam s := by
  unfold kapLam
  rw [show (s + 2 * Real.pi) / 2 = s / 2 + Real.pi by ring, Real.sin_add_pi, abs_neg]

theorem kapLam_eq_zero_or_one_of_sin_eq_zero {s : ℝ} (h : Real.sin s = 0) :
    kapLam s = 0 ∨ kapLam s = 1 := by
  have h2 : Real.sin (s / 2) = 0 ∨ Real.cos (s / 2) = 0 := by
    have hsin : Real.sin s = 2 * (Real.sin (s / 2) * Real.cos (s / 2)) := by
      conv_lhs => rw [show s = 2 * (s / 2) by ring]
      rw [Real.sin_two_mul]; ring
    rw [hsin] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (by norm_num)
    · exact mul_eq_zero.mp h'
  unfold kapLam
  rcases h2 with h2 | h2
  · left; rw [h2, abs_zero]
  · right
    have hs2 : Real.sin (s / 2) ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq (s / 2)]
    have habs : |Real.sin (s / 2)| ^ 2 = 1 := by rw [sq_abs, hs2]
    nlinarith [abs_nonneg (Real.sin (s / 2))]

theorem continuous_kapTheta : Continuous kapTheta :=
  continuous_const.add (continuous_const.mul continuous_kapLam)

theorem kapTheta_periodic (s : ℝ) : kapTheta (s + 2 * Real.pi) = kapTheta s := by
  unfold kapTheta; rw [kapLam_periodic]

theorem kapTheta_mem (s : ℝ) : kapTheta s ∈ Set.Icc u0 v0 := by
  have h1 : 0 ≤ kapLam s := kapLam_nonneg s
  have h2 : kapLam s ≤ 1 := kapLam_le_one s
  have hlen : 0 < v0 - u0 := by rw [v0_sub_u0]; positivity
  constructor <;> unfold kapTheta <;> nlinarith

theorem kapTheta_zero : kapTheta 0 = u0 := by
  unfold kapTheta kapLam; rw [zero_div, Real.sin_zero, abs_zero, mul_zero, add_zero]

theorem kapTheta_pi : kapTheta Real.pi = v0 := by
  unfold kapTheta kapLam
  rw [Real.sin_pi_div_two, abs_one, mul_one]; ring

theorem neg_pi_lt_kapTheta (s : ℝ) : -Real.pi < kapTheta s := by
  have h := kapTheta_mem s
  have h1 : u0 = -(2 * Real.pi) / 3 := rfl
  rw [h1] at h; linarith [h.1, Real.pi_pos]

theorem kapTheta_le_pi (s : ℝ) : kapTheta s ≤ Real.pi := by
  have h := kapTheta_mem s
  have h1 : v0 = (2 * Real.pi) / 3 := rfl
  rw [h1] at h; linarith [h.2, Real.pi_pos]

theorem kapTheta_eq_u0_or_v0_of_sin_eq_zero {s : ℝ} (h : Real.sin s = 0) :
    kapTheta s = u0 ∨ kapTheta s = v0 := by
  rcases kapLam_eq_zero_or_one_of_sin_eq_zero h with h' | h'
  · left; unfold kapTheta; rw [h', mul_zero, add_zero]
  · right; unfold kapTheta; rw [h', mul_one]; ring

theorem kapPhi_agrees_of_sin_eq_zero {s : ℝ} (h : Real.sin s = 0) :
    phLift (kapTheta s) = phLift (kapTheta s) + dlt (kapTheta s) := by
  rcases kapTheta_eq_u0_or_v0_of_sin_eq_zero h with h' | h'
  · rw [h', dlt_u0, add_zero]
  · rw [h', dlt_v0, add_zero]

theorem continuous_phLift : Continuous phLift := by
  unfold phLift
  exact (continuous_id.sub ((continuous_const.mul (continuous_id.sub continuous_const)).div_const _))

theorem kapPhi_of_pos {s : ℝ} (h : 0 < Real.sin s) : kapPhi s = phLift (kapTheta s) := by
  unfold kapPhi; rw [if_pos h]

theorem kapPhi_of_nonpos {s : ℝ} (h : Real.sin s ≤ 0) :
    kapPhi s = phLift (kapTheta s) + dlt (kapTheta s) := by
  unfold kapPhi; rw [if_neg (not_lt.mpr h)]

theorem kapPhi_eq_left {s : ℝ} (h : 0 ≤ Real.sin s) : kapPhi s = phLift (kapTheta s) := by
  rcases lt_or_eq_of_le h with h' | h'
  · exact kapPhi_of_pos h'
  · rw [kapPhi_of_nonpos (le_of_eq h'.symm)]
    exact (kapPhi_agrees_of_sin_eq_zero h'.symm).symm

theorem continuous_kapPhi : Continuous kapPhi := by
  rw [← continuousOn_univ]
  have hA : ContinuousOn kapPhi {s : ℝ | 0 ≤ Real.sin s} :=
    (continuous_phLift.comp continuous_kapTheta).continuousOn.congr
      (fun s hs => by rw [Function.comp_apply]; exact (kapPhi_eq_left hs))
  have hB : ContinuousOn kapPhi {s : ℝ | Real.sin s ≤ 0} :=
    ((continuous_phLift.comp continuous_kapTheta).add
      (continuous_dlt.comp continuous_kapTheta)).continuousOn.congr
      (fun s hs => by
        rw [Pi.add_apply, Function.comp_apply, Function.comp_apply]
        exact (kapPhi_of_nonpos hs))
  have h := hA.union_of_isClosed hB (isClosed_Ici.preimage Real.continuous_sin)
    (isClosed_Iic.preimage Real.continuous_sin)
  rw [show {s : ℝ | 0 ≤ Real.sin s} ∪ {s : ℝ | Real.sin s ≤ 0} = Set.univ from
    Set.eq_univ_of_forall fun s => le_total 0 (Real.sin s)] at h
  exact h

theorem kapPhi_periodic (s : ℝ) : kapPhi (s + 2 * Real.pi) = kapPhi s := by
  unfold kapPhi
  rw [kapTheta_periodic, Real.sin_periodic s]

theorem continuous_kapGamma : Continuous kapGamma := by
  have hp : Continuous fun s : ℝ => (kapTheta s, kapPhi s) :=
    continuous_kapTheta.prodMk continuous_kapPhi
  have h := Continuous.comp Work.CoreTopology.torusMap_continuous hp
  exact h

theorem kapGamma_periodic (s : ℝ) : kapGamma (s + 2 * Real.pi) = kapGamma s := by
  unfold kapGamma; rw [kapTheta_periodic, kapPhi_periodic]

def kapCurve : Work.CoreTopology.ClosedCurve Work.CoreTopology.standard where
  γ := kapGamma
  cont := continuous_kapGamma
  periodic := kapGamma_periodic
  mem := fun s => ⟨(kapTheta s, kapPhi s), rfl⟩


@[simp] theorem kapCurve_gamma : kapCurve.γ = kapGamma := rfl

theorem kapLam_periodic' : Function.Periodic kapLam (2 * Real.pi) := kapLam_periodic
theorem kapTheta_periodic' : Function.Periodic kapTheta (2 * Real.pi) := kapTheta_periodic
theorem kapPhi_periodic' : Function.Periodic kapPhi (2 * Real.pi) := kapPhi_periodic
theorem kapGamma_periodic' : Function.Periodic kapGamma (2 * Real.pi) := kapGamma_periodic

/-! ## The wave on `[0,2π]` -/

theorem kapLam_eq_sin {s : ℝ} (h1 : 0 ≤ s) (h2 : s ≤ 2 * Real.pi) :
    kapLam s = Real.sin (s / 2) := by
  unfold kapLam
  rw [abs_of_nonneg]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

theorem kapTheta_eq_sin {s : ℝ} (h1 : 0 ≤ s) (h2 : s ≤ 2 * Real.pi) :
    kapTheta s = u0 + (v0 - u0) * Real.sin (s / 2) := by
  unfold kapTheta; rw [kapLam_eq_sin h1 h2]


/-! ## The two preimages of a point of the chord range under the triangular wave -/

/-- For `t` in the open chord range there is `s ∈ (0,π)` with `kapTheta s = t` (the rising
branch of the wave); there `sin s > 0`, so the tube angle is `phLift t`. -/
theorem exists_kapTheta_eq_of_mem_Ioo {t : ℝ} (ht : t ∈ Set.Ioo u0 v0) :
    ∃ s ∈ Set.Ioo (0 : ℝ) Real.pi, kapTheta s = t ∧ 0 < Real.sin s := by
  have hlen : 0 < v0 - u0 := by rw [v0_sub_u0]; positivity
  set x : ℝ := (t - u0) / (v0 - u0) with hx
  have hx0 : 0 < x := div_pos (by linarith [ht.1]) hlen
  have hx1 : x < 1 := (div_lt_one hlen).mpr (by linarith [ht.2])
  have har0 : 0 < Real.arcsin x := Real.arcsin_pos.mpr hx0
  have har1 : Real.arcsin x < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hx1
  have hsin : Real.sin (Real.arcsin x) = x :=
    Real.sin_arcsin (by linarith) (le_of_lt hx1)
  refine ⟨2 * Real.arcsin x, ⟨by linarith, by linarith [Real.pi_pos]⟩, ?_, ?_⟩
  · rw [kapTheta_eq_sin (by linarith) (by linarith [Real.pi_pos]),
      show 2 * Real.arcsin x / 2 = Real.arcsin x by ring, hsin, hx]
    field_simp
    ring
  · have hcos : 0 < Real.cos (Real.arcsin x) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith [Real.pi_pos]⟩
    rw [Real.sin_two_mul, hsin]
    nlinarith

/-- For `t` in the open chord range there is `s ∈ (π,2π)` with `kapTheta s = t` (the
falling branch of the wave); there `sin s < 0`, so the tube angle is `phLift t + dlt t`. -/
theorem exists_kapTheta_eq_of_mem_Ioo' {t : ℝ} (ht : t ∈ Set.Ioo u0 v0) :
    ∃ s ∈ Set.Ioo Real.pi (2 * Real.pi), kapTheta s = t ∧ Real.sin s < 0 := by
  obtain ⟨s, hs, hT, hsin⟩ := exists_kapTheta_eq_of_mem_Ioo ht
  refine ⟨2 * Real.pi - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_, ?_⟩
  · simp only [kapTheta] at hT ⊢
    unfold kapLam at hT ⊢
    rw [show (2 * Real.pi - s) / 2 = Real.pi - s / 2 by ring, Real.sin_pi_sub]
    exact hT
  · have hs2 : Real.sin (2 * Real.pi - s) = -Real.sin s := by
      rw [show 2 * Real.pi - s = -(s - 2 * Real.pi) by ring, Real.sin_neg]
      congr 1
      rw [show s - 2 * Real.pi = s + (-1 : ℤ) * (2 * Real.pi) by push_cast; ring]
      exact Real.sin_add_int_mul_two_pi s (-1)
    rw [hs2]
    linarith

end

end Work.Drive.EpsForm
