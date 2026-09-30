import Mathlib
import Submission.Work.SSSR.Stems.Cubical.CubeFace
import Submission.Work.RatHurewicz.CubeFaceAux
import Submission.Work.SSSR.ThomBordism.TwoSet.ConeDescent
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.RatHurewicz
variable {R : Type} [CommRing R] [Nontrivial R]

open scoped unitInterval Topology
namespace Work.SSSR.RatHurewicz

open Work.SSSR.ThomBordism.TwoSet (rad bpt rad_nonneg rad_le_one rad_le rad_boundary_eq_one
  continuous_rad bpt_mem_boundary bpt_coe bptR bpt_eq_self_of_mem_boundary continuous_bpt)
/-- Clamping a real number to `[0,1]`. -/
noncomputable def clamp01 (x : ℝ) : unitInterval :=
  ⟨max 0 (min 1 x), ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩⟩

theorem clamp01_coe (x : ℝ) : ((clamp01 x : unitInterval) : ℝ) = max 0 (min 1 x) := rfl

theorem clamp01_of_mem {x : ℝ} (h : x ∈ Set.Icc (0:ℝ) 1) :
    ((clamp01 x : unitInterval) : ℝ) = x := by
  rw [clamp01_coe, min_eq_right h.2, max_eq_right h.1]

variable {m : ℕ}

/-- The normalising radius `ρ = max r (1/2)`. -/
noncomputable def domeR (hm : 1 ≤ m) (y : Fin m → unitInterval) : ℝ :=
  max (rad hm y) (1/2)

theorem domeR_pos (hm : 1 ≤ m) (y : Fin m → unitInterval) : 0 < domeR hm y := by
  rw [domeR]; exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)

theorem domeR_le_one (hm : 1 ≤ m) (y : Fin m → unitInterval) : domeR hm y ≤ 1 :=
  max_le (rad_le_one hm y) (by norm_num)

theorem domeR_ge_half (hm : 1 ≤ m) (y : Fin m → unitInterval) : 1/2 ≤ domeR hm y :=
  le_max_right _ _

theorem domeR_eq_half {hm : 1 ≤ m} {y : Fin m → unitInterval} (hy : rad hm y ≤ 1/2) :
    domeR hm y = 1/2 := max_eq_right hy

theorem domeR_eq {hm : 1 ≤ m} {y : Fin m → unitInterval} (hy : 1/2 ≤ rad hm y) :
    domeR hm y = rad hm y := max_eq_left hy

theorem continuous_domeR (hm : 1 ≤ m) : Continuous (domeR hm) :=
  (continuous_rad hm).max continuous_const

/-- The "space" coordinate of the dome map. -/
noncomputable def domeSpace (hm : 1 ≤ m) (y : Fin m → unitInterval) : Fin m → unitInterval :=
  fun i => clamp01 (1/2 + ((y i : ℝ) - 1/2) / domeR hm y)

/-- The "time" coordinate of the dome map. -/
noncomputable def domeTime (hm : 1 ≤ m) (y : Fin m → unitInterval) : unitInterval :=
  clamp01 (2 * (1 - domeR hm y))

theorem continuous_domeSpace (hm : 1 ≤ m) : Continuous (domeSpace hm) := by
  refine continuous_pi (fun i => ?_)
  change Continuous fun y : Fin m → unitInterval =>
    (⟨max 0 (min 1 (1/2 + ((y i : ℝ) - 1/2) / domeR hm y)),
      ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩⟩ : unitInterval)
  refine Continuous.subtype_mk ?_ _
  refine continuous_const.max (continuous_const.min ?_)
  refine Continuous.add continuous_const ?_
  exact ((continuous_subtype_val.comp (continuous_apply i)).sub continuous_const).div
    (continuous_domeR hm) (fun y => ne_of_gt (domeR_pos hm y))

theorem continuous_domeTime (hm : 1 ≤ m) : Continuous (domeTime hm) := by
  change Continuous fun y : Fin m → unitInterval =>
    (⟨max 0 (min 1 (2 * (1 - domeR hm y))),
      ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩⟩ : unitInterval)
  refine Continuous.subtype_mk ?_ _
  refine continuous_const.max (continuous_const.min ?_)
  exact continuous_const.mul (continuous_const.sub (continuous_domeR hm))

section DomeProps

variable {m : ℕ}

/-- The clamping in the space coordinate is never active. -/
theorem domeSpace_coe (hm : 1 ≤ m) (y : Fin m → unitInterval) (i : Fin m) :
    ((domeSpace hm y i : unitInterval) : ℝ) = 1/2 + ((y i : ℝ) - 1/2) / domeR hm y := by
  rw [domeSpace, clamp01_of_mem]
  have h := rad_le hm y i
  rw [abs_le] at h
  have hρ := domeR_pos hm y
  have hle : rad hm y ≤ domeR hm y := le_max_left _ _
  constructor
  · have : -(1/2) ≤ ((y i : ℝ) - 1/2) / domeR hm y := by
      rw [le_div_iff₀ hρ]; nlinarith [h.1]
    linarith
  · have : ((y i : ℝ) - 1/2) / domeR hm y ≤ 1/2 := by
      rw [div_le_iff₀ hρ]; nlinarith [h.2, hle]
    linarith

/-- The clamping in the time coordinate is never active. -/
theorem domeTime_coe (hm : 1 ≤ m) (y : Fin m → unitInterval) :
    ((domeTime hm y : unitInterval) : ℝ) = 2 * (1 - domeR hm y) := by
  rw [domeTime, clamp01_of_mem]
  exact ⟨by nlinarith [domeR_le_one hm y], by nlinarith [domeR_ge_half hm y]⟩

theorem domeR_eq_one_iff (hm : 1 ≤ m) (y : Fin m → unitInterval) :
    domeR hm y = 1 ↔ rad hm y = 1 := by
  constructor
  · intro h
    have h1 : rad hm y ≤ 1 := rad_le_one hm y
    by_cases h2 : (1/2 : ℝ) ≤ rad hm y
    · rwa [domeR, max_eq_left h2] at h
    · rw [domeR, max_eq_right (le_of_lt (not_le.mp h2))] at h
      norm_num at h
  · intro h; rw [domeR, h, max_eq_left (by norm_num)]

/-- Scaling a point of the cube towards its centre by `ρ ∈ [0,1]`. -/
noncomputable def domScale {m : ℕ} (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (v : Fin m → unitInterval) :
    Fin m → unitInterval :=
  fun i => ⟨1/2 + ρ * ((v i : ℝ) - 1/2), by
    have hv := (v i).2
    constructor <;> nlinarith [hv.1, hv.2]⟩

theorem domScale_coe {m : ℕ} {ρ : ℝ} {h0 : 0 ≤ ρ} {h1 : ρ ≤ 1} (v : Fin m → unitInterval)
    (i : Fin m) :
    ((domScale ρ h0 h1 v i : unitInterval) : ℝ) = 1/2 + ρ * ((v i : ℝ) - 1/2) := rfl

theorem domScale_term {m : ℕ} {ρ : ℝ} {h0 : 0 ≤ ρ} {h1 : ρ ≤ 1} (v : Fin m → unitInterval)
    (i : Fin m) :
    |2 * ((domScale ρ h0 h1 v i : unitInterval) : ℝ) - 1| = ρ * |2 * (v i : ℝ) - 1| := by
  rw [domScale_coe]
  have : 2 * (1/2 + ρ * ((v i : ℝ) - 1/2)) - 1 = ρ * (2 * (v i : ℝ) - 1) := by ring
  rw [this, abs_mul, abs_of_nonneg h0]

theorem domScale_rad {m : ℕ} (hm : 1 ≤ m) {ρ : ℝ} {h0 : 0 ≤ ρ} {h1 : ρ ≤ 1}
    (v : Fin m → unitInterval) :
    rad hm (domScale ρ h0 h1 v) = ρ * rad hm v := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le _ _ (fun i _ => ?_)
    rw [domScale_term v i]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun i : Fin m => |2 * (v i : ℝ) - 1|)
      (Finset.mem_univ i)) h0
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
      (Work.SSSR.ThomBordism.TwoSet.finset_univ_nonempty hm)
      (fun i : Fin m => |2 * (v i : ℝ) - 1|)
    have h2 : rad hm v = |2 * (v i : ℝ) - 1| := hi
    rw [h2]
    calc ρ * |2 * (v i : ℝ) - 1|
        = |2 * ((domScale ρ h0 h1 v i : unitInterval) : ℝ) - 1| := (domScale_term v i).symm
      _ ≤ rad hm (domScale ρ h0 h1 v) := by
          rw [rad]
          exact Finset.le_sup'
            (fun i : Fin m => |2 * ((domScale ρ h0 h1 v i : unitInterval) : ℝ) - 1|)
            (Finset.mem_univ i)

end DomeProps

end Work.SSSR.RatHurewicz
