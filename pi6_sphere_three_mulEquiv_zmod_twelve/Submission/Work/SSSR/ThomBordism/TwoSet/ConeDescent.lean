import Mathlib
import Submission.Work.ThomBordism.TwoSet.Basic
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.ThomBordism.TwoSet
variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR.ThomBordism.TwoSet

open scoped Topology unitInterval
variable {m : ℕ}

/-- `Fin m` is nonempty when `1 ≤ m`. -/
theorem finset_univ_nonempty {m : ℕ} (hm : 1 ≤ m) :
    (Finset.univ : Finset (Fin m)).Nonempty :=
  ⟨⟨0, hm⟩, Finset.mem_univ _⟩

/-- The `ℓ∞` "radius" of a point of the cube: `max_i |2 p_i - 1|`, so `0` at the centre and `1`
exactly on the boundary. -/
noncomputable def rad (hm : 1 ≤ m) (p : Fin m → unitInterval) : ℝ :=
  (Finset.univ : Finset (Fin m)).sup' (finset_univ_nonempty hm)
    (fun i => |2 * (p i : ℝ) - 1|)

/-- `rad` is continuous: a finite `max` of continuous functions. -/
theorem continuous_rad (hm : 1 ≤ m) : Continuous (rad hm) :=
  Continuous.finset_sup'_apply (s := Finset.univ) (finset_univ_nonempty hm) fun i _ =>
    ((continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))).sub
      continuous_const).abs

theorem rad_nonneg (hm : 1 ≤ m) (p : Fin m → unitInterval) : 0 ≤ rad hm p := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) (finset_univ_nonempty hm)
    (fun i => |2 * (p i : ℝ) - 1|)
  rw [rad, hi]; positivity

theorem rad_le_one (hm : 1 ≤ m) (p : Fin m → unitInterval) : rad hm p ≤ 1 := by
  rw [rad]
  refine Finset.sup'_le _ (fun i => |2 * (p i : ℝ) - 1|) fun i _ => ?_
  have h0 : (0:ℝ) ≤ (p i : ℝ) := (p i).2.1
  have h1 : (p i : ℝ) ≤ 1 := (p i).2.2
  rw [abs_le]; constructor <;> linarith

theorem rad_le (hm : 1 ≤ m) (p : Fin m → unitInterval) (i : Fin m) :
    |2 * (p i : ℝ) - 1| ≤ rad hm p := by
  rw [rad]
  exact (Finset.le_sup'_iff (finset_univ_nonempty hm)).mpr ⟨i, Finset.mem_univ i, le_rfl⟩

theorem rad_boundary_eq_one (hm : 1 ≤ m) {x : Fin m → unitInterval}
    (hx : x ∈ Cube.boundary (Fin m)) : rad hm x = 1 := by
  obtain ⟨i, hi⟩ := hx
  have h2 : |2 * (x i : ℝ) - 1| = 1 := by
    rcases hi with h | h <;> rw [h] <;> norm_num
  refine le_antisymm (rad_le_one hm x) ?_
  calc (1:ℝ) = |2 * (x i : ℝ) - 1| := h2.symm
    _ ≤ rad hm x := rad_le hm x i

/-- The real formula underlying `bpt`. -/
noncomputable def bptR (hm : 1 ≤ m) (p : Fin m → unitInterval) (i : Fin m) : ℝ :=
  1/2 + ((p i : ℝ) - 1/2) / rad hm p

/-- The value of the radial projection stays in the unit interval. -/
theorem bptR_mem (hm : 1 ≤ m) (p : Fin m → unitInterval) (i : Fin m) :
    bptR hm p i ∈ Set.Icc (0:ℝ) 1 := by
  have hr := rad_nonneg hm p
  have hb := rad_le hm p i
  constructor
  · by_cases hr0 : rad hm p = 0
    · simp only [bptR, hr0, div_zero, add_zero]; norm_num
    · have hrp : 0 < rad hm p := lt_of_le_of_ne hr (Ne.symm hr0)
      have h1 : -(1/2) ≤ ((p i : ℝ) - 1/2) / rad hm p := by
        rw [le_div_iff₀ hrp]
        nlinarith [abs_le.mp hb]
      simp only [bptR]; linarith
  · by_cases hr0 : rad hm p = 0
    · simp only [bptR, hr0, div_zero, add_zero]; norm_num
    · have hrp : 0 < rad hm p := lt_of_le_of_ne hr (Ne.symm hr0)
      have h1 : ((p i : ℝ) - 1/2) / rad hm p ≤ 1/2 := by
        rw [div_le_iff₀ hrp]
        nlinarith [abs_le.mp hb]
      simp only [bptR]; linarith

/-- The boundary point on the ray from the centre through `p` (meaningful when `rad > 0`). -/
noncomputable def bpt (hm : 1 ≤ m) (p : Fin m → unitInterval) : Fin m → unitInterval :=
  fun i => ⟨bptR hm p i, bptR_mem hm p i⟩

theorem bpt_coe (hm : 1 ≤ m) (p : Fin m → unitInterval) (i : Fin m) :
    ((bpt hm p) i : ℝ) = bptR hm p i := rfl

theorem bpt_eq_self_of_mem_boundary (hm : 1 ≤ m) {x : Fin m → unitInterval}
    (hx : x ∈ Cube.boundary (Fin m)) : bpt hm x = x := by
  funext i
  apply Subtype.ext
  simp only [bpt_coe, bptR, rad_boundary_eq_one hm hx, div_one]
  ring

/-- The boundary point really is on the boundary, when the radius is nonzero. -/
theorem bpt_mem_boundary (hm : 1 ≤ m) (p : Fin m → unitInterval) (hp : rad hm p ≠ 0) :
    bpt hm p ∈ Cube.boundary (Fin m) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) (finset_univ_nonempty hm)
    (fun i => |2 * (p i : ℝ) - 1|)
  refine ⟨i, ?_⟩
  have hri : rad hm p = |2 * (p i : ℝ) - 1| := hi
  have hne : 2 * (p i : ℝ) - 1 ≠ 0 := by intro h; exact hp (by rw [hri, h]; norm_num)
  have hval : 2 * ((bpt hm p) i : ℝ) - 1 = (2 * (p i : ℝ) - 1) / rad hm p := by
    rw [bpt_coe, bptR]; field_simp; ring
  have h2 : |2 * ((bpt hm p) i : ℝ) - 1| = 1 := by
    rw [hval, abs_div, hri, abs_of_pos (abs_pos.mpr hne), div_self (abs_ne_zero.mpr hne)]
  have hgoal : ((bpt hm p) i : ℝ) = 0 ∨ ((bpt hm p) i : ℝ) = 1 := by
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h2 with h | h
    · right; linarith
    · left; linarith
  rcases hgoal with h | h
  · left; exact Subtype.ext h
  · right; exact Subtype.ext h

/-- `bptR` is continuous in the point, wherever `rad ≠ 0`. -/
theorem bptR_continuous (hm : 1 ≤ m) (i : Fin m) :
    Continuous fun q : {p : Fin m → unitInterval // rad hm p ≠ 0} => bptR hm q.1 i := by
  have hnum : Continuous fun q : {p : Fin m → unitInterval // rad hm p ≠ 0} =>
      ((q.1 i : ℝ) - 1/2) := by
    have h1 : Continuous fun q : {p : Fin m → unitInterval // rad hm p ≠ 0} =>
        ((q.1 i : unitInterval) : ℝ) :=
      continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val)
    exact h1.sub continuous_const
  have hden : Continuous fun q : {p : Fin m → unitInterval // rad hm p ≠ 0} => rad hm q.1 :=
    (continuous_rad hm).comp continuous_subtype_val
  exact continuous_const.add (hnum.div hden (fun q => q.2))

/-- `bpt` is continuous wherever `rad ≠ 0`. -/
theorem continuous_bpt (hm : 1 ≤ m) :
    Continuous (fun q : {p : Fin m → unitInterval // rad hm p ≠ 0} => bpt hm q.1) := by
  refine continuous_pi (fun i => ?_)
  have hfun : (fun q : {p : Fin m → unitInterval // rad hm p ≠ 0} => bpt hm q.1 i)
      = fun q => (⟨bptR hm q.1 i, bptR_mem hm q.1 i⟩ : unitInterval) := rfl
  rw [hfun]
  exact Continuous.subtype_mk (bptR_continuous hm i) (fun q => bptR_mem hm q.1 i)

end Work.SSSR.ThomBordism.TwoSet
