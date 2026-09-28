import Mathlib
import Submission.Work.Stems.Cubical.CubeFace
import Submission.Work.RatHurewicz.CubeFaceAux
import Submission.Work.ThomBordism.TwoSet.ConeDescent

/-!
# The "dome" parametrisation of the boundary of a cube

For `m ≥ 1` let `Q := I^{m+1}` and `∂Q` its boundary; write points of `Q` as `(u, s)` with
`u : I^m` and `s` the last coordinate.  The *bottom face* `D₀ = {s = 0}` is a copy of `I^m`, and
the *dome* `D = ∂Q ∖ interior D₀` is a closed disc whose boundary is the *rim* `∂I^m × {0}`.

With `r y = max_i |2 y_i - 1|` the `ℓ∞`-radius of `I^m` (from `Work.ThomBordism.TwoSet`) and
`ρ y = max (r y) (1/2)`, the dome map is

`ν y = ( (1/2 + (y_i - 1/2)/ρ y)_i , clamp (2 (1 - ρ y)) )`.

In the regime `r y ≤ 1/2` this is the "cap" formula `(2y - 1/2, 1)` and in the regime `r y ≥ 1/2`
it is `(c + (y-c)/r, 2 - 2r)`, the radial projection; the two agree at `r = 1/2`, so the single
formula above is continuous, injective, and surjective onto the dome, with `ν (∂I^m)` equal to the
rim.  This is the parametrisation used to turn boundary data which is constant on the bottom face
into a based cube.
-/

open scoped unitInterval Topology

namespace Work.RatHurewicz

open Work.ThomBordism.TwoSet (rad bpt rad_nonneg rad_le_one rad_le rad_boundary_eq_one
  continuous_rad bpt_mem_boundary bpt_coe bptR bpt_eq_self_of_mem_boundary continuous_bpt)

/-- Clamping a real number to `[0,1]`. -/
noncomputable def clamp01 (x : ℝ) : unitInterval :=
  ⟨max 0 (min 1 x), ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩⟩

theorem clamp01_coe (x : ℝ) : ((clamp01 x : unitInterval) : ℝ) = max 0 (min 1 x) := rfl

theorem continuous_clamp01 : Continuous clamp01 := by
  refine Continuous.subtype_mk (continuous_const.max (continuous_const.min continuous_id)) _

theorem clamp01_of_one_le {x : ℝ} (h : 1 ≤ x) : clamp01 x = 1 := by
  apply Subtype.ext
  rw [clamp01_coe, min_eq_left h, max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
  rfl

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

/-- **The dome map** `ν : I^m → I^{m+1}`. -/
noncomputable def domePt (hm : 1 ≤ m) (y : Fin m → unitInterval) : Fin (m + 1) → unitInterval :=
  @Fin.insertNth m (fun _ => unitInterval) (Fin.last m) (domeTime hm y) (domeSpace hm y)

theorem domePt_last (hm : 1 ≤ m) (y : Fin m → unitInterval) :
    domePt hm y (Fin.last m) = domeTime hm y :=
  Fin.insertNth_apply_same _ _ _

theorem domePt_castSucc (hm : 1 ≤ m) (y : Fin m → unitInterval) (i : Fin m) :
    domePt hm y i.castSucc = domeSpace hm y i := by
  rw [domePt, ← Fin.succAbove_last, Fin.insertNth_apply_succAbove]

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

theorem snoc_eq_insertNth {n : ℕ} (u : Fin n → unitInterval) (x : unitInterval) :
    Fin.snoc u x = @Fin.insertNth n (fun _ => unitInterval) (Fin.last n) x u := by
  rw [← Work.RatHurewicz.faceCM_last (n := n) x u,
    Work.RatHurewicz.faceCM_eq_insertNth]

theorem continuous_domePt (hm : 1 ≤ m) : Continuous (domePt hm) :=
  Continuous.finInsertNth (A := fun _ : Fin (m+1) => unitInterval) (i := Fin.last m)
    (f := fun y : Fin m → unitInterval => domeTime hm y)
    (g := fun y : Fin m → unitInterval => domeSpace hm y)
    (continuous_domeTime hm) (continuous_domeSpace hm)


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

theorem domeTime_eq_zero_iff (hm : 1 ≤ m) (y : Fin m → unitInterval) :
    domeTime hm y = 0 ↔ rad hm y = 1 := by
  rw [← domeR_eq_one_iff hm y]
  constructor
  · intro h
    have h2 : ((domeTime hm y : unitInterval) : ℝ) = 0 := by rw [h]; rfl
    rw [domeTime_coe] at h2
    linarith
  · intro h
    apply Subtype.ext
    rw [domeTime_coe, h]
    norm_num

theorem rad_eq_one_of_exists_extreme (hm : 1 ≤ m) {y : Fin m → unitInterval}
    (h : ∃ i : Fin m, (y i : ℝ) = 0 ∨ (y i : ℝ) = 1) : rad hm y = 1 := by
  obtain ⟨i, hi | hi⟩ := h
  · exact (rad_boundary_eq_one hm ⟨i, Or.inl (Subtype.ext hi)⟩)
  · exact (rad_boundary_eq_one hm ⟨i, Or.inr (Subtype.ext hi)⟩)

theorem exists_extreme_of_rad_eq_one (hm : 1 ≤ m) {y : Fin m → unitInterval}
    (h : rad hm y = 1) : ∃ i : Fin m, (y i : ℝ) = 0 ∨ (y i : ℝ) = 1 := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    (Work.ThomBordism.TwoSet.finset_univ_nonempty hm)
    (fun i : Fin m => |2 * (y i : ℝ) - 1|)
  have h1 : |2 * (y i : ℝ) - 1| = 1 := by rw [← hi]; exact h
  rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp h1 with h2 | h2
  · exact ⟨i, Or.inr (by linarith)⟩
  · exact ⟨i, Or.inl (by linarith)⟩

/-- **Injectivity of the dome map.** -/
theorem domePt_injective (hm : 1 ≤ m) : Function.Injective (domePt hm) := by
  intro y y' h
  have hR : domeR hm y = domeR hm y' := by
    have h2 := congrFun h (Fin.last m)
    rw [domePt_last, domePt_last] at h2
    have h1 : ((domeTime hm y : unitInterval) : ℝ) = ((domeTime hm y' : unitInterval) : ℝ) :=
      congrArg Subtype.val h2
    rw [domeTime_coe, domeTime_coe] at h1
    linarith
  funext i
  have h2 := congrFun h i.castSucc
  rw [domePt_castSucc, domePt_castSucc] at h2
  have h2' : ((domeSpace hm y i : unitInterval) : ℝ) =
      ((domeSpace hm y' i : unitInterval) : ℝ) := congrArg Subtype.val h2
  rw [domeSpace_coe, domeSpace_coe, hR] at h2'
  have hρ := domeR_pos hm y
  have h2'' : ((y i : ℝ) - 1/2) / domeR hm y' = ((y' i : ℝ) - 1/2) / domeR hm y' := by
    have hh := congrArg (fun z : ℝ => z - 1/2) h2'
    simpa only [add_sub_cancel_left] using hh
  have hρ' := domeR_pos hm y'
  have h5 := (div_eq_div_iff (ne_of_gt hρ') (ne_of_gt hρ')).mp h2''
  have h6 : (y i : ℝ) - 1/2 = (y' i : ℝ) - 1/2 := mul_right_cancel₀ (ne_of_gt hρ') h5
  exact Subtype.ext (by linarith [h6])

/-- The dome map sends `∂I^m` to the rim. -/
theorem domePt_last_eq_zero_of_mem_boundary (hm : 1 ≤ m) {y : Fin m → unitInterval}
    (hy : y ∈ Cube.boundary (Fin m)) : domePt hm y (Fin.last m) = 0 := by
  rw [domePt_last]
  rw [domeTime_eq_zero_iff]
  exact rad_boundary_eq_one hm hy

/-- Conversely, a point of the dome whose last coordinate vanishes lies on `∂I^m`. -/
theorem mem_boundary_of_domePt_last_eq_zero (hm : 1 ≤ m) {y : Fin m → unitInterval}
    (hy : domePt hm y (Fin.last m) = 0) : y ∈ Cube.boundary (Fin m) := by
  rw [domePt_last] at hy
  rw [domeTime_eq_zero_iff] at hy
  obtain ⟨i, hi | hi⟩ := exists_extreme_of_rad_eq_one hm hy
  · exact ⟨i, Or.inl (Subtype.ext hi)⟩
  · exact ⟨i, Or.inr (Subtype.ext hi)⟩

theorem domeSpace_eq_one_of_rad {hm : 1 ≤ m} {y : Fin m → unitInterval} {i : Fin m}
    (h : 2 * (y i : ℝ) - 1 = rad hm y) (h1 : 1/2 ≤ rad hm y) :
    ((domeSpace hm y i : unitInterval) : ℝ) = 1 := by
  rw [domeSpace_coe, domeR_eq h1]
  rw [show ((y i : ℝ) - 1/2) / rad hm y = 1/2 by
    rw [div_eq_iff (by linarith : rad hm y ≠ 0)]; linarith]
  norm_num

theorem domeSpace_eq_zero_of_rad {hm : 1 ≤ m} {y : Fin m → unitInterval} {i : Fin m}
    (h : 2 * (y i : ℝ) - 1 = -rad hm y) (h1 : 1/2 ≤ rad hm y) :
    ((domeSpace hm y i : unitInterval) : ℝ) = 0 := by
  rw [domeSpace_coe, domeR_eq h1]
  rw [show ((y i : ℝ) - 1/2) / rad hm y = -(1/2) by
    rw [div_eq_iff (by linarith : rad hm y ≠ 0)]; linarith]
  norm_num

/-- If `rad ≥ 1/2` then some space coordinate of the dome map is extreme. -/
theorem domeSpace_extreme (hm : 1 ≤ m) {y : Fin m → unitInterval} (h1 : 1/2 ≤ rad hm y) :
    ∃ i : Fin m, ((domeSpace hm y i : unitInterval) : ℝ) = 0 ∨
      ((domeSpace hm y i : unitInterval) : ℝ) = 1 := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    (Work.ThomBordism.TwoSet.finset_univ_nonempty hm)
    (fun i : Fin m => |2 * (y i : ℝ) - 1|)
  have hri : rad hm y = |2 * (y i : ℝ) - 1| := hi
  have hx : 2 * (y i : ℝ) - 1 = rad hm y ∨ 2 * (y i : ℝ) - 1 = -rad hm y := by
    have h2 : |2 * (y i : ℝ) - 1| = rad hm y := hri.symm
    rcases abs_cases (2 * (y i : ℝ) - 1) with h3 | h3
    · left; rw [h3.1] at h2; exact h2
    · right; rw [h3.1] at h2; linarith
  rcases hx with h4 | h4
  · exact ⟨i, Or.inr (domeSpace_eq_one_of_rad h4 h1)⟩
  · exact ⟨i, Or.inl (domeSpace_eq_zero_of_rad h4 h1)⟩

/-- The dome map lands in the boundary. -/
theorem domePt_mem_boundary (hm : 1 ≤ m) (y : Fin m → unitInterval) :
    domePt hm y ∈ Cube.boundary (Fin (m + 1)) := by
  rcases lt_or_ge (rad hm y) (1/2) with h | h
  · refine ⟨Fin.last m, Or.inr ?_⟩
    rw [domePt_last]
    apply Subtype.ext
    rw [domeTime_coe, domeR_eq_half (le_of_lt h)]
    norm_num
  · obtain ⟨i, hi⟩ := domeSpace_extreme hm (show 1/2 ≤ rad hm y from h)
    rcases hi with hi | hi
    · refine ⟨i.castSucc, Or.inl ?_⟩
      rw [domePt_castSucc]
      exact Subtype.ext hi
    · refine ⟨i.castSucc, Or.inr ?_⟩
      rw [domePt_castSucc]
      exact Subtype.ext hi

/-- The dome: boundary points which are not in the interior of the bottom face. -/
def IsDomePt (z : Fin (m + 1) → unitInterval) : Prop :=
  z ∈ Cube.boundary (Fin (m + 1)) ∧
    ¬ (z (Fin.last m) = 0 ∧ ∀ i : Fin m, 0 < (z i.castSucc : ℝ) ∧ (z i.castSucc : ℝ) < 1)

/-- The dome map lands in the dome. -/
theorem domePt_isDomePt (hm : 1 ≤ m) (y : Fin m → unitInterval) :
    IsDomePt (domePt hm y) := by
  refine ⟨domePt_mem_boundary hm y, fun h => ?_⟩
  have hb : y ∈ Cube.boundary (Fin m) := mem_boundary_of_domePt_last_eq_zero hm h.1
  obtain ⟨i, hi⟩ := domeSpace_extreme hm (by rw [rad_boundary_eq_one hm hb]; norm_num)
  have h3 := h.2 i
  rw [domePt_castSucc] at h3
  rcases hi with hi | hi
  · exact absurd h3.1 (by rw [hi]; norm_num)
  · exact absurd h3.2 (by rw [hi]; norm_num)

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
      (Work.ThomBordism.TwoSet.finset_univ_nonempty hm)
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

/-- **Surjectivity of the dome map** onto the boundary points whose last coordinate is `1` or
whose space part lies on `∂I^m`. -/
theorem domePt_surj (hm : 1 ≤ m) {z : Fin (m + 1) → unitInterval}
    (hz : z ∈ Cube.boundary (Fin (m + 1)))
    (h : z (Fin.last m) = 1 ∨ (fun i : Fin m => z i.castSucc) ∈ Cube.boundary (Fin m)) :
    ∃ y : Fin m → unitInterval, domePt hm y = z := by
  set s : unitInterval := z (Fin.last m) with hs
  set v : Fin m → unitInterval := fun i => z i.castSucc with hv
  by_cases hs1 : s = 1
  · refine ⟨domScale (1/2) (by norm_num) (by norm_num) v, ?_⟩
    have hrad : rad hm (domScale (1/2) (by norm_num) (by norm_num) v) ≤ 1/2 := by
      rw [domScale_rad hm, mul_comm]
      calc rad hm v * (1/2) ≤ 1 * (1/2) :=
            mul_le_mul_of_nonneg_right (rad_le_one hm v) (by norm_num)
        _ = 1/2 := by norm_num
    have hR : domeR hm (domScale (1/2) (by norm_num) (by norm_num) v) = 1/2 := domeR_eq_half hrad
    have hspace : ∀ j : Fin m,
        domeSpace hm (domScale (1/2) (by norm_num) (by norm_num) v) j = v j := by
      intro j
      apply Subtype.ext
      rw [domeSpace_coe, hR, domScale_coe]
      field_simp
      ring
    have htime : ((domeTime hm (domScale (1/2) (by norm_num) (by norm_num) v) : unitInterval) : ℝ)
        = 1 := by
      rw [domeTime_coe, hR]
      norm_num
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [domePt_castSucc, hspace j, hv]
    · rw [domePt_last]
      apply Subtype.ext
      rw [htime, ← hs, hs1]
      rfl
  · rcases h with hi | hi
    · exact absurd hi hs1
    have hvrad : rad hm v = 1 := rad_boundary_eq_one hm hi
    set ρ : ℝ := 1 - (s : ℝ) / 2 with hρdef
    have hρ0 : 0 ≤ ρ := by rw [hρdef]; nlinarith [(s : unitInterval).2.2]
    have hρ1 : ρ ≤ 1 := by rw [hρdef]; nlinarith [(s : unitInterval).2.1]
    have hρhalf : 1/2 ≤ ρ := by rw [hρdef]; nlinarith [(s : unitInterval).2.2]
    have hρpos : 0 < ρ := by rw [hρdef]; nlinarith [(s : unitInterval).2.2]
    refine ⟨domScale ρ hρ0 hρ1 v, ?_⟩
    have hrad : rad hm (domScale ρ hρ0 hρ1 v) = ρ := by
      rw [domScale_rad hm, hvrad, mul_one]
    have hR : domeR hm (domScale ρ hρ0 hρ1 v) = ρ := by
      rw [domeR_eq (by rw [hrad]; exact hρhalf), hrad]
    have hspace : ∀ j : Fin m, domeSpace hm (domScale ρ hρ0 hρ1 v) j = v j := by
      intro j
      apply Subtype.ext
      rw [domeSpace_coe, hR, domScale_coe]
      field_simp
      ring
    have htime : ((domeTime hm (domScale ρ hρ0 hρ1 v) : unitInterval) : ℝ) = (s : ℝ) := by
      rw [domeTime_coe, hR, hρdef]
      ring_nf
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [domePt_castSucc, hspace j, hv]
    · rw [domePt_last]
      apply Subtype.ext
      rw [htime, ← hs]

end DomeProps

end Work.RatHurewicz
