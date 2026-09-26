import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndexGeom

/-!
# The argument increment of a nowhere vanishing path

For a continuous nowhere vanishing path `c : [0,1] → ℂ`, `argChangeLift` provides a lift `Λ`
through `exp` and shows that `Λ 1 - Λ 0` does not depend on the lift.  We call this number the
**increment** of `c`.  It is additive under restrictions of the path, it is `2πI` times the winding
number when `c` is a closed loop, and it is invariant under reparametrisation.  This is the
bookkeeping device for the identity `windNumber (upPC true) x + windNumber (dnPC false) x = 1` and
its siblings.
-/

open Set

namespace Work.SphereJordan

noncomputable section

open Work.Smooth.SphereJordan

/-- A chosen continuous lift of a nowhere vanishing continuous path through `exp`. -/
def liftOf {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0) : C(unitInterval, ℂ) :=
  Classical.choose (argChangeLift c hc)

theorem exp_liftOf {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0) :
    ∀ t, Complex.exp (liftOf hc t) = c t :=
  (Classical.choose_spec (argChangeLift c hc)).1

/-- **The increment** of a nowhere vanishing continuous path: `Λ 1 - Λ 0` for any lift `Λ`. -/
def incr {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0) : ℂ := liftOf hc 1 - liftOf hc 0

/-- The increment is independent of the chosen lift. -/
theorem incr_spec {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0) (Λ : C(unitInterval, ℂ))
    (hΛ : ∀ t, Complex.exp (Λ t) = c t) : Λ 1 - Λ 0 = incr hc :=
  ((Classical.choose_spec (argChangeLift c hc)).2.2) Λ hΛ

/-- The increment of a closed loop is the winding number times `2πI`. -/
theorem incr_eq_loopIndex {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0) (hloop : c 0 = c 1) :
    incr hc = (loopIndex c : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  have h := loopIndex_spec c hc hloop (liftOf hc) (exp_liftOf hc)
  rw [incr]
  exact h

/-- Pointwise equal paths have equal increments. -/
theorem incr_congr {c c' : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0) (hc' : ∀ t, c' t ≠ 0)
    (h : ∀ t, c t = c' t) : incr hc = incr hc' := by
  have hlift : ∀ t, Complex.exp (liftOf hc t) = c' t := fun t => by rw [exp_liftOf hc t, h t]
  have h1 := incr_spec hc' (liftOf hc) hlift
  have h2 := incr_spec hc (liftOf hc) (exp_liftOf hc)
  rw [← h1, ← h2]

/-- The affine reparametrisation `t ↦ a + (b - a) t` of the unit interval, when it maps `[0,1]`
into itself. -/
def linMap (a b : ℝ) (h : ∀ t : ℝ, t ∈ Set.Icc 0 1 → a + (b - a) * t ∈ Set.Icc 0 1) :
    C(unitInterval, unitInterval) :=
  ⟨fun t => ⟨a + (b - a) * (t : ℝ), h _ t.2⟩, by fun_prop⟩

@[simp] theorem linMap_val (a b : ℝ) (h) (t : unitInterval) :
    ((linMap a b h t : unitInterval) : ℝ) = a + (b - a) * (t : ℝ) := rfl

theorem linMap_zero (a b : ℝ) (h) :
    linMap a b h 0 = (⟨a, by simpa using h 0 (by norm_num : (0:ℝ) ∈ Set.Icc 0 1)⟩ : unitInterval) := by
  apply Subtype.ext
  simp

theorem linMap_one (a b : ℝ) (h) :
    linMap a b h 1 = (⟨b, by simpa using h 1 (by norm_num : (1:ℝ) ∈ Set.Icc 0 1)⟩ : unitInterval) := by
  apply Subtype.ext
  simp

theorem linMap_mem (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∀ t : ℝ, t ∈ Set.Icc 0 1 → a + (b - a) * t ∈ Set.Icc 0 1 := by
  intro t ht
  constructor <;> nlinarith [ht.1, ht.2]

/-- **Increment of a reparametrised path.** -/
theorem incr_comp {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0) (σ : C(unitInterval, unitInterval)) :
    incr (c := c.comp σ) (fun t => hc (σ t)) =
      (liftOf hc) (σ 1) - (liftOf hc) (σ 0) := by
  have hlift : ∀ t, Complex.exp ((liftOf hc).comp σ t) = (c.comp σ) t := fun t => by
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
    exact exp_liftOf hc (σ t)
  have h := incr_spec (c := c.comp σ) (fun t => hc (σ t)) ((liftOf hc).comp σ) hlift
  rw [← h]
  simp only [ContinuousMap.comp_apply]

/-- The reversal of the unit interval. -/
def revI : C(unitInterval, unitInterval) :=
  linMap 1 0 (by intro t ht; constructor <;> [linarith [ht.1, ht.2]; linarith [ht.1, ht.2]])

theorem revI_zero : revI 0 = 1 := by
  apply Subtype.ext
  change (1 : ℝ) + (0 - 1) * (((0 : unitInterval)) : ℝ) = 1
  norm_num

theorem revI_one : revI 1 = 0 := by
  apply Subtype.ext
  change (1 : ℝ) + (0 - 1) * (((1 : unitInterval)) : ℝ) = 0
  norm_num

/-- The increment of the reversed path is the negative of the increment. -/
theorem incr_rev {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0) :
    incr (c := c.comp revI) (fun t => hc _) = -incr hc := by
  rw [incr_comp hc revI, revI_one, revI_zero, incr]
  ring

/-- First quarter reparametrisation. -/
def q1 : C(unitInterval, unitInterval) :=
  linMap 0 (1/4) (linMap_mem 0 (1/4) (by norm_num) (by norm_num) (by norm_num))

/-- Second quarter reparametrisation. -/
def q2 : C(unitInterval, unitInterval) :=
  linMap (1/4) (1/2) (linMap_mem (1/4) (1/2) (by norm_num) (by norm_num) (by norm_num))

/-- Third quarter reparametrisation. -/
def q3 : C(unitInterval, unitInterval) :=
  linMap (1/2) (3/4) (linMap_mem (1/2) (3/4) (by norm_num) (by norm_num) (by norm_num))

/-- Fourth quarter reparametrisation. -/
def q4 : C(unitInterval, unitInterval) :=
  linMap (3/4) 1 (linMap_mem (3/4) 1 (by norm_num) (by norm_num) (by norm_num))

theorem q1_zero : q1 0 = 0 := by
  apply Subtype.ext
  change (0:ℝ) + (1/4 - 0) * (((0 : unitInterval)) : ℝ) = 0
  norm_num

theorem q1_one : q1 1 = (⟨1/4, by norm_num⟩ : unitInterval) := by
  apply Subtype.ext
  change (0:ℝ) + (1/4 - 0) * (((1 : unitInterval)) : ℝ) = 1/4
  norm_num

theorem q2_zero : q2 0 = (⟨1/4, by norm_num⟩ : unitInterval) := by
  apply Subtype.ext
  change (1/4:ℝ) + (1/2 - 1/4) * (((0 : unitInterval)) : ℝ) = 1/4
  norm_num

theorem q2_one : q2 1 = (⟨1/2, by norm_num⟩ : unitInterval) := by
  apply Subtype.ext
  change (1/4:ℝ) + (1/2 - 1/4) * (((1 : unitInterval)) : ℝ) = 1/2
  norm_num

theorem q3_zero : q3 0 = (⟨1/2, by norm_num⟩ : unitInterval) := by
  apply Subtype.ext
  change (1/2:ℝ) + (3/4 - 1/2) * (((0 : unitInterval)) : ℝ) = 1/2
  norm_num

theorem q3_one : q3 1 = (⟨3/4, by norm_num⟩ : unitInterval) := by
  apply Subtype.ext
  change (1/2:ℝ) + (3/4 - 1/2) * (((1 : unitInterval)) : ℝ) = 3/4
  norm_num

theorem q4_zero : q4 0 = (⟨3/4, by norm_num⟩ : unitInterval) := by
  apply Subtype.ext
  change (3/4:ℝ) + (1 - 3/4) * (((0 : unitInterval)) : ℝ) = 3/4
  norm_num

theorem q4_one : q4 1 = 1 := by
  apply Subtype.ext
  change (3/4:ℝ) + (1 - 3/4) * (((1 : unitInterval)) : ℝ) = 1
  norm_num

/-- **Four-way splitting of the increment.** -/
theorem incr_quarter {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0) :
    incr hc = incr (c := c.comp q1) (fun t => hc _) + incr (c := c.comp q2) (fun t => hc _)
      + incr (c := c.comp q3) (fun t => hc _) + incr (c := c.comp q4) (fun t => hc _) := by
  rw [incr_comp hc q1, incr_comp hc q2, incr_comp hc q3, incr_comp hc q4,
    q4_one, q1_zero, incr]
  rw [show q2 1 = q3 0 from by rw [q2_one, q3_zero], show q3 1 = q4 0 from by rw [q3_one, q4_zero]]
  rw [show q1 1 = q2 0 from by rw [q1_one, q2_zero]]
  ring

end

end Work.SphereJordan
