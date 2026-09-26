import Mathlib
import Submission.Work.Smooth.SphereJordan.argChangeLift
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.loopIndexTrans
import Submission.Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy

/-!
# The increment of the argument along a nowhere vanishing path

For a continuous nowhere vanishing path `p : [0,1] → ℂ` the increment `Λ 1 - Λ 0` of a continuous
logarithm `Λ` of `p` is independent of `Λ` (`Work.Smooth.SphereJordan.argChangeLift`); this
increment is the fundamental tool for the additivity of winding numbers over concatenations of
arcs.  We also specialize to *parameter intervals* of a plane curve; the value is set to `0` on
paths meeting `0` (as for `loopIndex`), so that the definitions are total and rewriting does not
get blocked by proof terms.
-/

open Set
open Classical

namespace Work.SphereJordan

noncomputable section

/-- The **increment of the argument** of a path `p : [0,1] → ℂ`: the difference `Λ 1 - Λ 0` of a
continuous logarithm `Λ` of `p` if `p` never vanishes, and `0` otherwise. -/
noncomputable def pathIncTot (p : C(unitInterval, ℂ)) : ℂ :=
  if h : ∀ t : unitInterval, p t ≠ 0 then
    (Work.Smooth.SphereJordan.argChangeLift p h).choose 1 -
      (Work.Smooth.SphereJordan.argChangeLift p h).choose 0
  else 0

theorem pathIncTot_of_ne (p : C(unitInterval, ℂ)) (hp : ∀ t : unitInterval, p t ≠ 0) :
    pathIncTot p = (Work.Smooth.SphereJordan.argChangeLift p hp).choose 1 -
      (Work.Smooth.SphereJordan.argChangeLift p hp).choose 0 :=
  dif_pos hp

/-- **The characterising property of the increment**: every continuous logarithm gives the same
increment. -/
theorem pathIncTot_eq_of_lift (p : C(unitInterval, ℂ)) (hp : ∀ t : unitInterval, p t ≠ 0)
    (Λ : C(unitInterval, ℂ)) (hΛ : ∀ t : unitInterval, Complex.exp (Λ t) = p t) :
    pathIncTot p = Λ 1 - Λ 0 := by
  rw [pathIncTot_of_ne p hp]
  exact ((Work.Smooth.SphereJordan.argChangeLift p hp).choose_spec.2.2 Λ hΛ).symm

/-- The increment only depends on the path. -/
theorem pathIncTot_congr {p q : C(unitInterval, ℂ)} (hpq : ∀ t : unitInterval, p t = q t) :
    pathIncTot p = pathIncTot q := by
  by_cases hp : ∀ t : unitInterval, p t ≠ 0
  · have hq : ∀ t : unitInterval, q t ≠ 0 := fun t => hpq t ▸ hp t
    have hΛ := (Work.Smooth.SphereJordan.argChangeLift p hp).choose_spec
    rw [pathIncTot_eq_of_lift p hp _ hΛ.1,
      pathIncTot_eq_of_lift q hq _ (fun t => (hΛ.1 t).trans (hpq t))]
  · have hq : ¬ ∀ t : unitInterval, q t ≠ 0 := by
      intro hq
      exact hp (fun t => by rw [hpq t]; exact hq t)
    rw [pathIncTot, dif_neg hp, pathIncTot, dif_neg hq]

/-- A constant nowhere vanishing path has vanishing increment. -/
theorem pathIncTot_const (a : ℂ) (ha : a ≠ 0) :
    pathIncTot (ContinuousMap.const unitInterval a) = 0 := by
  have h : ∀ t : unitInterval, (ContinuousMap.const unitInterval a) t ≠ 0 := fun _ => ha
  have hΛ : ∀ t : unitInterval,
      Complex.exp ((ContinuousMap.const unitInterval (Complex.log a)) t) =
        (ContinuousMap.const unitInterval a) t := fun t => by
    rw [ContinuousMap.const_apply, ContinuousMap.const_apply, Complex.exp_log ha]
  rw [pathIncTot_eq_of_lift (ContinuousMap.const unitInterval a) h
    (ContinuousMap.const unitInterval (Complex.log a)) hΛ]
  simp only [ContinuousMap.const_apply, sub_self]

/-- The reversal homeomorphism of the unit interval. -/
def uIrev : C(unitInterval, unitInterval) :=
  ⟨fun t => ⟨1 - (t : ℝ), by
      refine ⟨by nlinarith [t.2.2], by nlinarith [t.2.1]⟩⟩,
    Continuous.subtype_mk (by fun_prop) (fun t =>
      ⟨by nlinarith [t.2.2], by nlinarith [t.2.1]⟩)⟩

@[simp] theorem uIrev_zero : uIrev 0 = 1 := Subtype.ext (by simp [uIrev])
@[simp] theorem uIrev_one : uIrev 1 = 0 := Subtype.ext (by simp [uIrev])

/-- **Reparametrisation**: if `q = p ∘ φ` with `φ` continuous, then the increment of `q` is
`Λ (φ 1) - Λ (φ 0)` for any continuous logarithm `Λ` of `p`. -/
theorem pathIncTot_comp_sub (φ : C(unitInterval, unitInterval)) {p q : C(unitInterval, ℂ)}
    (hpq : ∀ t : unitInterval, q t = p (φ t)) (hp : ∀ t : unitInterval, p t ≠ 0)
    (hq : ∀ t : unitInterval, q t ≠ 0) (Λ : C(unitInterval, ℂ))
    (hΛ : ∀ t : unitInterval, Complex.exp (Λ t) = p t) :
    pathIncTot q = Λ (φ 1) - Λ (φ 0) :=
  pathIncTot_eq_of_lift q hq (Λ.comp φ) (fun t => by
    rw [ContinuousMap.comp_apply, hΛ (φ t), hpq t])

/-- The increment of a closed path is its index times `2πi`. -/
theorem pathIncTot_eq_loopIndex (p : C(unitInterval, ℂ)) (hp : ∀ t : unitInterval, p t ≠ 0)
    (hloop : p 0 = p 1) :
    pathIncTot p = (Work.Smooth.SphereJordan.loopIndex p : ℂ)
      * (2 * (Real.pi : ℂ) * Complex.I) := by
  rw [pathIncTot_of_ne p hp]
  have hΛ := (Work.Smooth.SphereJordan.argChangeLift p hp).choose_spec
  rw [hΛ.2.2 _ hΛ.1]
  exact Work.Smooth.SphereJordan.loopIndex_spec p hp hloop _ hΛ.1

/-! ## Increments over parameter intervals of a plane curve -/

/-- The **increment of the argument of `γ` over the parameter interval `[a,b]`**, based at the
point `z` (the value is `0` if the arc meets `z`). -/
def incOn (γ : ℝ → ℂ) (hγ : Continuous γ) (z : ℂ) (a b : ℝ) : ℂ :=
  pathIncTot ⟨fun t : unitInterval => γ (a + (t : ℝ) * (b - a)) - z, by fun_prop⟩

/-- The increment over `[a,b]` (of an arc avoiding `z`, with `a ≤ b`) is the increment of any lift
of the arc. -/
theorem incOn_eq_of_lift {γ : ℝ → ℂ} (hγ : Continuous γ) {z : ℂ} {a b : ℝ} (hab : a ≤ b)
    (hav : ∀ t ∈ Set.Icc a b, γ t ≠ z) (Λ : C(unitInterval, ℂ))
    (hΛ : ∀ t : unitInterval, Complex.exp (Λ t) = γ (a + (t : ℝ) * (b - a)) - z) :
    incOn γ hγ z a b = Λ 1 - Λ 0 :=
  pathIncTot_eq_of_lift _ (fun t =>
    sub_ne_zero.mpr (hav _ ⟨by nlinarith [t.2.1, hab], by nlinarith [t.2.2, hab]⟩)) Λ hΛ

/-- The increment only depends on the values of the curve on the interval. -/
theorem incOn_congr {γ δ : ℝ → ℂ} (hγ : Continuous γ) (hδ : Continuous δ) {z : ℂ} {a b : ℝ}
    (hab : a ≤ b) (h : ∀ t ∈ Set.Icc a b, γ t = δ t) :
    incOn γ hγ z a b = incOn δ hδ z a b :=
  pathIncTot_congr (fun t => congrArg (fun w => w - z)
    (h _ ⟨by nlinarith [t.2.1, hab], by nlinarith [t.2.2, hab]⟩))

/-- The increment of an arc on which `γ` is constant vanishes. -/
theorem incOn_const {γ : ℝ → ℂ} (hγ : Continuous γ) {z : ℂ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Set.Icc a b, γ t = γ a) (hav : γ a ≠ z) : incOn γ hγ z a b = 0 := by
  have hconst : ∀ t : unitInterval, γ (a + (t : ℝ) * (b - a)) - z =
      (ContinuousMap.const unitInterval (γ a - z)) t := by
    intro t
    have ht : a + (t : ℝ) * (b - a) ∈ Set.Icc a b :=
      ⟨by nlinarith [t.2.1, hab], by nlinarith [t.2.2, hab]⟩
    rw [ContinuousMap.const_apply, h _ ht]
  rw [incOn, pathIncTot_congr hconst, pathIncTot_const _ (sub_ne_zero.mpr hav)]

/-- **Additivity of the increment over adjacent parameter intervals.** -/
theorem incOn_add {γ : ℝ → ℂ} (hγ : Continuous γ) {z : ℂ} {a b c : ℝ} (hab : a ≤ b)
    (hbc : b ≤ c) (havc : ∀ t ∈ Set.Icc a c, γ t ≠ z) :
    incOn γ hγ z a c = incOn γ hγ z a b + incOn γ hγ z b c := by
  have hcontP : Continuous fun t : unitInterval => γ (a + (t : ℝ) * (c - a)) - z := by fun_prop
  have hneP : ∀ t : unitInterval, γ (a + (t : ℝ) * (c - a)) - z ≠ 0 := fun t =>
    sub_ne_zero.mpr (havc _ ⟨by nlinarith [t.2.1, le_trans hab hbc],
      by nlinarith [t.2.2, le_trans hab hbc]⟩)
  obtain ⟨Λ, hΛ, -, -⟩ := Work.Smooth.SphereJordan.argChangeLift ⟨_, hcontP⟩ hneP
  rcases eq_or_lt_of_le (le_trans hab hbc) with hac | hac
  · -- degenerate: `a = c`
    have hba : b ≤ a := hac ▸ hbc
    have hb_eq : b = a := le_antisymm hba hab
    have hc_eq : c = a := hac.symm
    have hav' : γ a ≠ z := havc a ⟨le_of_eq rfl, hc_eq ▸ le_of_eq rfl⟩
    have e0 : incOn γ hγ z a c = 0 :=
      incOn_const hγ hac.le (fun t ht => by
        have hone : t = a := le_antisymm (hc_eq ▸ ht.2) ht.1
        rw [hone]) hav'
    have e1 : incOn γ hγ z a b = 0 :=
      incOn_const hγ hab (fun t ht => by
        have hone : t = a := le_antisymm (hb_eq ▸ ht.2) ht.1
        rw [hone]) hav'
    have hcb : c = b := hc_eq.trans hb_eq.symm
    have e2 : incOn γ hγ z b c = 0 :=
      incOn_const hγ hbc (fun t ht => by
        have hone : t = b := le_antisymm (hcb ▸ ht.2) ht.1
        rw [hone]) (by rw [hb_eq]; exact hav')
    calc incOn γ hγ z a c = 0 := e0
      _ = incOn γ hγ z a b + incOn γ hγ z b c := by rw [e1, e2]; ring
  · have hca : (0 : ℝ) < c - a := by linarith
    set s : ℝ := (b - a) / (c - a) with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith) hca.le
    have hs1 : s ≤ 1 := by rw [div_le_one hca]; linarith
    set φ₁ : C(unitInterval, unitInterval) :=
      ⟨fun t : unitInterval => ⟨(t : ℝ) * s, mul_nonneg t.2.1 hs0,
          by nlinarith [t.2.2, hs1]⟩,
        Continuous.subtype_mk (by fun_prop) (fun t =>
          ⟨mul_nonneg t.2.1 hs0, by nlinarith [t.2.2, hs1]⟩)⟩ with hφ₁
    set φ₂ : C(unitInterval, unitInterval) :=
      ⟨fun t : unitInterval => ⟨s + (t : ℝ) * (1 - s),
          by nlinarith [t.2.1, hs0, hs1], by nlinarith [t.2.2, hs0, hs1]⟩,
        Continuous.subtype_mk (by fun_prop) (fun t =>
          ⟨by nlinarith [t.2.1, hs0, hs1], by nlinarith [t.2.2, hs0, hs1]⟩)⟩ with hφ₂
    have hφ₁0 : φ₁ 0 = 0 := Subtype.ext (by simp [φ₁])
    have hφ₁1 : φ₁ 1 = (⟨s, ⟨hs0, hs1⟩⟩ : unitInterval) := Subtype.ext (by simp [φ₁])
    have hφ₂0 : φ₂ 0 = (⟨s, ⟨hs0, hs1⟩⟩ : unitInterval) := Subtype.ext (by simp [φ₂])
    have hφ₂1 : φ₂ 1 = 1 := Subtype.ext (by simp [φ₂])
    have hcontA : Continuous fun t : unitInterval => γ (a + (t : ℝ) * (b - a)) - z := by fun_prop
    have hcontC : Continuous fun t : unitInterval => γ (b + (t : ℝ) * (c - b)) - z := by fun_prop
    have hneA : ∀ t : unitInterval, γ (a + (t : ℝ) * (b - a)) - z ≠ 0 := fun t =>
      sub_ne_zero.mpr (havc _ ⟨by nlinarith [t.2.1, hab, hbc],
        by nlinarith [t.2.2, hab, hbc]⟩)
    have hneC : ∀ t : unitInterval, γ (b + (t : ℝ) * (c - b)) - z ≠ 0 := fun t =>
      sub_ne_zero.mpr (havc _ ⟨by nlinarith [t.2.1, hab, hbc],
        by nlinarith [t.2.2, hab, hbc]⟩)
    have hb_eq : b - a = s * (c - a) := by rw [hs]; field_simp
    have hcb_eq : c - b = (1 - s) * (c - a) := by rw [hs]; field_simp; ring
    have hpq₁ : ∀ t : unitInterval,
        γ (a + (t : ℝ) * (b - a)) - z =
          (⟨fun u : unitInterval => γ (a + (u : ℝ) * (c - a)) - z, hcontP⟩ :
            C(unitInterval, ℂ)) (φ₁ t) := by
      intro t
      simp only [ContinuousMap.coe_mk, φ₁]
      rw [hb_eq]; push_cast; ring_nf
    have hpq₂ : ∀ t : unitInterval,
        γ (b + (t : ℝ) * (c - b)) - z =
          (⟨fun u : unitInterval => γ (a + (u : ℝ) * (c - a)) - z, hcontP⟩ :
            C(unitInterval, ℂ)) (φ₂ t) := by
      intro t
      simp only [ContinuousMap.coe_mk, φ₂]
      have harg : b + (t : ℝ) * (c - b) = a + (s + (t : ℝ) * (1 - s)) * (c - a) := by
        rw [hs]; field_simp; ring
      rw [harg]
    have hA : incOn γ hγ z a b = Λ (⟨s, ⟨hs0, hs1⟩⟩ : unitInterval) - Λ 0 := by
      rw [incOn, pathIncTot_comp_sub φ₁ hpq₁ hneP hneA Λ hΛ, hφ₁1, hφ₁0]
    have hC : incOn γ hγ z b c = Λ 1 - Λ (⟨s, ⟨hs0, hs1⟩⟩ : unitInterval) := by
      rw [incOn, pathIncTot_comp_sub φ₂ hpq₂ hneP hneC Λ hΛ, hφ₂1, hφ₂0]
    have hAc : incOn γ hγ z a c = Λ 1 - Λ 0 := incOn_eq_of_lift hγ (le_trans hab hbc) havc Λ hΛ
    rw [hA, hC, hAc]; ring

/-- **Reversal**: the increment over `[b,a]` is the negative of the increment over `[a,b]`. -/
theorem incOn_rev {γ : ℝ → ℂ} (hγ : Continuous γ) {z : ℂ} {a b : ℝ} (hab : a ≤ b)
    (hav : ∀ t ∈ Set.Icc a b, γ t ≠ z) :
    incOn γ hγ z b a = -incOn γ hγ z a b := by
  have hcont : Continuous fun t : unitInterval => γ (a + (t : ℝ) * (b - a)) - z := by fun_prop
  have hne : ∀ t : unitInterval, γ (a + (t : ℝ) * (b - a)) - z ≠ 0 := fun t =>
    sub_ne_zero.mpr (hav _ ⟨by nlinarith [t.2.1, hab], by nlinarith [t.2.2, hab]⟩)
  obtain ⟨Λ, hΛ, -, -⟩ := Work.Smooth.SphereJordan.argChangeLift ⟨_, hcont⟩ hne
  have hne' : ∀ t : unitInterval, γ (b + (t : ℝ) * (a - b)) - z ≠ 0 := fun t =>
    sub_ne_zero.mpr (hav _ ⟨by nlinarith [t.2.1, hab, t.2.2],
      by nlinarith [t.2.2, hab, t.2.1]⟩)
  have hq : ∀ t : unitInterval, γ (b + (t : ℝ) * (a - b)) - z =
      (⟨fun u : unitInterval => γ (a + (u : ℝ) * (b - a)) - z, hcont⟩ : C(unitInterval, ℂ))
        (uIrev t) := by
    intro t
    simp only [ContinuousMap.coe_mk]
    refine congrArg (fun w => γ w - z) ?_
    show b + (t : ℝ) * (a - b) = a + ((uIrev t : unitInterval) : ℝ) * (b - a)
    have hu : ((uIrev t : unitInterval) : ℝ) = 1 - (t : ℝ) := rfl
    rw [hu]; ring
  rw [incOn, pathIncTot_comp_sub uIrev hq hne hne' Λ hΛ, uIrev_one, uIrev_zero]
  rw [incOn_eq_of_lift hγ hab hav Λ hΛ]
  ring

/-! ## The winding number as a full period increment -/

/-- **Rotating the parametrisation of a closed curve does not change its winding number.** -/
theorem windNumber_shift {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (z : ℂ) (hz : ∀ t : ℝ, γ t ≠ z) (c : ℝ) :
    Work.Smooth.SphereJordan.windNumber (fun t => γ (t + c))
        (hγ.comp (continuous_id.add continuous_const)) z =
      Work.Smooth.SphereJordan.windNumber γ hγ z := by
  set c₀ : C(unitInterval, ℂ) :=
    Work.Smooth.SphereJordan.curveLoop (fun t => γ t - z) (hγ.sub continuous_const) with hc₀
  set c₁ : C(unitInterval, ℂ) :=
    Work.Smooth.SphereJordan.curveLoop (fun t => γ (t + c) - z)
      ((hγ.comp (continuous_id.add continuous_const)).sub continuous_const) with hc₁
  have hc₀app : ∀ t : unitInterval, c₀ t = γ (2 * Real.pi * (t : ℝ)) - z := fun t => rfl
  have hc₁app : ∀ t : unitInterval, c₁ t = γ (2 * Real.pi * (t : ℝ) + c) - z := by
    intro t
    show γ (2 * Real.pi * (t : ℝ) + c) - z = γ (2 * Real.pi * (t : ℝ) + c) - z
    rfl
  have h₀ : ∀ t : unitInterval, c₀ t ≠ 0 := fun t => sub_ne_zero.mpr (hz _)
  have h₁ : ∀ t : unitInterval, c₁ t ≠ 0 := fun t => sub_ne_zero.mpr (hz _)
  have hloop : ∀ s : unitInterval, γ (2 * Real.pi * (0 : ℝ) + (s : ℝ) * c) - z =
      γ (2 * Real.pi * (1 : ℝ) + (s : ℝ) * c) - z := by
    intro s
    have h1 : 2 * Real.pi * (1 : ℝ) + (s : ℝ) * c = 2 * Real.pi + (s : ℝ) * c := by ring
    rw [h1, show 2 * Real.pi * (0 : ℝ) + (s : ℝ) * c = (s : ℝ) * c from by ring,
      show 2 * Real.pi + (s : ℝ) * c = (s : ℝ) * c + 2 * Real.pi from by ring,
      hper]
  have hmain := Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy h₀ h₁
    ⟨fun p : unitInterval × unitInterval =>
      γ (2 * Real.pi * (p.1 : ℝ) + (p.2 : ℝ) * c) - z, by fun_prop⟩
    (fun p => sub_ne_zero.mpr (hz _))
    (fun t => by
      show γ (2 * Real.pi * (t : ℝ) + (0 : ℝ) * c) - z = _
      rw [show (0 : ℝ) * c = 0 from by ring, add_zero]; rfl)
    (fun t => by
      show γ (2 * Real.pi * (t : ℝ) + (1 : ℝ) * c) - z = _
      rw [show (1 : ℝ) * c = c from by ring]; rfl)
    hloop
  have h0def : Work.Smooth.SphereJordan.windNumber γ hγ z =
      Work.Smooth.SphereJordan.loopIndex c₀ := by rw [hc₀]; rfl
  have h1def : Work.Smooth.SphereJordan.windNumber (fun t => γ (t + c))
      (hγ.comp (continuous_id.add continuous_const)) z =
      Work.Smooth.SphereJordan.loopIndex c₁ := by rw [hc₁]; rfl
  rw [h0def, h1def]
  exact hmain.symm

/-- **The increment over one full period is the winding number times `2πi`.** -/
theorem incOn_windNumber {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (z : ℂ) (hz : ∀ t : ℝ, γ t ≠ z) :
    incOn γ hγ z 0 (2 * Real.pi) = (Work.Smooth.SphereJordan.windNumber γ hγ z : ℂ)
      * (2 * (Real.pi : ℂ) * Complex.I) := by
  set P : C(unitInterval, ℂ) :=
    ⟨fun t : unitInterval => γ (0 + (t : ℝ) * (2 * Real.pi - 0)) - z, by fun_prop⟩ with hP
  set Q : C(unitInterval, ℂ) :=
    Work.Smooth.SphereJordan.curveLoop (fun t => γ t - z) (hγ.sub continuous_const) with hQ
  have hPQ : ∀ t : unitInterval, P t = Q t := by
    intro t
    simp only [P, Q, Work.Smooth.SphereJordan.curveLoop, ContinuousMap.coe_mk]
    ring_nf
  have hneP : ∀ t : unitInterval, P t ≠ 0 := by
    intro t
    simp only [P, ContinuousMap.coe_mk]
    exact sub_ne_zero.mpr (hz _)
  have hneQ : ∀ t : unitInterval, Q t ≠ 0 := by
    intro t
    simp only [Q, Work.Smooth.SphereJordan.curveLoop, ContinuousMap.coe_mk]
    exact sub_ne_zero.mpr (hz _)
  have hloop : Q 0 = Q 1 := by
    simp only [Q, Work.Smooth.SphereJordan.curveLoop, ContinuousMap.coe_mk]
    rw [show (2 : ℝ) * Real.pi * ((0 : unitInterval) : ℝ) = 0 from by simp,
      show (2 : ℝ) * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi from by simp]
    simpa using (hper 0).symm
  have hval : incOn γ hγ z 0 (2 * Real.pi) = pathIncTot Q := by
    rw [incOn]
    exact pathIncTot_congr (fun t => hPQ t)
  rw [hval, pathIncTot_eq_loopIndex Q hneQ hloop]
  rfl

/-- **The increment over any period-length interval is the winding number times `2πi`.** -/
theorem incOn_period {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (z : ℂ) (hz : ∀ t : ℝ, γ t ≠ z) (a : ℝ) :
    incOn γ hγ z a (a + 2 * Real.pi) = (Work.Smooth.SphereJordan.windNumber γ hγ z : ℂ)
      * (2 * (Real.pi : ℂ) * Complex.I) := by
  have hshift : incOn γ hγ z a (a + 2 * Real.pi) =
      incOn (fun s : ℝ => γ (s + a))
        (hγ.comp (continuous_id.add continuous_const)) z 0 (2 * Real.pi) := by
    refine pathIncTot_congr (fun t => ?_)
    simp only [incOn, ContinuousMap.coe_mk]
    congr 1
    ring
  have hper' : Function.Periodic (fun s : ℝ => γ (s + a)) (2 * Real.pi) := fun s => by
    show γ (s + 2 * Real.pi + a) = γ (s + a)
    rw [show s + 2 * Real.pi + a = (s + a) + 2 * Real.pi from by ring, hper]
  rw [hshift, incOn_windNumber _ hper' z (fun t => hz _), windNumber_shift hγ hper z hz a]

end

end Work.SphereJordan
