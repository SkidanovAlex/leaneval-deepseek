import Submission.Work.ThomBordism.Grassmann.Torsion.ModelGeom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The radial deformation of the total space towards the disc bundle

The map `p ↦ (max 1 (fibN p))⁻¹ • p` rescaled fibrewise: it contracts the total space of the
tautological bundle onto its closed unit disc bundle `{fibN ≤ 1}` and restricts to the identity on
it.  Because the coefficient is `1/max 1 (fibN p)`, it is *continuous everywhere* (it is bounded by
`1` and equals `1` where `fibN ≤ 1`), and
`Work.Thom.continuous_smul_section` applies verbatim.  This is the tool for

* `puncturedDiscPairIso`: `(D, D∖0)` and `(E, E∖0)` are homotopy equivalent pairs, and
* `discPairIso`: the annulus `{1 < fibN < 2}` is a deformation retract of `{0 < fibN < 2}`.
-/

open scoped Topology

namespace Work.ThomBordism.Grassmann.Torsion

open Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-- The disc `{fibN < 2}` of the total space. -/
abbrev discSet (k m : ℕ) : Set (TM k m) := {p : TM k m | fibN k m p < 2}

/-- The punctured disc `{0 < fibN < 2}`. -/
abbrev punctSet (k m : ℕ) : Set (TM k m) := {p : TM k m | 0 < fibN k m p ∧ fibN k m p < 2}

/-- The annulus `{1 < fibN < 2}`. -/
abbrev annSet (k m : ℕ) : Set (TM k m) := {p : TM k m | 1 < fibN k m p ∧ fibN k m p < 2}

/-- The disc `{fibN < 2}`, as a type. -/
abbrev DiscT (k m : ℕ) : Type := ↥(discSet k m)

/-- The punctured disc, as a type. -/
abbrev PunctT (k m : ℕ) : Type := ↥(punctSet k m)

/-- The radial coefficient `1 / max 1 (fibN p)`: equals `1` on `{fibN ≤ 1}` and `1/fibN p`
beyond. -/
noncomputable def radCoef (k m : ℕ) (p : TM k m) : ℝ := (max 1 (fibN k m p))⁻¹

theorem continuous_radCoef (k m : ℕ) : Continuous (radCoef k m) := by
  unfold radCoef
  exact Continuous.inv₀ (continuous_const.max (fibN_continuous k m))
    (fun p => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))

theorem radCoef_pos (k m : ℕ) (p : TM k m) : 0 < radCoef k m p :=
  inv_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

theorem radCoef_le_one (k m : ℕ) (p : TM k m) : radCoef k m p ≤ 1 := by
  rw [radCoef, inv_le_one₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
  exact le_max_left _ _

theorem radCoef_mul_fibN (k m : ℕ) (p : TM k m) :
    radCoef k m p * fibN k m p = min (fibN k m p) 1 := by
  rw [radCoef, inv_mul_eq_div]
  rcases le_total (fibN k m p) 1 with h | h
  · rw [min_eq_left h, max_eq_left h, div_one]
  · rw [min_eq_right h, max_eq_right h, div_self (ne_of_gt (lt_of_lt_of_le zero_lt_one h))]

/-- The radial map `p ↦ (max 1 (fibN p))⁻¹ • p` of the total space, as a continuous map. -/
noncomputable def radPt (k m : ℕ) : C(TM k m, TM k m) where
  toFun p := ⟨p.1, radCoef k m p • p.2⟩
  continuous_toFun :=
    Work.Thom.continuous_smul_section (tautologicalBundle k m)
      (ContinuousMap.id (TM k m)) ⟨radCoef k m, continuous_radCoef k m⟩

@[simp] theorem radPt_apply (k m : ℕ) (p : TM k m) :
    radPt k m p = ⟨p.1, radCoef k m p • p.2⟩ := rfl

theorem fibN_radPt (k m : ℕ) (p : TM k m) : fibN k m (radPt k m p) = min (fibN k m p) 1 := by
  rw [radPt_apply, fibN_smul k m (le_of_lt (radCoef_pos k m p)), radCoef_mul_fibN]

theorem fibN_radPt_le_one (k m : ℕ) (p : TM k m) : fibN k m (radPt k m p) ≤ 1 := by
  rw [fibN_radPt]; exact min_le_right _ _

theorem radPt_eq_self (k m : ℕ) {p : TM k m} (hp : fibN k m p ≤ 1) : radPt k m p = p := by
  show (⟨p.1, radCoef k m p • p.2⟩ : TM k m) = p
  have h1 : radCoef k m p = 1 := by rw [radCoef, max_eq_left hp, inv_one]
  rw [h1, one_smul]

/-! ## The annulus coefficient

The coefficient that pushes the punctured disc `{0 < fibN < 2}` into the annulus
`{1 < fibN < 2}`: `p ↦ s (fibN p) / fibN p` with `s t = 1 + min t (2 - t)/4`, which satisfies
`1 < s t < 2` for `0 < t < 2`. -/

/-- The "annulus shift" `s t = 1 + min t (2 - t)/4`. -/
noncomputable def annShift (t : ℝ) : ℝ := 1 + min t (2 - t) / 4

theorem continuous_annShift : Continuous annShift := by
  unfold annShift; fun_prop

theorem annShift_mem {t : ℝ} (h0 : 0 < t) (h2 : t < 2) : 1 < annShift t ∧ annShift t < 2 := by
  have hmin_pos : 0 < min t (2 - t) := lt_min h0 (by linarith)
  have hmin_lt : min t (2 - t) < 2 := lt_of_le_of_lt (min_le_left _ _) h2
  constructor <;> · unfold annShift; linarith

theorem annShift_pos {t : ℝ} (h0 : 0 < t) (h2 : t < 2) : 0 < annShift t :=
  lt_trans zero_lt_one (annShift_mem h0 h2).1

theorem continuous_annShift_comp (k m : ℕ) : Continuous fun p : TM k m => annShift (fibN k m p) :=
  continuous_annShift.comp (fibN_continuous k m)

/-- The radial coefficient of the annulus: `s (fibN p) / fibN p`.  It is continuous on the
punctured disc (where `fibN ≠ 0`), and `fibN (c p • p) = s (fibN p) ∈ (1,2)` there. -/
noncomputable def annCoef (k m : ℕ) (p : TM k m) : ℝ := annShift (fibN k m p) / fibN k m p

/-- **The annulus coefficient is continuous on the punctured disc.** -/
theorem continuous_annCoef_subtype {S : Set (TM k m)} (hS : ∀ p ∈ S, 0 < fibN k m p) :
    Continuous fun p : ↥S => annCoef k m p.1 := by
  have hnum : Continuous fun p : ↥S => annShift (fibN k m p.1) :=
    continuous_annShift.comp ((fibN_continuous k m).comp continuous_subtype_val)
  have hden : Continuous fun p : ↥S => fibN k m p.1 :=
    (fibN_continuous k m).comp continuous_subtype_val
  have hne : ∀ p : ↥S, fibN k m p.1 ≠ 0 := fun p => ne_of_gt (hS p.1 p.2)
  have hinv : Continuous fun p : ↥S => (fibN k m p.1)⁻¹ := hden.inv₀ hne
  have hmul : Continuous fun p : ↥S => annShift (fibN k m p.1) * (fibN k m p.1)⁻¹ := hnum.mul hinv
  have heq : (fun p : ↥S => annCoef k m p.1)
      = fun p : ↥S => annShift (fibN k m p.1) * (fibN k m p.1)⁻¹ := by
    funext p
    rw [annCoef, div_eq_mul_inv]
  rw [heq]
  exact hmul

theorem annCoef_pos {k m : ℕ} {p : TM k m} (h0 : 0 < fibN k m p) (h2 : fibN k m p < 2) :
    0 < annCoef k m p :=
  div_pos (annShift_pos h0 h2) h0

theorem annCoef_mul_fibN {k m : ℕ} {p : TM k m} (h : 0 < fibN k m p) :
    annCoef k m p * fibN k m p = annShift (fibN k m p) := by
  rw [annCoef, div_mul_cancel₀ _ (ne_of_gt h)]

theorem fibN_radPt_pos_iff (k m : ℕ) (p : TM k m) : 0 < fibN k m (radPt k m p) ↔ 0 < fibN k m p := by
  rw [fibN_radPt, lt_min_iff]; exact ⟨fun h => h.1, fun h => ⟨h, zero_lt_one⟩⟩

/-- The coefficient of the radial deformation at time `t`: `(1-t)·radCoef p + t`; at `t = 0` it is
the retraction coefficient and at `t = 1` it is `1`. -/
noncomputable def homCoeff (k m : ℕ) (t : ℝ) (p : TM k m) : ℝ := (1 - t) * radCoef k m p + t

theorem continuous_homCoeff (k m : ℕ) : Continuous fun z : ↥(unitInterval) × TM k m =>
    homCoeff k m (z.1 : ℝ) z.2 := by
  have h1 : Continuous fun z : ↥(unitInterval) × TM k m => (((z.1 : ↥unitInterval) : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous fun z : ↥(unitInterval) × TM k m => radCoef k m z.2 :=
    (continuous_radCoef k m).comp continuous_snd
  unfold homCoeff
  exact ((continuous_const.sub h1).mul h2).add h1

/-- The deformation point `z ↦ ⟨p, c p • v⟩` of `p`. -/
noncomputable def homPt (k m : ℕ) (z : ↥(unitInterval) × TM k m) : TM k m :=
  ⟨z.2.1, homCoeff k m (z.1 : ℝ) z.2 • z.2.2⟩

theorem continuous_homPt (k m : ℕ) : Continuous (homPt k m) :=
  Work.Thom.continuous_smul_section (tautologicalBundle k m)
    ⟨fun z : ↥(unitInterval) × TM k m => z.2, continuous_snd⟩
    ⟨fun z => homCoeff k m (z.1 : ℝ) z.2, continuous_homCoeff k m⟩

theorem homCoeff_zero (k m : ℕ) (p : TM k m) :
    homCoeff k m ((0 : ↥unitInterval) : ℝ) p = radCoef k m p := by
  unfold homCoeff
  norm_num

theorem homCoeff_one (k m : ℕ) (p : TM k m) :
    homCoeff k m ((1 : ↥unitInterval) : ℝ) p = 1 := by
  unfold homCoeff
  norm_num

theorem homPt_zero (k m : ℕ) (p : TM k m) :
    homPt k m ⟨(0 : ↥unitInterval), p⟩ = radPt k m p := by
  show (⟨p.1, homCoeff k m (((0 : ↥unitInterval) : ℝ)) p • p.2⟩ : TM k m) = radPt k m p
  rw [radPt_apply]
  exact congrArg (fun c : ℝ => (⟨p.1, c • p.2⟩ : TM k m)) (homCoeff_zero k m p)

theorem homPt_one (k m : ℕ) (p : TM k m) :
    homPt k m ⟨(1 : ↥unitInterval), p⟩ = p := by
  show (⟨p.1, homCoeff k m (((1 : ↥unitInterval) : ℝ)) p • p.2⟩ : TM k m) = p
  rw [homCoeff_one k m p, one_smul]

theorem fibN_homPt (k m : ℕ) (z : ↥(unitInterval) × TM k m) :
    fibN k m (homPt k m z)
      = (1 - (z.1 : ℝ)) * min (fibN k m z.2) 1 + (z.1 : ℝ) * fibN k m z.2 := by
  have hcoef : 0 ≤ homCoeff k m (z.1 : ℝ) z.2 := by
    unfold homCoeff
    have h1 : 0 ≤ 1 - (z.1 : ℝ) := sub_nonneg.mpr (Set.mem_Icc.mp z.1.2).2
    have h2 : 0 ≤ radCoef k m z.2 := le_of_lt (radCoef_pos k m z.2)
    have h3 : 0 ≤ (z.1 : ℝ) := (Set.mem_Icc.mp z.1.2).1
    nlinarith
  rw [homPt, fibN_smul k m hcoef]
  have hkey : (radCoef k m z.2 - (z.1 : ℝ) * radCoef k m z.2) * fibN k m z.2
      = (1 - (z.1 : ℝ)) * (radCoef k m z.2 * fibN k m z.2) := by ring
  rw [homCoeff, add_mul, sub_mul, one_mul, hkey, radCoef_mul_fibN]

theorem fibN_homPt_le (k m : ℕ) (z : ↥(unitInterval) × TM k m) :
    fibN k m (homPt k m z) ≤ fibN k m z.2 := by
  rw [fibN_homPt]
  have h1 : 0 ≤ 1 - (z.1 : ℝ) := sub_nonneg.mpr (Set.mem_Icc.mp z.1.2).2
  have h2 : 0 ≤ (z.1 : ℝ) := (Set.mem_Icc.mp z.1.2).1
  have h3 : min (fibN k m z.2) 1 ≤ fibN k m z.2 := min_le_left _ _
  nlinarith

theorem fibN_homPt_pos (k m : ℕ) (z : ↥(unitInterval) × TM k m) (h : 0 < fibN k m z.2) :
    0 < fibN k m (homPt k m z) := by
  rw [fibN_homPt]
  have h3 : 0 < min (fibN k m z.2) 1 := lt_min h zero_lt_one
  rcases lt_or_eq_of_le (Set.mem_Icc.mp z.1.2).2 with hlt | heq
  · have h1 : 0 < 1 - (z.1 : ℝ) := sub_pos.mpr hlt
    have h2 : 0 ≤ (z.1 : ℝ) := (Set.mem_Icc.mp z.1.2).1
    nlinarith [mul_pos h1 h3, mul_nonneg h2 (le_of_lt h)]
  · rw [heq]
    norm_num
    exact h


end

end Work.ThomBordism.Grassmann.Torsion
