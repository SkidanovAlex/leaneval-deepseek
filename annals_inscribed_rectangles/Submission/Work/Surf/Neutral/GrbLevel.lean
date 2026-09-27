import Mathlib
import Submission.Work.Surf.grbDefs
import Submission.Work.Surf.grbCurve
import Submission.Work.Surf.goodRayDefs
import Submission.Work.Surf.defs
import Submission.Work.Drive.Neutral.HalfDir
import Submission.Work.Surf.Neutral.WindingEqTwoMulDegreeHalfDir
import Submission.Work.Surf.ncard_crossSet_mod_two
import Submission.Work.Surf.hasDerivAt_of_lift_arg
import Submission.Work.Surf.volume_badSet_eq_zero
import Submission.Work.Surf.chordFamily
import Submission.Work.Drive.winding_homotopy

/-!
# (Neutral copy) `GrbLevel`

Verbatim copy of the module `Work.Surf.grbLevel` in the namespace `Work.Surf.ChordN`, with:

* every import of a module whose closure contains the declaration `Work.Drive.toC` of
  `Submission/Work/Drive/winding_eq_crossing_sum.lean` redirected to the neutral copy of that module
  (the only such channel is the import of `Submission/Work/Drive/line_crossings_even.lean`, replaced
  by `Submission/Work/Drive/Neutral/HalfDir.lean`);
* every qualified reference to the declarations of the neutral half-direction file
  (`halfDir`, `continuous_halfDir`, `halfDir_apply`, `halfDir_add_self`, `rescaleAngle`,
  `twoPiNeZero`, `toC`) redirected to `Work.Drive.NH`.

Reason: `Work.Drive.toC` is declared both in `Submission/Work/Drive/winding_eq_crossing_sum.lean` (in
the chord-parity world) and in `Submission/Work/Drive/UmlaufSetup.lean` (in the capping world), so the
two worlds cannot be imported together.  With these copies,
`Work.Surf.ChordN.chord_crossing_parity` — the strict base case of the mod-2 intersection form of
`ℝP²` — is importable next to `Work.Drive.CappingSpace`; see
`Submission/Work/Drive/cutTransportStrict.lean`.
-/
/-!
# The honest direction of the boundary curve of the difference map

The counting lemma `Work.Surf.ChordN.grb_level_odd`: a transverse level of a continuous lift of the honest
direction of the boundary curve `grbCurve a b` is met in a number of points congruent modulo `2` to
the honest degree `grbDeg a b`.
-/

namespace Work.Surf.ChordN

open Work.Drive.NH

open Set Work.Surf.GRB Work.Drive

noncomputable section

open scoped Topology

section Counting

variable {a b : ℝ → EuclideanSpace ℝ (Fin 2)}

/-- The boundary curve as a function on `ℝ`. -/
def grbCurveR (a b : ℝ → EuclideanSpace ℝ (Fin 2)) : ℝ → ℝ × ℝ :=
  fun t => grbCurve a b (t : UnitAddCircle)

lemma continuous_grbCurveR (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) :
    Continuous (grbCurveR a b) :=
  continuous_grbCurve_coe a b ha hb

lemma contDiff_grbCurveR (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) :
    ContDiff ℝ 1 (grbCurveR a b) :=
  contDiff_grbCurve_coe a b ha hb

lemma grbCurveR_ne_zero (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 →
      a s = b t → s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1) (t : ℝ) :
    grbCurveR a b t ≠ 0 :=
  grbCurve_ne_zero (a := a) (b := b) hint

lemma grbCurveR_hasDerivAt (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) (t : ℝ) :
    HasDerivAt (grbCurveR a b) (deriv (grbCurveR a b) t) t :=
  ((contDiff_grbCurveR ha hb).differentiable (by norm_num)).differentiableAt.hasDerivAt

/-- The complexified boundary curve. -/
def grbCurveC (a b : ℝ → EuclideanSpace ℝ (Fin 2)) : ℝ → ℂ :=
  fun t => gToC (grbCurveR a b t)

lemma gToC_hasDerivAt {f : ℝ → ℝ × ℝ} {f' : ℝ × ℝ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => gToC (f s)) (gToC f') t := by
  have h1 : HasDerivAt (fun s => (f s).1) f'.1 t := by
    have := h.hasFDerivAt.fst
    simpa using this.hasDerivAt
  have h2 : HasDerivAt (fun s => (f s).2) f'.2 t := by
    have := h.hasFDerivAt.snd
    simpa using this.hasDerivAt
  have h3 : HasDerivAt (fun s => ((f s).1 : ℂ)) ((f'.1 : ℂ)) t :=
    (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t h1).congr_deriv (by simp)
  have h4 : HasDerivAt (fun s => ((f s).2 : ℂ) * Complex.I) ((f'.2 : ℂ) * Complex.I) t := by
    have h5 : HasDerivAt (fun s => ((f s).2 : ℂ)) ((f'.2 : ℂ)) t :=
      (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t h2).congr_deriv (by simp)
    simpa using h5.mul_const Complex.I
  have hval : ((f'.1 : ℂ) + (f'.2 : ℂ) * Complex.I) = gToC f' := by
    apply Complex.ext <;> simp [gToC]
  have h6 : HasDerivAt (fun s => ((f s).1 : ℂ) + ((f s).2 : ℂ) * Complex.I) (gToC f') t :=
    (h3.add h4).congr_deriv hval
  exact h6.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
    apply Complex.ext <;> simp [gToC])

lemma continuous_grbCurveC (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) :
    Continuous (grbCurveC a b) :=
  gToC_continuous.comp (continuous_grbCurveR ha hb)

lemma grbCurveC_ne_zero (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 →
      a s = b t → s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1) (t : ℝ) :
    grbCurveC a b t ≠ 0 :=
  gToC_ne_zero_iff.mpr (grbCurveR_ne_zero (a := a) (b := b) hint t)

lemma hasDerivAt_grbCurveC (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) (t : ℝ) :
    HasDerivAt (grbCurveC a b) (gToC (deriv (grbCurveR a b) t)) t :=
  gToC_hasDerivAt (grbCurveR_hasDerivAt (a := a) (b := b) ha hb t)

lemma deriv_grbCurveC (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) (t : ℝ) :
    deriv (grbCurveC a b) t = gToC (deriv (grbCurveR a b) t) :=
  (hasDerivAt_grbCurveC (a := a) (b := b) ha hb t).deriv

end Counting

/-! ## The parity of the boundary ray count -/

section LevelOdd

variable {a b : ℝ → EuclideanSpace ℝ (Fin 2)}

/-- The honest direction map of the boundary curve. -/
def grbDir (a b : ℝ → EuclideanSpace ℝ (Fin 2)) : UnitAddCircle → UnitAddCircle :=
  halfDir (grbCurve a b) 0

lemma continuous_grbDir (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1) :
    Continuous (grbDir a b) :=
  continuous_halfDir _ (continuous_grbCurve a b ha hb)
    (by rintro ⟨u, hu⟩
        obtain ⟨t, ht⟩ := Quotient.exists_rep u
        rw [← ht] at hu
        exact grbCurve_ne_zero (a := a) (b := b) hint (u := t) hu)

/-- The honest degree of the boundary curve. -/
def grbDeg (a b : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1) : ℤ :=
  degree (grbDir a b) (continuous_grbDir ha hb hint)

/-- A continuous lift of the honest direction of the boundary curve. -/
noncomputable def grbLift (a b : ℝ → EuclideanSpace ℝ (Fin 2)) (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1) : ℝ → ℝ :=
  liftOf (grbDir a b) (continuous_grbDir ha hb hint)

lemma continuous_grbLift (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1) :
    Continuous (grbLift a b ha hb hint) :=
  liftOf_continuous _ _

lemma grbLift_lifts (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1) (t : ℝ) :
    ((grbLift a b ha hb hint t : ℝ) : UnitAddCircle) = grbDir a b (t : UnitAddCircle) :=
  liftOf_lifts _ _ t

lemma grbLift_add_one (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1) (t : ℝ) :
    grbLift a b ha hb hint (t + 1) = grbLift a b ha hb hint t + (grbDeg a b ha hb hint : ℝ) :=
  liftOf_add_one _ _ t

lemma grbCurveC_eq (a b : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    grbCurveC a b t = toC (grbCurve a b (t : UnitAddCircle) - 0) := by
  rw [sub_zero, grbCurveC, grbCurveR]
  apply Complex.ext <;> simp [gToC, toC]

/-- The lift property in the form needed for `Work.Surf.hasDerivAt_of_lift_arg`. -/
lemma grbLift_arg (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1) (t : ℝ) :
    ((grbLift a b ha hb hint t : ℝ) : UnitAddCircle) =
      ((grbCurveC a b t).arg / (2 * Real.pi) : ℝ) := by
  rw [grbLift_lifts, grbDir, halfDir_apply, grbCurveC_eq]

/-- The derivative of the lift at a crossing, from `hasDerivAt_of_lift_arg`. -/
lemma hasDerivAt_grbLift (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1) (t : ℝ) :
    HasDerivAt (grbLift a b ha hb hint) ((deriv (grbCurveC a b) t / grbCurveC a b t).im
      / (2 * Real.pi)) t := by
  refine hasDerivAt_of_lift_arg (γ := grbCurveC a b) ?_ (grbCurveC_ne_zero (a := a) (b := b) hint)
    (continuous_grbLift ha hb hint) (grbLift_arg ha hb hint)
  have h := hasDerivAt_grbCurveC (a := a) (b := b) ha hb t
  rwa [← deriv_grbCurveC ha hb t] at h

/-- **The crossing count of a transverse level has the parity of the honest degree.** -/
theorem grb_level_odd (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1)
    (α : ℝ) (htr : ∀ t ∈ Set.Ico (0:ℝ) 1,
      (∃ k : ℤ, grbLift a b ha hb hint t - α = (k : ℝ)) →
      deriv (grbLift a b ha hb hint) t ≠ 0) :
    Odd (Set.ncard {t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧
        grbDir a b (t : UnitAddCircle) = (α : UnitAddCircle)}) ↔
      Odd (grbDeg a b ha hb hint) := by
  set L := grbLift a b ha hb hint with hL
  have hLcont : Continuous L := continuous_grbLift ha hb hint
  have hLper : ∀ t : ℝ, L (t + 1) = L t + (grbDeg a b ha hb hint : ℝ) :=
    fun t => grbLift_add_one ha hb hint t
  have hLlifts : ∀ t : ℝ, ((L t : ℝ) : UnitAddCircle) = grbDir a b (t : UnitAddCircle) :=
    fun t => grbLift_lifts ha hb hint t
  set G : ℝ → ℝ := fun t => L t - α with hG
  have hGcont : Continuous G := hLcont.sub continuous_const
  have hGper : ∀ t : ℝ, G (t + 1) = G t + (grbDeg a b ha hb hint : ℝ) := by
    intro t
    simp only [hG]
    rw [hLper t]
    ring
  have hGderiv : ∀ t : ℝ, t ∈ Set.Ico (0:ℝ) 1 → (∃ k : ℤ, G t = (k:ℝ)) →
      HasDerivAt G (deriv G t) t ∧ deriv G t ≠ 0 := by
    intro t ht hk
    have hk' : ∃ k : ℤ, L t - α = (k:ℝ) := hk
    have hdL : deriv L t ≠ 0 := htr t ht hk'
    have h1 : HasDerivAt L (deriv L t) t := by
      have h := hasDerivAt_grbLift (a := a) (b := b) ha hb hint t
      exact h.congr_deriv h.deriv.symm
    have h2 : HasDerivAt G (deriv L t) t := by
      simpa only [hG] using h1.sub_const α
    have h3 : deriv G t = deriv L t := by
      simp only [hG, deriv_sub_const]
    exact ⟨h3 ▸ h2, by rw [h3]; exact hdL⟩
  obtain ⟨hfin, hmod⟩ := ncard_crossSet_mod_two G hGcont (grbDeg a b ha hb hint) hGper hGderiv
  have hset : {t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧ ∃ k : ℤ, G t = (k:ℝ)}
      = {t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧ grbDir a b (t : UnitAddCircle) = (α : UnitAddCircle)} := by
    ext t
    constructor
    · rintro ⟨ht, k, hk⟩
      refine ⟨ht, ?_⟩
      have hLt : L t = α + (k:ℝ) := by simp only [hG] at hk; linarith
      rw [← hLlifts t, hLt]
      have : (((α + (k:ℝ)) : ℝ) : UnitAddCircle) = (α : UnitAddCircle) := by
        rw [AddCircle.coe_add, show (((k:ℝ)) : UnitAddCircle) = 0 from ?_, add_zero]
        rw [show (k:ℝ) = k • (1:ℝ) by simp, AddCircle.coe_zsmul, AddCircle.coe_period (1:ℝ),
          zsmul_zero]
      exact this
    · rintro ⟨ht, ht'⟩
      refine ⟨ht, ?_⟩
      have h1 : ((L t : ℝ) : UnitAddCircle) = (α : UnitAddCircle) := by
        rw [hLlifts t]; exact ht'
      have h2 : ((L t - α : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub, h1, sub_self]
      obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1:ℝ))).mp h2
      refine ⟨k, ?_⟩
      simp only [hG]
      rw [← hk, zsmul_eq_mul, mul_one]
  rw [hset] at hmod
  rw [modEq_two_iff_odd] at hmod
  rw [odd_natCast] at hmod
  exact hmod

end LevelOdd

end

end Work.Surf.ChordN
