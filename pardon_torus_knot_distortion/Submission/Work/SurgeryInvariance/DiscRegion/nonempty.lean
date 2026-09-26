import Mathlib
import Submission.Work.SurgeryInvariance.Defs

/-!
# Every parametrised torus carries an embedded disc

This file proves `Work.SurgeryInvariance.DiscRegion.nonempty`: for every `ParamTorus P` there is
an embedded disc of the surface `F = P.carrier`, in the sense of the structure
`Work.SurgeryInvariance.DiscRegion`.

The disc is the image of the closed unit disc of the parameter plane under the parametrisation
`P.psi`:

  `e z = P.psi z.re z.im`,  `z ∈ Metric.closedBall (0 : ℂ) 1`.

Since the parameters range over `|z| ≤ 1`, the coordinates `z.re, z.im` vary in an interval of
length `< 2π`, so `e` is injective (`P.inj_mod`) and lands in the carrier
(`P.psi_mem_carrier`).

The only substantial point is that the *interior* of this disc is open in the surface
(`open_interior`): the interior is the image under the parametrisation of the open unit disc
`{|z| < 1} ⊆ ℝ²`, and the parametrisation is the quotient map
`ℝ² → ℝ²/2πℤ²` (an open map) followed by the homeomorphism
`Work.TorusCover.quotHomeo P : ℝ²/2πℤ² ≃ₜ P.carrier` of the sibling development.  Hence the
saturation of an open set of the parameter plane is again open, and its homeomorphic image in
`P.carrier` is open.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.SurgeryInvariance.DiscRegion

noncomputable section

/-- The open unit disc of the parameter plane, written in rectangular coordinates. -/
def openUnitDisc : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 < 1}

theorem isOpen_unitDisc : IsOpen openUnitDisc := by
  have hcont : Continuous (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) := by continuity
  have : openUnitDisc = (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) ⁻¹' (Set.Iio 1) := rfl
  rw [this]
  exact hcont.isOpen_preimage _ isOpen_Iio

/-- Membership in the open unit disc, for a complex number read as a parameter. -/
theorem mem_unitDisc_iff (z : ℂ) : ((z.re, z.im) ∈ openUnitDisc) ↔ ‖z‖ < 1 := by
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  constructor
  · intro h
    have : ‖z‖ ^ 2 < 1 := by rw [hsq]; exact h
    nlinarith [norm_nonneg z]
  · intro h
    have : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z, h]
    rw [hsq] at this; exact this

/-- Two parameter points give the same coset of the period lattice exactly when they differ by a
lattice element. -/
theorem mk_eq_iff (r p : ℝ × ℝ) :
    (QuotientAddGroup.mk r : (ℝ × ℝ) ⧸ Work.TorusCover.lattice) = QuotientAddGroup.mk p ↔
      r - p ∈ Work.TorusCover.lattice := by
  constructor
  · intro h; exact Work.TorusCover.sub_mem_lattice_of_leftRel ((Quotient.eq'').mp h)
  · intro h; exact (Quotient.eq'').mpr (Work.TorusCover.leftRel_of_sub_mem_lattice h)

/-- The closed unit disc of the parameter plane, mapped into `ℝ³` by the parametrisation. -/
def discMap (P : Work.CoreTopology.ParamTorus) :
    C(Metric.closedBall (0 : ℂ) 1, R3) where
  toFun := fun z => P.psi (z : ℂ).re (z : ℂ).im
  continuous_toFun :=
    P.cont.comp ((Complex.continuous_re.comp continuous_subtype_val).prodMk
      (Complex.continuous_im.comp continuous_subtype_val))

@[simp] theorem discMap_apply (P : Work.CoreTopology.ParamTorus)
    (z : Metric.closedBall (0 : ℂ) 1) :
    discMap P z = P.psi (z : ℂ).re (z : ℂ).im := rfl

theorem discMap_mem (P : Work.CoreTopology.ParamTorus)
    (z : Metric.closedBall (0 : ℂ) 1) : discMap P z ∈ P.carrier :=
  P.psi_mem_carrier _ _

/-- The disc map is injective: the parameters `z.re, z.im` range over an interval of length at
most `2`, hence two of them have the same image only if they agree modulo `2π` in each
coordinate, which forces them to be equal. -/
theorem discMap_injective (P : Work.CoreTopology.ParamTorus) :
    Function.Injective (discMap P) := by
  intro z w h
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := (P.psi_eq_iff _ _ _ _).mp h
  have hzn : ‖(z : ℂ)‖ ≤ 1 := by
    have h' : (z : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := z.2
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h'
    exact h'
  have hwn : ‖(w : ℂ)‖ ≤ 1 := by
    have h' : (w : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := w.2
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h'
    exact h'
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hk0 : k = 0 := by
    have hkre : (z : ℂ).re - (w : ℂ).re = k * (2 * Real.pi) := by linarith
    have h1 : |(k : ℝ) * (2 * Real.pi)| ≤ 2 := by
      rw [← hkre]
      calc |(z : ℂ).re - (w : ℂ).re| ≤ |(z : ℂ).re| + |(w : ℂ).re| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (le_trans (Complex.abs_re_le_norm _) hzn)
            (le_trans (Complex.abs_re_le_norm _) hwn)
        _ = 2 := by norm_num
    have h1' : |(k : ℝ)| * (2 * Real.pi) ≤ 2 := by rwa [abs_mul, abs_of_pos hpi] at h1
    have hlt : |(k : ℝ)| < 1 := by nlinarith [Real.pi_gt_three, h1', hpi]
    have : (-1 : ℤ) < k := by exact_mod_cast (abs_lt.mp hlt).1
    have h2 : k < 1 := by exact_mod_cast (abs_lt.mp hlt).2
    omega
  have hl0 : l = 0 := by
    have hkim : (z : ℂ).im - (w : ℂ).im = l * (2 * Real.pi) := by linarith
    have h1 : |(l : ℝ) * (2 * Real.pi)| ≤ 2 := by
      rw [← hkim]
      calc |(z : ℂ).im - (w : ℂ).im| ≤ |(z : ℂ).im| + |(w : ℂ).im| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (le_trans (Complex.abs_im_le_norm _) hzn)
            (le_trans (Complex.abs_im_le_norm _) hwn)
        _ = 2 := by norm_num
    have h1' : |(l : ℝ)| * (2 * Real.pi) ≤ 2 := by rwa [abs_mul, abs_of_pos hpi] at h1
    have hlt : |(l : ℝ)| < 1 := by nlinarith [Real.pi_gt_three, h1', hpi]
    have : (-1 : ℤ) < l := by exact_mod_cast (abs_lt.mp hlt).1
    have h2 : l < 1 := by exact_mod_cast (abs_lt.mp hlt).2
    omega
  have hre : (z : ℂ).re = (w : ℂ).re := by rw [hk0] at hk; simpa using hk
  have him : (z : ℂ).im = (w : ℂ).im := by rw [hl0] at hl; simpa using hl
  exact Subtype.ext (Complex.ext hre him)

/-- **The interior of the disc is open in the surface.**  The interior is the image of the open
unit disc of the parameter plane, whose saturation under the period lattice is open (the
parametrisation is an open quotient map onto its image). -/
theorem discMap_open_interior (P : Work.CoreTopology.ParamTorus) :
    IsOpenInCarrier P (discMap P '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}) := by
  have hset : (⇑(Work.TorusCover.quotHomeo P)) ⁻¹'
      ((Subtype.val ⁻¹'
        (discMap P '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}) : Set P.carrier))
      = QuotientAddGroup.mk '' openUnitDisc := by
    ext q
    constructor
    · intro hq
      obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective q
      simp only [Set.mem_preimage] at hq
      have hcoe : Subtype.val (⇑(Work.TorusCover.quotHomeo P) (QuotientAddGroup.mk p)) =
          Work.TorusCover.psiMap P.psi p := rfl
      rw [hcoe] at hq
      obtain ⟨z, hzS, hze⟩ := hq
      refine ⟨((z : ℂ).re, (z : ℂ).im), ?_, ?_⟩
      · exact (mem_unitDisc_iff (z : ℂ)).mpr hzS
      · rw [mk_eq_iff]
        have h1 : Work.TorusCover.psiMap P.psi ((z : ℂ).re, (z : ℂ).im) = discMap P z := rfl
        exact (Work.TorusCover.psiMap_eq_iff_param P).mp (by rw [h1]; exact hze)
    · rintro ⟨r, hrD, hrq⟩
      rw [← hrq]
      simp only [Set.mem_preimage]
      have hcoe : Subtype.val (⇑(Work.TorusCover.quotHomeo P) (QuotientAddGroup.mk r)) =
          Work.TorusCover.psiMap P.psi r := rfl
      rw [hcoe]
      have hz0 : ‖(Complex.mk r.1 r.2 : ℂ)‖ < 1 := (mem_unitDisc_iff (Complex.mk r.1 r.2)).mp hrD
      refine ⟨⟨Complex.mk r.1 r.2, ?_⟩, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact le_of_lt hz0
      · exact hz0
      · rfl
  have hopen : IsOpen ((⇑(Work.TorusCover.quotHomeo P)) ⁻¹'
      ((Subtype.val ⁻¹'
        (discMap P '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}) : Set P.carrier))) := by
    rw [hset]
    exact (QuotientAddGroup.isOpenQuotientMap_mk
      (N := Work.TorusCover.lattice)).isOpenMap openUnitDisc isOpen_unitDisc
  exact ((Work.TorusCover.quotHomeo P).isOpen_preimage
    (s := (Subtype.val ⁻¹'
      (discMap P '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}) : Set P.carrier))).mp hopen

/-- **The standard embedded disc of a parametrised torus**, given by the parametrisation of the
closed unit disc of the parameter plane. -/
def disc (P : Work.CoreTopology.ParamTorus) : Work.SurgeryInvariance.DiscRegion P where
  e := discMap P
  inj := discMap_injective P
  mem := discMap_mem P
  open_interior := discMap_open_interior P

/-- **Every parametrised torus carries an embedded disc.** -/
theorem nonempty (P : Work.CoreTopology.ParamTorus) :
    Nonempty (Work.SurgeryInvariance.DiscRegion P) :=
  ⟨disc P⟩

end

end Work.SurgeryInvariance.DiscRegion
