import Mathlib
import Submission.Work.Smooth.SphereJordan.localArcCore
import Submission.Work.Smooth.SphereJordan.localSliceArc
import Submission.Work.Smooth.SphereJordan.outFrontierPath

/-!
# The frontier near a point with a free direction (the generic case)

Let `S = ⋃ w ∈ Q, closedBall w r`, `x ∈ frontier S`, and suppose there is a unit direction
`ustar` with `Re (star ustar * (w - x)) < 0` for every *active* centre `w` (one with
`dist x w = r`).  Rotating by `ustar`, the local picture at `x` becomes:

* the profile `mRot ustar θ = max_w ⟪eicC θ, star ustar * (w - x)⟫` equals
  `max_w r * cos (Phi w - θ)` where `Phi w = argBranch (star ustar * (w - x)) ∈ (π/2, 3π/2)`;
* the frontier near `x` is the graph `θ ↦ x + 2 * mRot ustar θ * (ustar * eicC θ)`;
* at a given level, the graph hits `x` exactly at the two angular parameters `Φmin - β` and
  `Φmax + β`, so each side is a branch of an arc.
-/

namespace Work.Smooth.SphereJordan

open Set Metric

noncomputable section

open scoped Classical

variable {Q : Finset ℂ} {r : ℝ} {x : ℂ}

/-- The rotated radial profile at the unit direction `ustar * eicC θ`. -/
def mRot (Q : Finset ℂ) (r : ℝ) (x : ℂ) (hA : (actC Q r x).Nonempty) (ustar : ℂ) (θ : ℝ) : ℝ :=
  (actC Q r x).sup' hA (fun w => (star (eicC θ) * (star ustar * (w - x))).re)

/-- The rotated angular coordinate of a centre. -/
def PhiC (ustar w x : ℂ) : ℝ := argBranch (star ustar * (w - x))

theorem mC_mul_eicC (hA : (actC Q r x).Nonempty) (ustar : ℂ) (θ : ℝ) :
    mC Q r x hA (ustar * eicC θ) = mRot Q r x hA ustar θ := by
  rw [mC, mRot]
  exact Finset.sup'_congr hA rfl (fun w _ => by rw [star_mul, mul_assoc])

theorem mRot_cos {hA : (actC Q r x).Nonempty} {ustar : ℂ} (hu : ‖ustar‖ = 1) (θ : ℝ) :
    mRot Q r x hA ustar θ
      = (actC Q r x).sup' hA (fun w => r * Real.cos (PhiC ustar w x - θ)) := by
  rw [mRot]
  refine Finset.sup'_congr hA rfl (fun w hw => ?_)
  have hwx : dist x w = r := (mem_actC.mp hw).2
  have hnorm : ‖star ustar * (w - x)‖ = r := by
    rw [norm_mul, norm_star, hu, one_mul, ← dist_eq_norm, dist_comm]; exact hwx
  simp only [eicC]
  rw [re_star_exp_I_mul, hnorm, ← cos_argBranch_sub]
  rfl

theorem PhiC_lt {ustar w x : ℂ} (h : (star ustar * (w - x)).re < 0) :
    PhiC ustar w x < 3 * Real.pi / 2 := (argBranch_mem h).2

theorem PhiC_gt {ustar w x : ℂ} (h : (star ustar * (w - x)).re < 0) :
    Real.pi / 2 < PhiC ustar w x := (argBranch_mem h).1

/-- For `z ≤ -β` (and `z > -3π/2`) the cosine is at most `cos β`. -/
theorem cos_le_cos_of_le_neg {β z : ℝ} (hβ0 : 0 < β) (hβπ : β < Real.pi / 2)
    (hzlo : -3 * Real.pi / 2 < z) (hzhi : z ≤ -β) : Real.cos z ≤ Real.cos β := by
  have hpos : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  by_cases hz : -Real.pi ≤ z
  · rw [← Real.cos_abs z]
    have habs : |z| = -z := abs_of_neg (by linarith)
    have hzmem : |z| ∈ Set.Icc (0 : ℝ) Real.pi := ⟨abs_nonneg z, by rw [habs]; linarith⟩
    have hbmem : β ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hβ0.le, by linarith [Real.pi_pos]⟩
    exact Real.antitoneOn_cos hbmem hzmem (by rw [habs]; linarith)
  · rw [not_le] at hz
    have hneg : Real.cos z < 0 := by
      have h := Real.cos_neg_of_pi_div_two_lt_of_lt (x := -z) (by linarith)
        (by linarith [hzlo])
      rwa [Real.cos_neg] at h
    linarith

/-- For `z ≥ β` (and `z < 3π/2`) the cosine is at most `cos β`. -/
theorem cos_le_cos_of_ge {β z : ℝ} (hβ0 : 0 < β) (hβπ : β < Real.pi / 2)
    (hzlo : β ≤ z) (hzhi : z < 3 * Real.pi / 2) : Real.cos z ≤ Real.cos β := by
  by_cases hz : z ≤ Real.pi
  · have hbmem : β ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hβ0.le, by linarith [Real.pi_pos]⟩
    have hzmem : z ∈ Set.Icc (0 : ℝ) Real.pi := ⟨by linarith, hz⟩
    exact Real.antitoneOn_cos hbmem hzmem hzlo
  · rw [not_le] at hz
    have hneg : Real.cos z < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith)
      (by linarith [hzhi])
    have hpos : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    linarith

/-- If `cos z ≤ cos β` and `-β < z`, then `β ≤ z`. -/
theorem le_of_cos_le_cos {β z : ℝ} (hβ0 : 0 < β) (hβπ : β < Real.pi / 2)
    (hz : -β < z) (h : Real.cos z ≤ Real.cos β) : β ≤ z := by
  by_contra hlt
  rw [not_le] at hlt
  have hlt' : |z| < β := by rw [abs_lt]; exact ⟨hz, hlt⟩
  have hzmem : |z| ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨abs_nonneg z, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hbmem : β ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hβ0.le, by linarith [Real.pi_pos]⟩
  have hstrict : Real.cos β < Real.cos |z| := Real.strictAntiOn_cos hzmem hbmem hlt'
  rw [Real.cos_abs] at hstrict
  linarith

/-- If `cos z ≤ cos β` and `z < β`, then `z ≤ -β`. -/
theorem le_neg_of_cos_le_cos {β z : ℝ} (hβ0 : 0 < β) (hβπ : β < Real.pi / 2)
    (hz : z < β) (h : Real.cos z ≤ Real.cos β) : z ≤ -β := by
  by_contra hlt
  rw [not_le] at hlt
  have hlt' : |z| < β := by rw [abs_lt]; exact ⟨hlt, hz⟩
  have hzmem : |z| ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨abs_nonneg z, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hbmem : β ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hβ0.le, by linarith [Real.pi_pos]⟩
  have hstrict : Real.cos β < Real.cos |z| := Real.strictAntiOn_cos hzmem hbmem hlt'
  rw [Real.cos_abs] at hstrict
  linarith

theorem cos_add_int_mul_two_pi (θ : ℝ) (k : ℤ) :
    Real.cos (θ + (k : ℝ) * (2 * Real.pi)) = Real.cos θ :=
  Real.cos_periodic.int_mul k θ

theorem eicC_add_int_mul_two_pi (θ : ℝ) (k : ℤ) :
    eicC (θ + (k : ℝ) * (2 * Real.pi)) = eicC θ := by
  rw [eicC_add]
  have hone : eicC ((k : ℝ) * (2 * Real.pi)) = 1 := by
    rw [eicC]
    have h : (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I
        = (k : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  rw [hone, mul_one]

theorem cos_sub_int_mul_two_pi (θ : ℝ) (k : ℤ) :
    Real.cos (θ - (k : ℝ) * (2 * Real.pi)) = Real.cos θ := by
  rw [show θ - (k : ℝ) * (2 * Real.pi) = θ + ((-k : ℤ) : ℝ) * (2 * Real.pi) by push_cast; ring]
  exact cos_add_int_mul_two_pi θ (-k)

theorem eicC_sub_int_mul_two_pi (θ : ℝ) (k : ℤ) :
    eicC (θ - (k : ℝ) * (2 * Real.pi)) = eicC θ := by
  rw [show θ - (k : ℝ) * (2 * Real.pi) = θ + ((-k : ℤ) : ℝ) * (2 * Real.pi) by push_cast; ring]
  exact eicC_add_int_mul_two_pi θ (-k)

/-- **The `Φmax` direction is at the level `cos β`.** -/
theorem sup_cos_max_aux {hA : (actC Q r x).Nonempty} {ustar : ℂ} {β Φmax Φmin : ℝ}
    (hmax : ∀ w ∈ actC Q r x, PhiC ustar w x ≤ Φmax)
    (hmin : ∀ w ∈ actC Q r x, Φmin ≤ PhiC ustar w x)
    (hatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmax)
    (hβ0 : 0 < β) (hβπ : β < Real.pi / 2) (hspread : Φmax - Φmin < 2 * β)
    (hlo : Real.pi / 2 < Φmin) (hhi : Φmax < 3 * Real.pi / 2) :
    (actC Q r x).sup' hA (fun w => Real.cos (PhiC ustar w x - (Φmax + β))) = Real.cos β := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le hA (fun w => Real.cos (PhiC ustar w x - (Φmax + β))) (fun w hw => ?_)
    have h1 : PhiC ustar w x ≤ Φmax := hmax w hw
    have h2 : Φmin ≤ PhiC ustar w x := hmin w hw
    have hz : PhiC ustar w x - (Φmax + β) ≤ -β := by linarith
    have hzlo : -3 * Real.pi / 2 < PhiC ustar w x - (Φmax + β) := by linarith
    exact cos_le_cos_of_le_neg hβ0 hβπ hzlo hz
  · obtain ⟨w₀, hw₀, hw₀eq⟩ := hatt
    have hterm : Real.cos (PhiC ustar w₀ x - (Φmax + β)) = Real.cos β := by
      rw [hw₀eq]; ring_nf; rw [Real.cos_neg]
    rw [← hterm]
    exact Finset.le_sup' (fun w => Real.cos (PhiC ustar w x - (Φmax + β))) hw₀

/-- **The `Φmin` direction is at the level `cos β`.** -/
theorem sup_cos_min_aux {hA : (actC Q r x).Nonempty} {ustar : ℂ} {β Φmax Φmin : ℝ}
    (hmax : ∀ w ∈ actC Q r x, PhiC ustar w x ≤ Φmax)
    (hmin : ∀ w ∈ actC Q r x, Φmin ≤ PhiC ustar w x)
    (hatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmin)
    (hβ0 : 0 < β) (hβπ : β < Real.pi / 2) (hspread : Φmax - Φmin < 2 * β)
    (hlo : Real.pi / 2 < Φmin) (hhi : Φmax < 3 * Real.pi / 2) :
    (actC Q r x).sup' hA (fun w => Real.cos (PhiC ustar w x - (Φmin - β))) = Real.cos β := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le hA (fun w => Real.cos (PhiC ustar w x - (Φmin - β))) (fun w hw => ?_)
    have h2 : Φmin ≤ PhiC ustar w x := hmin w hw
    have h3 : PhiC ustar w x ≤ Φmax := hmax w hw
    have hz : β ≤ PhiC ustar w x - (Φmin - β) := by linarith
    have hzhi : PhiC ustar w x - (Φmin - β) < 3 * Real.pi / 2 := by linarith
    exact cos_le_cos_of_ge hβ0 hβπ hz hzhi
  · obtain ⟨w₀, hw₀, hw₀eq⟩ := hatt
    have hterm : Real.cos (PhiC ustar w₀ x - (Φmin - β)) = Real.cos β := by
      rw [hw₀eq]; ring_nf
    rw [← hterm]
    exact Finset.le_sup' (fun w => Real.cos (PhiC ustar w x - (Φmin - β))) hw₀

/-- **The level set of the profile, in "pointwise" form.**  If `cos (Phi w - θ) ≤ cos β` for all
active `w` and the value `cos β` is attained, then `θ` is one of the two critical angles
`Φmax + β`, `Φmin - β` (modulo `2π`). -/
theorem level_set_aux {hA : (actC Q r x).Nonempty} {ustar : ℂ} {β Φmax Φmin θ : ℝ}
    (hmax : ∀ w ∈ actC Q r x, PhiC ustar w x ≤ Φmax)
    (hmin : ∀ w ∈ actC Q r x, Φmin ≤ PhiC ustar w x)
    (hmaxatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmax)
    (hminatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmin)
    (hβ0 : 0 < β) (hβπ : β < Real.pi / 2) (hspread : Φmax - Φmin < 2 * β)
    (hall : ∀ w ∈ actC Q r x, Real.cos (PhiC ustar w x - θ) ≤ Real.cos β)
    (hatt : ∃ w ∈ actC Q r x, Real.cos (PhiC ustar w x - θ) = Real.cos β) :
    eicC θ = eicC (Φmax + β) ∨ eicC θ = eicC (Φmin - β) := by
  obtain ⟨w₀, hw₀, hw₀eq⟩ := hatt
  have hwmax : PhiC ustar w₀ x ≤ Φmax := hmax w₀ hw₀
  have hwmin : Φmin ≤ PhiC ustar w₀ x := hmin w₀ hw₀
  rcases (Real.cos_eq_cos_iff.mp hw₀eq) with ⟨k, hk | hk⟩
  · -- `β = 2kπ + (Phi w₀ - θ)`, so `θ = Phi w₀ - β + 2kπ` and `Phi w₀ = Φmin`
    right
    have htheta : θ = PhiC ustar w₀ x - β + (k : ℝ) * (2 * Real.pi) := by linarith
    have hval : PhiC ustar w₀ x = Φmin := by
      have hkey : ∀ w ∈ actC Q r x, PhiC ustar w₀ x ≤ PhiC ustar w x := by
        intro w hw
        have hcw : Real.cos (PhiC ustar w x - θ) ≤ Real.cos β := hall w hw
        have hper : PhiC ustar w x - θ
            = (PhiC ustar w x - PhiC ustar w₀ x + β) - (k : ℝ) * (2 * Real.pi) := by
          rw [htheta]; ring_nf
        rw [hper, cos_sub_int_mul_two_pi] at hcw
        have hz : -β < PhiC ustar w x - PhiC ustar w₀ x + β := by
          have h1 : Φmin ≤ PhiC ustar w x := hmin w hw
          linarith
        have := le_of_cos_le_cos hβ0 hβπ hz hcw
        linarith
      obtain ⟨w₁, hw₁, hw₁eq⟩ := hminatt
      have h1 : PhiC ustar w₀ x ≤ PhiC ustar w₁ x := hkey w₁ hw₁
      rw [hw₁eq] at h1
      exact le_antisymm h1 hwmin
    have hthis : eicC θ = eicC (Φmin - β) := by
      rw [htheta, eicC_add_int_mul_two_pi, hval]
    exact hthis
  · -- `β = 2kπ - (Phi w₀ - θ)`, so `θ = Phi w₀ + β - 2kπ` and `Phi w₀ = Φmax`
    left
    have htheta : θ = PhiC ustar w₀ x + β - (k : ℝ) * (2 * Real.pi) := by linarith
    have hval : PhiC ustar w₀ x = Φmax := by
      have hkey : ∀ w ∈ actC Q r x, PhiC ustar w x ≤ PhiC ustar w₀ x := by
        intro w hw
        have hcw : Real.cos (PhiC ustar w x - θ) ≤ Real.cos β := hall w hw
        have hper : PhiC ustar w x - θ
            = (PhiC ustar w x - PhiC ustar w₀ x - β) + (k : ℝ) * (2 * Real.pi) := by
          rw [htheta]; ring_nf
        rw [hper, cos_add_int_mul_two_pi] at hcw
        have hz : PhiC ustar w x - PhiC ustar w₀ x - β < β := by
          have h1 : PhiC ustar w x ≤ Φmax := hmax w hw
          linarith
        have := le_neg_of_cos_le_cos hβ0 hβπ hz hcw
        linarith
      obtain ⟨w₁, hw₁, hw₁eq⟩ := hmaxatt
      have h1 : PhiC ustar w₁ x ≤ PhiC ustar w₀ x := hkey w₁ hw₁
      rw [hw₁eq] at h1
      exact le_antisymm hwmax h1
    have hthis : eicC θ = eicC (Φmax + β) := by
      rw [htheta, eicC_sub_int_mul_two_pi, hval]
    exact hthis

/-- **The level set of the profile** (supremum form). -/
theorem eicC_eq_of_sup_cos_eq {hA : (actC Q r x).Nonempty} {ustar : ℂ} {β Φmax Φmin θ : ℝ}
    (hmax : ∀ w ∈ actC Q r x, PhiC ustar w x ≤ Φmax)
    (hmin : ∀ w ∈ actC Q r x, Φmin ≤ PhiC ustar w x)
    (hmaxatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmax)
    (hminatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmin)
    (hβ0 : 0 < β) (hβπ : β < Real.pi / 2) (hspread : Φmax - Φmin < 2 * β)
    (heq : (actC Q r x).sup' hA (fun w => Real.cos (PhiC ustar w x - θ)) = Real.cos β) :
    eicC θ = eicC (Φmax + β) ∨ eicC θ = eicC (Φmin - β) := by
  refine level_set_aux (hA := hA) hmax hmin hmaxatt hminatt hβ0 hβπ hspread ?_ ?_
  · intro w hw
    rw [← heq]
    exact Finset.le_sup' (fun w => Real.cos (PhiC ustar w x - θ)) hw
  · obtain ⟨w₀, hw₀, hw₀eq⟩ :=
      Finset.exists_mem_eq_sup' hA (fun w => Real.cos (PhiC ustar w x - θ))
    exact ⟨w₀, hw₀, by rw [← hw₀eq]; exact heq⟩

/-- `sup'` of a nonnegative scalar multiple. -/
theorem sup'_const_mul {ι : Type*} {s : Finset ι} (h : s.Nonempty) (f : ι → ℝ) {a : ℝ}
    (ha : 0 ≤ a) : s.sup' h (fun i => a * f i) = a * s.sup' h f := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le h (fun i => a * f i) (fun i hi => ?_)
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' f hi) ha
  · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' h f
    rw [heq]
    exact Finset.le_sup' (fun i => a * f i) hi

/-- The angle whose cosine is `ρ / (2r)`. -/
noncomputable def betaC (r ρ : ℝ) : ℝ := Real.arccos (ρ / (2 * r))

theorem betaC_pos {r ρ : ℝ} (hr : 0 < r) (hρ0 : 0 < ρ) (hρ : ρ < 2 * r) :
    0 < betaC r ρ := by
  rw [betaC, Real.arccos_pos]
  rw [div_lt_one (by linarith)]; linarith

theorem betaC_lt_pi_div_two {r ρ : ℝ} (hr : 0 < r) (hρ0 : 0 < ρ) :
    betaC r ρ < Real.pi / 2 := by
  rw [betaC, Real.arccos_lt_pi_div_two]
  positivity

theorem cos_betaC {r ρ : ℝ} (hr : 0 < r) (hρ0 : 0 < ρ) (hρ : ρ < 2 * r) :
    Real.cos (betaC r ρ) = ρ / (2 * r) := by
  have h1 : -1 ≤ ρ / (2 * r) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have h2 : ρ / (2 * r) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  rw [betaC]
  exact Real.cos_arccos h1 h2

theorem mul_cos_betaC {r ρ : ℝ} (hr : 0 < r) (hρ0 : 0 < ρ) (hρ : ρ < 2 * r) :
    r * Real.cos (betaC r ρ) = ρ / 2 := by
  rw [cos_betaC hr hρ0 hρ]
  field_simp

theorem betaC_gt_of_cos {r ρ β : ℝ} (hr : 0 < r) (hρ0 : 0 < ρ) (hρ : ρ < 2 * r)
    (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi) (h : ρ < 2 * r * Real.cos β) :
    β < betaC r ρ := by
  have h1 : ρ / (2 * r) < Real.cos β := by
    rw [div_lt_iff₀ (by linarith)]; linarith
  have h4 : Real.arccos (Real.cos β) < Real.arccos (ρ / (2 * r)) :=
    Real.arccos_lt_arccos (x := ρ / (2 * r)) (y := Real.cos β)
      (by rw [le_div_iff₀ (by linarith)]; linarith) h1 (Real.cos_le_one β)
  rw [Real.arccos_cos hβ0 hβπ] at h4
  rw [betaC]
  exact h4

theorem sup_rcos_max_aux {hA : (actC Q r x).Nonempty} {ustar : ℂ} {β Φmax Φmin : ℝ}
    (hr : 0 ≤ r)
    (hmax : ∀ w ∈ actC Q r x, PhiC ustar w x ≤ Φmax)
    (hmin : ∀ w ∈ actC Q r x, Φmin ≤ PhiC ustar w x)
    (hmaxatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmax)
    (hminatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmin)
    (hβ0 : 0 < β) (hβπ : β < Real.pi / 2) (hspread : Φmax - Φmin < 2 * β)
    (hlo : Real.pi / 2 < Φmin) (hhi : Φmax < 3 * Real.pi / 2) :
    (actC Q r x).sup' hA (fun w => r * Real.cos (PhiC ustar w x - (Φmax + β)))
      = r * Real.cos β := by
  rw [sup'_const_mul hA _ hr, sup_cos_max_aux hmax hmin hmaxatt hβ0 hβπ hspread hlo hhi]

theorem sup_rcos_min_aux {hA : (actC Q r x).Nonempty} {ustar : ℂ} {β Φmax Φmin : ℝ}
    (hr : 0 ≤ r)
    (hmax : ∀ w ∈ actC Q r x, PhiC ustar w x ≤ Φmax)
    (hmin : ∀ w ∈ actC Q r x, Φmin ≤ PhiC ustar w x)
    (hmaxatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmax)
    (hminatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmin)
    (hβ0 : 0 < β) (hβπ : β < Real.pi / 2) (hspread : Φmax - Φmin < 2 * β)
    (hlo : Real.pi / 2 < Φmin) (hhi : Φmax < 3 * Real.pi / 2) :
    (actC Q r x).sup' hA (fun w => r * Real.cos (PhiC ustar w x - (Φmin - β)))
      = r * Real.cos β := by
  rw [sup'_const_mul hA _ hr, sup_cos_min_aux hmax hmin hminatt hβ0 hβπ hspread hlo hhi]

/-- **The maximum branch of the graph is on the frontier.** -/
theorem mC_dir_max {hA : (actC Q r x).Nonempty} {ustar : ℂ} {Φmax Φmin β : ℝ}
    (hr : 0 ≤ r) (hustar : ‖ustar‖ = 1) (hmax : ∀ w ∈ actC Q r x, PhiC ustar w x ≤ Φmax)
    (hmin : ∀ w ∈ actC Q r x, Φmin ≤ PhiC ustar w x)
    (hmaxatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmax)
    (hminatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmin)
    (hlo : Real.pi / 2 < Φmin) (hhi : Φmax < 3 * Real.pi / 2)
    (hβ0 : 0 < β) (hβπ : β < Real.pi / 2) (hspread : Φmax - Φmin < 2 * β) :
    mC Q r x hA (ustar * eicC (Φmax + β)) = r * Real.cos β := by
  rw [mC_mul_eicC, mRot_cos hustar,
    sup_rcos_max_aux hr hmax hmin hmaxatt hminatt hβ0 hβπ hspread hlo hhi]

/-- **The minimum branch of the graph is on the frontier.** -/
theorem mC_dir_min {hA : (actC Q r x).Nonempty} {ustar : ℂ} {Φmax Φmin β : ℝ}
    (hr : 0 ≤ r) (hustar : ‖ustar‖ = 1) (hmax : ∀ w ∈ actC Q r x, PhiC ustar w x ≤ Φmax)
    (hmin : ∀ w ∈ actC Q r x, Φmin ≤ PhiC ustar w x)
    (hmaxatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmax)
    (hminatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmin)
    (hlo : Real.pi / 2 < Φmin) (hhi : Φmax < 3 * Real.pi / 2)
    (hβ0 : 0 < β) (hβπ : β < Real.pi / 2) (hspread : Φmax - Φmin < 2 * β) :
    mC Q r x hA (ustar * eicC (Φmin - β)) = r * Real.cos β := by
  rw [mC_mul_eicC, mRot_cos hustar,
    sup_rcos_min_aux hr hmax hmin hmaxatt hminatt hβ0 hβπ hspread hlo hhi]

/-- **The frontier is the graph of the profile.**  Every point of the frontier of `S` whose distance
from `x` is less than `ε` and whose angular parameter is in the "free" range is either on the
`Φmax`-branch or on the `Φmin`-branch. -/
theorem frontier_eq_graph {hA : (actC Q r x).Nonempty} {ustar : ℂ} {Φmax Φmin : ℝ}
    (hr : 0 < r) (hustar : ‖ustar‖ = 1) (hmax : ∀ w ∈ actC Q r x, PhiC ustar w x ≤ Φmax)
    (hmin : ∀ w ∈ actC Q r x, Φmin ≤ PhiC ustar w x)
    (hmaxatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmax)
    (hminatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmin)
    (hlo : Real.pi / 2 < Φmin) (hhi : Φmax < 3 * Real.pi / 2)
    {εm : ℝ} (hmodel : ∀ (u : ℂ) (ρ : ℝ), ‖u‖ = 1 → 0 < ρ → ρ < εm →
      (x + ρ * u ∈ ⋃ w ∈ Q, Metric.closedBall w r ↔ ρ ≤ 2 * mC Q r x hA u))
    {ε : ℝ} (hε : 0 < ε) (hεε : ε ≤ εm)
    (hεc : ε ≤ 2 * r * Real.cos ((Φmax - Φmin) / 2))
    {y : ℂ} (hy : y ∈ frontier (⋃ w ∈ Q, Metric.closedBall w r)) (hyx : y ≠ x)
    (hyd : dist y x < ε) :
    ∃ ρ ∈ Set.Ioo (0 : ℝ) ε,
      (y = x + (ρ : ℂ) * (ustar * eicC (Φmax + betaC r ρ))
        ∨ y = x + (ρ : ℂ) * (ustar * eicC (Φmin - betaC r ρ))) := by
  have hρ0 : 0 < dist y x := dist_pos.mpr hyx
  have hρlt : dist y x < ε := hyd
  have hρltm : dist y x < εm := lt_of_lt_of_le hρlt hεε
  have hcos1 : Real.cos ((Φmax - Φmin) / 2) ≤ 1 := Real.cos_le_one _
  have h2c : 2 * r * Real.cos ((Φmax - Φmin) / 2) ≤ 2 * r := by nlinarith [hcos1, hr]
  have hρ2r : dist y x < 2 * r := lt_of_lt_of_le hρlt (le_trans hεc h2c)
  set ρ : ℝ := dist y x with hρdef
  set u : ℂ := (y - x) / ((ρ : ℝ) : ℂ) with hudef
  have hρne : ((ρ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hρ0
  have hnormu : ‖u‖ = 1 := by
    rw [hudef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0, hρdef,
      dist_eq_norm]
    exact div_self (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hyx))
  have hyu : x + (ρ : ℂ) * u = y := by
    have hρc : ((ρ : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hρ0
    have h1 : (ρ : ℂ) * ((y - x) / (ρ : ℂ)) = y - x := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hρc]
    rw [hudef, h1]
    ring
  have heq : ρ = 2 * mC Q r x hA u :=
    (frontier_iff_eq_mC hmodel hnormu hρ0 hρltm).mp (by rw [hyu]; exact hy)
  have hu1 : ustar * star ustar = 1 := by
    have h1 := RCLike.mul_conj ustar
    rw [hustar] at h1
    norm_num at h1
    exact h1
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, ustar * eicC θ = u := by
    refine ⟨Complex.arg (star ustar * u), ?_⟩
    have h1 : ‖star ustar * u‖ = 1 := by rw [norm_mul, norm_star, hustar, one_mul, hnormu]
    have h2 := Complex.norm_mul_exp_arg_mul_I (star ustar * u)
    rw [h1] at h2
    simp only [Complex.ofReal_one, one_mul] at h2
    have h3 : eicC (Complex.arg (star ustar * u)) = star ustar * u := by
      rw [eicC]; exact h2
    rw [h3, ← mul_assoc, hu1, one_mul]
  have hβ0 : 0 < betaC r ρ := betaC_pos hr hρ0 hρ2r
  have hβπ : betaC r ρ < Real.pi / 2 := betaC_lt_pi_div_two hr hρ0
  have hΦ : Φmin ≤ Φmax := by
    obtain ⟨w, hw⟩ := hA
    exact le_trans (hmin w hw) (hmax w hw)
  have hspread : Φmax - Φmin < 2 * betaC r ρ := by
    have hβhalf : 0 ≤ (Φmax - Φmin) / 2 := by linarith
    have hβhalfπ : (Φmax - Φmin) / 2 ≤ Real.pi := by linarith [Real.pi_pos]
    have hlt : ρ < 2 * r * Real.cos ((Φmax - Φmin) / 2) := lt_of_lt_of_le hρlt hεc
    have h2 := betaC_gt_of_cos hr hρ0 hρ2r hβhalf hβhalfπ hlt
    linarith
  have hsup : (actC Q r x).sup' hA (fun w => Real.cos (PhiC ustar w x - θ))
      = Real.cos (betaC r ρ) := by
    have h1 : mC Q r x hA (ustar * eicC θ) = r * (actC Q r x).sup' hA
        (fun w => Real.cos (PhiC ustar w x - θ)) := by
      rw [mC_mul_eicC, mRot_cos hustar, sup'_const_mul hA _ hr.le]
    have h2 : r * (actC Q r x).sup' hA (fun w => Real.cos (PhiC ustar w x - θ)) = ρ / 2 := by
      rw [← h1, hθ]
      linarith
    have h3 : r * Real.cos (betaC r ρ) = ρ / 2 := mul_cos_betaC hr hρ0 hρ2r
    have h4 : r * (actC Q r x).sup' hA (fun w => Real.cos (PhiC ustar w x - θ))
        = r * Real.cos (betaC r ρ) := by rw [h2, h3]
    exact mul_left_cancel₀ (ne_of_gt hr) h4
  have hcase := eicC_eq_of_sup_cos_eq (hA := hA) hmax hmin hmaxatt hminatt hβ0 hβπ hspread hsup
  refine ⟨ρ, ⟨hρ0, hρlt⟩, ?_⟩
  rcases hcase with hcase | hcase
  · left
    have hu : u = ustar * eicC (Φmax + betaC r ρ) := by rw [← hθ, hcase]
    rw [hyu.symm, hu]
  · right
    have hu : u = ustar * eicC (Φmin - betaC r ρ) := by rw [← hθ, hcase]
    rw [hyu.symm, hu]

/-- `betaC` is antitone in the radius. -/
theorem betaC_anti {r ρ ρ' : ℝ} (hr : 0 < r) (hρ0 : 0 < ρ) (hρ' : ρ' ≤ 2 * r) (h : ρ ≤ ρ') :
    betaC r ρ' ≤ betaC r ρ := by
  have h1 : ρ / (2 * r) ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by rw [le_div_iff₀ (by linarith)]; linarith, by rw [div_le_one (by linarith)]; linarith⟩
  have h2 : ρ' / (2 * r) ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by rw [le_div_iff₀ (by linarith)]; linarith, by rw [div_le_one (by linarith)]; linarith⟩
  have h3 : ρ / (2 * r) ≤ ρ' / (2 * r) := by
    exact div_le_div_of_nonneg_right h (by linarith : (0:ℝ) ≤ 2 * r)
  rw [betaC, betaC]
  exact Real.strictAntiOn_arccos.antitoneOn h1 h2 h3

/-- `eicC a = eicC b` for `a - b ∈ (0, 2π)` is impossible. -/
theorem eicC_ne_of_sub_mem {a b : ℝ} (h0 : 0 < a - b) (h2π : a - b < 2 * Real.pi) :
    eicC a ≠ eicC b := by
  intro hEq
  have hEq' : Complex.exp (((a : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((b : ℝ) : ℂ) * Complex.I) := by
    simpa only [eicC] using hEq
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hEq'
  have hn' : ((a : ℝ) : ℂ) * Complex.I
      = ((b : ℝ) : ℂ) * Complex.I + (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    rw [hn]; push_cast; ring
  have him : a = b + (n : ℝ) * (2 * Real.pi) := by
    have h := congrArg Complex.im hn'
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_mul, add_zero, sub_zero] at h
    exact h
  rcases lt_or_ge n 0 with hn' | hn'
  · have hn0 : n ≠ 0 := by omega
    have hle : (n : ℝ) ≤ -1 := by
      have : n ≤ -1 := by omega
      exact_mod_cast this
    nlinarith [him, h0, Real.pi_pos]
  · have hn0 : n ≠ 0 := by
      rintro rfl
      simp at him
      linarith
    have hge : (1 : ℝ) ≤ (n : ℝ) := by
      have h1 : 1 ≤ n := by omega
      exact_mod_cast h1
    nlinarith [him, h2π, Real.pi_pos]

/-- **The generic (free-direction) case of the local-arc property.**  If at `x` there is a unit
direction `ustar` with `Re (star ustar * (w - x)) < 0` for every active centre, and the local
complement of `S` at `x` (up to some radius) lies in the component of `q`, then the frontier of that
component is locally an arc at `x`. -/
theorem frontierLocallyArc_of_freeDirection {Q : Finset ℂ} {r : ℝ} (hr : 0 < r) {q x : ℂ}
    (hxq : x ∈ frontier (connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q))
    (hgen : ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ w ∈ Q, dist x w = r → (star u * (w - x)).re < 0)
    (hU : ∃ ε' > 0, ∀ y ∈ (⋃ w ∈ Q, Metric.closedBall w r)ᶜ, y ∈ Metric.ball x ε' →
      y ∈ connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q) :
    ∃ (ε : ℝ) (γ : ℝ → ℂ), 0 < ε ∧ Continuous γ ∧ Function.Injective γ ∧ γ 0 = x ∧
      γ '' Set.Ioo (-1) 1 =
        frontier (connectedComponentIn ((⋃ w ∈ Q, Metric.closedBall w r)ᶜ) q) ∩ Metric.ball x ε := by
  classical
  set S : Set ℂ := ⋃ w ∈ Q, Metric.closedBall w r with hSdef
  have hSclosed : IsClosed S := isClosed_ballUAux Q r
  have hx : x ∈ frontier S := frontier_componentIn_subset hSclosed hxq
  have hA : (actC Q r x).Nonempty := actC_nonempty hr hx
  obtain ⟨ustar, hustar, hfreeraw⟩ := hgen
  have hfree : ∀ w ∈ actC Q r x, (star ustar * (w - x)).re < 0 := fun w hw =>
    hfreeraw w (mem_actC.mp hw).1 (mem_actC.mp hw).2
  set Φmax : ℝ := (actC Q r x).sup' hA (fun w => PhiC ustar w x) with hΦmaxdef
  set Φmin : ℝ := (actC Q r x).inf' hA (fun w => PhiC ustar w x) with hΦmindef
  have hmax : ∀ w ∈ actC Q r x, PhiC ustar w x ≤ Φmax := fun w hw => by
    rw [hΦmaxdef]; exact Finset.le_sup' (fun w => PhiC ustar w x) hw
  have hmin : ∀ w ∈ actC Q r x, Φmin ≤ PhiC ustar w x := fun w hw => by
    rw [hΦmindef]; exact Finset.inf'_le (fun w => PhiC ustar w x) hw
  have hmaxatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmax := by
    obtain ⟨w, hw, heq⟩ := Finset.exists_mem_eq_sup' (s := actC Q r x) hA
      (fun w => PhiC ustar w x)
    exact ⟨w, hw, by rw [hΦmaxdef]; exact heq.symm⟩
  have hminatt : ∃ w ∈ actC Q r x, PhiC ustar w x = Φmin := by
    obtain ⟨w, hw, heq⟩ := Finset.exists_mem_eq_inf' (s := actC Q r x) hA
      (fun w => PhiC ustar w x)
    exact ⟨w, hw, by rw [hΦmindef]; exact heq.symm⟩
  have hlo : Real.pi / 2 < Φmin := by
    rw [hΦmindef]; exact (Finset.lt_inf'_iff hA).mpr (fun i hi => PhiC_gt (hfree i hi))
  have hhi : Φmax < 3 * Real.pi / 2 := by
    rw [hΦmaxdef]; exact (Finset.sup'_lt_iff hA).mpr (fun i hi => PhiC_lt (hfree i hi))
  have hΦle : Φmin ≤ Φmax := by
    obtain ⟨w, hw⟩ := hA
    exact le_trans (hmin w hw) (hmax w hw)
  obtain ⟨ε', hε'pos, hε'mem⟩ := hU
  obtain ⟨ε₁, hε₁pos, hmodel₁⟩ := exists_model_mC hr hx
  set c : ℝ := r * Real.cos ((Φmax - Φmin) / 2) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact mul_pos hr (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
  set ε : ℝ := min ε₁ (min ε' c) with hεdef
  have hεpos : 0 < ε := lt_min hε₁pos (lt_min hε'pos hcpos)
  have hεε₁ : ε ≤ ε₁ := min_le_left _ _
  have hεε' : ε ≤ ε' := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεc : ε ≤ c := le_trans (min_le_right _ _) (min_le_right _ _)
  have hε2c : ε < 2 * r * Real.cos ((Φmax - Φmin) / 2) := by
    have h2 : c < 2 * (r * Real.cos ((Φmax - Φmin) / 2)) := by rw [hcdef]; linarith
    calc ε ≤ c := hεc
      _ < 2 * (r * Real.cos ((Φmax - Φmin) / 2)) := h2
      _ = 2 * r * Real.cos ((Φmax - Φmin) / 2) := by ring
  have hε2r : ε < 2 * r := by
    have hcos1 : Real.cos ((Φmax - Φmin) / 2) ≤ 1 := Real.cos_le_one _
    have h2c : 2 * r * Real.cos ((Φmax - Φmin) / 2) ≤ 2 * r := by nlinarith [hcos1, hr]
    linarith
  have hmodel : ∀ (u : ℂ) (ρ : ℝ), ‖u‖ = 1 → 0 < ρ → ρ < ε →
      (x + ρ * u ∈ S ↔ ρ ≤ 2 * mC Q r x hA u) := fun u ρ hu hρ hρε =>
    hmodel₁ u ρ hu hρ (lt_of_lt_of_le hρε hεε₁)
  have hspreadρ : ∀ ρ ∈ Set.Ioo (0 : ℝ) ε, Φmax - Φmin < 2 * betaC r ρ := by
    intro ρ hρ
    have hρ2r : ρ < 2 * r := lt_trans hρ.2 hε2r
    have hβhalf : 0 ≤ (Φmax - Φmin) / 2 := by linarith
    have hβhalfπ : (Φmax - Φmin) / 2 ≤ Real.pi := by linarith [Real.pi_pos]
    have hlt : ρ < 2 * r * Real.cos ((Φmax - Φmin) / 2) := lt_of_lt_of_le hρ.2 hε2c.le
    have h2 := betaC_gt_of_cos hr hρ.1 hρ2r hβhalf hβhalfπ hlt
    linarith
  have hspreadε : Φmax - Φmin < 2 * betaC r ε := by
    have hβhalf : 0 ≤ (Φmax - Φmin) / 2 := by linarith
    have hβhalfπ : (Φmax - Φmin) / 2 ≤ Real.pi := by linarith [Real.pi_pos]
    have h2 := betaC_gt_of_cos hr hεpos hε2r hβhalf hβhalfπ hε2c
    linarith
  -- the profile at the two branches
  have hρeqPlus : ∀ ρ ∈ Set.Ioo (0 : ℝ) ε,
      ρ = 2 * mC Q r x hA (ustar * eicC (Φmax + betaC r ρ)) := by
    intro ρ hρ
    rw [mC_dir_max hr.le hustar hmax hmin hmaxatt hminatt hlo hhi
      (betaC_pos hr hρ.1 (lt_trans hρ.2 hε2r)) (betaC_lt_pi_div_two hr hρ.1) (hspreadρ ρ hρ),
      mul_cos_betaC hr hρ.1 (lt_trans hρ.2 hε2r)]
    ring
  have hρeqMinus : ∀ ρ ∈ Set.Ioo (0 : ℝ) ε,
      ρ = 2 * mC Q r x hA (ustar * eicC (Φmin - betaC r ρ)) := by
    intro ρ hρ
    rw [mC_dir_min hr.le hustar hmax hmin hmaxatt hminatt hlo hhi
      (betaC_pos hr hρ.1 (lt_trans hρ.2 hε2r)) (betaC_lt_pi_div_two hr hρ.1) (hspreadρ ρ hρ),
      mul_cos_betaC hr hρ.1 (lt_trans hρ.2 hε2r)]
    ring
  have hbranchPlus : ∀ ρ ∈ Set.Ioo (0 : ℝ) ε,
      x + (ρ : ℂ) * (ustar * eicC (Φmax + betaC r ρ)) ∈ frontier S := by
    intro ρ hρ
    refine (frontier_iff_eq_mC hmodel (by rw [norm_mul, norm_eicC, mul_one]; exact hustar)
      hρ.1 hρ.2).mpr (hρeqPlus ρ hρ)
  have hbranchMinus : ∀ ρ ∈ Set.Ioo (0 : ℝ) ε,
      x + (ρ : ℂ) * (ustar * eicC (Φmin - betaC r ρ)) ∈ frontier S := by
    intro ρ hρ
    refine (frontier_iff_eq_mC hmodel (by rw [norm_mul, norm_eicC, mul_one]; exact hustar)
      hρ.1 hρ.2).mpr (hρeqMinus ρ hρ)
  -- the local equality of the frontiers
  have hfrontier_eq : frontier (connectedComponentIn (Sᶜ) q) ∩ Metric.ball x ε
      = frontier S ∩ Metric.ball x ε := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro y ⟨hy, hyb⟩
      exact ⟨frontier_componentIn_subset hSclosed hy, hyb⟩
    · rintro y ⟨hyS, hyb⟩
      refine ⟨⟨?_, ?_⟩, hyb⟩
      · refine Metric.mem_closure_iff.mpr ?_
        intro δ hδ
        obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball y hyb
        set δ₂ : ℝ := min δ δ₁ / 2 with hδ₂def
        have hδ₂pos : 0 < δ₂ := by
          rw [hδ₂def]; exact div_pos (lt_min hδ (by linarith)) (by norm_num)
        have hδ₂δ : δ₂ < δ := by rw [hδ₂def]; linarith [min_le_left δ δ₁]
        have hδ₂δ₁ : δ₂ < δ₁ := by rw [hδ₂def]; linarith [min_le_right δ δ₁]
        have hmeet : ∃ z ∈ Metric.ball y δ₂, z ∉ S := by
          by_contra hcon
          push Not at hcon
          exact hyS.2 (interior_maximal (fun z hz => hcon z hz) Metric.isOpen_ball
            (Metric.mem_ball_self hδ₂pos))
        obtain ⟨z, hzδ, hzS⟩ := hmeet
        refine ⟨z, ?_, ?_⟩
        · have hzε : z ∈ Metric.ball x ε := hδ₁ (Metric.ball_subset_ball hδ₂δ₁.le hzδ)
          exact hε'mem z hzS (Metric.ball_subset_ball hεε' hzε)
        · have hmem := Metric.mem_ball.mp hzδ
          linarith [dist_comm y z, hmem, hδ₂δ]
      · intro hyint
        obtain ⟨δ, hδpos, hδsub⟩ :=
          Metric.isOpen_iff.mp (hSclosed.isOpen_compl.connectedComponentIn (F := Sᶜ) (x := q))
            y (interior_subset hyint)
        obtain ⟨z, hzS, hzd⟩ := (Metric.mem_closure_iff.mp hyS.1) δ hδpos
        exact (connectedComponentIn_subset Sᶜ q)
          (hδsub (by simpa [Metric.mem_ball, dist_comm] using hzd)) hzS
  -- the range points at radius below `ε` are precisely the branch points
  have hmemBranch : ∀ ρ ∈ Set.Ioo (0 : ℝ) ε,
      x + (ρ : ℂ) * (ustar * eicC (Φmax + betaC r ρ))
          ∈ frontier (connectedComponentIn (Sᶜ) q)
      ∧ x + (ρ : ℂ) * (ustar * eicC (Φmin - betaC r ρ))
          ∈ frontier (connectedComponentIn (Sᶜ) q) := by
    intro ρ hρ
    have hρlt : ρ < ε := hρ.2
    have hball : ∀ {y : ℂ}, dist y x = ρ → y ∈ Metric.ball x ε := by
      intro y hy
      rw [Metric.mem_ball, hy]; exact hρlt
    have hdPlus : dist (x + (ρ : ℂ) * (ustar * eicC (Φmax + betaC r ρ))) x = ρ := by
      rw [dist_eq_norm]
      have h1 : x + (ρ : ℂ) * (ustar * eicC (Φmax + betaC r ρ)) - x
          = (ρ : ℂ) * (ustar * eicC (Φmax + betaC r ρ)) := by ring
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ.1, norm_mul,
        norm_eicC, mul_one, hustar, mul_one]
    have hdMinus : dist (x + (ρ : ℂ) * (ustar * eicC (Φmin - betaC r ρ))) x = ρ := by
      rw [dist_eq_norm]
      have h1 : x + (ρ : ℂ) * (ustar * eicC (Φmin - betaC r ρ)) - x
          = (ρ : ℂ) * (ustar * eicC (Φmin - betaC r ρ)) := by ring
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ.1, norm_mul,
        norm_eicC, mul_one, hustar, mul_one]
    refine ⟨?_, ?_⟩
    · have hmem := show x + (ρ : ℂ) * (ustar * eicC (Φmax + betaC r ρ))
          ∈ frontier (connectedComponentIn (Sᶜ) q) ∩ Metric.ball x ε from by
        rw [hfrontier_eq]; exact ⟨hbranchPlus ρ hρ, hball hdPlus⟩
      exact hmem.1
    · have hmem := show x + (ρ : ℂ) * (ustar * eicC (Φmin - betaC r ρ))
          ∈ frontier (connectedComponentIn (Sᶜ) q) ∩ Metric.ball x ε from by
        rw [hfrontier_eq]; exact ⟨hbranchMinus ρ hρ, hball hdMinus⟩
      exact hmem.1
  -- the two direction families differ
  have hdirNe : ∀ {ρ ρ' : ℝ}, 0 < ρ → 0 < ρ' → ρ ≤ ε → ρ' ≤ ε →
      ustar * eicC (Φmax + betaC r ρ) ≠ ustar * eicC (Φmin - betaC r ρ') := by
    intro ρ ρ' hρ hρ' hρε hρ'ε
    have hβπ : betaC r ρ < Real.pi / 2 := betaC_lt_pi_div_two hr hρ
    have hβ'π : betaC r ρ' < Real.pi / 2 := betaC_lt_pi_div_two hr hρ'
    have hβ0 : 0 < betaC r ρ := betaC_pos hr hρ (lt_of_le_of_lt hρε hε2r)
    have hβ'0 : 0 < betaC r ρ' := betaC_pos hr hρ' (lt_of_le_of_lt hρ'ε hε2r)
    have hsp : Φmax - Φmin < 2 * betaC r ρ := by
      have h1 : betaC r ε ≤ betaC r ρ := betaC_anti hr hρ (le_of_lt hε2r) hρε
      linarith [hspreadε, h1]
    have hsub : 0 < (Φmax + betaC r ρ) - (Φmin - betaC r ρ') := by
      linarith [hΦle, hβ0, hβ'0]
    have hsub2 : (Φmax + betaC r ρ) - (Φmin - betaC r ρ') < 2 * Real.pi := by
      linarith [hβπ, hβ'π, Real.pi_pos]
    intro hEq
    have hu0 : ustar ≠ 0 := by
      intro h; rw [h, norm_zero] at hustar; exact zero_ne_one hustar
    have := mul_left_cancel₀ hu0 hEq
    exact eicC_ne_of_sub_mem hsub hsub2 this

  -- the parametrisation
  let γ : ℝ → ℂ := fun s => if 0 ≤ s then
      x + ((ε * s : ℝ) : ℂ) * (ustar * eicC (Φmax + betaC r (min (ε * s) ε)))
    else x + ((ε * (-s) : ℝ) : ℂ) * (ustar * eicC (Φmin - betaC r (min (ε * (-s)) ε)))
  have hγ0 : γ 0 = x := by
    rw [show γ 0 = x + ((ε * 0 : ℝ) : ℂ)
        * (ustar * eicC (Φmax + betaC r (min (ε * 0) ε))) from by
      simp only [γ, if_pos (le_refl (0 : ℝ))]]
    simp
  have hcontPlus : Continuous (fun s : ℝ =>
      x + ((ε * s : ℝ) : ℂ) * (ustar * eicC (Φmax + betaC r (min (ε * s) ε)))) := by
    have hb : Continuous (fun s : ℝ => betaC r (min (ε * s) ε)) := by
      simp only [betaC]
      exact Real.continuous_arccos.comp
        (((continuous_const.mul continuous_id : Continuous fun s : ℝ => ε * s).min
          continuous_const).div_const (2 * r))
    have h2 : Continuous (fun s : ℝ => eicC (Φmax + betaC r (min (ε * s) ε))) :=
      continuous_eicC.comp (continuous_const.add hb)
    exact ((((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
      (continuous_const.mul h2)))).const_add x
  have hcontMinus : Continuous (fun s : ℝ =>
      x + ((ε * (-s) : ℝ) : ℂ) * (ustar * eicC (Φmin - betaC r (min (ε * (-s)) ε)))) := by
    have hb : Continuous (fun s : ℝ => betaC r (min (ε * (-s)) ε)) := by
      simp only [betaC]
      exact Real.continuous_arccos.comp
        (((continuous_const.mul continuous_neg : Continuous fun s : ℝ => ε * (-s)).min
          continuous_const).div_const (2 * r))
    have h2 : Continuous (fun s : ℝ => eicC (Φmin - betaC r (min (ε * (-s)) ε))) :=
      continuous_eicC.comp (continuous_const.sub hb)
    exact ((((Complex.continuous_ofReal.comp (continuous_const.mul continuous_neg)).mul
      (continuous_const.mul h2)))).const_add x
  have hcont : Continuous γ := by
    rw [show γ = fun s : ℝ => if 0 ≤ s then
        x + ((ε * s : ℝ) : ℂ) * (ustar * eicC (Φmax + betaC r (min (ε * s) ε)))
      else x + ((ε * (-s) : ℝ) : ℂ) * (ustar * eicC (Φmin - betaC r (min (ε * (-s)) ε)))
      from rfl]
    refine Continuous.if ?_ hcontPlus hcontMinus
    intro a ha
    have ha0 : a = 0 := by
      rw [show {s : ℝ | 0 ≤ s} = Set.Ici (0 : ℝ) from rfl, frontier_Ici] at ha
      exact ha
    subst ha0
    simp
  have hdist : ∀ s : ℝ, dist (γ s) x = ε * |s| := by
    intro s
    by_cases hs : 0 ≤ s
    · simp only [γ, if_pos hs]
      rw [dist_eq_norm]
      have h1 : x + ((ε * s : ℝ) : ℂ) * (ustar * eicC (Φmax + betaC r (min (ε * s) ε))) - x
          = ((ε * s : ℝ) : ℂ) * (ustar * eicC (Φmax + betaC r (min (ε * s) ε))) := by ring
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hεpos.le hs),
        norm_mul, norm_eicC, mul_one, hustar, mul_one, abs_of_nonneg hs]
    · rw [not_le] at hs
      simp only [γ, if_neg (not_le.mpr hs)]
      rw [dist_eq_norm]
      have h1 : x + ((ε * (-s) : ℝ) : ℂ) * (ustar * eicC (Φmin - betaC r (min (ε * (-s)) ε))) - x
          = ((ε * (-s) : ℝ) : ℂ) * (ustar * eicC (Φmin - betaC r (min (ε * (-s)) ε))) := by ring
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hεpos.le (by linarith)),
        norm_mul, norm_eicC, mul_one, hustar, mul_one, abs_of_neg hs]
  have hsign : ∀ s : ℝ, s ≠ 0 → γ s ≠ γ (-s) := by
    intro s hs0 hEq
    have hminpos : ∀ a : ℝ, 0 < a → 0 < min (ε * a) ε := fun a ha =>
      lt_min (mul_pos hεpos ha) hεpos
    have hminle : ∀ a : ℝ, 0 < a → min (ε * a) ε ≤ ε := fun a ha => min_le_right _ _
    rcases lt_or_gt_of_ne hs0 with hs | hs
    · have h1 : γ s = x + ((ε * (-s) : ℝ) : ℂ)
          * (ustar * eicC (Φmin - betaC r (min (ε * (-s)) ε))) := by
        simp only [γ, if_neg (not_le.mpr hs)]
      have h2 : γ (-s) = x + ((ε * (-s) : ℝ) : ℂ)
          * (ustar * eicC (Φmax + betaC r (min (ε * (-s)) ε))) := by
        have hle : (0 : ℝ) ≤ -s := by linarith
        simp only [γ, if_pos hle, neg_neg]
      rw [h1, h2] at hEq
      have hρne : ((ε * (-s) : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact mul_ne_zero (ne_of_gt hεpos) (by linarith)
      have hdir : ustar * eicC (Φmin - betaC r (min (ε * (-s)) ε))
          = ustar * eicC (Φmax + betaC r (min (ε * (-s)) ε)) := by
        have h3 := congrArg (fun z : ℂ => z - x) hEq
        simp only [add_sub_cancel_left] at h3
        exact mul_left_cancel₀ hρne h3
      exact hdirNe (hminpos (-s) (by linarith)) (hminpos (-s) (by linarith))
        (hminle (-s) (by linarith)) (hminle (-s) (by linarith)) hdir.symm
    · have h1 : γ s = x + ((ε * s : ℝ) : ℂ)
          * (ustar * eicC (Φmax + betaC r (min (ε * s) ε))) := by
        simp only [γ, if_pos hs.le]
      have h2 : γ (-s) = x + ((ε * s : ℝ) : ℂ)
          * (ustar * eicC (Φmin - betaC r (min (ε * s) ε))) := by
        have hlt : ¬ ((0 : ℝ) ≤ -s) := by linarith
        simp only [γ, if_neg hlt, neg_neg]
      rw [h1, h2] at hEq
      have hρne : ((ε * s : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact mul_ne_zero (ne_of_gt hεpos) (ne_of_gt hs)
      have hdir : ustar * eicC (Φmax + betaC r (min (ε * s) ε))
          = ustar * eicC (Φmin - betaC r (min (ε * s) ε)) := by
        have h3 := congrArg (fun z : ℂ => z - x) hEq
        simp only [add_sub_cancel_left] at h3
        exact mul_left_cancel₀ hρne h3
      exact hdirNe (hminpos s hs) (hminpos s hs) (hminle s hs) (hminle s hs) hdir
  have hinj : Function.Injective γ := by
    intro s s' hEq
    have h1 : ε * |s| = ε * |s'| := by rw [← hdist s, ← hdist s', hEq]
    have h2 : |s| = |s'| := mul_left_cancel₀ (ne_of_gt hεpos) h1
    by_cases hs : 0 ≤ s
    · by_cases hs' : 0 ≤ s'
      · rwa [abs_of_nonneg hs, abs_of_nonneg hs'] at h2
      · exfalso
        rw [not_le] at hs'
        rw [abs_of_nonneg hs, abs_of_neg hs'] at h2
        exact hsign s (by rintro rfl; linarith)
          (by rw [show s' = -s by linarith] at hEq; exact hEq)
    · rw [not_le] at hs
      by_cases hs' : 0 ≤ s'
      · exfalso
        rw [abs_of_neg hs, abs_of_nonneg hs'] at h2
        exact hsign s (by rintro rfl; linarith)
          (by rw [show s' = -s by linarith] at hEq; exact hEq)
      · rw [not_le] at hs'
        rw [abs_of_neg hs, abs_of_neg hs'] at h2; linarith
  have hgraph : ∀ y ∈ frontier S, y ≠ x → dist y x < ε →
      ∃ ρ ∈ Set.Ioo (0 : ℝ) ε,
        (y = x + (ρ : ℂ) * (ustar * eicC (Φmax + betaC r ρ))
          ∨ y = x + (ρ : ℂ) * (ustar * eicC (Φmin - betaC r ρ))) :=
    fun y hy hyx hyd => frontier_eq_graph hr hustar hmax hmin hmaxatt hminatt hlo hhi hmodel
      hεpos le_rfl hε2c.le hy hyx hyd
  refine ⟨ε, γ, hεpos, hcont, hinj, hγ0, ?_⟩
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨s, hs, rfl⟩
    rcases eq_or_ne s 0 with hs0 | hs0
    · subst hs0
      rw [hγ0, hfrontier_eq]
      exact ⟨hx, Metric.mem_ball_self hεpos⟩
    rcases lt_or_gt_of_ne hs0 with hsneg | hspos
    · have hb : γ s = x + ((ε * (-s) : ℝ) : ℂ)
          * (ustar * eicC (Φmin - betaC r (ε * (-s)))) := by
        have h1 : ¬ ((0 : ℝ) ≤ s) := not_le.mpr hsneg
        simp only [γ, if_neg h1]
        rw [show min (ε * (-s)) ε = ε * (-s) from min_eq_left (by nlinarith [hs.1, hεpos])]
      rw [hb]
      have h1 : (0:ℝ) < -s := by linarith
      have h2 : ε * (-s) < ε := by
        have := mul_lt_mul_of_pos_left (show -s < 1 by linarith [hs.1]) hεpos
        rwa [mul_one] at this
      refine ⟨(hmemBranch (ε * (-s)) ⟨mul_pos hεpos h1, h2⟩).2, ?_⟩
      rw [Metric.mem_ball, ← hb, hdist s, abs_of_neg hsneg]
      exact h2
    · have hb : γ s = x + ((ε * s : ℝ) : ℂ)
          * (ustar * eicC (Φmax + betaC r (ε * s))) := by
        simp only [γ, if_pos hspos.le]
        rw [show min (ε * s) ε = ε * s from min_eq_left (by nlinarith [hs.2, hεpos])]
      rw [hb]
      have h2 : ε * s < ε := by
        have := mul_lt_mul_of_pos_left hs.2 hεpos
        rwa [mul_one] at this
      refine ⟨(hmemBranch (ε * s) ⟨mul_pos hεpos hspos, h2⟩).1, ?_⟩
      rw [Metric.mem_ball, ← hb, hdist s, abs_of_nonneg hspos.le]
      exact h2
  · rintro y ⟨hy, hyb⟩
    have hyd : dist y x < ε := by
      have hmem := Metric.mem_ball.mp hyb
      linarith [dist_comm y x, hmem]
    rcases eq_or_ne y x with hyx | hyx
    · subst hyx
      exact ⟨0, ⟨by norm_num, by norm_num⟩, hγ0⟩
    · have hyS : y ∈ frontier S := by
        have hmem : y ∈ frontier (connectedComponentIn (Sᶜ) q) ∩ Metric.ball x ε := ⟨hy, hyb⟩
        rw [hfrontier_eq] at hmem
        exact hmem.1
      obtain ⟨ρ, hρ, hρcase⟩ := hgraph y hyS hyx hyd
      rcases hρcase with hρcase | hρcase
      · refine ⟨ρ / ε, ⟨?_, ?_⟩, ?_⟩
        · linarith [div_pos hρ.1 hεpos]
        · rw [div_lt_one hεpos]; exact hρ.2
        · have hmin : min (ε * (ρ / ε)) ε = ε * (ρ / ε) := by
            refine min_eq_left ?_
            rw [mul_div_cancel₀ _ (ne_of_gt hεpos)]; exact hρ.2.le
          have hb : γ (ρ / ε) = x + ((ε * (ρ / ε) : ℝ) : ℂ)
              * (ustar * eicC (Φmax + betaC r (min (ε * (ρ / ε)) ε))) := by
            simp only [γ, if_pos (div_nonneg hρ.1.le hεpos.le)]
          rw [hb, hmin, mul_div_cancel₀ _ (ne_of_gt hεpos)]
          exact hρcase.symm
      · refine ⟨-(ρ / ε), ?_, ?_⟩
        · rw [Set.mem_Ioo]
          constructor
          · linarith [(div_lt_one hεpos).mpr hρ.2]
          · linarith [div_pos hρ.1 hεpos]
        · have hεs : ε * (ρ / ε) = ρ := mul_div_cancel₀ _ (ne_of_gt hεpos)
          have hmin : min (ε * (ρ / ε)) ε = ε * (ρ / ε) := by
            refine min_eq_left ?_
            rw [hεs]; exact hρ.2.le
          have hb : γ (-(ρ / ε)) = x + ((ε * (ρ / ε) : ℝ) : ℂ)
              * (ustar * eicC (Φmin - betaC r (min (ε * (ρ / ε)) ε))) := by
            have h1 : ¬ ((0 : ℝ) ≤ -(ρ / ε)) := by linarith [div_pos hρ.1 hεpos]
            simp only [γ, if_neg h1, neg_neg]
          rw [hb, hmin, hεs]
          exact hρcase.symm
