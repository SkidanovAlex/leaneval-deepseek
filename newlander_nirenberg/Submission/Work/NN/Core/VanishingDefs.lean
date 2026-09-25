/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The fixed-disc potential of data vanishing on a polydisc: definitions

This file collects the objects used by `Work.NN.Core.holderNorm_fiberPot_of_vanishing`.

For radii `r < s < R` (componentwise, with `s` the radius of vanishing and `R` the radius of the
fixed disc) and a datum `v` vanishing on `polydisc 0 s`, the fixed-disc potential
`fiberPot R j v` agrees, on `polydisc 0 r`, with the integral over the *annulus*
`fiberAnnulus (s j) R = {w : ℂ | s j ≤ ‖w‖ ∧ ‖w‖ < R}` of the integrand `v (z with z j := w)`
against a *non-singular* kernel, because the integrand vanishes on the missing disc
`‖w‖ < s j`.  This is what makes the `C^{m,α}` estimate on `polydisc 0 r` elementary: the kernel
`(w - z j)^{-(l+1)}` is smooth and bounded on the annulus, so all derivatives may be taken under
the integral sign and are bounded by the sup norms and `α`-seminorms of the derivatives of `v` on
the access polydisc `fiberAccess r j R`.

The `l`-th potential `fiberPotAnn j l A η` below is the operator obtained by differentiating
`fiberPot` `l` times in the `j`-th coordinate: the kernel `(w - z j)⁻¹` becomes
`(w - z j)^{-(l+1)}`, while the data `η` is untouched.  The induction on the derivative order in
the main theorem uses the family `l = 0, …, m`.
-/
import Mathlib
import Submission.Work.NN.Core.fiberPot
import Submission.Work.NN.Core.fiberBeurling
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.NN.Core

/-- The annulus `{w : ℂ | s ≤ ‖w‖ ∧ ‖w‖ < R}`: the region on which the integrand of the
fixed-disc potential survives when the datum vanishes on the disc of radius `s`. -/
def fiberAnnulus (s R : ℝ) : Set ℂ := {w : ℂ | s ≤ ‖w‖ ∧ ‖w‖ < R}

@[simp] lemma mem_fiberAnnulus {s R : ℝ} {w : ℂ} :
    w ∈ fiberAnnulus s R ↔ s ≤ ‖w‖ ∧ ‖w‖ < R := Iff.rfl

lemma measurableSet_fiberAnnulus (s R : ℝ) : MeasurableSet (fiberAnnulus s R) :=
  ((isClosed_le continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet)

lemma fiberAnnulus_subset_ball (s R : ℝ) : fiberAnnulus s R ⊆ Metric.ball (0 : ℂ) R :=
  fun w hw => by rw [Metric.mem_ball, dist_zero_right]; exact hw.2

lemma fiberAnnulus_eq_ball_diff (s R : ℝ) :
    fiberAnnulus s R = Metric.ball (0 : ℂ) R \ Metric.ball (0 : ℂ) s := by
  ext w
  simp only [mem_fiberAnnulus, Metric.mem_ball, dist_zero_right, Set.mem_sdiff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, fun h => absurd h (not_lt.mpr h1)⟩
  · rintro ⟨h2, h3⟩
    exact ⟨not_lt.mp h3, h2⟩

lemma volume_fiberAnnulus_lt_top (s R : ℝ) : volume (fiberAnnulus s R) < ⊤ :=
  lt_of_le_of_lt (measure_mono (fiberAnnulus_subset_ball s R))
    (by rw [Complex.volume_ball]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (by simp))

/-- Explicit numerical bound for the area of the annulus. -/
lemma volume_fiberAnnulus_toReal_le {s R : ℝ} (hR : 0 ≤ R) :
    (volume (fiberAnnulus s R)).toReal ≤ R ^ 2 * Real.pi := by
  have htop : volume (Metric.ball (0 : ℂ) R) ≠ ⊤ := by
    rw [Complex.volume_ball]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (by simp)
  refine le_trans (ENNReal.toReal_mono htop (measure_mono (fiberAnnulus_subset_ball s R))) ?_
  rw [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR,
    ENNReal.coe_toReal, NNReal.coe_real_pi]

/-- **The `l`-th fixed-disc potential in an annulus.**  `fiberPotAnn j l A η z` is the potential
`-(1/π) ∫_{w ∈ A} η (z with z j := w) (w - z j)^{-(l+1)} dw`; for `l = 0` and `A` the full disc
this is the fixed-disc Cauchy potential `fiberPot`. -/
def fiberPotAnn {n : ℕ} (j : Fin n) (l : ℕ) (A : Set ℂ) (η : Cn n → ℂ) (z : Cn n) : ℂ :=
  -((Real.pi : ℂ))⁻¹ * ∫ w in A, η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)

@[simp] lemma fiberPotAnn_apply {n : ℕ} (j : Fin n) (l : ℕ) (A : Set ℂ) (η : Cn n → ℂ)
    (z : Cn n) :
    fiberPotAnn j l A η z
      = -((Real.pi : ℂ))⁻¹ *
        ∫ w in A, η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1) := rfl

lemma fiberPotAnn_zero_fun {n : ℕ} (j : Fin n) (l : ℕ) (A : Set ℂ) (z : Cn n) :
    fiberPotAnn j l A (fun _ => 0) z = 0 := by
  simp [fiberPotAnn]

lemma fiberPotAnn_const_mul {n : ℕ} (j : Fin n) (l : ℕ) (A : Set ℂ) (c : ℂ)
    (η : Cn n → ℂ) (z : Cn n) :
    fiberPotAnn j l A (fun y => c * η y) z = c * fiberPotAnn j l A η z := by
  rw [fiberPotAnn_apply, fiberPotAnn_apply]
  have hlin : (∫ w in A, (fun y => c * η y) (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1))
      = ∫ w in A, c * (η (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    ring
  rw [hlin, MeasureTheory.integral_const_mul]
  ring

/-- The vanishing condition: `η` vanishes on the open polydisc `polydisc 0 s`. -/
def VanOn {n : ℕ} (s : Fin n → ℝ) (η : Cn n → ℂ) : Prop :=
  ∀ z : Cn n, (∀ i, ‖z i‖ < s i) → η z = 0

/-- The continuous linear map `z ↦ (z with z j := 0)`, i.e. the projection that kills the `j`-th
coordinate.  It is the derivative of `z ↦ Function.update z j w`. -/
def updateZero {n : ℕ} (j : Fin n) : Cn n →L[ℝ] Cn n :=
  ContinuousLinearMap.pi fun i => if i = j then 0 else ContinuousLinearMap.proj i

lemma updateZero_apply {n : ℕ} (j : Fin n) (x : Cn n) :
    updateZero j x = Function.update x j 0 := by
  ext i
  by_cases h : i = j
  · subst h
    simp [updateZero]
  · simp [updateZero, h]

/-- The derivative (with respect to the base point) of the insertion map
`z ↦ Function.update z j w`. -/
lemma hasFDerivAt_update_ann {n : ℕ} (j : Fin n) (w : ℂ) (x : Cn n) :
    HasFDerivAt (fun z : Cn n => Function.update z j w) (updateZero j) x := by
  have hfe : (fun z : Cn n => Function.update z j w)
      = fun z => updateZero j z + Function.update (0 : Cn n) j w := by
    funext z
    rw [updateZero_apply]
    ext i
    by_cases h : i = j
    · subst h; simp
    · simp [Function.update_of_ne h]
  rw [hfe]
  exact (ContinuousLinearMap.hasFDerivAt (updateZero j)).add_const _

/-- Points of the annulus are at distance at least `s - ‖z j‖` from the pole `z j`. -/
lemma norm_sub_le_of_mem_fiberAnnulus {s R : ℝ} {z w : ℂ} (hw : w ∈ fiberAnnulus s R) :
    s - ‖z‖ ≤ ‖w - z‖ := by
  have h1 : s ≤ ‖w‖ := hw.1
  calc s - ‖z‖ ≤ ‖w‖ - ‖z‖ := by linarith
    _ ≤ ‖w - z‖ := norm_sub_norm_le w z

lemma inv_norm_le_of_mem_fiberAnnulus {s R d : ℝ} (hd0 : 0 < d) {z w : ℂ}
    (hw : w ∈ fiberAnnulus s R) (hd : d ≤ s - ‖z‖) : ‖(w - z)⁻¹‖ ≤ d⁻¹ := by
  have h1 : d ≤ ‖w - z‖ := le_trans hd (norm_sub_le_of_mem_fiberAnnulus hw)
  rw [norm_inv]
  exact inv_anti₀ hd0 h1

/-- The kernel is bounded on the annulus. -/
lemma norm_pow_inv_le_of_mem_fiberAnnulus {s R d : ℝ} (hd0 : 0 < d) {z w : ℂ} (l : ℕ)
    (hw : w ∈ fiberAnnulus s R) (hd : d ≤ s - ‖z‖) :
    ‖((w - z)⁻¹) ^ (l + 1)‖ ≤ (d⁻¹) ^ (l + 1) := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (inv_norm_le_of_mem_fiberAnnulus hd0 hw hd) _

/-- The point of the access polydisc reached from `polydisc 0 r` by inserting `w` in the `j`-th
coordinate lies in `fiberAccess r j R` as soon as `‖w‖ < R`. -/
lemma mem_fiberAccess_update {n : ℕ} {r : Fin n → ℝ} {j : Fin n} {R : ℝ} {z : Cn n} {w : ℂ}
    (hz : z ∈ Work.CR.Flat.polydisc 0 r) (hw : ‖w‖ < R) :
    Function.update z j w ∈ fiberAccess r j R := by
  rw [mem_fiberAccess]
  refine ⟨fun i hi => ?_, ?_⟩
  · have h : ‖z i‖ < r i := by simpa using hz i
    simpa [Function.update_of_ne hi] using h
  · simpa using hw

/-- Inserting `w` in the `j`-th coordinate of a point of `polydisc 0 r` gives a point of
`polydisc 0 s` whenever `‖w‖ < s j` and `r i < s i`. -/
lemma mem_polydisc_update {n : ℕ} {r s : Fin n → ℝ} {j : Fin n} {z : Cn n} {w : ℂ}
    (hrs : ∀ i, r i < s i) (hz : z ∈ Work.CR.Flat.polydisc 0 r) (hw : ‖w‖ < s j) :
    Function.update z j w ∈ Work.CR.Flat.polydisc 0 s := by
  intro i
  by_cases h : i = j
  · subst h
    simpa using hw
  · rw [Function.update_of_ne h]
    simpa using lt_trans (by simpa using hz i) (hrs i)

/-- Inserting the same `w` in the `j`-th coordinate is `1`-Lipschitz in the base point. -/
lemma norm_update_sub_update_le_van {n : ℕ} (j : Fin n) (w : ℂ) (x y : Cn n) :
    ‖Function.update x j w - Function.update y j w‖ ≤ ‖x - y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
  by_cases h : i = j
  · subst h
    simp
  · rw [Pi.sub_apply, Function.update_of_ne h, Function.update_of_ne h]
    exact norm_le_pi_norm (x - y) i

/-- A function vanishing on the open polydisc `polydisc 0 s` has vanishing derivative at each
point of the polydisc. -/
lemma VanOn.fderiv_eq_zero {n : ℕ} {s : Fin n → ℝ} {η : Cn n → ℂ} (h : VanOn s η)
    {y : Cn n} (hy : ∀ i, ‖y i‖ < s i) : fderiv ℝ η y = 0 := by
  have hopen : Work.CR.Flat.polydisc (0 : Cn n) s ∈ nhds y :=
    (Work.CR.Flat.isOpen_polydisc 0 s).mem_nhds (by simpa using hy)
  have hev : η =ᶠ[nhds y] (fun _ => 0) := by
    filter_upwards [hopen] with z hz
    exact h z (by simpa using hz)
  rw [hev.fderiv_eq]
  simp

/-- Any directional derivative of a function vanishing on `polydisc 0 s` also vanishes there. -/
lemma VanOn.fderiv_apply {n : ℕ} {s : Fin n → ℝ} {η : Cn n → ℂ} (h : VanOn s η)
    {y : Cn n} (hy : ∀ i, ‖y i‖ < s i) (v : Cn n) : fderiv ℝ η y v = 0 := by
  rw [h.fderiv_eq_zero hy]; simp

/-- The data obtained from `η` by taking a directional derivative vanishes on `polydisc 0 s`. -/
lemma VanOn.fderiv_fun {n : ℕ} {s : Fin n → ℝ} {η : Cn n → ℂ} (h : VanOn s η) (v : Cn n) :
    VanOn s (fun y => fderiv ℝ η y v) :=
  fun y hy => h.fderiv_apply hy v

end Work.NN.Core
