/-
# `Work.FIArea6Hecke.R2.Defs`

Vocabulary for a **self-contained proof of the conductor Gauss-sum duality**
(`Work.FIArea6Hecke.R.conductorGaussSumDualityClean`) that avoids the *cardinality* of the
residue ring `ℤ[i]/M`: it works with the canonical complete residue system `crsMin M`
(the "minimal element of each box fibre") and with the common fibre size `kappa M`, so that
the two occurrences of `kappa M` cancel in the final duality identity.

* `crsMin M` — the elements of the box `gbox (gnorm M) = [0,N)²` that are minimal (for the
  order `z ↦ z.re + N·z.im`) inside their residue class modulo `M`;
* `boxK M` — the kernel `[0,N)² ∩ M·ℤ[i]`;
* `kappa M = (boxK M).card` — the common cardinality of every fibre of the reduction
  `box → ℤ[i]/M`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.ConductorGaussSumDefs
import Submission.Work.FIArea6Hecke.R.ConductorThetaDefs
import Submission.Work.FIArea6Hecke.R.StrictConductorDefs
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea6Hecke.CGD.BoxCRS
import Submission.Work.FIArea6Hecke.CGD.FibDefs
import Submission.Work.FIArea6Hecke.CGD.CrsCalculus
import Submission.Work.FIArea6Hecke.CGD.EkernOne
import Submission.Work.FIArea6Hecke.CGD.Reindex

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R2

open scoped BigOperators
open Work.FIArea6Hecke.R

noncomputable section

/-! ## The canonical complete residue system and the fibre size -/

/-- `crsMin M` is the set of elements of the box `[0,N)²`, `N = gnorm M`, that are minimal in
their residue class mod `M` for the order `z ↦ z.re + N · z.im`.  This is a complete residue
system modulo `M` (see `crsMin_isCRS`). -/
def crsMin (M : GaussianInt) : Finset GaussianInt := by
  classical
  exact (gbox (Work.FIPlan.gnorm M)).filter fun s =>
    ∀ t ∈ gbox (Work.FIPlan.gnorm M), M ∣ (t - s) →
      s.re + (Work.FIPlan.gnorm M : ℤ) * s.im ≤ t.re + (Work.FIPlan.gnorm M : ℤ) * t.im

/-- The kernel `[0,N)² ∩ M ℤ[i]` of the reduction of the box modulo `M`. -/
def boxK (M : GaussianInt) : Finset GaussianInt := by
  classical
  exact (gbox (Work.FIPlan.gnorm M)).filter fun k => M ∣ k

/-- The common cardinality of all fibres of the reduction of the box modulo `M`. -/
def kappa (M : GaussianInt) : ℕ := (boxK M).card

/-! ## The Gaussian norm -/

lemma gnorm_eq_zero_iff {z : GaussianInt} : Work.FIPlan.gnorm z = 0 ↔ z = 0 := by
  simp only [Work.FIPlan.gnorm, Int.natAbs_eq_zero, GaussianInt.norm_eq_zero]

lemma gnorm_ne_zero {z : GaussianInt} (hz : z ≠ 0) : Work.FIPlan.gnorm z ≠ 0 :=
  fun h => hz (gnorm_eq_zero_iff.mp h)

lemma gnorm_pos {z : GaussianInt} (hz : z ≠ 0) : 0 < Work.FIPlan.gnorm z :=
  Nat.pos_of_ne_zero (gnorm_ne_zero hz)

/-- `M * conj M = |M|²`, as an identity in `ℤ[i]`. -/
lemma mul_star_eq_gnorm (M : GaussianInt) :
    M * star M = ((Work.FIPlan.gnorm M : ℕ) : GaussianInt) := by
  rw [← Zsqrtd.norm_eq_mul_conj M, ← GaussianInt.natCast_natAbs_norm (α := GaussianInt) M]
  rfl

lemma dvd_gnorm (M : GaussianInt) : M ∣ ((Work.FIPlan.gnorm M : ℕ) : GaussianInt) :=
  ⟨star M, (mul_star_eq_gnorm M).symm⟩

lemma intCast_gnorm_ne_zero {M : GaussianInt} (hM : M ≠ 0) :
    ((Work.FIPlan.gnorm M : ℕ) : GaussianInt) ≠ 0 := by
  rw [← mul_star_eq_gnorm, mul_ne_zero_iff]
  exact ⟨hM, fun h => hM (star_eq_zero.mp h)⟩

lemma gnorm_one : Work.FIPlan.gnorm (1 : GaussianInt) = 1 := by
  rw [Work.FIPlan.gnorm, Zsqrtd.norm_one]
  rfl

lemma gnorm_mul (z w : GaussianInt) :
    Work.FIPlan.gnorm (z * w) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-! ## The bilinear form `gdot` -/

lemma gdot_eq_re_mul_star (x y : GaussianInt) : gdot x y = (x * star y).re := by
  simp only [gdot, Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star]
  ring

lemma gdot_add_right (x y z : GaussianInt) : gdot x (y + z) = gdot x y + gdot x z := by
  simp only [gdot, Zsqrtd.re_add, Zsqrtd.im_add]
  ring

@[simp] lemma gdot_zero_right' (x : GaussianInt) : gdot x 0 = 0 := by simp [gdot]

lemma gdot_natCast_left (n : ℕ) (x y : GaussianInt) :
    gdot (((n : ℕ) : GaussianInt) * x) y = (n : ℤ) * gdot x y := by
  rw [gdot_eq_re_mul_star, gdot_eq_re_mul_star]
  have h : (((n : ℕ) : GaussianInt) * x) * star y
      = ((n : ℕ) : GaussianInt) * (x * star y) := by ring
  rw [h]
  simp only [Zsqrtd.re_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast]
  ring

/-- `N ∣ gdot (N z) ξ`. -/
lemma dvd_gdot_intCast_mul (M : GaussianInt) (z ξ : GaussianInt) :
    (Work.FIPlan.gnorm M : ℤ) ∣ gdot (((Work.FIPlan.gnorm M : ℕ) : GaussianInt) * z) ξ := by
  rw [gdot_natCast_left]
  exact dvd_mul_right _ _

lemma gdot_mul_left (x y z : GaussianInt) : gdot (x * y) z = gdot x (z * star y) := by
  rw [gdot_eq_re_mul_star, gdot_eq_re_mul_star]
  congr 1
  rw [star_mul, star_star]
  ring

/-- `gdot (M*b) (M*a) = gnorm M * gdot b a`: the multiplicative transparency of the pairing. -/
lemma gdot_mul_mul (M a b : GaussianInt) :
    gdot (M * b) (M * a) = (Work.FIPlan.gnorm M : ℤ) * gdot b a := by
  rw [gdot_eq_re_mul_star, gdot_eq_re_mul_star]
  have h1 : star (M * a) = star a * star M := star_mul M a
  have h2 : (M * b) * (star a * star M) = (M * star M) * (b * star a) := by ring
  have h : (M * b) * star (M * a) = ((Work.FIPlan.gnorm M : ℕ) : GaussianInt) * (b * star a) := by
    rw [h1, h2, mul_star_eq_gnorm]
  rw [h]
  simp only [Zsqrtd.re_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast]
  ring

/-! ## The additive character `ekern` -/

/-- `ekern` is `N`-periodic in its point variable (`N = gnorm M ≥ 1`, `M ≠ 0`). -/
lemma ekern_add_intCast (M w z x : GaussianInt) (hM : M ≠ 0) :
    ekern M w (x + ((Work.FIPlan.gnorm M : ℕ) : GaussianInt) * z) = ekern M w x := by
  rw [ekern_add_right]
  have h1 : ekern M w (((Work.FIPlan.gnorm M : ℕ) : GaussianInt) * z) = 1 := by
    rw [Work.FIArea6Hecke.CGD.EkernOne M hM w _]
    exact dvd_gdot_intCast_mul M z w
  rw [h1, mul_one]

/-- If `M ∣ w` and `M ∣ x` then the character is trivial at `x` with frequency `w`. -/
lemma ekern_one_of_dvd_mul (M w x : GaussianInt) (hM : M ≠ 0) (hw : M ∣ w) (hx : M ∣ x) :
    ekern M w x = 1 := by
  obtain ⟨b, rfl⟩ := hw
  obtain ⟨a, rfl⟩ := hx
  rw [Work.FIArea6Hecke.CGD.EkernOne M hM (M * b) (M * a), gdot_mul_mul]
  exact dvd_mul_right _ _

/-- `ekern M w` is periodic for multiples of `M` when `M ∣ w`. -/
lemma ekern_add_of_dvd (M w x t : GaussianInt) (hM : M ≠ 0) (hw : M ∣ w) (ht : M ∣ t) :
    ekern M w (x + t) = ekern M w x := by
  rw [ekern_add_right, ekern_one_of_dvd_mul M w t hM hw ht, mul_one]

/-- `ekern M w (-s) = conj (ekern M w s)`. -/
lemma ekern_neg_right (M w s : GaussianInt) : ekern M w (-s) = star (ekern M w s) := by
  have hg : gdot (-s) w = gdot s (-w) := by
    simp only [gdot, Zsqrtd.re_neg, Zsqrtd.im_neg]
    ring
  rw [star_ekern, ekern, ekern, hg]

/-- `ekern M w` is multiplicative in the difference of its arguments. -/
lemma ekern_sub (M w s t : GaussianInt) :
    ekern M w (s - t) = ekern M w s * star (ekern M w t) := by
  rw [sub_eq_add_neg, ekern_add_right, ekern_neg_right]

/-! ## Periodicity of a character mod `M` -/

/-- A character mod `M` is `N`-periodic for `N = gnorm M`. -/
lemma chi_add_gnorm (M : GaussianInt) (chi : GaussianInt → ℂ) (hchi : IsCharModStrict M chi)
    (z x : GaussianInt) :
    chi (x + ((Work.FIPlan.gnorm M : ℕ) : GaussianInt) * z) = chi x := by
  refine hchi.2.2.2.1 _ _ ?_
  have h : x + ((Work.FIPlan.gnorm M : ℕ) : GaussianInt) * z - x
      = ((Work.FIPlan.gnorm M : ℕ) : GaussianInt) * z := by ring
  rw [h]
  exact dvd_mul_of_dvd_left (dvd_gnorm M) z

/-- A character mod `M` is invariant under adding multiples of `M`. -/
lemma chi_add_of_dvd (M : GaussianInt) (chi : GaussianInt → ℂ) (hchi : IsCharModStrict M chi)
    {x t : GaussianInt} (ht : M ∣ t) : chi (x + t) = chi x := by
  refine hchi.2.2.2.1 _ _ ?_
  have h : x + t - x = t := by ring
  rw [h]; exact ht

end

end Work.FIArea6Hecke.R2
