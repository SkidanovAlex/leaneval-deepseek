/-
# `GaussBasic`: the finite ring `ℤ[i]/(4d)` and its Gauss-sum data.

This file sets up the concrete model `(ZMod (4d))²` of the Gaussian residue ring `ℤ[i]/(4d)`
(the product being given the Gaussian multiplication `gmul`), the residue class map
`gOfZI : ℤ[i] → (ZMod (4d))²` and the canonical representative map `zOfG`, together with the
elementary algebra needed to transfer multiplication and conjugation of `ℤ[i]` to the residue
ring, and the parity description of oddness in `ℤ[i]`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators

noncomputable section

/-- Gaussian multiplication on `(ZMod (4d))²`, modelling the ring `ℤ[i]/(4d)`. -/
def gmul (d : ℕ) (x y : ZMod (4 * d) × ZMod (4 * d)) : ZMod (4 * d) × ZMod (4 * d) :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- The unit `1` of the Gaussian residue ring. -/
def gone (d : ℕ) : ZMod (4 * d) × ZMod (4 * d) := (1, 0)

/-- Gaussian conjugation in the residue ring. -/
def gconj (d : ℕ) (x : ZMod (4 * d) × ZMod (4 * d)) : ZMod (4 * d) × ZMod (4 * d) :=
  (x.1, -x.2)

/-- The norm form `x·x̄`, a scalar (i.e. in the "real" coordinate). -/
def gsq (d : ℕ) (x : ZMod (4 * d) × ZMod (4 * d)) : ZMod (4 * d) := x.1 ^ 2 + x.2 ^ 2

/-- The dot product pairing `Re(x·ξ̄)` of two residue classes. -/
def pairG (d : ℕ) (θ x : ZMod (4 * d) × ZMod (4 * d)) : ZMod (4 * d) :=
  x.1 * θ.1 + x.2 * θ.2

/-- The residue-class map `ℤ[i] → (ZMod (4d))²`. -/
def gOfZI (d : ℕ) (z : GaussianInt) : ZMod (4 * d) × ZMod (4 * d) :=
  ((z.re : ZMod (4 * d)), (z.im : ZMod (4 * d)))

/-- The canonical Gaussian-integer representative of a residue class. -/
def zOfG (d : ℕ) (x : ZMod (4 * d) × ZMod (4 * d)) : GaussianInt :=
  ⟨(x.1.val : ℤ), (x.2.val : ℤ)⟩

/-- A residue class is a unit of the Gaussian residue ring. -/
def IsUnitR (d : ℕ) (x : ZMod (4 * d) × ZMod (4 * d)) : Prop := ∃ y, gmul d x y = gone d

/-- Oddness of the canonical representative of a residue class. -/
def isOddR (d : ℕ) (x : ZMod (4 * d) × ZMod (4 * d)) : Prop := isOddG (zOfG d x)

/-- The character `χ` evaluated on the canonical representative of a residue class. -/
def chiR (d : ℕ) (chi : GaussianInt → ℂ) (x : ZMod (4 * d) × ZMod (4 * d)) : ℂ :=
  chi (zOfG d x)

/-- The periodic weight `χ·1_odd` on the residue ring, the function whose finite Fourier
transform is the Gauss sum `gaussSum d χ`. -/
def FR (d : ℕ) (chi : GaussianInt → ℂ) (x : ZMod (4 * d) × ZMod (4 * d)) : ℂ := by
  classical
  exact if isOddR d x then chiR d chi x else 0

/-- The finite Fourier transform of `FR`, evaluated at `θ`:
`Fhat d χ θ = Σ_x FR x · e^{2πi Re(x θ̄)/(4d)}`. -/
def Fhat (d : ℕ) [NeZero (4 * d)] (chi : GaussianInt → ℂ)
    (θ : ZMod (4 * d) × ZMod (4 * d)) : ℂ :=
  ∑ x : ZMod (4 * d) × ZMod (4 * d), FR d chi x * ZMod.stdAddChar (pairG d θ x)

namespace GaussBasic

variable {d : ℕ} [NeZero (4 * d)]

/-! ## Parity in `ℤ[i]` -/

lemma oneAddI_eq : oneAddI = (⟨1,1⟩ : GaussianInt) := by ext <;> simp [oneAddI]

lemma odd_sub_two_mul_iff (x y : ℤ) : Odd (x - 2*y) ↔ Odd x := by
  rw [Int.odd_iff, Int.odd_iff]; omega

lemma odd_mul_iff (a b : ℤ) : Odd (a*b) ↔ Odd a ∧ Odd b := by
  constructor
  · intro h
    have h' : ¬ Even (a*b) := (Int.not_even_iff_odd).mpr h
    exact ⟨(Int.not_even_iff_odd).mp (fun ha => h' (ha.mul_right b)),
           (Int.not_even_iff_odd).mp (fun hb => h' (hb.mul_left a))⟩
  · rintro ⟨ha,hb⟩; exact ha.mul hb

lemma odd_add_even_iff {x c : ℤ} (h : Even c) : Odd (x + c) ↔ Odd x := by
  constructor
  · intro hh; simpa using (show Odd (x + c - c) from hh.sub_even h)
  · intro hh; simpa using hh.add_even h

lemma dvd_oneAddI_iff_even (z : GaussianInt) : oneAddI ∣ z ↔ Even (z.re + z.im) := by
  rw [oneAddI_eq]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨w.re, ?_⟩
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    ring
  · rintro ⟨k, hk⟩
    refine ⟨⟨k, z.im - k⟩, ?_⟩
    ext
    · simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
      linarith
    · simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
      ring

lemma isOddG_iff_odd (z : GaussianInt) : isOddG z ↔ Odd (z.re + z.im) := by
  rw [isOddG, dvd_oneAddI_iff_even]
  exact Int.not_even_iff_odd

lemma isOddG_one : isOddG (1 : GaussianInt) := by
  rw [isOddG_iff_odd]; norm_num

@[simp] lemma isOddG_natCast (n : ℕ) : isOddG (n : GaussianInt) ↔ Odd n := by
  rw [isOddG_iff_odd]; simp

@[simp] lemma isOddG_intCast (n : ℤ) : isOddG (n : GaussianInt) ↔ Odd n := by
  rw [isOddG_iff_odd]; simp

lemma isOddG_mul (z w : GaussianInt) : isOddG (z*w) ↔ isOddG z ∧ isOddG w := by
  have h : (z*w).re + (z*w).im = (z.re + z.im)*(w.re + w.im) - 2*(z.im*w.im) := by
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]; ring
  rw [isOddG_iff_odd, isOddG_iff_odd, isOddG_iff_odd, h, odd_sub_two_mul_iff, odd_mul_iff]

lemma isOddG_star (z : GaussianInt) : isOddG (star z) ↔ isOddG z := by
  have h : (star z).re + (star z).im = (z.re + z.im) - 2*z.im := by
    simp only [Zsqrtd.re_star, Zsqrtd.im_star]; ring
  rw [isOddG_iff_odd, isOddG_iff_odd, h, odd_sub_two_mul_iff]

/-- Oddness depends only on the residue class modulo `4d`. -/
lemma isOddG_periodic {z w : GaussianInt}
    (h : ((((4*d:ℕ):ℤ)) : GaussianInt) ∣ (z - w)) : isOddG z ↔ isOddG w := by
  obtain ⟨u, hu⟩ := h
  have hre : z.re - w.re = ((4*d:ℕ):ℤ) * u.re := by
    have := congrArg Zsqrtd.re hu; simpa [Zsqrtd.re_mul] using this
  have him : z.im - w.im = ((4*d:ℕ):ℤ) * u.im := by
    have := congrArg Zsqrtd.im hu; simpa [Zsqrtd.im_mul] using this
  rw [isOddG_iff_odd, isOddG_iff_odd]
  have he : Even (((4*d:ℕ):ℤ) * (u.re + u.im)) := by
    refine ⟨2*(d:ℤ)*(u.re+u.im), ?_⟩
    push_cast; ring
  have hz : z.re + z.im = (w.re + w.im) + ((4*d:ℕ):ℤ)*(u.re+u.im) := by linarith
  rw [hz]
  exact odd_add_even_iff he

/-! ## The residue ring `ℤ[i]/(4d)` -/

@[simp] lemma gmul_fst (x y : ZMod (4 * d) × ZMod (4 * d)) :
    (gmul d x y).1 = x.1 * y.1 - x.2 * y.2 := rfl

@[simp] lemma gmul_snd (x y : ZMod (4 * d) × ZMod (4 * d)) :
    (gmul d x y).2 = x.1 * y.2 + x.2 * y.1 := rfl

@[simp] lemma gone_fst : (gone d).1 = 1 := rfl

@[simp] lemma gone_snd : (gone d).2 = 0 := rfl

@[simp] lemma gconj_fst (x : ZMod (4 * d) × ZMod (4 * d)) : (gconj d x).1 = x.1 := rfl

@[simp] lemma gconj_snd (x : ZMod (4 * d) × ZMod (4 * d)) : (gconj d x).2 = -x.2 := rfl

@[simp] lemma gOfZI_re (z : GaussianInt) : (gOfZI d z).1 = (z.re : ZMod (4 * d)) := rfl
@[simp] lemma gOfZI_im (z : GaussianInt) : (gOfZI d z).2 = (z.im : ZMod (4 * d)) := rfl
@[simp] lemma zOfG_re (x : ZMod (4 * d) × ZMod (4 * d)) : (zOfG d x).re = (x.1.val : ℤ) := rfl
@[simp] lemma zOfG_im (x : ZMod (4 * d) × ZMod (4 * d)) : (zOfG d x).im = (x.2.val : ℤ) := rfl

lemma gmul_comm (x y : ZMod (4 * d) × ZMod (4 * d)) : gmul d x y = gmul d y x := by
  ext <;> simp [gmul] <;> ring

lemma gmul_assoc (x y z : ZMod (4 * d) × ZMod (4 * d)) :
    gmul d (gmul d x y) z = gmul d x (gmul d y z) := by
  ext <;> simp [gmul] <;> ring

lemma gmul_gone_left (x : ZMod (4 * d) × ZMod (4 * d)) : gmul d (gone d) x = x := by
  ext <;> simp [gmul, gone]

lemma gmul_gone_right (x : ZMod (4 * d) × ZMod (4 * d)) : gmul d x (gone d) = x := by
  ext <;> simp [gmul, gone]

@[simp] lemma gconj_gone : gconj d (gone d) = gone d := by ext <;> simp [gconj, gone]

@[simp] lemma gconj_gconj (x : ZMod (4 * d) × ZMod (4 * d)) : gconj d (gconj d x) = x := by
  ext <;> simp [gconj]

lemma gconj_gmul (x y : ZMod (4 * d) × ZMod (4 * d)) :
    gconj d (gmul d x y) = gmul d (gconj d x) (gconj d y) := by
  ext <;> simp [gmul, gconj] <;> ring

@[simp] lemma gmul_gconj (x : ZMod (4 * d) × ZMod (4 * d)) :
    gmul d x (gconj d x) = (gsq d x, 0) := by
  ext <;> simp [gmul, gconj, gsq] <;> ring

lemma pairG_eq_fst_gmul (θ x : ZMod (4 * d) × ZMod (4 * d)) :
    pairG d θ x = (gmul d x (gconj d θ)).1 := by
  simp [pairG, gmul, gconj]

@[simp] lemma gOfZI_mul (z w : GaussianInt) :
    gOfZI d (z * w) = gmul d (gOfZI d z) (gOfZI d w) := by
  ext <;> simp [gOfZI, gmul] <;> push_cast <;> ring

@[simp] lemma gOfZI_one : gOfZI d (1 : GaussianInt) = gone d := by
  ext <;> simp [gOfZI, gone]

@[simp] lemma gOfZI_zero : gOfZI d (0 : GaussianInt) = (0, 0) := by
  ext <;> simp [gOfZI]

lemma gOfZI_zOfG (x : ZMod (4 * d) × ZMod (4 * d)) : gOfZI d (zOfG d x) = x := by
  ext <;> simp [gOfZI, zOfG, ZMod.natCast_zmod_val]

/-- `gOfZI` is injective modulo `4d`: equal residue classes differ by a multiple of `4d`. -/
lemma dvd_of_gOfZI_eq {z w : GaussianInt} (h : gOfZI d z = gOfZI d w) :
    ((((4*d:ℕ):ℤ)) : GaussianInt) ∣ (z - w) := by
  have hre : (z.re : ZMod (4*d)) = (w.re : ZMod (4*d)) := by
    have := congrArg Prod.fst h; simpa [gOfZI] using this
  have him : (z.im : ZMod (4*d)) = (w.im : ZMod (4*d)) := by
    have := congrArg Prod.snd h; simpa [gOfZI] using this
  have h1 : ((4*d:ℕ):ℤ) ∣ z.re - w.re :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub w.re z.re (4*d)).mp hre.symm
  have h2 : ((4*d:ℕ):ℤ) ∣ z.im - w.im :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub w.im z.im (4*d)).mp him.symm
  rw [Zsqrtd.intCast_dvd]
  exact ⟨h1, h2⟩

/-- Conversely, `gOfZI` only depends on the class modulo `4d`. -/
lemma gOfZI_eq_of_dvd {z w : GaussianInt}
    (h : ((((4*d:ℕ):ℤ)) : GaussianInt) ∣ (z - w)) : gOfZI d z = gOfZI d w := by
  rw [Zsqrtd.intCast_dvd] at h
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub] at h
  obtain ⟨h1, h2⟩ := h
  ext
  · simp only [gOfZI_re]
    exact ((ZMod.intCast_eq_intCast_iff_dvd_sub w.re z.re (4*d)).mpr h1).symm
  · simp only [gOfZI_im]
    exact ((ZMod.intCast_eq_intCast_iff_dvd_sub w.im z.im (4*d)).mpr h2).symm

lemma IsUnitR.conj {x : ZMod (4 * d) × ZMod (4 * d)} (h : IsUnitR d x) :
    IsUnitR d (gconj d x) := by
  obtain ⟨y, hy⟩ := h
  refine ⟨gconj d y, ?_⟩
  have := congrArg (gconj d) hy
  simpa [gconj_gmul, gconj_gone] using this

lemma IsUnitR.mul {x y : ZMod (4 * d) × ZMod (4 * d)} (hx : IsUnitR d x) (hy : IsUnitR d y) :
    IsUnitR d (gmul d x y) := by
  obtain ⟨x', hx'⟩ := hx
  obtain ⟨y', hy'⟩ := hy
  refine ⟨gmul d y' x', ?_⟩
  rw [gmul_assoc, ← gmul_assoc y y' x', hy', gmul_gone_left, hx']

lemma IsUnitR.of_mul_right {x u : ZMod (4 * d) × ZMod (4 * d)}
    (h : IsUnitR d (gmul d x u)) : IsUnitR d x := by
  obtain ⟨v, hv⟩ := h
  exact ⟨gmul d u v, by rw [← gmul_assoc]; exact hv⟩

lemma isUnitR_mul_right {x u : ZMod (4 * d) × ZMod (4 * d)} (hu : IsUnitR d u) :
    IsUnitR d (gmul d x u) ↔ IsUnitR d x :=
  ⟨IsUnitR.of_mul_right, fun h => IsUnitR.mul h hu⟩

end GaussBasic

end

end Work.FIArea5.S16Hecke
