/-
# `Submission.Work.FIArea7.FIsymbols` — the symbols of *FI* §§19–20

Area 7 of the Friedlander–Iwaniec contract (`Work.FITop3.Area7`, *FI* §§17, 19–26) needs two
arithmetic symbols attached to Gaussian integers, neither of which is in Mathlib:

* **the Dirichlet symbol** `ξ_w(z) = (z/w)` of §19, defined for `w` primary primitive by
  (19.10)/(19.11) as the Jacobi symbol of the rational residue `Re(wz)` modulo `|w|²`;
* **the Jacobi–Kubota symbol** `[z]` of §20, `(20.1)`, `[z] = i^{(r-1)/2}(s/|r|)` for `z = r + is`.

This file *defines* them (as `DirichletSym`, `JKCoeff`, `JKSym`) together with the coefficient
`β'_z = [z]β_z` of (17.8)/(17.14), and proves the immediate algebraic facts (multiplicativity in
the lower entry of the Jacobi symbol, the `±1`-bounds, and the trivial reciprocity
`ξ_w(z)ξ_z(w) = (Re(wz) | |w|²|z|²)` whose vanishing-free case is (19.12)).  The substantive laws —
(19.8), the multiplicativity (19.2)/(19.15) and the multiplier rule (20.3)/(20.4) — are separate
lemmas (delegated).

Notation: `z.re = r`, `z.im = s`; `gnorm z = |z|²` (`Work.FIPlan.gnorm`).
-/
import Mathlib
import Submission.Work.FIPlan.Interface

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Coordinates of a Gaussian integer -/

/-- `Re(w z) = w.re * z.re + (-1) * w.im * z.im`. -/
lemma re_mul (w z : GaussianInt) : (w * z).re = w.re * z.re - w.im * z.im := by
  rw [Zsqrtd.re_mul]; ring

/-- `Im(w z) = w.re * z.im + w.im * z.re`. -/
lemma im_mul (w z : GaussianInt) : (w * z).im = w.re * z.im + w.im * z.re := by
  rw [Zsqrtd.im_mul]

/-- `|wz|² = |w|²|z|²`. -/
lemma gnorm_mul (w z : GaussianInt) :
    Work.FIPlan.gnorm (w * z) = Work.FIPlan.gnorm w * Work.FIPlan.gnorm z := by
  simp [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- `|z|² = r² + s²` as an integer. -/
lemma norm_eq (z : GaussianInt) : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := by
  have h : Zsqrtd.norm z = z.re * z.re + z.im * z.im := by rw [Zsqrtd.norm_def]; ring
  have hnn : 0 ≤ Zsqrtd.norm z := by rw [h]; nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  show ((Zsqrtd.norm z).natAbs : ℤ) = _
  rw [Int.natAbs_of_nonneg hnn, h]
  ring

/-- `|z|² = 0` only for `z = 0`. -/
lemma gnorm_eq_zero_iff {z : GaussianInt} : Work.FIPlan.gnorm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h2 : (Work.FIPlan.gnorm z : ℤ) = 0 := by simp [h]
    rw [norm_eq] at h2
    have hr : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    have hi : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    exact Zsqrtd.ext hr hi
  · rintro rfl; simp [Work.FIPlan.gnorm]

/-- `|z|² > 0` for `z ≠ 0`. -/
lemma gnorm_pos_of_ne_zero {z : GaussianInt} (h : z ≠ 0) : 0 < Work.FIPlan.gnorm z :=
  Nat.pos_of_ne_zero fun h0 => h (gnorm_eq_zero_iff.mp h0)

/-! ## 2. The Dirichlet symbol `ξ_w(z) = (z/w)` of §19

*FI* (19.9)–(19.11): for `w = u + iv` primary and primitive and `z = r + is`,
`ξ_w(z) = (ur - vs)/q)` with `q = |w|² = u² + v²`; equivalently `ξ_w(z) = (Re(wz) | |w|²)`
(that equality is the content of (19.8), proved separately).  We take the latter as the
definition, since it needs no choice of `ω`. -/

/-- **The Dirichlet symbol** (19.10)/(19.11): `ξ_w(z) = (Re(wz) | |w|²)`. -/
def DirichletSym (w z : GaussianInt) : ℤ := jacobiSym (w * z).re (Work.FIPlan.gnorm w)

/-- Unfolding lemma (definitional). -/
lemma dirichletSym_def (w z : GaussianInt) :
    DirichletSym w z = jacobiSym (w * z).re (Work.FIPlan.gnorm w) := rfl

/-- `ξ_w(1) = (Re w | |w|²)`. -/
lemma dirichletSym_one (w : GaussianInt) :
    DirichletSym w 1 = jacobiSym w.re (Work.FIPlan.gnorm w) := by
  simp [DirichletSym]

/-- Rational argument: `ξ_w(n) = (n·Re w | |w|²)`. -/
lemma dirichletSym_int (w : GaussianInt) (n : ℤ) :
    DirichletSym w (n : GaussianInt) = jacobiSym (n * w.re) (Work.FIPlan.gnorm w) := by
  rw [DirichletSym, re_mul]
  simp only [Zsqrtd.re_intCast, Zsqrtd.im_intCast, mul_zero, sub_zero]
  congr 1
  ring

/-- (19.3): on rational integers `ξ_w` is the Jacobi symbol of the rational character, times the
normalising factor `ξ_w(1) = (Re w | |w|²)` (which is `1` for primary primitive `w`, by (19.8)). -/
lemma dirichletSym_int_eq (w : GaussianInt) (n : ℤ) :
    DirichletSym w (n : GaussianInt)
      = jacobiSym w.re (Work.FIPlan.gnorm w) * jacobiSym n (Work.FIPlan.gnorm w) := by
  rw [dirichletSym_int, jacobiSym.mul_left, mul_comm]

/-- `|ξ_w(z)| ≤ 1`. -/
lemma abs_dirichletSym_le_one (w z : GaussianInt) : |DirichletSym w z| ≤ 1 := by
  rw [DirichletSym]
  rcases jacobiSym.trichotomy (w * z).re (Work.FIPlan.gnorm w) with h | h | h <;> rw [h] <;> norm_num

/-- **(19.12), symmetric form.**  `ξ_w(z)ξ_z(w) = (Re(wz) | |w|²|z|²)`; by (19.8) applied to
`wz` the right-hand side is `1` whenever `wz` is primitive (that is (19.12) itself). -/
lemma dirichletSym_mul_swap {w z : GaussianInt} (hw : Work.FIPlan.gnorm w ≠ 0)
    (hz : Work.FIPlan.gnorm z ≠ 0) :
    DirichletSym w z * DirichletSym z w
      = jacobiSym (w * z).re (Work.FIPlan.gnorm w * Work.FIPlan.gnorm z) := by
  haveI : NeZero (Work.FIPlan.gnorm w) := ⟨hw⟩
  haveI : NeZero (Work.FIPlan.gnorm z) := ⟨hz⟩
  rw [DirichletSym, DirichletSym]
  rw [show jacobiSym (z * w).re (Work.FIPlan.gnorm z) = jacobiSym (w * z).re (Work.FIPlan.gnorm z)
      from by rw [mul_comm z w]]
  rw [← jacobiSym.mul_right, ← gnorm_mul]

/-! ## 3. The Jacobi–Kubota symbol `[z]` of §20 -/

/-- The rational factor `(s/|r|)` of the Jacobi–Kubota symbol (20.1), as a complex number. -/
def JKCoeff (z : GaussianInt) : ℂ := (jacobiSym z.im z.re.natAbs : ℂ)

/-- **The Jacobi–Kubota symbol** (20.1): `[z] = i^{(r-1)/2}(s/|r|)` for `z = r + is`.  It vanishes
unless `z` is primitive (then `(r,s) = 1` and the Jacobi symbol of `s` against `|r|` is `0` only
if `r` and `s` share a factor). -/
def JKSym (z : GaussianInt) : ℂ := Complex.I ^ ((z.re - 1) / 2 : ℤ) * JKCoeff z

/-- Unfolding lemma (definitional). -/
lemma JKSym_def (z : GaussianInt) :
    JKSym z = Complex.I ^ ((z.re - 1) / 2 : ℤ) * JKCoeff z := rfl

/-- `‖[z]‖ ≤ 1`. -/
lemma norm_JKSym_le_one (z : GaussianInt) : ‖JKSym z‖ ≤ 1 := by
  rw [JKSym, norm_mul]
  have h1 : ‖Complex.I ^ ((z.re - 1) / 2 : ℤ)‖ = 1 := by
    rw [norm_zpow]; simp
  have h2 : ‖JKCoeff z‖ ≤ 1 := by
    rw [JKCoeff, Complex.norm_intCast]
    rcases jacobiSym.trichotomy z.im z.re.natAbs with h | h | h <;> simp [h]
  rw [h1, one_mul]; exact h2


/-- **(17.7), the Hilbert symbol at ∞**: `(x,y)_∞ = -1` iff both `x` and `y` are negative. -/
def HilbertInf (x y : ℤ) : ℤ := if x < 0 ∧ y < 0 then -1 else 1

/-- **The sign `ε(w,z)` of the multiplier rule** (20.5)/(20.6), written for `w = u + iv`,
`z = r + is` as `ε = (u,v)_∞(r,−v)_∞` if `ur > vs` and `ε = (u,v)_∞(−r,v)_∞` if `ur < vs`.
(`ur = vs` cannot occur for `w, z ≡ 1 (mod 2)`: `Re(wz) = ur − vs` is odd.) -/
def MultEps (w z : GaussianInt) : ℤ :=
  if w.re * z.re > w.im * z.im then HilbertInf w.re w.im * HilbertInf z.re (-w.im)
  else HilbertInf w.re w.im * HilbertInf (-z.re) w.im

/-- `ε` takes the values `±1`. -/
lemma multEps_eq_pm_one (w z : GaussianInt) : MultEps w z = 1 ∨ MultEps w z = -1 := by
  unfold MultEps HilbertInf
  split_ifs <;> simp

/-- **(17.8)/(17.14): the twisted coefficient** `β'_z = [z]β_z`. -/
def betaPrime (β : GaussianInt → ℂ) (z : GaussianInt) : ℂ := JKSym z * β z

/-- `‖β'_z‖ ≤ ‖β_z‖`. -/
lemma norm_betaPrime_le (β : GaussianInt → ℂ) (z : GaussianInt) :
    ‖betaPrime β z‖ ≤ ‖β z‖ := by
  rw [betaPrime, norm_mul]
  calc ‖JKSym z‖ * ‖β z‖ ≤ 1 * ‖β z‖ :=
        mul_le_mul_of_nonneg_right (norm_JKSym_le_one z) (norm_nonneg _)
    _ = ‖β z‖ := one_mul _

end

end Work.FIArea7
