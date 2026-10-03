/-
# The vocabulary of the §6 Poisson step (6.7) → (6.9), in the form needed by the final assembly

`Work.FIArea2.sum_gBox_eq_sum_congruences` (6.7) rewrites the `w`-sum of (5.27) as a sum over the
parametrising pairs `p = (c₁,c₂) ∈ ℤ²` with `Δ ∣ c₁²z₂ − c₂²z₁` of `F(|w|²)`, `w = wOf z₁ z₂ c₁ c₂`.
The Poisson step (6.8)–(6.11) then

* replaces the pair `(c₁,c₂)` by the value at the lattice point `(c₁,c₂)` of the *smooth* phase
  `Ψ(t) = F(|t₁²z₂ − t₂²z₁|²/|Δ|²)` (`PsiC`, `phiOf`),
* restricts to the admissible lattice points (`Adm`: the congruence (6.4) componentwise),
* splits the lattice into classes modulo `m = |Δ|` (`cosetVec`, `cosetPt`),
* and sums the class `(γ₁,γ₂)` by Poisson summation.

This file fixes the objects of that decomposition so that the individual steps can be stated
separately: the Gaussian integer `Xof z₁ z₂ p = c₁²z₂ − c₂²z₁` whose `Δ`-divisibility is the
admissibility of `p` (`Adm`, with `Adm_iff_dvd`), the complex lattice phase `PsiC` and the
admissibility-restricted lattice function `Gh`, the coset map `cosetVec` on `ℤ²` (the integral
companion of `Work.FIArea2.cosetPt`), and the truncation height `Kpar` with its box `Kbox`, which
is the `K` (and `S`) of (6.7) for the box `boxM Pa` of (4.18).
-/
import Mathlib
import Submission.Work.FIArea2.SmoothSec6Defs
import Submission.Work.FIArea2.sec6_change_of_variables
import Submission.Work.FIArea2.poisson_coset_2d
import Submission.Work.FIArea2.sum_gBox_eq_sum_congruences
import Submission.Work.FIArea2.gnorm_wOf
import Submission.Work.FIArea2.G8Defs
import Submission.Work.FIArea2.hits_card_le

set_option autoImplicit false

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The congruence of (6.4)/(6.5) and the admissibility of a lattice point -/

/-- `Xof z₁ z₂ p = c₁²z₂ − c₂²z₁` for `p = (c₁,c₂)`: the Gaussian integer whose `Δ`-divisibility is
the congruence (6.4)/(6.5) of the re-parametrisation (6.7). -/
def Xof (z1 z2 : GaussianInt) (p : ℤ × ℤ) : GaussianInt :=
  ((p.1 ^ 2 : ℤ) : GaussianInt) * z2 - ((p.2 ^ 2 : ℤ) : GaussianInt) * z1

/-- **The admissibility of a lattice point** (6.4)/(6.5): the class of `p = (c₁,c₂)` modulo
`m = |Δ|` satisfies `c₁²z₂ ≡ c₂²z₁ (mod |Δ|)`, i.e. `|Δ|` divides both coordinates of
`Xof z₁ z₂ p`.  These are exactly the classes summed by the arithmetic sum `Gsum` of (6.10). -/
def Adm (z1 z2 : GaussianInt) (p : ℤ × ℤ) : Prop :=
  (Work.FIPlan.absDelta z1 z2 : ℤ) ∣ (Xof z1 z2 p).re ∧
    (Work.FIPlan.absDelta z1 z2 : ℤ) ∣ (Xof z1 z2 p).im

/-- The two forms of `Xof`: as a product with a rational integer cast, and as the square of `p.1`
(these are the forms in which (6.3)/(6.4) and `Work.FIArea2.exists_cForm_eq_iff` state it). -/
lemma Xof_eq (z1 z2 : GaussianInt) (p : ℤ × ℤ) :
    Xof z1 z2 p = (p.1 : GaussianInt) ^ 2 * z2 - (p.2 : GaussianInt) ^ 2 * z1 := by
  rw [Xof]
  push_cast
  ring

lemma Xof_re (z1 z2 : GaussianInt) (p : ℤ × ℤ) :
    (Xof z1 z2 p).re = p.1 ^ 2 * z2.re - p.2 ^ 2 * z1.re := by
  simp only [Xof, Zsqrtd.re_sub, Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
  ring

lemma Xof_im (z1 z2 : GaussianInt) (p : ℤ × ℤ) :
    (Xof z1 z2 p).im = p.1 ^ 2 * z2.im - p.2 ^ 2 * z1.im := by
  simp only [Xof, Zsqrtd.im_sub, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
  ring

/-! ## 2. The lattice phase and the admissibility-restricted lattice function -/

/-- The smooth lattice phase of (6.7), complex valued: `Ψ(t) = F(|t₁²z₂ − t₂²z₁|²/|Δ|²)`. -/
def PsiC (F : ℝ → ℝ) (z1 z2 : GaussianInt) (t : ℝ × ℝ) : ℂ := ((phiOf F z1 z2 t : ℝ) : ℂ)

lemma PsiC_apply (F : ℝ → ℝ) (z1 z2 : GaussianInt) (t : ℝ × ℝ) :
    PsiC F z1 z2 t = ((F (gphase z1 z2 t) : ℝ) : ℂ) := by
  rw [PsiC, phiOf_eq_gphase]

/-- The lattice function of the Poisson step: `Ψ` on the admissible points of `ℤ²`, `0` elsewhere. -/
def Gh (F : ℝ → ℝ) (z1 z2 : GaussianInt) (p : ℤ × ℤ) : ℂ :=
  if Adm z1 z2 p then PsiC F z1 z2 ((p.1 : ℝ), (p.2 : ℝ)) else 0

lemma Gh_of_adm {F : ℝ → ℝ} {z1 z2 : GaussianInt} {p : ℤ × ℤ} (h : Adm z1 z2 p) :
    Gh F z1 z2 p = PsiC F z1 z2 ((p.1 : ℝ), (p.2 : ℝ)) := by
  rw [Gh, if_pos h]

lemma Gh_of_not_adm {F : ℝ → ℝ} {z1 z2 : GaussianInt} {p : ℤ × ℤ} (h : ¬ Adm z1 z2 p) :
    Gh F z1 z2 p = 0 := by
  rw [Gh, if_neg h]

/-! ## 3. The coset map and the truncation box of (6.7) -/

/-- The integral coset point `(γ₁ + m c₁, γ₂ + m c₂) ∈ ℤ²`.  Its image in `ℝ²` is
`Work.FIArea2.cosetPt m (γ₁,γ₂) c`. -/
def cosetVec (m : ℕ) (γ : ℕ × ℕ) (c : ℤ × ℤ) : ℤ × ℤ :=
  ((γ.1 : ℤ) + (m : ℤ) * c.1, (γ.2 : ℤ) + (m : ℤ) * c.2)

lemma cosetPt_eq_cosetVec (m : ℕ) (γ : ℕ × ℕ) (c : ℤ × ℤ) :
    cosetPt m ((γ.1 : ℤ), (γ.2 : ℤ)) c
      = (((cosetVec m γ c).1 : ℝ), ((cosetVec m γ c).2 : ℝ)) := by
  simp [cosetPt, cosetVec]

/-- The truncation height of (6.7): `|c| ≤ Kpar` for every square `c² = Re(wz)` with `w` in the
box `boxM Pa` and `z ∈ {z₁,z₂}` — see `Work.FIArea2.Kpar_bound`. -/
def Kpar (Pa : Work.FITop.Params) (z1 z2 : GaussianInt) : ℕ :=
  ⌈Real.sqrt (((Work.FITop.radM Pa : ℤ) : ℝ)
    * (|(z1.re : ℝ)| + |(z1.im : ℝ)| + |(z2.re : ℝ)| + |(z2.im : ℝ)| + 1))⌉₊

/-- The truncated box `[-K,K]² ⊂ ℤ²` of (6.7), with `K = Kpar Pa z₁ z₂`. -/
def Kbox (Pa : Work.FITop.Params) (z1 z2 : GaussianInt) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(Kpar Pa z1 z2 : ℤ)) (Kpar Pa z1 z2 : ℤ)
    ×ˢ Finset.Icc (-(Kpar Pa z1 z2 : ℤ)) (Kpar Pa z1 z2 : ℤ)

/-! ## 4. The exponential factor of the class sums -/

/-- The exponential factor `e((γ₁h₁ + γ₂h₂)/m)` of the class sums (6.10). -/
def eGam (m : ℕ) (γ : ℕ × ℕ) (h1 h2 : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I
    * (((γ.1 : ℤ) * h1 + (γ.2 : ℤ) * h2 : ℤ) : ℝ) / (m : ℝ))


/-- The class of `p` modulo `m`: the coordinates `p_j mod m` read as natural numbers in `[0,m)`. -/
def qVec (m : ℕ) (p : ℤ × ℤ) : ℕ × ℕ :=
  ((p.1 % (m : ℤ)).toNat, (p.2 % (m : ℤ)).toNat)

/-- The quotient of `p` by `m` (Euclidean division, coordinatewise). -/
def cVec (m : ℕ) (p : ℤ × ℤ) : ℤ × ℤ := (p.1 / (m : ℤ), p.2 / (m : ℤ))

/-- **Euclidean division on `ℤ²`**: `p = qVec m p + m · cVec m p`. -/
lemma cosetVec_qVec_cVec {m : ℕ} (hm : 0 < m) (p : ℤ × ℤ) :
    cosetVec m (qVec m p) (cVec m p) = p := by
  have hm' : ((m : ℤ)) ≠ 0 := by exact_mod_cast hm.ne'
  have h1 : ((p.1 % (m : ℤ)).toNat : ℤ) = p.1 % (m : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hm')
  have h2 : ((p.2 % (m : ℤ)).toNat : ℤ) = p.2 % (m : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hm')
  ext
  · simp only [cosetVec, qVec, cVec, Prod.mk.eta]
    rw [h1]
    linarith [Int.emod_add_mul_ediv p.1 (m : ℤ)]
  · simp only [cosetVec, qVec, cVec, Prod.mk.eta]
    rw [h2]
    linarith [Int.emod_add_mul_ediv p.2 (m : ℤ)]

/-- The class `qVec m p` is a vector of residues in `range m`. -/
lemma qVec_mem {m : ℕ} (hm : 0 < m) (p : ℤ × ℤ) :
    qVec m p ∈ Finset.range m ×ˢ Finset.range m := by
  have hm' : ((m : ℤ)) ≠ 0 := by exact_mod_cast hm.ne'
  have h1 : p.1 % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  have h2 : p.2 % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  have h1' : (p.1 % (m : ℤ)).toNat < m := by omega
  have h2' : (p.2 % (m : ℤ)).toNat < m := by omega
  simp only [qVec, Finset.mem_product, Finset.mem_range]
  exact ⟨h1', h2'⟩

/-- **The admissibility is constant on the cosets modulo `|Δ|`**: adding a multiple of `|Δ|` to a
lattice point changes `Xof` by a multiple of `|Δ|` in both coordinates, so the congruence (6.4)
is a condition on the class alone. -/
lemma Adm_cosetVec (z1 z2 : GaussianInt) (g : ℕ × ℕ) (c : ℤ × ℤ) :
    Adm z1 z2 (cosetVec (Work.FIPlan.absDelta z1 z2) g c)
      ↔ Adm z1 z2 (((g.1 : ℤ)), ((g.2 : ℤ))) := by
  have hre : ∀ (gg : ℕ × ℕ) (cc : ℤ × ℤ),
      (Xof z1 z2 (cosetVec (Work.FIPlan.absDelta z1 z2) gg cc)).re
        = (Xof z1 z2 (((gg.1 : ℤ)), ((gg.2 : ℤ)))).re
          + ((Work.FIPlan.absDelta z1 z2 : ℤ))
            * (2 * (gg.1 : ℤ) * cc.1 * z2.re
              + ((Work.FIPlan.absDelta z1 z2 : ℤ)) * cc.1 ^ 2 * z2.re
              - 2 * (gg.2 : ℤ) * cc.2 * z1.re
              - ((Work.FIPlan.absDelta z1 z2 : ℤ)) * cc.2 ^ 2 * z1.re) := by
    intro gg cc
    simp only [Xof_re, cosetVec]
    ring
  have him : ∀ (gg : ℕ × ℕ) (cc : ℤ × ℤ),
      (Xof z1 z2 (cosetVec (Work.FIPlan.absDelta z1 z2) gg cc)).im
        = (Xof z1 z2 (((gg.1 : ℤ)), ((gg.2 : ℤ)))).im
          + ((Work.FIPlan.absDelta z1 z2 : ℤ))
            * (2 * (gg.1 : ℤ) * cc.1 * z2.im
              + ((Work.FIPlan.absDelta z1 z2 : ℤ)) * cc.1 ^ 2 * z2.im
              - 2 * (gg.2 : ℤ) * cc.2 * z1.im
              - ((Work.FIPlan.absDelta z1 z2 : ℤ)) * cc.2 ^ 2 * z1.im) := by
    intro gg cc
    simp only [Xof_im, cosetVec]
    ring
  rw [Adm, Adm, hre g c, him g c]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(dvd_add_left (dvd_mul_right _ _)).mp h1,
           (dvd_add_left (dvd_mul_right _ _)).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨dvd_add h1 (dvd_mul_right _ _), dvd_add h2 (dvd_mul_right _ _)⟩

end

end Work.FIArea2
