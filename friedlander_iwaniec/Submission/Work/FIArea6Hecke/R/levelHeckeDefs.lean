/-
# `Work.FIArea6Hecke.R.levelHeckeDefs`

The theta/Mellin engine of Hecke's functional equation, **for a general real scaling parameter**.

Fix `B > 0` and put `c = 1/√B`, the fixed point of the involution `u ↦ 1/(B u)` of `(0,∞)`.
For a theta series `f : ℝ → ℂ` satisfying the theta transformation law

  `f(u) = A·u^{-(m+1)}·conj f(1/(B u))`  (`u > 0`)

we define the two truncations of `f` at the fixed point `c` (`thetaCutHi`, `thetaCutLo`), the
conjugate truncation (`thetaCutHiStar`), and the three integrals

* `thetaA B f t  = ∫_c^∞ f(u) u^{t-1} du`,
* `thetaE B f m t = ∫_c^∞ conj f(v) v^{m-t} dv = ∫_c^∞ conj f(v) v^{(m+1-t)-1} dv`,
* `thetaXi B f m A t = thetaA B f t + A·B^{m+1-t}·thetaE B f m t`,

together with the completed `L`-function `thetaLam B f m A s = (√B)^s π^{m/2} Ξ(s+m/2)`.

This is the same construction as `Work.FIArea5.S16Hecke` (`heckeA`, `heckeE`, `heckeXi`,
`heckeLambda`, `thetaCut`, `thetaCutLow`, `thetaCutStar`), which is the special case
`B = thetaB d = 16 d²`, `c = thetaC d = 1/(4d)`, `A = thetaCθ U A`.  Everything there uses only
`B > 0` together with the fixed-point property `1/(B c) = c` of `c`, so the whole engine runs
verbatim for a general real `B > 0`; this is what the level-`R` functional equation
(`Work.FIArea6Hecke.R.levelHeckeFE`, where only `√R` occurs) needs.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeFE_defs
import Submission.Work.FIArea5.S16Hecke.integral_inv_scale
import Submission.Work.FIArea5.S16Hecke.cpow_inv_scale

set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R

open MeasureTheory Set
open scoped ComplexConjugate Topology

noncomputable section

/-! ## The truncations of `(0,∞)` at the fixed point `c = 1/√B` -/

/-- `c = 1/√B`: the fixed point of the involution `u ↦ 1/(B u)` of `(0,∞)`. -/
def thetaCutPt (B : ℝ) : ℝ := 1 / Real.sqrt B

/-- The `(c,∞)`-truncation of `f`. -/
def thetaCutHi (B : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun u => if thetaCutPt B < u then f u else 0

/-- The `(c,∞)`-truncation of `conj f`. -/
def thetaCutHiStar (B : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun u => if thetaCutPt B < u then star (f u) else 0

/-- The `(0,c)`-truncation of `f`. -/
def thetaCutLo (B : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun u => if u < thetaCutPt B then f u else 0

/-- `A(t) = ∫_c^∞ f(u)u^{t-1}du`, as a Mellin transform of the cutoff `thetaCutHi`. -/
def thetaA (B : ℝ) (f : ℝ → ℂ) (t : ℂ) : ℂ := mellin (thetaCutHi B f) t

/-- `E(t) = ∫_c^∞ conj f(v) v^{m-t}dv`. -/
def thetaE (B : ℝ) (f : ℝ → ℂ) (m : ℕ) (t : ℂ) : ℂ :=
  mellin (thetaCutHiStar B f) ((m : ℂ) + 1 - t)

/-- `Ξ(t) = A(t) + A·B^{m+1-t}·E(t)`. -/
def thetaXi (B : ℝ) (f : ℝ → ℂ) (m : ℕ) (A : ℂ) (t : ℂ) : ℂ :=
  thetaA B f t + A * ((B : ℂ) ^ ((m : ℂ) + 1 - t)) * thetaE B f m t

/-- `Λ(s) = (√B)^s π^{m/2} Ξ(s+m/2)`: the completed `L`-function at scale `B`. -/
def thetaLam (B : ℝ) (f : ℝ → ℂ) (m : ℕ) (A : ℂ) (s : ℂ) : ℂ :=
  ((Real.sqrt B : ℝ) : ℂ) ^ s * ((Real.pi : ℂ) ^ ((m : ℂ) / 2)) *
    thetaXi B f m A (s + (m : ℂ) / 2)

/-! ## The fixed point `c = 1/√B` -/

lemma thetaCutPt_pos {B : ℝ} (hB : 0 < B) : 0 < thetaCutPt B := by
  rw [thetaCutPt]
  exact div_pos one_pos (Real.sqrt_pos.mpr hB)

/-- `c = 1/√B` is the fixed point of `u ↦ 1/(B u)`. -/
lemma thetaCutPt_inv {B : ℝ} (hB : 0 < B) : 1 / (B * thetaCutPt B) = thetaCutPt B := by
  have hs : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  rw [thetaCutPt]
  field_simp
  exact Real.sq_sqrt hB.le

/-- The involution `v ↦ 1/(B v)` reverses the order around the fixed point `c`: for `v > 0`,
`1/(Bv) < c ↔ c < v`. -/
lemma inv_mul_lt_thetaCutPt_iff {B : ℝ} (hB : 0 < B) {v : ℝ} (hv : 0 < v) :
    1 / (B * v) < thetaCutPt B ↔ thetaCutPt B < v := by
  have hs : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  have hBv : 0 < B * v := mul_pos hB hv
  have hBsq : B = Real.sqrt B * Real.sqrt B := by rw [← pow_two, Real.sq_sqrt hB.le]
  rw [thetaCutPt]
  have h1 : 1 / (B * v) < 1 / Real.sqrt B ↔ Real.sqrt B < B * v := by
    rw [div_lt_div_iff₀ hBv hs]; simp
  have h2 : 1 / Real.sqrt B < v ↔ Real.sqrt B < B * v := by
    rw [div_lt_iff₀ hs]
    constructor
    · intro h; nlinarith [hs, h, hBsq]
    · intro h; nlinarith [hs, h, hBsq]
  rw [h1, h2]

/-- The same inequality in the direction used by the change of variables
`u = 1/(B v)`: for `v > 0`, `c < 1/(Bv) ↔ v < c`. -/
lemma thetaCutPt_lt_inv_iff {B : ℝ} (hB : 0 < B) {v : ℝ} (hv : 0 < v) :
    thetaCutPt B < 1 / (B * v) ↔ v < thetaCutPt B := by
  have hv' : 0 < 1 / (B * v) := div_pos one_pos (mul_pos hB hv)
  have h1 : 1 / (B * (1 / (B * v))) = v := by field_simp
  have h := (inv_mul_lt_thetaCutPt_iff hB hv').symm
  rw [h1] at h
  exact h

/-! ## Elementary norm bounds and star-relations -/

lemma thetaCutHi_norm_le (B : ℝ) (f : ℝ → ℂ) (u : ℝ) :
    ‖thetaCutHi B f u‖ ≤ ‖f u‖ := by
  rw [thetaCutHi]; split_ifs <;> simp

lemma thetaCutHiStar_norm_le (B : ℝ) (f : ℝ → ℂ) (u : ℝ) :
    ‖thetaCutHiStar B f u‖ ≤ ‖f u‖ := by
  rw [thetaCutHiStar]; split_ifs <;> simp

lemma thetaCutLo_norm_le (B : ℝ) (f : ℝ → ℂ) (u : ℝ) :
    ‖thetaCutLo B f u‖ ≤ ‖f u‖ := by
  rw [thetaCutLo]; split_ifs <;> simp

lemma star_thetaCutHi (B : ℝ) (f : ℝ → ℂ) :
    (fun u => star (thetaCutHi B f u)) = thetaCutHiStar B f := by
  funext u
  simp only [thetaCutHi, thetaCutHiStar]
  split <;> simp

lemma star_thetaCutHiStar (B : ℝ) (f : ℝ → ℂ) :
    (fun u => star (thetaCutHiStar B f u)) = thetaCutHi B f := by
  funext u
  simp only [thetaCutHi, thetaCutHiStar]
  split <;> simp

/-- `conj A(m+1-conj t) = E(t)`. -/
lemma star_thetaA (B : ℝ) (f : ℝ → ℂ) (m : ℕ) (t : ℂ) :
    star (thetaA B f ((m : ℂ) + 1 - star t)) = thetaE B f m t := by
  rw [thetaA, thetaE, Work.FIArea5.S16Hecke.star_mellin]
  have h1 : star ((m : ℂ) + 1 - star t) = (m : ℂ) + 1 - t := by
    rw [star_sub, star_add, star_one, star_natCast, star_star]
  rw [h1, star_thetaCutHi]

/-- `conj E(m+1-conj t) = A(t)`. -/
lemma star_thetaE (B : ℝ) (f : ℝ → ℂ) (m : ℕ) (t : ℂ) :
    star (thetaE B f m ((m : ℂ) + 1 - star t)) = thetaA B f t := by
  rw [thetaE, thetaA]
  have h1 : (m : ℂ) + 1 - ((m : ℂ) + 1 - star t) = star t := by ring
  rw [h1, Work.FIArea5.S16Hecke.star_mellin, star_star, star_thetaCutHiStar]

/-! ## Pointwise form of the change of variables `u ↦ 1/(B u)` -/

/-- The lower cutoff at `u` is the upper cutoff of `conj f` at `1/(Bu)`, with the prefactor
supplied by the theta law. -/
lemma thetaCutLo_eq_smul (B : ℝ) (hB : 0 < B) (f : ℝ → ℂ) (m : ℕ) (A : ℂ)
    (hlaw : ∀ u : ℝ, 0 < u → f u = A * ((u : ℂ) ^ (-(m : ℤ) - 1)) *
        star (f (1 / (B * u)))) :
    ∀ u : ℝ, 0 < u → thetaCutLo B f u = A •
      ((u : ℂ) ^ (-((m : ℂ) + 1)) • thetaCutHiStar B f (1 / (B * u))) := by
  intro u hu
  have hkey := thetaCutPt_lt_inv_iff hB hu
  rw [thetaCutLo, thetaCutHiStar]
  by_cases h : u < thetaCutPt B
  · rw [if_pos h, if_pos (hkey.mpr h), hlaw u hu]
    have hexp : ((-(m : ℤ) - 1 : ℤ) : ℂ) = -((m : ℂ) + 1) := by push_cast; ring
    rw [← Complex.cpow_intCast ((u : ℂ)) (-(m : ℤ) - 1), hexp, smul_eq_mul, smul_eq_mul]
    ring
  · rw [if_neg h, if_neg (fun hh => h (hkey.mp hh))]
    simp

/-! ## Entireness of the standard factors -/

lemma analyticOn_const_cpow (c : ℂ) (hc : c ≠ 0) :
    AnalyticOn ℂ (fun t : ℂ => c ^ t) Set.univ := by
  refine DifferentiableOn.analyticOn ?_ isOpen_univ
  intro t _
  exact (DifferentiableAt.const_cpow differentiableAt_id (Or.inl hc)).differentiableWithinAt

lemma analyticOn_const_cpow_affine (c : ℂ) (hc : c ≠ 0) (m : ℕ) :
    AnalyticOn ℂ (fun t : ℂ => c ^ ((m : ℂ) + 1 - t)) Set.univ := by
  refine DifferentiableOn.analyticOn ?_ isOpen_univ
  intro t _
  exact (DifferentiableAt.const_cpow (c := c)
    ((differentiableAt_const _).sub differentiableAt_id) (Or.inl hc)).differentiableWithinAt

/-- `E` is entire as soon as the Mellin transform of the upper conjugate cutoff is. -/
lemma analyticOn_thetaE (B : ℝ) (f : ℝ → ℂ) (m : ℕ)
    (h : AnalyticOn ℂ (fun t : ℂ => mellin (thetaCutHiStar B f) t) Set.univ) :
    AnalyticOn ℂ (thetaE B f m) Set.univ := by
  have hE : AnalyticOn ℂ (fun t : ℂ => ((m : ℂ) + 1) - t) Set.univ :=
    (analyticOn_const (v := ((m : ℂ) + 1)) (s := (Set.univ : Set ℂ))).sub analyticOn_id
  exact h.comp hE (fun t _ => Set.mem_univ _)

/-- `Λ` is entire as soon as `Ξ` is. -/
lemma analyticOn_thetaLam (B : ℝ) (hB : 0 < B) (f : ℝ → ℂ) (m : ℕ) (A : ℂ)
    (hXi : AnalyticOn ℂ (thetaXi B f m A) Set.univ) :
    AnalyticOn ℂ (thetaLam B f m A) Set.univ := by
  have hs : ((Real.sqrt B : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB).ne'
  have hcomp : AnalyticOn ℂ (fun s : ℂ => thetaXi B f m A (s + (m : ℂ) / 2)) Set.univ := by
    refine hXi.comp ?_ (fun x _ => Set.mem_univ _)
    refine DifferentiableOn.analyticOn ?_ isOpen_univ
    intro s _
    exact (differentiableAt_id.add_const _).differentiableWithinAt
  have h1 : AnalyticOn ℂ (fun x : ℂ => ((Real.sqrt B : ℝ) : ℂ) ^ x *
      ((Real.pi : ℂ) ^ ((m : ℂ) / 2) * thetaXi B f m A (x + (m : ℂ) / 2))) Set.univ :=
    (analyticOn_const_cpow _ hs).mul (analyticOn_const.mul hcomp)
  rw [show thetaLam B f m A = (fun x : ℂ => ((Real.sqrt B : ℝ) : ℂ) ^ x *
      ((Real.pi : ℂ) ^ ((m : ℂ) / 2) * thetaXi B f m A (x + (m : ℂ) / 2))) from
    funext (fun x => by rw [thetaLam]; ring)]
  exact h1

/-! ## The vanishing case -/

/-- A function vanishing on `(0,∞)` has zero Mellin transform. -/
lemma mellin_eq_zero_of_pos_zero (f : ℝ → ℂ) (h : ∀ u : ℝ, 0 < u → f u = 0) (t : ℂ) :
    mellin f t = 0 := by
  rw [mellin]
  rw [show (∫ u in Set.Ioi (0 : ℝ), (u : ℂ) ^ (t - 1) • f u)
      = ∫ u in Set.Ioi (0 : ℝ), (0 : ℂ) from
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun u hu => by rw [h u hu, smul_zero])]
  simp

/-- If the theta series vanishes on `(0,∞)` then the Mellin identity forces `L ≡ 0` on
`re s > 1 + m/2`. -/
lemma L_eq_zero_of_theta_eq_zero {f : ℝ → ℂ} {L : ℂ → ℂ} {m : ℕ}
    (hmellin : ∀ s : ℂ, 1 + (m : ℝ) / 2 < s.re →
      mellin f s = Complex.Gamma s * ((Real.pi : ℂ) ^ (-s)) * L (s - (m : ℂ) / 2))
    (hzero : ∀ u : ℝ, 0 < u → f u = 0) :
    ∀ s : ℂ, 1 + (m : ℝ) / 2 < s.re → L s = 0 := by
  intro s hs
  have hm2 : (m : ℂ) / 2 = (((m : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  have hm0 : (0 : ℝ) ≤ (m : ℝ) / 2 := by positivity
  have ht : 1 + (m : ℝ) / 2 < (s + (m : ℂ) / 2).re := by
    have hre : (s + (m : ℂ) / 2).re = s.re + (m : ℝ) / 2 := by
      rw [Complex.add_re, hm2, Complex.ofReal_re]
    rw [hre]
    linarith
  have hm := hmellin (s + (m : ℂ) / 2) ht
  rw [mellin_eq_zero_of_pos_zero f hzero] at hm
  have hΓ : Complex.Gamma (s + (m : ℂ) / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun k hk => ?_)
    have hre : (s + (m : ℂ) / 2).re = -(k : ℝ) := by
      have h1 := congrArg Complex.re hk
      simpa only [Complex.neg_re, Complex.natCast_re] using h1
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [hre] at ht
    linarith
  have hpi : (Real.pi : ℂ) ^ (-(s + (m : ℂ) / 2)) ≠ 0 := by
    rw [ne_eq, Complex.cpow_eq_zero_iff]
    exact fun hh => Complex.ofReal_ne_zero.mpr Real.pi_ne_zero hh.1
  have h0 := (mul_eq_zero.mp hm.symm).resolve_left (mul_ne_zero hΓ hpi)
  rwa [show s + (m : ℂ) / 2 - (m : ℂ) / 2 = s by ring] at h0

end

end Work.FIArea6Hecke.R
