import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.Table4.HB83
import Submission.Work.ZeroFreeTables.Table4.Engine8
import Submission.Work.ZeroFreeTables.Table4.FarNear
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg
import Submission.Work.LinnikAreas.A5.LFunction_disc_zeroCount
import Submission.Work.A7.zeroMult_conj_sq_one
import Submission.Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Work.ZeroFreeTables.HB95h2.pointwise
import Submission.Work.ZeroFreeTables.HB95h2.masterP3kept
import Submission.Work.ZeroFreeTables.HB95h2.imprimCorr
import Submission.Work.ZeroFreeTables.HB95h2.principalBound
import Submission.Work.ZeroFreeTables.HB95h2.logDerivEighth
import Submission.Work.ZeroFreeTables.HB95h2.keptExtractW

/-!
# `ZeroFreeTables.HB95_h2_engine` — the analytic engine of HB Lemma 9.5, `h = 2`

With `a = 34/10`, `P₃(X) = X + X² + (2/3)X³` (`P3R`), `σ = 1 + a/L` (`L = log q`), the five
points `s_j = σ + i·j·γ` (`γ = Im ρ₁`) and the Chebyshev expansion of (9.15)

`(3+10cos θ)²(9+10cos θ)² = 14379 + 24480cos θ + 14900cos 2θ + 6000cos 3θ + 1250cos 4θ`,

the pointwise inequality `0 ≤ Re(z̄^k)`-positivity (9.16) gives

`0 ≤ 14379Σ(σ,χ₀) + 24480Σ(σ+iγ,χ₁) + 14900Σ(σ+2iγ,χ₀) + 6000Σ(σ+3iγ,χ₁) + 1250Σ(σ+4iγ,χ₀)`

(`HB95h2.pointwise`), and the per-point bounds of HB §8.2 turn this into

`0 ≤ 14379P₃(α/a) − 24480P₃(1) + 30480α(1/8+ε)`

once the two side facts

* `Re P₃(α/(β+it)) ≥ 0` for `α ≤ β` (HB (4.11)), and
* `Re P₃(α/(a+it)) ≤ (8/3)(αa/(a²+t²))³` for `a ≤ α` (HB §8.2)

show that the "`T`-bracket" is non-positive — `HB95h2_Tstep` below, the exact analogue
of "the argument leading to Lemma 8.3" of the paper.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.ZeroFreeTables

/-- `P₃(1) = 8/3`. -/
theorem P3AB_one_one_zero : Table4.P3AB 1 1 0 = 8/3 := by
  rw [Table4.P3AB_zero]
  norm_num [P3R]

theorem h2_side {lam : ℝ} (h0 : 0 ≤ lam) (hle : lam ≤ 348 / 1000) :
    14900 * (((34:ℝ)/10 + lam) / ((34:ℝ)/10))^3 ≤ 30480 ∧
      1250 * (((34:ℝ)/10 + lam) / ((34:ℝ)/10))^3 ≤ 6000 := by
  have hle' : (34:ℝ)/10 + lam ≤ 1874/500 := by linarith only [hle]
  have hpos' : 0 < (34:ℝ)/10 + lam := by linarith only [h0]
  have hcube : ((34:ℝ)/10 + lam)^3 ≤ (1874/500)^3 := pow_le_pow_left₀ hpos'.le hle' 3
  have hd : (0:ℝ) < ((34:ℝ)/10)^3 := by norm_num
  constructor
  · rw [div_pow]
    rw [show 14900 * (((34:ℝ)/10 + lam)^3 / ((34:ℝ)/10)^3)
        = (14900 * ((34:ℝ)/10 + lam)^3) / ((34:ℝ)/10)^3 by ring]
    rw [div_le_iff₀ hd]
    have h1 : 14900 * ((34:ℝ)/10 + lam)^3 ≤ 14900 * (1874/500)^3 :=
      mul_le_mul_of_nonneg_left hcube (by norm_num)
    have h2 : 14900 * (1874/500)^3 ≤ 30480 * ((34:ℝ)/10)^3 := by norm_num
    linarith only [h1, h2, hcube]
  · rw [div_pow]
    rw [show 1250 * (((34:ℝ)/10 + lam)^3 / ((34:ℝ)/10)^3)
        = (1250 * ((34:ℝ)/10 + lam)^3) / ((34:ℝ)/10)^3 by ring]
    rw [div_le_iff₀ hd]
    have h1 : 1250 * ((34:ℝ)/10 + lam)^3 ≤ 1250 * (1874/500)^3 :=
      mul_le_mul_of_nonneg_left hcube (by norm_num)
    have h2 : 1250 * (1874/500)^3 ≤ 6000 * ((34:ℝ)/10)^3 := by norm_num
    linarith only [h1, h2, hcube]

theorem ratio_cube {a α t : ℝ} (ha : 0 < a) (hα : 0 < α) (hale : a ≤ α) :
    (α * a / (a^2 + t^2))^3 ≤ (α/a)^3 * (α^2/(α^2 + t^2))^3 := by
  have hd1 : 0 < a^2 + t^2 := by positivity
  have hd2 : 0 < α^2 + t^2 := by positivity
  have hkey : ((α/a) * (α^2/(α^2 + t^2))) - (α * a / (a^2 + t^2))
      = (α*(α^2 - a^2)*t^2)/(a*(a^2+t^2)*(α^2+t^2)) := by
    field_simp
    ring
  have hnum : 0 ≤ α*(α^2 - a^2)*t^2 := by
    have h1 : 0 ≤ α^2 - a^2 := by nlinarith only [hale, ha.le, hα.le, ha, hα]
    positivity
  have hAB : α * a / (a^2 + t^2) ≤ (α/a) * (α^2/(α^2 + t^2)) := by
    have h3 : 0 ≤ ((α/a) * (α^2/(α^2 + t^2))) - (α * a / (a^2 + t^2)) := by
      rw [hkey]; positivity
    linarith only [h3]
  calc (α * a / (a^2 + t^2))^3 ≤ ((α/a) * (α^2/(α^2 + t^2)))^3 :=
        pow_le_pow_left₀ (by positivity) hAB 3
    _ = (α/a)^3 * (α^2/(α^2 + t^2))^3 := by ring

theorem h2_Tstep {lam T : ℝ} (h0 : 0 ≤ lam) (hle : lam ≤ 348 / 1000) :
    14900 * Table4.P3AB ((34:ℝ)/10 + lam) ((34:ℝ)/10) T
      + 1250 * Table4.P3AB ((34:ℝ)/10 + lam) ((34:ℝ)/10) (2 * T)
      ≤ 30480 * Table4.P3AB ((34:ℝ)/10 + lam) ((34:ℝ)/10 + lam) T
        + 6000 * Table4.P3AB ((34:ℝ)/10 + lam) ((34:ℝ)/10 + lam) (2 * T) := by
  obtain ⟨hs1, hs2⟩ := h2_side h0 hle
  have ha : 0 < ((34:ℝ)/10) := by norm_num
  have hα : 0 < ((34:ℝ)/10) + lam := by linarith only [h0]
  have hale : ((34:ℝ)/10) ≤ ((34:ℝ)/10) + lam := by linarith only [h0]
  have hfac : ∀ t : ℝ, (((34:ℝ)/10 + lam) * ((34:ℝ)/10)
        / (((34:ℝ)/10)^2 + t^2))^3
      ≤ (((34:ℝ)/10 + lam) / ((34:ℝ)/10))^3
        * ((((34:ℝ)/10 + lam)^2) / ((((34:ℝ)/10 + lam)^2) + t^2))^3 :=
    fun t => ratio_cube ha hα hale (t := t)
  have key : ∀ t : ℝ, 14900 * ((8/3) * (((34:ℝ)/10 + lam) * ((34:ℝ)/10)
        / (((34:ℝ)/10)^2 + t^2))^3)
      ≤ 30480 * ((8/3) * (((34:ℝ)/10 + lam)^2 / (((34:ℝ)/10 + lam)^2 + t^2))^3) := by
    intro t
    have h1 : 14900 * ((((34:ℝ)/10 + lam) * ((34:ℝ)/10)
          / (((34:ℝ)/10)^2 + t^2))^3)
        ≤ 14900 * ((((34:ℝ)/10 + lam) / ((34:ℝ)/10))^3
            * ((((34:ℝ)/10 + lam)^2) / ((((34:ℝ)/10 + lam)^2) + t^2))^3) :=
      mul_le_mul_of_nonneg_left (hfac t) (by norm_num)
    have h2 : 14900 * ((((34:ℝ)/10 + lam) / ((34:ℝ)/10))^3
          * ((((34:ℝ)/10 + lam)^2) / ((((34:ℝ)/10 + lam)^2) + t^2))^3)
        ≤ 30480 * ((((34:ℝ)/10 + lam)^2 / ((((34:ℝ)/10 + lam)^2) + t^2))^3) := by
      have h3 : 14900 * ((((34:ℝ)/10 + lam) / ((34:ℝ)/10))^3) ≤ 30480 := hs1
      have h4 : 0 ≤ ((((34:ℝ)/10 + lam)^2 / ((((34:ℝ)/10 + lam)^2) + t^2))^3) := by
        positivity
      nlinarith only [h3, h4, hs1]
    have h5 : 0 ≤ (8/3 : ℝ) := by norm_num
    linarith only [h1, h2, h5]
  have key2 : 1250 * ((8/3) * (((34:ℝ)/10 + lam) * ((34:ℝ)/10)
        / (((34:ℝ)/10)^2 + (2*T)^2))^3)
      ≤ 6000 * ((8/3) * (((34:ℝ)/10 + lam)^2 / (((34:ℝ)/10 + lam)^2 + (2*T)^2))^3) := by
    have h1 : 1250 * ((((34:ℝ)/10 + lam) * ((34:ℝ)/10)
          / (((34:ℝ)/10)^2 + (2*T)^2))^3)
        ≤ 1250 * ((((34:ℝ)/10 + lam) / ((34:ℝ)/10))^3
            * ((((34:ℝ)/10 + lam)^2) / ((((34:ℝ)/10 + lam)^2) + (2*T)^2))^3) :=
      mul_le_mul_of_nonneg_left (hfac (2*T)) (by norm_num)
    have h2 : 1250 * ((((34:ℝ)/10 + lam) / ((34:ℝ)/10))^3
          * ((((34:ℝ)/10 + lam)^2) / ((((34:ℝ)/10 + lam)^2) + (2*T)^2))^3)
        ≤ 6000 * ((((34:ℝ)/10 + lam)^2 / ((((34:ℝ)/10 + lam)^2) + (2*T)^2))^3) := by
      have h3 : 1250 * ((((34:ℝ)/10 + lam) / ((34:ℝ)/10))^3) ≤ 6000 := hs2
      have h4 : 0 ≤ ((((34:ℝ)/10 + lam)^2 / ((((34:ℝ)/10 + lam)^2) + (2*T)^2))^3) := by
        positivity
      nlinarith only [h3, h4, hs1]
    have h5 : 0 ≤ (8/3 : ℝ) := by norm_num
    linarith only [h1, h2, h5]
  have hle1 := Table4.P3AB_le (((34:ℝ)/10 + lam)) ((34:ℝ)/10) T hα ha hale
  have hle2 := Table4.P3AB_le (((34:ℝ)/10 + lam)) ((34:ℝ)/10) (2*T) hα ha hale
  have hge1 := Table4.P3AB_ge (((34:ℝ)/10 + lam)) (((34:ℝ)/10 + lam)) T hα hα le_rfl
  have hge2 := Table4.P3AB_ge (((34:ℝ)/10 + lam)) (((34:ℝ)/10 + lam)) (2*T) hα hα le_rfl
  have hk1 : 14900 * Table4.P3AB ((34:ℝ)/10 + lam) ((34:ℝ)/10) T
      ≤ 30480 * ((8/3) * (((34:ℝ)/10 + lam)^2 / (((34:ℝ)/10 + lam)^2 + T^2))^3) :=
    le_trans (mul_le_mul_of_nonneg_left hle1 (by norm_num)) (key T)
  have hk2 : 1250 * Table4.P3AB ((34:ℝ)/10 + lam) ((34:ℝ)/10) (2*T)
      ≤ 6000 * ((8/3) * (((34:ℝ)/10 + lam)^2
          / (((34:ℝ)/10 + lam)^2 + (2*T)^2))^3) :=
    le_trans (mul_le_mul_of_nonneg_left hle2 (by norm_num)) (key2)
  have hge1' : (8/3) * ((((34:ℝ)/10 + lam)^2) / (((34:ℝ)/10 + lam)^2 + T^2))^3
      ≤ Table4.P3AB ((34:ℝ)/10 + lam) ((34:ℝ)/10 + lam) T := by
    simpa [pow_two] using hge1
  have hge2' : (8/3) * ((((34:ℝ)/10 + lam)^2) / (((34:ℝ)/10 + lam)^2 + (2*T)^2))^3
      ≤ Table4.P3AB ((34:ℝ)/10 + lam) ((34:ℝ)/10 + lam) (2*T) := by
    simpa [pow_two] using hge2
  have hfin1 : 30480 * ((8/3) * (((34:ℝ)/10 + lam)^2
        / (((34:ℝ)/10 + lam)^2 + T^2))^3)
      ≤ 30480 * Table4.P3AB ((34:ℝ)/10 + lam) ((34:ℝ)/10 + lam) T :=
    mul_le_mul_of_nonneg_left hge1' (by norm_num)
  have hfin2 : 6000 * ((8/3) * (((34:ℝ)/10 + lam)^2
        / (((34:ℝ)/10 + lam)^2 + (2*T)^2))^3)
      ≤ 6000 * Table4.P3AB ((34:ℝ)/10 + lam) ((34:ℝ)/10 + lam) (2*T) :=
    mul_le_mul_of_nonneg_left hge2' (by norm_num)
  linarith only [hk1, hk2, hfin1, hfin2, key2, hle2, hge1', hge2']

/-- A non-principal character of level `q` forces `2 ≤ q`. -/
theorem two_le_of_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : 2 ≤ q := by
  by_contra h
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq2 : q ≤ 1 := by omega
  have hs : Subsingleton (ZMod q)ˣ := by interval_cases q <;> infer_instance
  refine hχ (MulChar.ext (fun a => ?_))
  rw [show a = 1 from Subsingleton.elim a 1]
  simp

/-- The primitive character inducing a real character is real. -/
theorem primitiveCharacter_sq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (h : χ ^ 2 = 1) : χ.primitiveCharacter ^ 2 = 1 := by
  refine DirichletCharacter.changeLevel_injective χ.conductor_dvd_level ?_
  rw [map_pow, DirichletCharacter.changeLevel_primitiveCharacter, h,
    DirichletCharacter.changeLevel_one]

/-- The primitive character inducing a non-principal character is non-principal. -/
theorem primitiveCharacter_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h
  refine hχ ?_
  have h2 := DirichletCharacter.changeLevel_primitiveCharacter χ
  rw [h, map_one] at h2
  exact h2.symm

/-- `Re P₃` at a scaled zero argument, in terms of `P3AB`. -/
theorem reP3_eq_P3AB {x y t : ℝ} {z : ℂ}
    (hz : z = ((y : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) :
    (P3 (((x : ℝ) : ℂ) / z)).re = Table4.P3AB x y t := by
  rw [hz]
  rfl

/-- The decomposition of `starRingEnd ℂ z`. -/
theorem starRingEnd_eq (z : ℂ) :
    starRingEnd ℂ z = ((z.re : ℂ)) + ((-z.im : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.conj_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.I_re, Complex.I_im]
  · simp [Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im]

/-- Conjugation does not change the multiplicity. -/
theorem zeroMult_prim {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (ρ : ℂ) :
    Work.LinnikContract.zeroMult χ (starRingEnd ℂ ρ) = Work.LinnikContract.zeroMult χ ρ :=
  Work.A7.zeroMult_conj_sq_one χ hsq ρ

/-- If `u` is a zero with `Re u < 1` lying *outside* the near disk
`‖1 + i·Im s - u‖ ≤ δ`, and `a/L ≤ δ/2` with `Re s = 1 + a/L`, then the `k = 1` kernel
`Re (1/(s-u))` is at most `8/δ²`. -/
theorem re_inv_le_of_far {δ a L : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 < a) (hL : 0 < L)
    (hLa : a / L ≤ δ / 2) {s u : ℂ} (hsre : s.re = 1 + a / L) (hu : u.re < 1)
    (hfar : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖) :
    ((1 / (s - u)).re) ≤ 8 / δ^2 := by
  have hδpos : 0 < δ^2 := by positivity
  have haL : 0 ≤ a / L := div_nonneg ha.le hL.le
  have hxpos : 0 < s.re - u.re := by rw [hsre]; linarith only [hu, haL]
  have hsq : ‖s - u‖^2 = (s.re - u.re)^2 + (s.im - u.im)^2 := by
    have hre : (s - u).re = s.re - u.re := by simp
    have him : (s - u).im = s.im - u.im := by simp
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  have hsq2 : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖^2
      = (1 - u.re)^2 + (s.im - u.im)^2 := by
    have hre : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u).re = 1 - u.re := by simp
    have him : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u).im = s.im - u.im := by simp
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  have hkey : δ^2 < (1 - u.re)^2 + (s.im - u.im)^2 := by
    have h1 : δ^2 < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖^2 := by
      nlinarith only [hfar, hδ, norm_nonneg ((1 : ℂ) + (s.im : ℂ) * Complex.I - u)]
    rwa [hsq2] at h1
  have hre : ((1 / (s - u)).re) = (s.re - u.re) / ((s.re - u.re)^2 + (s.im - u.im)^2) := by
    rw [one_div, Complex.inv_re]
    have h1 : Complex.normSq (s - u) = (s.re - u.re)^2 + (s.im - u.im)^2 := by
      rw [Complex.normSq_apply]
      have hre' : (s - u).re = s.re - u.re := by simp
      have him' : (s - u).im = s.im - u.im := by simp
      rw [hre', him']
      ring
    rw [h1]
    simp only [Complex.sub_re]
  have hsplit : (1 - u.re) = (s.re - u.re) - a / L := by rw [hsre]; ring
  have hden : (0:ℝ) < (s.re - u.re)^2 + (s.im - u.im)^2 := by positivity
  rcases le_or_gt (s.re - u.re) (δ/2) with hxle | hxgt
  · have hupper : (s.re - u.re) - a/L ≤ δ/2 := by linarith only [hxle, haL]
    have hlower : -(δ/2) ≤ (s.re - u.re) - a/L := by linarith only [hLa, hxpos, hsre, hu, haL, hxle]
    have hsquare : (1 - u.re)^2 ≤ δ^2/4 := by
      have h1 : |1 - u.re| ≤ δ/2 := by
        rw [abs_le]
        exact ⟨by rw [hsplit]; exact hlower, by rw [hsplit]; exact hupper⟩
      have h3 := abs_le.mp h1
      have h4 : (1 - u.re)^2 ≤ (δ/2)^2 := by nlinarith only [h3.1, h3.2, hδ, haL, hLa, hsre, hxle, hu]
      linarith only [h4, hδ]
    have hy : 3*δ^2/4 ≤ (s.im - u.im)^2 := by linarith only [hkey, hsquare]
    rw [hre, div_le_iff₀ hden]
    have hxsq : 0 ≤ (s.re - u.re)^2 := sq_nonneg _
    have hbig : 6 ≤ (8/δ^2) * ((s.re - u.re)^2 + (s.im - u.im)^2) := by
      have h6 : (8/δ^2) * (3*δ^2/4) = 6 := by field_simp <;> ring
      have h8 : (3*δ^2/4) ≤ (s.re - u.re)^2 + (s.im - u.im)^2 := by linarith only [hy, hxsq, hkey, hsquare]
      exact le_trans h6.ge (mul_le_mul_of_nonneg_left h8 (by positivity : (0:ℝ) ≤ 8/δ^2))
    linarith only [hbig, hxle, hδ1, hδ, hsre, hu, haL]
  · have h4 : δ^2/8 ≤ s.re - u.re := by nlinarith only [hxgt, hδ, hδ1, hsre, hu, haL]
    have h5 : 1 ≤ (8/δ^2) * (s.re - u.re) := by
      have h6 : (8/δ^2) * (δ^2/8) ≤ (8/δ^2) * (s.re - u.re) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      have h7 : (8/δ^2) * (δ^2/8) = 1 := by field_simp <;> ring
      linarith only [h6, h7.le, h7]
    rw [hre, div_le_iff₀ hden]
    have h9 : (s.re - u.re) ≤ ((8/δ^2) * (s.re - u.re)) * (s.re - u.re) := by
      have h := mul_le_mul_of_nonneg_right h5 hxpos.le
      simpa using h
    have h10 : 0 ≤ (8/δ^2) * (s.im - u.im)^2 := by positivity
    linarith only [h9, h10]

/-- The final numeric absorption of the engine.  If two real quantities are each bounded by
`(P/L)·(16m/δ²)` with `1 ≤ m` integral, `P ≤ 4`, `δ²L ≥ 1000` and `δ²εL ≥ 1000`, then their
weighted sum with weights `24480` and `6000` is at most `65280(m-1) + 22856·P·ε`. -/
theorem hBnum_aux {P L δ ε R1 R3 m : ℝ} (hP : 0 < P) (hL : 0 < L) (hδ : 0 < δ) (hε : 0 < ε)
    (hP4 : P ≤ 4) (hm : 1 ≤ m) (hk : ∃ k : ℕ, m = (k : ℝ))
    (h1 : R1 ≤ (P / L) * (16 * m / δ ^ 2)) (h3 : R3 ≤ (P / L) * (16 * m / δ ^ 2))
    (hLδ : 1000 ≤ δ ^ 2 * L) (hLε : 1000 ≤ δ ^ 2 * ε * L) :
    24480 * R1 + 6000 * R3 ≤ 65280 * (m - 1) + 22856 * P * ε := by
  obtain ⟨k, hk'⟩ := hk
  have hkpos : 1 ≤ k := by
    rw [hk'] at hm
    exact_mod_cast hm
  have hmpos : 0 < m := lt_of_lt_of_le one_pos hm
  have hδ2L : 0 < δ ^ 2 * L := by positivity
  set R : ℝ := 16 * m * P / (δ ^ 2 * L) with hRdef
  have hkey : (P / L) * (16 * m / δ ^ 2) = R := by
    rw [hRdef, div_mul_div_comm, mul_comm L (δ ^ 2)]
    ring
  have hR1 : R1 ≤ R := hkey ▸ h1
  have hR3 : R3 ≤ R := hkey ▸ h3
  have hRnn : 0 ≤ R := by rw [hRdef]; positivity
  have hstep : 24480 * R1 + 6000 * R3 ≤ 30480 * R := by linarith only [hR1, hR3, hRnn, h1, h3, hkey]
  have hRform : R = 16 * m * P * (1 / (δ ^ 2 * L)) := by rw [hRdef]; ring
  have hnonneg : (0:ℝ) ≤ 16 * m * P := by positivity
  have hinv : 1 / (δ ^ 2 * L) ≤ ε / 1000 := by
    rw [div_le_div_iff₀ hδ2L (by norm_num)]
    have h : ε * (δ ^ 2 * L) = δ ^ 2 * ε * L := by ring
    linarith only [hLε, h]
  have hinv2 : 1 / (δ ^ 2 * L) ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ hδ2L (by norm_num)]
    linarith only [hLδ]
  rcases (by omega : k = 1 ∨ 2 ≤ k) with hk1 | hk2
  · subst hk1
    have hmm : m = 1 := by rw [hk']; norm_num
    have hRle : R ≤ 16 * m * P * (ε / 1000) := by
      rw [hRform]
      exact mul_le_mul_of_nonneg_left hinv hnonneg
    have hfin : 24480 * R1 + 6000 * R3 ≤ 22856 * P * ε := by
      have h2 := mul_le_mul_of_nonneg_left hRle (show (0:ℝ) ≤ 30480 by norm_num)
      nlinarith only [hstep, h2, hmm, hP.le, hε.le, h1, h3, hkey, hRle, hP, hε, hm, hRnn]
    have hz : (65280 : ℝ) * (m - 1) = 0 := by rw [hmm]; norm_num
    rw [hz, zero_add]
    exact hfin
  · have hk2' : (2 : ℝ) ≤ m := by rw [hk']; exact_mod_cast hk2
    have hRle : R ≤ 16 * m * P / 1000 := by
      rw [hRform]
      have h := mul_le_mul_of_nonneg_left hinv2 hnonneg
      linarith only [h]
    have hfin : 24480 * R1 + 6000 * R3 ≤ 65280 * (m - 1) := by
      have h2 := mul_le_mul_of_nonneg_left hRle (show (0:ℝ) ≤ 30480 by norm_num)
      nlinarith only [hstep, h2, hk2', hP4, hmpos, h1, h3, hk', hkey, hRle, hP]
    have hεP : (0:ℝ) ≤ 22856 * P * ε := by positivity
    linarith only [hfin, hεP]

theorem HB95_h2_engine :
    ∀ ε : ℝ, 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 →
      Work.LinnikContract.lamOf q ρ₁ ≤ (348 : ℝ) / 1000 →
        0 ≤ 14379 * Work.ZeroFreeTables.P3R (((34 : ℝ) / 10 + Work.LinnikContract.lamOf q ρ₁) / ((34 : ℝ) / 10))
          - 24480 * Work.ZeroFreeTables.P3R 1
          + 30480 * ((34 : ℝ) / 10 + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε) := by
  intro ε hε
  -- ## the analytic inputs
  obtain ⟨L₀_log, δ, hδ0, hδ1, hlog⟩ := HB95h2.logDerivEighth (e := ε / 16) (by positivity)
  obtain ⟨L₀_m, hm⟩ := HB95h2.masterP3kept (a := (34 : ℝ) / 10) (δ := δ) (c := 1 / 8 + ε / 16)
      (e := ε / 16) (M := 1) (by norm_num) hδ0 hδ1 (by positivity)
  obtain ⟨L₀_i, hi⟩ := HB95h2.imprimCorr (a := (34 : ℝ) / 10) (e := ε / 16) (M := 1)
      (by norm_num) (by positivity)
  obtain ⟨L₀_p, hp⟩ := HB95h2.principalBound (a := (34 : ℝ) / 10) (e := ε / 16) (M := 1)
      (by norm_num) (by positivity)
  -- ## the threshold
  set Y : ℝ := max 64 (max (1000 / (δ ^ 2 * ε)) (1000 / δ ^ 2)) with hYdef
  set Z : ℝ := max (8 / δ) Y with hZdef
  set Lreq : ℝ := max (max L₀_log (max L₀_m (max L₀_i L₀_p))) Z with hLreqdef
  refine ⟨Nat.ceil (Real.exp Lreq) + 10, ?_⟩
  intro q hq hqne χ₁ ρ₁ hm1 hsq him hle
  haveI : NeZero q := hqne
  have hq1 : 1 < q := by
    have h1 : Nat.ceil (Real.exp Lreq) + 10 ≤ q := hq
    omega
  have hexp : Real.exp Lreq ≤ (q : ℝ) := by
    have h1 : Real.exp Lreq ≤ (Nat.ceil (Real.exp Lreq) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.exp Lreq) + 10 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    push_cast at h2
    linarith only [hδ0, hδ1, h1, h2]
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hLge : Lreq ≤ L := by
    rw [hLdef, ← Real.log_exp Lreq]
    exact Real.log_le_log (Real.exp_pos Lreq) hexp
  have hZL : Z ≤ L := le_trans (le_max_right (max L₀_log (max L₀_m (max L₀_i L₀_p))) Z) hLge
  have hYL : Y ≤ L := le_trans (le_max_right (8 / δ) Y) hZL
  have h8δ : 8 / δ ≤ L := le_trans (le_max_left (8 / δ) Y) hZL
  have h64 : (64 : ℝ) ≤ L := le_trans (le_max_left (64:ℝ) (max (1000 / (δ ^ 2 * ε)) (1000 / δ ^ 2))) hYL
  have hLε : 1000 / (δ ^ 2 * ε) ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right (64:ℝ) _)) hYL
  have hLδ : 1000 / δ ^ 2 ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right (64:ℝ) _)) hYL
  have hL0log : L₀_log ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLge
  have hL0m : L₀_m ≤ L :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_left _ _)) hLge
  have hL0i : L₀_i ≤ L :=
    le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_left _ _)) hLge
  have hL0p : L₀_p ≤ L :=
    le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_left _ _)) hLge
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by exact_mod_cast hq1)
  -- ## facts about the pair
  have hZ : Work.LinnikContract.IsZ χ₁ ρ₁ := isMin1_isZ hm1.1
  have hχ1ne : χ₁ ≠ 1 := isZ_ne_one hZ
  have hzm : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hZ.2.1
  have hγ1 : |ρ₁.im| ≤ 1 := hZ.2.2
  have hq2 : 2 ≤ q := two_le_of_ne_one χ₁ hχ1ne
  have hlam0 : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    Work.LinnikContract.API.isZ_lambda_nonneg hq2 hZ
  have hlam1 : Work.LinnikContract.lamOf q ρ₁ ≤ 1 := by linarith only [hδ0, hδ1, hle]
  have hlamval : Work.LinnikContract.lamOf q ρ₁ = (1 - ρ₁.re) * L := by rw [hLdef]; rfl
  -- ## the primitive character and the notation
  haveI hNne : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hχs_ne : χ₁.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one χ₁ hχ1ne
  have hχs_prim : (χ₁.primitiveCharacter).IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ₁
  have hχs_sq : (χ₁.primitiveCharacter) ^ 2 = 1 := primitiveCharacter_sq_one χ₁ hsq
  have hzm_eq : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u
      = Work.LinnikContract.zeroMult χ₁.primitiveCharacter u := by
    intro u
    rw [show Work.LinnikContract.zeroMult χ₁.primitiveCharacter u
        = analyticOrderNatAt (DirichletCharacter.completedLFunction (χ₁.primitiveCharacter)) u from
      Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive
        (χ₁.primitiveCharacter) hχs_prim u]
    rfl
  have hNq : χ₁.conductor ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ₁.conductor_dvd_level
  have hlogN : Real.log ((χ₁.conductor : ℕ) : ℝ) ≤ L := by
    rw [hLdef]
    exact Real.log_le_log
      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ₁.conductor)) (by exact_mod_cast hNq)
  set A : ℝ := (34 : ℝ) / 10 with hAdef
  set α : ℝ := A + Work.LinnikContract.lamOf q ρ₁ with hαdef
  set γ : ℝ := ρ₁.im with hγdef
  set T : ℝ := 2 * γ * L with hTdef
  set σ : ℝ := 1 + A / L with hσdef
  set s₁ : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I with hs₁def
  set s₂ : ℂ := (σ : ℂ) + (((2 : ℝ) * γ) : ℂ) * Complex.I with hs₂def
  set s₃ : ℂ := (σ : ℂ) + (((3 : ℝ) * γ) : ℂ) * Complex.I with hs₃def
  set s₄ : ℂ := (σ : ℂ) + (((4 : ℝ) * γ) : ℂ) * Complex.I with hs₄def
  set S : Finset ℂ := {ρ₁, starRingEnd ℂ ρ₁} with hSdef
  have hApos : 0 < A := by rw [hAdef]; norm_num
  have hαpos : 0 < α := by rw [hαdef, hAdef]; linarith only [hδ0, hδ1, hlam0]
  have hαle4 : α ≤ 4 := by rw [hαdef, hAdef]; linarith only [hδ0, hδ1, hle]
  have hσgt : 1 < σ := by
    rw [hσdef]
    have h : 0 < A / L := div_pos hApos hLpos
    linarith only [h]
  have hLne : L ≠ 0 := hLpos.ne'
  have hAlL : A / L ≤ δ / 2 := by
    rw [div_le_iff₀ hLpos]
    have h1 : (δ / 2) * (8 / δ) = 4 := by field_simp <;> ring
    have h2 : (4:ℝ) ≤ (δ / 2) * L := by
      have h3 := mul_le_mul_of_nonneg_left h8δ (by positivity : (0:ℝ) ≤ δ / 2)
      linarith only [h3, h1]
    have h4 : A ≤ 4 := by rw [hAdef]; norm_num
    linarith only [h2, h4, hδ0, hδ1]
  have hconj_ne : starRingEnd ℂ ρ₁ ≠ ρ₁ := by
    intro h
    have h2 : (starRingEnd ℂ ρ₁).im = ρ₁.im := by rw [h]
    rw [Complex.conj_im] at h2
    have h3 : ρ₁.im = 0 := by linarith only [h2]
    exact him h3
  -- ## the six denominator identities
  have hρrepr : ((ρ₁.re : ℂ)) + (ρ₁.im : ℂ) * Complex.I = ρ₁ := Complex.re_add_im ρ₁
  have hLℂ : ((L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hLne
  have d1 : (s₁ - ρ₁) * (L : ℂ) = ((α : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I := by
    rw [hs₁def, ← hρrepr, hσdef, hγdef, hαdef, hlamval]
    push_cast
    field_simp
    ring
  have d2 : (s₁ - starRingEnd ℂ ρ₁) * (L : ℂ) = ((α : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I := by
    rw [hs₁def, hσdef, hγdef, hαdef, hTdef, hlamval]
    rw [starRingEnd_eq]
    push_cast
    field_simp
    ring
  have d3 : (s₃ - ρ₁) * (L : ℂ) = ((α : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I := by
    rw [hs₃def, ← hρrepr, hσdef, hγdef, hαdef, hTdef, hlamval]
    push_cast
    field_simp
    ring
  have d4 : (s₃ - starRingEnd ℂ ρ₁) * (L : ℂ)
      = ((α : ℝ) : ℂ) + ((2 * T : ℝ) : ℂ) * Complex.I := by
    rw [hs₃def, hσdef, hγdef, hαdef, hTdef, hlamval]
    rw [starRingEnd_eq]
    push_cast
    field_simp
    ring
  have d5 : (s₂ - 1) * (L : ℂ) = ((A : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I := by
    rw [hs₂def, hσdef, hγdef, hTdef]
    push_cast
    field_simp
    ring
  have d6 : (s₄ - 1) * (L : ℂ) = ((A : ℝ) : ℂ) + ((2 * T : ℝ) : ℂ) * Complex.I := by
    rw [hs₄def, hσdef, hγdef, hTdef]
    push_cast
    field_simp
    ring
  have d0 : ((σ : ℂ) - 1) * (L : ℂ) = ((A : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I := by
    rw [hσdef]
    push_cast
    field_simp
    ring
  -- ## the pointwise inequality (HB (9.16))
  have hpt := HB95h2.pointwise (q := q) χ₁ hsq (a := A) (lam₁ := Work.LinnikContract.lamOf q ρ₁)
      (σ := σ) (γ := γ) (le_of_lt hαpos) hσgt hq2
  simp only [← hs₁def, ← hs₂def, ← hs₃def, ← hs₄def] at hpt
  rw [← hLdef] at hpt
  -- ## the real/im parts of the five points
  have hγabs : |γ| ≤ 1 := by rw [hγdef]; exact hγ1
  have hre1 : s₁.re = 1 + A / L := by rw [hs₁def]; simp [hσdef]
  have him1 : |s₁.im| ≤ 4 := by
    have h : s₁.im = γ := by rw [hs₁def]; simp
    rw [h]; rw [abs_le] at hγabs ⊢
    constructor <;> linarith only [hγabs.1, hγabs.2, hγabs, hδ1, hσdef, hσgt, hAlL]
  have hre2 : s₂.re = 1 + A / L := by rw [hs₂def]; simp [hσdef]
  have him2 : |s₂.im| ≤ 4 := by
    have h : s₂.im = 2 * γ := by rw [hs₂def]; simp
    rw [h]; rw [abs_le] at hγabs ⊢
    constructor <;> linarith only [hγabs.1, hγabs.2, hγabs, hδ1, hσdef, hσgt, hAlL]
  have hre3 : s₃.re = 1 + A / L := by rw [hs₃def]; simp [hσdef]
  have him3 : |s₃.im| ≤ 4 := by
    have h : s₃.im = 3 * γ := by rw [hs₃def]; simp
    rw [h]; rw [abs_le] at hγabs ⊢
    constructor <;> linarith only [hγabs.1, hγabs.2, hγabs, hδ1, hσdef, hσgt, hAlL]
  have hre4 : s₄.re = 1 + A / L := by rw [hs₄def]; simp [hσdef]
  have him4 : |s₄.im| ≤ 4 := by
    have h : s₄.im = 4 * γ := by rw [hs₄def]; simp
    rw [h]; rw [abs_le] at hγabs ⊢
    constructor <;> linarith only [hγabs.1, hγabs.2, hγabs]
  have hre0 : ((σ : ℂ)).re = 1 + A / L := by simp [hσdef]
  have him0 : |((σ : ℂ)).im| ≤ 4 := by simp
  -- ## the principal-character bounds
  have hp0 := hp (L := L) (lam₁ := Work.LinnikContract.lamOf q ρ₁) hL0p (le_of_eq hLdef.symm)
      hlam0 hlam1 (s := (σ : ℂ)) hre0 him0
  have hp2 := hp (L := L) (lam₁ := Work.LinnikContract.lamOf q ρ₁) hL0p (le_of_eq hLdef.symm)
      hlam0 hlam1 (s := s₂) hre2 him2
  have hp4 := hp (L := L) (lam₁ := Work.LinnikContract.lamOf q ρ₁) hL0p (le_of_eq hLdef.symm)
      hlam0 hlam1 (s := s₄) hre4 him4
  have hpack : ((↑A + ↑(Work.LinnikContract.lamOf q ρ₁)) : ℂ)
      = (((A + Work.LinnikContract.lamOf q ρ₁ : ℝ)) : ℂ) := by rw [Complex.ofReal_add]
  have e0 : (P3 ((↑A + ↑(Work.LinnikContract.lamOf q ρ₁)) / (((σ : ℂ) - 1) * (L : ℂ)))).re
      = P3R (α / A) := by
    rw [hpack, reP3_eq_P3AB (x := A + Work.LinnikContract.lamOf q ρ₁) (y := A) (t := 0) d0,
      Table4.P3AB_zero, ← hαdef]
  have e2 : (P3 ((↑A + ↑(Work.LinnikContract.lamOf q ρ₁)) / ((s₂ - 1) * (L : ℂ)))).re
      = Table4.P3AB α A T := by
    rw [hpack, reP3_eq_P3AB (x := A + Work.LinnikContract.lamOf q ρ₁) (y := A) (t := T) d5,
      ← hαdef]
  have e4 : (P3 ((↑A + ↑(Work.LinnikContract.lamOf q ρ₁)) / ((s₄ - 1) * (L : ℂ)))).re
      = Table4.P3AB α A (2 * T) := by
    rw [hpack, reP3_eq_P3AB (x := A + Work.LinnikContract.lamOf q ρ₁) (y := A) (t := 2*T) d6,
      ← hαdef]
  have hρ₁re_lt : ρ₁.re < 1 := by
    have hz : DirichletCharacter.completedLFunction (χ₁.primitiveCharacter) ρ₁ = 0 :=
      apply_eq_zero_of_analyticOrderNatAt_ne_zero
        (by simpa [Work.LinnikContract.zeroMult] using hzm)
    exact (Commons.NumberTheory.Linnik.completedL_zero_strip (χ₁.primitiveCharacter)
      hχs_ne hχs_prim hz).2
  -- ## the `χ₁`-bounds at `s₁` and `s₃`
  have hlog1 : Work.ZeroFreeTables.LogDerivHyp χ₁.primitiveCharacter δ L (1 / 8 + ε / 16) :=
    hlog χ₁.primitiveCharacter hχs_ne hχs_prim hχs_sq hL0log hlogN
  have hi1 := hi (χ := χ₁) hχ1ne (L := L) (lam₁ := Work.LinnikContract.lamOf q ρ₁)
      hL0i (le_of_eq hLdef.symm) hlam0 hlam1 (s := s₁) hre1 him1
  have hi3 := hi (χ := χ₁) hχ1ne (L := L) (lam₁ := Work.LinnikContract.lamOf q ρ₁)
      hL0i (le_of_eq hLdef.symm) hlam0 hlam1 (s := s₃) hre3 him3
  have hm1' := hm (χ := χ₁.primitiveCharacter) hχs_ne hχs_prim (L := L)
      (lam₁ := Work.LinnikContract.lamOf q ρ₁) hL0m hlogN hlam0 hlam1 hlog1 S s₁ hre1 him1
  have hm3' := hm (χ := χ₁.primitiveCharacter) hχs_ne hχs_prim (L := L)
      (lam₁ := Work.LinnikContract.lamOf q ρ₁) hL0m hlogN hlam0 hlam1 hlog1 S s₃ hre3 him3
  -- ## the multiplicity and the `S`-members
  set m : ℝ := (Work.LinnikContract.zeroMult χ₁ ρ₁ : ℝ) with hmdef
  have hm_ge1 : 1 ≤ m := by
    rw [hmdef]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzm
  have hconj_zm : Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) (starRingEnd ℂ ρ₁)
      ≠ 0 := by
    rw [zeroMult_prim (χ₁.primitiveCharacter) hχs_sq, ← hzm_eq]
    exact hzm
  have hρ₁_zm : Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) ρ₁ ≠ 0 := by
    rw [← hzm_eq]; exact hzm
  have hαne : α ≠ 0 := ne_of_gt hαpos
  have hW1nn : 0 ≤ Table4.P3AB α α T := Table4.P3AB_nonneg α α T hαpos hαpos le_rfl
  have hW2nn : 0 ≤ Table4.P3AB α α (2 * T) := Table4.P3AB_nonneg α α (2 * T) hαpos hαpos le_rfl
  -- ## the kept extractions
  have hmin1 : ∀ v : ℂ, Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) v ≠ 0 →
      (v ∈ S ∨ ‖(1 : ℂ) + (s₁.im : ℂ) * Complex.I - v‖ ≤ δ) →
      Work.LinnikContract.lamOf q ρ₁ ≤ (1 - v.re) * L := by
    intro v hv hcase
    have himv : |v.im| ≤ 10 := by
      rcases hcase with hvS | hvwin
      · rw [hSdef] at hvS
        rcases Finset.mem_insert.mp hvS with h | h
        · rw [h, ← hγdef]
          rw [abs_le] at hγ1 ⊢
          exact ⟨by linarith only [hγ1.1, hγ1], by linarith only [hγ1.2, hγ1]⟩
        · rw [Finset.mem_singleton.mp h, Complex.conj_im, abs_neg, ← hγdef]
          rw [abs_le] at hγ1 ⊢
          exact ⟨by linarith only [hγ1.1, hγ1], by linarith only [hγ1.2, hγ1]⟩
      · have h2 : |s₁.im - v.im| ≤ 1 := by
          have h3 : |((1 : ℂ) + (s₁.im : ℂ) * Complex.I - v).im| ≤ 1 :=
            le_trans (Complex.abs_im_le_norm _) (le_trans hvwin (by linarith only [hδ1]))
          simpa using h3
        have h4 : |s₁.im| ≤ 1 := by
          have h : s₁.im = γ := by rw [hs₁def]; simp
          rw [h]; exact hγabs
        rw [abs_le] at h2 h4 ⊢
        constructor <;> linarith only [h2.1, h2.2, h4.1, h4.2, hδ1, hσdef, hσgt, hAlL, h2, h4]
    have hv' : Work.LinnikContract.zeroMult χ₁ v ≠ 0 := by rw [hzm_eq v]; exact hv
    have hmin' := hm1.2 χ₁ v hχ1ne hv' himv
    simpa [Work.LinnikContract.lamOf, hLdef] using hmin'
  have hmin3 : ∀ v : ℂ, Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) v ≠ 0 →
      (v ∈ S ∨ ‖(1 : ℂ) + (s₃.im : ℂ) * Complex.I - v‖ ≤ δ) →
      Work.LinnikContract.lamOf q ρ₁ ≤ (1 - v.re) * L := by
    intro v hv hcase
    have himv : |v.im| ≤ 10 := by
      rcases hcase with hvS | hvwin
      · rw [hSdef] at hvS
        rcases Finset.mem_insert.mp hvS with h | h
        · rw [h, ← hγdef]
          rw [abs_le] at hγ1 ⊢
          exact ⟨by linarith only [hγ1.1, hγ1], by linarith only [hγ1.2, hγ1]⟩
        · rw [Finset.mem_singleton.mp h, Complex.conj_im, abs_neg, ← hγdef]
          rw [abs_le] at hγ1 ⊢
          exact ⟨by linarith only [hγ1.1, hγ1], by linarith only [hγ1.2, hγ1]⟩
      · have h2 : |s₃.im - v.im| ≤ 1 := by
          have h3 : |((1 : ℂ) + (s₃.im : ℂ) * Complex.I - v).im| ≤ 1 :=
            le_trans (Complex.abs_im_le_norm _) (le_trans hvwin (by linarith only [hδ1]))
          simpa using h3
        have h4 : |s₃.im| ≤ 3 := by
          have h : s₃.im = 3 * γ := by rw [hs₃def]; simp
          rw [h]; rw [abs_le] at hγabs ⊢
          constructor <;> linarith only [hγabs.1, hγabs.2, hγabs]
        rw [abs_le] at h2 h4 ⊢
        constructor <;> linarith only [h2.1, h2.2, h4.1, h4.2, hδ1, hσdef, hσgt, hAlL, h2, h4]
    have hv' : Work.LinnikContract.zeroMult χ₁ v ≠ 0 := by rw [hzm_eq v]; exact hv
    have hmin' := hm1.2 χ₁ v hχ1ne hv' himv
    simpa [Work.LinnikContract.lamOf, hLdef] using hmin'
  have hK1 := HB95h2.keptExtractW (χ := χ₁.primitiveCharacter) hχs_ne hχs_prim
      (a := A) (lam₁ := Work.LinnikContract.lamOf q ρ₁) (L := L) (δ := δ) (s := s₁) (S := S)
      hLpos hApos hlam0 hδ0 hre1 hmin1
  have hK3 := HB95h2.keptExtractW (χ := χ₁.primitiveCharacter) hχs_ne hχs_prim
      (a := A) (lam₁ := Work.LinnikContract.lamOf q ρ₁) (L := L) (δ := δ) (s := s₃) (S := S)
      hLpos hApos hlam0 hδ0 hre3 hmin3
  -- ## the evaluation of the two kept sums
  have hSsum1 : (∑ u ∈ S, (Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ)
      * (P3 (((A + Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ) / ((s₁ - u) * (L : ℂ)))).re)
      = m * P3R 1 + m * Table4.P3AB α α T := by
    rw [hSdef, Finset.sum_pair (Ne.symm hconj_ne)]
    have h1 : (P3 (((A + Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ)
        / ((s₁ - ρ₁) * (L : ℂ)))).re = P3R 1 := by
      rw [reP3_eq_P3AB (x := A + Work.LinnikContract.lamOf q ρ₁) (y := α) (t := 0) d1,
        ← hαdef, Table4.P3AB_zero, div_self hαne]
    have h2 : (P3 (((A + Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ)
        / ((s₁ - starRingEnd ℂ ρ₁) * (L : ℂ)))).re = Table4.P3AB α α T := by
      rw [reP3_eq_P3AB (x := A + Work.LinnikContract.lamOf q ρ₁) (y := α) (t := T) d2, ← hαdef]
    rw [h1, h2, zeroMult_prim (χ₁.primitiveCharacter) hχs_sq, ← hzm_eq ρ₁, ← hmdef]
  have hSsum3 : (∑ u ∈ S, (Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ)
      * (P3 (((A + Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ) / ((s₃ - u) * (L : ℂ)))).re)
      = m * Table4.P3AB α α T + m * Table4.P3AB α α (2 * T) := by
    rw [hSdef, Finset.sum_pair (Ne.symm hconj_ne)]
    have h1 : (P3 (((A + Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ)
        / ((s₃ - ρ₁) * (L : ℂ)))).re = Table4.P3AB α α T := by
      rw [reP3_eq_P3AB (x := A + Work.LinnikContract.lamOf q ρ₁) (y := α) (t := T) d3, ← hαdef]
    have h2 : (P3 (((A + Work.LinnikContract.lamOf q ρ₁ : ℝ) : ℂ)
        / ((s₃ - starRingEnd ℂ ρ₁) * (L : ℂ)))).re = Table4.P3AB α α (2 * T) := by
      rw [reP3_eq_P3AB (x := A + Work.LinnikContract.lamOf q ρ₁) (y := α) (t := 2 * T) d4,
        ← hαdef]
    rw [h1, h2, zeroMult_prim (χ₁.primitiveCharacter) hχs_sq, ← hzm_eq ρ₁, ← hmdef]
  -- ## the pointwise bounds, with the kept sums kept explicit
  have hb0 : SigmaP3L q L 1 (σ : ℂ) A (Work.LinnikContract.lamOf q ρ₁)
      ≤ P3R (α / A) + (A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16) := by
    rw [← e0]
    exact hp0
  have hb2 : SigmaP3L q L 1 s₂ A (Work.LinnikContract.lamOf q ρ₁)
      ≤ Table4.P3AB α A T + (A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16) := by
    rw [← e2]
    exact hp2
  have hb4 : SigmaP3L q L 1 s₄ A (Work.LinnikContract.lamOf q ρ₁)
      ≤ Table4.P3AB α A (2 * T) + (A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16) := by
    rw [← e4]
    exact hp4
  have hb1 : SigmaP3L q L χ₁ s₁ A (Work.LinnikContract.lamOf q ρ₁)
      ≤ - Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₁ A
            (Work.LinnikContract.lamOf q ρ₁) δ S
        + (A + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε / 16 + ε / 16)
        + (A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16)
        + ((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S,
            (1 - Work.ZeroFreeTables.P9.nearInd s₁ δ u)
            * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ)
                * ((1 / (s₁ - u)).re))) := by
    linarith only [hi1, hm1', this, hNne]
  have hb3 : SigmaP3L q L χ₁ s₃ A (Work.LinnikContract.lamOf q ρ₁)
      ≤ - Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₃ A
            (Work.LinnikContract.lamOf q ρ₁) δ S
        + (A + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε / 16 + ε / 16)
        + (A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16)
        + ((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S,
            (1 - Work.ZeroFreeTables.P9.nearInd s₃ δ u)
            * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ)
                * ((1 / (s₃ - u)).re))) := by
    linarith only [hi3, hm3', this, hNne]
  have hExbound : ∀ (s : ℂ), s.re = 1 + A / L → |s.im| ≤ 4 →
      ((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S,
          (1 - Work.ZeroFreeTables.P9.nearInd s δ u)
          * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ)
              * ((1 / (s - u)).re)))
        ≤ ((A + Work.LinnikContract.lamOf q ρ₁) / L) * (16 * m / δ ^ 2) := by
    intro s hsre hsim
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hsum_le : (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s δ u)
        * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ)
            * ((1 / (s - u)).re))) ≤ ∑ u ∈ S, m * (8 / δ ^ 2) := by
      refine Finset.sum_le_sum (fun u hu => ?_)
      by_cases hzu : Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u = 0
      · rw [hzu]; simp only [Nat.cast_zero, mul_zero, zero_mul]
        exact mul_nonneg (by linarith only [hm_ge1]) (by positivity)
      · have hzu_pos : 0 < (Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hzu
        by_cases hnear : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
        · rw [Work.ZeroFreeTables.P9.nearInd_eq_ite, if_pos hnear]
          simp only [sub_self, zero_mul]
          exact mul_nonneg (by linarith only [hm_ge1]) (by positivity)
        · rw [Work.ZeroFreeTables.P9.nearInd_eq_ite, if_neg hnear]
          have hfar : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ := lt_of_not_ge hnear
          have hu' : u = ρ₁ ∨ u = starRingEnd ℂ ρ₁ := by
            rw [hSdef] at hu
            rcases Finset.mem_insert.mp hu with h | h
            · exact Or.inl h
            · exact Or.inr (Finset.mem_singleton.mp h)
          have hure : u.re < 1 := by
            rcases hu' with h | h
            · rw [h]; exact hρ₁re_lt
            · rw [h, Complex.conj_re]; exact hρ₁re_lt
          have hrec := re_inv_le_of_far hδ0 hδ1.le hApos hLpos hAlL hsre hure hfar
          have hle : (Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) ≤ m := by
            rcases hu' with h | h
            · rw [h, ← hzm_eq ρ₁, ← hmdef]
            · rw [h, zeroMult_prim (χ₁.primitiveCharacter) hχs_sq, ← hzm_eq ρ₁, ← hmdef]
          simp only [sub_zero, one_mul]
          exact le_trans (mul_le_mul_of_nonneg_left hrec hzu_pos.le)
            (mul_le_mul_of_nonneg_right hle (by positivity))
    have hconst : (∑ u ∈ S, m * (8 / δ ^ 2)) = 16 * m / δ ^ 2 := by
      rw [hSdef, Finset.sum_pair (Ne.symm hconj_ne)]
      have h2 : m * (8 / δ ^ 2) + m * (8 / δ ^ 2) = 16 * m / δ ^ 2 := by
        field_simp
        ring
      rw [h2]
    linarith only [hsum_le, hconst, hNne]
  have hEx1 : ((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S,
        (1 - Work.ZeroFreeTables.P9.nearInd s₁ δ u)
        * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ)
            * ((1 / (s₁ - u)).re)))
      ≤ ((A + Work.LinnikContract.lamOf q ρ₁) / L) * (16 * m / δ ^ 2) :=
    hExbound s₁ hre1 him1
  have hEx3 : ((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S,
        (1 - Work.ZeroFreeTables.P9.nearInd s₃ δ u)
        * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ)
            * ((1 / (s₃ - u)).re)))
      ≤ ((A + Work.LinnikContract.lamOf q ρ₁) / L) * (16 * m / δ ^ 2) :=
    hExbound s₃ hre3 him3
  have hK1' : m * P3R 1 + m * Table4.P3AB α α T ≤ Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₁ A (Work.LinnikContract.lamOf q ρ₁) δ S := by
    rw [← hSsum1]
    exact hK1
  have hK3' : m * Table4.P3AB α α T + m * Table4.P3AB α α (2 * T) ≤ Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₃ A (Work.LinnikContract.lamOf q ρ₁) δ S := by
    rw [← hSsum3]
    exact hK3
  have hP1 : P3R 1 = 8 / 3 := by norm_num [P3R]
  have hK1b : m * ((8 : ℝ) / 3) + m * Table4.P3AB α α T ≤ Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₁ A (Work.LinnikContract.lamOf q ρ₁) δ S := by
    rw [← hP1]
    exact hK1'
  have hT : 14900 * Table4.P3AB α A T + 1250 * Table4.P3AB α A (2 * T) ≤ 30480 * Table4.P3AB α α T + 6000 * Table4.P3AB α α (2 * T) := by
    have h := h2_Tstep (lam := Work.LinnikContract.lamOf q ρ₁) (T := T) hlam0 hle
    rw [← hAdef, ← hαdef] at h
    exact h
  -- ## the raw chain out of the pointwise inequality
  have hraw : 0 ≤ 14379 * (P3R (α / A) + (A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16)) + 24480 * (- Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₁ A (Work.LinnikContract.lamOf q ρ₁) δ S + (A + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε / 16 + ε / 16) + (A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16) + (((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s₁ δ u) * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₁ - u)).re))))) + 14900 * (Table4.P3AB α A T + (A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16)) + 6000 * (- Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₃ A (Work.LinnikContract.lamOf q ρ₁) δ S + (A + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε / 16 + ε / 16) + (A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16) + (((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s₃ δ u) * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₃ - u)).re))))) + 1250 * (Table4.P3AB α A (2 * T) + (A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16)) := by
    have t0 := mul_le_mul_of_nonneg_left hb0 (show (0:ℝ) ≤ 14379 by norm_num)
    have t1 := mul_le_mul_of_nonneg_left hb1 (show (0:ℝ) ≤ 24480 by norm_num)
    have t2 := mul_le_mul_of_nonneg_left hb2 (show (0:ℝ) ≤ 14900 by norm_num)
    have t3 := mul_le_mul_of_nonneg_left hb3 (show (0:ℝ) ≤ 6000 by norm_num)
    have t4 := mul_le_mul_of_nonneg_left hb4 (show (0:ℝ) ≤ 1250 by norm_num)
    exact le_trans hpt (add_le_add (add_le_add (add_le_add (add_le_add t0 t1) t2) t3) t4)
  -- ## stage 2: the `T`-bracket is non-positive
  have hQ1 : Table4.P3AB α α T ≤ m * Table4.P3AB α α T := by nlinarith only [hW1nn, hm_ge1]
  have hQ2 : Table4.P3AB α α (2 * T) ≤ m * Table4.P3AB α α (2 * T) := by nlinarith only [hW2nn, hm_ge1]
  have hbracket : 24480 * (m * ((8 : ℝ) / 3) - Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₁ A (Work.LinnikContract.lamOf q ρ₁) δ S) + (-6000 * Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₃ A (Work.LinnikContract.lamOf q ρ₁) δ S) + (14900 * Table4.P3AB α A T + 1250 * Table4.P3AB α A (2 * T)) ≤ 0 := by
    have q1 : m * ((8 : ℝ) / 3) - Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₁ A (Work.LinnikContract.lamOf q ρ₁) δ S ≤ -(m * Table4.P3AB α α T) := by linarith only [hK1b]
    have q3 : - Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₃ A (Work.LinnikContract.lamOf q ρ₁) δ S ≤ -(m * Table4.P3AB α α T) - m * Table4.P3AB α α (2 * T) := by linarith only [hK3']
    have s1 : 24480 * (m * ((8 : ℝ) / 3) - Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₁ A (Work.LinnikContract.lamOf q ρ₁) δ S) ≤ 24480 * (-(m * Table4.P3AB α α T)) :=
      mul_le_mul_of_nonneg_left q1 (show (0 : ℝ) ≤ 24480 by norm_num)
    have s3 : -6000 * Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₃ A (Work.LinnikContract.lamOf q ρ₁) δ S ≤ -6000 * (m * Table4.P3AB α α T) - 6000 * (m * Table4.P3AB α α (2 * T)) := by
      have h := mul_le_mul_of_nonneg_left q3 (show (0 : ℝ) ≤ 6000 by norm_num)
      linarith only [h]
    have sQ : 30480 * Table4.P3AB α α T ≤ 30480 * (m * Table4.P3AB α α T) := mul_le_mul_of_nonneg_left hQ1 (by norm_num)
    have sQ2 : 6000 * Table4.P3AB α α (2 * T) ≤ 6000 * (m * Table4.P3AB α α (2 * T)) := mul_le_mul_of_nonneg_left hQ2 (by norm_num)
    have step1 : 24480 * (m * ((8 : ℝ) / 3) - Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₁ A (Work.LinnikContract.lamOf q ρ₁) δ S) + (-6000 * Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₃ A (Work.LinnikContract.lamOf q ρ₁) δ S) + (14900 * Table4.P3AB α A T + 1250 * Table4.P3AB α A (2 * T))
        ≤ (24480 * (-(m * Table4.P3AB α α T)) + (-6000 * (m * Table4.P3AB α α T) - 6000 * (m * Table4.P3AB α α (2 * T)))) + (30480 * Table4.P3AB α α T + 6000 * Table4.P3AB α α (2 * T)) :=
      add_le_add (add_le_add s1 s3) hT
    have step2 : (24480 * (-(m * Table4.P3AB α α T)) + (-6000 * (m * Table4.P3AB α α T) - 6000 * (m * Table4.P3AB α α (2 * T)))) + (30480 * Table4.P3AB α α T + 6000 * Table4.P3AB α α (2 * T))
        ≤ (24480 * (-(m * Table4.P3AB α α T)) + (-6000 * (m * Table4.P3AB α α T) - 6000 * (m * Table4.P3AB α α (2 * T)))) + (30480 * (m * Table4.P3AB α α T) + 6000 * (m * Table4.P3AB α α (2 * T))) :=
      add_le_add (le_refl _) (add_le_add sQ sQ2)
    have step3 : (24480 * (-(m * Table4.P3AB α α T)) + (-6000 * (m * Table4.P3AB α α T) - 6000 * (m * Table4.P3AB α α (2 * T))))
        + (30480 * (m * Table4.P3AB α α T) + 6000 * (m * Table4.P3AB α α (2 * T))) = 0 := by ring
    exact le_trans step1 (le_trans step2 (le_of_eq step3))
  have hstage2 : 0 ≤ 14379 * P3R (α / A) - 24480 * (m * ((8 : ℝ) / 3)) + 30480 * ((A + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε / 16 + ε / 16)) + 61009 * ((A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16)) + (24480 * (((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s₁ δ u) * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₁ - u)).re)))) + 6000 * (((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s₃ δ u) * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₃ - u)).re))))) := by
    have hid : 14379 * (P3R (α / A) + (A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16)) + 24480 * (- Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₁ A (Work.LinnikContract.lamOf q ρ₁) δ S + (A + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε / 16 + ε / 16) + (A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16) + (((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s₁ δ u) * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₁ - u)).re))))) + 14900 * (Table4.P3AB α A T + (A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16)) + 6000 * (- Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₃ A (Work.LinnikContract.lamOf q ρ₁) δ S + (A + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε / 16 + ε / 16) + (A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16) + (((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s₃ δ u) * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₃ - u)).re))))) + 1250 * (Table4.P3AB α A (2 * T) + (A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16)) = (14379 * P3R (α / A) - 24480 * (m * ((8 : ℝ) / 3)) + 30480 * ((A + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε / 16 + ε / 16)) + 61009 * ((A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16)) + (24480 * (((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s₁ δ u) * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₁ - u)).re)))) + 6000 * (((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s₃ δ u) * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₃ - u)).re))))) + 24480 * (m * ((8 : ℝ) / 3) - Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₁ A (Work.LinnikContract.lamOf q ρ₁) δ S) + (-6000 * Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₃ A (Work.LinnikContract.lamOf q ρ₁) δ S) + (14900 * Table4.P3AB α A T + 1250 * Table4.P3AB α A (2 * T))) := by ring
    rw [hid] at hraw
    have hneg : (0 : ℝ) ≤ -(24480 * (m * ((8 : ℝ) / 3) - Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₁ A (Work.LinnikContract.lamOf q ρ₁) δ S) + (-6000 * Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₃ A (Work.LinnikContract.lamOf q ρ₁) δ S) + (14900 * Table4.P3AB α A T + 1250 * Table4.P3AB α A (2 * T))) := neg_nonneg.mpr hbracket
    have hsum2 : (0 : ℝ) + 0 ≤ (14379 * P3R (α / A) - 24480 * (m * ((8 : ℝ) / 3)) + 30480 * ((A + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε / 16 + ε / 16)) + 61009 * ((A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16)) + (24480 * (((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s₁ δ u) * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₁ - u)).re)))) + 6000 * (((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s₃ δ u) * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₃ - u)).re))))) + 24480 * (m * ((8 : ℝ) / 3) - Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₁ A (Work.LinnikContract.lamOf q ρ₁) δ S) + (-6000 * Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₃ A (Work.LinnikContract.lamOf q ρ₁) δ S) + (14900 * Table4.P3AB α A T + 1250 * Table4.P3AB α A (2 * T))) + -(24480 * (m * ((8 : ℝ) / 3) - Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₁ A (Work.LinnikContract.lamOf q ρ₁) δ S) + (-6000 * Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₃ A (Work.LinnikContract.lamOf q ρ₁) δ S) + (14900 * Table4.P3AB α A T + 1250 * Table4.P3AB α A (2 * T))) := add_le_add hraw hneg
    have hcan : (14379 * P3R (α / A) - 24480 * (m * ((8 : ℝ) / 3)) + 30480 * ((A + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε / 16 + ε / 16)) + 61009 * ((A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16)) + (24480 * (((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s₁ δ u) * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₁ - u)).re)))) + 6000 * (((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s₃ δ u) * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₃ - u)).re))))) + 24480 * (m * ((8 : ℝ) / 3) - Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₁ A (Work.LinnikContract.lamOf q ρ₁) δ S) + (-6000 * Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₃ A (Work.LinnikContract.lamOf q ρ₁) δ S) + (14900 * Table4.P3AB α A T + 1250 * Table4.P3AB α A (2 * T))) + -(24480 * (m * ((8 : ℝ) / 3) - Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₁ A (Work.LinnikContract.lamOf q ρ₁) δ S) + (-6000 * Table4.keptP3Sum χ₁.conductor L (χ₁.primitiveCharacter) s₃ A (Work.LinnikContract.lamOf q ρ₁) δ S) + (14900 * Table4.P3AB α A T + 1250 * Table4.P3AB α A (2 * T))) = 14379 * P3R (α / A) - 24480 * (m * ((8 : ℝ) / 3)) + 30480 * ((A + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε / 16 + ε / 16)) + 61009 * ((A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16)) + (24480 * (((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s₁ δ u) * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₁ - u)).re)))) + 6000 * (((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s₃ δ u) * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₃ - u)).re))))) := by ring
    rw [hcan] at hsum2
    simpa using hsum2
  have hα4 : A + Work.LinnikContract.lamOf q ρ₁ ≤ 4 := by rw [← hαdef]; exact hαle4
  have hαnn : 0 < A + Work.LinnikContract.lamOf q ρ₁ := by rw [← hαdef]; exact hαpos
  have hbound : 24480 * ((((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s₁ δ u) * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₁ - u)).re))))) + 6000 * ((((A + Work.LinnikContract.lamOf q ρ₁) / L) * (∑ u ∈ S, (1 - Work.ZeroFreeTables.P9.nearInd s₃ δ u) * ((Work.LinnikContract.zeroMult (χ₁.primitiveCharacter) u : ℝ) * ((1 / (s₃ - u)).re))))) ≤ 65280 * (m - 1) + 22856 * (A + Work.LinnikContract.lamOf q ρ₁) * ε := by
    have hδ2L : 1000 ≤ δ ^ 2 * L := by
      have h := (div_le_iff₀ (show (0:ℝ) < δ ^ 2 by positivity)).mp hLδ
      rw [mul_comm L (δ ^ 2)] at h
      exact h
    have hδ2εL : 1000 ≤ δ ^ 2 * ε * L := by
      have h := (div_le_iff₀ (show (0:ℝ) < δ ^ 2 * ε by positivity)).mp hLε
      rw [mul_comm L (δ ^ 2 * ε)] at h
      exact h
    exact hBnum_aux hαnn hLpos hδ0 hε hα4 hm_ge1 ⟨_, hmdef⟩ hEx1 hEx3 hδ2L hδ2εL
  have hfinalbound : 0 ≤ 14379 * P3R (α / A) - 24480 * (m * ((8 : ℝ) / 3)) + 30480 * ((A + Work.LinnikContract.lamOf q ρ₁) * (1 / 8 + ε / 16 + ε / 16)) + 61009 * ((A + Work.LinnikContract.lamOf q ρ₁) * (ε / 16)) + (65280 * (m - 1) + 22856 * (A + Work.LinnikContract.lamOf q ρ₁) * ε) := by
    exact le_trans hstage2 (add_le_add (le_refl _) hbound)
  have hgoal : 0 ≤ 14379 * P3R (α / A) - 24480 * P3R 1 + 30480 * α * (1 / 8 + ε) := by
    rw [hP1]
    rw [← hαdef] at hfinalbound
    have hrew : 14379 * P3R (α / A) - 24480 * (m * ((8 : ℝ) / 3)) + 30480 * (α * (1 / 8 + ε / 16 + ε / 16)) + 61009 * (α * (ε / 16)) + (65280 * (m - 1) + 22856 * α * ε) = 14379 * P3R (α / A) - 24480 * ((8 : ℝ) / 3) + 30480 * α * (1 / 8 + ε) - (15 / 16) * α * ε := by ring
    rw [hrew] at hfinalbound
    have hαε : 0 ≤ (15 / 16) * α * ε := by positivity
    have hsum := add_nonneg hfinalbound hαε
    rw [sub_add_cancel] at hsum
    exact hsum
  exact hgoal

end Work.ZeroFreeTables
