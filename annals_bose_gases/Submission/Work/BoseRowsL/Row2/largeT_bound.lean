import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Submission.Work.BoseBoxFock.KinRowQuant
import Submission.Work.BoseBoxFock.LatVec
import Submission.Work.BoseBoxFock.sqrtKin_diffForm
import Submission.Work.BoseRowsL.Row2.gauss_integrals
import Submission.Work.BoseRowsL.Row2.lattice_gauss_sum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.Row2.largeT_bound`

The large-`t` row of the lattice/continuum comparison for the cosine transform `chat h` of an
`L¹`-function `h`:

`∫_{t > ℓ²} |(ℓ³)⁻¹(Σ_n chat h(p_n)e^{−t‖p_n‖²} − chat h 0) − (2π)⁻³∫_p chat h(p)e^{−t‖p‖²}|
  ≤ 100 ℓ⁻¹ ∫|h|`,

where `p_n = kmomInt ℓ n = 2πn/ℓ` is the box lattice.

The proof is elementary and needs **no** Poisson summation: for `t ≥ ℓ²` the lattice sum is
dominated by the Gaussian tail `75 e^{−4π²t/ℓ²}` (`lattice_gauss_sum`), while the continuum
integral is bounded by `∫|h| · (π/t)^{3/2}` (the Gaussian integral of `gauss_integrals`, since
`|chat h| ≤ ∫|h|`).  Both bounds are integrable in `t`, and the two remaining constants are
`75/(4π²) ≤ 18.75` and `1/(4π^{3/2}) ≤ 1/4`, so the total error constant is below `19`.
-/

namespace Work.BoseRowsL.Row2

open MeasureTheory Set
open scoped BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## 1. Lattice bookkeeping -/

/-- `Work.BoseB4.vec n = 2π • zvec n`. -/
lemma vec_eq_smul_zvec (n : Fin 3 → ℤ) :
    Work.BoseB4.vec n = (2 * Real.pi) • Work.BoseRowsFS.zvec n := by
  ext i; simp [Work.BoseB4.vec, Work.BoseRowsFS.zvec]

/-- `kmomInt ℓ n = (2π/ℓ) • zvec n`. -/
lemma kmomInt_eq_smul_zvec (ℓ : ℝ) (n : Fin 3 → ℤ) :
    Work.BoseBoxFock.kmomInt ℓ n = (2 * Real.pi * ℓ⁻¹) • Work.BoseRowsFS.zvec n := by
  rw [Work.BoseBoxFock.kmomInt, vec_eq_smul_zvec, smul_smul, mul_comm]

/-- The zero label is the zero momentum. -/
lemma kmomInt_zero (ℓ : ℝ) : Work.BoseBoxFock.kmomInt ℓ 0 = 0 := by
  rw [Work.BoseBoxFock.kmomInt]
  have h : Work.BoseB4.vec (0 : Fin 3 → ℤ) = 0 := by ext i; simp [Work.BoseB4.vec]
  rw [h, smul_zero]

/-- The norm of the lattice momentum. -/
lemma norm_kmomInt_eq (ℓ : ℝ) (hℓ : 0 < ℓ) (n : Fin 3 → ℤ) :
    ‖Work.BoseBoxFock.kmomInt ℓ n‖ = 2 * Real.pi * ℓ⁻¹ * ‖Work.BoseRowsFS.zvec n‖ := by
  rw [kmomInt_eq_smul_zvec, norm_smul, Real.norm_of_nonneg (by positivity)]

/-- The Gaussian weight of the lattice momentum in terms of `zvec`. -/
lemma exp_kmomInt_eq (ℓ : ℝ) (hℓ : 0 < ℓ) (t : ℝ) (n : Fin 3 → ℤ) :
    Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))
      = Real.exp (-((4 * Real.pi ^ 2 / ℓ ^ 2 * t) * ‖Work.BoseRowsFS.zvec n‖ ^ 2)) := by
  congr 1
  rw [norm_kmomInt_eq ℓ hℓ n]
  field_simp
  ring

/-- A nonzero lattice label has norm at least `1`. -/
lemma one_le_norm_zvec {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    1 ≤ ‖Work.BoseRowsFS.zvec n‖ := by
  have hsum : ‖Work.BoseRowsFS.zvec n‖ ^ 2 = ∑ i, ((n i : ℤ) : ℝ) ^ 2 := by
    rw [zvec_eq_vecZ, Work.BoseRowsFS.norm_vecZ_sq]
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, n i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hn (funext h)
  have h1 : (1 : ℝ) ≤ ((n i : ℤ) : ℝ) ^ 2 := by
    have h2 : (1 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast Int.one_le_abs hi
    rw [Int.cast_abs] at h2
    nlinarith [h2, abs_nonneg (((n i : ℤ) : ℝ)), sq_abs (((n i : ℤ) : ℝ))]
  have h3 : (1 : ℝ) ≤ ∑ j, ((n j : ℤ) : ℝ) ^ 2 :=
    le_trans h1 (Finset.single_le_sum (f := fun j : Fin 3 => ((n j : ℤ) : ℝ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  have h4 : (1 : ℝ) ≤ Real.sqrt (‖Work.BoseRowsFS.zvec n‖ ^ 2) := by
    rw [hsum]
    exact (Real.le_sqrt zero_le_one (Finset.sum_nonneg (fun j _ => sq_nonneg _))).mpr
      (by simpa using h3)
  rwa [Real.sqrt_sq (norm_nonneg _)] at h4

/-! ## 2. The cosine transform of an `L¹`-function is bounded by its `L¹`-norm -/

/-- `|chat h p| ≤ ∫|h|` for every `p`. -/
lemma chat_abs_le (h : ℝ³ → ℝ) (p : ℝ³) :
    |Work.BoseFixR.chat h p| ≤ ∫ x : ℝ³, |h x| := by
  have h1 : |Work.BoseFixR.chat h p| ≤
      ‖Submission.BoseGases.kinFT (fun y : ℝ³ => ((h y : ℝ) : ℂ)) p‖ := by
    rw [Work.BoseFixR.chat]
    exact Complex.abs_re_le_norm _
  have h2 : ‖Submission.BoseGases.kinFT (fun y : ℝ³ => ((h y : ℝ) : ℂ)) p‖
      ≤ ∫ y : ℝ³, ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((h y : ℝ) : ℂ)‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  have h3 : (∫ y : ℝ³, ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((h y : ℝ) : ℂ)‖)
      = ∫ x : ℝ³, |h x| := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    show ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((h y : ℝ) : ℂ)‖ = |h y|
    have hre : (-(Complex.I * (inner ℝ p y : ℂ))).re = 0 := by simp
    rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
  linarith [h1, h2, h3.le]

/-! ## 3. Lattice Gaussian sums -/

/-- Summability of the Gaussian on `zvec ℤ³`. -/
lemma summable_zvec_gauss {c : ℝ} (hc : 0 < c) :
    Summable (fun n : Fin 3 → ℤ => Real.exp (-(c * ‖Work.BoseRowsFS.zvec n‖ ^ 2))) := by
  have h := Work.BoseRowsFS.summable_pi3_exp_neg_mul_normSq hc
  exact h.congr (fun n => by rw [zvec_eq_vecZ])

/-- The lattice Gaussian tail over the non-zero labels. -/
lemma tsum_ne_zero_exp_le {a : ℝ} (ha : 1 ≤ a) :
    (∑' n : Fin 3 → ℤ, if n = 0 then 0 else Real.exp (-(a * ‖Work.BoseRowsFS.zvec n‖ ^ 2)))
      ≤ 75 * Real.exp (-a) := by
  have hsumm := summable_zvec_gauss (lt_of_lt_of_le zero_lt_one ha)
  have hsplit := hsumm.tsum_eq_add_tsum_ite (0 : Fin 3 → ℤ)
  have h0 : Real.exp (-(a * ‖Work.BoseRowsFS.zvec (0 : Fin 3 → ℤ)‖ ^ 2)) = 1 := by
    have hz : Work.BoseRowsFS.zvec (0 : Fin 3 → ℤ) = 0 := by
      ext i; simp [Work.BoseRowsFS.zvec]
    simp [hz]
  rw [h0] at hsplit
  have hbound := lattice_gauss_sum.1 a ha
  linarith

/-- The Gaussian tail of the box lattice for `t ≥ ℓ²`. -/
lemma lattice_sum_le (ℓ : ℝ) (hℓ : 0 < ℓ) {t : ℝ} (ht : ℓ ^ 2 ≤ t) :
    (∑' n : Fin 3 → ℤ, if n = 0 then 0
        else Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2)))
      ≤ 75 * Real.exp (-(4 * Real.pi ^ 2 / ℓ ^ 2 * t)) := by
  have ha : 1 ≤ 4 * Real.pi ^ 2 / ℓ ^ 2 * t := by
    have ht' : 1 ≤ t / ℓ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      simpa using ht
    have hsplit : 4 * Real.pi ^ 2 / ℓ ^ 2 * t = 4 * Real.pi ^ 2 * (t / ℓ ^ 2) := by
      rw [div_mul_eq_mul_div, mul_div_assoc]
    have hp : (36 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have hmul : (36 : ℝ) * 1 ≤ 4 * Real.pi ^ 2 * (t / ℓ ^ 2) :=
      mul_le_mul hp ht' (by norm_num) (by positivity)
    rw [hsplit]
    linarith
  refine le_trans (le_of_eq (tsum_congr (fun n => ?_))) (tsum_ne_zero_exp_le ha)
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn, if_neg hn, exp_kmomInt_eq ℓ hℓ t n]

/-! ## 4. The Gaussian integral on `ℝ³` and the continuum bound -/

/-- Integrability of the Gaussian on `ℝ³`. -/
lemma gaussian_integrable_3 (t : ℝ) (ht : 0 < t) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) => Real.exp (-(t * ‖p‖ ^ 2))) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℝ (Fin 3)) (b := (t : ℂ)) (by simpa using ht) (0 : ℂ)
    (0 : EuclideanSpace ℝ (Fin 3))
  refine h.re.congr (Filter.Eventually.of_forall (fun v => ?_))
  show (Complex.exp (-(t : ℂ) * (‖v‖ ^ 2 : ℂ)
      + 0 * (inner ℝ (0 : EuclideanSpace ℝ (Fin 3)) v : ℂ))).re = Real.exp (-(t * ‖v‖ ^ 2))
  have hz : -(t : ℂ) * (‖v‖ ^ 2 : ℂ)
        + 0 * (inner ℝ (0 : EuclideanSpace ℝ (Fin 3)) v : ℂ)
      = ((-(t * ‖v‖ ^ 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hz, Complex.exp_re, Complex.ofReal_re, Complex.ofReal_im, Real.cos_zero, mul_one]

/-- `∫_{t>a} e^{−ct} = e^{−ca}/c` for `c > 0`.

Renamed (2026-10-07) from `integral_exp_neg_mul_Ioi` to avoid a duplicate-declaration clash
with the identically-named helper of `Submission.Work.BoseRowsL.Row2.heatFubini`: the two
modules are both imported by `Row2/omegaLatticeRow_of_interface.lean`, and Lean rejects a
name declared in two modules of one import cone.  No use site outside this file existed. -/
lemma largeT_exp_neg_mul_Ioi {cc a : ℝ} (hc : 0 < cc) :
    ∫ t in Set.Ioi a, Real.exp (-(cc * t)) = Real.exp (-(cc * a)) / cc := by
  have h : ∫ t in Set.Ioi a, Real.exp ((-cc) * t) = -Real.exp ((-cc) * a) / (-cc) :=
    integral_exp_mul_Ioi (by linarith) a
  rw [show (fun t : ℝ => Real.exp (-(cc * t))) = (fun t : ℝ => Real.exp ((-cc) * t)) from
    funext (fun t => by rw [neg_mul])] at *
  rw [h]
  ring

/-- The continuum integral term is bounded by `∫|h| · (π/t)^{3/2}`. -/
lemma chat_integral_bound {h : ℝ³ → ℝ} {t : ℝ} (ht : 0 < t) :
    |∫ p : ℝ³, Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2))|
      ≤ (∫ x : ℝ³, |h x|) * Real.pi ^ (3 / 2 : ℝ) * t ^ (-(3 : ℝ) / 2) := by
  have hg : MeasureTheory.Integrable (fun p : ℝ³ =>
      (∫ x : ℝ³, |h x|) * Real.exp (-(t * ‖p‖ ^ 2))) :=
    (gaussian_integrable_3 t ht).const_mul _
  have hnorm : |∫ p : ℝ³, Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2))|
      ≤ ∫ p : ℝ³, ‖Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2))‖ := by
    have := MeasureTheory.norm_integral_le_integral_norm (μ := volume)
      (fun p : ℝ³ => Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2)))
    simpa [Real.norm_eq_abs] using this
  have heq : (∫ p : ℝ³, ‖Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2))‖)
      = ∫ p : ℝ³, |Work.BoseFixR.chat h p| * Real.exp (-(t * ‖p‖ ^ 2)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    show ‖Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2))‖
      = |Work.BoseFixR.chat h p| * Real.exp (-(t * ‖p‖ ^ 2))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hmono : (∫ p : ℝ³, |Work.BoseFixR.chat h p| * Real.exp (-(t * ‖p‖ ^ 2)))
      ≤ ∫ p : ℝ³, (∫ x : ℝ³, |h x|) * Real.exp (-(t * ‖p‖ ^ 2)) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun p => by positivity)) hg
      (Filter.Eventually.of_forall
        (fun p => mul_le_mul_of_nonneg_right (chat_abs_le h p) (Real.exp_pos _).le))
  have hval : (∫ p : ℝ³, (∫ x : ℝ³, |h x|) * Real.exp (-(t * ‖p‖ ^ 2)))
      = (∫ x : ℝ³, |h x|) * (Real.pi / t) ^ (3 / 2 : ℝ) := by
    rw [MeasureTheory.integral_const_mul, gauss_integrals.2 t ht]
  have hrpow : (∫ x : ℝ³, |h x|) * (Real.pi / t) ^ (3 / 2 : ℝ)
      = (∫ x : ℝ³, |h x|) * Real.pi ^ (3 / 2 : ℝ) * t ^ (-(3 : ℝ) / 2) := by
    rw [Real.div_rpow Real.pi_pos.le ht.le, div_eq_mul_inv]
    have h1 : (-(3 : ℝ) / 2) = -(3 / 2 : ℝ) := by norm_num
    rw [show (t ^ (3 / 2 : ℝ))⁻¹ = t ^ (-(3 : ℝ) / 2) by
      rw [h1, ← Real.rpow_neg ht.le (3 / 2 : ℝ)]]
    ring
  linarith [hnorm, heq.le, hmono, hval.le, hval.ge, hrpow.le, hrpow.ge]

/-! ## 5. The lattice-sum bound at `t ≥ ℓ²` -/

/-- For `t ≥ ℓ²` the lattice sum `Σ_n chat h(p_n)e^{−t‖p_n‖²} − chat h 0` is bounded by
`∫|h| · 75 e^{−4π²t/ℓ²}`. -/
lemma chat_sum_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    {t : ℝ} (ht : ℓ ^ 2 ≤ t) :
    |(∑' n : Fin 3 → ℤ, Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n)
        * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))) - Work.BoseFixR.chat h 0|
      ≤ (∫ x : ℝ³, |h x|) * (75 * Real.exp (-(4 * Real.pi ^ 2 / ℓ ^ 2 * t))) := by
  set W : ℝ := ∫ x : ℝ³, |h x| with hW
  have hWnn : 0 ≤ W := by rw [hW]; exact integral_nonneg (fun x => abs_nonneg (h x))
  have hchat : ∀ p : ℝ³, |Work.BoseFixR.chat h p| ≤ W := by
    intro p; rw [hW]; exact chat_abs_le h p
  set f : (Fin 3 → ℤ) → ℝ := fun n => Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n)
      * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2)) with hf
  have hsumm_gauss : Summable (fun n : Fin 3 → ℤ =>
      Real.exp (-((4 * Real.pi ^ 2 / ℓ ^ 2 * t) * ‖Work.BoseRowsFS.zvec n‖ ^ 2))) :=
    summable_zvec_gauss (c := 4 * Real.pi ^ 2 / ℓ ^ 2 * t) (by
      have htpos : (0 : ℝ) < t := lt_of_lt_of_le (by positivity) ht
      positivity)
  have hsumm : Summable f := by
    refine Summable.of_norm_bounded
      (g := fun n : Fin 3 → ℤ =>
        W * Real.exp (-((4 * Real.pi ^ 2 / ℓ ^ 2 * t) * ‖Work.BoseRowsFS.zvec n‖ ^ 2)))
      (hsumm_gauss.mul_left W) ?_
    intro n
    rw [hf, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      exp_kmomInt_eq ℓ hℓ t n]
    exact mul_le_mul_of_nonneg_right (hchat _) (Real.exp_pos _).le
  have hf0 : f 0 = Work.BoseFixR.chat h 0 := by
    rw [hf]
    simp [kmomInt_zero]
  have hsplit := hsumm.tsum_eq_add_tsum_ite (0 : Fin 3 → ℤ)
  rw [hf0] at hsplit
  have h1 : (∑' n : Fin 3 → ℤ, f n) - Work.BoseFixR.chat h 0
      = ∑' n : Fin 3 → ℤ, (if n = 0 then 0 else f n) := by linarith
  rw [h1]
  have hsumm_abs : Summable (fun n : Fin 3 → ℤ => |f n|) := Summable.abs hsumm
  have hB : Summable (fun n : Fin 3 → ℤ => if n = 0 then 0 else |f n|) :=
    Summable.of_nonneg_of_le
      (fun n => by
        split_ifs with hn
        · positivity
        · exact abs_nonneg _)
      (fun n => by
        split_ifs with hn
        · positivity
        · exact le_rfl) hsumm_abs
  have hC : Summable (fun n : Fin 3 → ℤ =>
      if n = 0 then 0 else W * Real.exp (-((4 * Real.pi ^ 2 / ℓ ^ 2 * t) * ‖Work.BoseRowsFS.zvec n‖ ^ 2))) :=
    Summable.of_nonneg_of_le
      (fun n => by
        split_ifs with hn
        · positivity
        · exact mul_nonneg hWnn (Real.exp_pos _).le)
      (fun n => by
        split_ifs with hn
        · positivity
        · exact le_rfl)
      (hsumm_gauss.mul_left W)
  have hD : Summable (fun n : Fin 3 → ℤ =>
      if n = 0 then 0 else Real.exp (-((4 * Real.pi ^ 2 / ℓ ^ 2 * t) * ‖Work.BoseRowsFS.zvec n‖ ^ 2))) :=
    Summable.of_nonneg_of_le
      (fun n => by
        split_ifs with hn
        · positivity
        · exact (Real.exp_pos _).le)
      (fun n => by
        split_ifs with hn
        · positivity
        · exact le_rfl)
      hsumm_gauss
  have hstep1 : |∑' n : Fin 3 → ℤ, (if n = 0 then 0 else f n)|
      ≤ ∑' n : Fin 3 → ℤ, |if n = 0 then 0 else f n| := by
    have hnorm : Summable (fun n : Fin 3 → ℤ => ‖if n = 0 then 0 else f n‖) :=
      hB.congr (fun n => by
        split_ifs with hn
        · simp
        · rw [Real.norm_eq_abs])
    have h := norm_tsum_le_tsum_norm hnorm
    simpa [Real.norm_eq_abs] using h
  have hstep2 : (∑' n : Fin 3 → ℤ, |if n = 0 then 0 else f n|)
      = ∑' n : Fin 3 → ℤ, (if n = 0 then 0 else |f n|) := by
    refine tsum_congr (fun n => ?_)
    split_ifs with hn
    · exact abs_zero
    · rfl
  have hstep3 : (∑' n : Fin 3 → ℤ, (if n = 0 then 0 else |f n|))
      ≤ ∑' n : Fin 3 → ℤ, (if n = 0 then 0 else
          W * Real.exp (-((4 * Real.pi ^ 2 / ℓ ^ 2 * t) * ‖Work.BoseRowsFS.zvec n‖ ^ 2))) := by
    refine Summable.tsum_le_tsum (fun n => ?_) hB hC
    split_ifs with hn
    · positivity
    · have hfn : f n = Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n)
          * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2)) := rfl
      rw [hfn, abs_mul, abs_of_pos (Real.exp_pos _), exp_kmomInt_eq ℓ hℓ t n]
      exact mul_le_mul_of_nonneg_right (hchat _) (Real.exp_pos _).le
  have hstep4 : (∑' n : Fin 3 → ℤ, (if n = 0 then 0 else
        W * Real.exp (-((4 * Real.pi ^ 2 / ℓ ^ 2 * t) * ‖Work.BoseRowsFS.zvec n‖ ^ 2))))
      = W * (∑' n : Fin 3 → ℤ, (if n = 0 then 0 else
          Real.exp (-((4 * Real.pi ^ 2 / ℓ ^ 2 * t) * ‖Work.BoseRowsFS.zvec n‖ ^ 2)))) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    by_cases hn : n = 0 <;> simp [hn]
  have hstep5 : (∑' n : Fin 3 → ℤ, (if n = 0 then 0 else
        Real.exp (-((4 * Real.pi ^ 2 / ℓ ^ 2 * t) * ‖Work.BoseRowsFS.zvec n‖ ^ 2))))
      ≤ 75 * Real.exp (-(4 * Real.pi ^ 2 / ℓ ^ 2 * t)) := tsum_ne_zero_exp_le (by
        have ht' : 1 ≤ t / ℓ ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          simpa using ht
        have hsplit : 4 * Real.pi ^ 2 / ℓ ^ 2 * t = 4 * Real.pi ^ 2 * (t / ℓ ^ 2) := by
          rw [div_mul_eq_mul_div, mul_div_assoc]
        have hp : (36 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
        have hmul : (36 : ℝ) * 1 ≤ 4 * Real.pi ^ 2 * (t / ℓ ^ 2) :=
          mul_le_mul hp ht' (by norm_num) (by positivity)
        rw [hsplit]
        linarith)
  calc |∑' n : Fin 3 → ℤ, (if n = 0 then 0 else f n)|
      ≤ ∑' n : Fin 3 → ℤ, |if n = 0 then 0 else f n| := hstep1
    _ = ∑' n : Fin 3 → ℤ, (if n = 0 then 0 else |f n|) := hstep2
    _ ≤ ∑' n : Fin 3 → ℤ, (if n = 0 then 0 else
          W * Real.exp (-((4 * Real.pi ^ 2 / ℓ ^ 2 * t) * ‖Work.BoseRowsFS.zvec n‖ ^ 2))) := hstep3
    _ = W * (∑' n : Fin 3 → ℤ, (if n = 0 then 0 else
          Real.exp (-((4 * Real.pi ^ 2 / ℓ ^ 2 * t) * ‖Work.BoseRowsFS.zvec n‖ ^ 2)))) := hstep4
    _ ≤ W * (75 * Real.exp (-(4 * Real.pi ^ 2 / ℓ ^ 2 * t))) :=
        mul_le_mul_of_nonneg_left hstep5 hWnn

/-- **The pointwise bound at `t ≥ ℓ²`**: the integrand is dominated by the sum of the two
integrable majorants. -/
lemma integrand_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ} {t : ℝ} (ht : ℓ ^ 2 ≤ t) :
    |(ℓ ^ 3)⁻¹ * ((∑' n : Fin 3 → ℤ, Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n)
        * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))) - Work.BoseFixR.chat h 0)
      - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2))|
    ≤ (ℓ ^ 3)⁻¹ * (75 * (∫ x : ℝ³, |h x|)) * Real.exp (-(4 * Real.pi ^ 2 / ℓ ^ 2 * t))
      + ((2 * Real.pi) ^ 3)⁻¹ * ((∫ x : ℝ³, |h x|) * Real.pi ^ (3 / 2 : ℝ))
          * t ^ (-(3 : ℝ) / 2) := by
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hA := chat_sum_bound (h := h) hℓ ht
  have hB := chat_integral_bound (h := h) htpos
  have h1 : |(ℓ ^ 3)⁻¹ * ((∑' n : Fin 3 → ℤ, Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n)
        * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))) - Work.BoseFixR.chat h 0)|
      ≤ (ℓ ^ 3)⁻¹ * ((∫ x : ℝ³, |h x|) * (75 * Real.exp (-(4 * Real.pi ^ 2 / ℓ ^ 2 * t)))) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹)]
    exact mul_le_mul_of_nonneg_left hA (by positivity)
  have h2 : |((2 * Real.pi) ^ 3)⁻¹
        * ∫ p : ℝ³, Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2))|
      ≤ ((2 * Real.pi) ^ 3)⁻¹
          * ((∫ x : ℝ³, |h x|) * Real.pi ^ (3 / 2 : ℝ) * t ^ (-(3 : ℝ) / 2)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹)]
    exact mul_le_mul_of_nonneg_left hB (by positivity)
  have h3 : |(ℓ ^ 3)⁻¹ * ((∑' n : Fin 3 → ℤ, Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n)
          * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))) - Work.BoseFixR.chat h 0)
        - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2))|
      ≤ |(ℓ ^ 3)⁻¹ * ((∑' n : Fin 3 → ℤ, Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n)
          * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))) - Work.BoseFixR.chat h 0)|
        + |((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2))| := by
    have h := abs_add_le
      ((ℓ ^ 3)⁻¹ * ((∑' n : Fin 3 → ℤ, Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n)
          * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))) - Work.BoseFixR.chat h 0))
      (-(((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2))))
    simpa [sub_eq_add_neg, abs_neg] using h
  calc |(ℓ ^ 3)⁻¹ * ((∑' n : Fin 3 → ℤ, Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n)
          * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))) - Work.BoseFixR.chat h 0)
        - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2))|
      ≤ |(ℓ ^ 3)⁻¹ * ((∑' n : Fin 3 → ℤ, Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n)
          * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))) - Work.BoseFixR.chat h 0)|
        + |((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2))| := h3
    _ ≤ (ℓ ^ 3)⁻¹ * ((∫ x : ℝ³, |h x|) * (75 * Real.exp (-(4 * Real.pi ^ 2 / ℓ ^ 2 * t))))
        + ((2 * Real.pi) ^ 3)⁻¹
          * ((∫ x : ℝ³, |h x|) * Real.pi ^ (3 / 2 : ℝ) * t ^ (-(3 : ℝ) / 2)) :=
        add_le_add h1 h2
    _ = (ℓ ^ 3)⁻¹ * (75 * (∫ x : ℝ³, |h x|)) * Real.exp (-(4 * Real.pi ^ 2 / ℓ ^ 2 * t))
        + ((2 * Real.pi) ^ 3)⁻¹ * ((∫ x : ℝ³, |h x|) * Real.pi ^ (3 / 2 : ℝ))
            * t ^ (-(3 : ℝ) / 2) := by ring

theorem largeT_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ} (hI : MeasureTheory.Integrable h) :
    ∫ t in Set.Ioi (ℓ ^ 2), |(ℓ ^ 3)⁻¹ * ((∑' n : Fin 3 → ℤ, Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n) * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))) - Work.BoseFixR.chat h 0) - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2))| ≤ 100 * (∫ x : ℝ³, |h x|) / ℓ := by
  set W : ℝ := ∫ x : ℝ³, |h x| with hW
  have hWnn : 0 ≤ W := by rw [hW]; exact integral_nonneg (fun x => abs_nonneg (h x))
  set q : ℝ := 4 * Real.pi ^ 2 / ℓ ^ 2 with hq
  have hqpos : 0 < q := by rw [hq]; positivity
  set G₁ : ℝ → ℝ := fun t => (ℓ ^ 3)⁻¹ * (75 * W) * Real.exp (-(q * t)) with hG₁def
  set G₂ : ℝ → ℝ := fun t => ((2 * Real.pi) ^ 3)⁻¹ * (W * Real.pi ^ (3 / 2 : ℝ))
    * t ^ (-(3 : ℝ) / 2) with hG₂def
  have hG₁int : MeasureTheory.Integrable G₁ (volume.restrict (Set.Ioi (ℓ ^ 2))) := by
    have h0 : IntegrableOn (fun t : ℝ => Real.exp (-q * t)) (Set.Ioi (ℓ ^ 2)) :=
      integrableOn_exp_mul_Ioi (show -q < 0 by linarith) (ℓ ^ 2)
    refine (h0.const_mul ((ℓ ^ 3)⁻¹ * (75 * W))).congr
      (Filter.Eventually.of_forall (fun t => ?_))
    show ((ℓ ^ 3)⁻¹ * (75 * W)) * Real.exp (-q * t) = G₁ t
    rw [hG₁def, neg_mul]
  have hG₂int : MeasureTheory.Integrable G₂ (volume.restrict (Set.Ioi (ℓ ^ 2))) := by
    have h0 : IntegrableOn (fun t : ℝ => t ^ (-(3 : ℝ) / 2)) (Set.Ioi (ℓ ^ 2)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by positivity)
    refine (h0.const_mul (((2 * Real.pi) ^ 3)⁻¹ * (W * Real.pi ^ (3 / 2 : ℝ)))).congr
      (Filter.Eventually.of_forall (fun t => ?_))
    show (((2 * Real.pi) ^ 3)⁻¹ * (W * Real.pi ^ (3 / 2 : ℝ))) * t ^ (-(3 : ℝ) / 2) = G₂ t
    rw [hG₂def]
  have hpt : ∀ t ∈ Set.Ioi (ℓ ^ 2),
      |(ℓ ^ 3)⁻¹ * ((∑' n : Fin 3 → ℤ, Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n)
          * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))) - Work.BoseFixR.chat h 0)
        - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2))|
      ≤ G₁ t + G₂ t := by
    intro t ht
    have hmain := integrand_bound (h := h) hℓ (le_of_lt ht)
    rw [← hW, ← hq] at hmain
    exact hmain
  have hGint : MeasureTheory.Integrable (fun t => G₁ t + G₂ t)
      (volume.restrict (Set.Ioi (ℓ ^ 2))) := hG₁int.add hG₂int
  have hmono : ∫ t in Set.Ioi (ℓ ^ 2), |(ℓ ^ 3)⁻¹ * ((∑' n : Fin 3 → ℤ,
          Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n)
          * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))) - Work.BoseFixR.chat h 0)
        - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2))|
      ≤ ∫ t in Set.Ioi (ℓ ^ 2), (G₁ t + G₂ t) :=
    MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict (Set.Ioi (ℓ ^ 2)))
      (Filter.Eventually.of_forall (fun t => abs_nonneg _)) hGint
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hpt))
  have hsplit : ∫ t in Set.Ioi (ℓ ^ 2), (G₁ t + G₂ t)
      = (∫ t in Set.Ioi (ℓ ^ 2), G₁ t) + (∫ t in Set.Ioi (ℓ ^ 2), G₂ t) :=
    MeasureTheory.integral_add hG₁int hG₂int
  have e1 : ∫ t in Set.Ioi (ℓ ^ 2), G₁ t
      = (ℓ ^ 3)⁻¹ * (75 * W) * (Real.exp (-(q * ℓ ^ 2)) / q) := by
    show ∫ t in Set.Ioi (ℓ ^ 2), (ℓ ^ 3)⁻¹ * (75 * W) * Real.exp (-(q * t)) = _
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact largeT_exp_neg_mul_Ioi hqpos
  have hrpow : ∫ t in Set.Ioi (ℓ ^ 2), t ^ (-(3 : ℝ) / 2) = 2 / ℓ := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-(3 : ℝ) / 2) < -1)
      (by positivity : (0 : ℝ) < ℓ ^ 2)]
    have h1 : (-(3 : ℝ) / 2) + 1 = -(1 / 2 : ℝ) := by norm_num
    rw [h1, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
      abs_of_pos hℓ]
    field_simp
  have e2 : ∫ t in Set.Ioi (ℓ ^ 2), G₂ t
      = ((2 * Real.pi) ^ 3)⁻¹ * (W * Real.pi ^ (3 / 2 : ℝ)) * (2 / ℓ) := by
    show ∫ t in Set.Ioi (ℓ ^ 2),
      ((2 * Real.pi) ^ 3)⁻¹ * (W * Real.pi ^ (3 / 2 : ℝ)) * t ^ (-(3 : ℝ) / 2) = _
    rw [MeasureTheory.integral_const_mul, hrpow]
  have hfin : (ℓ ^ 3)⁻¹ * (75 * W) * (Real.exp (-(q * ℓ ^ 2)) / q)
      + ((2 * Real.pi) ^ 3)⁻¹ * (W * Real.pi ^ (3 / 2 : ℝ)) * (2 / ℓ) ≤ 100 * W / ℓ := by
    have hπ : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hexp1 : Real.exp (-(q * ℓ ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 < q * ℓ ^ 2 := mul_pos hqpos (pow_pos hℓ 2)
      linarith
    have hqinv : 1 / q = ℓ ^ 2 / (4 * Real.pi ^ 2) := by rw [hq, one_div, inv_div]
    have hfirst : (ℓ ^ 3)⁻¹ * (75 * W) * (Real.exp (-(q * ℓ ^ 2)) / q) ≤ 75 * W / (4 * ℓ) := by
      have h1 : Real.exp (-(q * ℓ ^ 2)) / q ≤ ℓ ^ 2 / 4 := by
        have ha : Real.exp (-(q * ℓ ^ 2)) / q ≤ 1 / q := div_le_div_of_nonneg_right hexp1 hqpos.le
        have hb : 1 / q ≤ ℓ ^ 2 / 4 := by
          rw [hqinv]
          exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by nlinarith [hπ])
        linarith
      calc (ℓ ^ 3)⁻¹ * (75 * W) * (Real.exp (-(q * ℓ ^ 2)) / q)
          ≤ (ℓ ^ 3)⁻¹ * (75 * W) * (ℓ ^ 2 / 4) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 75 * W / (4 * ℓ) := by field_simp
    have hsecond : ((2 * Real.pi) ^ 3)⁻¹ * (W * Real.pi ^ (3 / 2 : ℝ)) * (2 / ℓ)
        ≤ W / (4 * ℓ) := by
      have hconst : 2 * Real.pi ^ (3 / 2 : ℝ) / (2 * Real.pi) ^ 3 ≤ 1 / 4 := by
        have hle : Real.pi ^ (2 : ℕ) ≤ Real.pi ^ (3 : ℕ) := pow_le_pow_right₀ hπ (by norm_num)
        have h1 : Real.pi ^ (3 / 2 : ℝ) ≤ Real.pi ^ (2 : ℕ) := by
          have h := Real.rpow_le_rpow_of_exponent_le hπ (by norm_num : (3 : ℝ) / 2 ≤ 2)
          simpa using h
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 * Real.pi) ^ 3)]
        have hcube : (2 * Real.pi) ^ 3 = 8 * Real.pi ^ 3 := by ring
        rw [hcube]
        have h2 : 1 / 4 * (8 * Real.pi ^ 3) = 2 * Real.pi ^ 3 := by ring
        have h3 : 2 * Real.pi ^ (3 / 2 : ℝ) ≤ 2 * Real.pi ^ (2 : ℕ) := by linarith [h1]
        have h4 : 2 * Real.pi ^ (2 : ℕ) ≤ 2 * Real.pi ^ (3 : ℕ) := by linarith [hle]
        linarith [h3, h4, h2]
      have hred : ((2 * Real.pi) ^ 3)⁻¹ * (W * Real.pi ^ (3 / 2 : ℝ)) * (2 / ℓ)
          = W * ℓ⁻¹ * (2 * Real.pi ^ (3 / 2 : ℝ) / (2 * Real.pi) ^ 3) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      rw [hred]
      calc W * ℓ⁻¹ * (2 * Real.pi ^ (3 / 2 : ℝ) / (2 * Real.pi) ^ 3)
          ≤ W * ℓ⁻¹ * (1 / 4) := mul_le_mul_of_nonneg_left hconst (by positivity)
        _ = W / (4 * ℓ) := by ring
    have hcomb : 75 * W / (4 * ℓ) + W / (4 * ℓ) = 19 * W / ℓ := by
      field_simp
      ring
    have h19 : 19 * W / ℓ ≤ 100 * W / ℓ :=
      div_le_div_of_nonneg_right (by linarith [hWnn]) hℓ.le
    linarith
  calc ∫ t in Set.Ioi (ℓ ^ 2), |(ℓ ^ 3)⁻¹ * ((∑' n : Fin 3 → ℤ,
          Work.BoseFixR.chat h (Work.BoseBoxFock.kmomInt ℓ n)
          * Real.exp (-(t * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2))) - Work.BoseFixR.chat h 0)
        - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2))|
      ≤ ∫ t in Set.Ioi (ℓ ^ 2), (G₁ t + G₂ t) := hmono
    _ = (∫ t in Set.Ioi (ℓ ^ 2), G₁ t) + (∫ t in Set.Ioi (ℓ ^ 2), G₂ t) := hsplit
    _ = (ℓ ^ 3)⁻¹ * (75 * W) * (Real.exp (-(q * ℓ ^ 2)) / q)
        + ((2 * Real.pi) ^ 3)⁻¹ * (W * Real.pi ^ (3 / 2 : ℝ)) * (2 / ℓ) := by rw [e1, e2]
    _ ≤ 100 * W / ℓ := hfin
    _ = 100 * (∫ x : ℝ³, |h x|) / ℓ := by rw [hW]

end Work.BoseRowsL.Row2
