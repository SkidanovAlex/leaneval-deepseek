import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Submission.Commons.Analysis.Fourier.theta_shift_real
import Submission.Work.BoseFixR.LatGreen.Theta
import Submission.Work.BoseFixR.LatGreen.TsumPiFin3Prod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open scoped Real BigOperators Topology
open MeasureTheory Set Filter
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.BoseFixR.LatGreen

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Summability companion of `TsumPiFin3Prod`. -/
theorem SummablePiFin3Prod {F : Fin 3 → ℤ → ℝ} (hF : ∀ i m, 0 ≤ F i m)
    (hS : ∀ i, Summable fun m : ℤ => F i m) :
    Summable fun n : Fin 3 → ℤ => ∏ i, F i (n i) := by
  rw [← Equiv.summable_iff fin3IntEquivProd.symm]
  change Summable fun p : ℤ × ℤ × ℤ => ∏ i, F i ((fin3IntEquivProd.symm p) i)
  have heq : (fun p : ℤ × ℤ × ℤ => ∏ i, F i ((fin3IntEquivProd.symm p) i))
      = fun p : ℤ × ℤ × ℤ => F 0 p.1 * (F 1 p.2.1 * F 2 p.2.2) := by
    funext p
    obtain ⟨a, b, c⟩ := p
    simp only [fin3IntEquivProd, Equiv.coe_fn_symm_mk]
    rw [Fin.prod_univ_three]
    simp [mul_assoc]
  rw [heq]
  have h12 : Summable fun q : ℤ × ℤ => F 1 q.1 * F 2 q.2 := by
    refine (summable_prod_of_nonneg (fun q => mul_nonneg (hF 1 q.1) (hF 2 q.2))).mpr ⟨?_, ?_⟩
    · intro a
      exact (hS 2).mul_left (F 1 a)
    · have h1 : (fun a : ℤ => ∑' b : ℤ, F 1 a * F 2 b) = fun a : ℤ => F 1 a * ∑' b : ℤ, F 2 b := by
        funext a
        rw [tsum_mul_left]
      rw [h1]
      exact (hS 1).mul_right _
  refine (summable_prod_of_nonneg (fun p : ℤ × ℤ × ℤ =>
    mul_nonneg (hF 0 p.1) (mul_nonneg (hF 1 p.2.1) (hF 2 p.2.2)))).mpr ⟨?_, ?_⟩
  · intro a
    exact h12.mul_left (F 0 a)
  · have h1 : (fun a : ℤ => ∑' q : ℤ × ℤ, F 0 a * (F 1 q.1 * F 2 q.2))
        = fun a : ℤ => F 0 a * ∑' q : ℤ × ℤ, F 1 q.1 * F 2 q.2 := by
      funext a
      rw [tsum_mul_left]
    rw [h1]
    exact (hS 0).mul_right _

/-- A real number that is not an integer is at positive distance from `ℤ`. -/
theorem DistInt {x : ℝ} (hx : ∀ m : ℤ, x ≠ (m : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℤ, δ ≤ |x - (m : ℝ)| := by
  set k : ℤ := ⌊x⌋ with hk
  have hkx : (k : ℝ) < x := by
    rcases lt_or_eq_of_le (Int.floor_le x) with h | h
    · exact h
    · exact absurd h.symm (hx k)
  have hxk : x < (k : ℝ) + 1 := by
    rcases lt_or_eq_of_le (Int.lt_floor_add_one x).le with h | h
    · exact h
    · have : x = ((k + 1 : ℤ) : ℝ) := by push_cast; exact h
      exact absurd this (hx (k + 1))
  refine ⟨min (x - (k : ℝ)) ((k : ℝ) + 1 - x), lt_min (sub_pos.mpr hkx) (sub_pos.mpr hxk), ?_⟩
  intro m
  by_cases hm : (m : ℝ) ≤ (k : ℝ)
  · rw [abs_of_pos (by linarith : 0 < x - (m : ℝ))]
    linarith [min_le_left (x - (k : ℝ)) ((k : ℝ) + 1 - x)]
  · have hm' : (k : ℝ) + 1 ≤ (m : ℝ) := by
      have h1 : k < m := by exact_mod_cast (lt_of_not_ge hm)
      have h2 : k + 1 ≤ m := by omega
      exact_mod_cast h2
    rw [abs_of_neg (by linarith : x - (m : ℝ) < 0)]
    linarith [min_le_right (x - (k : ℝ)) ((k : ℝ) + 1 - x)]

/-- Pointwise factorisation of the Gaussian weight of a lattice vector. -/
lemma exp_norm_sub_latVec (t : ℝ) (u : ℝ³) (m : Fin 3 → ℤ) :
    Real.exp (-‖u - latVec m‖ ^ 2 / (4 * t))
      = ∏ i : Fin 3, Real.exp (-((u i - (m i : ℝ)) ^ 2) / (4 * t)) := by
  rw [← Real.exp_sum]
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [show (∑ x ∈ Finset.univ, -(u.ofLp x - (m x : ℝ)) ^ 2 / (4 * t))
      = -(∑ x ∈ Finset.univ, (u.ofLp x - (m x : ℝ)) ^ 2) / (4 * t) by
    rw [← Finset.sum_div, Finset.sum_neg_distrib]]
  have : (∑ i : Fin 3, (u - latVec m).ofLp i ^ 2)
      = ∑ x : Fin 3, (u.ofLp x - (m x : ℝ)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp [latVec]
  rw [this]

/-- Summability of the Gaussian lattice sum in one coordinate. -/
lemma summable_one (t : ℝ) (ht : 0 < t) (x : ℝ) :
    Summable fun m : ℤ => Real.exp (-((x - (m : ℝ)) ^ 2) / (4 * t)) := by
  have hbase : Summable fun m : ℤ => Real.exp (-(1 / (8 * t)) * (m : ℝ) ^ 2) :=
    Commons.Analysis.Fourier.summable_exp_neg_mul_sq_int (by positivity)
  refine Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) (fun m => ?_)
    (hbase.mul_left (Real.exp (x ^ 2 / (4 * t))))
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h : (m : ℝ) ^ 2 / 2 - x ^ 2 ≤ (x - (m : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (2 * x - (m:ℝ))]
  have h4 : (0:ℝ) < 4 * t := by positivity
  rw [show -(1 / (8 * t)) * (m : ℝ) ^ 2 = (-((m:ℝ) ^ 2 / 2)) / (4 * t) by
    field_simp; ring]
  rw [← add_div, div_le_div_iff_of_pos_right h4]
  linarith

/-- Summability of the three-dimensional Gaussian lattice sum. -/
theorem GaussSummable {t : ℝ} (ht : 0 < t) (u : ℝ³) :
    Summable fun m : Fin 3 → ℤ => Real.exp (-‖u - latVec m‖ ^ 2 / (4 * t)) := by
  have hG : Summable fun m : Fin 3 → ℤ =>
      ∏ i : Fin 3, Real.exp (-((u i - (m i : ℝ)) ^ 2) / (4 * t)) :=
    SummablePiFin3Prod (F := fun i m => Real.exp (-((u i - (m : ℝ)) ^ 2) / (4 * t)))
      (fun i m => (Real.exp_pos _).le) (fun i => summable_one t ht (u i))
  exact hG.congr (fun m => (exp_norm_sub_latVec t u m).symm)

/-- The product formula for the periodised heat kernel. -/
theorem HeatPeriodProd {t : ℝ} (ht : 0 < t) (u : ℝ³) :
    heatPeriod t u = ∏ i : Fin 3,
      ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
        ∑' m : ℤ, Real.exp (-((u i - (m : ℝ)) ^ 2) / (4 * t))) := by
  have hpos : (0:ℝ) < 4 * Real.pi * t := by positivity
  have h1 : heatPeriod t u = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
      ∑' m : Fin 3 → ℤ, Real.exp (-‖u - latVec m‖ ^ 2 / (4 * t)) := by
    rw [heatPeriod, ← tsum_mul_left]
    rfl
  have h2 : (∑' m : Fin 3 → ℤ, Real.exp (-‖u - latVec m‖ ^ 2 / (4 * t)))
      = ∏ i : Fin 3, ∑' m : ℤ, Real.exp (-((u i - (m : ℝ)) ^ 2) / (4 * t)) := by
    rw [← TsumPiFin3Prod (F := fun i m => Real.exp (-((u i - (m : ℝ)) ^ 2) / (4 * t)))
      (fun i m => (Real.exp_pos _).le) (fun i => summable_one t ht (u i))]
    apply tsum_congr
    intro m
    rw [exp_norm_sub_latVec]
  have h3 : (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))
      = ∏ _i : Fin 3, (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [show ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ))) ^ 3
        = ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ))) ^ (3 : ℝ) from
      (Real.rpow_natCast _ 3).symm]
    rw [← Real.rpow_mul hpos.le]
    norm_num
  rw [h1, h2, h3, Finset.prod_mul_distrib]

/-- Some coordinate of a point that is not a lattice vector is not an integer. -/
lemma exists_nonIntegral_coord {u : ℝ³} (hu : ∀ n : Fin 3 → ℤ, u ≠ latVec n) :
    ∃ j : Fin 3, ∀ m : ℤ, u j ≠ (m : ℝ) := by
  by_contra h
  simp only [not_exists, not_forall] at h
  choose n hn using h
  refine hu n ?_
  have hcoord : ∀ i : Fin 3, u.ofLp i = (n i : ℝ) := by
    intro i
    by_contra hc
    exact hn i hc
  have h2 : u.ofLp = (latVec n).ofLp := by
    funext i
    simpa [latVec] using hcoord i
  exact WithLp.ofLp_injective 2 h2

/-- A point that is not a lattice vector is at positive distance from the lattice. -/
lemma exists_dist_pos {u : ℝ³} (hu : ∀ n : Fin 3 → ℤ, u ≠ latVec n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : Fin 3 → ℤ, δ ≤ ‖u - latVec m‖ := by
  obtain ⟨j, hj⟩ := exists_nonIntegral_coord hu
  obtain ⟨δ, hδpos, hδ⟩ := DistInt hj
  refine ⟨δ, hδpos, fun m => ?_⟩
  have h1 : |u j - (m j : ℝ)| ≤ ‖u - latVec m‖ := by
    have h := PiLp.norm_apply_le (u - latVec m) j
    simpa [latVec, Real.norm_eq_abs] using h
  exact le_trans (hδ (m j)) h1

/-- A three-fold product close to `1` is close to `1`. -/
lemma abs_prod_sub_one_le {r : ℝ} (hr : 0 ≤ r) {a : Fin 3 → ℝ} (ha : ∀ i, |a i - 1| ≤ r) :
    |∏ i : Fin 3, a i - 1| ≤ 3 * r * (1 + r) ^ 2 := by
  have hb : ∀ i, |a i| ≤ 1 + r := fun i => by
    have h := ha i
    calc |a i| = |(a i - 1) + 1| := by ring_nf
      _ ≤ |a i - 1| + |(1:ℝ)| := abs_add_le _ _
      _ ≤ r + 1 := by simp only [abs_one]; linarith
      _ = 1 + r := by ring
  have hkey : ∏ i : Fin 3, a i - 1
      = (a 0 - 1) * a 1 * a 2 + (a 1 - 1) * a 2 + (a 2 - 1) := by
    rw [Fin.prod_univ_three]; ring
  rw [hkey]
  have e1 : |(a 0 - 1) * a 1 * a 2| ≤ r * (1 + r) ^ 2 := by
    rw [abs_mul, abs_mul]
    calc |a 0 - 1| * |a 1| * |a 2| ≤ r * (1 + r) * (1 + r) := by
          apply mul_le_mul
          · exact mul_le_mul (ha 0) (hb 1) (abs_nonneg _) hr
          · exact hb 2
          · exact abs_nonneg _
          · positivity
      _ = r * (1 + r) ^ 2 := by ring
  have e2 : |(a 1 - 1) * a 2| ≤ r * (1 + r) := by
    rw [abs_mul]
    exact mul_le_mul (ha 1) (hb 2) (abs_nonneg _) hr
  have e3 : |a 2 - 1| ≤ r := ha 2
  calc |(a 0 - 1) * a 1 * a 2 + (a 1 - 1) * a 2 + (a 2 - 1)|
      ≤ |(a 0 - 1) * a 1 * a 2 + (a 1 - 1) * a 2| + |a 2 - 1| := abs_add_le _ _
    _ ≤ (|(a 0 - 1) * a 1 * a 2| + |(a 1 - 1) * a 2|) + |a 2 - 1| := by
        linarith [abs_add_le ((a 0 - 1) * a 1 * a 2) ((a 1 - 1) * a 2)]
    _ ≤ (r * (1 + r) ^ 2 + r * (1 + r)) + r := by linarith
    _ ≤ 3 * r * (1 + r) ^ 2 := by
        have h1r : (1:ℝ) ≤ 1 + r := by linarith
        have hsq : (1:ℝ) ≤ (1 + r) ^ 2 := by nlinarith
        have hA : r * (1 + r) ≤ r * (1 + r) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith) hr
        have hB : r ≤ r * (1 + r) ^ 2 := by nlinarith
        linarith


/-- One-dimensional theta identity for the periodised heat kernel. -/
lemma oneD_theta_eq {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∑' m : ℤ, Real.exp (-((x - (m : ℝ)) ^ 2) / (4 * t)))
      = Real.sqrt (4 * Real.pi * t) *
        ∑' n : ℤ, Real.exp (-(4 * Real.pi ^ 2 * t) * (n : ℝ) ^ 2)
          * Real.cos (2 * Real.pi * (n : ℝ) * x) := by
  have ha : (0 : ℝ) < 1 / (4 * t) := by positivity
  have h := Commons.Analysis.Fourier.theta_shift_real (a := 1 / (4 * t)) (c := -x) ha
  rw [show Real.pi / (1 / (4 * t)) = 4 * Real.pi * t by field_simp] at h
  rw [show (∑' m : ℤ, Real.exp (-((x - (m : ℝ)) ^ 2) / (4 * t)))
      = ∑' n : ℤ, Real.exp (-((1 / (4 * t)) * ((n : ℝ) + -x) ^ 2)) by
    apply tsum_congr
    intro n
    congr 1
    field_simp
    ring]
  rw [h]
  congr 1
  apply tsum_congr
  intro n
  rw [show -(4 * Real.pi ^ 2 * t) * (n : ℝ) ^ 2
      = -((Real.pi * (n : ℝ)) ^ 2) / (1 / (4 * t)) by rw [div_eq_mul_inv, inv_div]; ring]
  rw [mul_neg, Real.cos_neg]

/-- The periodised one-dimensional heat kernel equals its Fourier series. -/
lemma oneD_Q_eq {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∑' m : ℤ, (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((x - (m : ℝ)) ^ 2) / (4 * t)))
      = ∑' n : ℤ, Real.exp (-(4 * Real.pi ^ 2 * t) * (n : ℝ) ^ 2)
          * Real.cos (2 * Real.pi * (n : ℝ) * x) := by
  have hconst : (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.sqrt (4 * Real.pi * t) = 1 := by
    rw [show (-(1 / 2 : ℝ)) = -((1 / 2 : ℝ)) by norm_num, Real.rpow_neg (by positivity),
      Real.sqrt_eq_rpow, inv_mul_cancel₀]
    positivity
  rw [tsum_mul_left, oneD_theta_eq ht x, ← mul_assoc, hconst, one_mul]

/-- Exponential decay of the one-dimensional theta error. -/
theorem OneDThetaExpBound : ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 1 ≤ t → ∀ x : ℝ,
    |(∑' m : ℤ, (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-((x - (m : ℝ)) ^ 2) / (4 * t))) - 1|
      ≤ D * Real.exp (-(4 * Real.pi ^ 2) * t) := by
  refine ⟨∑' n : ℤ, Real.exp (-(4 * Real.pi ^ 2) * ((n : ℝ) ^ 2 - 1)), ?_, ?_⟩
  · have hsum : Summable fun n : ℤ => Real.exp (-(4 * Real.pi ^ 2) * ((n : ℝ) ^ 2 - 1)) := by
      have h := (Commons.Analysis.Fourier.summable_exp_neg_mul_sq_int
        (show (0 : ℝ) < 4 * Real.pi ^ 2 by positivity)).mul_left (Real.exp (4 * Real.pi ^ 2))
      refine h.congr (fun n => ?_)
      rw [← Real.exp_add]
      congr 1
      ring
    have h := hsum.le_tsum 0 (fun j hj => (Real.exp_pos _).le)
    have h0 : Real.exp (-(4 * Real.pi ^ 2) * ((0 : ℤ) ^ 2 - 1)) = Real.exp (4 * Real.pi ^ 2) := by
      norm_num
    rw [h0] at h
    exact lt_of_lt_of_le (Real.exp_pos _) h
  · intro t ht x
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have hbase : Summable fun n : ℤ => Real.exp (-(4 * Real.pi ^ 2 * t) * (n : ℝ) ^ 2) :=
      Commons.Analysis.Fourier.summable_exp_neg_mul_sq_int (by positivity)
    have hexp_le : ∀ n : ℤ, n ≠ 0 → Real.exp (-(4 * Real.pi ^ 2 * t) * (n : ℝ) ^ 2)
        ≤ Real.exp (-(4 * Real.pi ^ 2) * t) * Real.exp (-(4 * Real.pi ^ 2) * ((n : ℝ) ^ 2 - 1)) := by
      intro n hn
      have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have h1 : (1 : ℤ) ≤ |n| := by
          have hpos : (0:ℤ) < |n| := abs_pos.mpr hn
          omega
        have h2 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast h1
        have h4 : (1:ℝ) ≤ |(n:ℝ)| * |(n:ℝ)| := by
          simpa using mul_le_mul h2 h2 (by norm_num : (0:ℝ) ≤ 1) (by linarith)
        have h5 : |(n:ℝ)| * |(n:ℝ)| = (n:ℝ)^2 := by rw [← sq, sq_abs]
        rwa [h5] at h4
      have key : 0 ≤ ((n : ℝ) ^ 2 - 1) * (t - 1) :=
        mul_nonneg (sub_nonneg.mpr hn2) (sub_nonneg.mpr ht)
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [key, Real.pi_pos]
    have hDsum : Summable fun n : ℤ =>
        Real.exp (-(4 * Real.pi ^ 2) * t) * Real.exp (-(4 * Real.pi ^ 2) * ((n : ℝ) ^ 2 - 1)) := by
      have h : Summable fun n : ℤ => Real.exp (-(4 * Real.pi ^ 2) * ((n : ℝ) ^ 2 - 1)) := by
        have h2 := (Commons.Analysis.Fourier.summable_exp_neg_mul_sq_int
          (show (0 : ℝ) < 4 * Real.pi ^ 2 by positivity)).mul_left (Real.exp (4 * Real.pi ^ 2))
        refine h2.congr (fun n => ?_)
        rw [← Real.exp_add]
        congr 1
        ring
      exact h.mul_left _
    rw [oneD_Q_eq ht0 x]
    set G : ℤ → ℝ := fun n => Real.exp (-(4 * Real.pi ^ 2 * t) * (n : ℝ) ^ 2)
      * Real.cos (2 * Real.pi * (n : ℝ) * x) with hG
    have hG0 : G 0 = 1 := by simp [hG]
    have hGabs : Summable fun n : ℤ => ‖G n‖ := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hbase
      rw [hG, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
    have hGsum : Summable G := hGabs.of_norm
    have hsplit := hGsum.tsum_eq_add_tsum_ite (0 : ℤ)
    have hiteabs : Summable fun n : ℤ => ‖(if n = 0 then 0 else G n)‖ := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hbase
      by_cases hn : n = 0
      · simp [hn]
      · rw [if_neg hn, hG, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
    have hitemaj : Summable fun n : ℤ => (if n = 0 then 0 else Real.exp (-(4 * Real.pi ^ 2 * t) * (n : ℝ) ^ 2)) := by
      refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
      · by_cases hn : n = 0
        · simp [hn]
        · rw [if_neg hn]; positivity
      · by_cases hn : n = 0
        · simp [hn]
        · rw [if_neg hn]
    have step1 : |(∑' n : ℤ, G n) - 1| = |∑' n : ℤ, (if n = 0 then 0 else G n)| := by
      rw [hsplit, hG0]
      congr 1
      ring
    have step2 : |∑' n : ℤ, (if n = 0 then 0 else G n)|
        ≤ ∑' n : ℤ, ‖(if n = 0 then 0 else G n)‖ := norm_tsum_le_tsum_norm hiteabs
    have step3 : (∑' n : ℤ, ‖(if n = 0 then 0 else G n)‖)
        ≤ ∑' n : ℤ, (if n = 0 then 0 else Real.exp (-(4 * Real.pi ^ 2 * t) * (n : ℝ) ^ 2)) := by
      apply Summable.tsum_le_tsum _ hiteabs hitemaj
      intro n
      by_cases hn : n = 0
      · simp [hn]
      · rw [if_neg hn, if_neg hn, hG, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
    have step4 : (∑' n : ℤ, (if n = 0 then 0 else Real.exp (-(4 * Real.pi ^ 2 * t) * (n : ℝ) ^ 2)))
        ≤ ∑' n : ℤ, Real.exp (-(4 * Real.pi ^ 2) * t) *
            Real.exp (-(4 * Real.pi ^ 2) * ((n : ℝ) ^ 2 - 1)) := by
      apply Summable.tsum_le_tsum _ hitemaj hDsum
      intro n
      by_cases hn : n = 0
      · simp only [hn, ↓reduceIte]
        exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
      · rw [if_neg hn]
        exact hexp_le n hn
    have step5 : (∑' n : ℤ, Real.exp (-(4 * Real.pi ^ 2) * t) *
            Real.exp (-(4 * Real.pi ^ 2) * ((n : ℝ) ^ 2 - 1)))
        = (∑' n : ℤ, Real.exp (-(4 * Real.pi ^ 2) * ((n : ℝ) ^ 2 - 1))) * Real.exp (-(4 * Real.pi ^ 2) * t) := by
      rw [tsum_mul_left, mul_comm]
    linarith [step1, step2, step3, step4, step5.le, step5.ge]


/-- Exponential decay of the three-dimensional periodised heat kernel. -/
theorem heatPeriod_sub_one_exp (u : ℝ³) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 1 ≤ t →
      |heatPeriod t u - 1| ≤ D * Real.exp (-(4 * Real.pi ^ 2) * t) := by
  obtain ⟨D, hDpos, hD⟩ := OneDThetaExpBound
  refine ⟨3 * (1 + D * Real.exp (-(4 * Real.pi ^ 2))) ^ 2 * D, by positivity, fun t ht => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hfac : ∀ i : Fin 3,
      |(4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
        (∑' m : ℤ, Real.exp (-((u i - (m : ℝ)) ^ 2) / (4 * t))) - 1|
        ≤ D * Real.exp (-(4 * Real.pi ^ 2) * t) := by
    intro i
    rw [← tsum_mul_left]
    exact hD t ht (u i)
  have hr : 0 ≤ D * Real.exp (-(4 * Real.pi ^ 2) * t) := by positivity
  rw [HeatPeriodProd ht0 u]
  refine le_trans (abs_prod_sub_one_le hr hfac) ?_
  have hle : Real.exp (-(4 * Real.pi ^ 2) * t) ≤ Real.exp (-(4 * Real.pi ^ 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [ht, Real.pi_pos]
  have hr_le : D * Real.exp (-(4 * Real.pi ^ 2) * t) ≤ D * Real.exp (-(4 * Real.pi ^ 2)) :=
    mul_le_mul_of_nonneg_left hle hDpos.le
  have h1r : 1 + D * Real.exp (-(4 * Real.pi ^ 2) * t)
      ≤ 1 + D * Real.exp (-(4 * Real.pi ^ 2)) := by linarith
  have hsq : (1 + D * Real.exp (-(4 * Real.pi ^ 2) * t)) ^ 2
      ≤ (1 + D * Real.exp (-(4 * Real.pi ^ 2))) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1r 2
  calc 3 * (D * Real.exp (-(4 * Real.pi ^ 2) * t))
        * (1 + D * Real.exp (-(4 * Real.pi ^ 2) * t)) ^ 2
      ≤ 3 * (D * Real.exp (-(4 * Real.pi ^ 2) * t))
        * (1 + D * Real.exp (-(4 * Real.pi ^ 2))) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 3 * (1 + D * Real.exp (-(4 * Real.pi ^ 2))) ^ 2 * D
        * Real.exp (-(4 * Real.pi ^ 2) * t) := by ring

/-- Boundedness of the periodised heat kernel near `t = 0`, off the lattice. -/
theorem heatPeriod_le_small {u : ℝ³} (hu : ∀ n : Fin 3 → ℤ, u ≠ latVec n) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      heatPeriod t u ≤ C * t ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_dist_pos hu
  set c : ℝ := δ ^ 2 / 8 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hsumm8 : Summable fun m : Fin 3 → ℤ => Real.exp (-‖u - latVec m‖ ^ 2 / 8) :=
    (GaussSummable (t := 2) (by norm_num) u).congr (fun m => by norm_num)
  refine ⟨(4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
      (∑' m : Fin 3 → ℤ, Real.exp (-‖u - latVec m‖ ^ 2 / 8)) * (1 / c), ?_, fun t ht0 ht1 => ?_⟩
  · have h := hsumm8.le_tsum 0 (fun j hj => (Real.exp_pos _).le)
    have h0 : Real.exp (-‖u - latVec 0‖ ^ 2 / 8) = Real.exp (-‖u‖ ^ 2 / 8) := by
      rw [show latVec 0 = (0 : ℝ³) from by ext i; simp [latVec]]
      simp
    rw [h0] at h
    have h1 : 0 < ∑' m : Fin 3 → ℤ, Real.exp (-‖u - latVec m‖ ^ 2 / 8) :=
      lt_of_lt_of_le (Real.exp_pos _) h
    positivity
  · have hdef : heatPeriod t u = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
        (∑' m : Fin 3 → ℤ, Real.exp (-‖u - latVec m‖ ^ 2 / (4 * t))) := by
      rw [heatPeriod, ← tsum_mul_left]
      rfl
    have h4t : (0 : ℝ) < 4 * t := by positivity
    have hsum4t : Summable fun m : Fin 3 → ℤ => Real.exp (-‖u - latVec m‖ ^ 2 / (4 * t)) :=
      GaussSummable ht0 u
    have hcmp : (∑' m : Fin 3 → ℤ, Real.exp (-‖u - latVec m‖ ^ 2 / (4 * t)))
        ≤ Real.exp (-(c / t)) * (∑' m : Fin 3 → ℤ, Real.exp (-‖u - latVec m‖ ^ 2 / 8)) := by
      calc (∑' m : Fin 3 → ℤ, Real.exp (-‖u - latVec m‖ ^ 2 / (4 * t)))
          ≤ ∑' m : Fin 3 → ℤ, Real.exp (-(c / t)) * Real.exp (-‖u - latVec m‖ ^ 2 / 8) := by
            apply Summable.tsum_le_tsum _ hsum4t (hsumm8.mul_left _)
            intro m
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have hd := hδ m
            have hsq : δ ^ 2 ≤ ‖u - latVec m‖ ^ 2 := by
              nlinarith [hd, norm_nonneg (u - latVec m)]
            have hgoal' : c / t + ‖u - latVec m‖ ^ 2 / 8
                ≤ ‖u - latVec m‖ ^ 2 / (4 * t) := by
              rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * t)]
              have e : (c / t + ‖u - latVec m‖ ^ 2 / 8) * (4 * t)
                  = 4 * c + ‖u - latVec m‖ ^ 2 * t / 2 := by
                field_simp
                ring
              rw [e]
              nlinarith [hsq, ht1, hc, norm_nonneg (u - latVec m)]
            have hX : -‖u - latVec m‖ ^ 2 / (4 * t)
                = -(‖u - latVec m‖ ^ 2 / (4 * t)) := by ring
            have hY : -(c / t) + -‖u - latVec m‖ ^ 2 / 8
                = -(c / t + ‖u - latVec m‖ ^ 2 / 8) := by ring
            rw [hX, hY]
            exact neg_le_neg hgoal'
        _ = Real.exp (-(c / t)) * (∑' m : Fin 3 → ℤ, Real.exp (-‖u - latVec m‖ ^ 2 / 8)) := by
            rw [tsum_mul_left]
    have hkey : t ^ (-(3 / 2 : ℝ)) * Real.exp (-(c / t)) ≤ (1 / c) * t ^ (-(1 / 2 : ℝ)) := by
      have h1 : (c / t) * Real.exp (-(c / t)) ≤ 1 := by
        have h := Real.add_one_le_exp (c / t)
        have h2 : c / t ≤ Real.exp (c / t) := by linarith
        have h3 : (c / t) * Real.exp (-(c / t)) = (c / t) / Real.exp (c / t) := by
          simp only [Real.exp_neg, div_eq_mul_inv]
        rw [h3]
        exact (div_le_one (Real.exp_pos _)).mpr h2
      have h2 : Real.exp (-(c / t)) / t ≤ 1 / c := by
        have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / c)
        calc Real.exp (-(c / t)) / t
            = (1 / c) * ((c / t) * Real.exp (-(c / t))) := by field_simp
          _ ≤ (1 / c) * 1 := h3
          _ = 1 / c := by ring
      calc t ^ (-(3 / 2 : ℝ)) * Real.exp (-(c / t))
          = t ^ (-(1 / 2 : ℝ)) * (Real.exp (-(c / t)) / t) := by
            rw [show (-(3 / 2 : ℝ)) = (-(1 / 2 : ℝ)) + (-1 : ℝ) by norm_num, Real.rpow_add ht0,
              Real.rpow_neg_one, div_eq_mul_inv]
            ring
        _ ≤ t ^ (-(1 / 2 : ℝ)) * (1 / c) :=
            mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg ht0.le _)
        _ = (1 / c) * t ^ (-(1 / 2 : ℝ)) := by ring
    calc heatPeriod t u
        ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))
            * (Real.exp (-(c / t)) * (∑' m : Fin 3 → ℤ, Real.exp (-‖u - latVec m‖ ^ 2 / 8))) := by
          rw [hdef]
          exact mul_le_mul_of_nonneg_left hcmp (Real.rpow_nonneg (by positivity) _)
      _ = (4 * Real.pi) ^ (-(3 / 2 : ℝ))
            * (∑' m : Fin 3 → ℤ, Real.exp (-‖u - latVec m‖ ^ 2 / 8))
            * (t ^ (-(3 / 2 : ℝ)) * Real.exp (-(c / t))) := by
          rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * Real.pi) ht0.le]
          ring_nf
      _ ≤ (4 * Real.pi) ^ (-(3 / 2 : ℝ))
            * (∑' m : Fin 3 → ℤ, Real.exp (-‖u - latVec m‖ ^ 2 / 8))
            * ((1 / c) * t ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = ((4 * Real.pi) ^ (-(3 / 2 : ℝ))
            * (∑' m : Fin 3 → ℤ, Real.exp (-‖u - latVec m‖ ^ 2 / 8)) * (1 / c))
            * t ^ (-(1 / 2 : ℝ)) := by ring

/-- Continuity of the individual heat kernels in the time variable, away from `t = 0`. -/
lemma heatK3_continuousOn (m : Fin 3 → ℤ) (u : ℝ³) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => heatK3 t (u - latVec m)) (Ioo a b) := by
  have h1 : ContinuousOn (fun t : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))) (Ioo a b) := by
    apply ContinuousOn.rpow_const
    · fun_prop
    · intro t ht
      left
      exact ne_of_gt (mul_pos (mul_pos (by norm_num) Real.pi_pos) (by linarith [ha, ht.1]))
  have h2 : ContinuousOn (fun t : ℝ => Real.exp (-‖u - latVec m‖ ^ 2 / (4 * t))) (Ioo a b) := by
    refine Real.continuous_exp.comp_continuousOn ?_
    have h3 : (fun t : ℝ => -‖u - latVec m‖ ^ 2 / (4 * t))
        = fun t : ℝ => (-(‖u - latVec m‖ ^ 2) / 4) / t := by
      funext t
      ring
    rw [h3]
    exact continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (by linarith [ha, ht.1]))
  exact h1.mul h2

/-- The periodised heat kernel is continuous in `t` on `(0, ∞)`. -/
lemma heatPeriod_continuousOn (u : ℝ³) :
    ContinuousOn (fun t : ℝ => heatPeriod t u) (Ioi 0) := by
  intro t0 ht0
  have ht0' : (0 : ℝ) < t0 := ht0
  have hmem : Ioo (t0 / 2) (2 * t0) ∈ 𝓝 t0 :=
    Ioo_mem_nhds (by linarith) (by linarith)
  refine (ContinuousOn.continuousAt ?_ hmem).continuousWithinAt
  have hcont : ContinuousOn (fun t : ℝ => heatPeriod t u) (Ioo (t0 / 2) (2 * t0)) :=
    continuousOn_tsum (s := Ioo (t0 / 2) (2 * t0))
      (u := fun m : Fin 3 → ℤ => (4 * Real.pi * (t0 / 2)) ^ (-(3 / 2 : ℝ))
        * Real.exp (-‖u - latVec m‖ ^ 2 / (4 * (2 * t0))))
      (f := fun m t => heatK3 t (u - latVec m))
      (fun m => heatK3_continuousOn m u (by linarith))
      ((GaussSummable (t := 2 * t0) (by linarith) u).mul_left _)
      (fun m t ht => ?_)
  exact hcont
  rw [Real.norm_of_nonneg (heatK3_nonneg (by linarith [ht0', ht.1]) _)]
  have hsq : 4 * Real.pi * (t0 / 2) ≤ 4 * Real.pi * t := by
    nlinarith [ht.1, Real.pi_pos]
  have h4a : (0:ℝ) < 4 * Real.pi * (t0 / 2) := by positivity
  refine mul_le_mul ?_ ?_ (Real.exp_pos _).le (Real.rpow_nonneg h4a.le _)
  · exact Real.rpow_le_rpow_of_nonpos h4a hsq (by norm_num)
  · apply Real.exp_le_exp.mpr
    rw [show -‖u - latVec m‖ ^ 2 / (4 * t)
          = -(‖u - latVec m‖ ^ 2 / (4 * t)) by ring,
      show -‖u - latVec m‖ ^ 2 / (4 * (2 * t0))
          = -(‖u - latVec m‖ ^ 2 / (4 * (2 * t0))) by ring]
    apply neg_le_neg
    exact div_le_div_of_nonneg_left (by positivity)
      (by linarith [ht.1, ht0'] : (0:ℝ) < 4 * t) (by linarith [ht.2, ht0'])

/-- **Integrability of the mean-zero part of the periodised heat kernel.**  For a point `u` that
is not a lattice vector, `t ↦ heatPeriod t u - 1` is integrable on `(0, ∞)`: on `(0,1]` it is
dominated by `t^{-1/2}` (the nearest lattice point in a non-integral coordinate bounds the
Gaussian exponentially) and on `[1,∞)` it decays like `exp (-4π²t)` (Jacobi/Poisson summation in
the product form `heatPeriod = ∏ᵢ Q₁(·, uᵢ)`). -/
theorem PeriodIntegrable {u : EuclideanSpace ℝ (Fin 3)}
    (hu : ∀ n : Fin 3 → ℤ, u ≠ Work.BoseFixR.LatGreen.latVec n) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.BoseFixR.LatGreen.heatPeriod t u - 1) (Set.Ioi (0 : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := heatPeriod_le_small hu
  obtain ⟨D, hDpos, hD⟩ := heatPeriod_sub_one_exp u
  have hcont : ContinuousOn (fun t : ℝ => heatPeriod t u - 1) (Ioi 0) :=
    (heatPeriod_continuousOn u).sub continuousOn_const
  have hsmall : IntegrableOn (fun t : ℝ => heatPeriod t u - 1) (Ioc 0 1) := by
    have hint : IntegrableOn (fun t : ℝ => (C + 1) * t ^ (-(1 / 2 : ℝ))) (Ioc 0 1) := by
      have h := intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ)) (by norm_num)
        (a := 0) (b := 1)
      rw [intervalIntegrable_iff, uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
      exact h.const_mul (C + 1)
    refine Integrable.mono' hint ?_ ?_
    · exact (hcont.mono (fun t ht => ht.1)).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs, abs_le]
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have h1le : (1 : ℝ) ≤ t ^ (-(1 / 2 : ℝ)) := by
        rw [show (-(1 / 2 : ℝ)) = -((1 / 2 : ℝ)) by norm_num, Real.rpow_neg ht0.le,
          one_le_inv₀ (Real.rpow_pos_of_pos ht0 _)]
        exact Real.rpow_le_one ht0.le ht1 (by norm_num)
      have hbnd : heatPeriod t u ≤ C * t ^ (-(1 / 2 : ℝ)) := hC t ht0 ht1
      have hnonneg : (0 : ℝ) ≤ heatPeriod t u := by
        rw [heatPeriod]
        exact tsum_nonneg (fun m => heatK3_nonneg (by positivity) _)
      constructor
      · nlinarith [hbnd, h1le, hCpos]
      · have : (0 : ℝ) ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht0.le _
        nlinarith [hnonneg, h1le, hCpos, this]
  have hlarge : IntegrableOn (fun t : ℝ => heatPeriod t u - 1) (Ioi 1) := by
    have hint : IntegrableOn (fun t : ℝ => D * Real.exp (-(4 * Real.pi ^ 2) * t)) (Ioi 1) :=
      Integrable.const_mul (exp_neg_integrableOn_Ioi 1 (by positivity : (0 : ℝ) < 4 * Real.pi ^ 2)) D
    refine Integrable.mono' hint ?_ ?_
    · exact (hcont.mono (fun t ht => by simp only [mem_Ioi] at ht ⊢; linarith)).aestronglyMeasurable
        measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs]
      exact hD t (le_of_lt ht)
  have hunion := hsmall.union hlarge
  rwa [show Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 from by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · exact h1
      · linarith
    · intro h
      by_cases h2 : t ≤ 1
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr (by linarith)] at hunion

end Work.BoseFixR.LatGreen
