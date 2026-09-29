import Submission.Work.CLift.defs

/-!
# Area CLift — the analytic function defined by `P`, its derivatives and the ODE
-/

set_option maxHeartbeats 4000000

namespace Work.CLift

open PowerSeries Submission.CDTPlan Submission.CDT
open scoped BigOperators

noncomputable section

/-! ## Polynomial versions of the operator data -/

/-- `Q4` as a polynomial. -/
def Q4poly (m n : ℕ) : Polynomial ℚ :=
  1 - Polynomial.C (4 * aa m * bb n) * Polynomial.X
    + Polynomial.C (4 * (aa m) ^ 2 + 4 * (bb n) ^ 2 - 2) * Polynomial.X ^ 2
    - Polynomial.C (4 * aa m * bb n) * Polynomial.X ^ 3 + Polynomial.X ^ 4

/-- `P2` as a polynomial. -/
def P2poly (m n : ℕ) : Polynomial ℚ :=
  (Polynomial.X - 1) * Polynomial.X * (Polynomial.X + 1) * Q4poly m n

/-- `P1` as a polynomial. -/
def P1poly (m n : ℕ) : Polynomial ℚ :=
  -1 + Polynomial.C (8 * aa m * bb n) * Polynomial.X
    + Polynomial.C (5 - 12 * (aa m) ^ 2 - 12 * (bb n) ^ 2) * Polynomial.X ^ 2
    + Polynomial.C (16 * aa m * bb n) * Polynomial.X ^ 3
    + Polynomial.C (4 * (aa m) ^ 2 + 4 * (bb n) ^ 2 - 7) * Polynomial.X ^ 4
    - Polynomial.C (8 * aa m * bb n) * Polynomial.X ^ 5 + Polynomial.C 3 * Polynomial.X ^ 6

/-- `P0` as a polynomial. -/
def P0poly (m n : ℕ) : Polynomial ℚ :=
  Polynomial.C (aa m * bb n) + Polynomial.C (1 - 3 * (aa m) ^ 2 - 3 * (bb n) ^ 2) * Polynomial.X
    + Polynomial.C (8 * aa m * bb n) * Polynomial.X ^ 2
    - Polynomial.C ((aa m) ^ 2 + (bb n) ^ 2 + 2) * Polynomial.X ^ 3
    - Polynomial.C (aa m * bb n) * Polynomial.X ^ 4 + Polynomial.X ^ 5

/-- `RaFam` as a polynomial. -/
def Rapoly (m n : ℕ) : Polynomial ℚ :=
  Polynomial.C (-(bb n)) * Polynomial.X ^ 0 + Polynomial.C (3 * aa m) * Polynomial.X ^ 1
    + Polynomial.C (-(3 * bb n)) * Polynomial.X ^ 2 + Polynomial.C (aa m) * Polynomial.X ^ 3

/-- `RbFam` as a polynomial. -/
def Rbpoly (m n : ℕ) : Polynomial ℚ :=
  Polynomial.C (-(aa m)) * Polynomial.X ^ 0 + Polynomial.C (3 * bb n) * Polynomial.X ^ 1
    + Polynomial.C (-(3 * aa m)) * Polynomial.X ^ 2 + Polynomial.C (bb n) * Polynomial.X ^ 3

/-- `RabFam` as a polynomial. -/
def Rabpoly : Polynomial ℚ :=
  Polynomial.C (-1) * Polynomial.X ^ 0 + Polynomial.C (2) * Polynomial.X ^ 2
    + Polynomial.C (-1) * Polynomial.X ^ 4

/-- The right-hand side of `logP_ode` as a polynomial. -/
def Rhpoly (m n : ℕ) (ra rb rab : ℤ) : Polynomial ℚ :=
  Polynomial.C (ra : ℚ) * Rapoly m n + Polynomial.C (rb : ℚ) * Rbpoly m n
    + Polynomial.C (rab : ℚ) * Rabpoly

/-! ## The bridges -/

lemma Q4poly_coe (m n : ℕ) :
    ((Q4poly m n : Polynomial ℚ) : PowerSeries ℚ) = logPAQ4 (aa m) (bb n) := by
  simp only [Q4poly, logPAQ4]; push_cast; ring

lemma P2poly_coe (m n : ℕ) :
    ((P2poly m n : Polynomial ℚ) : PowerSeries ℚ) = logPAP2 (aa m) (bb n) := by
  simp only [P2poly, Q4poly, logPAP2, logPAQ4]; push_cast; ring

lemma P1poly_coe (m n : ℕ) :
    ((P1poly m n : Polynomial ℚ) : PowerSeries ℚ) = logPAP1 (aa m) (bb n) := by
  simp only [P1poly, logPAP1]; push_cast; ring_nf; rfl

lemma P0poly_coe (m n : ℕ) :
    ((P0poly m n : Polynomial ℚ) : PowerSeries ℚ) = logPAP0 (aa m) (bb n) := by
  simp only [P0poly, logPAP0]; push_cast; ring

lemma Rapoly_coe (m n : ℕ) :
    ((Rapoly m n : Polynomial ℚ) : PowerSeries ℚ) = RaFam (aa m) (bb n) := by
  simp only [Rapoly, RaFam]; push_cast; ring

lemma Rbpoly_coe (m n : ℕ) :
    ((Rbpoly m n : Polynomial ℚ) : PowerSeries ℚ) = RbFam (aa m) (bb n) := by
  simp only [Rbpoly, RbFam]; push_cast; ring

lemma Rabpoly_coe (m n : ℕ) :
    ((Rabpoly : Polynomial ℚ) : PowerSeries ℚ) = RabFam (aa m) (bb n) := by
  simp only [Rabpoly, RabFam]; push_cast; ring

lemma Rhpoly_coe (m n : ℕ) (ra rb rab : ℤ) :
    ((Rhpoly m n ra rb rab : Polynomial ℚ) : PowerSeries ℚ)
      = PowerSeries.C (ra : ℚ) * RaFam (aa m) (bb n)
        + PowerSeries.C (rb : ℚ) * RbFam (aa m) (bb n)
        + PowerSeries.C (rab : ℚ) * RabFam (aa m) (bb n) := by
  simp only [Rhpoly, Rapoly, Rbpoly, Rabpoly, RaFam, RbFam, RabFam]; push_cast; ring

/-! ## Evaluating polynomials -/

lemma evA_coe_poly (p : Polynomial ℚ) (x : ℂ) :
    evA (p : PowerSeries ℚ) x = p.eval₂ (algebraMap ℚ ℂ) x := by
  rw [evA, tsum_eq_sum (s := Finset.range (p.natDegree + 1))]
  · rw [Polynomial.eval₂_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Polynomial.coeff_coe]
    rfl
  · intro k hk
    rw [Polynomial.coeff_coe]
    have : p.coeff k = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      simp only [Finset.mem_range, not_lt] at hk; omega
    rw [this]; simp

lemma evA_P2 (m n : ℕ) (x : ℂ) : evA (logPAP2 (aa m) (bb n)) x = P2p m n x := by
  rw [← P2poly_coe m n, evA_coe_poly]
  simp only [P2poly, Q4poly, P2p, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one,
    Polynomial.eval₂_neg]
  push_cast
  norm_num
  try ring

lemma evA_P1 (m n : ℕ) (x : ℂ) : evA (logPAP1 (aa m) (bb n)) x = P1p m n x := by
  rw [← P1poly_coe m n, evA_coe_poly]
  simp only [P1poly, P1p, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one,
    Polynomial.eval₂_neg]
  push_cast
  norm_num
  try ring

lemma evA_P0 (m n : ℕ) (x : ℂ) : evA (logPAP0 (aa m) (bb n)) x = P0p m n x := by
  rw [← P0poly_coe m n, evA_coe_poly]
  simp only [P0poly, P0p, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one,
    Polynomial.eval₂_neg]
  push_cast
  norm_num
  try ring

lemma evA_Rh (m n : ℕ) (ra rb rab : ℤ) (x : ℂ) :
    evA (PowerSeries.C (ra : ℚ) * RaFam (aa m) (bb n)
        + PowerSeries.C (rb : ℚ) * RbFam (aa m) (bb n)
        + PowerSeries.C (rab : ℚ) * RabFam (aa m) (bb n)) x = Rhp m n ra rb rab x := by
  rw [← Rhpoly_coe m n ra rb rab, evA_coe_poly]
  simp only [Rhpoly, Rapoly, Rbpoly, Rabpoly, Rhp, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.eval₂_one, Polynomial.eval₂_neg]
  push_cast
  norm_num
  try ring


/-! ## Coefficient bounds and summability -/

lemma coef_bound (m n : ℕ) (ra rb rab r0 : ℤ) (hR : PRadius) (hAdm : CAdm m n)
    (hRel : CRel m n ra rb rab r0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ‖coef m n ra rb rab r0 k‖ ≤ C * (3 / 2 : ℝ) ^ k := by
  obtain ⟨C, hC⟩ := hR m n ra rb rab r0 hAdm hRel
  refine ⟨|C|, abs_nonneg C, fun k => ?_⟩
  have h1 : |(((PowerSeries.coeff k (Pt m n ra rb rab r0) : ℚ)) : ℝ)| ≤ C * (3 / 2) ^ k := hC k
  rw [coef, ← Complex.ofReal_ratCast, Complex.norm_real]
  exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))

lemma norm_add_nat (k c : ℕ) : ‖((k : ℂ) + (c : ℂ))‖ = (k : ℝ) + (c : ℝ) := by
  rw [show ((k : ℂ) + (c : ℂ)) = ((k + c : ℕ) : ℂ) by push_cast; ring]
  rw [Complex.norm_natCast]
  push_cast; ring

lemma norm_add_one (k : ℕ) : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
  simpa using norm_add_nat k 1

lemma norm_add_two (k : ℕ) : ‖((k : ℂ) + 2)‖ = (k : ℝ) + 2 := by
  simpa using norm_add_nat k 2

lemma summable_norm_U0 (m n : ℕ) (ra rb rab r0 : ℤ) (hR : PRadius) (hAdm : CAdm m n)
    (hRel : CRel m n ra rb rab r0) (x : ℂ) (hx : ‖x‖ ≤ 1 / 2) :
    Summable fun k : ℕ => ‖coef m n ra rb rab r0 k * x ^ k‖ := by
  obtain ⟨C, hC0, hC⟩ := coef_bound m n ra rb rab r0 hR hAdm hRel
  have hg : Summable fun k : ℕ => C * (3 / 4 : ℝ) ^ k :=
    (summable_geometric_iff_norm_lt_one.mpr (by norm_num)).mul_left C
  refine Summable.of_nonneg_of_le (g := fun k : ℕ => ‖coef m n ra rb rab r0 k * x ^ k‖)
    (f := fun k : ℕ => C * (3 / 4 : ℝ) ^ k) (fun k => norm_nonneg _) (fun k => ?_) hg
  have hx' : ((3 : ℝ) / 2) * ‖x‖ ≤ 3 / 4 := by nlinarith [norm_nonneg x, hx]
  calc ‖coef m n ra rb rab r0 k * x ^ k‖
      = ‖coef m n ra rb rab r0 k‖ * ‖x‖ ^ k := by rw [norm_mul, norm_pow]
    _ ≤ (C * (3 / 2) ^ k) * ‖x‖ ^ k := mul_le_mul_of_nonneg_right (hC k) (by positivity)
    _ = C * ((3 / 2) * ‖x‖) ^ k := by rw [mul_pow]; ring
    _ ≤ C * (3 / 4) ^ k := by
        apply mul_le_mul_of_nonneg_left _ hC0
        exact pow_le_pow_left₀ (by positivity) hx' k

lemma summable_norm_U1 (m n : ℕ) (ra rb rab r0 : ℤ) (hR : PRadius) (hAdm : CAdm m n)
    (hRel : CRel m n ra rb rab r0) (x : ℂ) (hx : ‖x‖ ≤ 1 / 2) :
    Summable fun k : ℕ => ‖(((k : ℂ) + 1) * coef m n ra rb rab r0 (k + 1)) * x ^ k‖ := by
  obtain ⟨C, hC0, hC⟩ := coef_bound m n ra rb rab r0 hR hAdm hRel
  have h1 : Summable fun k : ℕ => (k : ℝ) * (3 / 4 : ℝ) ^ k := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (3/4:ℝ)) (by norm_num)
  have h2 : Summable fun k : ℕ => (3 / 4 : ℝ) ^ k :=
    summable_geometric_iff_norm_lt_one.mpr (by norm_num)
  have h3 : Summable fun k : ℕ => ((k : ℝ) + 1) * (3 / 4 : ℝ) ^ k := by
    have h4 : (fun k : ℕ => ((k : ℝ) + 1) * (3 / 4 : ℝ) ^ k)
        = (fun k : ℕ => (k : ℝ) * (3 / 4 : ℝ) ^ k + (3 / 4 : ℝ) ^ k) := by
      funext k; ring
    rw [h4]; exact h1.add h2
  have hg : Summable fun k : ℕ => C * (3 / 2) * ((k : ℝ) + 1) * (3 / 4 : ℝ) ^ k :=
    (h3.mul_left (C * (3 / 2))).congr (by intro k; ring)
  refine Summable.of_nonneg_of_le (g := fun k : ℕ => ‖(((k : ℂ) + 1) * coef m n ra rb rab r0 (k + 1)) * x ^ k‖)
    (f := fun k : ℕ => C * (3 / 2) * ((k : ℝ) + 1) * (3 / 4 : ℝ) ^ k)
    (fun k => norm_nonneg _) (fun k => ?_) hg
  have hk : (0:ℝ) ≤ (k:ℝ) + 1 := by positivity
  have hx' : ((3 : ℝ) / 2) * ‖x‖ ≤ 3 / 4 := by nlinarith [norm_nonneg x, hx]
  have h4 : C * (3 / 2) ^ (k + 1) * ‖x‖ ^ k = C * (3 / 2) * ((3 / 2) * ‖x‖) ^ k := by
    rw [pow_succ]; ring
  calc ‖(((k : ℂ) + 1) * coef m n ra rb rab r0 (k + 1)) * x ^ k‖
      = ((k:ℝ) + 1) * (‖coef m n ra rb rab r0 (k + 1)‖ * ‖x‖ ^ k) := by
        rw [norm_mul, norm_mul, norm_pow, norm_add_one]; ring
    _ ≤ ((k:ℝ) + 1) * ((C * (3 / 2) ^ (k + 1)) * ‖x‖ ^ k) := by
        apply mul_le_mul_of_nonneg_left _ hk
        exact mul_le_mul_of_nonneg_right (hC (k + 1)) (by positivity)
    _ = ((k:ℝ) + 1) * (C * (3 / 2) * ((3 / 2) * ‖x‖) ^ k) := by rw [h4]
    _ ≤ ((k:ℝ) + 1) * (C * (3 / 2) * (3 / 4 : ℝ) ^ k) := by
        apply mul_le_mul_of_nonneg_left _ hk
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (by positivity) hx' k
    _ = C * (3 / 2) * ((k : ℝ) + 1) * (3 / 4 : ℝ) ^ k := by ring

lemma summable_norm_U2 (m n : ℕ) (ra rb rab r0 : ℤ) (hR : PRadius) (hAdm : CAdm m n)
    (hRel : CRel m n ra rb rab r0) (x : ℂ) (hx : ‖x‖ ≤ 1 / 2) :
    Summable fun k : ℕ => ‖(((k : ℂ) + 1) * ((k : ℂ) + 2) * coef m n ra rb rab r0 (k + 2)) * x ^ k‖ := by
  obtain ⟨C, hC0, hC⟩ := coef_bound m n ra rb rab r0 hR hAdm hRel
  have h1 : Summable fun k : ℕ => (k : ℝ) ^ 2 * (3 / 4 : ℝ) ^ k := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 (r := (3/4:ℝ)) (by norm_num)
  have h2 : Summable fun k : ℕ => (k : ℝ) * (3 / 4 : ℝ) ^ k := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (3/4:ℝ)) (by norm_num)
  have h3 : Summable fun k : ℕ => (3 / 4 : ℝ) ^ k :=
    summable_geometric_iff_norm_lt_one.mpr (by norm_num)
  have h4 : Summable fun k : ℕ => ((k : ℝ) + 1) * ((k : ℝ) + 2) * (3 / 4 : ℝ) ^ k := by
    have h5 : (fun k : ℕ => ((k : ℝ) + 1) * ((k : ℝ) + 2) * (3 / 4 : ℝ) ^ k)
        = (fun k : ℕ => (k:ℝ)^2 * (3/4:ℝ)^k + 3 * ((k:ℝ) * (3/4:ℝ)^k) + 2 * (3/4:ℝ)^k) := by
      funext k; ring
    rw [h5]
    exact (h1.add (h2.mul_left 3)).add (h3.mul_left 2)
  have hg : Summable fun k : ℕ =>
      C * (3 / 2) ^ 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * (3 / 4 : ℝ) ^ k) :=
    (h4.mul_left (C * (3/2)^2)).congr (by intro k; ring)
  refine Summable.of_nonneg_of_le
    (g := fun k : ℕ => ‖(((k : ℂ) + 1) * ((k : ℂ) + 2) * coef m n ra rb rab r0 (k + 2)) * x ^ k‖)
    (f := fun k : ℕ => C * (3 / 2) ^ 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * (3 / 4 : ℝ) ^ k))
    (fun k => norm_nonneg _) (fun k => ?_) hg
  have hk : (0:ℝ) ≤ ((k:ℝ) + 1) * ((k:ℝ) + 2) := by positivity
  have hx' : ((3 : ℝ) / 2) * ‖x‖ ≤ 3 / 4 := by nlinarith [norm_nonneg x, hx]
  have h6 : C * (3 / 2) ^ (k + 2) * ‖x‖ ^ k
      = C * (3 / 2) ^ 2 * ((3 / 2) * ‖x‖) ^ k := by
    rw [pow_add]; ring
  calc ‖(((k : ℂ) + 1) * ((k : ℂ) + 2) * coef m n ra rb rab r0 (k + 2)) * x ^ k‖
      = ((k:ℝ) + 1) * ((k:ℝ) + 2) * (‖coef m n ra rb rab r0 (k + 2)‖ * ‖x‖ ^ k) := by
        rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_add_one, norm_add_two]; ring
    _ ≤ ((k:ℝ) + 1) * ((k:ℝ) + 2) * ((C * (3 / 2) ^ (k + 2)) * ‖x‖ ^ k) := by
        apply mul_le_mul_of_nonneg_left _ hk
        exact mul_le_mul_of_nonneg_right (hC (k + 2)) (by positivity)
    _ = ((k:ℝ) + 1) * ((k:ℝ) + 2) * (C * (3 / 2) ^ 2 * ((3 / 2) * ‖x‖) ^ k) := by
        rw [h6]
    _ ≤ ((k:ℝ) + 1) * ((k:ℝ) + 2) * (C * (3 / 2) ^ 2 * (3 / 4 : ℝ) ^ k) := by
        apply mul_le_mul_of_nonneg_left _ hk
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (by positivity) hx' k
    _ = C * (3 / 2) ^ 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * (3 / 4 : ℝ) ^ k) := by ring

end
end Work.CLift
