import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Commons.Analysis.ExponentialSums.quadratic_phase_residue_factor
import Submission.Commons.Analysis.ExponentialSums.sum_exp_quadratic_vs_integral

namespace Commons.Analysis.ExponentialSums

open MeasureTheory intervalIntegral
open scoped BigOperators


/-- The additive character `e(x) = exp(2πi x)` of the reals. -/
noncomputable def expTwoPiI (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

lemma expTwoPiI_def (x : ℝ) : expTwoPiI x = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := rfl

/-- The character `e` takes values of modulus `1`. -/
lemma norm_expTwoPiI (x : ℝ) : ‖expTwoPiI x‖ = 1 := by
  rw [expTwoPiI_def,
    show (2 * Real.pi * Complex.I * (x:ℂ)) = ((2*Real.pi*x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Lipschitz bound for the character `e`: `‖e x - e y‖ ≤ 2π|x - y|`. -/
lemma norm_expTwoPiI_sub_le (x y : ℝ) : ‖expTwoPiI x - expTwoPiI y‖ ≤ 2 * Real.pi * |x - y| := by
  have h : expTwoPiI x - expTwoPiI y = expTwoPiI y * (expTwoPiI (x - y) - 1) := by
    rw [expTwoPiI_def, expTwoPiI_def, expTwoPiI_def, mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, norm_expTwoPiI, one_mul, expTwoPiI_def,
    show (2 * Real.pi * Complex.I * (((x-y) : ℝ) : ℂ)) = Complex.I * (((2 * Real.pi * (x - y)):ℝ):ℂ) by
      push_cast; ring]
  have hb := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (x - y))
  calc ‖Complex.exp (Complex.I * ↑(2*Real.pi*(x-y))) - 1‖
      ≤ ‖2 * Real.pi * (x - y)‖ := hb
    _ = 2 * Real.pi * |x - y| := by rw [Real.norm_eq_abs, abs_mul]; simp [abs_of_nonneg Real.pi_pos.le]

/-- Continuity of the quadratic character `s ↦ e(a s²)`. -/
lemma continuous_expTwoPiI_quad (a : ℝ) : Continuous (fun s : ℝ => expTwoPiI (a * s ^ 2)) := by
  rw [show (fun s : ℝ => expTwoPiI (a * s^2))
      = (fun s : ℝ => Complex.exp (2 * Real.pi * Complex.I * (((a * s^2) : ℝ) : ℂ))) from rfl]
  fun_prop

/-- The oscillatory quadratic integral is bounded by `1` on the unit interval. -/
lemma norm_integral_expTwoPiI_quad_le (a : ℝ) :
    ‖∫ s in (0:ℝ)..1, expTwoPiI (a * s^2)‖ ≤ 1 := by
  calc ‖∫ s in (0:ℝ)..1, expTwoPiI (a*s^2)‖
      ≤ ∫ s in (0:ℝ)..1, ‖expTwoPiI (a*s^2)‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = 1 := by simp_rw [norm_expTwoPiI]; simp

/-- Comparison of two oscillatory quadratic integrals: the difference of
`∫_0^1 e(a s²) ds` and `∫_0^1 e(b s²) ds` is at most `2π|a - b|/3`. -/
lemma norm_integral_expTwoPiI_quad_sub_le (a b : ℝ) :
    ‖(∫ s in (0:ℝ)..1, expTwoPiI (a * s^2)) - (∫ s in (0:ℝ)..1, expTwoPiI (b * s^2))‖
      ≤ 2 * Real.pi * |a - b| / 3 := by
  have hsub : (∫ s in (0:ℝ)..1, expTwoPiI (a*s^2)) - (∫ s in (0:ℝ)..1, expTwoPiI (b*s^2))
      = ∫ s in (0:ℝ)..1, (expTwoPiI (a*s^2) - expTwoPiI (b*s^2)) := by
    rw [intervalIntegral.integral_sub ((continuous_expTwoPiI_quad a).intervalIntegrable _ _)
      ((continuous_expTwoPiI_quad b).intervalIntegrable _ _)]
  rw [hsub]
  have hpoint : ∀ s : ℝ, ‖expTwoPiI (a*s^2) - expTwoPiI (b*s^2)‖ ≤ 2 * Real.pi * |a - b| * s^2 := by
    intro s
    calc ‖expTwoPiI (a*s^2) - expTwoPiI (b*s^2)‖
        ≤ 2 * Real.pi * |a*s^2 - b*s^2| := norm_expTwoPiI_sub_le _ _
      _ = 2 * Real.pi * |a - b| * s^2 := by
          rw [show a*s^2 - b*s^2 = (a-b)*s^2 by ring, abs_mul, abs_of_nonneg (sq_nonneg s)]
          ring
  have hint2 : IntervalIntegrable (fun s : ℝ => 2 * Real.pi * |a - b| * s^2) volume 0 1 :=
    (by fun_prop : Continuous (fun s : ℝ => 2 * Real.pi * |a - b| * s^2)).intervalIntegrable _ _
  calc ‖∫ s in (0:ℝ)..1, (expTwoPiI (a*s^2) - expTwoPiI (b*s^2))‖
      ≤ ∫ s in (0:ℝ)..1, 2 * Real.pi * |a - b| * s^2 := by
        refine intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by norm_num) ?_ hint2
        filter_upwards with s _
        exact hpoint s
    _ = 2 * Real.pi * |a - b| / 3 := by
        rw [show (∫ s in (0:ℝ)..1, 2 * Real.pi * |a - b| * s^2)
              = (2 * Real.pi * |a - b|) * ∫ s in (0:ℝ)..1, s^2 by
              rw [← intervalIntegral.integral_const_mul]]
        rw [integral_pow]
        norm_num
        ring

/-- Arithmetic of the residue blocks: for `r < q ≤ N` the number
`P = (N + q - 1 - r) / q` of integers `p` with `p q + r < N` satisfies `1 ≤ P`,
`P q ≤ N + q` and `N - q ≤ P q`. -/
lemma div_block_bounds {N q r : ℕ} (hq : 1 ≤ q) (hr : r < q) (hqN : q ≤ N) :
    1 ≤ (N + q - 1 - r) / q ∧
    ((((N + q - 1 - r) / q : ℕ)) : ℝ) * q ≤ (N : ℝ) + q ∧
    (N : ℝ) - q ≤ ((((N + q - 1 - r) / q : ℕ)) : ℝ) * q := by
  set P : ℕ := (N + q - 1 - r) / q with hP
  have hq0 : 0 < q := by omega
  have hrN : r ≤ N - 1 := by omega
  have hle : P * q ≤ N + q - 1 - r := by rw [hP]; exact Nat.div_mul_le_self _ _
  have hlt : N + q - 1 - r < (P + 1) * q := by
    rw [hP]
    exact Nat.lt_mul_of_div_lt (Nat.lt_succ_self _) hq0
  have he : N + q - 1 - r = (N - 1 - r) + q := by omega
  have hkey : N - 1 - r < P * q := by
    rw [he] at hlt
    have hlt2 : (N - 1 - r) + q < P * q + q := by
      have h : (P + 1) * q = P * q + q := by ring
      rwa [h] at hlt
    omega
  have hcast1 : ((N - 1 - r : ℕ) : ℝ) = (N:ℝ) - 1 - r := by
    rw [show N - 1 - r = (N - 1) - r by omega, Nat.cast_sub hrN]
    have h1 : ((N - 1 : ℕ) : ℝ) = (N:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N)]; simp
    rw [h1]
  have hcast2 : ((N + q - 1 - r : ℕ) : ℝ) = (N:ℝ) + q - 1 - r := by
    have hle1 : 1 + r ≤ N + q := by omega
    rw [show N + q - 1 - r = (N + q) - (1 + r) by omega, Nat.cast_sub hle1]
    push_cast
    ring
  have hPq : ((N - 1 - r : ℕ) : ℝ) < (P:ℝ) * q := by
    have h2 : ((N - 1 - r : ℕ) : ℝ) < ((P * q : ℕ) : ℝ) := by exact_mod_cast hkey
    rwa [Nat.cast_mul] at h2
  rw [hcast1] at hPq
  refine ⟨?_, ?_, ?_⟩
  · by_contra hc
    simp only [not_le] at hc
    have hc0 : P = 0 := Nat.lt_one_iff.mp hc
    rw [hc0] at hkey
    simp at hkey
  · have h1 : (P:ℝ) * q ≤ ((N + q - 1 - r : ℕ) : ℝ) := by exact_mod_cast hle
    rw [hcast2] at h1
    linarith
  · have hrq : (r:ℝ) ≤ (q:ℝ) - 1 := by
      have h1 : r ≤ q - 1 := by omega
      have h2 : (r:ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast h1
      rw [Nat.cast_sub (by omega : 1 ≤ q)] at h2
      push_cast at h2
      linarith
    linarith [hPq]

/-- The residue-class factorisation of the quadratic Weyl sum, phrased with the
character `e(x) = exp(2πi x)`. -/
lemma residue_factor_expTwoPiI (N q : ℕ) (hq : 0 < q) (a : ℤ) (β : ℝ) :
    (∑ n ∈ Finset.range N, expTwoPiI (((a : ℝ) / (q : ℝ) + β) * (n : ℝ) ^ 2))
      = ∑ r ∈ Finset.range q, expTwoPiI ((a : ℝ) / (q : ℝ) * (r : ℝ) ^ 2)
          * ∑ p ∈ Finset.range ((N + q - 1 - r) / q),
              expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ 2) := by
  simp only [expTwoPiI_def]
  rw [quadratic_phase_residue_factor N q hq a β]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  have h1 : Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * ((r : ℝ) ^ 2 : ℂ) / (q : ℂ)))
      = Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) / (q : ℝ) * (r : ℝ) ^ 2 : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [h1]

/-- Bound for a single residue block of the quadratic Weyl sum: the contribution of the
residue class `r mod q` to the major-arc sum differs from `(1/q) v_N(β)` by at most
`(28π/3)|β|(N+q)²/N + 1/N`. -/
lemma quadratic_major_arc_block_bound
    (N q r P : ℕ) (β : ℝ) (hq : 1 ≤ q) (hN : 1 ≤ N) (hr : r < q)
    (hP1 : 1 ≤ P) (hPq_le : (P:ℝ) * q ≤ (N:ℝ) + q) (hPq_ge : (N:ℝ) - q ≤ (P:ℝ) * q) :
    ‖(N : ℂ)⁻¹ * (∑ p ∈ Finset.range P, expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ 2))
      - (q : ℂ)⁻¹ * (∫ s in (0:ℝ)..1, expTwoPiI (β * (N:ℝ)^2 * s^2))‖
    ≤ (28 * Real.pi / 3) * |β| * (((N:ℝ) + (q:ℝ))^2 / (N:ℝ)) + 1 / (N:ℝ) := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hP0 : (0:ℝ) < (P:ℝ) := by exact_mod_cast hP1
  have hPc : (P:ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast]; exact Complex.ofReal_ne_zero.mpr (ne_of_gt hP0)
  set Y : ℝ := ((N:ℝ) + (q:ℝ))^2 / (N:ℝ) with hY
  set A : ℂ := ∑ p ∈ Finset.range P, expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ 2) with hA
  set B : ℂ := ∑ p ∈ Finset.range P, expTwoPiI (β * (q:ℝ)^2 * (p:ℝ)^2) with hB
  set v : ℂ := ∫ s in (0:ℝ)..1, expTwoPiI (β * (N:ℝ)^2 * s^2) with hv
  set u : ℂ := ∫ s in (0:ℝ)..1, expTwoPiI (β * (q:ℝ)^2 * (P:ℝ)^2 * s^2) with hu
  set e : ℂ := (P:ℂ)⁻¹ * B - u with he
  set κ : ℂ := ((((P:ℝ)/(N:ℝ)) : ℝ) : ℂ) with hκ
  set lam : ℂ := (q:ℂ)⁻¹ with hlam
  -- norms of the scalars
  have hNnorm : ‖(N:ℂ)⁻¹‖ = 1/(N:ℝ) := by
    rw [norm_inv, Complex.norm_natCast, one_div]
  have hYe : Y = ((N:ℝ) + (q:ℝ))^2 / (N:ℝ) := hY
  -- split
  have hsplit : (N:ℂ)⁻¹ * A - (q:ℂ)⁻¹ * v
      = ((N:ℂ)⁻¹ * A - (N:ℂ)⁻¹ * B) + ((N:ℂ)⁻¹ * B - (q:ℂ)⁻¹ * v) := by ring
  have hnorm : ‖(N:ℂ)⁻¹ * A - (q:ℂ)⁻¹ * v‖
      ≤ ‖(N:ℂ)⁻¹ * A - (N:ℂ)⁻¹ * B‖ + ‖(N:ℂ)⁻¹ * B - (q:ℂ)⁻¹ * v‖ := by
    rw [hsplit]; exact norm_add_le _ _
  -- PART 1
  have hpq_le : ∀ p : ℕ, p < P → (p:ℝ) * q ≤ (N:ℝ) := by
    intro p hp
    have hp1 : p ≤ P - 1 := by omega
    have h2 : (p:ℝ) ≤ ((P - 1 : ℕ) : ℝ) := by exact_mod_cast hp1
    rw [Nat.cast_sub hP1] at h2
    push_cast at h2
    nlinarith [hPq_le]
  have hAB : ‖A - B‖ ≤ 4 * Real.pi * |β| * ((N:ℝ) + (q:ℝ))^2 := by
    have hper : ∀ p ∈ Finset.range P,
        ‖expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ 2) - expTwoPiI (β * (q:ℝ)^2 * (p:ℝ)^2)‖
          ≤ 2 * Real.pi * |β| * ((q:ℝ) * (2*(N:ℝ) + (q:ℝ))) := by
      intro p hp
      have hpP : p < P := Finset.mem_range.mp hp
      have hpq := hpq_le p hpP
      calc ‖expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ 2) - expTwoPiI (β * (q:ℝ)^2 * (p:ℝ)^2)‖
          ≤ 2 * Real.pi * |β * (((p * q + r : ℕ) : ℝ)) ^ 2 - β * (q:ℝ)^2 * (p:ℝ)^2| :=
            norm_expTwoPiI_sub_le _ _
        _ = 2 * Real.pi * |β| * ((r:ℝ) * (2*(p:ℝ)*(q:ℝ) + (r:ℝ))) := by
            rw [show β * (((p * q + r : ℕ) : ℝ)) ^ 2 - β * (q:ℝ)^2 * (p:ℝ)^2
                  = β * ((r:ℝ) * (2*(p:ℝ)*(q:ℝ) + (r:ℝ))) by push_cast; ring]
            rw [abs_mul,
              abs_of_nonneg (by positivity : (0:ℝ) ≤ (r:ℝ) * (2*(p:ℝ)*(q:ℝ) + (r:ℝ)))]
            ring
        _ ≤ 2 * Real.pi * |β| * ((q:ℝ) * (2*(N:ℝ) + (q:ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have hrq' : (r:ℝ) ≤ (q:ℝ) := by exact_mod_cast le_of_lt hr
            exact mul_le_mul hrq' (by linarith) (by positivity) (by positivity)
    calc ‖A - B‖
        = ‖∑ p ∈ Finset.range P, (expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ 2)
            - expTwoPiI (β * (q:ℝ)^2 * (p:ℝ)^2))‖ := by
          rw [hA, hB, Finset.sum_sub_distrib]
      _ ≤ ∑ p ∈ Finset.range P, ‖expTwoPiI (β * (((p * q + r : ℕ) : ℝ)) ^ 2)
            - expTwoPiI (β * (q:ℝ)^2 * (p:ℝ)^2)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ Finset.range P, 2 * Real.pi * |β| * ((q:ℝ) * (2*(N:ℝ) + (q:ℝ))) :=
          Finset.sum_le_sum hper
      _ = (P:ℝ) * (2 * Real.pi * |β| * ((q:ℝ) * (2*(N:ℝ) + (q:ℝ)))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 4 * Real.pi * |β| * ((N:ℝ) + (q:ℝ))^2 := by
          have hbase : ((P:ℝ)*(q:ℝ)) * (2*(N:ℝ) + (q:ℝ))
              ≤ ((N:ℝ)+(q:ℝ)) * (2*((N:ℝ)+(q:ℝ))) :=
            mul_le_mul hPq_le (by linarith) (by positivity) (by positivity)
          calc (P:ℝ) * (2 * Real.pi * |β| * ((q:ℝ) * (2*(N:ℝ) + (q:ℝ))))
              = (2 * Real.pi * |β|) * (((P:ℝ)*(q:ℝ)) * (2*(N:ℝ) + (q:ℝ))) := by ring
            _ ≤ (2 * Real.pi * |β|) * (((N:ℝ)+(q:ℝ)) * (2*((N:ℝ)+(q:ℝ)))) :=
                mul_le_mul_of_nonneg_left hbase (by positivity)
            _ = 4 * Real.pi * |β| * ((N:ℝ) + (q:ℝ))^2 := by ring
  have hpart1 : ‖(N:ℂ)⁻¹ * A - (N:ℂ)⁻¹ * B‖ ≤ 4 * Real.pi * |β| * Y := by
    rw [hYe]
    calc ‖(N:ℂ)⁻¹ * A - (N:ℂ)⁻¹ * B‖ = ‖(N:ℂ)⁻¹‖ * ‖A - B‖ := by rw [← mul_sub, norm_mul]
      _ = (1/(N:ℝ)) * ‖A - B‖ := by rw [hNnorm]
      _ ≤ (1/(N:ℝ)) * (4 * Real.pi * |β| * ((N:ℝ) + (q:ℝ))^2) :=
          mul_le_mul_of_nonneg_left hAB (by positivity)
      _ = 4 * Real.pi * |β| * (((N:ℝ) + (q:ℝ))^2 / (N:ℝ)) := by ring
  -- PART 2
  have hκeq : κ = (P:ℂ) * (N:ℂ)⁻¹ := by
    rw [hκ]; push_cast; rw [div_eq_mul_inv]
  have hkey1 : (N:ℂ)⁻¹ * B = κ * ((P:ℂ)⁻¹ * B) := by
    rw [hκeq]
    rw [show (P:ℂ) * (N:ℂ)⁻¹ * ((P:ℂ)⁻¹ * B) = (N:ℂ)⁻¹ * B by
      calc (P:ℂ) * (N:ℂ)⁻¹ * ((P:ℂ)⁻¹ * B)
          = (N:ℂ)⁻¹ * ((P:ℂ) * (P:ℂ)⁻¹) * B := by ring
        _ = (N:ℂ)⁻¹ * B := by rw [mul_inv_cancel₀ hPc]; ring]
  have hqinvcast : (q:ℂ)⁻¹ = (((q:ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [show (q:ℂ) = ((q:ℝ) : ℂ) by exact Complex.ofReal_natCast q]
    exact (Complex.ofReal_inv (q:ℝ)).symm
  have hlamnorm : ‖lam‖ = 1/(q:ℝ) := by
    rw [hlam, norm_inv, Complex.norm_natCast, one_div]
  have hκnorm : ‖κ‖ = (P:ℝ)/(N:ℝ) := by
    have h : ‖κ‖ = |(((P:ℝ)/(N:ℝ)) : ℝ)| := by rw [hκ]; exact RCLike.norm_ofReal _
    rw [h, abs_of_nonneg (by positivity)]
  have hdecomp : (N:ℂ)⁻¹ * B - (q:ℂ)⁻¹ * v = (κ - lam) * u + lam * (u - v) + κ * e := by
    rw [hkey1, he, hlam]
    ring
  -- the three pieces
  have hδ : ‖κ - lam‖ ≤ 1/(N:ℝ) := by
    have hδeq : κ - lam = ((((P:ℝ)/(N:ℝ) - (1:ℝ)/(q:ℝ)) : ℝ) : ℂ) := by
      rw [hκ, hlam, hqinvcast]; push_cast; ring
    have hδn : ‖κ - lam‖ = |(((P:ℝ)/(N:ℝ) - (1:ℝ)/(q:ℝ)) : ℝ)| := by
      rw [hδeq]; exact RCLike.norm_ofReal _
    rw [hδn]
    have h1 : (P:ℝ)/(N:ℝ) - (1:ℝ)/(q:ℝ) = ((P:ℝ)*(q:ℝ) - (N:ℝ))/((N:ℝ)*(q:ℝ)) := by
      field_simp
    rw [h1, abs_div, abs_of_pos (by positivity : (0:ℝ) < (N:ℝ)*(q:ℝ))]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have habs : |(P:ℝ)*(q:ℝ) - (N:ℝ)| ≤ (q:ℝ) :=
      abs_le.mpr ⟨by linarith [hPq_ge], by linarith [hPq_le]⟩
    nlinarith [habs]
  have hpiece1 : ‖(κ - lam) * u‖ ≤ 1/(N:ℝ) := by
    rw [norm_mul]
    calc ‖κ - lam‖ * ‖u‖ ≤ (1/(N:ℝ)) * 1 :=
          mul_le_mul hδ (norm_integral_expTwoPiI_quad_le _) (norm_nonneg _) (by positivity)
      _ = 1/(N:ℝ) := by ring
  have huv : ‖u - v‖ ≤ (2*Real.pi/3) * |β| * ((q:ℝ) * (2*(N:ℝ) + (q:ℝ))) := by
    have h1 : ‖u - v‖ ≤ 2 * Real.pi * |β * (q:ℝ)^2 * (P:ℝ)^2 - β * (N:ℝ)^2| / 3 := by
      rw [hu, hv]; exact norm_integral_expTwoPiI_quad_sub_le _ _
    have h2 : |β * (q:ℝ)^2 * (P:ℝ)^2 - β * (N:ℝ)^2|
        = |β| * |(q:ℝ)^2*(P:ℝ)^2 - (N:ℝ)^2| := by
      rw [show β * (q:ℝ)^2 * (P:ℝ)^2 - β * (N:ℝ)^2 = β * ((q:ℝ)^2*(P:ℝ)^2 - (N:ℝ)^2) by ring,
        abs_mul]
    have h3 : |(q:ℝ)^2*(P:ℝ)^2 - (N:ℝ)^2| ≤ (q:ℝ) * (2*(N:ℝ) + (q:ℝ)) := by
      have hfac : (q:ℝ)^2*(P:ℝ)^2 - (N:ℝ)^2
          = ((P:ℝ)*(q:ℝ) - (N:ℝ)) * ((P:ℝ)*(q:ℝ) + (N:ℝ)) := by ring
      rw [hfac, abs_mul]
      have h4 : |(P:ℝ)*(q:ℝ) - (N:ℝ)| ≤ (q:ℝ) :=
        abs_le.mpr ⟨by linarith [hPq_ge], by linarith [hPq_le]⟩
      have h5 : |(P:ℝ)*(q:ℝ) + (N:ℝ)| ≤ 2*(N:ℝ) + (q:ℝ) := by
        rw [abs_of_nonneg (by positivity)]; linarith [hPq_le]
      exact mul_le_mul h4 h5 (abs_nonneg _) (by positivity)
    calc ‖u - v‖ ≤ 2 * Real.pi * |β * (q:ℝ)^2 * (P:ℝ)^2 - β * (N:ℝ)^2| / 3 := h1
      _ = (2*Real.pi/3) * |β| * |(q:ℝ)^2*(P:ℝ)^2 - (N:ℝ)^2| := by rw [h2]; ring
      _ ≤ (2*Real.pi/3) * |β| * ((q:ℝ) * (2*(N:ℝ) + (q:ℝ))) := by
          apply mul_le_mul_of_nonneg_left h3 (by positivity)
  have hpiece2 : ‖lam * (u - v)‖ ≤ (4*Real.pi/3) * |β| * Y := by
    rw [norm_mul, hlamnorm, hYe]
    calc (1/(q:ℝ)) * ‖u - v‖
        ≤ (1/(q:ℝ)) * ((2*Real.pi/3) * |β| * ((q:ℝ) * (2*(N:ℝ) + (q:ℝ)))) :=
          mul_le_mul_of_nonneg_left huv (by positivity)
      _ = (2*Real.pi/3) * |β| * (2*(N:ℝ) + (q:ℝ)) := by field_simp
      _ ≤ (2*Real.pi/3) * |β| * (2*((N:ℝ) + (q:ℝ))) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ (4*Real.pi/3) * |β| * (((N:ℝ) + (q:ℝ))^2 / (N:ℝ)) := by
          have h1 : ((N:ℝ) + (q:ℝ)) ≤ ((N:ℝ) + (q:ℝ))^2 / (N:ℝ) := by
            rw [le_div_iff₀ hN0]
            nlinarith [hq0, hN0]
          have h2 : (2*Real.pi/3) * |β| * (2*((N:ℝ) + (q:ℝ)))
              = (4*Real.pi/3) * |β| * ((N:ℝ) + (q:ℝ)) := by ring
          rw [h2]
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have he_bd : ‖e‖ ≤ 4 * Real.pi * |β| * (q:ℝ)^2 * (P:ℝ) := by
    rw [he]
    have := sum_exp_quadratic_vs_integral P hP1 (β * (q:ℝ)^2)
    calc ‖(P:ℂ)⁻¹ * B - u‖ ≤ 4 * Real.pi * |β * (q:ℝ)^2| * (P:ℝ) := this
      _ = 4 * Real.pi * |β| * (q:ℝ)^2 * (P:ℝ) := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (q:ℝ))]; ring
  have hpiece3 : ‖κ * e‖ ≤ 4 * Real.pi * |β| * Y := by
    rw [norm_mul, hκnorm, hYe]
    calc (P:ℝ)/(N:ℝ) * ‖e‖ ≤ ((P:ℝ)/(N:ℝ)) * (4 * Real.pi * |β| * (q:ℝ)^2 * (P:ℝ)) :=
          mul_le_mul_of_nonneg_left he_bd (by positivity)
      _ = 4 * Real.pi * |β| * (((P:ℝ)*(q:ℝ))^2 / (N:ℝ)) := by field_simp
      _ ≤ 4 * Real.pi * |β| * (((N:ℝ) + (q:ℝ))^2 / (N:ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply div_le_div_of_nonneg_right _ (le_of_lt hN0)
          have h0 : (0:ℝ) ≤ (P:ℝ)*(q:ℝ) := by positivity
          nlinarith [hPq_le, h0]
  have hpart2 : ‖(N:ℂ)⁻¹ * B - (q:ℂ)⁻¹ * v‖
      ≤ (16*Real.pi/3) * |β| * Y + 1/(N:ℝ) := by
    rw [hdecomp]
    calc ‖(κ - lam) * u + lam * (u - v) + κ * e‖
        ≤ ‖(κ - lam) * u + lam * (u - v)‖ + ‖κ * e‖ := norm_add_le _ _
      _ ≤ (‖(κ - lam) * u‖ + ‖lam * (u - v)‖) + ‖κ * e‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (1/(N:ℝ) + (4*Real.pi/3) * |β| * Y) + 4 * Real.pi * |β| * Y :=
          add_le_add (add_le_add hpiece1 hpiece2) hpiece3
      _ = (16*Real.pi/3) * |β| * Y + 1/(N:ℝ) := by ring
  calc ‖(N:ℂ)⁻¹ * A - (q:ℂ)⁻¹ * v‖
      ≤ ‖(N:ℂ)⁻¹ * A - (N:ℂ)⁻¹ * B‖ + ‖(N:ℂ)⁻¹ * B - (q:ℂ)⁻¹ * v‖ := hnorm
    _ ≤ 4 * Real.pi * |β| * Y + ((16*Real.pi/3) * |β| * Y + 1/(N:ℝ)) := add_le_add hpart1 hpart2
    _ = (28 * Real.pi / 3) * |β| * Y + 1 / (N:ℝ) := by ring


/-- Major-arc approximation for the quadratic Weyl sum.  Writing `α = a/q + β`, the
normalized sum `(1/N) ∑_{n<N} e(α n²)` is, up to an explicit error, the product of the
complete quadratic Gauss-type sum `q⁻¹ ∑_{r<q} e(a r²/q)` with the oscillatory integral
`v_N(β) = ∫_0^1 e(β N² s²) ds`.

This is the algebraic core of the major-arc analysis (Bourgain, *Pointwise ergodic theorems
for arithmetic sets* §6; Krause, arXiv:1402.1803, §6).  The exact residue-class
factorisation is `Commons.Analysis.ExponentialSums.quadratic_phase_residue_factor`: expand
`n = p q + r` and factor out `e(a r²/q)`.  The inner `β`-sum over `p` is compared with its
continuous analogue (a Riemann sum with mesh `q`) using the derivative bound of
`Commons.Analysis.ExponentialSums.sum_exp_quadratic_vs_integral`; the two resulting error
sources are the Riemann-sum error `≈ |β| q (N+q)²/N` and the endpoint discrepancy `≈ q/N`. -/
theorem quadratic_major_arc_approx :
    ∃ C : ℝ, 0 < C ∧ ∀ (N q : ℕ) (a : ℤ) (β : ℝ), 1 ≤ q → 1 ≤ N →
      ‖(N : ℂ)⁻¹ * (∑ n ∈ Finset.range N,
            Complex.exp (2 * Real.pi * Complex.I *
              ((((a : ℝ) / (q : ℝ) + β) * (n : ℝ) ^ 2 : ℝ) : ℂ)))
          - (q : ℂ)⁻¹ * (∑ r ∈ Finset.range q,
                Complex.exp (2 * Real.pi * Complex.I *
                  (((a : ℝ) / (q : ℝ) * (r : ℝ) ^ 2 : ℝ) : ℂ)))
              * (∫ s in (0 : ℝ)..1,
                  Complex.exp (2 * Real.pi * Complex.I *
                    ((β * (N : ℝ) ^ 2 * s ^ 2 : ℝ) : ℂ)))‖
        ≤ C * (|β| * (q : ℝ) * ((N : ℝ) + (q : ℝ)) ^ 2 / (N : ℝ) + (q : ℝ) / (N : ℝ)) := by
  refine ⟨40, by norm_num, ?_⟩
  intro N q a β hq hN
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  change ‖(N : ℂ)⁻¹ * (∑ n ∈ Finset.range N, expTwoPiI (((a : ℝ) / (q : ℝ) + β) * (n : ℝ) ^ 2))
      - (q : ℂ)⁻¹ * (∑ r ∈ Finset.range q, expTwoPiI ((a : ℝ) / (q : ℝ) * (r : ℝ) ^ 2))
        * (∫ s in (0 : ℝ)..1, expTwoPiI (β * (N : ℝ) ^ 2 * s ^ 2))‖
      ≤ 40 * (|β| * (q : ℝ) * ((N : ℝ) + (q : ℝ)) ^ 2 / (N : ℝ) + (q : ℝ) / (N : ℝ))
  set S : ℂ := ∑ n ∈ Finset.range N, expTwoPiI (((a : ℝ) / (q : ℝ) + β) * (n : ℝ) ^ 2) with hS
  set G : ℂ := ∑ r ∈ Finset.range q, expTwoPiI ((a : ℝ) / (q : ℝ) * (r : ℝ) ^ 2) with hG
  set v : ℂ := ∫ s in (0 : ℝ)..1, expTwoPiI (β * (N : ℝ) ^ 2 * s ^ 2) with hv
  set T : ℝ := |β| * (q : ℝ) * ((N : ℝ) + (q : ℝ)) ^ 2 / (N : ℝ) + (q : ℝ) / (N : ℝ) with hT
  have hNnorm : ‖(N:ℂ)⁻¹‖ = 1/(N:ℝ) := by rw [norm_inv, Complex.norm_natCast, one_div]
  have hqnorm : ‖(q:ℂ)⁻¹‖ = 1/(q:ℝ) := by rw [norm_inv, Complex.norm_natCast, one_div]
  by_cases hqN : q ≤ N
  · have hq0 : 0 < q := by omega
    have hTY : T = |β| * (q:ℝ) * (((N:ℝ)+(q:ℝ))^2/(N:ℝ)) + (q:ℝ)/(N:ℝ) := by
      rw [hT]; ring
    have hfac : S = ∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ)*(r:ℝ)^2)
        * ∑ p ∈ Finset.range ((N+q-1-r)/q), expTwoPiI (β * (((p*q+r:ℕ):ℝ))^2) := by
      rw [hS]; exact residue_factor_expTwoPiI N q hq0 a β
    have hGv : (q:ℂ)⁻¹ * G * v
        = ∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ)*(r:ℝ)^2) * ((q:ℂ)⁻¹ * v) := by
      rw [hG, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun r hr => ?_)
      ring
    have hblock : ∀ r ∈ Finset.range q,
        ‖(N:ℂ)⁻¹ * (∑ p ∈ Finset.range ((N+q-1-r)/q), expTwoPiI (β * (((p*q+r:ℕ):ℝ))^2))
            - (q:ℂ)⁻¹ * v‖
        ≤ (28*Real.pi/3) * |β| * (((N:ℝ)+(q:ℝ))^2/(N:ℝ)) + 1/(N:ℝ) := by
      intro r hr
      have hrq : r < q := Finset.mem_range.mp hr
      have hb := div_block_bounds hq hrq hqN
      rw [hv]
      exact quadratic_major_arc_block_bound N q r ((N+q-1-r)/q) β hq hN hrq hb.1 hb.2.1 hb.2.2
    have hsum_eq : (N:ℂ)⁻¹ * S - (q:ℂ)⁻¹ * G * v
        = ∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ)*(r:ℝ)^2)
            * ((N:ℂ)⁻¹ * (∑ p ∈ Finset.range ((N+q-1-r)/q), expTwoPiI (β * (((p*q+r:ℕ):ℝ))^2))
               - (q:ℂ)⁻¹ * v) := by
      rw [hfac, hGv, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun r hr => ?_)
      ring
    have hmain : ‖(N:ℂ)⁻¹ * S - (q:ℂ)⁻¹ * G * v‖
        ≤ (q:ℝ) * ((28*Real.pi/3) * |β| * (((N:ℝ)+(q:ℝ))^2/(N:ℝ)) + 1/(N:ℝ)) := by
      rw [hsum_eq]
      calc ‖∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ)*(r:ℝ)^2)
              * ((N:ℂ)⁻¹ * (∑ p ∈ Finset.range ((N+q-1-r)/q), expTwoPiI (β * (((p*q+r:ℕ):ℝ))^2))
                 - (q:ℂ)⁻¹ * v)‖
          ≤ ∑ r ∈ Finset.range q, ‖expTwoPiI ((a:ℝ)/(q:ℝ)*(r:ℝ)^2)
              * ((N:ℂ)⁻¹ * (∑ p ∈ Finset.range ((N+q-1-r)/q), expTwoPiI (β * (((p*q+r:ℕ):ℝ))^2))
                 - (q:ℂ)⁻¹ * v)‖ := norm_sum_le _ _
        _ = ∑ r ∈ Finset.range q, ‖(N:ℂ)⁻¹ * (∑ p ∈ Finset.range ((N+q-1-r)/q),
              expTwoPiI (β * (((p*q+r:ℕ):ℝ))^2)) - (q:ℂ)⁻¹ * v‖ := by
            refine Finset.sum_congr rfl (fun r hr => ?_)
            rw [norm_mul, norm_expTwoPiI, one_mul]
        _ ≤ ∑ r ∈ Finset.range q, ((28*Real.pi/3) * |β| * (((N:ℝ)+(q:ℝ))^2/(N:ℝ)) + 1/(N:ℝ)) :=
            Finset.sum_le_sum hblock
        _ = (q:ℝ) * ((28*Real.pi/3) * |β| * (((N:ℝ)+(q:ℝ))^2/(N:ℝ)) + 1/(N:ℝ)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc ‖(N:ℂ)⁻¹ * S - (q:ℂ)⁻¹ * G * v‖
        ≤ (q:ℝ) * ((28*Real.pi/3) * |β| * (((N:ℝ)+(q:ℝ))^2/(N:ℝ)) + 1/(N:ℝ)) := hmain
      _ ≤ 40 * T := by
          rw [hTY]
          have hpi : (28*Real.pi/3) ≤ 40 := by nlinarith [Real.pi_lt_four]
          have hY : 0 ≤ |β| * (q:ℝ) * (((N:ℝ)+(q:ℝ))^2/(N:ℝ)) := by positivity
          have hqN0 : 0 ≤ (q:ℝ)/(N:ℝ) := by positivity
          calc (q:ℝ) * ((28*Real.pi/3) * |β| * (((N:ℝ)+(q:ℝ))^2/(N:ℝ)) + 1/(N:ℝ))
              = (28*Real.pi/3) * (|β| * (q:ℝ) * (((N:ℝ)+(q:ℝ))^2/(N:ℝ))) + (q:ℝ)/(N:ℝ) := by
                ring
            _ ≤ 40 * (|β| * (q:ℝ) * (((N:ℝ)+(q:ℝ))^2/(N:ℝ))) + 40 * ((q:ℝ)/(N:ℝ)) := by
                exact add_le_add (mul_le_mul_of_nonneg_right hpi hY) (by linarith [hqN0])
            _ = 40 * (|β| * (q:ℝ) * (((N:ℝ)+(q:ℝ))^2/(N:ℝ)) + (q:ℝ)/(N:ℝ)) := by ring
  · have hNq : (N:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : N < q)
    have hSle : ‖S‖ ≤ (N:ℝ) := by
      rw [hS]
      calc ‖∑ n ∈ Finset.range N, expTwoPiI (((a:ℝ)/(q:ℝ)+β)*(n:ℝ)^2)‖
          ≤ ∑ n ∈ Finset.range N, ‖expTwoPiI (((a:ℝ)/(q:ℝ)+β)*(n:ℝ)^2)‖ := norm_sum_le _ _
        _ = (N:ℝ) := by simp [norm_expTwoPiI]
    have hGle : ‖G‖ ≤ (q:ℝ) := by
      rw [hG]
      calc ‖∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ)*(r:ℝ)^2)‖
          ≤ ∑ r ∈ Finset.range q, ‖expTwoPiI ((a:ℝ)/(q:ℝ)*(r:ℝ)^2)‖ := norm_sum_le _ _
        _ = (q:ℝ) := by simp [norm_expTwoPiI]
    have hvle : ‖v‖ ≤ 1 := by rw [hv]; exact norm_integral_expTwoPiI_quad_le _
    have h1 : ‖(N:ℂ)⁻¹ * S‖ ≤ 1 := by
      rw [norm_mul, hNnorm]
      calc (1/(N:ℝ)) * ‖S‖ ≤ (1/(N:ℝ)) * (N:ℝ) :=
            mul_le_mul_of_nonneg_left hSle (by positivity)
        _ = 1 := by field_simp
    have h2 : ‖(q:ℂ)⁻¹ * G * v‖ ≤ 1 := by
      have hstep : ‖(q:ℂ)⁻¹ * G * v‖ = (1/(q:ℝ)) * ‖G‖ * ‖v‖ := by
        rw [norm_mul, norm_mul, hqnorm]
      rw [hstep]
      calc (1/(q:ℝ)) * ‖G‖ * ‖v‖ ≤ (1/(q:ℝ)) * (q:ℝ) * 1 := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hGle (by positivity)) hvle
              (norm_nonneg _) (by positivity)
        _ = 1 := by field_simp
    calc ‖(N:ℂ)⁻¹ * S - (q:ℂ)⁻¹ * G * v‖ ≤ ‖(N:ℂ)⁻¹ * S‖ + ‖(q:ℂ)⁻¹ * G * v‖ :=
          norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add h1 h2
      _ = 2 := by norm_num
      _ ≤ 40 * T := by
          have h1q : 1 < (q:ℝ)/(N:ℝ) := by
            rw [lt_div_iff₀ hNpos]; linarith
          have hTge : (q:ℝ)/(N:ℝ) ≤ T := by
            rw [hT]
            have : (0:ℝ) ≤ |β| * (q:ℝ) * ((N:ℝ)+(q:ℝ))^2/(N:ℝ) := by positivity
            linarith
          nlinarith [hTge, h1q]

end Commons.Analysis.ExponentialSums