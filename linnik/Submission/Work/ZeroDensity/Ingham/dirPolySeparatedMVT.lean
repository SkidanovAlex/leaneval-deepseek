import Mathlib
import Submission.Work.ZeroDensity.Montgomery.gallagherSeparated
import Submission.Work.ZeroDensity.Montgomery.dirichletPoly_hasDerivAt
import Submission.Work.ZeroDensity.Montgomery.mvtSpread

/-!
# The separated-points mean value theorem for a Dirichlet polynomial

`Work.ZeroDensity.Ingham.dirPolySeparatedMVT`: there is an absolute `C > 0` such that for all
`T ≥ 2`, `δ > 0`, `N ≥ 1`, all coefficients `b : ℕ → ℂ` and every `δ`-separated set `S ⊆ [-T,T]`,

`Σ_{t ∈ S} ‖Σ_{n ≤ N} b n · n^{-it}‖² ≤ C (1/δ + log 2N) (T + N) Σ_{n ≤ N} ‖b n‖²`.

The proof has three ingredients.

* The *sharp* integral mean value theorem for a Dirichlet polynomial (Montgomery--Vaughan):
  `∫_a^B ‖Σ_{n≤N} b n n^{-ix}‖² dx ≤ C ((B-a) + N) Σ ‖b n‖²`.  It is proved here from the
  Fourier/spreading estimate `Work.ZeroDensity.Montgomery.mvtSpread` together with the elementary
  support and size properties of the spreading kernel `mvtTheta` (`mvtTheta_support`,
  `mvtTheta_bound`): `Θ_S` is supported in `|x| ≤ 2·rOut·E/S` and bounded by `A·S/E`, so the
  quadratic form `Σ_{m,n} b m conj(b n) Θ_S (log (n/m))` is at most `(A/E)(2 K e^K N + S) Σ`,
  where `K = 2·rOut·E` (a window `|log (n/m)| ≤ K/S` contains at most `m (2K/S) e^K + 1` integers
  `n`), and one rescales `s ↦ 2πs`.  Small `T` is handled by the trivial bound `‖·‖² ≤ N Σ`.
* Gallagher's sampling bound `Work.ZeroDensity.Montgomery.gallagherSeparated` with
  `h = min (δ/2) 1` on `[-T-1, T+1]`.
* Bookkeeping: `1/(2 min (δ/2) 1) ≤ 2(1/δ + log 2N)`, `2T+2+N ≤ 3(T+N)`, `log 2N ≥ 1/2`.
-/

set_option maxHeartbeats 1000000

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators

noncomputable section

open Work.ZeroDensity.Montgomery (mvtA mvtE mvtC mvtTheta mvtTheta_support mvtTheta_bound mvtDelta
  mvtBump mvtSpread mvtA_pos mvtE_pos mvtC_pos gallagherSeparated)

/-- `A x = Σ_{n ≤ N} b n · n^{-ix}`. -/
private def dpoly (N : ℕ) (b : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, b n * (n : ℂ) ^ (-((x : ℂ) * Complex.I))

/-- `A' x = Σ_{n ≤ N} (-(i log n)) b n · n^{-ix}`, the termwise derivative of `A`. -/
private def dpolyDeriv (N : ℕ) (b : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (-(Complex.I * (Real.log n : ℂ))) * b n * (n : ℂ) ^ (-((x : ℂ) * Complex.I))

private lemma dpoly_hasDerivAt (N : ℕ) (b : ℕ → ℂ) (x : ℝ) :
    HasDerivAt (dpoly N b) (dpolyDeriv N b x) x :=
  Work.ZeroDensity.Montgomery.dirichletPoly_hasDerivAt N b x

private lemma cpow_cont (n : ℕ) (hn : 0 < n) :
    Continuous (fun x : ℝ => (n : ℂ) ^ (-((x : ℂ) * Complex.I))) :=
  Continuous.const_cpow ((Complex.continuous_ofReal.mul continuous_const).neg)
    (Or.inl (by exact_mod_cast (by omega : n ≠ 0)))

private lemma dpoly_cont (N : ℕ) (b : ℕ → ℂ) : Continuous (dpoly N b) := by
  unfold dpoly
  apply continuous_finsetSum
  intro n hn
  exact (cpow_cont n (by have h1 := (Finset.mem_Icc.mp hn).1; omega)).const_mul (b n)

private lemma continuous_dpolyDeriv (N : ℕ) (b : ℕ → ℂ) : Continuous (dpolyDeriv N b) := by
  unfold dpolyDeriv
  apply continuous_finsetSum
  intro n hn
  exact (cpow_cont n (by have h1 := (Finset.mem_Icc.mp hn).1; omega)).const_mul
    ((-(Complex.I * (Real.log n : ℂ))) * b n)

/-- `‖-(i log n) · z‖ = log n · ‖z‖` for `n ≥ 1`. -/
private lemma norm_derivCoeff (n : ℕ) (hn : 1 ≤ n) (z : ℂ) :
    ‖(-(Complex.I * (Real.log n : ℂ))) * z‖ = Real.log n * ‖z‖ := by
  rw [norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn))]

/-- The squared-norm sum of the derivative coefficients is at most `(log 2N)²` times `Σ`. -/
private lemma sum_derivCoeff_sq_le (N : ℕ) (b : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, ‖(-(Complex.I * (Real.log n : ℂ))) * b n‖ ^ 2)
      ≤ (Real.log (2 * (N : ℝ))) ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hlogL : Real.log n ≤ Real.log (2 * (N : ℝ)) := by
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < n))
    linarith [hnN, show (0 : ℝ) ≤ (N : ℝ) by positivity]
  rw [norm_derivCoeff n hn1, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlog0 hlogL 2) (by positivity)

/-- Pointwise trivial bound `‖A x‖² ≤ N · Σ ‖b n‖²`. -/
private lemma dpoly_norm_sq_le (N : ℕ) (b : ℕ → ℂ) (x : ℝ) :
    ‖dpoly N b x‖ ^ 2 ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
  have h1 : ‖dpoly N b x‖ ≤ ∑ n ∈ Finset.Icc 1 N, ‖b n‖ := by
    calc ‖dpoly N b x‖ ≤ ∑ n ∈ Finset.Icc 1 N, ‖b n * (n : ℂ) ^ (-((x : ℂ) * Complex.I))‖ :=
          norm_sum_le _ _
      _ = ∑ n ∈ Finset.Icc 1 N, ‖b n‖ := by
          refine Finset.sum_congr rfl (fun n hn => ?_)
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          rw [norm_mul]
          have hnorm : ‖(n : ℂ) ^ (-((x : ℂ) * Complex.I))‖ = 1 := by
            rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < n)]
            simp
          rw [hnorm, mul_one]
  have h2 : (∑ n ∈ Finset.Icc 1 N, ‖b n‖) ^ 2
      ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N)
      (fun _ : ℕ => (1 : ℝ)) (fun n => ‖b n‖)
    have hcard : (((Finset.Icc 1 N).card : ℕ) : ℝ) ≤ (N : ℝ) := by
      rw [Nat.card_Icc]
      have : N + 1 - 1 = N := by omega
      rw [this]
    calc (∑ n ∈ Finset.Icc 1 N, ‖b n‖) ^ 2
        = (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) * ‖b n‖) ^ 2 := by simp
      _ ≤ (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := hcs
      _ = (((Finset.Icc 1 N).card : ℕ) : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          norm_num
      _ ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
  exact le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2

/-! ## The sharp integral mean value theorem -/

/-- The support radius `K = 2 · rOut · E` of the spreading kernel: `Θ_S` vanishes outside
`|x| ≤ K/S`. -/
private def thetaK : ℝ := 2 * mvtBump.rOut * mvtE

private lemma thetaK_pos : 0 < thetaK := by
  rw [thetaK]; exact mul_pos (mul_pos (by norm_num) mvtBump.rOut_pos) mvtE_pos

private lemma thetaK_nonneg : 0 ≤ thetaK := le_of_lt thetaK_pos

private lemma abs_log_div_comm {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |Real.log (x / y)| = |Real.log (y / x)| := by
  rw [Real.log_div hx.ne' hy.ne', Real.log_div hy.ne' hx.ne', abs_sub_comm]

/-- A finset of naturals all of whose elements lie in `[m e^{-u}, m e^{u}]` has at most
`m (e^u - e^{-u}) + 1` elements. -/
private lemma card_le_of_mem_window (s : Finset ℕ) (m : ℕ) (hm : 1 ≤ m) {u : ℝ} (hu : 0 ≤ u)
    (h : ∀ n ∈ s, (m : ℝ) * Real.exp (-u) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (m : ℝ) * Real.exp u) :
    (s.card : ℝ) ≤ (m : ℝ) * (Real.exp u - Real.exp (-u)) + 1 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  by_cases hne : s.Nonempty
  · have hminA : s.min' hne ∈ s := Finset.min'_mem s hne
    have hmaxA : s.max' hne ∈ s := Finset.max'_mem s hne
    have hsub : s ⊆ Finset.Icc (s.min' hne) (s.max' hne) := fun n hn =>
      Finset.mem_Icc.mpr ⟨Finset.min'_le s n hn, Finset.le_max' s n hn⟩
    have hcard : s.card ≤ (Finset.Icc (s.min' hne) (s.max' hne)).card := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hcast : (((s.max' hne + 1 - s.min' hne : ℕ)) : ℝ)
        ≤ (s.max' hne : ℝ) + 1 - (s.min' hne : ℝ) := by
      have hle : s.min' hne ≤ s.max' hne + 1 := by
        have := Finset.min'_le s (s.max' hne) hmaxA; omega
      rw [Nat.cast_sub hle]
      push_cast
      linarith
    have hle1 : (s.max' hne : ℝ) ≤ (m : ℝ) * Real.exp u := (h _ hmaxA).2
    have hle2 : (m : ℝ) * Real.exp (-u) ≤ (s.min' hne : ℝ) := (h _ hminA).1
    have hfin : (s.card : ℝ) ≤ (m : ℝ) * Real.exp u + 1 - (m : ℝ) * Real.exp (-u) := by
      calc (s.card : ℝ) ≤ ((s.max' hne + 1 - s.min' hne : ℕ) : ℝ) := by exact_mod_cast hcard
        _ ≤ (s.max' hne : ℝ) + 1 - (s.min' hne : ℝ) := hcast
        _ ≤ (m : ℝ) * Real.exp u + 1 - (m : ℝ) * Real.exp (-u) := by linarith
    linarith [hfin]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    have h' : Real.exp (-u) ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
    nlinarith [hmpos, h']

/-- Membership in a multiplicative window gives the two-sided bounds (fixed index in the
denominator). -/
private lemma mem_window_bounds {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {u : ℝ}
    (h : |Real.log ((n : ℝ) / (m : ℝ))| ≤ u) :
    (m : ℝ) * Real.exp (-u) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (m : ℝ) * Real.exp u := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdivpos : 0 < (n : ℝ) / (m : ℝ) := div_pos hnpos hmpos
  have hle : Real.log ((n : ℝ) / (m : ℝ)) ≤ u := (abs_le.mp h).2
  have hge : -u ≤ Real.log ((n : ℝ) / (m : ℝ)) := (abs_le.mp h).1
  have hexp1 : Real.exp (-u) ≤ (n : ℝ) / (m : ℝ) := by
    have h' := Real.exp_le_exp.mpr hge
    rwa [Real.exp_log hdivpos] at h'
  have hexp2 : (n : ℝ) / (m : ℝ) ≤ Real.exp u := by
    have h' := Real.exp_le_exp.mpr hle
    rwa [Real.exp_log hdivpos] at h'
  constructor
  · calc (m : ℝ) * Real.exp (-u) ≤ (m : ℝ) * ((n : ℝ) / (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hexp1 (le_of_lt hmpos)
      _ = (n : ℝ) := by field_simp
  · calc (n : ℝ) = (m : ℝ) * ((n : ℝ) / (m : ℝ)) := by field_simp
      _ ≤ (m : ℝ) * Real.exp u := mul_le_mul_of_nonneg_left hexp2 (le_of_lt hmpos)

/-- `e^u - e^{-u} ≤ 2u e^{K}` for `0 ≤ u ≤ K`. -/
private lemma exp_sub_exp_neg_le (u K : ℝ) (hu : 0 ≤ u) (huK : u ≤ K) :
    Real.exp u - Real.exp (-u) ≤ 2 * u * Real.exp K := by
  have hsplit : Real.exp (-(2 * u)) = Real.exp (-u) * Real.exp (-u) := by
    rw [← Real.exp_add]; congr 1; ring
  have hone : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]; simp
  have hfac : Real.exp u - Real.exp (-u) = Real.exp u * (1 - Real.exp (-(2 * u))) := by
    rw [hsplit, mul_sub, mul_one, ← mul_assoc, hone, one_mul]
  have hlin : 1 - Real.exp (-(2 * u)) ≤ 2 * u := by
    have h := Real.add_one_le_exp (-(2 * u))
    linarith
  have hexpK : Real.exp u ≤ Real.exp K := Real.exp_le_exp.mpr huK
  have h2u : 0 ≤ 2 * u := by linarith
  calc Real.exp u - Real.exp (-u) = Real.exp u * (1 - Real.exp (-(2 * u))) := hfac
    _ ≤ Real.exp u * (2 * u) := mul_le_mul_of_nonneg_left hlin (Real.exp_pos u).le
    _ ≤ Real.exp K * (2 * u) := mul_le_mul_of_nonneg_right hexpK h2u
    _ = 2 * u * Real.exp K := by ring

/-- **Row sums of the spreading kernel** (fixed index in the denominator, `S ≥ 1`, `1 ≤ m ≤ N`). -/
private lemma theta_row_sum_le (S : ℝ) (hS : 1 ≤ S) (N m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖
      ≤ (mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S) := by
  have hS0 : 0 < S := by linarith
  have hmN' : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
  have hAE : 0 < mvtA / mvtE := div_pos mvtA_pos mvtE_pos
  have hu0 : 0 ≤ thetaK / S := div_nonneg thetaK_nonneg hS0.le
  have hpoint : ∀ n ∈ Finset.Icc 1 N,
      ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖
        ≤ (mvtA * S / mvtE)
            * (if |Real.log ((n : ℝ) / (m : ℝ))| ≤ thetaK / S then (1 : ℝ) else 0) := by
    intro n hn
    by_cases hb : |Real.log ((n : ℝ) / (m : ℝ))| ≤ thetaK / S
    · rw [if_pos hb, mul_one]
      exact mvtTheta_bound S hS0 _
    · rw [if_neg hb, mul_zero]
      have hx : thetaK / S < |Real.log ((n : ℝ) / (m : ℝ))| := lt_of_not_ge hb
      have h0 : mvtTheta S (Real.log ((n : ℝ) / (m : ℝ))) = 0 := by
        refine mvtTheta_support S hS0 ?_
        rw [mvtDelta]
        have hc : 2 * mvtBump.rOut * (mvtE / S) = thetaK / S := by rw [thetaK]; ring
        rw [hc]; exact hx
      rw [h0, norm_zero]
  have hcard : ((((Finset.Icc 1 N).filter
      (fun n : ℕ => |Real.log ((n : ℝ) / (m : ℝ))| ≤ thetaK / S)).card : ℕ) : ℝ)
      ≤ (m : ℝ) * (2 * (thetaK / S) * Real.exp thetaK) + 1 := by
    refine le_trans (card_le_of_mem_window _ _ hm1 hu0 (fun n hn => ?_)) ?_
    · rw [Finset.mem_filter] at hn
      exact mem_window_bounds hm1 (Finset.mem_Icc.mp hn.1).1 hn.2
    · have hsplit := exp_sub_exp_neg_le (thetaK / S) thetaK hu0 (by
        rw [div_le_iff₀ hS0]
        nlinarith [thetaK_nonneg, hS])
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith [mul_le_mul_of_nonneg_left hsplit hm0]
  calc ∑ n ∈ Finset.Icc 1 N, ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖
      ≤ ∑ n ∈ Finset.Icc 1 N, (mvtA * S / mvtE)
          * (if |Real.log ((n : ℝ) / (m : ℝ))| ≤ thetaK / S then (1 : ℝ) else 0) :=
        Finset.sum_le_sum hpoint
    _ = (mvtA * S / mvtE) * ((((Finset.Icc 1 N).filter
          (fun n : ℕ => |Real.log ((n : ℝ) / (m : ℝ))| ≤ thetaK / S)).card : ℕ) : ℝ) := by
        rw [← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (mvtA * S / mvtE) * ((m : ℝ) * (2 * (thetaK / S) * Real.exp thetaK) + 1) :=
        mul_le_mul_of_nonneg_left hcard (div_nonneg (mul_nonneg mvtA_pos.le hS0.le) mvtE_pos.le)
    _ ≤ (mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S) := by
        have hsimp : (mvtA * S / mvtE) * ((m : ℝ) * (2 * (thetaK / S) * Real.exp thetaK) + 1)
            = (mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (m : ℝ) + S) := by
          field_simp
        rw [hsimp]
        have h1 : 2 * thetaK * Real.exp thetaK * (m : ℝ) + S
            ≤ 2 * thetaK * Real.exp thetaK * (N : ℝ) + S := by
          have hpos : 0 ≤ 2 * thetaK * Real.exp thetaK :=
            mul_nonneg (mul_nonneg (by norm_num) thetaK_nonneg) (Real.exp_pos _).le
          linarith [mul_le_mul_of_nonneg_left hmN' hpos]
        exact mul_le_mul_of_nonneg_left h1 hAE.le

/-- **Column sums of the spreading kernel** (fixed index in the numerator, `S ≥ 1`,
`1 ≤ k ≤ N`). -/
private lemma theta_col_sum_le (S : ℝ) (hS : 1 ≤ S) (N k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ‖mvtTheta S (Real.log ((k : ℝ) / (n : ℝ)))‖
      ≤ (mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S) := by
  have hS0 : 0 < S := by linarith
  have hkN' : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
  have hAE : 0 < mvtA / mvtE := div_pos mvtA_pos mvtE_pos
  have hu0 : 0 ≤ thetaK / S := div_nonneg thetaK_nonneg hS0.le
  have hpoint : ∀ n ∈ Finset.Icc 1 N,
      ‖mvtTheta S (Real.log ((k : ℝ) / (n : ℝ)))‖
        ≤ (mvtA * S / mvtE)
            * (if |Real.log ((k : ℝ) / (n : ℝ))| ≤ thetaK / S then (1 : ℝ) else 0) := by
    intro n hn
    by_cases hb : |Real.log ((k : ℝ) / (n : ℝ))| ≤ thetaK / S
    · rw [if_pos hb, mul_one]
      exact mvtTheta_bound S hS0 _
    · rw [if_neg hb, mul_zero]
      have hx : thetaK / S < |Real.log ((k : ℝ) / (n : ℝ))| := lt_of_not_ge hb
      have h0 : mvtTheta S (Real.log ((k : ℝ) / (n : ℝ))) = 0 := by
        refine mvtTheta_support S hS0 ?_
        rw [mvtDelta]
        have hc : 2 * mvtBump.rOut * (mvtE / S) = thetaK / S := by rw [thetaK]; ring
        rw [hc]; exact hx
      rw [h0, norm_zero]
  have hcard : ((((Finset.Icc 1 N).filter
      (fun n : ℕ => |Real.log ((k : ℝ) / (n : ℝ))| ≤ thetaK / S)).card : ℕ) : ℝ)
      ≤ (k : ℝ) * (2 * (thetaK / S) * Real.exp thetaK) + 1 := by
    refine le_trans (card_le_of_mem_window _ _ hk1 hu0 (fun n hn => ?_)) ?_
    · rw [Finset.mem_filter] at hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn.1).1
      have hkn : |Real.log ((n : ℝ) / (k : ℝ))| ≤ thetaK / S := by
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
        rw [abs_log_div_comm hnpos hkpos]
        exact hn.2
      exact mem_window_bounds hk1 hn1 hkn
    · have hsplit := exp_sub_exp_neg_le (thetaK / S) thetaK hu0 (by
        rw [div_le_iff₀ hS0]
        nlinarith [thetaK_nonneg, hS])
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith [mul_le_mul_of_nonneg_left hsplit hk0]
  calc ∑ n ∈ Finset.Icc 1 N, ‖mvtTheta S (Real.log ((k : ℝ) / (n : ℝ)))‖
      ≤ ∑ n ∈ Finset.Icc 1 N, (mvtA * S / mvtE)
          * (if |Real.log ((k : ℝ) / (n : ℝ))| ≤ thetaK / S then (1 : ℝ) else 0) :=
        Finset.sum_le_sum hpoint
    _ = (mvtA * S / mvtE) * ((((Finset.Icc 1 N).filter
          (fun n : ℕ => |Real.log ((k : ℝ) / (n : ℝ))| ≤ thetaK / S)).card : ℕ) : ℝ) := by
        rw [← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (mvtA * S / mvtE) * ((k : ℝ) * (2 * (thetaK / S) * Real.exp thetaK) + 1) :=
        mul_le_mul_of_nonneg_left hcard (div_nonneg (mul_nonneg mvtA_pos.le hS0.le) mvtE_pos.le)
    _ ≤ (mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S) := by
        have hsimp : (mvtA * S / mvtE) * ((k : ℝ) * (2 * (thetaK / S) * Real.exp thetaK) + 1)
            = (mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (k : ℝ) + S) := by
          field_simp
        rw [hsimp]
        have h1 : 2 * thetaK * Real.exp thetaK * (k : ℝ) + S
            ≤ 2 * thetaK * Real.exp thetaK * (N : ℝ) + S := by
          have hpos : 0 ≤ 2 * thetaK * Real.exp thetaK :=
            mul_nonneg (mul_nonneg (by norm_num) thetaK_nonneg) (Real.exp_pos _).le
          linarith [mul_le_mul_of_nonneg_left hkN' hpos]
        exact mul_le_mul_of_nonneg_left h1 hAE.le

/-- The two-half splitting identity for the symmetrised double sum. -/
private lemma sum_sum_half_split (s : Finset ℕ) (b : ℕ → ℂ) (c : ℕ → ℕ → ℝ) :
    ∑ m ∈ s, ∑ n ∈ s, (1 / 2 : ℝ) * (‖b m‖ ^ 2 + ‖b n‖ ^ 2) * c m n
      = (1 / 2) * (∑ m ∈ s, ∑ n ∈ s, ‖b m‖ ^ 2 * c m n)
        + (1 / 2) * (∑ m ∈ s, ∑ n ∈ s, ‖b n‖ ^ 2 * c m n) := by
  have h1 : ∀ m n : ℕ, (1 / 2 : ℝ) * (‖b m‖ ^ 2 + ‖b n‖ ^ 2) * c m n
      = (1 / 2) * (‖b m‖ ^ 2 * c m n) + (1 / 2) * (‖b n‖ ^ 2 * c m n) := fun m n => by ring
  simp_rw [h1]
  simp_rw [Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]

/-- **The quadratic form of the spreading kernel.** -/
private lemma theta_quadform_bound (S : ℝ) (hS : 1 ≤ S) (b : ℕ → ℂ) (N : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        b m * star (b n) * mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖
      ≤ (mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S)
          * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
  have hAE : 0 < mvtA / mvtE := div_pos mvtA_pos mvtE_pos
  have hMnn : 0 ≤ (mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S) := by
    have h1 : 0 ≤ 2 * thetaK * Real.exp thetaK * (N : ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) thetaK_nonneg) (Real.exp_pos _).le)
        (Nat.cast_nonneg _)
    have h2 : 0 ≤ S := by linarith
    exact mul_nonneg hAE.le (by linarith)
  have hrow : ∀ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖
        ≤ (mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S) := fun m hm =>
    theta_row_sum_le S hS N m (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2
  have hcol : ∀ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
      ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖
        ≤ (mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S) := fun n hn =>
    theta_col_sum_le S hS N n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
  have htri : ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        b m * star (b n) * mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖
      ≤ ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ‖b m‖ * ‖b n‖ * ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun m _ => ?_))
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun n _ => ?_))
    rw [norm_mul, norm_mul, norm_star]
  have hsym : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ‖b m‖ * ‖b n‖ * ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖
      ≤ ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (1 / 2 : ℝ) * (‖b m‖ ^ 2 + ‖b n‖ ^ 2)
            * ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖ := by
    refine Finset.sum_le_sum (fun m _ => Finset.sum_le_sum (fun n _ => ?_))
    have h1 : ‖b m‖ * ‖b n‖ ≤ (1 / 2 : ℝ) * (‖b m‖ ^ 2 + ‖b n‖ ^ 2) := by
      nlinarith [sq_nonneg (‖b m‖ - ‖b n‖)]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hsplit := sum_sum_half_split (Finset.Icc 1 N) b
    (fun m n => ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖)
  have hA : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ‖b m‖ ^ 2 * ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖
      ≤ ((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S))
          * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
    have hstep : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ‖b m‖ ^ 2 * ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖
        = ∑ m ∈ Finset.Icc 1 N, ‖b m‖ ^ 2 * (∑ n ∈ Finset.Icc 1 N,
            ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖) := by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.mul_sum]
    rw [hstep]
    calc ∑ m ∈ Finset.Icc 1 N, ‖b m‖ ^ 2 * (∑ n ∈ Finset.Icc 1 N,
          ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖)
        ≤ ∑ m ∈ Finset.Icc 1 N, ‖b m‖ ^ 2
            * ((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S)) :=
          Finset.sum_le_sum (fun m hm => mul_le_mul_of_nonneg_left (hrow m hm) (by positivity))
      _ = ((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S))
            * ∑ m ∈ Finset.Icc 1 N, ‖b m‖ ^ 2 := by
          rw [← Finset.sum_mul]; ring
      _ = ((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S))
            * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
          congr 1
  have hB : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ‖b n‖ ^ 2 * ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖
      ≤ ((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S))
          * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
    rw [Finset.sum_comm]
    have hstep : ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
          ‖b n‖ ^ 2 * ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖
        = ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 * (∑ m ∈ Finset.Icc 1 N,
            ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [Finset.mul_sum]
    rw [hstep]
    calc ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 * (∑ m ∈ Finset.Icc 1 N,
          ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖)
        ≤ ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2
            * ((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S)) :=
          Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left (hcol n hn) (by positivity))
      _ = ((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S))
            * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
          rw [← Finset.sum_mul]; ring
  have hfin : (1 / 2) * (((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S))
        * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)
      + (1 / 2) * (((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S))
        * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)
      = ((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S))
        * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by ring
  calc ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        b m * star (b n) * mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖
      ≤ ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (1 / 2 : ℝ) * (‖b m‖ ^ 2 + ‖b n‖ ^ 2)
            * ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖ := le_trans htri hsym
    _ = (1 / 2) * (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            ‖b m‖ ^ 2 * ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖)
          + (1 / 2) * (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            ‖b n‖ ^ 2 * ‖mvtTheta S (Real.log ((n : ℝ) / (m : ℝ)))‖) := hsplit
    _ ≤ (1 / 2) * (((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S))
            * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)
          + (1 / 2) * (((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S))
            * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num))
          (mul_le_mul_of_nonneg_left hB (by norm_num))
    _ = ((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S))
          * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := hfin

/-- The integrand of `mvtSpread` written as `dpoly`. -/
private lemma spread_integrand (N : ℕ) (b : ℕ → ℂ) (s : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 N, b n
        * Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ) * (Real.log (n : ℝ) : ℂ)))‖
      = ‖dpoly N b (2 * Real.pi * s)‖ := by
  congr 1
  unfold dpoly
  refine Finset.sum_congr rfl (fun n hn => ?_)
  congr 1
  have hnz : (n : ℂ) ≠ 0 := by
    have h1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (by omega : n ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hnz, Complex.natCast_log]
  congr 1
  push_cast
  ring

/-- **The spreading bound.**  For `S ≥ 1`,
`∫_{-S}^{S} ‖Σ_{n≤N} b n n^{-2πis}‖² ds ≤ C (N + S) Σ ‖b n‖²`. -/
private lemma spread_bound (b : ℕ → ℂ) (N : ℕ) (S : ℝ) (hS : 1 ≤ S) :
    (∫ s in (-S)..S, ‖dpoly N b (2 * Real.pi * s)‖ ^ 2)
      ≤ (mvtC ^ 2)⁻¹ * ((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S))
          * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
  have hsp := mvtSpread S hS b N
  rw [intervalIntegral.integral_congr (fun s _ => by rw [spread_integrand N b s])] at hsp
  have hq := theta_quadform_bound S hS b N
  have hC : 0 ≤ (mvtC ^ 2)⁻¹ := by positivity
  calc (∫ s in (-S)..S, ‖dpoly N b (2 * Real.pi * s)‖ ^ 2)
      ≤ (mvtC ^ 2)⁻¹ * ((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S)
          * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) :=
        le_trans hsp (mul_le_mul_of_nonneg_left hq hC)
    _ = (mvtC ^ 2)⁻¹ * ((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S))
          * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by ring

/-- The constant of the sharp mean value theorem. -/
private def mvtCst : ℝ :=
  max (2 * Real.pi * (mvtC ^ 2)⁻¹ * (mvtA / mvtE) * (2 * thetaK * Real.exp thetaK + 1))
    (4 * Real.pi) + 1

private lemma mvtCst_pos : 0 < mvtCst := by
  rw [mvtCst]
  have h : (0 : ℝ) ≤ max (2 * Real.pi * (mvtC ^ 2)⁻¹ * (mvtA / mvtE)
      * (2 * thetaK * Real.exp thetaK + 1)) (4 * Real.pi) := le_max_of_le_right (by positivity)
  linarith

/-- The sharp mean value theorem on the symmetric interval `[-T,T]`, `T ≥ 0`. -/
private lemma sharp_negT (b : ℕ → ℂ) (N : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    (∫ x in (-T)..T, ‖dpoly N b x‖ ^ 2)
      ≤ mvtCst * (T + (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
  have hSg0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by positivity
  have hmnonneg : 0 ≤ max (2 * Real.pi * (mvtC ^ 2)⁻¹ * (mvtA / mvtE)
      * (2 * thetaK * Real.exp thetaK + 1)) (4 * Real.pi) := le_max_of_le_right (by positivity)
  rcases le_or_gt T (2 * Real.pi) with hsmall | hbig
  · -- crude bound
    have hint : (∫ x in (-T)..T, ‖dpoly N b x‖ ^ 2)
        ≤ 2 * T * ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) := by
      have hmono : (∫ x in (-T)..T, ‖dpoly N b x‖ ^ 2)
          ≤ ∫ x in (-T)..T, ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) :=
        intervalIntegral.integral_mono_on (by linarith)
          (((dpoly_cont N b).norm.pow 2).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
          (fun x _ => dpoly_norm_sq_le N b x)
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      calc (∫ x in (-T)..T, ‖dpoly N b x‖ ^ 2)
          ≤ (T - -T) * ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) := hmono
        _ = 2 * T * ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) := by ring
    have hkey : 2 * T * (N : ℝ) ≤ mvtCst * (T + (N : ℝ)) := by
      have h1 : 2 * T * (N : ℝ) ≤ 4 * Real.pi * (T + (N : ℝ)) := by
        nlinarith [hT, hsmall, Real.pi_pos]
      have h2 : 4 * Real.pi * (T + (N : ℝ))
          ≤ (max (2 * Real.pi * (mvtC ^ 2)⁻¹ * (mvtA / mvtE)
              * (2 * thetaK * Real.exp thetaK + 1)) (4 * Real.pi) + 1) * (T + (N : ℝ)) := by
        have hT0 : 0 ≤ T + (N : ℝ) := by positivity
        have hm4 : 4 * Real.pi
            ≤ max (2 * Real.pi * (mvtC ^ 2)⁻¹ * (mvtA / mvtE)
                * (2 * thetaK * Real.exp thetaK + 1)) (4 * Real.pi) := le_max_right _ _
        have h45 : (4 : ℝ) * Real.pi
            ≤ max (2 * Real.pi * (mvtC ^ 2)⁻¹ * (mvtA / mvtE)
                * (2 * thetaK * Real.exp thetaK + 1)) (4 * Real.pi) + 1 := by linarith
        exact mul_le_mul_of_nonneg_right h45 hT0
      rw [mvtCst]
      linarith
    calc (∫ x in (-T)..T, ‖dpoly N b x‖ ^ 2)
        ≤ 2 * T * ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) := hint
      _ = (2 * T * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by ring
      _ ≤ (mvtCst * (T + (N : ℝ))) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hkey hSg0
      _ = mvtCst * (T + (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by ring
  · -- spreading bound
    set S : ℝ := T / (2 * Real.pi) with hSdef
    have hS1 : 1 ≤ S := by
      rw [hSdef, le_div_iff₀ (by positivity)]
      linarith
    have h2piS : 2 * Real.pi * S = T := by rw [hSdef]; field_simp
    have hmS : 2 * Real.pi * (-S) = -T := by rw [mul_neg, h2piS]
    have hsubst : (∫ x in (-T)..T, ‖dpoly N b x‖ ^ 2)
        = 2 * Real.pi * (∫ s in (-S)..S, ‖dpoly N b (2 * Real.pi * s)‖ ^ 2) := by
      have hcomp := intervalIntegral.integral_comp_mul_left (a := -S) (b := S)
        (c := 2 * Real.pi) (f := fun y : ℝ => ‖dpoly N b y‖ ^ 2) (by positivity)
      rw [hmS, h2piS, smul_eq_mul] at hcomp
      calc (∫ x in (-T)..T, ‖dpoly N b x‖ ^ 2)
          = (2 * Real.pi) * ((2 * Real.pi)⁻¹ * ∫ x in (-T)..T, ‖dpoly N b x‖ ^ 2) := by
            field_simp
        _ = (2 * Real.pi) * (∫ s in (-S)..S, ‖dpoly N b (2 * Real.pi * s)‖ ^ 2) := by
            rw [← hcomp]
    have hspread := spread_bound b N S hS1
    have hSleT : S ≤ T := by
      rw [hSdef, div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three, hT]
    have hb1 : 2 * thetaK * Real.exp thetaK * (N : ℝ) + S
        ≤ (2 * thetaK * Real.exp thetaK + 1) * (T + (N : ℝ)) := by
      have hK1 : 0 ≤ 2 * thetaK * Real.exp thetaK :=
        mul_nonneg (mul_nonneg (by norm_num) thetaK_nonneg) (Real.exp_pos _).le
      have hNa : (N : ℝ) ≤ (N : ℝ) + T := by linarith
      have hSa : S ≤ (N : ℝ) + T := by linarith
      nlinarith [hK1, hNa, hSa, mul_nonneg hK1 (Nat.cast_nonneg N)]
    have hkey : 2 * Real.pi * ((mvtC ^ 2)⁻¹ * ((mvtA / mvtE)
          * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S)))
        ≤ mvtCst * (T + (N : ℝ)) := by
      have hC1 : 0 < (mvtC ^ 2)⁻¹ := inv_pos.mpr (pow_pos mvtC_pos 2)
      have hAE : 0 < mvtA / mvtE := div_pos mvtA_pos mvtE_pos
      have hstep1 : (mvtC ^ 2)⁻¹ * ((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S))
          ≤ (mvtC ^ 2)⁻¹ * ((mvtA / mvtE) * ((2 * thetaK * Real.exp thetaK + 1) * (T + (N : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb1 hAE.le) hC1.le
      have hstep2 : 2 * Real.pi * ((mvtC ^ 2)⁻¹ * ((mvtA / mvtE)
            * ((2 * thetaK * Real.exp thetaK + 1) * (T + (N : ℝ)))))
          = (2 * Real.pi * ((mvtC ^ 2)⁻¹ * (mvtA / mvtE))
              * (2 * thetaK * Real.exp thetaK + 1)) * (T + (N : ℝ)) := by ring
      have hle : 2 * Real.pi * (mvtC ^ 2)⁻¹ * (mvtA / mvtE) * (2 * thetaK * Real.exp thetaK + 1)
          ≤ max (2 * Real.pi * (mvtC ^ 2)⁻¹ * (mvtA / mvtE)
              * (2 * thetaK * Real.exp thetaK + 1)) (4 * Real.pi) := le_max_left _ _
      have hle_eq : 2 * Real.pi * ((mvtC ^ 2)⁻¹ * (mvtA / mvtE)) * (2 * thetaK * Real.exp thetaK + 1)
          = 2 * Real.pi * (mvtC ^ 2)⁻¹ * (mvtA / mvtE) * (2 * thetaK * Real.exp thetaK + 1) := by
        ring
      have hTN : 0 ≤ T + (N : ℝ) := by positivity
      rw [mvtCst]
      calc 2 * Real.pi * ((mvtC ^ 2)⁻¹ * ((mvtA / mvtE) * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S)))
          ≤ 2 * Real.pi * ((mvtC ^ 2)⁻¹ * ((mvtA / mvtE)
              * ((2 * thetaK * Real.exp thetaK + 1) * (T + (N : ℝ))))) :=
            mul_le_mul_of_nonneg_left hstep1 (by positivity)
        _ = (2 * Real.pi * ((mvtC ^ 2)⁻¹ * (mvtA / mvtE))
              * (2 * thetaK * Real.exp thetaK + 1)) * (T + (N : ℝ)) := hstep2
        _ ≤ (max (2 * Real.pi * (mvtC ^ 2)⁻¹ * (mvtA / mvtE)
              * (2 * thetaK * Real.exp thetaK + 1)) (4 * Real.pi) + 1) * (T + (N : ℝ)) := by
            rw [hle_eq]
            have h45 : 2 * Real.pi * (mvtC ^ 2)⁻¹ * (mvtA / mvtE)
                * (2 * thetaK * Real.exp thetaK + 1)
                ≤ max (2 * Real.pi * (mvtC ^ 2)⁻¹ * (mvtA / mvtE)
                    * (2 * thetaK * Real.exp thetaK + 1)) (4 * Real.pi) + 1 := by linarith
            exact mul_le_mul_of_nonneg_right h45 hTN
    rw [hsubst]
    calc 2 * Real.pi * (∫ s in (-S)..S, ‖dpoly N b (2 * Real.pi * s)‖ ^ 2)
        ≤ 2 * Real.pi * ((mvtC ^ 2)⁻¹ * ((mvtA / mvtE)
            * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S)) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hspread (by positivity)
      _ = (2 * Real.pi * ((mvtC ^ 2)⁻¹ * ((mvtA / mvtE)
            * (2 * thetaK * Real.exp thetaK * (N : ℝ) + S)))) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
          ring
      _ ≤ (mvtCst * (T + (N : ℝ))) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hkey hSg0
      _ = mvtCst * (T + (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by ring

/-- The sharp mean value theorem on an arbitrary interval. -/
private lemma sharp_interval (b : ℕ → ℂ) (N : ℕ) (a B : ℝ) (haB : a ≤ B) :
    (∫ x in a..B, ‖dpoly N b x‖ ^ 2)
      ≤ mvtCst * ((B - a) + (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
  have hSg0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by positivity
  by_cases hbig : 1 ≤ B - a
  · set b' : ℕ → ℂ := fun n => b n * (n : ℂ) ^ (-((a : ℂ) * Complex.I)) with hb'
    have hpoint : ∀ u : ℝ, dpoly N b (a + u) = dpoly N b' u := by
      intro u
      unfold dpoly
      rw [hb']
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have hnz : (n : ℂ) ≠ 0 := by
        have h1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        exact_mod_cast (by omega : n ≠ 0)
      have hexp : -((((a + u) : ℝ) : ℂ) * Complex.I)
          = (-((a : ℂ) * Complex.I)) + (-((u : ℂ) * Complex.I)) := by push_cast; ring
      rw [hexp, Complex.cpow_add (-((a : ℂ) * Complex.I)) (-((u : ℂ) * Complex.I)) hnz]
      ring
    have hshift : (∫ x in a..B, ‖dpoly N b x‖ ^ 2)
        = ∫ u in (0 : ℝ)..(B - a), ‖dpoly N b' u‖ ^ 2 := by
      have hcomp := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := B - a) (d := a)
        (f := fun y : ℝ => ‖dpoly N b y‖ ^ 2)
      rw [add_zero, show a + (B - a) = B from by ring] at hcomp
      rw [← hcomp]
      exact intervalIntegral.integral_congr (fun u _ => by rw [hpoint u])
    have hsym : (∫ u in (0 : ℝ)..(B - a), ‖dpoly N b' u‖ ^ 2)
        ≤ ∫ u in (-(B - a))..(B - a), ‖dpoly N b' u‖ ^ 2 := by
      have hadj := intervalIntegral.integral_add_adjacent_intervals
        (f := fun u : ℝ => ‖dpoly N b' u‖ ^ 2) (a := -(B - a)) (b := 0) (c := B - a)
        (((dpoly_cont N b').norm.pow 2).intervalIntegrable (μ := MeasureTheory.volume) (-(B - a)) 0)
        (((dpoly_cont N b').norm.pow 2).intervalIntegrable (μ := MeasureTheory.volume) 0 (B - a))
      have hnn : 0 ≤ ∫ u in (-(B - a))..(0 : ℝ), ‖dpoly N b' u‖ ^ 2 :=
        intervalIntegral.integral_nonneg (by linarith) (fun u _ => by positivity)
      linarith [hadj, hnn]
    have hnegT := sharp_negT b' N (B - a) (by linarith)
    have hSgeq : (∑ n ∈ Finset.Icc 1 N, ‖b' n‖ ^ 2) = ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      rw [hb', norm_mul]
      have hnorm : ‖(n : ℂ) ^ (-((a : ℂ) * Complex.I))‖ = 1 := by
        rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < n)]
        simp
      rw [hnorm, mul_one]
    rw [hSgeq] at hnegT
    calc (∫ x in a..B, ‖dpoly N b x‖ ^ 2)
        = ∫ u in (0 : ℝ)..(B - a), ‖dpoly N b' u‖ ^ 2 := hshift
      _ ≤ ∫ u in (-(B - a))..(B - a), ‖dpoly N b' u‖ ^ 2 := hsym
      _ ≤ mvtCst * ((B - a) + (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := hnegT
  · -- short interval
    have hℓ0 : 0 ≤ B - a := by linarith
    have hℓ1 : B - a ≤ 1 := le_of_not_ge hbig
    have hint : (∫ x in a..B, ‖dpoly N b x‖ ^ 2)
        ≤ 2 * ((B - a) * ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)) := by
      have hmono : (∫ x in a..B, ‖dpoly N b x‖ ^ 2)
          ≤ ∫ x in a..B, ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) :=
        intervalIntegral.integral_mono_on haB
          (((dpoly_cont N b).norm.pow 2).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
          (fun x _ => dpoly_norm_sq_le N b x)
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      calc (∫ x in a..B, ‖dpoly N b x‖ ^ 2)
          ≤ (B - a) * ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) := hmono
        _ ≤ 2 * ((B - a) * ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)) := by
            have h0 : 0 ≤ (B - a) * ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) := by positivity
            linarith
    have hkey : 2 * (B - a) * (N : ℝ) ≤ mvtCst * ((B - a) + (N : ℝ)) := by
      have h1 : 2 * (B - a) * (N : ℝ) ≤ 2 * ((B - a) + (N : ℝ)) := by
        have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        nlinarith [hℓ0, hℓ1, hN0]
      have h2 : 2 * ((B - a) + (N : ℝ)) ≤ mvtCst * ((B - a) + (N : ℝ)) := by
        have h0 : 0 ≤ (B - a) + (N : ℝ) := by positivity
        have h3 : 2 ≤ mvtCst := by
          rw [mvtCst]
          have h4 : (4 : ℝ) * Real.pi ≤ max (2 * Real.pi * (mvtC ^ 2)⁻¹ * (mvtA / mvtE)
              * (2 * thetaK * Real.exp thetaK + 1)) (4 * Real.pi) := le_max_right _ _
          linarith [Real.pi_gt_three]
        nlinarith [h0, h3]
      linarith
    calc (∫ x in a..B, ‖dpoly N b x‖ ^ 2)
        ≤ 2 * ((B - a) * ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)) := hint
      _ = (2 * (B - a) * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by ring
      _ ≤ (mvtCst * ((B - a) + (N : ℝ))) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hkey hSg0
      _ = mvtCst * ((B - a) + (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by ring

/-! ## The final bookkeeping and the main theorem -/

private lemma log_two_ge_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

private lemma inv_two_min_le (δ L : ℝ) (hδ : 0 < δ) (hL : 1 / 2 ≤ L) :
    1 / (2 * min (δ / 2) 1) ≤ 2 * (1 / δ + L) := by
  rcases le_or_gt δ 2 with h2 | h2
  · have hmin : min (δ / 2) 1 = δ / 2 := min_eq_left (by linarith)
    rw [hmin, show 1 / (2 * (δ / 2)) = 1 / δ by ring]
    have h1δ : 0 < 1 / δ := by positivity
    linarith
  · have hmin : min (δ / 2) 1 = 1 := min_eq_right (by linarith)
    rw [hmin]
    have h1δ : 0 < 1 / δ := by positivity
    linarith

/-- The final bookkeeping inequality, in the abstract form in which it is used. -/
private lemma final_arith (C₀ Q U P Sg L : ℝ) (hC₀ : 0 < C₀) (hL0 : 0 ≤ L) (hU0 : 0 ≤ U)
    (hS0 : 0 ≤ Sg) (hP0 : 0 ≤ P) (hQ3P : Q ≤ 3 * P) (hLU : L ≤ U) :
    2 * U * (C₀ * Q * Sg) + 2 * (C₀ * Q * L * Sg) ≤ (12 * C₀ + 1) * U * P * Sg := by
  have h1 : 2 * U * (C₀ * Q * Sg) ≤ 6 * C₀ * U * P * Sg := by
    have hA : C₀ * Q * Sg ≤ C₀ * (3 * P) * Sg := by
      apply mul_le_mul_of_nonneg_right _ hS0
      exact mul_le_mul_of_nonneg_left hQ3P hC₀.le
    calc 2 * U * (C₀ * Q * Sg) ≤ 2 * U * (C₀ * (3 * P) * Sg) :=
          mul_le_mul_of_nonneg_left hA (by linarith)
      _ = 6 * C₀ * U * P * Sg := by ring
  have h2 : 2 * (C₀ * Q * L * Sg) ≤ 6 * C₀ * U * P * Sg := by
    have hQL : C₀ * Q * L * Sg ≤ C₀ * (3 * P) * U * Sg := by
      have h1 : Q * L ≤ 3 * P * U := by
        calc Q * L ≤ (3 * P) * L := mul_le_mul_of_nonneg_right hQ3P hL0
          _ ≤ (3 * P) * U := mul_le_mul_of_nonneg_left hLU (by linarith)
      calc C₀ * Q * L * Sg = C₀ * (Q * L) * Sg := by ring
        _ ≤ C₀ * (3 * P * U) * Sg :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC₀.le) hS0
        _ = C₀ * (3 * P) * U * Sg := by ring
    calc 2 * (C₀ * Q * L * Sg) ≤ 2 * (C₀ * (3 * P) * U * Sg) := by linarith [hQL]
      _ = 6 * C₀ * U * P * Sg := by ring
  have h3 : 0 ≤ U * P * Sg := mul_nonneg (mul_nonneg hU0 hP0) hS0
  have h4 : 6 * C₀ * U * P * Sg + 6 * C₀ * U * P * Sg ≤ (12 * C₀ + 1) * U * P * Sg := by
    have h5 : (12 * C₀ + 1) * U * P * Sg = 12 * C₀ * U * P * Sg + 1 * (U * P * Sg) := by ring
    rw [h5]; linarith
  linarith [h1, h2, h4]

theorem dirPolySeparatedMVT :
    ∃ C : ℝ, 0 < C ∧ ∀ (T δ : ℝ), 2 ≤ T → 0 < δ → ∀ (N : ℕ), 1 ≤ N →
      ∀ (b : ℕ → ℂ) (S : Finset ℝ),
        (∀ t ∈ S, -T ≤ t ∧ t ≤ T) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → δ ≤ |t - t'|) →
        (∑ t ∈ S, ‖∑ n ∈ Finset.Icc 1 N, b n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2)
          ≤ C * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) *
              ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
  refine ⟨12 * mvtCst + 1, by linarith [mvtCst_pos], ?_⟩
  intro T δ hT hδ N hN b S hSbd hSsep
  set L : ℝ := Real.log (2 * (N : ℝ)) with hLdef
  set Sg : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 with hSgdef
  have hSgnn : 0 ≤ Sg := by rw [hSgdef]; positivity
  have hLhalf : (1 : ℝ) / 2 ≤ L := by
    rw [hLdef]
    refine le_trans log_two_ge_half (Real.log_le_log (by norm_num) ?_)
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hL0 : 0 ≤ L := by linarith
  set A : ℝ := -(T + 1) with hA
  set B : ℝ := T + 1 with hB
  have hAB : A ≤ B := by rw [hA, hB]; linarith
  have hBA : B - A = 2 * T + 2 := by rw [hA, hB]; ring
  have hK₀ : (∫ x in A..B, ‖dpoly N b x‖ ^ 2) ≤ mvtCst * ((B - A) + (N : ℝ)) * Sg := by
    have h := sharp_interval b N A B hAB
    simpa only [hSgdef] using h
  have hK₁ : (∫ x in A..B, ‖dpolyDeriv N b x‖ ^ 2)
      ≤ mvtCst * ((B - A) + (N : ℝ)) * (L ^ 2 * Sg) := by
    have h := sharp_interval (fun n => (-(Complex.I * (Real.log n : ℂ))) * b n) N A B hAB
    have hsum : (∑ n ∈ Finset.Icc 1 N, ‖(-(Complex.I * (Real.log n : ℂ))) * b n‖ ^ 2)
        ≤ L ^ 2 * Sg := by
      rw [hLdef, hSgdef]
      exact sum_derivCoeff_sq_le N b
    have hcongr : ∀ x : ℝ, dpolyDeriv N b x
        = ∑ n ∈ Finset.Icc 1 N,
            ((-(Complex.I * (Real.log n : ℂ))) * b n) * (n : ℂ) ^ (-((x : ℂ) * Complex.I)) := by
      intro x
      unfold dpolyDeriv
      exact Finset.sum_congr rfl (fun n _ => by ring)
    have hint : (∫ x in A..B, ‖dpolyDeriv N b x‖ ^ 2)
        = ∫ x in A..B, ‖∑ n ∈ Finset.Icc 1 N,
            ((-(Complex.I * (Real.log n : ℂ))) * b n) * (n : ℂ) ^ (-((x : ℂ) * Complex.I))‖ ^ 2 :=
      intervalIntegral.integral_congr (fun x _ => by rw [hcongr x])
    rw [hint]
    refine le_trans h (mul_le_mul_of_nonneg_left hsum ?_)
    have hQ0 : 0 ≤ (B - A) + (N : ℝ) := by rw [hBA]; positivity
    exact mul_nonneg mvtCst_pos.le hQ0
  set hh : ℝ := min (δ / 2) 1 with hhh
  have hhpos : 0 < hh := by rw [hhh]; exact lt_min (by positivity) one_pos
  have hhle1 : hh ≤ 1 := by rw [hhh]; exact min_le_right _ _
  have h2hh : 2 * hh ≤ δ := by
    rw [hhh]
    rcases le_or_gt δ 2 with h2 | h2
    · rw [min_eq_left (by linarith)]; linarith
    · rw [min_eq_right (by linarith)]; linarith
  have hgall : (∑ s ∈ S, ‖dpoly N b s‖ ^ 2)
      ≤ (1 / (2 * hh)) * (∫ x in A..B, ‖dpoly N b x‖ ^ 2)
        + 2 * Real.sqrt (∫ x in A..B, ‖dpoly N b x‖ ^ 2)
            * Real.sqrt (∫ x in A..B, ‖dpolyDeriv N b x‖ ^ 2) :=
    gallagherSeparated (g := dpoly N b) (g' := dpolyDeriv N b) (h := hh) (A := A) (B := B) (S := S)
      (fun x => dpoly_hasDerivAt N b x) (continuous_dpolyDeriv N b) hhpos hAB
      (fun s hs => by
        have hs' := hSbd s hs
        rw [hA, hB]
        constructor <;> linarith [hs'.1, hs'.2, hhle1])
      (fun s hs s' hs' hne => le_trans h2hh (hSsep s hs s' hs' hne))
  have hsqrt : Real.sqrt (∫ x in A..B, ‖dpoly N b x‖ ^ 2)
        * Real.sqrt (∫ x in A..B, ‖dpolyDeriv N b x‖ ^ 2)
      ≤ mvtCst * ((B - A) + (N : ℝ)) * L * Sg := by
    have hQ0 : 0 ≤ (B - A) + (N : ℝ) := by rw [hBA]; positivity
    have hbase : 0 ≤ mvtCst * ((B - A) + (N : ℝ)) * Sg :=
      mul_nonneg (mul_nonneg mvtCst_pos.le hQ0) hSgnn
    have hbase2 : 0 ≤ mvtCst * ((B - A) + (N : ℝ)) * L * Sg :=
      mul_nonneg (mul_nonneg (mul_nonneg mvtCst_pos.le hQ0) hL0) hSgnn
    have h1 : Real.sqrt (∫ x in A..B, ‖dpoly N b x‖ ^ 2)
        ≤ Real.sqrt (mvtCst * ((B - A) + (N : ℝ)) * Sg) := Real.sqrt_le_sqrt hK₀
    have h2 : Real.sqrt (∫ x in A..B, ‖dpolyDeriv N b x‖ ^ 2)
        ≤ Real.sqrt (mvtCst * ((B - A) + (N : ℝ)) * (L ^ 2 * Sg)) := Real.sqrt_le_sqrt hK₁
    have hprod := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have heq : Real.sqrt (mvtCst * ((B - A) + (N : ℝ)) * Sg)
          * Real.sqrt (mvtCst * ((B - A) + (N : ℝ)) * (L ^ 2 * Sg))
        = mvtCst * ((B - A) + (N : ℝ)) * L * Sg := by
      rw [← Real.sqrt_mul hbase]
      have : (mvtCst * ((B - A) + (N : ℝ)) * Sg) * (mvtCst * ((B - A) + (N : ℝ)) * (L ^ 2 * Sg))
          = (mvtCst * ((B - A) + (N : ℝ)) * L * Sg) ^ 2 := by ring
      rw [this, Real.sqrt_sq hbase2]
    calc Real.sqrt (∫ x in A..B, ‖dpoly N b x‖ ^ 2)
          * Real.sqrt (∫ x in A..B, ‖dpolyDeriv N b x‖ ^ 2)
        ≤ Real.sqrt (mvtCst * ((B - A) + (N : ℝ)) * Sg)
          * Real.sqrt (mvtCst * ((B - A) + (N : ℝ)) * (L ^ 2 * Sg)) := hprod
      _ = mvtCst * ((B - A) + (N : ℝ)) * L * Sg := heq
  have hterm1 : (1 / (2 * hh)) * (∫ x in A..B, ‖dpoly N b x‖ ^ 2)
      ≤ 2 * (1 / δ + L) * (mvtCst * ((B - A) + (N : ℝ)) * Sg) := by
    have hinv : 1 / (2 * hh) ≤ 2 * (1 / δ + L) := by
      rw [hhh]; exact inv_two_min_le δ L hδ hLhalf
    have h1 : 0 ≤ 1 / (2 * hh) := by positivity
    have h2 : 0 ≤ mvtCst * ((B - A) + (N : ℝ)) * Sg := by
      have hQ0 : 0 ≤ (B - A) + (N : ℝ) := by rw [hBA]; positivity
      exact mul_nonneg (mul_nonneg mvtCst_pos.le hQ0) hSgnn
    calc (1 / (2 * hh)) * (∫ x in A..B, ‖dpoly N b x‖ ^ 2)
        ≤ (1 / (2 * hh)) * (mvtCst * ((B - A) + (N : ℝ)) * Sg) :=
          mul_le_mul_of_nonneg_left hK₀ h1
      _ ≤ (2 * (1 / δ + L)) * (mvtCst * ((B - A) + (N : ℝ)) * Sg) :=
          mul_le_mul_of_nonneg_right hinv h2
  have hterm2 : 2 * (Real.sqrt (∫ x in A..B, ‖dpoly N b x‖ ^ 2)
        * Real.sqrt (∫ x in A..B, ‖dpolyDeriv N b x‖ ^ 2))
      ≤ 2 * (mvtCst * ((B - A) + (N : ℝ)) * L * Sg) := by linarith [hsqrt]
  have hQ3P : (B - A) + (N : ℝ) ≤ 3 * (T + (N : ℝ)) := by rw [hBA]; linarith
  have hU0 : 0 ≤ 1 / δ + L := by
    have : 0 < 1 / δ := by positivity
    linarith
  have hP0 : 0 ≤ T + (N : ℝ) := by positivity
  have harith : 2 * (1 / δ + L) * (mvtCst * ((B - A) + (N : ℝ)) * Sg)
        + 2 * (mvtCst * ((B - A) + (N : ℝ)) * L * Sg)
      ≤ (12 * mvtCst + 1) * (1 / δ + L) * (T + (N : ℝ)) * Sg :=
    final_arith mvtCst ((B - A) + (N : ℝ)) (1 / δ + L) (T + (N : ℝ)) Sg L mvtCst_pos hL0 hU0
      hSgnn hP0 hQ3P (by
        have h1δ : (0 : ℝ) < 1 / δ := by positivity
        linarith)
  have hchain : (∑ s ∈ S, ‖dpoly N b s‖ ^ 2)
      ≤ (12 * mvtCst + 1) * (1 / δ + L) * (T + (N : ℝ)) * Sg := by
    linarith [hgall, hterm1, hterm2, harith]
  simpa only [dpoly, hLdef, hSgdef] using hchain

end

end Work.ZeroDensity.Ingham
