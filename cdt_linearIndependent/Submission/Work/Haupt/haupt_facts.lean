import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.Work.Haupt.defs
import Submission.Work.Haupt.theta_differentiable
import Submission.Work.Haupt.tprod_identity
import Submission.Work.Haupt.theta_duplication
import Submission.Work.Haupt.theta_landen
import Submission.Work.Haupt.T4prod_ne_zero
import Submission.Work.Haupt.theta_four_product
import Submission.Work.Haupt.theta_two_product

/-! # Area M — the hauptmodul `h`

Progress and plan (see also `Scratch/algebra.lean`, `Scratch/hmain.lean`, `Scratch/assembly.lean`
where the algebraic choreography is developed and tested).

Done here: `hauptH` is holomorphic on the disc, `deriv hauptH 0 = -256`, `h(q) = 0 → q = 0`
(conjuncts 1–3 of `HauptFacts`), plus `differentiableOn_UQ`, `sqrt_sq`, `sqrt_norm_lt_one`,
and the final packaging `hauptH_sqroot_of` (given the key identity and `T4 ≠ 0` on the disc).

Delegated (separate modules): the two theta product formulas (`theta_four_product`,
`theta_two_product`, from the Jacobi triple product `jacobi_triple_product`), the elementary
theta identities `theta_duplication`, `theta_landen`, differentiability of the theta series
(`theta_differentiable`, delivered), the pure infinite-product identity `tprod_identity`
(delivered) and `T4prod_ne_zero`.

Remaining to assemble (all derivations already tested in `Scratch/`):
* `U_sq : U x ^ 2 = x ^ 2 * T2 x ^ 8 + 4 * T4 (x ^ 2) ^ 8`   [Landen + Jacobi]
* `jacobi_from_dup : T3 x ^ 4 = T4 x ^ 4 + x * T2 x ^ 4`      [duplication]
* `UQ_eq_U : UQ (x ^ 2) = U x`                                [duplication]
* `hauptH_mul_T4 : hauptH (x^2) * T4 (x^2)^8 = -x^2 * T2 x^8` [product formulas + `tprod_identity`]
* `hmain : ∀ q ∈ ball 0 1, hauptH q - 4 = -(UQ q)^2/(T4 q)^8` [previous two, `x = √q`]
* `T4_ne_zero` on the disc                                    [`theta_four_product`, `T4prod_ne_zero`]
-/

set_option maxHeartbeats 4000000

namespace Work.Haupt

open Submission.CDTPlan Filter
open scoped BigOperators

noncomputable section

/-- The deviation `(1+q^{n+1})^24 - 1`. -/
def hdev (n : ℕ) (q : ℂ) : ℂ := (1 + q ^ (n + 1)) ^ 24 - 1

/-- The factor `(1+q^{n+1})^24`. -/
def hfactor (n : ℕ) (q : ℂ) : ℂ := 1 + hdev n q

/-- The infinite product `∏'_{n≥1} (1 + qⁿ)^24` occurring in `hauptH`. -/
def hprod (q : ℂ) : ℂ := ∏' n : ℕ, hfactor n q

lemma hauptH_eq (q : ℂ) : hauptH q = -256 * q * hprod q := by
  simp [hauptH, hprod, hfactor, hdev]

lemma hsum24 : (∑ i ∈ Finset.range 24, (2 : ℝ) ^ i) = 2 ^ 24 - 1 := by
  norm_num

lemma hsum24C : (∑ i ∈ Finset.range 24, (2 : ℂ) ^ i) = 2 ^ 24 - 1 := by
  norm_num

/-- Elementary bound: `‖(1+z)^24 - 1‖ ≤ (2^24-1)‖z‖` for `‖z‖ ≤ 1`. -/
lemma norm_pow24_sub_one_le (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖(1 + z) ^ 24 - 1‖ ≤ (2 ^ 24 - 1) * ‖z‖ := by
  have key : (1 + z) ^ 24 - 1 = (∑ i ∈ Finset.range 24, (1 + z) ^ i) * z := by
    have h := geom_sum_mul_add z 24
    have h' : (∑ i ∈ Finset.range 24, (1 + z) ^ i) * z + 1 = (1 + z) ^ 24 := by
      simpa [add_comm] using h
    rw [← h']
    ring
  rw [key, norm_mul]
  have h1 : ‖∑ i ∈ Finset.range 24, (1 + z) ^ i‖ ≤ 2 ^ 24 - 1 := by
    have h3 : ‖1 + z‖ ≤ 2 := by
      calc ‖1 + z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_add_le _ _
        _ = 1 + ‖z‖ := by simp
        _ ≤ 2 := by linarith
    have h2 : ∀ i ∈ Finset.range 24, ‖(1 + z) ^ i‖ ≤ (2 : ℝ) ^ i := fun i hi => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) h3 i
    refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum h2) (le_of_eq hsum24))
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

lemma continuousOn_hdev (n : ℕ) (K : Set ℂ) : ContinuousOn (hdev n) K := by
  have h : hdev n = fun q : ℂ => (1 + q ^ (n + 1)) ^ 24 - 1 := rfl
  rw [h]
  fun_prop

/-- The product of the factors converges locally uniformly on the unit disc. -/
theorem hasProdLocallyUniformlyOn_hfactor :
    HasProdLocallyUniformlyOn hfactor (fun q => ∏' n, hfactor n q) (Metric.ball 0 1) := by
  refine hasProdLocallyUniformlyOn_of_forall_compact Metric.isOpen_ball (fun K hK hKc => ?_)
  obtain ⟨r, hr0, hr1, hrK⟩ : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ q ∈ K, ‖q‖ ≤ r := by
    rcases K.eq_empty_or_nonempty with h | hne
    · exact ⟨0, le_rfl, zero_lt_one, by simp [h]⟩
    · obtain ⟨q₀, hq₀⟩ := hKc.exists_isMaxOn hne continuous_norm.continuousOn
      have hlt : ‖q₀‖ < 1 := by
        have := hK hq₀.1
        rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at this
      exact ⟨‖q₀‖, norm_nonneg _, hlt, fun q hq => hq₀.2 hq⟩
  have hb : ∀ᶠ n in atTop, ∀ q ∈ K, ‖hdev n q‖ ≤ (2 ^ 24 - 1) * r ^ (n + 1) := by
    filter_upwards with n q hq
    have hqr : ‖q‖ ≤ r := hrK q hq
    have h1 : ‖q ^ (n + 1)‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (le_of_lt (lt_of_le_of_lt hqr hr1))
    calc ‖hdev n q‖ = ‖(1 + q ^ (n + 1)) ^ 24 - 1‖ := by rw [hdev]
      _ ≤ (2 ^ 24 - 1) * ‖q ^ (n + 1)‖ := norm_pow24_sub_one_le _ h1
      _ = (2 ^ 24 - 1) * ‖q‖ ^ (n + 1) := by rw [norm_pow]
      _ ≤ (2 ^ 24 - 1) * r ^ (n + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hqr _) (by norm_num)
  have hsum_u : Summable (fun n : ℕ => (2 ^ 24 - 1) * r ^ (n + 1)) := by
    refine ((summable_geometric_of_lt_one hr0 hr1).mul_left ((2 ^ 24 - 1) * r)).congr (fun n => ?_)
    rw [pow_succ]
    ring
  exact Summable.hasProdUniformlyOn_nat_one_add (f := hdev)
    (u := fun n => (2 ^ 24 - 1) * r ^ (n + 1)) hKc hsum_u hb (fun n => continuousOn_hdev n K)

/-- `hprod` is holomorphic on the unit disc. -/
theorem differentiableOn_hprod : DifferentiableOn ℂ hprod (Metric.ball 0 1) := by
  have htend := hasProdLocallyUniformlyOn_hfactor.tendstoLocallyUniformlyOn_finsetRange
  refine htend.differentiableOn ?_ Metric.isOpen_ball
  filter_upwards with N
  induction N with
  | zero => simpa using (differentiableOn_const (c := (1 : ℂ)) (s := Metric.ball (0:ℂ) 1))
  | succ n ih =>
    have hstep : (fun b : ℂ => ∏ i ∈ Finset.range (n + 1), hfactor i b)
        = (fun b : ℂ => (∏ i ∈ Finset.range n, hfactor i b) * hfactor n b) := by
      funext b
      rw [Finset.prod_range_succ]
    rw [hstep]
    refine ih.mul ?_
    have hh : (hfactor n : ℂ → ℂ) = fun b : ℂ => (1 + b ^ (n + 1)) ^ 24 := by
      funext b
      simp [hfactor, hdev]
    rw [hh]
    fun_prop

/-- `hauptH` is holomorphic on the unit disc. -/
theorem differentiableOn_hauptH : DifferentiableOn ℂ hauptH (Metric.ball 0 1) := by
  have h : DifferentiableOn ℂ (fun q : ℂ => -256 * q * hprod q) (Metric.ball 0 1) :=
    ((differentiableOn_const (c := (-256 : ℂ))).mul differentiableOn_id).mul differentiableOn_hprod
  rw [show hauptH = fun q => -256 * q * hprod q from funext hauptH_eq]
  exact h

lemma hprod_zero : hprod 0 = 1 := by
  have h : (fun n : ℕ => hfactor n 0) = fun _ : ℕ => (1 : ℂ) := by
    funext n
    simp only [hfactor, hdev]
    rw [zero_pow (Nat.succ_ne_zero n)]
    norm_num
  rw [hprod, h, tprod_one]

theorem deriv_hauptH_zero : deriv hauptH 0 = -256 := by
  have h2 : HasDerivAt hprod (deriv hprod 0) 0 :=
    (differentiableOn_hprod.differentiableAt
      (Metric.isOpen_ball.mem_nhds (by simp))).hasDerivAt
  have h1 : HasDerivAt (fun q : ℂ => -256 * q) (-256) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul (-256)
  have hmul := h1.mul h2
  have hval : (-256 * hprod 0 + (-256 * 0) * deriv hprod 0) = (-256 : ℂ) := by
    simp [hprod_zero]
  have hmain : HasDerivAt (fun q : ℂ => -256 * q * hprod q) (-256) 0 := by
    rw [show (fun q : ℂ => -256 * q * hprod q) = (fun q => (-256 * q) * hprod q) from
      funext (fun q => by ring)]
    exact hmul.congr_deriv hval
  rw [show hauptH = fun q => -256 * q * hprod q from funext hauptH_eq]
  exact hmain.deriv

lemma hfactor_ne_zero (q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) : hfactor n q ≠ 0 := by
  have hqpow : q ^ (n + 1) ≠ (-1 : ℂ) := by
    intro hzero
    have h1 : ‖q‖ ^ (n + 1) = 1 := by
      have := congrArg norm hzero
      simpa [norm_pow] using this
    have h2 : ‖q‖ ^ (n + 1) < 1 :=
      pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero n)
    rw [h1] at h2
    exact lt_irrefl 1 h2
  have hne : (1 + q ^ (n + 1)) ≠ 0 := by
    intro h0
    have h1 : -(q ^ (n + 1)) = 1 := ((add_eq_zero_iff_eq_neg).mp h0).symm
    exact hqpow ((neg_eq_iff_eq_neg).mp h1)
  have heq : hfactor n q = (1 + q ^ (n + 1)) ^ 24 := by
    rw [hfactor, hdev]
    ring
  rw [heq]
  exact pow_ne_zero 24 hne

lemma hprod_ne_zero (q : ℂ) (hq : ‖q‖ < 1) : hprod q ≠ 0 := by
  have hbase : Summable (fun n : ℕ => ‖q‖ ^ (n + 1)) := by
    simpa [pow_succ, mul_comm] using
      (summable_geometric_of_norm_lt_one
        (show ‖(‖q‖ : ℝ)‖ < 1 from by simpa using hq)).mul_left ‖q‖
  have hsum : Summable (fun n : ℕ => ‖hdev n q‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (hbase.mul_left ((2 : ℝ) ^ 24 - 1))
    have h1 : ‖q ^ (n + 1)‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hq.le
    calc ‖hdev n q‖ = ‖(1 + q ^ (n + 1)) ^ 24 - 1‖ := by rw [hdev]
      _ ≤ (2 ^ 24 - 1) * ‖q ^ (n + 1)‖ := norm_pow24_sub_one_le _ h1
      _ = (2 ^ 24 - 1) * ‖q‖ ^ (n + 1) := by rw [norm_pow]
  rw [hprod]
  exact tprod_one_add_ne_zero_of_summable (fun n => hfactor_ne_zero q hq n) hsum

theorem hauptH_ne_zero : ∀ q ∈ Metric.ball (0 : ℂ) 1, hauptH q = 0 → q = 0 := by
  intro q hq h
  have hq' : ‖q‖ < 1 := by
    have := hq
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at this
  have hne := hprod_ne_zero q hq'
  rw [hauptH_eq] at h
  have h' : (-256 : ℂ) * q = 0 := by
    rcases mul_eq_zero.mp h with h1 | h1
    · exact h1
    · exact absurd h1 hne
  exact (mul_eq_zero.mp h').resolve_left (by norm_num)


/-- `(√q)^2 = q` for the principal complex square root. -/
lemma sqrt_sq (q : ℂ) : Complex.sqrt q ^ 2 = q := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · have h := sqrt_eq_exp hq
    rw [h, ← Complex.exp_nat_mul]
    rw [show (2 : ℕ) * (Complex.log q / 2) = Complex.log q by ring]
    exact Complex.exp_log hq

lemma sqrt_norm_lt_one (q : ℂ) (hq : ‖q‖ < 1) : ‖Complex.sqrt q‖ < 1 := by
  have h2 : ‖Complex.sqrt q‖ ^ 2 = ‖q‖ := by
    rw [← norm_pow, sqrt_sq]
  nlinarith [norm_nonneg (Complex.sqrt q)]

/-- `UQ` is holomorphic on the unit disc. -/
lemma differentiableOn_UQ : DifferentiableOn ℂ UQ (Metric.ball 0 1) := by
  obtain ⟨hd3, -, hd2⟩ := theta_differentiable
  rw [show UQ = fun q : ℂ => 2 * T3 q ^ 4 + 2 * q * T2 q ^ 4 from rfl]
  refine DifferentiableOn.add ?_ ?_
  · exact ((hd3.pow 4).const_mul 2).congr (fun q _ => by simp only [Pi.pow_apply])
  · exact (((differentiableOn_id.mul (hd2.pow 4)).const_mul 2).congr (fun q _ => by
      simp only [Pi.pow_apply, Pi.mul_apply, id_eq]
      ring))

/-- Jacobi's identity `θ₃⁴ = θ₄⁴ + x θ₂⁴` from the duplication identities. -/
lemma jacobi_of_dup (x : ℂ)
    (h1 : T3 x ^ 2 = T3 (x ^ 2) ^ 2 + x * T2 (x ^ 2) ^ 2)
    (h2 : T4 x ^ 2 = T3 (x ^ 2) ^ 2 - x * T2 (x ^ 2) ^ 2)
    (h3 : T2 x ^ 2 = 2 * T2 (x ^ 2) * T3 (x ^ 2)) :
    T3 x ^ 4 = T4 x ^ 4 + x * T2 x ^ 4 := by
  have hd : T3 x ^ 2 - T4 x ^ 2 = 2 * x * T2 (x ^ 2) ^ 2 := by rw [h1, h2]; ring
  have hs : T3 x ^ 2 + T4 x ^ 2 = 2 * T3 (x ^ 2) ^ 2 := by rw [h1, h2]; ring
  have hmul : (T3 x ^ 2 - T4 x ^ 2) * (T3 x ^ 2 + T4 x ^ 2)
      = 4 * x * T2 (x ^ 2) ^ 2 * T3 (x ^ 2) ^ 2 := by rw [hd, hs]; ring
  have h3' : T2 x ^ 4 = 4 * T2 (x ^ 2) ^ 2 * T3 (x ^ 2) ^ 2 := by
    rw [show T2 x ^ 4 = (T2 x ^ 2) ^ 2 by ring, h3]
    ring
  have hkey : T3 x ^ 4 - T4 x ^ 4 = 4 * x * T2 (x ^ 2) ^ 2 * T3 (x ^ 2) ^ 2 := by
    rw [show T3 x ^ 4 - T4 x ^ 4
        = (T3 x ^ 2 - T4 x ^ 2) * (T3 x ^ 2 + T4 x ^ 2) by ring]
    exact hmul
  have : T3 x ^ 4 - T4 x ^ 4 = x * T2 x ^ 4 := by
    rw [hkey, h3']
    ring
  linear_combination this

/-- `U x ^ 2 = x ^ 2 θ₂(x)^8 + 4 θ₄(x^2)^8` from Jacobi and Landen. -/
lemma U_sq_of (x : ℂ)
    (hJ : T3 x ^ 4 = T4 x ^ 4 + x * T2 x ^ 4)
    (hL : T3 x * T4 x = T4 (x ^ 2) ^ 2) :
    U x ^ 2 = x ^ 2 * T2 x ^ 8 + 4 * T4 (x ^ 2) ^ 8 := by
  have hAB : T3 x ^ 4 * T4 x ^ 4 = T4 (x ^ 2) ^ 8 := by
    have h := congrArg (fun z => z ^ 4) hL
    rw [mul_pow] at h
    rw [← pow_mul, show (2 : ℕ) * 4 = 8 by norm_num] at h
    exact h
  have hX : T3 x ^ 4 - T4 x ^ 4 = x * T2 x ^ 4 := by rw [hJ]; ring
  have hsq : (T3 x ^ 4 + T4 x ^ 4) ^ 2
      = (T3 x ^ 4 - T4 x ^ 4) ^ 2 + 4 * (T3 x ^ 4 * T4 x ^ 4) := by ring
  rw [U, hsq, hX, hAB]
  ring

/-- `UQ (x^2) = U x` from the duplication identities. -/
lemma UQ_eq_U_of (x : ℂ)
    (h1 : T3 x ^ 2 = T3 (x ^ 2) ^ 2 + x * T2 (x ^ 2) ^ 2)
    (h2 : T4 x ^ 2 = T3 (x ^ 2) ^ 2 - x * T2 (x ^ 2) ^ 2) :
    UQ (x ^ 2) = U x := by
  rw [UQ, U]
  rw [show T3 x ^ 4 = (T3 x ^ 2) ^ 2 by ring, show T4 x ^ 4 = (T4 x ^ 2) ^ 2 by ring, h1, h2]
  ring

/-- `UQ (x^2) = U x` for `‖x‖ < 1` (from the duplication identities). -/
lemma UQ_eq_U (x : ℂ) (hx : ‖x‖ < 1) : UQ (x ^ 2) = U x :=
  UQ_eq_U_of x (theta_duplication x hx).1 (theta_duplication x hx).2.1

/-- Jacobi's identity `θ₃⁴ = θ₄⁴ + x θ₂⁴` for `‖x‖ < 1`. -/
lemma jacobi_identity (x : ℂ) (hx : ‖x‖ < 1) : T3 x ^ 4 = T4 x ^ 4 + x * T2 x ^ 4 :=
  jacobi_of_dup x (theta_duplication x hx).1 (theta_duplication x hx).2.1
    (theta_duplication x hx).2.2

/-- `U x ^ 2 = x ^ 2 θ₂(x)^8 + 4 θ₄(x^2)^8` for `‖x‖ < 1`. -/
lemma U_sq (x : ℂ) (hx : ‖x‖ < 1) : U x ^ 2 = x ^ 2 * T2 x ^ 8 + 4 * T4 (x ^ 2) ^ 8 :=
  U_sq_of x (jacobi_identity x hx) (theta_landen x hx)

/-- `T4 x ≠ 0` on the unit disc (from the product formula). -/
lemma T4_ne_zero_of (hprod : ∀ x : ℂ, ‖x‖ < 1 → T4 x = T4prod x) (x : ℂ) (hx : ‖x‖ < 1) :
    T4 x ≠ 0 := by
  rw [hprod x hx]
  exact T4prod_ne_zero x hx

/-- `T4 x ≠ 0` on the unit disc. -/
lemma T4_ne_zero (x : ℂ) (hx : ‖x‖ < 1) : T4 x ≠ 0 := T4_ne_zero_of theta_four_product x hx

/-- The product identity `hauptH(x^2) θ₄(x^2)^8 = -x^2 θ₂(x)^8`, given the product formulas. -/
lemma hauptH_mul_T4_of (hT4 : ∀ x : ℂ, ‖x‖ < 1 → T4 x = T4prod x)
    (hT2 : ∀ x : ℂ, ‖x‖ < 1 → T2 x = T2prod x)
    (x : ℂ) (hx : ‖x‖ < 1) : hauptH (x ^ 2) * T4 (x ^ 2) ^ 8 = -x ^ 2 * T2 x ^ 8 := by
  have hx2 : ‖x ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg x, hx]
  rw [hT4 (x ^ 2) hx2, hT2 x hx]
  have hmain := tprod_identity x hx
  rw [show hauptH (x ^ 2) = -256 * x ^ 2 * ∏' n : ℕ, (1 + (x ^ 2) ^ (n + 1)) ^ 24 from rfl]
  exact hmain

/-- The key identity `hauptH q - 4 = -(UQ q)^2/(T4 q)^8`, given the ingredients. -/
lemma hmain_of (hUQ : ∀ x : ℂ, ‖x‖ < 1 → UQ (x ^ 2) = U x)
    (hU : ∀ x : ℂ, ‖x‖ < 1 → U x ^ 2 = x ^ 2 * T2 x ^ 8 + 4 * T4 (x ^ 2) ^ 8)
    (hprod : ∀ x : ℂ, ‖x‖ < 1 → hauptH (x ^ 2) * T4 (x ^ 2) ^ 8 = -x ^ 2 * T2 x ^ 8)
    (hT4ne : ∀ x : ℂ, ‖x‖ < 1 → T4 (x ^ 2) ≠ 0) :
    ∀ q ∈ Metric.ball (0 : ℂ) 1, hauptH q - 4 = -(UQ q) ^ 2 / (T4 q) ^ 8 := by
  intro q hq
  have hq' : ‖q‖ < 1 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hq
    exact hq
  have hx : ‖Complex.sqrt q‖ < 1 := sqrt_norm_lt_one q hq'
  obtain ⟨h1, h2, h3, h4⟩ : UQ (Complex.sqrt q ^ 2) = U (Complex.sqrt q) ∧
      U (Complex.sqrt q) ^ 2 = Complex.sqrt q ^ 2 * T2 (Complex.sqrt q) ^ 8 +
        4 * T4 (Complex.sqrt q ^ 2) ^ 8 ∧
      hauptH (Complex.sqrt q ^ 2) * T4 (Complex.sqrt q ^ 2) ^ 8 =
        -Complex.sqrt q ^ 2 * T2 (Complex.sqrt q) ^ 8 ∧
      T4 (Complex.sqrt q ^ 2) ≠ 0 :=
    ⟨hUQ _ hx, hU _ hx, hprod _ hx, hT4ne _ hx⟩
  have h5 : hauptH (Complex.sqrt q ^ 2) - 4
      = -(UQ (Complex.sqrt q ^ 2)) ^ 2 / (T4 (Complex.sqrt q ^ 2)) ^ 8 := by
    have hden : (T4 (Complex.sqrt q ^ 2)) ^ 8 ≠ 0 := pow_ne_zero 8 h4
    rw [h1, h2]
    rw [eq_div_iff hden]
    linear_combination h3
  rwa [sqrt_sq] at h5

/-- Final packaging: a holomorphic square root of `hauptH - 4` on the disc, from the key
identity plus analyticity and nonvanishing of `T4`. -/
theorem hauptH_sqroot_of (hne : ∀ q ∈ Metric.ball (0 : ℂ) 1, T4 q ≠ 0)
    (hmain : ∀ q ∈ Metric.ball (0 : ℂ) 1,
      hauptH q - 4 = -(UQ q) ^ 2 / (T4 q) ^ 8) :
    ∃ k : ℂ → ℂ, DifferentiableOn ℂ k (Metric.ball 0 1) ∧
      ∀ q ∈ Metric.ball (0 : ℂ) 1, hauptH q - 4 = k q ^ 2 := by
  obtain ⟨-, hd4, -⟩ := theta_differentiable
  refine ⟨fun q => Complex.I * UQ q / T4 q ^ 4, ?_, ?_⟩
  · have hI : DifferentiableOn ℂ (fun _ : ℂ => Complex.I) (Metric.ball 0 1) :=
      differentiableOn_const (c := Complex.I) (s := Metric.ball 0 1)
    exact (hI.mul differentiableOn_UQ).div (hd4.pow 4)
      (fun q hq => pow_ne_zero 4 (hne q hq))
  · intro q hq
    rw [hmain q hq]
    have hne' : (T4 q) ^ 4 ≠ 0 := pow_ne_zero 4 (hne q hq)
    have hne8 : (T4 q) ^ 8 ≠ 0 := pow_ne_zero 8 (hne q hq)
    field_simp
    rw [show Complex.I ^ 2 = (-1 : ℂ) by rw [pow_two, Complex.I_mul_I]]
    ring

theorem hauptH_sqroot : ∃ k : ℂ → ℂ, DifferentiableOn ℂ k (Metric.ball 0 1) ∧
    ∀ q ∈ Metric.ball (0 : ℂ) 1, hauptH q - 4 = k q ^ 2 := by
  refine hauptH_sqroot_of ?_ ?_
  · intro q hq
    refine T4_ne_zero q ?_
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hq
    exact hq
  · refine hmain_of (fun x hx => UQ_eq_U x hx) (fun x hx => U_sq x hx) ?_ ?_
    · intro x hx
      exact hauptH_mul_T4_of theta_four_product theta_two_product x hx
    · intro x hx
      refine T4_ne_zero _ ?_
      rw [norm_pow]
      nlinarith [norm_nonneg x, hx]

end

theorem haupt_facts : HauptFacts :=
  ⟨differentiableOn_hauptH, deriv_hauptH_zero, hauptH_ne_zero, hauptH_sqroot⟩

end Work.Haupt
