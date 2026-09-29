import Mathlib
import Submission.Work.CPull.defs
import Submission.Work.Pure.b4_B2_ode
import Submission.Work.CPull.B2_coeff_bound
import Submission.Work.CPull.ps_analytic2
import Submission.Work.CPull.B2_rec_cplx

/-!
# Area CPull — the facts about `evp B₂` on the unit disc

`Work.CPull.evp_B2_ode` proves the differentiability, the series expansion and the differential
equation of `y ↦ evp B₂ y` on the disc of radius `4`.  This module re-derives them on the unit
disc without depending on the (still unproved) general power-series differentiability lemma
`Work.CPull.powerSeries_hasDerivAt`: the summability and differentiability input is taken from
`Work.CPull.ps_analytic2` (valid on the disc of radius `2`), the coefficient recurrence from the
formal ODE `Work.Pure.b4_B2_ode` is taken from `Work.CPull.B2_rec_cplx`, and the passage from the
recurrence to the analytic equation is `evp_ode_of_rec` below.
-/

namespace Work.CPull

open PowerSeries

/-- The coefficient sequence of `B₂`, as a function `ℕ → ℂ`. -/
private noncomputable def b2c : ℕ → ℂ :=
  fun n => ((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ)

private lemma evp_B2_eq (z : ℂ) :
    Work.CPull.evp Submission.CDTPlan.B2 z = ∑' n : ℕ, b2c n * z ^ n := rfl

private lemma tsum_mul_pow_shift (a : ℕ → ℂ) (y : ℂ) (h : Summable fun n => a n * y ^ n) :
    y * (∑' n, a n * y ^ n) = ∑' n, (if n = 0 then 0 else a (n - 1)) * y ^ n := by
  have hmul : y * (∑' n, a n * y ^ n) = ∑' n, a n * y ^ (n + 1) := by
    rw [← Summable.tsum_mul_left y h]
    exact tsum_congr (fun n => by ring)
  rw [hmul]
  set b : ℕ → ℂ := fun n => (if n = 0 then 0 else a (n - 1)) * y ^ n with hb
  have hb0 : b 0 = 0 := by simp [hb]
  have hb1 : ∀ n : ℕ, b (n + 1) = a n * y ^ (n + 1) := by intro n; simp [hb]
  have hsum_shift : Summable fun n => b (n + 1) := by
    rw [show (fun n => b (n + 1)) = fun n => a n * y ^ (n + 1) from funext hb1]
    exact (h.mul_right y).congr (fun n => by ring)
  have hSb : Summable b := (summable_nat_add_iff 1).mp hsum_shift
  have hshift : HasSum (fun n => b (n + 1)) (∑' n, b n) := by
    have h' := (hasSum_nat_add_iff' (f := b) 1).mpr hSb.hasSum
    rwa [Finset.sum_range_one, hb0, sub_zero] at h'
  rw [← hshift.tsum_eq]
  exact tsum_congr hb1

/-! ## The ODE from the recurrence

If the coefficients `c` satisfy the recurrence of `B₂` and the coefficient series of `c` and of
the derived series are summable at `y`, then the function `z ↦ Σ cₙ zⁿ` satisfies the ODE at `y`.
The proof expands both sides into a single series over `ℕ` — `y(4-y)·F'(y) = Σ (4n cₙ - (n-1)cₙ₋₁)yⁿ`
and `(2-y)·F(y) + y² = Σ (2cₙ - cₙ₋₁ + [n=2])yⁿ` — and compares termwise using the recurrence. -/

private theorem evp_ode_of_rec (c : ℕ → ℂ) (y : ℂ)
    (hrec : ∀ n : ℕ, 4 * ((n : ℂ) * c n) - (((n - 1 : ℕ) : ℂ) * c (n - 1))
      = 2 * c n - (if n = 0 then 0 else c (n - 1)) + (if n = 2 then 1 else 0))
    (hS : Summable fun n : ℕ => c n * y ^ n)
    (hS2 : Summable fun n : ℕ => (n : ℂ) * c n * y ^ n)
    (hS3 : Summable fun n : ℕ => ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n)
    (hderiv : deriv (fun z : ℂ => ∑' n : ℕ, c n * z ^ n) y
      = ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n) :
    y * (4 - y) * deriv (fun z : ℂ => ∑' n : ℕ, c n * z ^ n) y
      = (2 - y) * (∑' n : ℕ, c n * y ^ n) + y ^ 2 := by
  have hshift1 : Summable fun n : ℕ => (if n = 0 then 0 else c (n - 1) * y ^ (n - 1)) := by
    refine (summable_nat_add_iff 1).mp ?_
    simpa using hS
  have hS1 : Summable fun n : ℕ => (if n = 0 then 0 else c (n - 1)) * y ^ n := by
    refine (hshift1.mul_right y).congr (fun n => ?_)
    rcases n with _ | k
    · simp
    · simp [pow_succ, mul_assoc]
  have hshift2 : Summable fun n : ℕ =>
      (if n = 0 then 0 else (((n - 1 : ℕ) : ℂ) * c (n - 1)) * y ^ (n - 1)) := by
    refine (summable_nat_add_iff 1).mp ?_
    simpa using hS2
  have hS2' : Summable fun n : ℕ => ((((n - 1 : ℕ) : ℂ) * c (n - 1))) * y ^ n := by
    refine (hshift2.mul_right y).congr (fun n => ?_)
    rcases n with _ | k
    · simp
    · simp [pow_succ, mul_assoc]
  have hS4 : Summable fun n : ℕ => (4 * ((n : ℂ) * c n)) * y ^ n :=
    (hS2.mul_left 4).congr (fun n => by ring)
  have hS2c : Summable fun n : ℕ => (2 * c n) * y ^ n :=
    (hS.mul_left 2).congr (fun n => by ring)
  have hC : Summable fun n : ℕ => (if n = 2 then 1 else 0) * y ^ n := by
    refine summable_of_ne_finset_zero (s := {2}) fun n hn => ?_
    rw [Finset.mem_singleton] at hn
    simp [hn]
  have h1 : y * (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n)
      = ∑' n : ℕ, ((n : ℂ) * c n) * y ^ n := by
    rw [tsum_mul_pow_shift (fun n => ((n + 1 : ℕ) : ℂ) * c (n + 1)) y hS3]
    refine tsum_congr fun n => ?_
    rcases n with _ | k <;> simp
  have h2 : y * (∑' n : ℕ, ((n : ℂ) * c n) * y ^ n)
      = ∑' n : ℕ, ((((n - 1 : ℕ) : ℂ) * c (n - 1))) * y ^ n := by
    rw [tsum_mul_pow_shift (fun n => (n : ℂ) * c n) y hS2]
    refine tsum_congr fun n => ?_
    rcases n with _ | k <;> simp
  have h4 : 4 * (∑' n : ℕ, ((n : ℂ) * c n) * y ^ n)
      = ∑' n : ℕ, (4 * ((n : ℂ) * c n)) * y ^ n := by
    rw [(Summable.tsum_mul_left (4 : ℂ) hS2).symm]
    exact tsum_congr fun n => by ring
  have hleft : y * (4 - y) * (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n)
      = ∑' n : ℕ, (4 * ((n : ℂ) * c n) - (((n - 1 : ℕ) : ℂ) * c (n - 1))) * y ^ n := by
    rw [show y * (4 - y) * (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n)
        = 4 * (y * (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n))
          - y * (y * (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * c (n + 1) * y ^ n)) by ring]
    rw [h1, h4, h2, ← Summable.tsum_sub hS4 hS2']
    exact tsum_congr fun n => by ring
  have hyS : y * (∑' n : ℕ, c n * y ^ n)
      = ∑' n : ℕ, (if n = 0 then 0 else c (n - 1)) * y ^ n :=
    tsum_mul_pow_shift c y hS
  have hy2 : y ^ 2 = ∑' n : ℕ, (if n = 2 then 1 else 0) * y ^ n := by
    rw [tsum_eq_single 2 (fun b hb => by simp [hb])]
    norm_num
  have h2eq : 2 * (∑' n : ℕ, c n * y ^ n) = ∑' n : ℕ, (2 * c n) * y ^ n := by
    rw [(Summable.tsum_mul_left (2 : ℂ) hS).symm]
    exact tsum_congr fun n => by ring
  have hright : (2 - y) * (∑' n : ℕ, c n * y ^ n) + y ^ 2
      = ∑' n : ℕ, (2 * c n - (if n = 0 then 0 else c (n - 1))
        + (if n = 2 then 1 else 0)) * y ^ n := by
    rw [show (2 - y) * (∑' n : ℕ, c n * y ^ n) + y ^ 2
        = (2 * (∑' n : ℕ, c n * y ^ n) - y * (∑' n : ℕ, c n * y ^ n)) + y ^ 2 by ring]
    rw [h2eq, hyS, hy2, ← Summable.tsum_sub hS2c hS1, ← Summable.tsum_add (hS2c.sub hS1) hC]
    exact tsum_congr fun n => by ring
  have hkey : (∑' n : ℕ, (4 * ((n : ℂ) * c n) - (((n - 1 : ℕ) : ℂ) * c (n - 1))) * y ^ n)
      = ∑' n : ℕ, (2 * c n - (if n = 0 then 0 else c (n - 1))
        + (if n = 2 then 1 else 0)) * y ^ n :=
    tsum_congr fun n => by rw [hrec n]
  rw [hderiv, hleft, hright, hkey]


theorem evp_B2_facts_ball1 :
    DifferentiableOn ℂ (fun y : ℂ => Work.CPull.evp Submission.CDTPlan.B2 y) (Metric.ball 0 1) ∧
    (∀ y ∈ Metric.ball (0:ℂ) 1, HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ) * y ^ n)
      (Work.CPull.evp Submission.CDTPlan.B2 y)) ∧
    (∀ y ∈ Metric.ball (0:ℂ) 1,
      y * (4 - y) * deriv (fun w : ℂ => Work.CPull.evp Submission.CDTPlan.B2 w) y
        = (2 - y) * Work.CPull.evp Submission.CDTPlan.B2 y + y ^ 2) := by
  have hb : ∀ n : ℕ, ‖b2c n‖ ≤ 3 * (1 / 4 : ℝ) ^ n :=
    fun n => B2_coeff_bound n
  obtain ⟨hS, hS2, hS3, hhderiv⟩ := ps_analytic2 b2c 3 (by norm_num) hb
  have hsub : Metric.ball (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 2 :=
    Metric.ball_subset_ball (by norm_num)
  have hy2 : ∀ y ∈ Metric.ball (0 : ℂ) 1, ‖y‖ < 2 := by
    intro y hy
    have h1 : ‖y‖ < 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hy
      simpa using hy
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    have hd : DifferentiableAt ℂ (fun z : ℂ => ∑' n : ℕ, b2c n * z ^ n) y :=
      (hhderiv y (hy2 y hy)).differentiableAt
    exact hd.differentiableWithinAt
  · intro y hy
    exact (hS y (hy2 y hy)).hasSum
  · intro y hy
    have h2 := hy2 y hy
    exact evp_ode_of_rec b2c y (fun n => B2_rec_cplx n) (hS y h2) (hS2 y h2) (hS3 y h2)
      (hhderiv y h2).deriv

end Work.CPull
