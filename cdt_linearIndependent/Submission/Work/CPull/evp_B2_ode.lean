import Mathlib
import Submission.Work.CPull.defs
import Submission.Work.Pure.b4_B2_ode
import Submission.Work.CPull.B2_coeff_bound
import Submission.Work.CPull.powerSeries_hasDerivAt

/-!
# Area CPull — the analytic ODE satisfied by `evp B₂` on the disc of radius `4`

`Submission.CDTPlan.B2` is the pure function `B₂ = Σ_{n ≥ 2} 2·(n-2)!·n!/(2n)! · yⁿ`
(paper Calegari–Dimitrov–Tang, eq. `(defB)`), and `Work.Pure.b4_B2_ode` proves the *formal*
identity

`X·(4 - X)·B₂' = (2 - X)·B₂ + X²`

in `ℚ⟦X⟧`.  This module transfers it to the analytic function `y ↦ evp B₂ y = Σ cₙ yⁿ`
on the disc `‖y‖ < 4`, which is its true disc of convergence:

* `Work.CPull.B2_coeff_bound` gives `‖cₙ‖ ≤ 3·(1/4)ⁿ` (so the radius is `≥ 4`);
* `Work.CPull.powerSeries_hasDerivAt` gives term-by-term differentiability inside the disc,
  i.e. `deriv (evp B₂) y = Σ (n+1) cₙ₊₁ yⁿ`;
* `Work.CPull.B2_coeff_rec` below extracts the coefficient recurrence
  `4n·cₙ - (n-1)·cₙ₋₁ = 2·cₙ - cₙ₋₁ + [n = 2]` from the formal identity, and
  `evp_ode_of_rec` turns a recurrence of this shape together with the termwise derivative
  and the summabilities into the analytic ODE.

The assembly at the end is the requested `Work.CPull.evp_B2_ode`.
-/

namespace Work.CPull

open PowerSeries

/-! ## Extracting the coefficient recurrence from the formal ODE

The two auxiliary computations `coeff_lhs`/`coeff_rhs` are the coefficient form of the two sides
of `Work.Pure.b4_B2_ode`; comparing them gives the recurrence used by the analytic argument. -/

private lemma coeff_X_mul (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (PowerSeries.X * f) = if 1 ≤ m then PowerSeries.coeff (m - 1) f else 0 := by
  simpa using PowerSeries.coeff_X_pow_mul' f 1 m

private lemma coeff_XD (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (PowerSeries.X * PowerSeries.derivative (R := ℚ) f) =
      (m : ℚ) * PowerSeries.coeff m f := by
  rcases m with _ | k
  · rw [PowerSeries.coeff_zero_X_mul]; simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]; push_cast; ring

private lemma coeff_XsqD (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (PowerSeries.X ^ 2 * PowerSeries.derivative (R := ℚ) f) =
      ((m - 1 : ℕ) : ℚ) * PowerSeries.coeff (m - 1) f := by
  have h : (PowerSeries.X : PowerSeries ℚ) ^ 2 * PowerSeries.derivative (R := ℚ) f
      = PowerSeries.X * (PowerSeries.X * PowerSeries.derivative (R := ℚ) f) := by ring
  rw [h]
  rcases m with _ | k
  · rw [PowerSeries.coeff_zero_X_mul]; simp
  · rw [PowerSeries.coeff_succ_X_mul, coeff_XD]; simp only [Nat.add_sub_cancel]

private lemma coeff_C2_mul (m : ℕ) (g : PowerSeries ℚ) :
    PowerSeries.coeff m ((2 : PowerSeries ℚ) * g) = 2 * PowerSeries.coeff m g := by
  rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C_mul]

private lemma coeff_C4_mul (m : ℕ) (g : PowerSeries ℚ) :
    PowerSeries.coeff m ((4 : PowerSeries ℚ) * g) = 4 * PowerSeries.coeff m g := by
  rw [show (4 : PowerSeries ℚ) = PowerSeries.C 4 from rfl, PowerSeries.coeff_C_mul]

private lemma coeff_Xsq (m : ℕ) :
    PowerSeries.coeff m ((PowerSeries.X : PowerSeries ℚ) ^ 2) = if m = 2 then 1 else 0 := by
  simpa using PowerSeries.coeff_X_pow m 2

private lemma coeff_lhs (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (PowerSeries.X * (4 - PowerSeries.X) * PowerSeries.derivative (R := ℚ) f) =
      4 * ((m : ℚ) * PowerSeries.coeff m f)
        - ((m - 1 : ℕ) : ℚ) * PowerSeries.coeff (m - 1) f := by
  rw [show PowerSeries.X * (4 - PowerSeries.X) * PowerSeries.derivative (R := ℚ) f
      = (4 : PowerSeries ℚ) * (PowerSeries.X * PowerSeries.derivative (R := ℚ) f)
        - PowerSeries.X ^ 2 * PowerSeries.derivative (R := ℚ) f by ring]
  rw [map_sub, coeff_C4_mul, coeff_XD, coeff_XsqD]

private lemma coeff_rhs (m : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff m ((2 - PowerSeries.X) * f + PowerSeries.X ^ 2) =
      2 * PowerSeries.coeff m f - (if 1 ≤ m then PowerSeries.coeff (m - 1) f else 0)
        + (if m = 2 then 1 else 0) := by
  rw [show (2 - PowerSeries.X) * f + PowerSeries.X ^ 2
      = (2 : PowerSeries ℚ) * f - PowerSeries.X * f + PowerSeries.X ^ 2 by ring]
  rw [map_add, map_sub, coeff_C2_mul, coeff_X_mul, coeff_Xsq]

/-- The coefficient recurrence of `B₂`, read off the formal ODE `Work.Pure.b4_B2_ode`:
for every `n`, `4n·cₙ - (n-1)·cₙ₋₁ = 2·cₙ - cₙ₋₁ + [n = 2]` (where `c₋₁` means `c₀`, the
convention being `(n - 1 : ℕ) = 0` for `n = 0`). -/
theorem B2_coeff_rec (m : ℕ) :
    4 * ((m : ℚ) * PowerSeries.coeff m Submission.CDTPlan.B2)
      - (((m - 1 : ℕ) : ℚ) * PowerSeries.coeff (m - 1) Submission.CDTPlan.B2)
    = 2 * PowerSeries.coeff m Submission.CDTPlan.B2
      - (if m = 0 then 0 else PowerSeries.coeff (m - 1) Submission.CDTPlan.B2)
      + (if m = 2 then 1 else 0) := by
  have h := congrArg (fun f : PowerSeries ℚ => PowerSeries.coeff m f) Work.Pure.b4_B2_ode
  rw [coeff_lhs, coeff_rhs] at h
  rw [h]
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg hm, if_pos (by omega : 1 ≤ m)]

/-- The coefficient recurrence of `B₂` over `ℂ`. -/
private theorem B2_coeff_rec_c (m : ℕ) :
    4 * ((m : ℂ) * ((PowerSeries.coeff m Submission.CDTPlan.B2 : ℚ) : ℂ))
      - (((m - 1 : ℕ) : ℂ) * ((PowerSeries.coeff (m - 1) Submission.CDTPlan.B2 : ℚ) : ℂ))
    = 2 * ((PowerSeries.coeff m Submission.CDTPlan.B2 : ℚ) : ℂ)
      - (if m = 0 then 0 else ((PowerSeries.coeff (m - 1) Submission.CDTPlan.B2 : ℚ) : ℂ))
      + (if m = 2 then 1 else 0) := by
  have h' := congrArg (fun z : ℚ => (z : ℂ)) (B2_coeff_rec m)
  push_cast at h'
  rw [show (((if m = 0 then (0 : ℚ) else PowerSeries.coeff (m - 1) Submission.CDTPlan.B2 : ℚ)) : ℂ)
      = (if m = 0 then 0 else ((PowerSeries.coeff (m - 1) Submission.CDTPlan.B2 : ℚ) : ℂ)) from by
        split_ifs <;> norm_num] at h'
  rw [show (((if m = 2 then (1 : ℚ) else 0 : ℚ)) : ℂ) = (if m = 2 then (1 : ℂ) else 0) from by
        split_ifs <;> norm_num] at h'
  exact h'

/-! ## Multiplication of a power series of a complex number by the variable

`tsum_mul_pow_shift` is the only manipulation of series needed below: multiplying
`Σ aₙ yⁿ` by `y` shifts the coefficient sequence. -/

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

/-! ## The main theorem -/

theorem evp_B2_ode :
    DifferentiableOn ℂ (fun y : ℂ => Work.CPull.evp Submission.CDTPlan.B2 y) (Metric.ball 0 4) ∧
    (∀ y ∈ Metric.ball (0 : ℂ) 4, HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ) * y ^ n)
      (Work.CPull.evp Submission.CDTPlan.B2 y)) ∧
    (∀ y ∈ Metric.ball (0 : ℂ) 4,
      y * (4 - y) * deriv (fun w : ℂ => Work.CPull.evp Submission.CDTPlan.B2 w) y
        = (2 - y) * Work.CPull.evp Submission.CDTPlan.B2 y + y ^ 2) := by
  obtain ⟨hS, hS2, hS3, hderiv⟩ :=
    powerSeries_hasDerivAt (fun n : ℕ => ((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ))
      3 (by norm_num) B2_coeff_bound
  refine ⟨?_, ?_, ?_⟩
  · -- differentiability of the sum on the disc
    intro y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact ((hderiv y hy).differentiableAt).differentiableWithinAt
  · -- the series sums to `evp B₂`
    intro y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact (hS y hy).hasSum
  · -- the ODE
    intro y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact evp_ode_of_rec _ y (fun n => B2_coeff_rec_c n) (hS y hy) (hS2 y hy) (hS3 y hy)
      (hderiv y hy).deriv

end Work.CPull
