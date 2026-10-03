import Mathlib
import Submission.Work.Pert.EuDefs

/-!
# PERT · `Work.Pert.EuCenterBounds`

The `η/450` (difference) and `η/60` (sum) oscillation bounds for the deviation
`E_u = τ₀ ∘ τ_f - id` at the two centres `±iη` (Shishikura (4.2.5), the cross estimate).

Writing `s = euS α = 2πiα`, `t = euT α η = 2παη = -s·iη`, `ψ = euPsi α = (e^s-1)/s` and
`E = e^s = 1 - σu₀`, the two combinations are exactly

* `E_u(iη) - E_u(-iη) = 2iη(u₀ sinh t/(tψ) - 1) = 2iη(u₀/ψ - 1) + 2u₀(sinh t - t)/(1-E)`,
* `E_u(iη) + E_u(-iη) = 2(cosh t - 1)/σ`.

The estimates are therefore pure Taylor bounds: `‖ψ - 1‖ ≤ (1/2 + 1/10000)‖s‖`,
`‖sinh w - w - w³/6‖ ≤ ‖w‖⁵/60`, `‖cosh w - 1‖ ≤ ‖w‖²/2 + ‖w‖⁴/24 + ‖w‖⁵/60`, together with
`‖s‖η ≤ 1/64` (i.e. `‖t‖ ≤ 1/64`), `‖u₀ - 1‖ ≤ 1/1024` and `η ≥ 100`.
-/

namespace Work.Pert

open Complex

noncomputable section

set_option linter.unusedVariables false

/-- Quartic Taylor remainder of `exp` at the origin: for `‖z‖ ≤ 1/2`,
`‖e^z - (1 + z + z²/2 + z³/6 + z⁴/24)‖ ≤ ‖z‖⁵/60`. -/
lemma exp_T4_rem {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    ‖Complex.exp z - (1 + z + z^2/2 + z^3/6 + z^4/24)‖ ≤ ‖z‖^5/60 := by
  have h := Complex.exp_bound' (x := z) (n := 5) (by push_cast; linarith)
  have hs : (∑ m ∈ Finset.range 5, z ^ m / (m.factorial : ℂ))
      = 1 + z + z^2/2 + z^3/6 + z^4/24 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at h
  rw [show (Nat.factorial 5 : ℝ) = 120 by norm_num] at h
  rwa [show ‖z‖ ^ 5 / 120 * 2 = ‖z‖^5/60 by ring] at h

/-- **Sharp Taylor estimate for `sinh`**: for `‖z‖ ≤ 1/2`, `‖sinh z - z - z³/6‖ ≤ ‖z‖⁵/60`. -/
lemma norm_sinh_sub_id_sub_cube_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.sinh z - z - z^3/6‖ ≤ ‖z‖^5/60 := by
  have hb1 := exp_T4_rem (z := z) hz
  have hb2 := exp_T4_rem (z := -z) (by rw [norm_neg]; exact hz)
  rw [norm_neg] at hb2
  have hid : Complex.sinh z - z - z^3/6
      = ((Complex.exp z - (1 + z + z^2/2 + z^3/6 + z^4/24))
          - (Complex.exp (-z) - (1 + (-z) + (-z)^2/2 + (-z)^3/6 + (-z)^4/24)))/2 := by
    rw [Complex.sinh]; ring
  rw [hid, Complex.norm_div]
  rw [show ‖(2:ℂ)‖ = 2 by norm_num]
  have hab : ‖(Complex.exp z - (1 + z + z^2/2 + z^3/6 + z^4/24))
        - (Complex.exp (-z) - (1 + (-z) + (-z)^2/2 + (-z)^3/6 + (-z)^4/24))‖ ≤ ‖z‖^5/30 := by
    refine (norm_sub_le _ _).trans ?_
    linarith
  linarith

/-- **Taylor estimate for `cosh`**: for `‖z‖ ≤ 1/2`,
`‖cosh z - 1‖ ≤ ‖z‖²/2 + ‖z‖⁴/24 + ‖z‖⁵/60`. -/
lemma norm_cosh_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.cosh z - 1‖ ≤ ‖z‖^2/2 + ‖z‖^4/24 + ‖z‖^5/60 := by
  have hb1 := exp_T4_rem (z := z) hz
  have hb2 := exp_T4_rem (z := -z) (by rw [norm_neg]; exact hz)
  rw [norm_neg] at hb2
  have hid : Complex.cosh z - 1
      = ((Complex.exp z - (1 + z + z^2/2 + z^3/6 + z^4/24))
          + (Complex.exp (-z) - (1 + (-z) + (-z)^2/2 + (-z)^3/6 + (-z)^4/24)))/2
        + (z^2/2 + z^4/24) := by
    rw [Complex.cosh]; ring
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖((Complex.exp z - (1 + z + z^2/2 + z^3/6 + z^4/24))
        + (Complex.exp (-z) - (1 + (-z) + (-z)^2/2 + (-z)^3/6 + (-z)^4/24)))/2‖ ≤ ‖z‖^5/60 := by
    rw [Complex.norm_div]
    rw [show ‖(2:ℂ)‖ = 2 by norm_num]
    have hab : ‖(Complex.exp z - (1 + z + z^2/2 + z^3/6 + z^4/24))
        + (Complex.exp (-z) - (1 + (-z) + (-z)^2/2 + (-z)^3/6 + (-z)^4/24))‖ ≤ ‖z‖^5/30 := by
      refine (norm_add_le _ _).trans ?_
      linarith
    linarith
  have h2 : ‖z^2/2 + z^4/24‖ ≤ ‖z‖^2/2 + ‖z‖^4/24 := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_div, Complex.norm_div, Complex.norm_pow, Complex.norm_pow]
    norm_num
  linarith

/-- `‖ψ - 1‖ ≤ (1/2 + 1/10000)‖s‖` for `ψ = (e^s - 1)/s` and `‖s‖ ≤ 1/6400`, `s ≠ 0`. -/
lemma euPsi_sub_one_le {α : ℂ} (hα : α ≠ 0) (hs : ‖euS α‖ ≤ 1 / 6400) :
    ‖euPsi α - 1‖ ≤ (5001 / 10000) * ‖euS α‖ := by
  have hs0 : 0 < ‖euS α‖ := norm_pos_iff.mpr (euS_ne_zero hα)
  have hnorm : ‖euS α‖ ≤ 1 / 2 := by linarith
  have hb := exp_T4_rem (z := euS α) hnorm
  have hsplit : Complex.exp (euS α) - 1 - euS α
      = (Complex.exp (euS α) - (1 + euS α + (euS α)^2/2 + (euS α)^3/6 + (euS α)^4/24))
        + ((euS α)^2/2 + (euS α)^3/6 + (euS α)^4/24) := by ring
  have hpoly : ‖(euS α)^2/2 + (euS α)^3/6 + (euS α)^4/24‖
      ≤ ‖euS α‖^2 * (1/2 + ‖euS α‖/6 + ‖euS α‖^2/24) := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [Complex.norm_div, Complex.norm_div, Complex.norm_div, Complex.norm_pow,
      Complex.norm_pow, Complex.norm_pow]
    norm_num
    ring_nf
    rfl
  have hnum : ‖Complex.exp (euS α) - 1 - euS α‖
      ≤ ‖euS α‖^2 * (1/2 + ‖euS α‖/6 + ‖euS α‖^2/24) + ‖euS α‖^5/60 := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    linarith [hb, hpoly]
  have heq : euPsi α - 1 = (Complex.exp (euS α) - 1 - euS α)/euS α := by
    rw [euPsi]
    rw [div_sub_one (euS_ne_zero hα)]
  rw [heq, Complex.norm_div, div_le_iff₀ hs0]
  have hkey : ‖euS α‖^2 * (1/2 + ‖euS α‖/6 + ‖euS α‖^2/24) + ‖euS α‖^5/60
      ≤ (5001/10000) * ‖euS α‖ * ‖euS α‖ := by
    nlinarith [hs0, hs, sq_nonneg ‖euS α‖, pow_nonneg hs0.le 3]
  linarith

/-- The exact algebra of the difference of the two centre values:
`-(1-e^t)/σ - iη + (1-e^{-t})/σ - iη = 2iη(u₀/ψ - 1) + 2u₀(sinh t - t)/(1-e^s)`
under `σu₀ = 1 - e^s`, `sψ = e^s - 1`, `t = -s·iη`. -/
lemma eu_center_diff_algebra {σ u₀ s t ψ : ℂ} {η : ℝ}
    (hσ : σ ≠ 0) (hu₀ : u₀ ≠ 0) (hs : s ≠ 0) (hη : (η:ℂ) ≠ 0)
    (hE : Complex.exp s = 1 - σ*u₀)
    (hψ : ψ = (Complex.exp s - 1)/s)
    (ht : t = -(s)*(Complex.I*(η:ℂ))) :
    (-(1 - Complex.exp t)/σ - Complex.I*(η:ℂ))
      - (-(1 - Complex.exp (-t))/σ + Complex.I*(η:ℂ))
    = 2*Complex.I*(η:ℂ)*(u₀/ψ - 1) + 2*u₀*(Complex.sinh t - t)/(1 - Complex.exp s) := by
  rw [Complex.sinh]
  rw [hψ, hE, ht]
  field_simp
  ring

/-- The exact algebra of the sum of the two centre values:
`-(1-e^t)/σ - iη - (1-e^{-t})/σ + iη = 2(cosh t - 1)/σ`. -/
lemma eu_center_sum_algebra {σ u₀ s t ψ : ℂ} {η : ℝ}
    (hσ : σ ≠ 0) (hu₀ : u₀ ≠ 0) (hs : s ≠ 0) (hη : (η:ℂ) ≠ 0)
    (hE : Complex.exp s = 1 - σ*u₀)
    (hψ : ψ = (Complex.exp s - 1)/s)
    (ht : t = -(s)*(Complex.I*(η:ℂ))) :
    (-(1 - Complex.exp t)/σ - Complex.I*(η:ℂ))
      + (-(1 - Complex.exp (-t))/σ + Complex.I*(η:ℂ))
    = 2*(Complex.cosh t - 1)/σ := by
  rw [Complex.cosh]
  field_simp
  ring

/-- Arithmetic core of the **difference** bound: with `a η ≤ 1/64` (so `‖t‖ = aη ≤ 1/64`),
`r ≤ 1060/10⁶` (the `ψ`-ratio), `b ≤ 1025/1024` (bound for `‖u₀‖`), `Zb ≤ a³η³/6 + a⁵η⁵/60`
(the sharp `sinh` bound) and `D ≥ (9999/10000)a` (lower bound for `‖1 - e^s‖ = ‖sψ‖`),
one has `2ηr + 2b(Zb/D) ≤ η/450`. -/
lemma arith_diff_bound {η a b r Zb D : ℝ} (hη : 0 < η) (ha : 0 ≤ a) (hD : 0 < D)
    (hSη : a * η ≤ 1 / 64) (hr : r ≤ 1060 / 1000000) (hb0 : 0 ≤ b) (hb : b ≤ 1025 / 1024)
    (hZb0 : 0 ≤ Zb) (hZb : Zb ≤ a ^ 3 * η ^ 3 / 6 + a ^ 5 * η ^ 5 / 60)
    (hDlb : (9999 / 10000) * a ≤ D) :
    2 * η * r + 2 * b * (Zb / D) ≤ η / 450 := by
  have haη0 : 0 ≤ a * η := mul_nonneg ha hη.le
  have hA0 : 0 ≤ a ^ 2 * η ^ 3 / 6 + a ^ 4 * η ^ 5 / 60 := by positivity
  have hX : Zb / D ≤ (10000 / 9999) * (a ^ 2 * η ^ 3 / 6 + a ^ 4 * η ^ 5 / 60) := by
    rw [div_le_iff₀ hD]
    calc Zb ≤ a ^ 3 * η ^ 3 / 6 + a ^ 5 * η ^ 5 / 60 := hZb
      _ = a * (a ^ 2 * η ^ 3 / 6 + a ^ 4 * η ^ 5 / 60) := by ring
      _ = ((10000 / 9999) * (a ^ 2 * η ^ 3 / 6 + a ^ 4 * η ^ 5 / 60)) * ((9999 / 10000) * a) := by
            ring
      _ ≤ ((10000 / 9999) * (a ^ 2 * η ^ 3 / 6 + a ^ 4 * η ^ 5 / 60)) * D :=
            mul_le_mul_of_nonneg_left hDlb (by positivity)
  have hstep : 2 * b * (Zb / D)
      ≤ 2 * (1025 / 1024) * ((10000 / 9999) * (a ^ 2 * η ^ 3 / 6 + a ^ 4 * η ^ 5 / 60)) := by
    calc 2 * b * (Zb / D) ≤ (2 * (1025 / 1024)) * (Zb / D) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (2 * (1025 / 1024)) * ((10000 / 9999) * (a ^ 2 * η ^ 3 / 6 + a ^ 4 * η ^ 5 / 60)) :=
          mul_le_mul_of_nonneg_left hX (by norm_num)
  have hp2 : (a * η) ^ 2 ≤ (1 / 64 : ℝ) ^ 2 := pow_le_pow_left₀ haη0 hSη 2
  have hp4 : (a * η) ^ 4 ≤ (1 / 64 : ℝ) ^ 4 := pow_le_pow_left₀ haη0 hSη 4
  have hm2 : (a * η) ^ 2 * η ≤ (1 / 64 : ℝ) ^ 2 * η := mul_le_mul_of_nonneg_right hp2 hη.le
  have hm4 : (a * η) ^ 4 * η ≤ (1 / 64 : ℝ) ^ 4 * η := mul_le_mul_of_nonneg_right hp4 hη.le
  have ha2 : a ^ 2 * η ^ 3 ≤ η / 4096 := by
    rw [show a ^ 2 * η ^ 3 = (a * η) ^ 2 * η by ring,
      show η / 4096 = (1 / 64 : ℝ) ^ 2 * η by ring]
    exact hm2
  have ha4 : a ^ 4 * η ^ 5 ≤ η / 16777216 := by
    rw [show a ^ 4 * η ^ 5 = (a * η) ^ 4 * η by ring,
      show η / 16777216 = (1 / 64 : ℝ) ^ 4 * η by ring]
    exact hm4
  have hfin : 2 * (1060 / 1000000) * η
      + 2 * (1025 / 1024) * (10000 / 9999) * (a ^ 2 * η ^ 3 / 6 + a ^ 4 * η ^ 5 / 60)
      ≤ η / 450 := by
    nlinarith [ha2, ha4, hη]
  have hr' : 2 * η * r ≤ 2 * η * (1060 / 1000000) :=
    mul_le_mul_of_nonneg_left hr (by positivity)
  linarith [hr', hstep, hfin]

/-- Arithmetic core of the **sum** bound: with `a η ≤ 1/64`, `b ≤ 1025/1024`,
`Zc ≤ a²η²/2 + a⁴η⁴/24 + a⁵η⁵/60` (the `cosh` bound) and `D ≥ (9999/10000)a`,
one has `2b(Zc/D) ≤ η/60`. -/
lemma arith_sum_bound {η a b Zc D : ℝ} (hη : 0 < η) (ha : 0 ≤ a) (hD : 0 < D)
    (hSη : a * η ≤ 1 / 64) (hb0 : 0 ≤ b) (hb : b ≤ 1025 / 1024) (hZc0 : 0 ≤ Zc)
    (hZc : Zc ≤ a ^ 2 * η ^ 2 / 2 + a ^ 4 * η ^ 4 / 24 + a ^ 5 * η ^ 5 / 60)
    (hDlb : (9999 / 10000) * a ≤ D) :
    2 * b * (Zc / D) ≤ η / 60 := by
  have haη0 : 0 ≤ a * η := mul_nonneg ha hη.le
  have hA0 : 0 ≤ a * η ^ 2 / 2 + a ^ 3 * η ^ 4 / 24 + a ^ 4 * η ^ 5 / 60 := by positivity
  have hX : Zc / D
      ≤ (10000 / 9999) * (a * η ^ 2 / 2 + a ^ 3 * η ^ 4 / 24 + a ^ 4 * η ^ 5 / 60) := by
    rw [div_le_iff₀ hD]
    calc Zc ≤ a ^ 2 * η ^ 2 / 2 + a ^ 4 * η ^ 4 / 24 + a ^ 5 * η ^ 5 / 60 := hZc
      _ = a * (a * η ^ 2 / 2 + a ^ 3 * η ^ 4 / 24 + a ^ 4 * η ^ 5 / 60) := by ring
      _ = ((10000 / 9999) * (a * η ^ 2 / 2 + a ^ 3 * η ^ 4 / 24 + a ^ 4 * η ^ 5 / 60))
            * ((9999 / 10000) * a) := by ring
      _ ≤ ((10000 / 9999) * (a * η ^ 2 / 2 + a ^ 3 * η ^ 4 / 24 + a ^ 4 * η ^ 5 / 60)) * D :=
            mul_le_mul_of_nonneg_left hDlb (by positivity)
  have hstep : 2 * b * (Zc / D)
      ≤ 2 * (1025 / 1024)
        * ((10000 / 9999) * (a * η ^ 2 / 2 + a ^ 3 * η ^ 4 / 24 + a ^ 4 * η ^ 5 / 60)) := by
    calc 2 * b * (Zc / D) ≤ (2 * (1025 / 1024)) * (Zc / D) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (2 * (1025 / 1024))
            * ((10000 / 9999) * (a * η ^ 2 / 2 + a ^ 3 * η ^ 4 / 24 + a ^ 4 * η ^ 5 / 60)) :=
          mul_le_mul_of_nonneg_left hX (by norm_num)
  have hp1 : (a * η) ^ 1 ≤ (1 / 64 : ℝ) ^ 1 := pow_le_pow_left₀ haη0 hSη 1
  have hp3 : (a * η) ^ 3 ≤ (1 / 64 : ℝ) ^ 3 := pow_le_pow_left₀ haη0 hSη 3
  have hp4 : (a * η) ^ 4 ≤ (1 / 64 : ℝ) ^ 4 := pow_le_pow_left₀ haη0 hSη 4
  have hm1 : (a * η) ^ 1 * η ≤ (1 / 64 : ℝ) ^ 1 * η := mul_le_mul_of_nonneg_right hp1 hη.le
  have hm3 : (a * η) ^ 3 * η ≤ (1 / 64 : ℝ) ^ 3 * η := mul_le_mul_of_nonneg_right hp3 hη.le
  have hm4 : (a * η) ^ 4 * η ≤ (1 / 64 : ℝ) ^ 4 * η := mul_le_mul_of_nonneg_right hp4 hη.le
  have hb1 : a * η ^ 2 ≤ η / 64 := by
    rw [show a * η ^ 2 = (a * η) ^ 1 * η by ring,
      show η / 64 = (1 / 64 : ℝ) ^ 1 * η by ring]
    exact hm1
  have hb3 : a ^ 3 * η ^ 4 ≤ η / 262144 := by
    rw [show a ^ 3 * η ^ 4 = (a * η) ^ 3 * η by ring,
      show η / 262144 = (1 / 64 : ℝ) ^ 3 * η by ring]
    exact hm3
  have hb4 : a ^ 4 * η ^ 5 ≤ η / 16777216 := by
    rw [show a ^ 4 * η ^ 5 = (a * η) ^ 4 * η by ring,
      show η / 16777216 = (1 / 64 : ℝ) ^ 4 * η by ring]
    exact hm4
  have hfin : 2 * (1025 / 1024) * (10000 / 9999)
      * (a * η ^ 2 / 2 + a ^ 3 * η ^ 4 / 24 + a ^ 4 * η ^ 5 / 60) ≤ η / 60 := by
    nlinarith [hb1, hb3, hb4, hη]
  linarith [hstep, hfin]

/-- **Shishikura (4.2.5), the two centre values.**  Under the standing hypotheses
`η ≥ 100`, `σ ≠ 0`, `α ≠ 0`, `‖u₀ - 1‖ ≤ 1/1024`, `2π‖α‖η ≤ 1/64` and `1 - σu₀ = e^{2πiα}`,
the oscillation of `E_u = τ₀ ∘ τ_f - id` between `iη` and `-iη` is at most `η/450`, and its
average at most `η/60`. -/
theorem EuCenterBounds {σ α u₀ : ℂ} {η : ℝ}
    (hη : 0 < η) (hη100 : 100 ≤ η) (hσ : σ ≠ 0) (hα : α ≠ 0)
    (hu₀ : ‖u₀ - 1‖ ≤ 1 / 1024)
    (hαη : 2 * Real.pi * ‖α‖ * η ≤ 1 / 64)
    (heq : 1 - σ * u₀ = Complex.exp (euS α)) :
    ‖Eu σ α (Complex.I * (η : ℂ)) - Eu σ α (-(Complex.I * (η : ℂ)))‖ ≤ η / 450
    ∧ ‖Eu σ α (Complex.I * (η : ℂ)) + Eu σ α (-(Complex.I * (η : ℂ)))‖ ≤ η / 60 := by
  have hηc : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have hs_ne : euS α ≠ 0 := euS_ne_zero hα
  have hs0 : 0 < ‖euS α‖ := norm_pos_iff.mpr hs_ne
  have hsη0 : (0:ℝ) ≤ ‖euS α‖ * η := mul_nonneg hs0.le hη.le
  have hSle : ‖euS α‖ * η ≤ 1 / 64 := by rw [norm_euS]; exact hαη
  have hS6400 : ‖euS α‖ ≤ 1 / 6400 := by nlinarith [hSle, hη100, hs0]
  have hu₀_ne : u₀ ≠ 0 := by
    intro h0
    rw [h0] at hu₀
    norm_num at hu₀
  have hu₀norm : ‖u₀‖ ≤ 1025 / 1024 := by
    calc ‖u₀‖ = ‖(u₀ - 1) + 1‖ := by ring_nf
      _ ≤ ‖u₀ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1025 / 1024 := by simp; linarith
  have hEne : (1:ℂ) - Complex.exp (euS α) ≠ 0 := by
    have h : (1:ℂ) - Complex.exp (euS α) = σ*u₀ := by rw [← heq]; ring
    rw [h]; exact mul_ne_zero hσ hu₀_ne
  have hinv : (1:ℂ)/σ = u₀/(1 - Complex.exp (euS α)) := by
    rw [div_eq_div_iff hσ hEne]
    have h : (1:ℂ) - Complex.exp (euS α) = σ*u₀ := by rw [← heq]; ring
    rw [h]; ring
  have hinv' : σ⁻¹ = u₀/(1 - Complex.exp (euS α)) := by
    rw [inv_eq_one_div, hinv]
  -- unfold `Eu`
  have hEu : ∀ ζ : ℂ, Eu σ α ζ = -(1 - Complex.exp (-(euS α * ζ))) / σ - ζ := by
    intro ζ
    rw [Eu, MandelDim.tau0, tauC,
      show -(2 * Real.pi * Complex.I * α * ζ) = -(euS α * ζ) from rfl, neg_div, one_div_div]
    try ring
  have hE1 : Eu σ α (Complex.I * (η:ℂ)) = -(1 - Complex.exp (euT α η)) / σ - Complex.I * (η:ℂ) := by
    rw [hEu (Complex.I * (η:ℂ))]
    rw [show -(euS α * (Complex.I * (η:ℂ))) = euT α η from by
      rw [euT_eq_neg_mul, neg_mul]]
  have hE2 : Eu σ α (-(Complex.I * (η:ℂ)))
      = -(1 - Complex.exp (-(euT α η))) / σ + Complex.I * (η:ℂ) := by
    rw [hEu (-(Complex.I * (η:ℂ)))]
    rw [show -(euS α * (-(Complex.I * (η:ℂ)))) = -(euT α η) from by
      rw [euT_eq_neg_mul]; ring]
    try ring
  have htr1 : Eu σ α (Complex.I*(η:ℂ)) - Eu σ α (-(Complex.I*(η:ℂ)))
      = 2*Complex.I*(η:ℂ)*(u₀/euPsi α - 1)
        + 2*u₀*(Complex.sinh (euT α η) - euT α η)/(1 - Complex.exp (euS α)) := by
    rw [hE1, hE2]
    exact eu_center_diff_algebra hσ hu₀_ne hs_ne hηc heq.symm rfl euT_eq_neg_mul
  have htr2 : Eu σ α (Complex.I*(η:ℂ)) + Eu σ α (-(Complex.I*(η:ℂ)))
      = 2*(Complex.cosh (euT α η) - 1)/σ := by
    rw [hE1, hE2]
    exact eu_center_sum_algebra hσ hu₀_ne hs_ne hηc heq.symm rfl euT_eq_neg_mul
  -- ψ estimates
  have hψc : ‖euPsi α - 1‖ ≤ (5001/10000)*‖euS α‖ := euPsi_sub_one_le hα hS6400
  have hψlb : (9999:ℝ)/10000 ≤ ‖euPsi α‖ := by
    have h1 : (1:ℝ) - ‖euPsi α‖ ≤ ‖euPsi α - 1‖ := by
      simpa [norm_sub_rev] using norm_sub_norm_le (1:ℂ) (euPsi α)
    have h3 : (5001/10000) * ‖euS α‖ ≤ (5001/10000) * (1/6400) :=
      mul_le_mul_of_nonneg_left hS6400 (by norm_num)
    linarith
  have hψne : euPsi α ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hψlb
    norm_num at hψlb
  have hratio : ‖u₀/euPsi α - 1‖ ≤ 1060/1000000 := by
    have hnum : ‖u₀ - euPsi α‖ ≤ 1/1024 + (5001/10000)*‖euS α‖ := by
      rw [show u₀ - euPsi α = (u₀ - 1) + (1 - euPsi α) from by ring]
      refine (norm_add_le _ _).trans ?_
      rw [norm_sub_rev (1:ℂ) (euPsi α)]
      linarith [hu₀, hψc]
    rw [div_sub_one hψne, Complex.norm_div, div_le_iff₀ (norm_pos_iff.mpr hψne)]
    nlinarith [hnum, hS6400, hψlb, hs0]
  have ht_norm : ‖euT α η‖ = ‖euS α‖ * η := by rw [norm_euT, norm_euS, abs_of_pos hη]
  have ht_le : ‖euT α η‖ ≤ 1/2 := by rw [ht_norm]; linarith
  have hD : (9999/10000)*‖euS α‖ ≤ ‖1 - Complex.exp (euS α)‖ := by
    have h' : (1:ℂ) - Complex.exp (euS α) = -(euS α) * euPsi α := by
      rw [euPsi]; field_simp; ring
    rw [h', norm_mul, norm_neg]
    calc (9999/10000)*‖euS α‖ = ‖euS α‖ * (9999/10000) := by ring
      _ ≤ ‖euS α‖ * ‖euPsi α‖ := mul_le_mul_of_nonneg_left hψlb (norm_nonneg _)
  have hDpos : 0 < ‖1 - Complex.exp (euS α)‖ := lt_of_lt_of_le (mul_pos (by norm_num) hs0) hD
  -- power bounds from `‖s‖η ≤ 1/64`
  have hp2 : (‖euS α‖*η)^2 ≤ (1/64)^2 := by nlinarith [hSle, hsη0]
  have hp3 : (‖euS α‖*η)^3 ≤ (1/64)^3 := by nlinarith [hSle, hsη0]
  have hp4 : (‖euS α‖*η)^4 ≤ (1/64)^4 := by nlinarith [hSle, hsη0]
  have hsq : ‖euS α‖^2 * η^3 ≤ η/4096 := by nlinarith [hp2, hη]
  have hsq2 : ‖euS α‖^4 * η^5 ≤ η/16777216 := by nlinarith [hp4, hη]
  -- Taylor bounds for the `sinh` and `cosh` factors, written in terms of `‖s‖` and `η`
  have hSshr : ‖Complex.sinh (euT α η) - euT α η‖
      ≤ ‖euS α‖^3*η^3/6 + ‖euS α‖^5*η^5/60 := by
    have h0 := norm_sinh_sub_id_sub_cube_le ht_le
    have hC : ‖Complex.sinh (euT α η) - euT α η‖ ≤ ‖euT α η‖^3/6 + ‖euT α η‖^5/60 := by
      calc ‖Complex.sinh (euT α η) - euT α η‖
          = ‖(Complex.sinh (euT α η) - euT α η - (euT α η)^3/6) + (euT α η)^3/6‖ := by ring_nf
        _ ≤ ‖Complex.sinh (euT α η) - euT α η - (euT α η)^3/6‖ + ‖(euT α η)^3/6‖ :=
            norm_add_le _ _
        _ ≤ ‖euT α η‖^3/6 + ‖euT α η‖^5/60 := by
            rw [Complex.norm_div, Complex.norm_pow]
            norm_num
            linarith [h0]
    calc ‖Complex.sinh (euT α η) - euT α η‖ ≤ ‖euT α η‖^3/6 + ‖euT α η‖^5/60 := hC
      _ = ‖euS α‖^3*η^3/6 + ‖euS α‖^5*η^5/60 := by rw [ht_norm]; ring
  have hCsh : ‖Complex.cosh (euT α η) - 1‖
      ≤ ‖euS α‖^2*η^2/2 + ‖euS α‖^4*η^4/24 + ‖euS α‖^5*η^5/60 := by
    calc ‖Complex.cosh (euT α η) - 1‖
        ≤ ‖euT α η‖^2/2 + ‖euT α η‖^4/24 + ‖euT α η‖^5/60 := norm_cosh_sub_one_le ht_le
      _ = ‖euS α‖^2*η^2/2 + ‖euS α‖^4*η^4/24 + ‖euS α‖^5*η^5/60 := by rw [ht_norm]; ring
  constructor
  · -- the difference of the two centre values
    rw [htr1]
    have he1 : ‖2*Complex.I*(η:ℂ)*(u₀/euPsi α - 1)‖ = 2*η*‖u₀/euPsi α - 1‖ := by
      have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
      have hI : ‖Complex.I‖ = 1 := Complex.norm_I
      have hη' : ‖(η:ℂ)‖ = η := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
      simp only [norm_mul, h2, hI, hη', mul_one]
    have he2 : ‖2*u₀*(Complex.sinh (euT α η) - euT α η)/(1 - Complex.exp (euS α))‖
        = 2*‖u₀‖*(‖Complex.sinh (euT α η) - euT α η‖/‖1 - Complex.exp (euS α)‖) := by
      rw [Complex.norm_div, norm_mul, norm_mul, Complex.norm_ofNat]
      ring
    have hbd : ‖2*Complex.I*(η:ℂ)*(u₀/euPsi α - 1)
          + 2*u₀*(Complex.sinh (euT α η) - euT α η)/(1 - Complex.exp (euS α))‖
        ≤ 2*η*‖u₀/euPsi α - 1‖
          + 2*‖u₀‖*(‖Complex.sinh (euT α η) - euT α η‖/‖1 - Complex.exp (euS α)‖) := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [he1, he2]
    refine hbd.trans ?_
    exact arith_diff_bound hη (norm_nonneg _) hDpos hSle hratio (norm_nonneg _) hu₀norm
      (norm_nonneg _) hSshr hD
  · -- the sum of the two centre values
    rw [htr2]
    have he3 : ‖2*(Complex.cosh (euT α η) - 1)/σ‖
        = 2*‖u₀‖*(‖Complex.cosh (euT α η) - 1‖/‖1 - Complex.exp (euS α)‖) := by
      rw [Complex.norm_div, norm_mul, Complex.norm_ofNat]
      have h1 : (2*‖Complex.cosh (euT α η) - 1‖)/‖σ‖
          = (2*‖Complex.cosh (euT α η) - 1‖)*(‖u₀‖/‖1 - Complex.exp (euS α)‖) := by
        rw [div_eq_mul_inv, ← norm_inv, hinv', Complex.norm_div]
      rw [h1]
      ring
    rw [he3]
    exact arith_sum_bound hη (norm_nonneg _) hDpos hSle (norm_nonneg _) hu₀norm
      (norm_nonneg _) hCsh hD
end

end Work.Pert
