import Mathlib
import Submission.Work.FIArea4.logSine_defs
import Submission.Work.FIArea4.logSine_psi_deriv
import Submission.Work.FIArea4.logSine_tau_bound

namespace Work.FIArea4

open scoped Topology
open MeasureTheory

noncomputable section

/-! ### The derivative of the mollified log-sine function

`ufun N α = -Ψ_N(1-cos α) - Ψ_N(1+cos α) + 2 log 2`, so

`deriv (ufun N) α = sin α · (Ψ_N'(1+cos α) - Ψ_N'(1-cos α))`
-/

/-- The derivative of `ufun N` (valid for `1 ≤ N`, when `Psi N` is `C^∞`). -/
lemma deriv_ufun (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    deriv (ufun N) α
      = Real.sin α * (deriv (Psi N) (1 + Real.cos α) - deriv (Psi N) (1 - Real.cos α)) := by
  have hPsi : Differentiable ℝ (Psi N) := (contDiff_Psi N hN).differentiable (by simp)
  have hd1 : deriv (fun α => Psi N (1 - Real.cos α)) α
      = deriv (Psi N) (1 - Real.cos α) * Real.sin α := by
    have hdg : deriv (fun α : ℝ => 1 - Real.cos α) α = Real.sin α := by
      rw [deriv_fun_sub (by fun_prop) (by fun_prop), Real.deriv_cos]; simp
    have h := deriv_comp α (hPsi (1 - Real.cos α))
      (by fun_prop : DifferentiableAt ℝ (fun α : ℝ => 1 - Real.cos α) α)
    rw [hdg] at h
    exact h
  have hd2 : deriv (fun α => Psi N (1 + Real.cos α)) α
      = deriv (Psi N) (1 + Real.cos α) * (-Real.sin α) := by
    have hdg : deriv (fun α : ℝ => 1 + Real.cos α) α = -Real.sin α := by
      rw [deriv_fun_add (by fun_prop) (by fun_prop), Real.deriv_cos]; simp
    have h := deriv_comp α (hPsi (1 + Real.cos α))
      (by fun_prop : DifferentiableAt ℝ (fun α : ℝ => 1 + Real.cos α) α)
    rw [hdg] at h
    exact h
  have hA : HasDerivAt (fun α => Psi N (1 - Real.cos α))
      (deriv (Psi N) (1 - Real.cos α) * Real.sin α) α := by
    have h := (by fun_prop : DifferentiableAt ℝ (fun α => Psi N (1 - Real.cos α)) α).hasDerivAt
    rw [hd1] at h; exact h
  have hB : HasDerivAt (fun α => Psi N (1 + Real.cos α))
      (deriv (Psi N) (1 + Real.cos α) * (-Real.sin α)) α := by
    have h := (by fun_prop : DifferentiableAt ℝ (fun α => Psi N (1 + Real.cos α)) α).hasDerivAt
    rw [hd2] at h; exact h
  have key : HasDerivAt
      (fun α => -Psi N (1 - Real.cos α) - Psi N (1 + Real.cos α) + 2 * Real.log 2)
      (-(deriv (Psi N) (1 - Real.cos α) * Real.sin α)
        - deriv (Psi N) (1 + Real.cos α) * (-Real.sin α)) α :=
    (hA.neg.sub hB).add_const _
  have hval : -(deriv (Psi N) (1 - Real.cos α) * Real.sin α)
        - deriv (Psi N) (1 + Real.cos α) * (-Real.sin α)
      = Real.sin α * (deriv (Psi N) (1 + Real.cos α) - deriv (Psi N) (1 - Real.cos α)) := by
    ring
  rw [hval] at key
  exact key.deriv

/-! ### Two elementary substitutions

Both reduce `∫_{-π}^{π} |sin α| φ(1 ∓ cos α) dα` to `2 ∫_0^2 φ(u) du`.
-/

/-- Substitution `u = 1 - cos α`. -/
lemma integral_abs_sin_mul_comp_one_sub_cos (φ : ℝ → ℝ) (hφ : Continuous φ) :
    ∫ α in (-Real.pi)..Real.pi, |Real.sin α| * φ (1 - Real.cos α) = 2 * ∫ u in (0:ℝ)..2, φ u := by
  set f : ℝ → ℝ := fun α => |Real.sin α| * φ (1 - Real.cos α) with hfdef
  have hcont : Continuous f := by rw [hfdef]; fun_prop
  have hsymm : ∫ α in (-Real.pi)..0, f α = ∫ α in (0:ℝ)..Real.pi, f α := by
    have h1 : ∀ x, f (-x) = f x := by
      intro x; rw [hfdef]; simp only [Real.cos_neg, abs_neg, Real.sin_neg]
    calc ∫ α in (-Real.pi)..0, f α = ∫ α in (-Real.pi)..0, f (-α) :=
          (intervalIntegral.integral_congr fun x _ => (h1 x).symm)
      _ = ∫ α in (0:ℝ)..Real.pi, f α := by
          simpa using intervalIntegral.integral_comp_neg (a := -Real.pi) (b := 0) f
  have hsin : ∫ α in (0:ℝ)..Real.pi, f α
      = ∫ α in (0:ℝ)..Real.pi, Real.sin α * φ (1 - Real.cos α) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi), Set.mem_Icc] at hx
    rw [hfdef]
    simp only
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2)]
  have hf1 : ∀ x ∈ Set.uIcc (0:ℝ) Real.pi,
      HasDerivAt (fun α : ℝ => 1 - Real.cos α) (Real.sin x) x := by
    intro x _
    have h : HasDerivAt (fun α : ℝ => 1 - Real.cos α)
        (deriv (fun α : ℝ => 1 - Real.cos α) x) x :=
      (by fun_prop : DifferentiableAt ℝ (fun α : ℝ => 1 - Real.cos α) x).hasDerivAt
    have hd : deriv (fun α : ℝ => 1 - Real.cos α) x = Real.sin x := by
      rw [deriv_fun_sub (by fun_prop) (by fun_prop), Real.deriv_cos]; simp
    rwa [hd] at h
  have hsub : ∫ α in (0:ℝ)..Real.pi, Real.sin α * φ (1 - Real.cos α)
      = ∫ u in (0:ℝ)..2, φ u := by
    have h := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := Real.pi)
        (f := fun α : ℝ => 1 - Real.cos α) (f' := fun α : ℝ => Real.sin α) (g := φ)
        hf1 (by fun_prop) hφ
    have hleft : ∫ x in (0:ℝ)..Real.pi, (φ ∘ fun α : ℝ => 1 - Real.cos α) x * Real.sin x
        = ∫ α in (0:ℝ)..Real.pi, Real.sin α * φ (1 - Real.cos α) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp [Function.comp_def, mul_comm]
    rw [hleft] at h
    have hright : ∫ x in (1 - Real.cos 0)..(1 - Real.cos Real.pi), φ x
        = ∫ u in (0:ℝ)..2, φ u := by
      norm_num [Real.cos_zero, Real.cos_pi]
    rw [hright] at h
    exact h
  have hii1 : IntervalIntegrable f volume (-Real.pi) 0 := hcont.intervalIntegrable _ _
  have hii2 : IntervalIntegrable f volume 0 Real.pi := hcont.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hii1 hii2, hsymm, hsin, hsub]
  ring

/-- Substitution `u = 1 + cos α`. -/
lemma integral_abs_sin_mul_comp_one_add_cos (φ : ℝ → ℝ) (hφ : Continuous φ) :
    ∫ α in (-Real.pi)..Real.pi, |Real.sin α| * φ (1 + Real.cos α) = 2 * ∫ u in (0:ℝ)..2, φ u := by
  set f : ℝ → ℝ := fun α => |Real.sin α| * φ (1 + Real.cos α) with hfdef
  have hcont : Continuous f := by rw [hfdef]; fun_prop
  have hsymm : ∫ α in (-Real.pi)..0, f α = ∫ α in (0:ℝ)..Real.pi, f α := by
    have h1 : ∀ x, f (-x) = f x := by
      intro x; rw [hfdef]; simp only [Real.cos_neg, abs_neg, Real.sin_neg]
    calc ∫ α in (-Real.pi)..0, f α = ∫ α in (-Real.pi)..0, f (-α) :=
          (intervalIntegral.integral_congr fun x _ => (h1 x).symm)
      _ = ∫ α in (0:ℝ)..Real.pi, f α := by
          simpa using intervalIntegral.integral_comp_neg (a := -Real.pi) (b := 0) f
  have hsin : ∫ α in (0:ℝ)..Real.pi, f α
      = ∫ α in (0:ℝ)..Real.pi, Real.sin α * φ (1 + Real.cos α) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi), Set.mem_Icc] at hx
    rw [hfdef]
    simp only
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2)]
  have hf1 : ∀ x ∈ Set.uIcc (0:ℝ) Real.pi,
      HasDerivAt (fun α : ℝ => 1 + Real.cos α) (-Real.sin x) x := by
    intro x _
    have h : HasDerivAt (fun α : ℝ => 1 + Real.cos α)
        (deriv (fun α : ℝ => 1 + Real.cos α) x) x :=
      (by fun_prop : DifferentiableAt ℝ (fun α : ℝ => 1 + Real.cos α) x).hasDerivAt
    have hd : deriv (fun α : ℝ => 1 + Real.cos α) x = -Real.sin x := by
      rw [deriv_fun_add (by fun_prop) (by fun_prop), Real.deriv_cos]; simp
    rwa [hd] at h
  have hsub : ∫ α in (0:ℝ)..Real.pi, Real.sin α * φ (1 + Real.cos α)
      = ∫ u in (0:ℝ)..2, φ u := by
    have h := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := Real.pi)
        (f := fun α : ℝ => 1 + Real.cos α) (f' := fun α : ℝ => -Real.sin α) (g := φ)
        hf1 (by fun_prop) hφ
    have hL : ∫ x in (0:ℝ)..Real.pi, (φ ∘ fun α : ℝ => 1 + Real.cos α) x * (-Real.sin x)
        = -∫ α in (0:ℝ)..Real.pi, Real.sin α * φ (1 + Real.cos α) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x _
      simp only [Function.comp_def]
      ring
    rw [hL] at h
    have hR : ∫ x in (1 + Real.cos 0)..(1 + Real.cos Real.pi), φ x = -∫ u in (0:ℝ)..2, φ u := by
      rw [Real.cos_zero, Real.cos_pi]
      norm_num
      rw [intervalIntegral.integral_symm]
    rw [hR] at h
    linarith [h]
  have hii1 : IntervalIntegrable f volume (-Real.pi) 0 := hcont.intervalIntegrable _ _
  have hii2 : IntervalIntegrable f volume 0 Real.pi := hcont.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hii1 hii2, hsymm, hsin, hsub]
  ring

/-! ### The `L¹` bound `∫_0^2 |Ψ_N'| ≤ C log N` -/

/-- `∫_0^2 |Ψ_N'(u)| du ≤ (24K+1) log N`, where `K ≥ 1` bounds `|τ'|` and `|τ''|`.

The integral splits at the two transition thresholds `1/(2N²)` and `2/N²`: on
`[0, 1/(2N²)]` and `[1/(2N²), 2/N²]` the derivative is bounded by `4K N²(log N + 1)`
(vanishing below the window), giving `2K(log N + 1)` and `6K(log N + 1)`, while on
`[2/N², 2]` it equals `1/(2u)`, whose integral is `log N`. -/
lemma integral_abs_deriv_Psi_le (N : ℕ) (hN : 2 ≤ N) (K : ℝ) (hK : 1 ≤ K)
    (hK1 : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ K)
    (hK2 : ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ K) :
    ∫ u in (0:ℝ)..2, |deriv (Psi N) u| ≤ (24*K+1) * Real.log N := by
  obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := logSine_psi_deriv N hN K hK hK1 hK2
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hNpos : (0:ℝ) < N := by positivity
  have hB : (0:ℝ) < (N:ℝ)^2 := by positivity
  have hcont : Continuous fun u : ℝ => |deriv (Psi N) u| :=
    ((contDiff_Psi N hN1).continuous_deriv (by simp)).abs
  have ha2 : (1:ℝ)/(2*(N:ℝ)^2) ≤ 2/(N:ℝ)^2 := by
    have h1 : (1:ℝ)/(2*(N:ℝ)^2) = (1/2) * (1/(N:ℝ)^2) := by ring
    have h2 : (2:ℝ)/(N:ℝ)^2 = 2 * (1/(N:ℝ)^2) := by ring
    rw [h1, h2]
    have : (0:ℝ) ≤ 1/(N:ℝ)^2 := by positivity
    nlinarith
  have hr1 : ∫ u in (0:ℝ)..(1/(2*(N:ℝ)^2)), |deriv (Psi N) u| ≤ 2*K*(Real.log N+1) := by
    have hmain := intervalIntegral.integral_mono_on
        (show (0:ℝ) ≤ 1/(2*(N:ℝ)^2) by positivity)
        (hcont.intervalIntegrable _ _)
        (intervalIntegrable_const (c := 4*K*(N:ℝ)^2*(Real.log N+1)) (μ := volume)
          (a := (0:ℝ)) (b := 1/(2*(N:ℝ)^2)))
        (fun x hx => by
          rw [Set.mem_Icc] at hx
          rcases lt_or_eq_of_le hx.2 with hlt | heq
          · rw [hp3 x hlt]; simp only [abs_zero]; positivity
          · subst heq
            exact (hp5 _ le_rfl ha2).1)
    rw [intervalIntegral.integral_const] at hmain
    rw [smul_eq_mul] at hmain
    refine le_trans hmain (le_of_eq ?_)
    field_simp
    ring
  have hr2 : ∫ u in (1/(2*(N:ℝ)^2))..(2/(N:ℝ)^2), |deriv (Psi N) u| ≤ 6*K*(Real.log N+1) := by
    have hmain := intervalIntegral.integral_mono_on ha2
        (hcont.intervalIntegrable _ _)
        (intervalIntegrable_const (c := 4*K*(N:ℝ)^2*(Real.log N+1)) (μ := volume)
          (a := 1/(2*(N:ℝ)^2)) (b := 2/(N:ℝ)^2))
        (fun x hx => by
          rw [Set.mem_Icc] at hx
          exact (hp5 x hx.1 hx.2).1)
    rw [intervalIntegral.integral_const] at hmain
    rw [smul_eq_mul] at hmain
    refine le_trans hmain (le_of_eq ?_)
    field_simp
    ring
  have hr3 : ∫ u in (2/(N:ℝ)^2)..(2:ℝ), |deriv (Psi N) u| ≤ Real.log N := by
    have hle : 2/(N:ℝ)^2 ≤ 2 := by
      rw [div_le_iff₀ hB]
      have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      nlinarith
    have hcongr : ∫ u in (2/(N:ℝ)^2)..(2:ℝ), |deriv (Psi N) u|
        = ∫ u in (2/(N:ℝ)^2)..(2:ℝ), (1:ℝ)/(2*u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hle, Set.mem_Icc] at hu
      show |deriv (Psi N) u| = (1:ℝ)/(2*u)
      rw [hp1 u hu.1]
      have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu.1
      rw [abs_of_pos (by positivity)]
    rw [hcongr]
    have h2 : ∫ u in (2/(N:ℝ)^2)..(2:ℝ), (1:ℝ)/(2*u) = Real.log N := by
      have hstep : ∫ u in (2/(N:ℝ)^2)..(2:ℝ), (1:ℝ)/(2*u)
          = (1/2) * ∫ u in (2/(N:ℝ)^2)..(2:ℝ), (1:ℝ)/u := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro u _
        ring
      rw [hstep, integral_one_div_of_pos (by positivity) (by norm_num)]
      have hq : 2/(2/(N:ℝ)^2) = (N:ℝ)^2 := by field_simp
      rw [hq, Real.log_pow]
      ring
    exact le_of_eq h2
  have hsplit1 : ∫ u in (0:ℝ)..(2/(N:ℝ)^2), |deriv (Psi N) u|
      = (∫ u in (0:ℝ)..(1/(2*(N:ℝ)^2)), |deriv (Psi N) u|)
        + ∫ u in (1/(2*(N:ℝ)^2))..(2/(N:ℝ)^2), |deriv (Psi N) u| :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)).symm
  have hsplit2 : ∫ u in (0:ℝ)..(2:ℝ), |deriv (Psi N) u|
      = (∫ u in (0:ℝ)..(2/(N:ℝ)^2), |deriv (Psi N) u|)
        + ∫ u in (2/(N:ℝ)^2)..(2:ℝ), |deriv (Psi N) u| :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)).symm
  have hlog : (1/2:ℝ) ≤ Real.log N := by
    have h2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    linarith [Real.log_two_gt_d9]
  rw [hsplit2, hsplit1]
  nlinarith [hr1, hr2, hr3, hlog, hK]

/-- **`L¹` bound for `u_N'(α)`.**  `u_N = ufun N = -Ψ_N(1-cos α) - Ψ_N(1+cos α) + 2 log 2`
(`Work.FIArea4.logSine_defs`), and the claim is `∫_{-π}^{π} |u_N'(α)| dα ≪ log N`.

Hints: `deriv (ufun N) α = -Ψ_N'(1-cos α)·sin α + Ψ_N'(1+cos α)·sin α`, so
`|deriv (ufun N) α| ≤ |sin α|·(|Ψ_N'(1-cos α)| + |Ψ_N'(1+cos α)|)`.  For `α` with `1-cos α ≥ 2/N²`
one has `|Ψ_N'(1-cos α)| = 1/(2(1-cos α))` (`logSine_psi_deriv`), and with
`1 - cos x ≥ (43/96)x²` (`Work.FIArea4.one_sub_cos_ge`) and `|sin α| ≤ |α|` this is `≲ 1/|α|`,
integrable to `≲ log N` on `2/N ≤ |α| ≤ 1`.  The `Ψ_N'(1+cos α)` term has a *second* transition
window near `α = π` (`1 + cos α ≥ 2/N²` fails there), contributing another `O(log N)`; treat it by
the substitution `β = π - α`, where `1 + cos α = 1 - cos β` and `|sin α| = |sin β|`.  On
`|α| ≤ 2/N` (resp. `|π - α| ≤ 2/N`) use `|Ψ_N'(y)| ≤ 4K N²(1+log N)` for `y ≤ 2/N²` together with
`|sin α| ≤ |α|`.  `logSine_elem_integrals` supplies `∫_{2/N} dx/x ≤ log N`. -/
theorem logSine_integral_deriv :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ∫ α in (-Real.pi)..Real.pi, |deriv (ufun N) α| ≤ C * Real.log N := by
  obtain ⟨⟨K0, hK0pos, hK0bd⟩, -, -⟩ := logSine_tau_bound
  refine ⟨4 * (24 * max K0 1 + 1), by positivity, fun N hN => ?_⟩
  set K : ℝ := max K0 1 with hKdef
  have hK1 : 1 ≤ K := le_max_right _ _
  have hKb1 : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ K :=
    fun x => (hK0bd x).1.trans (le_max_left _ _)
  have hKb2 : ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ K :=
    fun x => (hK0bd x).2.trans (le_max_left _ _)
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hφcont : Continuous (fun u : ℝ => |deriv (Psi N) u|) :=
    ((contDiff_Psi N hN1).continuous_deriv (by simp)).abs
  have hI : ∫ u in (0:ℝ)..2, |deriv (Psi N) u| ≤ (24*K+1) * Real.log N :=
    integral_abs_deriv_Psi_le N hN K hK1 hKb1 hKb2
  have hsub1 : ∫ α in (-Real.pi)..Real.pi, |Real.sin α| * |deriv (Psi N) (1 - Real.cos α)|
      = 2 * ∫ u in (0:ℝ)..2, |deriv (Psi N) u| :=
    integral_abs_sin_mul_comp_one_sub_cos (fun u : ℝ => |deriv (Psi N) u|) hφcont
  have hsub2 : ∫ α in (-Real.pi)..Real.pi, |Real.sin α| * |deriv (Psi N) (1 + Real.cos α)|
      = 2 * ∫ u in (0:ℝ)..2, |deriv (Psi N) u| :=
    integral_abs_sin_mul_comp_one_add_cos (fun u : ℝ => |deriv (Psi N) u|) hφcont
  have hcont_d : Continuous (deriv (ufun N)) := (contDiff_ufun N hN1).continuous_deriv (by simp)
  have hcontA : Continuous (fun α : ℝ => |Real.sin α| * |deriv (Psi N) (1 - Real.cos α)|) :=
    Real.continuous_sin.abs.mul (hφcont.comp (by fun_prop))
  have hcontB : Continuous (fun α : ℝ => |Real.sin α| * |deriv (Psi N) (1 + Real.cos α)|) :=
    Real.continuous_sin.abs.mul (hφcont.comp (by fun_prop))
  have hpt : ∀ α : ℝ, |deriv (ufun N) α| ≤ |Real.sin α| * |deriv (Psi N) (1 - Real.cos α)|
      + |Real.sin α| * |deriv (Psi N) (1 + Real.cos α)| := by
    intro α
    rw [deriv_ufun N hN1 α]
    calc |Real.sin α * (deriv (Psi N) (1 + Real.cos α) - deriv (Psi N) (1 - Real.cos α))|
        = |Real.sin α| * |deriv (Psi N) (1 + Real.cos α)
            - deriv (Psi N) (1 - Real.cos α)| := abs_mul _ _
      _ ≤ |Real.sin α| * (|deriv (Psi N) (1 + Real.cos α)|
            + |deriv (Psi N) (1 - Real.cos α)|) :=
          mul_le_mul_of_nonneg_left
            (by have h := abs_sub_le (deriv (Psi N) (1 + Real.cos α)) 0
                    (deriv (Psi N) (1 - Real.cos α)); simpa using h)
            (abs_nonneg _)
      _ = |Real.sin α| * |deriv (Psi N) (1 - Real.cos α)|
            + |Real.sin α| * |deriv (Psi N) (1 + Real.cos α)| := by ring
  rw [hKdef] at hI
  calc ∫ α in (-Real.pi)..Real.pi, |deriv (ufun N) α|
      ≤ ∫ α in (-Real.pi)..Real.pi, (|Real.sin α| * |deriv (Psi N) (1 - Real.cos α)|
          + |Real.sin α| * |deriv (Psi N) (1 + Real.cos α)|) :=
        intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
          (hcont_d.abs.intervalIntegrable _ _) ((hcontA.add hcontB).intervalIntegrable _ _)
          (fun x _ => hpt x)
    _ = (∫ α in (-Real.pi)..Real.pi, |Real.sin α| * |deriv (Psi N) (1 - Real.cos α)|)
        + (∫ α in (-Real.pi)..Real.pi, |Real.sin α| * |deriv (Psi N) (1 + Real.cos α)|) :=
        intervalIntegral.integral_add (hcontA.intervalIntegrable _ _)
          (hcontB.intervalIntegrable _ _)
    _ = (2 * ∫ u in (0:ℝ)..2, |deriv (Psi N) u|)
          + (2 * ∫ u in (0:ℝ)..2, |deriv (Psi N) u|) := by
        rw [hsub1, hsub2]
    _ = 4 * (∫ u in (0:ℝ)..2, |deriv (Psi N) u|) := by ring
    _ ≤ 4 * ((24 * max K0 1 + 1) * Real.log N) :=
        mul_le_mul_of_nonneg_left hI (by norm_num)
    _ = 4 * (24 * max K0 1 + 1) * Real.log N := by ring

end

end Work.FIArea4
