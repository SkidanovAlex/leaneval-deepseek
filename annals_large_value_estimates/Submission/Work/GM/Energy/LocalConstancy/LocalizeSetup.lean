import Mathlib
import Submission.Work.GM.Energy.Defs
import Submission.Work.GM.Energy.RLocal.Bump

/-!
# Setup for GM Lemma 11.3 (locality of a Dirichlet polynomial)

GM Lemma 11.3 says that a Dirichlet polynomial `Σ_{n∼N} a_n n^{it}` does not vary too fast: its
value at `t` is controlled by its average over `[t-K,t+K]`, up to `K^{-m}·Σ|a_n|`.

The engine is the exact identity `Σ_n a_n n^{it} = ∫ ψ̂(ξ) Σ_n a_n n^{i(t+ξ)} dξ` for a fixed
smooth bump `ψ` which equals `1` at `log n / 2π` for all `n ∈ [N,2N]`.

Because `n = N · (n/N)`, we may factor out the twist `N^{it}` and work with the *normalised*
polynomial `G` below, whose frequencies are `log (n/N) ∈ [0, log 2]`: this is a fixed interval,
independent of `N`, and it is exactly an interval on which the flat-top bump
`Work.GM.Energy.RLocal.psiBump` (equal to `1` on `[0,1]`, supported in `[-1/3,4/3]`) — already
endowed with its Fourier decay, integrability and inversion formula in
`Submission/Work/GM/Energy/RLocal/Bump.lean` — is equal to `1`.  Hence all the analytic
constants below are uniform in `N`.

This file collects the elementary facts about `G` and about the bump that the main argument uses.
-/

open Complex Finset MeasureTheory
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Energy.LocalConstancy.Loc

/-- The *normalised* Dirichlet polynomial `Σ_{n∈[N,2N]} a n (n/N)^{iu}`; its frequencies
`log (n/N)` lie in the fixed interval `[0, log 2]`. -/
noncomputable def G (N : ℕ) (a : ℕ → ℂ) (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc N (2 * N),
    a n * (Complex.ofReal ((n : ℝ) / (N : ℝ))) ^ (Complex.I * (u : ℂ))

/-- `(x:ℂ)^{iu} = exp (i u log x)` for `x > 0`. -/
lemma cpow_I_mul_eq_exp {x : ℝ} (hx : 0 < x) (u : ℝ) :
    (x : ℂ) ^ (Complex.I * (u : ℂ)) = Complex.exp (((u * Real.log x : ℝ)) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le]
  congr 1
  push_cast
  ring

/-- `‖(x:ℂ)^{iu}‖ = 1` for `x > 0`. -/
lemma norm_cpow_I_mul_eq_one {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ‖(x : ℂ) ^ (Complex.I * (u : ℂ))‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (Complex.I * (u : ℂ)).re = 0 := by simp
  rw [hre, Real.rpow_zero]

/-- `u ↦ (x:ℂ)^{iu}` is continuous for `x > 0`. -/
lemma continuous_cpow_I_mul {x : ℝ} (hx : 0 < x) :
    Continuous fun u : ℝ => (x : ℂ) ^ (Complex.I * (u : ℂ)) := by
  rw [show (fun u : ℝ => (x : ℂ) ^ (Complex.I * (u : ℂ)))
      = fun u : ℝ => Complex.exp (((u * Real.log x : ℝ)) * Complex.I) from
    funext fun u => cpow_I_mul_eq_exp hx u]
  fun_prop

/-- The normalised polynomial is continuous (as a function of `u`) for `N ≥ 1`. -/
lemma G_continuous {N : ℕ} (hN : 1 ≤ N) (a : ℕ → ℂ) : Continuous (G N a) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  unfold G
  refine continuous_finset_sum _ fun n hn => ?_
  have hn1 : 1 ≤ n := le_trans hN (Finset.mem_Icc.mp hn).1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn1
  exact Continuous.mul continuous_const (continuous_cpow_I_mul (div_pos hnpos hNpos))

/-- The trivial supremum bound `‖G u‖ ≤ Σ_n ‖a n‖`. -/
lemma G_norm_le {N : ℕ} (hN : 1 ≤ N) (a : ℕ → ℂ) (u : ℝ) :
    ‖G N a u‖ ≤ ∑ n ∈ Finset.Icc N (2 * N), ‖a n‖ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  unfold G
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := le_trans hN (Finset.mem_Icc.mp hn).1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn1
  rw [norm_mul, norm_cpow_I_mul_eq_one (div_pos hnpos hNpos) u, mul_one]

/-- The flat-top bump `psiBump` is `1` at `log (n/N) / (2π)` for `n ∈ [N,2N]`, `N ≥ 1`. -/
lemma psiBump_log_div_eq_one {n N : ℕ} (hN : 1 ≤ N) (hn : n ∈ Finset.Icc N (2 * N)) :
    Work.GM.Energy.RLocal.psiBump (Real.log ((n : ℝ) / (N : ℝ)) / (2 * Real.pi)) = 1 := by
  apply Work.GM.Energy.RLocal.psiBump_eq_one
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hn1 : 1 ≤ n := le_trans hN (Finset.mem_Icc.mp hn).1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn1
  have hle : (n : ℝ) ≤ 2 * N := by
    have := (Finset.mem_Icc.mp hn).2
    exact_mod_cast this
  have hNle : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hx1 : (1 : ℝ) ≤ (n : ℝ) / (N : ℝ) := by
    rw [le_div_iff₀ hNpos]; linarith
  have hx2 : (n : ℝ) / (N : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hNpos]; linarith
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  constructor
  · have hlog := Real.log_nonneg hx1
    positivity
  · have hlog2 : Real.log ((n : ℝ) / (N : ℝ)) ≤ 1 := by
      have h1 : Real.log ((n : ℝ) / (N : ℝ)) ≤ Real.log 2 :=
        Real.log_le_log (by linarith) hx2
      have h2 : Real.log 2 ≤ 1 := by
        have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        norm_num at h3
        linarith
      linarith
    have h1 : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    rw [div_le_one hpi]
    linarith

/-- A uniform bound for the Fourier transform of the flat-top bump. -/
theorem PsiBump_fourier_norm_le :
    ∃ M : ℝ, 0 < M ∧ ∀ ξ : ℝ, ‖𝓕 Work.GM.Energy.RLocal.PsiBump ξ‖ ≤ M := by
  obtain ⟨C, hC0, hC⟩ := Work.GM.Energy.RLocal.PsiBump_fourier_decay 2
  set I := ∫ x, ‖Work.GM.Energy.RLocal.PsiBump x‖ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => norm_nonneg _
  refine ⟨max I C + 1, by positivity, fun ξ => ?_⟩
  rcases le_or_gt |ξ| 1 with h | h
  · have h1 := Work.GM.Energy.RLocal.PsiBump_fourier_le_integral ξ
    have h2 : I ≤ max I C + 1 := by linarith [le_max_left I C]
    rw [hI] at h2
    linarith
  · have hξ : ξ ≠ 0 := by
      intro h0; rw [h0, abs_zero] at h; norm_num at h
    have h1 := hC ξ hξ
    have h2 : C / |ξ| ^ 2 ≤ C := by
      have h4 : (1 : ℝ) < |ξ| ^ 2 := by nlinarith [abs_nonneg ξ, h]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h3 : C ≤ max I C + 1 := by linarith [le_max_right I C]
    linarith

end Work.GM.Energy.LocalConstancy.Loc
