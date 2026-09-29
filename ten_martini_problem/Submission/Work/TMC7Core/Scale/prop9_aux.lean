import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Lyap.lyap_nonneg
import Submission.Work.TMC7Core.Lyap.lyap_eq_lim
import Submission.Work.TMC7Core.Lyap.lyap_upperSemicontinuous
import Submission.Work.TMC7Core.Lyap.subadditive_integral_log_frob

/-!
# Elementary order structure of the finite-scale Lyapunov averages

Supporting facts for the Bourgain--Jitomirskaya scale induction (Prop. 9).

The Lyapunov exponent `lyap` is the infimum of the quantities
`lyapAvg α lam E (n+1)`; the function `n ↦ ∫₀¹ log ‖A_n(x)‖_F dx` is subadditive, which makes
`n ↦ lyapAvg α lam E n` non-increasing along divisibility and gives the elementary two-sided
bound `|lyap + L_n - 2 L_{2n}| ≤ L_n - lyap`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

set_option maxHeartbeats 800000

noncomputable section

namespace Work.TMC7Core.Scale

open Work.TMC7Core Work.TMC7Core.Lyap

/-- Each finite-scale average at scale `n+1` is nonnegative. -/
theorem lyapAvg_nonneg' (α lam : ℝ) (E : ℂ) (n : ℕ) : 0 ≤ lyapAvg α lam E (n+1) := by
  have h := @integral_log_frob_iterC_nonneg α lam E n
  simpa [lyapAvg, Nat.cast_add, Nat.cast_one] using h

/-- `lyap` is the infimum of the finite-scale averages, hence `≤ lyapAvg · N` for `N ≥ 1`. -/
theorem lyap_le_lyapAvg (α lam : ℝ) (E : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    lyap α lam E ≤ lyapAvg α lam E N := by
  rw [lyap_eq_iInf_lyapAvg]
  have hbdd : BddBelow (Set.range fun k : ℕ => lyapAvg α lam E (k + 1)) := ⟨0, by
    rintro y ⟨k, rfl⟩; exact lyapAvg_nonneg' α lam E k⟩
  simpa [Nat.sub_add_cancel hN] using ciInf_le hbdd (N - 1)

/-- `L_{2N} ≤ L_N`: subadditivity of `n ↦ ∫₀¹ log‖A_n‖_F`. -/
theorem lyapAvg_two_le (α lam : ℝ) (E : ℂ) (N : ℕ) :
    lyapAvg α lam E (2 * N) ≤ lyapAvg α lam E N := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; norm_num
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have h := subadditive_integral_log_frob α lam E N N
  simp only [lyapAvg]
  have h2N : (2 * N : ℕ) = N + N := by ring
  rw [h2N]
  have hcast : ((N+N : ℕ) : ℝ) = 2 * (N:ℝ) := by push_cast; ring
  rw [hcast]
  rw [div_le_iff₀ (by positivity)]
  have hkey : (∫ x in (0:ℝ)..1, Real.log (frob (iterC α lam E N x))) / (N:ℝ) * (2 * (N:ℝ))
      = 2 * (∫ x in (0:ℝ)..1, Real.log (frob (iterC α lam E N x))) := by
    field_simp
  rw [hkey]
  linarith [h]

/-- `|lyap + L_N - 2 L_{2N}| ≤ L_N - lyap` for `N ≥ 1` (from `lyap ≤ L_{2N} ≤ L_N`). -/
theorem abs_lyap_expr_le (α lam : ℝ) (E : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    |lyap α lam E + lyapAvg α lam E N - 2 * lyapAvg α lam E (2 * N)|
      ≤ lyapAvg α lam E N - lyap α lam E := by
  have h1 : lyap α lam E ≤ lyapAvg α lam E (2*N) := lyap_le_lyapAvg α lam E (by omega)
  have h2 : lyapAvg α lam E (2*N) ≤ lyapAvg α lam E N := lyapAvg_two_le α lam E N
  have h3 : lyap α lam E ≤ lyapAvg α lam E N := lyap_le_lyapAvg α lam E hN
  rw [abs_le]; constructor <;> linarith

/-- Subadditivity consequence: `u (k*n) ≤ k * u n` for `k ≥ 1`, `u n = ∫₀¹ log‖A_n‖_F`. -/
theorem integral_subadditive_mul (α lam : ℝ) (E : ℂ) (n : ℕ) :
    ∀ k : ℕ, 1 ≤ k → (∫ x in (0:ℝ)..1, Real.log (frob (iterC α lam E (n*k) x)))
      ≤ (k:ℝ) * (∫ x in (0:ℝ)..1, Real.log (frob (iterC α lam E n x))) := by
  intro k
  induction k with
  | zero => intro h; exact absurd h (by norm_num)
  | succ k ih =>
    intro _
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    have h := subadditive_integral_log_frob α lam E (n*k) n
    have heq : (n*(k+1)) = n*k + n := by ring
    rw [heq]
    have ih' := ih hk
    push_cast
    linarith [h, ih']

/-- `L_{N} ≤ L_n` whenever `n ∣ N` and `n ≥ 1` (divisor monotonicity). -/
theorem lyapAvg_mono_of_dvd (α lam : ℝ) (E : ℂ) {n N : ℕ} (hn : 1 ≤ n) (hdvd : n ∣ N) :
    lyapAvg α lam E N ≤ lyapAvg α lam E n := by
  obtain ⟨k, rfl⟩ := hdvd
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hn1 : n = (n-1)+1 := by omega
    rw [Nat.mul_zero, hn1]
    simpa [lyapAvg] using lyapAvg_nonneg' α lam E (n-1)
  have hk1 : 1 ≤ k := hk
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have h := integral_subadditive_mul α lam E n k hk1
  simp only [lyapAvg]
  have hcast : ((n*k : ℕ) : ℝ) = (k:ℝ)*(n:ℝ) := by push_cast; ring
  rw [hcast, div_le_iff₀ (by positivity)]
  have hkey : (∫ x in (0:ℝ)..1, Real.log (frob (iterC α lam E n x))) / (n:ℝ) * ((k:ℝ)*(n:ℝ))
      = (k:ℝ) * (∫ x in (0:ℝ)..1, Real.log (frob (iterC α lam E n x))) := by
    field_simp
  rw [hkey]; exact h

/-- The finite-scale averages converge to `lyap` along `atTop`. -/
theorem tendsto_lyapAvg (α lam : ℝ) (E : ℂ) :
    Filter.Tendsto (fun n : ℕ => lyapAvg α lam E n) Filter.atTop (nhds (lyap α lam E)) := by
  rw [← Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => lyapAvg α lam E n) (k := 1)]
  refine (lyap_eq_lim α lam E).congr' ?_
  filter_upwards with n
  simp [lyapAvg, Nat.cast_add, Nat.cast_one]

/-- **Chain limit.**  If the finite-scale averages are approximately constant along an
increasing sequence of scales `Nf`, with successive increments bounded by a geometric
sequence `K ρ^s` (`0 ≤ ρ < 1`), then the value at the first scale is within `K/(1-ρ)` of
the limit `lyap`. -/
theorem chain_limit (α lam : ℝ) (E : ℂ) (Nf : ℕ → ℕ) (K ρ : ℝ)
    (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hNmono : StrictMono Nf)
    (hstep : ∀ s, |lyapAvg α lam E (Nf (s+1)) - lyapAvg α lam E (Nf s)| ≤ K * ρ^s) :
    |lyap α lam E - lyapAvg α lam E (Nf 0)| ≤ K / (1 - ρ) := by
  have hlim : Filter.Tendsto (fun s : ℕ => lyapAvg α lam E (Nf s)) Filter.atTop
      (nhds (lyap α lam E)) :=
    (tendsto_lyapAvg α lam E).comp hNmono.tendsto_atTop
  -- telescoping bound
  have htele : ∀ m : ℕ, |lyapAvg α lam E (Nf m) - lyapAvg α lam E (Nf 0)| ≤ K / (1 - ρ) := by
    intro m
    have h1 : lyapAvg α lam E (Nf m) - lyapAvg α lam E (Nf 0)
        = ∑ s ∈ Finset.range m, (lyapAvg α lam E (Nf (s+1)) - lyapAvg α lam E (Nf s)) := by
      rw [Finset.sum_range_sub (fun s => lyapAvg α lam E (Nf s)) m]
    rw [h1]
    calc |∑ s ∈ Finset.range m, (lyapAvg α lam E (Nf (s+1)) - lyapAvg α lam E (Nf s))|
        ≤ ∑ s ∈ Finset.range m, |lyapAvg α lam E (Nf (s+1)) - lyapAvg α lam E (Nf s)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ Finset.range m, K * ρ^s := Finset.sum_le_sum (fun s _ => hstep s)
      _ = K * ∑ s ∈ Finset.range m, ρ^s := by rw [Finset.mul_sum]
      _ ≤ K * (1 / (1 - ρ)) := by
          apply mul_le_mul_of_nonneg_left _ hK
          have hpos : (0:ℝ) < 1 - ρ := by linarith
          have hmul : (∑ s ∈ Finset.range m, ρ^s) * (1 - ρ) = 1 - ρ^m := by
            have h := geom_sum_mul ρ m
            nlinarith [h]
          rw [le_div_iff₀ hpos, hmul]
          linarith [pow_nonneg hρ0 m]
      _ = K / (1 - ρ) := by ring
  -- pass to the limit
  have hlim2 : Filter.Tendsto (fun m : ℕ => |lyapAvg α lam E (Nf m) - lyapAvg α lam E (Nf 0)|)
      Filter.atTop (nhds |lyap α lam E - lyapAvg α lam E (Nf 0)|) :=
    (hlim.sub tendsto_const_nhds).abs
  have := le_of_tendsto_of_tendsto' hlim2 tendsto_const_nhds (fun m => htele m)
  simpa using this


/-- General subadditivity bound for the un-averaged quantity `u n = ∫₀¹ log‖A_n‖`:
`u (a*n + b) ≤ a * u n + u b`. -/
theorem integral_log_frob_add_mul (α lam : ℝ) (E : ℂ) (n : ℕ) :
    ∀ a b : ℕ, (∫ x in (0:ℝ)..1, Real.log (frob (iterC α lam E (a*n + b) x)))
      ≤ (a:ℝ) * (∫ x in (0:ℝ)..1, Real.log (frob (iterC α lam E n x)))
        + (∫ x in (0:ℝ)..1, Real.log (frob (iterC α lam E b x))) := by
  intro a
  induction a with
  | zero => intro b; simp
  | succ a ih =>
    intro b
    have h := subadditive_integral_log_frob α lam E (a*n + b) n
    have heq : ((a+1)*n + b) = (a*n + b) + n := by ring
    rw [heq]
    have ih' := ih b
    push_cast
    linarith [h, ih']

/-- **Subadditivity lower bound on `lyapAvg`.**  If `N = q n + r` with `r < n`, then
`q n * L_n ≥ u_N - u_r`, hence `L_n ≥ (u_N - u_r)/N`; in particular a large value `L_N`
forces a lower bound for smaller scales.  Concretely
`L_n ≥ L_N - (n/N) * C₁` whenever `u_r ≤ n * C₁`. -/
theorem lyapAvg_lower_bound (α lam : ℝ) (E : ℂ) {n N r q : ℕ} (hNr : N = q * n + r) :
    (∫ x in (0:ℝ)..1, Real.log (frob (iterC α lam E N x)))
        - (∫ x in (0:ℝ)..1, Real.log (frob (iterC α lam E r x)))
      ≤ (q:ℝ) * (n:ℝ) * lyapAvg α lam E n := by
  have h := integral_log_frob_add_mul α lam E n q r
  rw [← hNr] at h
  simp only [lyapAvg]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; rw [hNr]; simp
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hkey : (q:ℝ) * (n:ℝ) * ((∫ x in (0:ℝ)..1, Real.log (frob (iterC α lam E n x))) / (n:ℝ))
      = (q:ℝ) * (∫ x in (0:ℝ)..1, Real.log (frob (iterC α lam E n x))) := by
    field_simp
  rw [hkey]
  linarith [h]


end Work.TMC7Core.Scale
