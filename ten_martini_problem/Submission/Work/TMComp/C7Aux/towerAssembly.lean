import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.intervalIntegrable_log_frob
import Submission.Work.TMC7Core.LDT
import Submission.Work.TMC7Core.Lyap.lyap_eq_lim
import Submission.Work.TMC7Core.Scale.prop9_aux
import Submission.Work.TMC7Core.Scale.scale_step_avg
import Submission.Work.TMC7Core.Scale.pairing_step

/-!
# The scale tower of [BJ] Lemma 7 with growing approximants, and its passage to `lyap`

[Bourgain--Jitomirskaya, *Continuity of the Lyapunov exponent for quasiperiodic operators
with analytic potential*, J. Statist. Phys. 108 (2002), Lemmas 6--8 and §4] prove the
continuity of `E ↦ L(E)` at a point where `L > 0` by walking up a *tower of scales*
`N₀ | N₁ | N₂ | ⋯` and letting the tower's length go to infinity.  This file contains the
*assembly* of that tower: given, at every stage `s`,

* a scale `N s` and a multiplier `m s` with `N (s+1) = m s * N s`, `m s ≥ 3`,
* the [BJ] Lemma 6 relation `|L_{N_{s+1}} + L_{N_s} − 2 L_{2N_s}| ≤ ε₁ s` at stage `s`,
* the pairing-defect contraction `|D_{s+1} − D_s/m_s| ≤ ε₂ s`, `D_s = L_{N_s} − L_{2N_s}`,

with the error bounds `ε₁, ε₂` *summable*, the telescoped difference

`|lyap + L_{N₀} − 2 L_{2N₀}|` at the *base* scale of the tower is bounded by `Σ ε₁ + 4 Σ ε₂`
together with the single `1/m₀` remainder `6 |D₀| / m₀`.

The mathematical content is the cancellation observed in [BJ]: writing `c_s = 2 L_{2N_s} −
L_{N_s}`, the defect recursion `D_{s+1} = D_s/m_s + ψ_s` makes `D_s = D₀/M_s + O(Σε₂)` with
`M_s = m₀⋯m_{s−1}`, and the two large terms `2D₀(1 − Σ_{s}1/M_s)` and `−2Σ_s D_s` cancel to
leading order, leaving the accumulated errors and the `1/m₀` remainder.  Without that
cancellation the naive bound for the base-scale difference is `2|D₀|`, far too large.

Because the errors must be *summable*, the tower's scales have to come with approximants whose
denominators grow (`q_s → ∞`), so that `ε_s ≈ e^{−cκq_s/2}` decays: this is the "growing
approximants" requirement of the construction ([BJ] §4: Case I uses the next convergent,
Case II (Lemma 8) bridges the gap).  A tower run with a *fixed* approximant has `Σ_s ε_s = ∞`,
and no such bound can be extracted from it.

`tower_le` takes the per-stage relations as hypotheses (Case I supplies them through
`AvgStep.scale_step_avg` / `pairing_step`, Case II through [BJ] Lemma 8).
-/

open MeasureTheory Filter Topology Set
open Work.TMC7Core

noncomputable section

namespace Work.TMComp.C7Aux

/-! ## 1. The product of the multipliers -/

/-- `Pmul m s = m 0 · m 1 ⋯ m (s-1)` (empty product at `s = 0`).  This is the ratio
`N s / N 0` of the tower scales. -/
def Pmul (m : ℕ → ℕ) (s : ℕ) : ℕ := ∏ t ∈ Finset.range s, m t

@[simp] theorem Pmul_zero (m : ℕ → ℕ) : Pmul m 0 = 1 := by simp [Pmul]

theorem Pmul_succ (m : ℕ → ℕ) (s : ℕ) : Pmul m (s + 1) = Pmul m s * m s := by
  simp [Pmul, Finset.prod_range_succ]

theorem Pmul_pos {m : ℕ → ℕ} (hm : ∀ t, 1 ≤ m t) (s : ℕ) : 0 < Pmul m s :=
  Finset.prod_pos (fun t _ => lt_of_lt_of_le Nat.zero_lt_one (hm t))

theorem Pmul_cast_pos {m : ℕ → ℕ} (hm : ∀ t, 1 ≤ m t) (s : ℕ) : (0 : ℝ) < (Pmul m s : ℝ) := by
  exact_mod_cast Pmul_pos hm s

/-- `m 0 · 3^j ≤ m 0 ⋯ m j` when every multiplier is `≥ 3`. -/
theorem mul_pow_three_le_Pmul_succ {m : ℕ → ℕ} (h3 : ∀ t, 3 ≤ m t) (j : ℕ) :
    (m 0 : ℝ) * 3 ^ j ≤ (Pmul m (j + 1) : ℝ) := by
  have hm1 : ∀ t, 1 ≤ m t := fun t => le_trans (by norm_num) (h3 t)
  induction j with
  | zero => rw [Pmul_succ, Pmul_zero]; norm_num
  | succ j ih =>
    have hcast : (Pmul m (j + 1 + 1) : ℝ) = (Pmul m (j + 1) : ℝ) * (m (j + 1) : ℝ) := by
      rw [Pmul_succ]; push_cast; ring
    have hmj : (3 : ℝ) ≤ (m (j + 1) : ℝ) := by exact_mod_cast h3 (j + 1)
    have hpos : (0 : ℝ) ≤ (Pmul m (j + 1) : ℝ) := le_of_lt (Pmul_cast_pos hm1 (j + 1))
    calc (m 0 : ℝ) * 3 ^ (j + 1) = (m 0 : ℝ) * 3 ^ j * 3 := by ring
      _ ≤ (Pmul m (j + 1) : ℝ) * 3 := mul_le_mul_of_nonneg_right ih (by norm_num)
      _ ≤ (Pmul m (j + 1) : ℝ) * (m (j + 1) : ℝ) := mul_le_mul_of_nonneg_left hmj hpos
      _ = (Pmul m (j + 1 + 1) : ℝ) := hcast.symm

/-- `1/(m 0 ⋯ m j) ≤ (3/m 0)·(1/3)^{j+1}` when every multiplier is `≥ 3`. -/
theorem inv_Pmul_succ_le {m : ℕ → ℕ} (h3 : ∀ t, 3 ≤ m t) (j : ℕ) :
    (1 : ℝ) / (Pmul m (j + 1) : ℝ) ≤ (3 / (m 0 : ℝ)) * (1 / 3 : ℝ) ^ (j + 1) := by
  have hm1 : ∀ t, 1 ≤ m t := fun t => le_trans (by norm_num) (h3 t)
  have hm0 : (0 : ℝ) < (m 0 : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hm1 0)
  have h := mul_pow_three_le_Pmul_succ h3 j
  have hpos : (0 : ℝ) < (m 0 : ℝ) * 3 ^ j := by positivity
  have h1 : (1 : ℝ) / (Pmul m (j + 1) : ℝ) ≤ 1 / ((m 0 : ℝ) * 3 ^ j) :=
    one_div_le_one_div_of_le hpos h
  have h2 : (1 : ℝ) / ((m 0 : ℝ) * 3 ^ j) = (3 / (m 0 : ℝ)) * (1 / 3 : ℝ) ^ (j + 1) := by
    rw [div_pow, one_pow, div_mul_eq_mul_div]
    field_simp
    ring
  linarith [h1, h2]

/-! ## 2. Geometric bounds for the weights of the tower -/

/-- `Σ_{j<n} (1/3)^j ≤ 3/2`. -/
theorem geom_third_sum_le (n : ℕ) : ∑ j ∈ Finset.range n, (1 / 3 : ℝ) ^ j ≤ 3 / 2 := by
  have hinv : ∀ n, ∑ j ∈ Finset.range n, (1 / 3 : ℝ) ^ j ≤ 3 / 2 - (3 / 2) * (1 / 3 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h2 : (3 / 2 : ℝ) * (1 / 3 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) * (1 / 3 : ℝ) ^ n := by
        rw [pow_succ]; ring
      rw [h2] at *
      linarith [ih]
  have := hinv n
  have h : (0 : ℝ) ≤ (3 / 2) * (1 / 3 : ℝ) ^ n := by positivity
  linarith [this, h]

/-- The partial sum of the shifted weights `1/(m₀⋯m_j)` is at most `(3/2)/m₀`. -/
theorem sum_shifted_inv_Pmul_le {m : ℕ → ℕ} (h3 : ∀ t, 3 ≤ m t) (S : ℕ) :
    ∑ j ∈ Finset.range S, (1 : ℝ) / (Pmul m (j + 1) : ℝ) ≤ 3 / (2 * (m 0 : ℝ)) := by
  have hm1 : ∀ t, 1 ≤ m t := fun t => le_trans (by norm_num) (h3 t)
  have hm0 : (0 : ℝ) < (m 0 : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hm1 0)
  have h1 : ∀ j ∈ Finset.range S, (1 : ℝ) / (Pmul m (j + 1) : ℝ)
      ≤ (1 / (m 0 : ℝ)) * (1 / 3 : ℝ) ^ j := by
    intro j _
    have h := inv_Pmul_succ_le h3 j
    have h2 : (3 / (m 0 : ℝ)) * (1 / 3 : ℝ) ^ (j + 1) = (1 / (m 0 : ℝ)) * (1 / 3 : ℝ) ^ j := by
      rw [pow_succ]; ring
    linarith [h, h2]
  calc ∑ j ∈ Finset.range S, (1 : ℝ) / (Pmul m (j + 1) : ℝ)
      ≤ ∑ j ∈ Finset.range S, (1 / (m 0 : ℝ)) * (1 / 3 : ℝ) ^ j := Finset.sum_le_sum h1
    _ = (1 / (m 0 : ℝ)) * ∑ j ∈ Finset.range S, (1 / 3 : ℝ) ^ j := by rw [Finset.mul_sum]
    _ ≤ (1 / (m 0 : ℝ)) * (3 / 2) := by
        refine mul_le_mul_of_nonneg_left (geom_third_sum_le S) ?_
        positivity
    _ = 3 / (2 * (m 0 : ℝ)) := by ring

/-- Splitting the weight sum: `Σ_{s<S} 1/M_s = 1 + Σ_{j<S} 1/M_{j+1} − 1/M_S`. -/
theorem sum_inv_Pmul_eq (m : ℕ → ℕ) (hm : ∀ t, 1 ≤ m t) (S : ℕ) :
    ∑ s ∈ Finset.range S, (1 : ℝ) / (Pmul m s : ℝ)
      = 1 + (∑ j ∈ Finset.range S, (1 : ℝ) / (Pmul m (j + 1) : ℝ))
        - (1 : ℝ) / (Pmul m S : ℝ) := by
  induction S with
  | zero => simp [Pmul]
  | succ S ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

/-- The partial sum of the weights `1/(m₀⋯m_s)` is at most `1 + 3/m₀`, whenever every
multiplier is `≥ 3`.  This is the estimate that makes the leading `2D₀(1 − Σ_s 1/M_s)` term of
the telescoping small. -/
theorem sum_inv_Pmul_le {m : ℕ → ℕ} (h3 : ∀ t, 3 ≤ m t) (S : ℕ) :
    ∑ s ∈ Finset.range S, (1 : ℝ) / (Pmul m s : ℝ) ≤ 1 + 3 / (m 0 : ℝ) := by
  have hm1 : ∀ t, 1 ≤ m t := fun t => le_trans (by norm_num) (h3 t)
  have hm0 : (0 : ℝ) < (m 0 : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hm1 0)
  rw [sum_inv_Pmul_eq m hm1 S]
  have hV := sum_shifted_inv_Pmul_le h3 S
  have h1 : (0 : ℝ) ≤ (1 : ℝ) / (Pmul m S : ℝ) := by positivity
  have h2 : 3 / (2 * (m 0 : ℝ)) ≤ 3 / (m 0 : ℝ) := by
    have h2m : (0 : ℝ) < 2 * (m 0 : ℝ) := by positivity
    rw [div_le_iff₀ h2m]
    have hkey : 3 / (m 0 : ℝ) * (2 * (m 0 : ℝ)) = 6 := by
      field_simp
      norm_num
    rw [hkey]
    norm_num
  linarith [hV, h1, h2]

/-- The "tail weights" of the defect recursion: for every `u`, the weighted sum
`Σ_{s} [u < s] (m₀⋯m_u)/(m₀⋯m_s)` is at most `2`. -/
theorem sum_tail_weight_le {m : ℕ → ℕ} (h3 : ∀ t, 3 ≤ m t) (u S : ℕ) :
    ∑ j ∈ Finset.range S,
        (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0) ≤ 2 := by
  have hm1 : ∀ t, 1 ≤ m t := fun t => le_trans (by norm_num) (h3 t)
  have hm2 : ∀ t, 2 ≤ m t := fun t => le_trans (by norm_num) (h3 t)
  have hPpos : ∀ s, (0 : ℝ) < (Pmul m s : ℝ) := fun s => Pmul_cast_pos hm1 s
  have hzero : ∀ S, S ≤ u + 1 →
      ∑ j ∈ Finset.range S,
        (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0) = 0 := by
    intro S hS
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [if_neg]
    simp only [Finset.mem_range] at hj
    omega
  have hinv : ∀ d, ∑ j ∈ Finset.range (u + 1 + d),
        (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0)
      ≤ 2 - 2 * ((Pmul m (u + 1) : ℝ) / (Pmul m (u + 1 + d) : ℝ)) := by
    intro d
    induction d with
    | zero =>
      rw [hzero (u + 1) le_rfl, div_self (ne_of_gt (hPpos (u + 1)))]
      norm_num
    | succ d ih =>
      have hrew : u + 1 + (d + 1) = (u + 1 + d) + 1 := by ring
      rw [hrew, Finset.sum_range_succ]
      have hterm : (if u < u + 1 + d then
            (Pmul m (u + 1) : ℝ) / (Pmul m (u + 1 + d) : ℝ) else 0)
          = (Pmul m (u + 1) : ℝ) / (Pmul m (u + 1 + d) : ℝ) :=
        if_pos (by omega)
      rw [hterm]
      have hratio : (Pmul m (u + 1) : ℝ) / (Pmul m (u + 1 + d + 1) : ℝ)
          = ((Pmul m (u + 1) : ℝ) / (Pmul m (u + 1 + d) : ℝ)) / (m (u + 1 + d) : ℝ) := by
        rw [show Pmul m (u + 1 + d + 1) = Pmul m (u + 1 + d) * m (u + 1 + d) from
          Pmul_succ m (u + 1 + d), Nat.cast_mul, div_div]
      have hmS : (2 : ℝ) ≤ (m (u + 1 + d) : ℝ) := by
        exact_mod_cast hm2 (u + 1 + d)
      have hPu : (0 : ℝ) < (Pmul m (u + 1) : ℝ) := hPpos (u + 1)
      have hPS : (0 : ℝ) < (Pmul m (u + 1 + d) : ℝ) := hPpos (u + 1 + d)
      rw [hratio]
      have hquot : ((Pmul m (u + 1) : ℝ) / (Pmul m (u + 1 + d) : ℝ)) / (m (u + 1 + d) : ℝ)
          ≤ ((Pmul m (u + 1) : ℝ) / (Pmul m (u + 1 + d) : ℝ)) / 2 :=
        div_le_div_of_nonneg_left (div_nonneg (le_of_lt hPu) (le_of_lt hPS))
          (by norm_num) hmS
      linarith [ih, hquot]
  by_cases h : S ≤ u + 1
  · rw [hzero S h]; norm_num
  · obtain ⟨d, rfl⟩ : ∃ d, S = u + 1 + d := ⟨S - (u + 1), by omega⟩
    refine le_trans (hinv d) ?_
    have hg : (0 : ℝ) ≤ (Pmul m (u + 1) : ℝ) / (Pmul m (u + 1 + d) : ℝ) :=
      div_nonneg (le_of_lt (hPpos (u + 1))) (le_of_lt (hPpos (u + 1 + d)))
    linarith


/-! ## 3. The tower assembly -/

/-- The finite-scale averages converge to `lyap` along any sequence of scales tending to
infinity. -/
theorem tendsto_lyapAvg_of_tendsto {α lam : ℝ} {E : ℂ} {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) (hN1 : ∀ s, 1 ≤ N s) :
    Tendsto (fun s => lyapAvg α lam E (N s)) atTop (nhds (lyap α lam E)) := by
  have hbase : Tendsto (fun k : ℕ => lyapAvg α lam E (k + 1)) atTop (nhds (lyap α lam E)) := by
    simpa only [lyapAvg, Nat.cast_add, Nat.cast_one] using Lyap.lyap_eq_lim α lam E
  have hsub : Tendsto (fun s => N s - 1) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    obtain ⟨s₀, hs₀⟩ := Filter.tendsto_atTop_atTop.mp hN (b + 1)
    exact ⟨s₀, fun s hs => by have := hs₀ s hs; omega⟩
  have hcomp := hbase.comp hsub
  refine hcomp.congr' ?_
  filter_upwards with s
  simp only [Function.comp_apply]
  rw [Nat.sub_add_cancel (hN1 s)]

/-- **The scale tower of [BJ] Lemma 7** (with growing approximants).

Given the per-stage relations of the tower together with *summable* error bounds, the
telescoped difference `|lyap + L_{N₀} − 2 L_{2N₀}|` at the base scale is bounded by
`Σ ε₁ + 4 Σ ε₂ + 6 |D₀|/m₀`.  The per-stage relations are supplied by
`AvgStep.scale_step_avg`/`pairing_step` (Case I) and by [BJ] Lemma 8 (Case II). -/
theorem tower_le (α lam : ℝ) (E : ℂ) (N m : ℕ → ℕ) (ε₁ ε₂ : ℕ → ℝ)
    (hN0 : 1 ≤ N 0) (hm3 : ∀ s, 3 ≤ m s) (hNsucc : ∀ s, N (s + 1) = m s * N s)
    (hs₁ : Summable ε₁) (hs₂ : Summable ε₂)
    (hε₁ : ∀ s, 0 ≤ ε₁ s) (hε₂ : ∀ s, 0 ≤ ε₂ s)
    (hstep₁ : ∀ s, |lyapAvg α lam E (N (s + 1)) + lyapAvg α lam E (N s)
        - 2 * lyapAvg α lam E (2 * N s)| ≤ ε₁ s)
    (hstep₂ : ∀ s, |(lyapAvg α lam E (N (s + 1)) - lyapAvg α lam E (2 * N (s + 1)))
        - (1 / (m s : ℝ)) * (lyapAvg α lam E (N s) - lyapAvg α lam E (2 * N s))| ≤ ε₂ s) :
    |lyap α lam E + lyapAvg α lam E (N 0) - 2 * lyapAvg α lam E (2 * N 0)|
      ≤ 6 * |lyapAvg α lam E (N 0) - lyapAvg α lam E (2 * N 0)| / (m 0 : ℝ)
        + (∑' s, ε₁ s) + 4 * (∑' s, ε₂ s) := by
  have hm1 : ∀ s, 1 ≤ m s := fun s => le_trans (by norm_num) (hm3 s)
  have hmpos : ∀ s, (0 : ℝ) < (m s : ℝ) := fun s => by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hm1 s)
  have hPpos : ∀ s, (0 : ℝ) < (Pmul m s : ℝ) := fun s => Pmul_cast_pos hm1 s
  have hPne : ∀ s, (Pmul m s : ℝ) ≠ 0 := fun s => ne_of_gt (hPpos s)
  have hratio : ∀ s, (Pmul m s : ℝ) / (Pmul m (s + 1) : ℝ) = (1 : ℝ) / (m s : ℝ) := by
    intro s
    rw [Pmul_succ, Nat.cast_mul]
    rw [show (Pmul m s : ℝ) / ((Pmul m s : ℝ) * (m s : ℝ))
        = ((Pmul m s : ℝ) * 1) / ((Pmul m s : ℝ) * (m s : ℝ)) by rw [mul_one]]
    exact mul_div_mul_left 1 (m s : ℝ) (hPne s)
  set D : ℕ → ℝ := fun s => lyapAvg α lam E (N s) - lyapAvg α lam E (2 * N s) with hD
  set ψ : ℕ → ℝ := fun s => D (s + 1) - (Pmul m s : ℝ) / (Pmul m (s + 1) : ℝ) * D s with hψ
  have hψb : ∀ s, |ψ s| ≤ ε₂ s := by
    intro s
    have h := hstep₂ s
    rw [← hratio s] at h
    simpa only [hD, hψ] using h
  have hDsucc : ∀ s, D (s + 1) = ψ s + (Pmul m s : ℝ) / (Pmul m (s + 1) : ℝ) * D s := by
    intro s
    simp only [hψ]
    ring
  have hclosed : ∀ s, D s * (Pmul m s : ℝ)
      = D 0 + ∑ u ∈ Finset.range s, ψ u * (Pmul m (u + 1) : ℝ) := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      have hstep : D (s + 1) * (Pmul m (s + 1) : ℝ)
          = ψ s * (Pmul m (s + 1) : ℝ) + D s * (Pmul m s : ℝ) := by
        rw [hDsucc s, add_mul, div_mul_eq_mul_div, div_mul_cancel₀ _ (hPne (s + 1)),
          mul_comm (Pmul m s : ℝ) (D s)]
      rw [hstep, ih, Finset.sum_range_succ]
      ring
  have hpt : ∀ s, D s
      = (D 0 + ∑ u ∈ Finset.range s, ψ u * (Pmul m (u + 1) : ℝ)) / (Pmul m s : ℝ) := by
    intro s
    rw [eq_div_iff (hPne s)]
    exact hclosed s
  have hF : ∀ S, lyapAvg α lam E (N S) + lyapAvg α lam E (N 0)
      - 2 * lyapAvg α lam E (2 * N 0)
      = 2 * D 0
        + ∑ s ∈ Finset.range S, (lyapAvg α lam E (N (s + 1)) + lyapAvg α lam E (N s)
            - 2 * lyapAvg α lam E (2 * N s))
        - 2 * ∑ s ∈ Finset.range S, D s := by
    intro S
    have htel : ∑ s ∈ Finset.range S, (lyapAvg α lam E (N (s + 1)) - lyapAvg α lam E (N s))
        = lyapAvg α lam E (N S) - lyapAvg α lam E (N 0) := by
      induction S with
      | zero => simp
      | succ S ih => rw [Finset.sum_range_succ, ih]; ring
    have hpoint : ∀ s ∈ Finset.range S,
        lyapAvg α lam E (N (s + 1)) + lyapAvg α lam E (N s)
          - 2 * lyapAvg α lam E (2 * N s)
          = (lyapAvg α lam E (N (s + 1)) - lyapAvg α lam E (N s)) + 2 * D s := by
      intro s _
      simp only [hD]
      ring
    rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, ← Finset.mul_sum, htel]
    simp only [hD]
    ring
  have hDsum : ∀ S, ∑ s ∈ Finset.range S, D s
      = D 0 * (∑ s ∈ Finset.range S, (1 : ℝ) / (Pmul m s : ℝ))
        + ∑ s ∈ Finset.range S,
            ∑ u ∈ Finset.range s, ψ u * ((Pmul m (u + 1) : ℝ) / (Pmul m s : ℝ)) := by
    intro S
    calc ∑ s ∈ Finset.range S, D s
        = ∑ s ∈ Finset.range S, ((D 0 + ∑ u ∈ Finset.range s,
            ψ u * (Pmul m (u + 1) : ℝ)) / (Pmul m s : ℝ)) :=
          Finset.sum_congr rfl (fun s _ => hpt s)
      _ = ∑ s ∈ Finset.range S, ((D 0) / (Pmul m s : ℝ)
            + (∑ u ∈ Finset.range s, ψ u * (Pmul m (u + 1) : ℝ)) / (Pmul m s : ℝ)) :=
          Finset.sum_congr rfl (fun s _ => by rw [add_div])
      _ = (∑ s ∈ Finset.range S, (D 0) / (Pmul m s : ℝ))
            + ∑ s ∈ Finset.range S,
                (∑ u ∈ Finset.range s, ψ u * (Pmul m (u + 1) : ℝ)) / (Pmul m s : ℝ) :=
          Finset.sum_add_distrib
      _ = D 0 * (∑ s ∈ Finset.range S, (1 : ℝ) / (Pmul m s : ℝ))
            + ∑ s ∈ Finset.range S,
                ∑ u ∈ Finset.range s, ψ u * ((Pmul m (u + 1) : ℝ) / (Pmul m s : ℝ)) := by
          congr 1
          · rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun s _ => by rw [mul_one_div])
          · exact Finset.sum_congr rfl (fun s _ => by
              rw [Finset.sum_div]
              exact Finset.sum_congr rfl (fun u _ => by rw [mul_div_assoc]))
  have hswap : ∀ S, ∑ s ∈ Finset.range S,
        ∑ u ∈ Finset.range s, ψ u * ((Pmul m (u + 1) : ℝ) / (Pmul m s : ℝ))
      = ∑ u ∈ Finset.range S, ψ u * (∑ j ∈ Finset.range S,
          (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0)) := by
    intro S
    have hinner : ∀ s ∈ Finset.range S,
        ∑ u ∈ Finset.range s, ψ u * ((Pmul m (u + 1) : ℝ) / (Pmul m s : ℝ))
        = ∑ u ∈ Finset.range S,
            (if u < s then ψ u * ((Pmul m (u + 1) : ℝ) / (Pmul m s : ℝ)) else 0) := by
      intro s hs
      have hsS : s ≤ S := le_of_lt (Finset.mem_range.mp hs)
      rw [← Finset.sum_filter]
      congr 1
      ext u
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [mul_ite, mul_zero])
  have hTail : ∀ S, |∑ u ∈ Finset.range S, ψ u * (∑ j ∈ Finset.range S,
        (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0))|
      ≤ 2 * (∑' u, ε₂ u) := by
    intro S
    have h1 : |∑ u ∈ Finset.range S, ψ u * (∑ j ∈ Finset.range S,
          (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0))|
        ≤ ∑ u ∈ Finset.range S, |ψ u * (∑ j ∈ Finset.range S,
            (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0))| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : ∀ u ∈ Finset.range S, |ψ u * (∑ j ∈ Finset.range S,
          (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0))|
        ≤ ε₂ u * 2 := by
      intro u _
      have hTnn : 0 ≤ ∑ j ∈ Finset.range S,
          (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0) := by
        refine Finset.sum_nonneg (fun j _ => ?_)
        by_cases h : u < j
        · rw [if_pos h]; positivity
        · rw [if_neg h]
      have hT2 := sum_tail_weight_le hm3 u S
      rw [abs_mul, abs_of_nonneg hTnn]
      exact mul_le_mul (hψb u) hT2 hTnn (hε₂ u)
    calc |∑ u ∈ Finset.range S, ψ u * (∑ j ∈ Finset.range S,
            (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0))|
        ≤ ∑ u ∈ Finset.range S, |ψ u * (∑ j ∈ Finset.range S,
            (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0))| := h1
      _ ≤ ∑ u ∈ Finset.range S, ε₂ u * 2 := Finset.sum_le_sum h2
      _ = (∑ u ∈ Finset.range S, ε₂ u) * 2 := by rw [Finset.sum_mul]
      _ ≤ (∑' u, ε₂ u) * 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
          exact Summable.sum_le_tsum (Finset.range S) (fun i _ => hε₂ i) hs₂
      _ = 2 * (∑' u, ε₂ u) := by ring
  have hbound : ∀ S, 1 ≤ S → |lyapAvg α lam E (N S) + lyapAvg α lam E (N 0)
      - 2 * lyapAvg α lam E (2 * N 0)| ≤ 6 * |D 0| / (m 0 : ℝ)
        + (∑' s, ε₁ s) + 4 * (∑' s, ε₂ s) := by
    intro S hS
    have hUle := sum_inv_Pmul_le hm3 S
    have hUge : 1 ≤ ∑ s ∈ Finset.range S, (1 : ℝ) / (Pmul m s : ℝ) := by
      rw [sum_inv_Pmul_eq m hm1 S]
      have hlast : (1 : ℝ) / (Pmul m S : ℝ)
          ≤ ∑ j ∈ Finset.range S, (1 : ℝ) / (Pmul m (j + 1) : ℝ) := by
        obtain ⟨j, rfl⟩ : ∃ j, S = j + 1 := ⟨S - 1, by omega⟩
        refine Finset.single_le_sum (f := fun i => (1 : ℝ) / (Pmul m (i + 1) : ℝ))
          (fun i _ => by positivity) ?_
        exact Finset.mem_range.mpr (Nat.lt_succ_self j)
      linarith
    have habs : |1 - ∑ s ∈ Finset.range S, (1 : ℝ) / (Pmul m s : ℝ)| ≤ 3 / (m 0 : ℝ) := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤
        (∑ s ∈ Finset.range S, (1 : ℝ) / (Pmul m s : ℝ)) - 1)]
      linarith
    have hβ : |∑ s ∈ Finset.range S, (lyapAvg α lam E (N (s + 1)) + lyapAvg α lam E (N s)
        - 2 * lyapAvg α lam E (2 * N s))| ≤ ∑' s, ε₁ s := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun s _ => hstep₁ s)) ?_
      exact Summable.sum_le_tsum (Finset.range S) (fun i _ => hε₁ i) hs₁
    have hident : lyapAvg α lam E (N S) + lyapAvg α lam E (N 0)
        - 2 * lyapAvg α lam E (2 * N 0)
        = 2 * D 0 * (1 - ∑ s ∈ Finset.range S, (1 : ℝ) / (Pmul m s : ℝ))
          + (∑ s ∈ Finset.range S, (lyapAvg α lam E (N (s + 1)) + lyapAvg α lam E (N s)
              - 2 * lyapAvg α lam E (2 * N s)))
          - 2 * (∑ u ∈ Finset.range S, ψ u * (∑ j ∈ Finset.range S,
              (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0))) := by
      rw [hF S, hDsum S, hswap S]
      ring
    rw [hident]
    have hA : |2 * D 0 * (1 - ∑ s ∈ Finset.range S, (1 : ℝ) / (Pmul m s : ℝ))|
        ≤ 2 * |D 0| * (3 / (m 0 : ℝ)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      exact mul_le_mul_of_nonneg_left habs (by positivity)
    have htri : |2 * D 0 * (1 - ∑ s ∈ Finset.range S, (1 : ℝ) / (Pmul m s : ℝ))
          + (∑ s ∈ Finset.range S, (lyapAvg α lam E (N (s + 1)) + lyapAvg α lam E (N s)
              - 2 * lyapAvg α lam E (2 * N s)))
          - 2 * (∑ u ∈ Finset.range S, ψ u * (∑ j ∈ Finset.range S,
              (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0)))|
        ≤ |2 * D 0 * (1 - ∑ s ∈ Finset.range S, (1 : ℝ) / (Pmul m s : ℝ))|
          + |∑ s ∈ Finset.range S, (lyapAvg α lam E (N (s + 1)) + lyapAvg α lam E (N s)
              - 2 * lyapAvg α lam E (2 * N s))|
          + |2 * (∑ u ∈ Finset.range S, ψ u * (∑ j ∈ Finset.range S,
              (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0)))| := by
      set A := 2 * D 0 * (1 - ∑ s ∈ Finset.range S, (1 : ℝ) / (Pmul m s : ℝ))
      set B := ∑ s ∈ Finset.range S, (lyapAvg α lam E (N (s + 1)) + lyapAvg α lam E (N s)
              - 2 * lyapAvg α lam E (2 * N s))
      set Cc := 2 * (∑ u ∈ Finset.range S, ψ u * (∑ j ∈ Finset.range S,
              (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0)))
      have h2 : A + B - Cc = A + (B + (-Cc)) := by ring
      rw [h2]
      calc |A + (B + (-Cc))| ≤ |A| + |B + (-Cc)| := abs_add_le _ _
        _ ≤ |A| + (|B| + |(-Cc)|) := by
            have := abs_add_le B (-Cc); linarith [abs_nonneg A]
        _ = |A| + |B| + |Cc| := by rw [abs_neg]; ring
    have hC : |2 * (∑ u ∈ Finset.range S, ψ u * (∑ j ∈ Finset.range S,
        (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0)))|
        ≤ 4 * (∑' u, ε₂ u) := by
      have h1 : |2 * (∑ u ∈ Finset.range S, ψ u * (∑ j ∈ Finset.range S,
          (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0)))|
          ≤ 2 * (2 * (∑' u, ε₂ u)) := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
        exact mul_le_mul_of_nonneg_left (hTail S) (by norm_num)
      have h2 : 2 * (2 * (∑' u, ε₂ u)) = 4 * (∑' u, ε₂ u) := by ring
      linarith [h1, h2]
    calc |2 * D 0 * (1 - ∑ s ∈ Finset.range S, (1 : ℝ) / (Pmul m s : ℝ))
          + (∑ s ∈ Finset.range S, (lyapAvg α lam E (N (s + 1)) + lyapAvg α lam E (N s)
              - 2 * lyapAvg α lam E (2 * N s)))
          - 2 * (∑ u ∈ Finset.range S, ψ u * (∑ j ∈ Finset.range S,
              (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0)))|
        ≤ |2 * D 0 * (1 - ∑ s ∈ Finset.range S, (1 : ℝ) / (Pmul m s : ℝ))|
          + |∑ s ∈ Finset.range S, (lyapAvg α lam E (N (s + 1)) + lyapAvg α lam E (N s)
              - 2 * lyapAvg α lam E (2 * N s))|
          + |2 * (∑ u ∈ Finset.range S, ψ u * (∑ j ∈ Finset.range S,
              (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0)))| := htri
      _ ≤ 2 * |D 0| * (3 / (m 0 : ℝ)) + (∑' s, ε₁ s) + 4 * (∑' s, ε₂ s) :=
          add_le_add (add_le_add hA hβ) hC
      _ = 6 * |D 0| / (m 0 : ℝ) + (∑' s, ε₁ s) + 4 * (∑' s, ε₂ s) := by ring
  have hN1 : ∀ s, 1 ≤ N s := by
    intro s
    induction s with
    | zero => exact hN0
    | succ s ih => rw [hNsucc s]; exact Nat.mul_le_mul (hm1 s) ih
  have hNtend : Tendsto N atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    have hpow : ∀ s, 2 ^ s ≤ N s := by
      intro s
      induction s with
      | zero => simpa using hN0
      | succ s ih =>
        have hm : 2 ≤ m s := le_trans (by norm_num) (hm3 s)
        calc 2 ^ (s + 1) = 2 * 2 ^ s := by ring
          _ ≤ m s * N s := Nat.mul_le_mul hm ih
          _ = N (s + 1) := (hNsucc s).symm
    have h2b : b ≤ 2 ^ b := by
      induction b with
      | zero => simp
      | succ b ih =>
        have h1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
        calc b + 1 ≤ 2 * 2 ^ b := by omega
          _ = 2 ^ (b + 1) := by ring
    exact ⟨b, fun s hs => le_trans (le_trans h2b (Nat.pow_le_pow_right (by norm_num) hs)) (hpow s)⟩
  have htend : Tendsto (fun S => lyapAvg α lam E (N S)) atTop (nhds (lyap α lam E)) :=
    tendsto_lyapAvg_of_tendsto hNtend hN1
  have hlim : Tendsto (fun S => |lyapAvg α lam E (N S) + lyapAvg α lam E (N 0)
        - 2 * lyapAvg α lam E (2 * N 0)|) atTop
      (nhds |lyap α lam E + lyapAvg α lam E (N 0) - 2 * lyapAvg α lam E (2 * N 0)|) :=
    ((htend.add tendsto_const_nhds).sub tendsto_const_nhds).abs
  have hfin := le_of_tendsto hlim (eventually_atTop.mpr ⟨1, fun S hS => hbound S hS⟩)
  simpa only [hD] using hfin


/-! ## 4. The base-scale hypotheses and the Case I instantiation

The two facts about the *base* scale that the tower consumes are

* the level `100κ < lyapAvg (N 0)`, which follows from `100κ < lyap` because `lyap ≤ lyapAvg · n`
  for every `n ≥ 1` (this is the paper's setting: the *true* exponent is assumed large, and then
  every tower level is automatically large), and
* the pairing `(9/10)·lyapAvg (N 0) < lyapAvg (2·N 0)`,

plus the *propagation* of the pairing along the tower, which the defect contraction supplies:
`D_{s+1} ≤ C₀/m_s + 2ε_s` and the level `100κ < lyapAvg (N_{s+1})` give
`D_{s+1} < (1/10)·lyapAvg (N_{s+1})` as soon as `C₀/m_s + 2ε_s ≤ 10κ`.
-/

/-- `lyapAvg` at an energy of `K` is bounded by the `HasLEBound` constant. -/
theorem lyapAvg_le_of_hasLEBound {lam : ℝ} {K : Set ℝ} {C₀ : ℝ} (hC₀ : HasLEBound lam K C₀)
    {E : ℝ} (hE : E ∈ K) (α : ℝ) (N : ℕ) : lyapAvg α lam (E : ℂ) N ≤ C₀ := by
  rw [lyapAvg_eq_integral_uAvg]
  have hint : IntervalIntegrable (fun x : ℝ => uAvg α lam (E : ℂ) N x) volume (0 : ℝ) 1 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      have : (fun x : ℝ => uAvg α lam (E : ℂ) 0 x) = fun _ => (0 : ℝ) := by
        funext x; simp [uAvg]
      rw [this]
      exact intervalIntegrable_const
    · have hN : ((N : ℕ) : ℝ) ≠ 0 := by positivity
      have := (Cocycle.intervalIntegrable_log_frob α lam (E : ℂ) N).div_const ((N : ℕ) : ℝ)
      simpa [uAvg, div_eq_inv_mul] using this
  have hmono : (∫ x in (0 : ℝ)..1, uAvg α lam (E : ℂ) N x) ≤ ∫ x in (0 : ℝ)..1, C₀ := by
    refine intervalIntegral.integral_mono_on (by norm_num) hint intervalIntegrable_const ?_
    intro x _
    exact hC₀.2 E hE α N x
  simpa using hmono

/-- **The Case I scale tower.**  If the tower's scales carry approximants `(A s, Q s)` of `α`
in the LDT range (`Cκ⁻² ≤ Q s`, `|α − A s/Q s| < 1/(Q s)²`, `Cκ⁻²Q s ≤ N s`) and the multipliers
satisfy `3 ≤ m s`, `2 m s < e^{cκQ_s/2}`, then — assuming the levels `100κ < L_{N_s}` at **every** stage (in the paper's setting these are
free: `100κ < lyap ≤ L_n`), the pairing at the base scale, the propagation inequality
`C₀/m_s + 2(4C₀+1)e^{−cκQ_s/2} ≤ 10κ` and the summability of both `e^{−cκQ_s/2}` and `1/m_s` —
the difference form of [BJ] Proposition 9 holds at the base scale, with the explicit error
`6C₀/m₀ + 9(4C₀+1)Σ e^{−cκQ_s/2} + 2C₀Σ 1/m_s`. -/
theorem tower_le_of_scale_step (lam : ℝ) (K : Set ℝ) (c C C₀ : ℝ)
    (hLDT : HasLDTOn lam K c C) (hC₀ : HasLEBound lam K C₀) (hc1 : c ≤ 1)
    (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 100) (E : ℝ) (hE : E ∈ K) (α : ℝ)
    (N m : ℕ → ℕ) (A : ℕ → ℤ) (Q : ℕ → ℕ)
    (hN0 : 1 ≤ N 0) (hm3 : ∀ s, 3 ≤ m s) (hNsucc : ∀ s, N (s + 1) = m s * N s)
    (hq1 : ∀ s, 1 ≤ Q s) (hcop : ∀ s, Nat.Coprime (Int.natAbs (A s)) (Q s))
    (hqC : ∀ s, C * (κ ^ 2)⁻¹ ≤ (Q s : ℝ))
    (hα : ∀ s, |α - (A s : ℝ) / (Q s : ℝ)| < 1 / ((Q s : ℝ) ^ 2))
    (hNQ : ∀ s, C * (κ ^ 2)⁻¹ * (Q s : ℝ) ≤ (N s : ℝ))
    (hmq : ∀ s, ((2 * m s : ℕ) : ℝ) < Real.exp (c * κ * (Q s : ℝ) / 2))
    (hlev : ∀ s, 100 * κ < lyapAvg α lam (E : ℂ) (N s))
    (hpair : (9 / 10) * lyapAvg α lam (E : ℂ) (N 0) < lyapAvg α lam (E : ℂ) (2 * N 0))
    (hprop : ∀ s, C₀ / (m s : ℝ)
      + 2 * ((4 * C₀ + 1) * Real.exp (-(c * κ * (Q s : ℝ) / 2))) ≤ 10 * κ)
    (hS₁ : Summable fun s => Real.exp (-(c * κ * (Q s : ℝ) / 2)))
    (hS₂ : Summable fun s => (1 : ℝ) / (m s : ℝ)) :
    |lyap α lam (E : ℂ) + lyapAvg α lam (E : ℂ) (N 0)
        - 2 * lyapAvg α lam (E : ℂ) (2 * N 0)|
      ≤ 6 * C₀ / (m 0 : ℝ)
        + 9 * (4 * C₀ + 1) * (∑' s, Real.exp (-(c * κ * (Q s : ℝ) / 2)))
        + 2 * C₀ * (∑' s, (1 : ℝ) / (m s : ℝ)) := by
  have hm1 : ∀ s, 1 ≤ m s := fun s => le_trans (by norm_num) (hm3 s)
  have hmpos : ∀ s, (0 : ℝ) < (m s : ℝ) := fun s => by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hm1 s)
  have hN1 : ∀ s, 1 ≤ N s := by
    intro s
    induction s with
    | zero => exact hN0
    | succ s ih => rw [hNsucc s]; exact Nat.mul_le_mul (hm1 s) ih
  -- the defect is bounded by `C₀`
  have hDle : ∀ s, lyapAvg α lam (E : ℂ) (N s) - lyapAvg α lam (E : ℂ) (2 * N s) ≤ C₀ := by
    intro s
    have h1 := lyapAvg_le_of_hasLEBound hC₀ hE α (N s)
    have h2 : 0 ≤ lyapAvg α lam (E : ℂ) (2 * N s) := by
      rcases Nat.eq_zero_or_pos (2 * N s) with h | h
      · rw [h]; simp [lyapAvg]
      · obtain ⟨k, hk⟩ : ∃ k, 2 * N s = k + 1 := ⟨2 * N s - 1, by omega⟩
        rw [hk]
        exact Scale.lyapAvg_nonneg' α lam (E : ℂ) k
    linarith
  have hDnn : ∀ s, 0 ≤ lyapAvg α lam (E : ℂ) (N s) - lyapAvg α lam (E : ℂ) (2 * N s) :=
    fun s => sub_nonneg.mpr (by
      have := Scale.lyapAvg_two_le α lam (E : ℂ) (N s)
      linarith [this])
  -- the pairing propagates
  have hpair_all : ∀ s, (9 / 10) * lyapAvg α lam (E : ℂ) (N s)
      < lyapAvg α lam (E : ℂ) (2 * N s) := by
    intro s
    induction s with
    | zero => exact hpair
    | succ s ih =>
      have hstep := Scale.pairing_step lam K c C C₀ hLDT hC₀ hc1 κ hκ hκ1 E hE α (A s) (Q s)
        (hq1 s) (hcop s) (hqC s) (hα s) (N s) (hNQ s) (hlev s) ih (m s) (hm3 s) (hmq s)
      rw [← hNsucc s] at hstep
      have h2 := (abs_le.mp hstep).2
      have h4 : (1 / (m s : ℝ)) * (lyapAvg α lam (E : ℂ) (N s)
          - lyapAvg α lam (E : ℂ) (2 * N s)) ≤ C₀ / (m s : ℝ) := by
        rw [div_eq_inv_mul, div_eq_inv_mul, mul_one]
        exact mul_le_mul_of_nonneg_left (hDle s) (inv_nonneg.mpr (le_of_lt (hmpos s)))
      have h5 := hprop s
      have h6 := hlev (s + 1)
      have h7 : lyapAvg α lam (E : ℂ) (N (s + 1)) - lyapAvg α lam (E : ℂ) (2 * N (s + 1))
          ≤ C₀ / (m s : ℝ) + 2 * ((4 * C₀ + 1) * Real.exp (-(c * κ * (Q s : ℝ) / 2))) := by
        linarith [h2, h4]
      linarith [h7, h5, h6]
  -- the per-stage relations
  have hstep₂ : ∀ s, |(lyapAvg α lam (E : ℂ) (N (s + 1))
        - lyapAvg α lam (E : ℂ) (2 * N (s + 1)))
        - (1 / (m s : ℝ)) * (lyapAvg α lam (E : ℂ) (N s)
          - lyapAvg α lam (E : ℂ) (2 * N s))|
      ≤ 2 * ((4 * C₀ + 1) * Real.exp (-(c * κ * (Q s : ℝ) / 2))) := fun s => by
    have h := Scale.pairing_step lam K c C C₀ hLDT hC₀ hc1 κ hκ hκ1 E hE α (A s) (Q s)
      (hq1 s) (hcop s) (hqC s) (hα s) (N s) (hNQ s) (hlev s) (hpair_all s) (m s) (hm3 s) (hmq s)
    rw [← hNsucc s] at h
    exact h
  have hstep₁ : ∀ s, |lyapAvg α lam (E : ℂ) (N (s + 1)) + lyapAvg α lam (E : ℂ) (N s)
      - 2 * lyapAvg α lam (E : ℂ) (2 * N s)|
      ≤ ((4 * C₀ + 1) * Real.exp (-(c * κ * (Q s : ℝ) / 2)))
        + 2 * C₀ / (m s : ℝ) := by
    intro s
    have hmq' : ((m s : ℕ) : ℝ) < Real.exp (c * κ * (Q s : ℝ) / 2) := by
      have h2m : ((m s : ℕ) : ℝ) ≤ ((2 * m s : ℕ) : ℝ) := by push_cast; linarith [hm3 s]
      linarith [hmq s, h2m]
    have hscale := Scale.AvgStep.scale_step_avg lam K c C C₀ hLDT hC₀ hc1 κ hκ hκ1 E hE α (A s)
      (Q s) (hq1 s) (hcop s) (hqC s) (hα s) (N s) (hNQ s) (hlev s) (hpair_all s) (m s) (hm3 s) hmq'
    rw [← hNsucc s] at hscale
    have hrew : lyapAvg α lam (E : ℂ) (N (s + 1)) + lyapAvg α lam (E : ℂ) (N s)
        - 2 * lyapAvg α lam (E : ℂ) (2 * N s)
        = (lyapAvg α lam (E : ℂ) (N (s + 1)) + (1 - 2 / (m s : ℝ)) * lyapAvg α lam (E : ℂ) (N s)
            - (2 - 2 / (m s : ℝ)) * lyapAvg α lam (E : ℂ) (2 * N s))
          + (2 / (m s : ℝ)) * (lyapAvg α lam (E : ℂ) (N s)
            - lyapAvg α lam (E : ℂ) (2 * N s)) := by ring
    rw [hrew]
    have h2 : |(2 / (m s : ℝ)) * (lyapAvg α lam (E : ℂ) (N s)
        - lyapAvg α lam (E : ℂ) (2 * N s))| ≤ 2 * C₀ / (m s : ℝ) := by
      rw [abs_mul, abs_of_nonneg (div_nonneg (by norm_num) (le_of_lt (hmpos s))),
        abs_of_nonneg (hDnn s)]
      have h3 : (2 / (m s : ℝ)) * (lyapAvg α lam (E : ℂ) (N s)
          - lyapAvg α lam (E : ℂ) (2 * N s)) ≤ (2 / (m s : ℝ)) * C₀ :=
        mul_le_mul_of_nonneg_left (hDle s)
          (div_nonneg (by norm_num) (le_of_lt (hmpos s)))
      calc (2 / (m s : ℝ)) * (lyapAvg α lam (E : ℂ) (N s)
            - lyapAvg α lam (E : ℂ) (2 * N s)) ≤ (2 / (m s : ℝ)) * C₀ := h3
        _ = 2 * C₀ / (m s : ℝ) := by ring
    calc |_ + _| ≤ |lyapAvg α lam (E : ℂ) (N (s + 1)) + (1 - 2 / (m s : ℝ))
            * lyapAvg α lam (E : ℂ) (N s) - (2 - 2 / (m s : ℝ)) * lyapAvg α lam (E : ℂ) (2 * N s)|
          + |(2 / (m s : ℝ)) * (lyapAvg α lam (E : ℂ) (N s)
            - lyapAvg α lam (E : ℂ) (2 * N s))| := abs_add_le _ _
      _ ≤ (4 * C₀ + 1) * Real.exp (-(c * κ * (Q s : ℝ) / 2)) + 2 * C₀ / (m s : ℝ) :=
          add_le_add hscale h2
  -- summability
  have hsumε : Summable fun s => (4 * C₀ + 1) * Real.exp (-(c * κ * (Q s : ℝ) / 2)) :=
    hS₁.mul_left (4 * C₀ + 1)
  have hsumm : Summable fun s => 2 * C₀ / (m s : ℝ) := by
    refine (hS₂.mul_left (2 * C₀)).congr (fun s => ?_)
    ring_nf
  have hε₁ : ∀ s, 0 ≤ ((4 * C₀ + 1) * Real.exp (-(c * κ * (Q s : ℝ) / 2))) + 2 * C₀ / (m s : ℝ) :=
    fun s => by
      have h1 : (0 : ℝ) < 4 * C₀ + 1 := by linarith [hC₀.1]
      have h2 : (0 : ℝ) < Real.exp (-(c * κ * (Q s : ℝ) / 2)) := Real.exp_pos _
      have h3 : (0 : ℝ) ≤ 2 * C₀ / (m s : ℝ) :=
        div_nonneg (by linarith [hC₀.1]) (le_of_lt (hmpos s))
      linarith [mul_pos h1 h2]
  have hε₂ : ∀ s, 0 ≤ 2 * ((4 * C₀ + 1) * Real.exp (-(c * κ * (Q s : ℝ) / 2))) :=
    fun s => by
      have h1 : (0 : ℝ) < 4 * C₀ + 1 := by linarith [hC₀.1]
      have h2 : (0 : ℝ) < Real.exp (-(c * κ * (Q s : ℝ) / 2)) := Real.exp_pos _
      linarith [mul_pos h1 h2]
  have hmain := tower_le α lam (E : ℂ) N m
    (fun s => (4 * C₀ + 1) * Real.exp (-(c * κ * (Q s : ℝ) / 2)) + 2 * C₀ / (m s : ℝ))
    (fun s => 2 * ((4 * C₀ + 1) * Real.exp (-(c * κ * (Q s : ℝ) / 2))))
    hN0 hm3 hNsucc (hsumε.add hsumm) (hsumε.mul_left 2) hε₁ hε₂ hstep₁ hstep₂
  have ht₁ : (∑' s, ((4 * C₀ + 1) * Real.exp (-(c * κ * (Q s : ℝ) / 2)) + 2 * C₀ / (m s : ℝ)))
      = (4 * C₀ + 1) * (∑' s, Real.exp (-(c * κ * (Q s : ℝ) / 2)))
        + 2 * C₀ * (∑' s, (1 : ℝ) / (m s : ℝ)) := by
    rw [Summable.tsum_add hsumε hsumm, tsum_mul_left]
    congr 1
    rw [← tsum_mul_left]
    exact tsum_congr (fun s => by rw [div_eq_mul_inv]; ring)
  have ht₂ : (∑' s, 2 * ((4 * C₀ + 1) * Real.exp (-(c * κ * (Q s : ℝ) / 2))))
      = 2 * (4 * C₀ + 1) * (∑' s, Real.exp (-(c * κ * (Q s : ℝ) / 2))) := by
    rw [tsum_mul_left, tsum_mul_left]
    ring
  have hD0 : |lyapAvg α lam (E : ℂ) (N 0) - lyapAvg α lam (E : ℂ) (2 * N 0)| ≤ C₀ := by
    rw [abs_of_nonneg (hDnn 0)]
    exact hDle 0
  have hm0 : (0 : ℝ) < (m 0 : ℝ) := hmpos 0
  have hC₀pos : (0 : ℝ) ≤ C₀ := le_of_lt hC₀.1
  rw [ht₁, ht₂] at hmain
  have hb : 6 * |lyapAvg α lam (E : ℂ) (N 0) - lyapAvg α lam (E : ℂ) (2 * N 0)| / (m 0 : ℝ)
      ≤ 6 * C₀ / (m 0 : ℝ) := by
    have h6 : (0 : ℝ) ≤ 6 / (m 0 : ℝ) := by positivity
    calc 6 * |lyapAvg α lam (E : ℂ) (N 0) - lyapAvg α lam (E : ℂ) (2 * N 0)| / (m 0 : ℝ)
        = (6 / (m 0 : ℝ)) * |lyapAvg α lam (E : ℂ) (N 0) - lyapAvg α lam (E : ℂ) (2 * N 0)| := by
          ring
      _ ≤ (6 / (m 0 : ℝ)) * C₀ := mul_le_mul_of_nonneg_left hD0 h6
      _ = 6 * C₀ / (m 0 : ℝ) := by ring
  have h9 : (4 * C₀ + 1) * (∑' s, Real.exp (-(c * κ * (Q s : ℝ) / 2)))
      ≤ 9 * (4 * C₀ + 1) * (∑' s, Real.exp (-(c * κ * (Q s : ℝ) / 2))) := by
    have h0 : (0 : ℝ) ≤ (∑' s, Real.exp (-(c * κ * (Q s : ℝ) / 2))) :=
      tsum_nonneg (fun s => by positivity)
    have h1 : (0 : ℝ) ≤ 4 * C₀ + 1 := by linarith
    nlinarith [h0, h1]
  linarith [hmain, hb, h9]

/-- The Case I scale tower with the *true* exponent hypothesis: if `100κ < lyap` then the levels
`100κ < L_{N_s}` needed by `tower_le_of_scale_step` are free (`lyap ≤ lyapAvg · n`). -/
theorem tower_le_of_scale_step_of_lyap (lam : ℝ) (K : Set ℝ) (c C C₀ : ℝ)
    (hLDT : HasLDTOn lam K c C) (hC₀ : HasLEBound lam K C₀) (hc1 : c ≤ 1)
    (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 100) (E : ℝ) (hE : E ∈ K) (α : ℝ)
    (N m : ℕ → ℕ) (A : ℕ → ℤ) (Q : ℕ → ℕ)
    (hN0 : 1 ≤ N 0) (hm3 : ∀ s, 3 ≤ m s) (hNsucc : ∀ s, N (s + 1) = m s * N s)
    (hq1 : ∀ s, 1 ≤ Q s) (hcop : ∀ s, Nat.Coprime (Int.natAbs (A s)) (Q s))
    (hqC : ∀ s, C * (κ ^ 2)⁻¹ ≤ (Q s : ℝ))
    (hα : ∀ s, |α - (A s : ℝ) / (Q s : ℝ)| < 1 / ((Q s : ℝ) ^ 2))
    (hNQ : ∀ s, C * (κ ^ 2)⁻¹ * (Q s : ℝ) ≤ (N s : ℝ))
    (hmq : ∀ s, ((2 * m s : ℕ) : ℝ) < Real.exp (c * κ * (Q s : ℝ) / 2))
    (hL : 100 * κ < lyap α lam (E : ℂ))
    (hpair : (9 / 10) * lyapAvg α lam (E : ℂ) (N 0) < lyapAvg α lam (E : ℂ) (2 * N 0))
    (hprop : ∀ s, C₀ / (m s : ℝ)
      + 2 * ((4 * C₀ + 1) * Real.exp (-(c * κ * (Q s : ℝ) / 2))) ≤ 10 * κ)
    (hS₁ : Summable fun s => Real.exp (-(c * κ * (Q s : ℝ) / 2)))
    (hS₂ : Summable fun s => (1 : ℝ) / (m s : ℝ)) :
    |lyap α lam (E : ℂ) + lyapAvg α lam (E : ℂ) (N 0)
        - 2 * lyapAvg α lam (E : ℂ) (2 * N 0)|
      ≤ 6 * C₀ / (m 0 : ℝ)
        + 9 * (4 * C₀ + 1) * (∑' s, Real.exp (-(c * κ * (Q s : ℝ) / 2)))
        + 2 * C₀ * (∑' s, (1 : ℝ) / (m s : ℝ)) := by
  have hm1 : ∀ s, 1 ≤ m s := fun s => le_trans (by norm_num) (hm3 s)
  have hN1 : ∀ s, 1 ≤ N s := by
    intro s
    induction s with
    | zero => exact hN0
    | succ s ih => rw [hNsucc s]; exact Nat.mul_le_mul (hm1 s) ih
  exact tower_le_of_scale_step lam K c C C₀ hLDT hC₀ hc1 κ hκ hκ1 E hE α N m A Q
    hN0 hm3 hNsucc hq1 hcop hqC hα hNQ hmq
    (fun s => lt_of_lt_of_le hL (Scale.lyap_le_lyapAvg α lam (E : ℂ) (hN1 s)))
    hpair hprop hS₁ hS₂



/-! ## 5. The tower in *affine* form (the sharp form of [BJ] Lemma 7)

The per-stage relation of [BJ] Lemma 6 is naturally an *affine* one,
`|L_{mN} + (1 − 2/m)L_N − (2 − 2/m)L_{2N}| ≤ ε`: it carries the `1/m` remainder exactly, and
with it the telescoping is *exact*:

  `L_{N_S} + L_{N₀} − 2L_{2N₀} = 2 D_S + Σ_{s<S} (ρ_s − 2ψ_s)`,

where `D_s = L_{N_s} − L_{2N_s}`, `ψ_s = D_{s+1} − D_s/m_s` (the defect-contraction error) and
`ρ_s` is the affine error.  Since the defect recursion `D_{s+1} = D_s/m_s + ψ_s` makes `D_s → 0`
(the multipliers are `≥ 3` and `Σε₂ < ∞`), the base-scale difference is bounded by
`Σ ε₁ + 2 Σ ε₂` alone — in particular *without* the `6|D₀|/m₀` remainder of the non-affine form,
and *without* any hypothesis on `Σ 1/m_s`.  The latter matters: in [BJ]'s construction the tower
scales are tied to the approximant denominators (`N_{σ+1}/N_σ ≈ Q_{σ+1}/Q_σ`), so `Σ 1/m_s` is
*not* available in general, whereas `Σ e^{−cκQ_s/2}` always is (the approximants grow
geometrically).  This is the form the Case I construction should target.
-/

/-- **The scale tower, affine form.** -/
theorem tower_le_affine (α lam : ℝ) (E : ℂ) (N m : ℕ → ℕ) (ε₁ ε₂ : ℕ → ℝ)
    (hN0 : 1 ≤ N 0) (hm3 : ∀ s, 3 ≤ m s) (hNsucc : ∀ s, N (s + 1) = m s * N s)
    (hs₁ : Summable ε₁) (hs₂ : Summable ε₂)
    (hstep₁ : ∀ s, |lyapAvg α lam E (N (s + 1)) + (1 - 2 / (m s : ℝ)) * lyapAvg α lam E (N s)
        - (2 - 2 / (m s : ℝ)) * lyapAvg α lam E (2 * N s)| ≤ ε₁ s)
    (hstep₂ : ∀ s, |(lyapAvg α lam E (N (s + 1)) - lyapAvg α lam E (2 * N (s + 1)))
        - (1 / (m s : ℝ)) * (lyapAvg α lam E (N s) - lyapAvg α lam E (2 * N s))| ≤ ε₂ s) :
    |lyap α lam E + lyapAvg α lam E (N 0) - 2 * lyapAvg α lam E (2 * N 0)|
      ≤ (∑' s, ε₁ s) + 2 * (∑' s, ε₂ s) := by
  have hm1 : ∀ s, 1 ≤ m s := fun s => le_trans (by norm_num) (hm3 s)
  have hmpos : ∀ s, (0 : ℝ) < (m s : ℝ) := fun s => by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hm1 s)
  have hN1 : ∀ s, 1 ≤ N s := by
    intro s
    induction s with
    | zero => exact hN0
    | succ s ih => rw [hNsucc s]; exact Nat.mul_le_mul (hm1 s) ih
  have hNtend : Tendsto N atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    have hpow : ∀ s, 2 ^ s ≤ N s := by
      intro s
      induction s with
      | zero => simpa using hN0
      | succ s ih =>
        have hm : 2 ≤ m s := le_trans (by norm_num) (hm3 s)
        calc 2 ^ (s + 1) = 2 * 2 ^ s := by ring
          _ ≤ m s * N s := Nat.mul_le_mul hm ih
          _ = N (s + 1) := (hNsucc s).symm
    have h2b : b ≤ 2 ^ b := by
      induction b with
      | zero => simp
      | succ b ih =>
        have h1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
        calc b + 1 ≤ 2 * 2 ^ b := by omega
          _ = 2 ^ (b + 1) := by ring
    exact ⟨b, fun s hs => le_trans (le_trans h2b (Nat.pow_le_pow_right (by norm_num) hs)) (hpow s)⟩
  have htend : Tendsto (fun S => lyapAvg α lam E (N S)) atTop (nhds (lyap α lam E)) :=
    tendsto_lyapAvg_of_tendsto hNtend hN1
  set D : ℕ → ℝ := fun s => lyapAvg α lam E (N s) - lyapAvg α lam E (2 * N s) with hD
  set ψ : ℕ → ℝ := fun s => D (s + 1) - (1 / (m s : ℝ)) * D s with hψ
  set ρ : ℕ → ℝ := fun s => lyapAvg α lam E (N (s + 1))
      - (2 * lyapAvg α lam E (2 * N s) - lyapAvg α lam E (N s))
      - (2 / (m s : ℝ)) * D s with hρ
  have hψb : ∀ s, |ψ s| ≤ ε₂ s := by
    intro s
    have h := hstep₂ s
    simpa only [hD, hψ] using h
  have hρb : ∀ s, |ρ s| ≤ ε₁ s := by
    intro s
    have h := hstep₁ s
    have hρ' : ρ s = lyapAvg α lam E (N (s + 1)) + (1 - 2 / (m s : ℝ)) * lyapAvg α lam E (N s)
        - (2 - 2 / (m s : ℝ)) * lyapAvg α lam E (2 * N s) := by
      rw [hρ, hD]; ring
    rw [hρ']; exact h
  have hDrec : ∀ s, D (s + 1) = (1 / (m s : ℝ)) * D s + ψ s := by
    intro s
    rw [hψ]; ring
  have hstepaff : ∀ s, lyapAvg α lam E (N (s + 1)) = (2 * lyapAvg α lam E (2 * N s)
      - lyapAvg α lam E (N s)) + (2 / (m s : ℝ)) * D s + ρ s := by
    intro s
    rw [hρ]; ring
  -- the exact telescoping identity
  have hident : ∀ S, lyapAvg α lam E (N S) + lyapAvg α lam E (N 0)
      - 2 * lyapAvg α lam E (2 * N 0) = 2 * D S + ∑ s ∈ Finset.range S, (ρ s - 2 * ψ s) := by
    intro S
    induction S with
    | zero => rw [Finset.range_zero, Finset.sum_empty, add_zero, hD]; ring
    | succ S ih =>
      have hsplit : lyapAvg α lam E (N (S + 1)) + lyapAvg α lam E (N 0)
          - 2 * lyapAvg α lam E (2 * N 0)
          = (lyapAvg α lam E (N S) + lyapAvg α lam E (N 0)
              - 2 * lyapAvg α lam E (2 * N 0))
            + (lyapAvg α lam E (N (S + 1)) - lyapAvg α lam E (N S)) := by ring
      have hdiff : lyapAvg α lam E (N (S + 1)) - lyapAvg α lam E (N S)
          = -2 * D S + (2 / (m S : ℝ)) * D S + ρ S := by
        rw [hstepaff S, hD]; ring
      have hmain : (2 / (m S : ℝ)) * D S = 2 * D (S + 1) - 2 * ψ S := by
        rw [hDrec S]; ring
      rw [hsplit, ih, Finset.sum_range_succ, hdiff, hmain]
      ring
  -- the defect contracts: `D → 0`
  have hDrec_le : ∀ s, |D (s + 1)| ≤ |D s| / 3 + ε₂ s := by
    intro s
    have h := hDrec s
    have hm : (3 : ℝ) ≤ (m s : ℝ) := by exact_mod_cast hm3 s
    have h1 : |(1 / (m s : ℝ)) * D s| ≤ |D s| / 3 := by
      rw [abs_mul, abs_of_nonneg (div_nonneg (by norm_num) (le_of_lt (hmpos s)))]
      have h2 : (1 / (m s : ℝ)) ≤ 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num) hm
      calc (1 / (m s : ℝ)) * |D s| ≤ (1 / 3) * |D s| :=
            mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        _ = |D s| / 3 := by ring
    calc |D (s + 1)| = |(1 / (m s : ℝ)) * D s + ψ s| := by rw [h]
      _ ≤ |(1 / (m s : ℝ)) * D s| + |ψ s| := abs_add_le _ _
      _ ≤ |D s| / 3 + ε₂ s := add_le_add h1 (hψb s)
  have hDtolim : Tendsto D atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    simp only [Real.dist_eq, sub_zero]
    intro e he
    have hε₂tend : Tendsto ε₂ atTop (nhds 0) := hs₂.tendsto_atTop_zero
    have hev : ∀ᶠ s in atTop, ε₂ s < e / 4 :=
      hε₂tend.eventually (eventually_lt_nhds (by linarith))
    obtain ⟨S₀, hS₀⟩ := eventually_atTop.mp hev
    have h3t : Tendsto (fun t : ℕ => (3 : ℝ) ^ t) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    obtain ⟨t₀, ht₀⟩ := (h3t.eventually_gt_atTop (4 * |D S₀| / e)).exists
    have hD0t : |D S₀| / 3 ^ t₀ < e / 4 := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ) ^ t₀)]
      rw [div_lt_iff₀ he] at ht₀
      nlinarith [ht₀, he]
    have hiter : ∀ k, |D (S₀ + k)| ≤ |D S₀| / 3 ^ k + (e / 4) * (3 / 2) := by
      intro k
      induction k with
      | zero => simp only [pow_zero, div_one, add_zero]; linarith [le_abs_self (D S₀)]
      | succ k ih =>
        have hrec := hDrec_le (S₀ + k)
        have hε : ε₂ (S₀ + k) < e / 4 := hS₀ (S₀ + k) (Nat.le_add_right S₀ k)
        have h3k : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
        calc |D (S₀ + (k + 1))| = |D ((S₀ + k) + 1)| := by ring_nf
          _ ≤ |D (S₀ + k)| / 3 + ε₂ (S₀ + k) := hrec
          _ ≤ (|D S₀| / 3 ^ k + (e / 4) * (3 / 2)) / 3 + e / 4 := by linarith
          _ ≤ |D S₀| / 3 ^ (k + 1) + (e / 4) * (3 / 2) := by
              apply le_of_eq
              rw [pow_succ]
              have hne : (3 : ℝ) ^ k ≠ 0 := ne_of_gt h3k
              field_simp
              ring
    refine ⟨S₀ + t₀, fun S hS => ?_⟩
    have hSk : S = S₀ + (S - S₀) := (Nat.add_sub_cancel' (le_trans (Nat.le_add_right S₀ t₀) hS)).symm
    rw [hSk]
    have hk : t₀ ≤ S - S₀ := by omega
    have h1 := hiter (S - S₀)
    have h2 : |D S₀| / 3 ^ (S - S₀) ≤ |D S₀| / 3 ^ t₀ := by
      have h3 : (3 : ℝ) ^ t₀ ≤ (3 : ℝ) ^ (S - S₀) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hk
      have hp1 : (0 : ℝ) < (3 : ℝ) ^ (S - S₀) := by positivity
      have hp2 : (0 : ℝ) < (3 : ℝ) ^ t₀ := by positivity
      rw [div_le_iff₀ hp1, div_mul_eq_mul_div, le_div_iff₀ hp2]
      nlinarith [h3, abs_nonneg (D S₀)]
    linarith [h1, h2, hD0t]
  -- the eventual bound
  have hbound : ∀ S, |lyapAvg α lam E (N S) + lyapAvg α lam E (N 0)
      - 2 * lyapAvg α lam E (2 * N 0)|
      ≤ 2 * |D S| + ∑ s ∈ Finset.range S, ε₁ s + 2 * ∑ s ∈ Finset.range S, ε₂ s := by
    intro S
    rw [hident S]
    have h3 : ∀ s ∈ Finset.range S, |ρ s - 2 * ψ s| ≤ ε₁ s + 2 * ε₂ s := by
      intro s _
      have h4 : |ρ s - 2 * ψ s| ≤ |ρ s| + |2 * ψ s| := by
        have h := abs_add_le (ρ s) (-(2 * ψ s))
        simpa only [sub_eq_add_neg, abs_neg] using h
      have h5 : |2 * ψ s| = 2 * |ψ s| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      rw [h5] at h4
      linarith [h4, hρb s, hψb s]
    have h6 : |∑ s ∈ Finset.range S, (ρ s - 2 * ψ s)|
        ≤ ∑ s ∈ Finset.range S, (ε₁ s + 2 * ε₂ s) :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum h3)
    have h7 : (∑ s ∈ Finset.range S, (ε₁ s + 2 * ε₂ s))
        = (∑ s ∈ Finset.range S, ε₁ s) + 2 * ∑ s ∈ Finset.range S, ε₂ s := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    have h8 : |2 * D S| = 2 * |D S| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    calc |2 * D S + ∑ s ∈ Finset.range S, (ρ s - 2 * ψ s)|
        ≤ |2 * D S| + |∑ s ∈ Finset.range S, (ρ s - 2 * ψ s)| := abs_add_le _ _
      _ ≤ 2 * |D S| + ∑ s ∈ Finset.range S, (ε₁ s + 2 * ε₂ s) := by
          rw [h8]; linarith [h6]
      _ = 2 * |D S| + ∑ s ∈ Finset.range S, ε₁ s + 2 * ∑ s ∈ Finset.range S, ε₂ s := by
          rw [h7]; ring
  have hlim1 : Tendsto (fun S => |lyapAvg α lam E (N S) + lyapAvg α lam E (N 0)
      - 2 * lyapAvg α lam E (2 * N 0)|) atTop
      (nhds |lyap α lam E + lyapAvg α lam E (N 0) - 2 * lyapAvg α lam E (2 * N 0)|) :=
    ((htend.add tendsto_const_nhds).sub tendsto_const_nhds).abs
  have hD0 : Tendsto (fun S => 2 * |D S|) atTop (nhds 0) := by
    have h := hDtolim.abs.const_mul (2 : ℝ)
    simpa using h
  have h1t : Tendsto (fun S => ∑ s ∈ Finset.range S, ε₁ s) atTop (nhds (∑' s, ε₁ s)) :=
    hs₁.hasSum.tendsto_sum_nat
  have h2t : Tendsto (fun S => 2 * ∑ s ∈ Finset.range S, ε₂ s) atTop
      (nhds (2 * (∑' s, ε₂ s))) := hs₂.hasSum.tendsto_sum_nat.const_mul 2
  have hlim2 : Tendsto (fun S => 2 * |D S| + ∑ s ∈ Finset.range S, ε₁ s
      + 2 * ∑ s ∈ Finset.range S, ε₂ s) atTop (nhds ((∑' s, ε₁ s) + 2 * (∑' s, ε₂ s))) := by
    have h := (hD0.add h1t).add h2t
    simpa using h
  exact le_of_tendsto_of_tendsto hlim1 hlim2 (Filter.Eventually.of_forall hbound)

/-- **The Case I scale tower, affine form.**  Same hypotheses as `tower_le_of_scale_step`, but
the conclusion carries the sharp error `5(4C₀+1)·Σ_s e^{−cκQ_s/2}`: no hypothesis on `Σ 1/m_s`
is needed (and `Σ_s e^{−cκQ_s/2} ≤ 2e^{−cκq/2}` when the approximants grow by a factor `2`). -/
theorem tower_le_affine_of_scale_step (lam : ℝ) (K : Set ℝ) (c C C₀ : ℝ)
    (hLDT : HasLDTOn lam K c C) (hC₀ : HasLEBound lam K C₀) (hc1 : c ≤ 1)
    (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 100) (E : ℝ) (hE : E ∈ K) (α : ℝ)
    (N m : ℕ → ℕ) (A : ℕ → ℤ) (Q : ℕ → ℕ)
    (hN0 : 1 ≤ N 0) (hm3 : ∀ s, 3 ≤ m s) (hNsucc : ∀ s, N (s + 1) = m s * N s)
    (hq1 : ∀ s, 1 ≤ Q s) (hcop : ∀ s, Nat.Coprime (Int.natAbs (A s)) (Q s))
    (hqC : ∀ s, C * (κ ^ 2)⁻¹ ≤ (Q s : ℝ))
    (hα : ∀ s, |α - (A s : ℝ) / (Q s : ℝ)| < 1 / ((Q s : ℝ) ^ 2))
    (hNQ : ∀ s, C * (κ ^ 2)⁻¹ * (Q s : ℝ) ≤ (N s : ℝ))
    (hmq : ∀ s, ((2 * m s : ℕ) : ℝ) < Real.exp (c * κ * (Q s : ℝ) / 2))
    (hlev : ∀ s, 100 * κ < lyapAvg α lam (E : ℂ) (N s))
    (hpair : (9 / 10) * lyapAvg α lam (E : ℂ) (N 0) < lyapAvg α lam (E : ℂ) (2 * N 0))
    (hprop : ∀ s, C₀ / (m s : ℝ)
      + 2 * ((4 * C₀ + 1) * Real.exp (-(c * κ * (Q s : ℝ) / 2))) ≤ 10 * κ)
    (hS₁ : Summable fun s => Real.exp (-(c * κ * (Q s : ℝ) / 2))) :
    |lyap α lam (E : ℂ) + lyapAvg α lam (E : ℂ) (N 0)
        - 2 * lyapAvg α lam (E : ℂ) (2 * N 0)|
      ≤ 5 * (4 * C₀ + 1) * (∑' s, Real.exp (-(c * κ * (Q s : ℝ) / 2))) := by
  have hm1 : ∀ s, 1 ≤ m s := fun s => le_trans (by norm_num) (hm3 s)
  have hmpos : ∀ s, (0 : ℝ) < (m s : ℝ) := fun s => by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hm1 s)
  set ε : ℕ → ℝ := fun s => (4 * C₀ + 1) * Real.exp (-(c * κ * (Q s : ℝ) / 2)) with hε
  have hpair_all : ∀ s, (9 / 10) * lyapAvg α lam (E : ℂ) (N s)
      < lyapAvg α lam (E : ℂ) (2 * N s) := by
    intro s
    induction s with
    | zero => exact hpair
    | succ s ih =>
      have hstep := Scale.pairing_step lam K c C C₀ hLDT hC₀ hc1 κ hκ hκ1 E hE α (A s) (Q s)
        (hq1 s) (hcop s) (hqC s) (hα s) (N s) (hNQ s) (hlev s) ih (m s) (hm3 s) (hmq s)
      rw [← hNsucc s] at hstep
      have h2 := (abs_le.mp hstep).2
      have hDle : lyapAvg α lam (E : ℂ) (N s) - lyapAvg α lam (E : ℂ) (2 * N s) ≤ C₀ := by
        have h1 := lyapAvg_le_of_hasLEBound hC₀ hE α (N s)
        have h3 : 0 ≤ lyapAvg α lam (E : ℂ) (2 * N s) := by
          rcases Nat.eq_zero_or_pos (2 * N s) with h | h
          · rw [h]; simp [lyapAvg]
          · obtain ⟨k, hk⟩ : ∃ k, 2 * N s = k + 1 := ⟨2 * N s - 1, by omega⟩
            rw [hk]; exact Scale.lyapAvg_nonneg' α lam (E : ℂ) k
        linarith
      have h4 : (1 / (m s : ℝ)) * (lyapAvg α lam (E : ℂ) (N s)
          - lyapAvg α lam (E : ℂ) (2 * N s)) ≤ C₀ / (m s : ℝ) := by
        rw [div_eq_inv_mul, div_eq_inv_mul, mul_one]
        exact mul_le_mul_of_nonneg_left hDle (inv_nonneg.mpr (le_of_lt (hmpos s)))
      have h5 := hprop s
      have h6 := hlev (s + 1)
      have h7 : lyapAvg α lam (E : ℂ) (N (s + 1)) - lyapAvg α lam (E : ℂ) (2 * N (s + 1))
          ≤ C₀ / (m s : ℝ) + 2 * ε s := by
        rw [hε]; linarith [h2, h4]
      have h8 : C₀ / (m s : ℝ) + 2 * ε s ≤ 10 * κ := by
        rw [hε]; exact h5
      linarith [h7, h8, h6]
  have hstep₁ : ∀ s, |lyapAvg α lam (E : ℂ) (N (s + 1))
      + (1 - 2 / (m s : ℝ)) * lyapAvg α lam (E : ℂ) (N s)
      - (2 - 2 / (m s : ℝ)) * lyapAvg α lam (E : ℂ) (2 * N s)| ≤ ε s := by
    intro s
    have hmq' : ((m s : ℕ) : ℝ) < Real.exp (c * κ * (Q s : ℝ) / 2) := by
      have h2m : ((m s : ℕ) : ℝ) ≤ ((2 * m s : ℕ) : ℝ) := by push_cast; linarith [hm3 s]
      linarith [hmq s, h2m]
    have hscale := Scale.AvgStep.scale_step_avg lam K c C C₀ hLDT hC₀ hc1 κ hκ hκ1 E hE α (A s)
      (Q s) (hq1 s) (hcop s) (hqC s) (hα s) (N s) (hNQ s) (hlev s) (hpair_all s) (m s)
      (hm3 s) hmq'
    rw [← hNsucc s] at hscale
    rw [hε]; exact hscale
  have hstep₂ : ∀ s, |(lyapAvg α lam (E : ℂ) (N (s + 1))
        - lyapAvg α lam (E : ℂ) (2 * N (s + 1)))
        - (1 / (m s : ℝ)) * (lyapAvg α lam (E : ℂ) (N s)
          - lyapAvg α lam (E : ℂ) (2 * N s))| ≤ 2 * ε s := by
    intro s
    have h := Scale.pairing_step lam K c C C₀ hLDT hC₀ hc1 κ hκ hκ1 E hE α (A s) (Q s)
      (hq1 s) (hcop s) (hqC s) (hα s) (N s) (hNQ s) (hlev s) (hpair_all s) (m s) (hm3 s) (hmq s)
    rw [← hNsucc s] at h
    rw [hε]; exact h
  have hsum : Summable ε := by
    rw [hε]
    exact hS₁.mul_left (4 * C₀ + 1)
  have hmain := tower_le_affine α lam (E : ℂ) N m ε (fun s => 2 * ε s) hN0 hm3 hNsucc hsum
    (hsum.mul_left 2) hstep₁ hstep₂
  have h1 : (∑' s, ε s) = (4 * C₀ + 1) * (∑' s, Real.exp (-(c * κ * (Q s : ℝ) / 2))) := by
    rw [hε, tsum_mul_left]
  have h2 : (∑' s, 2 * ε s) = 2 * (4 * C₀ + 1)
      * (∑' s, Real.exp (-(c * κ * (Q s : ℝ) / 2))) := by
    rw [hε, tsum_mul_left, tsum_mul_left]
    ring
  rw [h1, h2] at hmain
  linarith [hmain]


/-! ## 6. The geometric decay of the tower weights

For a tower whose approximants grow at least by a factor `2` per stage (`2 Q_s ≤ Q_{s+1}`) and
whose first approximant is `q`, the weight sum `Σ_s e^{−cκQ_s/2}` is comparable to its first
term: with `ρ = e^{−cκq/2} ≤ 1/6`,

  `Σ_s e^{−cκQ_s/2} ≤ Σ_s ρ^{2^s} ≤ Σ_s ρ^{s+1} = ρ/(1−ρ) ≤ (6/5)ρ`.

This is the `hgeo` hypothesis of `chain_of_tower_data` (and hence the `6ε₀` slack of the
`hchain` margin of `prop9_final_of_selection`). -/

theorem tsum_exp_decay_le {c κ q : ℝ} {Q : ℕ → ℕ} (hκc : 0 < c * κ)
    (hQ0 : q ≤ (Q 0 : ℝ)) (hQ : ∀ s, 2 * Q s ≤ Q (s + 1))
    (hρ : Real.exp (-(c * κ * q / 2)) ≤ 1 / 6) :
    (∑' s, Real.exp (-(c * κ * (Q s : ℝ) / 2)))
      ≤ (6 / 5) * Real.exp (-(c * κ * q / 2)) := by
  set ρ : ℝ := Real.exp (-(c * κ * q / 2)) with hρdef
  have hρpos : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ ≤ 1 := le_trans hρ (by norm_num)
  have hρ6 : ρ ≤ 1 / 6 := hρ
  -- `Q s ≥ q · 2^s`
  have hQge : ∀ s, q * 2 ^ s ≤ (Q s : ℝ) := by
    intro s
    induction s with
    | zero => simpa using hQ0
    | succ s ih =>
      have h2 : (2 : ℝ) * (Q s : ℝ) ≤ (Q (s + 1) : ℝ) := by exact_mod_cast hQ s
      calc q * 2 ^ (s + 1) = 2 * (q * 2 ^ s) := by rw [pow_succ]; ring
        _ ≤ 2 * (Q s : ℝ) := by linarith
        _ ≤ (Q (s + 1) : ℝ) := h2
  -- each term is dominated by `ρ^{2^s}`
  have hterm : ∀ s, Real.exp (-(c * κ * (Q s : ℝ) / 2)) ≤ ρ ^ (2 ^ s) := by
    intro s
    have h1 : -(c * κ * (Q s : ℝ) / 2) ≤ -(c * κ * (q * 2 ^ s) / 2) := by
      have h2 := hQge s
      nlinarith [hκc, h2]
    calc Real.exp (-(c * κ * (Q s : ℝ) / 2)) ≤ Real.exp (-(c * κ * (q * 2 ^ s) / 2)) :=
          Real.exp_le_exp.mpr h1
      _ = ρ ^ (2 ^ s) := by
          rw [hρdef, ← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
  -- `ρ^{2^s} ≤ ρ^{s+1}` and the geometric series
  have hterm2 : ∀ s, ρ ^ (2 ^ s) ≤ ρ ^ (s + 1) := by
    intro s
    refine pow_le_pow_of_le_one (le_of_lt hρpos) hρ1 ?_
    have h : s < 2 ^ s := Nat.lt_two_pow_self
    omega
  have hsum2 : Summable fun s : ℕ => ρ ^ (s + 1) := by
    have h := (summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_pos hρpos]; exact lt_of_le_of_lt hρ6 (by norm_num))).mul_left ρ
    refine h.congr (fun s => ?_)
    rw [pow_succ]
    ring
  have hsum1 : Summable fun s : ℕ => ρ ^ (2 ^ s) := by
    refine Summable.of_nonneg_of_le (fun s => by positivity) hterm2 hsum2
  have hgeosum : (∑' s : ℕ, ρ ^ s) = 1 / (1 - ρ) := by
    have := tsum_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_pos hρpos]; exact lt_of_le_of_lt hρ6 (by norm_num))
    simpa using this
  have hsum0 : Summable fun s : ℕ => Real.exp (-(c * κ * (Q s : ℝ) / 2)) :=
    Summable.of_nonneg_of_le (fun s => Real.exp_nonneg _) hterm hsum1
  calc (∑' s, Real.exp (-(c * κ * (Q s : ℝ) / 2))) ≤ ∑' s : ℕ, ρ ^ (2 ^ s) :=
        Summable.tsum_le_tsum hterm hsum0 hsum1
    _ ≤ ∑' s : ℕ, ρ ^ (s + 1) := Summable.tsum_le_tsum hterm2 hsum1 hsum2
    _ = ρ * (∑' s : ℕ, ρ ^ s) := by
        rw [← tsum_mul_left]
        exact tsum_congr (fun s => by rw [pow_succ]; ring)
    _ = ρ / (1 - ρ) := by rw [hgeosum]; ring
    _ ≤ (6 / 5) * ρ := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - ρ)]
        nlinarith [hρ6, hρpos]

end Work.TMComp.C7Aux
