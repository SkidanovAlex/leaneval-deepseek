import Mathlib
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMComp.C7Aux.towerAssembly

/-!
# The finite scale tower: the telescoping bound

The finite version of `Work.TMComp.C7Aux.tower_le` (`towerAssembly.lean`).  For a *finite* tower
of scales `N 0 < N 1 < ⋯ < N S` with multipliers `N (s+1) = m s * N s`, `m s ≥ 3`, and per-stage
relations

* `|L_{N(s+1)} + L_{N s} − 2 L_{2N s}| ≤ ε₁ s`
* `|(L_{N(s+1)} − L_{2N(s+1)}) − (1/m s)(L_{N s} − L_{2N s})| ≤ ε₂ s`,

the base/top relation reads

`|L_{N S} + L_{N 0} − 2 L_{2N 0}| ≤ 6|D 0|/m 0 + Σ_{s<S} ε₁ s + 4 Σ_{s<S} ε₂ s`.

The infinite version `tower_le` passes to the limit `S → ∞` (using `Summable` errors and
`lyap ≤ L_N`); here the top of the tower is kept as `L_{N S}`.

**`1 ≤ S` is not removable**: for `S = 0` the identity degenerates to `2 D 0` and the bound
`6 |D 0| / m 0` is smaller than `2 |D 0|` as soon as `m 0 > 3`, which is the generic case
(`N 1 = m 0 * N 0` with `m 0 ≥ 3` arbitrary).  The tower of `rat_tower_lower` always has
`S = s0 + 1 ≥ 1`.
-/

open MeasureTheory Finset
open Work.TMC7Core
open Work.TMComp.C7Aux

namespace Work.TMComp.C7Aux.TowerV3

/-- **The finite scale tower.** -/
theorem finite_tower_bound_v3 (α lam : ℝ) (E : ℂ) (N m : ℕ → ℕ) (ε₁ ε₂ : ℕ → ℝ) (S : ℕ)
    (hS1 : 1 ≤ S)
    (hNsucc : ∀ s, N (s + 1) = m s * N s) (hm3 : ∀ s, 3 ≤ m s)
    (hε₁ : ∀ s < S, 0 ≤ ε₁ s) (hε₂ : ∀ s < S, 0 ≤ ε₂ s)
    (hstep₁ : ∀ s < S, |lyapAvg α lam E (N (s + 1)) + lyapAvg α lam E (N s)
        - 2 * lyapAvg α lam E (2 * N s)| ≤ ε₁ s)
    (hstep₂ : ∀ s < S, |(lyapAvg α lam E (N (s + 1)) - lyapAvg α lam E (2 * N (s + 1)))
        - (1 / (m s : ℝ)) * (lyapAvg α lam E (N s) - lyapAvg α lam E (2 * N s))| ≤ ε₂ s) :
    |lyapAvg α lam E (N S) + lyapAvg α lam E (N 0) - 2 * lyapAvg α lam E (2 * N 0)|
      ≤ 6 * |lyapAvg α lam E (N 0) - lyapAvg α lam E (2 * N 0)| / (m 0 : ℝ)
        + (∑ s ∈ Finset.range S, ε₁ s) + 4 * (∑ s ∈ Finset.range S, ε₂ s) := by
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
  have hψb : ∀ s, s < S → |ψ s| ≤ ε₂ s := by
    intro s hs
    have h := hstep₂ s hs
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
  have hTail : |∑ u ∈ Finset.range S, ψ u * (∑ j ∈ Finset.range S,
        (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0))|
      ≤ 2 * (∑ u ∈ Finset.range S, ε₂ u) := by
    have h1 : |∑ u ∈ Finset.range S, ψ u * (∑ j ∈ Finset.range S,
          (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0))|
        ≤ ∑ u ∈ Finset.range S, |ψ u * (∑ j ∈ Finset.range S,
            (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0))| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : ∀ u ∈ Finset.range S, |ψ u * (∑ j ∈ Finset.range S,
          (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0))|
        ≤ ε₂ u * 2 := by
      intro u hu
      have huS : u < S := Finset.mem_range.mp hu
      have hTnn : 0 ≤ ∑ j ∈ Finset.range S,
          (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0) := by
        refine Finset.sum_nonneg (fun j _ => ?_)
        by_cases h : u < j
        · rw [if_pos h]; positivity
        · rw [if_neg h]
      have hT2 := sum_tail_weight_le hm3 u S
      rw [abs_mul, abs_of_nonneg hTnn]
      exact mul_le_mul (hψb u huS) hT2 hTnn (hε₂ u huS)
    calc |∑ u ∈ Finset.range S, ψ u * (∑ j ∈ Finset.range S,
            (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0))|
        ≤ ∑ u ∈ Finset.range S, |ψ u * (∑ j ∈ Finset.range S,
            (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0))| := h1
      _ ≤ ∑ u ∈ Finset.range S, ε₂ u * 2 := Finset.sum_le_sum h2
      _ = (∑ u ∈ Finset.range S, ε₂ u) * 2 := by rw [Finset.sum_mul]
      _ = 2 * (∑ u ∈ Finset.range S, ε₂ u) := by ring
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
      - 2 * lyapAvg α lam E (2 * N s))| ≤ ∑ s ∈ Finset.range S, ε₁ s := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum (fun s hs => hstep₁ s (Finset.mem_range.mp hs))
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
      ≤ 4 * (∑ u ∈ Finset.range S, ε₂ u) := by
    have h1 : |2 * (∑ u ∈ Finset.range S, ψ u * (∑ j ∈ Finset.range S,
        (if u < j then (Pmul m (u + 1) : ℝ) / (Pmul m j : ℝ) else 0)))|
        ≤ 2 * (2 * (∑ u ∈ Finset.range S, ε₂ u)) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
      exact mul_le_mul_of_nonneg_left (hTail) (by norm_num)
    linarith [h1]
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
    _ ≤ 2 * |D 0| * (3 / (m 0 : ℝ)) + (∑ s ∈ Finset.range S, ε₁ s)
          + 4 * (∑ s ∈ Finset.range S, ε₂ s) := add_le_add (add_le_add hA hβ) hC
    _ = 6 * |D 0| / (m 0 : ℝ) + (∑ s ∈ Finset.range S, ε₁ s)
          + 4 * (∑ s ∈ Finset.range S, ε₂ s) := by ring

end Work.TMComp.C7Aux.TowerV3
