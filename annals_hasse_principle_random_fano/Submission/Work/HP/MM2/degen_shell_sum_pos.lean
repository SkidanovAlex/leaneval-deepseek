import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.FM3.ell_two_count_free
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MM2.degen_shell_sum
import Submission.Work.HP.MM2.dmin_two_singleton_le_eNorm

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Work.HP

namespace Work.HP.MM2

/-- A `finsum` over a finite set is the sum over the corresponding `Finset`. -/
private lemma finsum_mem_eq_sum_toFinset_pos {α : Type*} (s : Set α) (hs : s.Finite) (f : α → ℝ) :
    (∑ᶠ x ∈ s, f x) = ∑ x ∈ hs.toFinset, f x := by
  have hsupp : Function.support (s.indicator f) ⊆ ↑(hs.toFinset) := by
    intro x hx
    by_contra hxS
    refine hx (Set.indicator_of_notMem (fun h => hxS ?_) _)
    exact Finset.mem_coe.mpr (hs.mem_toFinset.mpr h)
  rw [finsum_mem_def, finsum_eq_finsetSum_of_support_subset (s.indicator f) hsupp]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Set.indicator_of_mem (hs.mem_toFinset.mp (Finset.mem_coe.mp hx))]

/-- Shell sums of `eNorm ^ s` over the degenerate set `{x ≠ 0 : ‖x‖ ≤ X, t·𝔡₂(x) ≤ ‖x‖}`,
valid for **every** `t > 0`, not only `t ≥ 1`.

This is node L0i of the design review with the inessential restriction `1 ≤ t` removed; the
`1 ≤ t` version is stated as `Work.HP.MM2.degen_shell_sum` in
`Submission/Work/HP/MM2/degen_shell_sum.lean`, whose dyadic proof can be copied (that file does
not currently compile: its `hackj` derives `1 ≤ Y` for `Y = X / 2^j` from `1 ≤ X`, which is false;
the correct reason in the branch `t ≤ Y` is that `Finset.filter (eNorm · ≤ Y)` is nonempty, and a
member is nonzero hence of norm `≥ 1`; in the branch `Y < t` the filter is empty because
`t·𝔡₂(x) ≤ eNorm x` and `1 ≤ 𝔡₂(x)` force `t ≤ eNorm x ≤ Y`).  Helpers in that file to copy:
`shell_select`, `shell_pointwise`, `shell_sum_geometric`, `shell_term_le`,
`finsum_mem_eq_sum_toFinset`, `one_le_eNorm_of_ne_zero'`, `dmin_two_singleton_ge_one`.  Do NOT
import `Submission.Work.HP.MM2.degen_shell_sum` or `Submission.Work.HP.MM2.dmin_two_singleton_le_eNorm`
(they are listed here as unfinished); copy or reprove what you need.

Suggested route for `t ≤ 1`: `dmin_two_singleton_le_eNorm` (`𝔡₂(x) ≤ eNorm x` for `x ≠ 0`, via
`Work.HP.Lat.exists_rk_two` and `Work.HP.Lat.detL_ge_one`) gives `Sh(t) ⊆ Sh(1)`, so the `t = 1`
instance of the `t ≥ 1` argument bounds the left side by
`K X^{n+2+s}(1+log X) ≤ K X^{n+2+s}(1+log X)/t^n`. -/
theorem degen_shell_sum_pos (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < (n : ℝ) + 2 + s) :
    ∃ K : ℝ, 0 < K ∧ ∀ X t : ℝ, 1 ≤ X → 0 < t →
      (∑ᶠ x ∈ {x : Fin (n + 1) → ℤ | x ≠ 0 ∧ eNorm x ≤ X ∧
          t * dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ eNorm x}, eNorm x ^ s)
        ≤ K * X ^ ((n : ℝ) + 2 + s) * (1 + Real.log X) / t ^ n := by
  obtain ⟨K, hKpos, hK⟩ := degen_shell_sum n hn s hs
  refine ⟨K, hKpos, ?_⟩
  intro X t hX ht
  rcases le_or_gt 1 t with ht1 | ht1
  · -- Case `1 ≤ t`: this is exactly the `1 ≤ t` shell-sum estimate.
    exact hK X t hX ht1
  -- Case `0 < t < 1`: the degenerate set for `t` is contained in the one for `t = 1`,
  -- since `𝔡₂(x) ≤ ‖x‖` for `x ≠ 0`; then use the `t = 1` instance and `1 ≤ t⁻ⁿ`.
  have htle : t ≤ 1 := le_of_lt ht1
  have hn1 : 1 ≤ n := by omega
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX
  set St : Set (Fin (n + 1) → ℤ) :=
    {x | x ≠ 0 ∧ eNorm x ≤ X ∧ t * dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ eNorm x} with hStdef
  set S1 : Set (Fin (n + 1) → ℤ) :=
    {x | x ≠ 0 ∧ eNorm x ≤ X ∧ 1 * dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ eNorm x} with hS1def
  have hStfin : St.Finite :=
    (MDBasic.finite_eNorm_le (ι := Fin (n + 1)) X).subset (fun v hv => hv.2.1)
  have hS1fin : S1.Finite :=
    (MDBasic.finite_eNorm_le (ι := Fin (n + 1)) X).subset (fun v hv => hv.2.1)
  have hsub : St ⊆ S1 := by
    intro x hx
    obtain ⟨hx0, hxX, -⟩ := hx
    exact ⟨hx0, hxX, by simpa using dmin_two_singleton_le_eNorm n hn1 x hx0⟩
  -- Monotonicity of the `finsum` over an inclusion of sets with nonnegative summands.
  have hmono : (∑ᶠ x ∈ St, eNorm x ^ s) ≤ ∑ᶠ x ∈ S1, eNorm x ^ s := by
    rw [finsum_mem_eq_sum_toFinset_pos St hStfin, finsum_mem_eq_sum_toFinset_pos S1 hS1fin]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx
      rw [Set.Finite.mem_toFinset] at hx ⊢
      exact hsub hx
    · intro x _ _
      exact Real.rpow_nonneg (eNorm_nonneg x) s
  have h1 : (∑ᶠ x ∈ S1, eNorm x ^ s) ≤ K * X ^ ((n : ℝ) + 2 + s) * (1 + Real.log X) := by
    have h := hK X 1 hX le_rfl
    rw [hS1def]
    simpa using h
  have h2 : K * X ^ ((n : ℝ) + 2 + s) * (1 + Real.log X)
      ≤ K * X ^ ((n : ℝ) + 2 + s) * (1 + Real.log X) / t ^ n := by
    have hA : 0 ≤ K * X ^ ((n : ℝ) + 2 + s) * (1 + Real.log X) := by
      have h1 : 0 < X ^ ((n : ℝ) + 2 + s) := Real.rpow_pos_of_pos hX0 _
      have h2 : 0 ≤ Real.log X := Real.log_nonneg hX
      positivity
    have htn_pos : 0 < t ^ n := pow_pos ht n
    have htn_le : t ^ n ≤ 1 := pow_le_one₀ (le_of_lt ht) htle
    have hle : (1 : ℝ) ≤ 1 / t ^ n := by
      rw [le_div_iff₀ htn_pos]; simpa using htn_le
    calc K * X ^ ((n : ℝ) + 2 + s) * (1 + Real.log X)
        = K * X ^ ((n : ℝ) + 2 + s) * (1 + Real.log X) * 1 := by ring
      _ ≤ K * X ^ ((n : ℝ) + 2 + s) * (1 + Real.log X) * (1 / t ^ n) :=
          mul_le_mul_of_nonneg_left hle hA
      _ = K * X ^ ((n : ℝ) + 2 + s) * (1 + Real.log X) / t ^ n := by ring
  exact le_trans hmono (le_trans h1 h2)

end Work.HP.MM2
