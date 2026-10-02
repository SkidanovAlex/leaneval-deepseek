import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.threshold_tools
import Submission.Work.Deep.Nibble.threshold_cond3
import Submission.Work.Deep.Nibble.threshold_cond4
import Submission.Work.Deep.Nibble.threshold_cond5
import Submission.Work.Deep.Nibble.threshold_cond6
import Submission.Work.Deep.Nibble.threshold_cond7

/-!
# The asymptotic side conditions of `cor:sparse_egj`

This module proves `Work.Deep.Nibble.exists_threshold`, the collection of asymptotic
side conditions needed to apply the sparse Erdős–Gyárfás–Lovász corollary
(`cor:sparse_egj`) of Kang--Kelly--Kühn--Methuku--Osthus, Annals 2023, in the form used by
`Work.Deep.Nibble.sparseMatchingStatement_of_EGJStatement`.

The proof is done clause by clause.  Clauses 1--2 are elementary; clauses 3--7 are provided
by the modules `threshold_cond3`, ..., `threshold_cond7` (each of the form: for every
`E > 0` -- resp. `0 < κ < 1`, `R > 0` -- there is a threshold `N` such that the clause holds
for all `n ≥ N` and all `D ≥ n^(1/100)`).  The main theorem takes the sum of the seven
thresholds (positivity of each gives `n ≥ 1` and hence `D ≥ 1`).
-/

set_option autoImplicit false

namespace Work.Deep.Nibble

/-- Assembly of the seven threshold lemmas: this is `exists_threshold` with the exponent
`ε² = (1/(1500 r²))²` replaced by an arbitrary `E > 0` and `r` by an arbitrary `R > 0`.
The clauses are proved one by one and the corresponding thresholds are added up. -/
theorem exists_threshold_aux {E R κ Δ₀ : ℝ} (hE : 0 < E) (hR : 0 < R) (hκ0 : 0 < κ)
    (hκ1 : κ < 1) (_hΔ₀ : 0 < Δ₀) :
    ∃ n₀ : ℝ, 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ (n : ℝ) → ∀ D : ℝ, (n : ℝ) ^ ((1 : ℝ) / 100) ≤ D →
      1 ≤ D ∧
      Δ₀ ≤ (1 + κ) * D ∧
      ((1 + κ) * D) ^ (-E) ≤ κ ∧
      2 * (n : ℝ) * D ≤ Real.exp (((1 + κ) * D) ^ E) ∧
      (n : ℝ) ^ (2 * Real.log n) ≤ Real.exp (((1 + κ) * D) ^ E) ∧
      (1 - κ) * D ^ ((21 : ℝ) / 20) ≥ ((1 + κ) * D) ^ ((26 : ℝ) / 25) ∧
      2 * (n : ℝ) ^ (2 * Real.log n) * Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1 : ℝ) / 20) / R)) < 1 := by
  obtain ⟨N₁₂, hN₁₂, h₁₂⟩ := sparse_egj_conds_1_2 (κ := κ) (Δ₀ := Δ₀) hκ0
  obtain ⟨N₃, hN₃, h₃⟩ := threshold_cond3 (E := E) hE hκ0
  obtain ⟨N₄, hN₄, h₄⟩ := threshold_cond4 (E := E) hE hκ0
  obtain ⟨N₅, hN₅, h₅⟩ := threshold_cond5 (E := E) hE hκ0
  obtain ⟨N₆, hN₆, h₆⟩ := threshold_cond6 hκ0 hκ1
  obtain ⟨N₇, hN₇, h₇⟩ := threshold_cond7 (R := R) hκ0 hR
  refine ⟨1 + N₁₂ + N₃ + N₄ + N₅ + N₆ + N₇, by linarith, ?_⟩
  intro n hn D hD
  have h1 : N₁₂ ≤ (n : ℝ) := by linarith
  have h3 : N₃ ≤ (n : ℝ) := by linarith
  have h4 : N₄ ≤ (n : ℝ) := by linarith
  have h5 : N₅ ≤ (n : ℝ) := by linarith
  have h6 : N₆ ≤ (n : ℝ) := by linarith
  have h7 : N₇ ≤ (n : ℝ) := by linarith
  exact ⟨(h₁₂ n h1 D hD).1, (h₁₂ n h1 D hD).2, h₃ n h3 D hD, h₄ n h4 D hD,
    h₅ n h5 D hD, h₆ n h6 D hD, h₇ n h7 D hD⟩


/-- **The asymptotic side conditions of `cor:sparse_egj`.**  For `r ≥ 2`, `0 < κ < 1/4` and
`Δ₀ > 0` there is `n₀ > 0` such that for every `n ≥ n₀` and every `D ≥ n^{1/100}`, writing
`Δ := (1+κ)D` and `ε := 1/(1500 r²)`, all of the following hold:

1. `1 ≤ D`,
2. `Δ₀ ≤ Δ`                       (so `EGJStatement` applies with `Δ`);
3. `Δ^{-ε²} ≤ κ`                   (the EGJ error term is absorbed in `κ`);
4. `2nD ≤ exp(Δ^{ε²})`             (the number of edges of `𝓗` is `≤ 2nD`);
5. `n^{2 log n} ≤ exp(Δ^{ε²})`     (the family `𝓕` has at most `n^{2 log n}` members);
6. `(1-κ)·D^{21/20} ≥ Δ^{26/25}`   (lower bound for `degreeSum` from `|S| ≥ D^{1/20}`);
7. `2·n^{2 log n}·exp(-(3/8)κ²D^{1/20}/r) < 1`  (the union bound of `thinning`).

All clauses are “for large `n`” statements: `D → ∞` and the conditions are asymptotic in `D`,
except 4. and 5. which use `D ≥ n^{1/100}` (for 4. a case split `D ≤ n` / `D ≥ n` with
`2nD ≤ 2n²` resp. `2nD ≤ 2D²`).  A clean route is `∀ᶠ n in atTop, …` followed by
`Filter.eventually_atTop`. -/
theorem exists_threshold {r : ℕ} (hr : 2 ≤ r) {κ Δ₀ : ℝ} (hκ0 : 0 < κ) (hκ : κ < 1 / 4)
    (hΔ₀ : 0 < Δ₀) :
    ∃ n₀ : ℝ, 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ (n : ℝ) → ∀ D : ℝ, (n : ℝ) ^ ((1 : ℝ) / 100) ≤ D →
      1 ≤ D ∧
      Δ₀ ≤ (1 + κ) * D ∧
      ((1 + κ) * D) ^ (-((1 / (1500 * (r : ℝ) ^ 2)) ^ 2)) ≤ κ ∧
      2 * (n : ℝ) * D ≤ Real.exp (((1 + κ) * D) ^ ((1 / (1500 * (r : ℝ) ^ 2)) ^ 2)) ∧
      (n : ℝ) ^ (2 * Real.log n) ≤ Real.exp (((1 + κ) * D) ^ ((1 / (1500 * (r : ℝ) ^ 2)) ^ 2)) ∧
      (1 - κ) * D ^ ((21 : ℝ) / 20) ≥ ((1 + κ) * D) ^ ((26 : ℝ) / 25) ∧
      2 * (n : ℝ) ^ (2 * Real.log n) * Real.exp (-(3 / 8 * κ ^ 2 * D ^ ((1 : ℝ) / 20) / (r : ℝ))) < 1 := by
  have hr' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hR : 0 < (r : ℝ) := by linarith
  have hR2 : 0 < (r : ℝ) ^ 2 := pow_pos hR 2
  have hden : 0 < 1500 * (r : ℝ) ^ 2 := mul_pos (by norm_num) hR2
  have hfrac : 0 < 1 / (1500 * (r : ℝ) ^ 2) := div_pos one_pos hden
  have hE : 0 < (1 / (1500 * (r : ℝ) ^ 2)) ^ 2 := pow_pos hfrac 2
  exact exists_threshold_aux hE hR hκ0 (by linarith) hΔ₀

end Work.Deep.Nibble
