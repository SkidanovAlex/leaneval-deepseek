/-
# `radial_mslot_le_cd6` — the mixed slots of a product with a **radial** multiplier

A `z`-only factor `z ↦ r z` whose `D_z`-iterates up to order six are bounded by `K` costs only
`K²` in the level-six weighted integrand: for `1 ≤ i`, `i + j ≤ 6`,

`(D_z^j D_θ^i (r·g)(z,θ) · W)² ≤ 200704 · K² · HkIntegrand α 6 g z θ`.

Since `D_θ` annihilates the radial factor, the Leibniz rule for `D_z^j D_θ^i` degenerates:
only the angular derivatives of `g` survive, with `D_z`-derivatives of `r` as scalar
coefficients (`D_z^j D_θ^i (r·g) = Σ_{b≤j} C(j,b) (D_z^b r)(D_z^{j-b}D_θ^i g)`, supplied here
as the hypothesis `hMx`).  Each surviving `g`-slot is a mixed slot of `g` of order
`i + (j-b) ≤ 6`, so `sq_le_HkIntegrand_mixed` bounds it by `HkIntegrand α 6 g`, and the scalar
factor is handled by Cauchy–Schwarz on the `j+1 ≤ 7` terms together with the binomial bound
`C(j,b) ≤ 2^j ≤ 2^6 = 64`.  The constant is the resulting `7² · 64² = 49 · 4096 = 200704`.

-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Nat.Choose.Bounds
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux

set_option linter.unusedVariables false

/-- `x² ≤ y²` from `|x| ≤ y` (with `y` allowed to be any real number). -/
private theorem sq_le_sq_of_abs_le {x y : ℝ} (h : |x| ≤ y) : x ^ 2 ≤ y ^ 2 :=
  calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    _ ≤ y ^ 2 := pow_le_pow_left₀ (abs_nonneg x) h 2

/-- Every binomial coefficient `n.choose k` with `n ≤ 6` is at most `2 ^ 6 = 64`. -/
private theorem choose_le_64 {n k : ℕ} (hn : n ≤ 6) : (n.choose k : ℝ) ≤ 64 := by
  have h2 : 2 ^ n ≤ 64 := by
    calc 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn
      _ = 64 := by norm_num
  exact_mod_cast le_trans (Nat.choose_le_two_pow n k) h2

theorem radial_mslot_le_cd6 {α K : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hMx : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 6 →
      Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i g z θ))
    (hKb : ∀ b : ℕ, b ≤ 6 → |Work.Elliptic.DzdIter b r z| ≤ K)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 6) :
    (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
  have hj6 : j ≤ 6 := by omega
  -- the summands of the Leibniz expansion, with the weight already distributed
  set Y : ℕ → ℝ := fun b => (j.choose b : ℝ) * (Work.Elliptic.DzdIter b r z
    * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ)) with hY
  have hsplit : Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
        * Work.Spaces.Wt α z θ = ∑ b ∈ Finset.range (j + 1), Y b := by
    rw [hMx j i hi hij, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [hY]; ring
  rw [hsplit]
  have hHk : (0 : ℝ) ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 g z θ
  have hcard : ((Finset.range (j + 1)).card : ℝ) = (j : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  -- Cauchy–Schwarz on the `j+1` summands
  have hcs : (∑ b ∈ Finset.range (j + 1), Y b) ^ 2
      ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1), (Y b) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (j + 1))
      (fun _ : ℕ => (1 : ℝ)) Y
    simpa [hcard] using h
  -- each summand: binomial coefficient, radial factor, surviving `g`-slot
  have hper : ∀ b ∈ Finset.range (j + 1), (Y b) ^ 2
      ≤ 4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
    intro b hb
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hb6 : b ≤ 6 := by omega
    have hsub : i + (j - b) ≤ 6 := by omega
    have hch : (j.choose b : ℝ) ≤ 64 := choose_le_64 hj6
    have hch2 : (j.choose b : ℝ) ^ 2 ≤ 64 ^ 2 :=
      pow_le_pow_left₀ (by positivity) hch 2
    have hD : (Work.Elliptic.DzdIter b r z) ^ 2 ≤ K ^ 2 :=
      sq_le_sq_of_abs_le (hKb b hb6)
    have hYg : (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ i (j - b) hi hsub
    have hYsq : (Y b) ^ 2 = (j.choose b : ℝ) ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2
        * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      simp only [hY]; ring
    rw [hYsq]
    calc (j.choose b : ℝ) ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2
          * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ (64 ^ 2 * K ^ 2) * Work.Spaces.HkIntegrand α 6 g z θ :=
          mul_le_mul (mul_le_mul hch2 hD (sq_nonneg _) (sq_nonneg _)) hYg
            (sq_nonneg _) (by positivity)
      _ = 4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by norm_num
  have hsum2 : ∑ b ∈ Finset.range (j + 1), (Y b) ^ 2
      ≤ ∑ _b ∈ Finset.range (j + 1),
          (4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) :=
    Finset.sum_le_sum hper
  have hsum3 : ∑ _b ∈ Finset.range (j + 1),
        (4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ)
      = ((j : ℝ) + 1) * (4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hj1 : (j : ℝ) + 1 ≤ 7 := by
    have : (j : ℝ) ≤ 6 := by exact_mod_cast hj6
    linarith
  have hjj : ((j : ℝ) + 1) * ((j : ℝ) + 1) ≤ 49 := by nlinarith [hj1]
  have h4096 : (0 : ℝ) ≤ 4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg K)) hHk
  calc (∑ b ∈ Finset.range (j + 1), Y b) ^ 2
      ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1), (Y b) ^ 2 := hcs
    _ ≤ ((j : ℝ) + 1) * ∑ _b ∈ Finset.range (j + 1),
          (4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = ((j : ℝ) + 1)
          * (((j : ℝ) + 1) * (4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ)) := by
        rw [hsum3]
    _ = (((j : ℝ) + 1) * ((j : ℝ) + 1))
          * (4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by ring
    _ ≤ 49 * (4096 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) :=
        mul_le_mul_of_nonneg_right hjj h4096
    _ = 200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux
