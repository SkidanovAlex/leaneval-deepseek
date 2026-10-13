import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux

open scoped Real Topology

/-- The Leibniz expansion of `D_z^i (r · g)` (a hypothesis of the main statement) bounds
`|D_z^i (r · g) · w / sin(2θ)^{η/2}|` by `(i+1) · 64 · K · √(HkIntegrand α 6 g)`:
there are at most `i + 1 ≤ 7` terms, each carrying a binomial coefficient `≤ 2^i ≤ 64`,
a radial factor bounded by `K`, and one `D_z`-slot `D_z^{i-b} g` of the `H^6` integrand. -/
theorem abs_DzIter_mul_w_le {K : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {α z θ : ℝ}
    (hDz : ∀ j : ℕ, j ≤ 6 →
      Work.Spaces.DzIter j (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.DzIter (j - b) g z θ))
    (hKb : ∀ b : ℕ, b ≤ 6 → |Work.Elliptic.DzdIter b r z| ≤ K)
    (i : ℕ) (hi : i ≤ 6) :
    |Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
      ≤ 448 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ) := by
  have hKnn : 0 ≤ K := le_trans (abs_nonneg (r z)) (by simpa using hKb 0 (by norm_num))
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 g z θ
  have hchoose : ∀ b : ℕ, |((i.choose b : ℕ) : ℝ)| ≤ 64 := by
    intro b
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    have h1 : i.choose b ≤ 2 ^ i := Nat.choose_le_two_pow i b
    have h2 : (2 : ℕ) ^ i ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : (2 : ℕ) ^ 6 = 64 := by norm_num
    have h4 : i.choose b ≤ 64 := by omega
    exact_mod_cast h4
  have hexp : Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
          * (Work.Elliptic.DzdIter b r z
              * (Work.Spaces.DzIter (i - b) g z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := by
    rw [hDz i hi, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hbound : |Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
      ≤ ∑ b ∈ Finset.range (i + 1), 64 * K
          * |Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| := by
    rw [hexp]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun b hb => ?_
    rw [Finset.mem_range] at hb
    have hbK : |Work.Elliptic.DzdIter b r z| ≤ K := hKb b (by omega)
    have h1 : |((i.choose b : ℕ) : ℝ)| * |Work.Elliptic.DzdIter b r z| ≤ 64 * K :=
      mul_le_mul (hchoose b) hbK (abs_nonneg _) (by norm_num)
    calc |((i.choose b : ℕ) : ℝ)
            * (Work.Elliptic.DzdIter b r z
              * (Work.Spaces.DzIter (i - b) g z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))|
        = |((i.choose b : ℕ) : ℝ)| * |Work.Elliptic.DzdIter b r z|
          * |Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| := by
          rw [abs_mul, abs_mul]; ring
      _ ≤ 64 * K * |Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hsum : ∑ b ∈ Finset.range (i + 1), 64 * K
        * |Work.Spaces.DzIter (i - b) g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
      ≤ 448 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ) := by
    have hstep : ∀ b ∈ Finset.range (i + 1),
        64 * K * |Work.Spaces.DzIter (i - b) g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
        ≤ 64 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ) := by
      intro b hb
      rw [Finset.mem_range] at hb
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hKnn)
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (Work.Spaces.sq_le_HkIntegrand_z α 6 g z θ (i - b) (by omega))
    calc ∑ b ∈ Finset.range (i + 1), 64 * K
          * |Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
        ≤ ∑ _b ∈ Finset.range (i + 1),
            64 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ) :=
          Finset.sum_le_sum hstep
      _ = ((i + 1 : ℕ) : ℝ) * (64 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 7 * (64 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) := by
          refine mul_le_mul_of_nonneg_right ?_
            (mul_nonneg (mul_nonneg (by norm_num) hKnn) (Real.sqrt_nonneg _))
          exact_mod_cast (show i + 1 ≤ 7 by omega)
      _ = 448 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ) := by ring
  exact le_trans hbound hsum

theorem radial_zslot_le_cd6 {K : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {α z θ : ℝ}
    (hDz : ∀ j : ℕ, j ≤ 6 →
      Work.Spaces.DzIter j (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.DzIter (j - b) g z θ))
    (hKb : ∀ b : ℕ, b ≤ 6 → |Work.Elliptic.DzdIter b r z| ≤ K)
    (i : ℕ) (hi : i ≤ 6) :
    (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 6 g z θ
  have hfinal := abs_DzIter_mul_w_le (α := α) (θ := θ) hDz hKb i hi
  have hsq : (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ (448 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) ^ 2 := by
    have h1 : |Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| ^ 2
        ≤ (448 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hfinal 2
    rwa [sq_abs] at h1
  calc (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ (448 * K * Real.sqrt (Work.Spaces.HkIntegrand α 6 g z θ)) ^ 2 := hsq
    _ = 200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hHnn]
        ring

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux
