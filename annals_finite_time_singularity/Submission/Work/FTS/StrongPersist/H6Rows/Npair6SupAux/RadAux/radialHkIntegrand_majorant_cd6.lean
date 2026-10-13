/-
# `radialHkIntegrand_majorant_cd6` — the pointwise `ℋ⁶`-integrand majorant for a
radial multiplier with bounded `D_z`-iterates

For a radial factor `r : ℝ → ℝ` whose `D_z = z∂_z`-iterates up to order `6` are bounded by `K`
at a single point `z > 0`, and an arbitrary `g`, the `ℋ⁶`-integrand of the product
`(z,θ) ↦ r z · g z θ` is bounded at `(z,θ)` by a universal constant times `K²` times the
`ℋ⁶`-integrand of `g`:

`HkIntegrand α 6 (r·g) z θ ≤ C · K² · HkIntegrand α 6 g z θ`  (`z > 0`, `0 < θ < π/2`),

with `C` independent of `α`, `K`, `z`, `θ` (here `C = 10⁸`).

The proof is a two-slot Cauchy–Schwarz:

* the pure `D_z`-slots are expanded by the (hypothesis) Leibniz rule
  `D_z^j (r·g) = Σ_b C(j,b) (D_z^b r)(D_z^{j-b} g)`, each surviving slot being a genuine slot of
  `HkIntegrand α 6 g` (`Work.Spaces.sq_le_HkIntegrand_z`), and the binomial coefficients of the
  rows `≤ 6` are bounded by `64` (`Nat.choose_le_two_pow`); the `card`-form of Cauchy–Schwarz
  (`Finset.sq_sum_le_card_mul_sum_sq`) then gives `200704 = 7·7·4096` per slot;
* the mixed slots are handled the same way with the radial Leibniz rule for
  `D_z^j D_θ^i` (`Work.Spaces.sq_le_HkIntegrand_mixed`), all the angular derivatives falling on
  `g` because `r` is radial.

The two slot bounds are `RadAux.radial_zslot_le_cd6` and `RadAux.radial_mslot_le_cd6`; the
assembly sums the seven pure slots and the (at most) `49` mixed slots:

`(7 + 49) · 200704 = 11239424 ≤ 10⁸`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.radial_zslot_le_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.radial_mslot_le_cd6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem radialHkIntegrand_majorant_cd6 :
    ∃ C : ℝ, 0 < C ∧ ∀ {α K : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ},
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j : ℕ, j ≤ 6 →
        Work.Spaces.DzIter j (fun z θ => r z * g z θ) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Work.Elliptic.DzdIter b r z * Work.Spaces.DzIter (j - b) g z θ)) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, 1 ≤ i → i + j ≤ 6 →
        Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i g z θ)) →
      ∀ {z θ : ℝ}, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (∀ b : ℕ, b ≤ 6 → |Work.Elliptic.DzdIter b r z| ≤ K) →
      Work.Spaces.HkIntegrand α 6 (fun z θ => r z * g z θ) z θ
        ≤ C * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro α K r g hDz hMx z θ hz hθ0 hθ1 hKb
  -- unfold the left-hand `ℋ⁶`-integrand into its two slot sums
  conv_lhs => simp only [Work.Spaces.HkIntegrand]
  -- ## the seven pure `D_z`-slots
  have hA : (∑ i ∈ Finset.range 7, (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 7 * (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
    calc (∑ i ∈ Finset.range 7, (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range 7, (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) :=
          Finset.sum_le_sum fun i hi =>
            radial_zslot_le_cd6 (fun j hj => hDz z θ hz hθ0 hθ1 j hj) hKb i (by
              have := Finset.mem_range.mp hi; omega)
      _ = 7 * (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  -- ## the (`≤ 49`) mixed slots
  have hB : (∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
        (if 1 ≤ i ∧ i + j ≤ 6 then (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
          * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 49 * (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
    calc (∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
          (if 1 ≤ i ∧ i + j ≤ 6 then (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ ∑ _i ∈ Finset.range 7, ∑ _j ∈ Finset.range 7,
            (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ 6
          · rw [ite_eq_left hc]
            exact radial_mslot_le_cd6 (fun j i hi hij => hMx z θ hz hθ0 hθ1 j i hi hij) hKb
              i j hc.1 hc.2
          · rw [ite_eq_right hc]
            exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg K))
              (Work.Spaces.HkIntegrand_nonneg α 6 g z θ)
      _ = 49 * (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- ## the assembly
  have hKH : 0 ≤ K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ :=
    mul_nonneg (sq_nonneg K) (Work.Spaces.HkIntegrand_nonneg α 6 g z θ)
  have h1 : (∑ i ∈ Finset.range 7, (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      + (∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
        (if 1 ≤ i ∧ i + j ≤ 6 then (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
          * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ (7 * (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ))
        + (49 * (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ)) := add_le_add hA hB
  have h2 : (7 * (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ))
        + (49 * (200704 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ))
      ≤ 10 ^ 8 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by linarith [hKH]
  exact le_trans h1 h2

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux
