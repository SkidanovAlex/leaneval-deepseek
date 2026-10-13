import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.radialMul_field
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialBounded6_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5.Atoms

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# `radialBounded5_majorant` — a bounded radial factor is a bounded multiplier on `ℋ⁵`

The claim is purely pointwise.  Let `r : ℝ → ℝ` be a radial factor whose one-dimensional
`D_z`-iterates (`DzdIter`, i.e. `z ↦ (z ∂_z)^k r`) are bounded by `Br` up to order `5`, and let
`g` be `C^∞` on the quadrant.  Then, at every interior point `(z,θ)`,

`HkIntegrand α 5 (r·g) ≤ 10^6 · Br² · HkIntegrand α 5 g`.

This is the level-`5` instance of the sibling `radialBounded6_majorant`
(`Submission/Work/FTS/StrongPersist/H6Rows/Npair6SupAux/radialBounded6_majorant.lean`), and the
proof is the same one; the constants are recomputed for `k = 5`.  The two ingredients are

* the Leibniz rules for a radial factor, `Work.FTS.OpenPkg.leibniz_rad_Dz` and
  `Work.FTS.OpenPkg.leibniz_rad_mixed`:
  `D_z^j(r·g) = ∑_{b≤j} C(j,b) (D_z^b r)(D_z^{j-b} g)` and
  `D_z^jD_θ^i(r·g) = ∑_{b≤j} C(j,b) (D_z^b r)(D_z^{j-b}D_θ^i g)` (all the `D_θ`-derivatives
  fall on `g`, since `r` is constant in `θ`);
* the weighted Cauchy–Schwarz bound `sum_choose_mul_sq_le` for such a Leibniz sum, in which the
  binomial coefficients cost the universal factor `10^4` and every slot
  `D_z^{j-b}D_θ^i g` is priced by the whole integrand `HkIntegrand α 5 g`
  (`Work.Spaces.sq_le_HkIntegrand_z`, `Work.Spaces.sq_le_HkIntegrand_mixed`).

There are `6` pure slots and `6·6 = 36` mixed slots, so the total cost is
`42 · 10^4 ≤ 10^6`.  No smoothness of `g` beyond `C^∞` on the open quadrant is used, and no
integrability at all: the statement is a pointwise majorant of the integrand.
-/

/-- **Weighted Cauchy–Schwarz for a Leibniz sum.**  For `n ≤ 5`, a family `A` bounded by `Br` and
a family `X` whose squares are bounded by `M`, the square of the binomial Leibniz sum
`∑_{b≤n} C(n,b)·(A b·X b)` is at most `10^4 · Br² · M`.

The constant is very generous: `∑_b C(n,b)² ≤ 1024` (as `C(n,b) ≤ 2^n ≤ 32`) and the
Cauchy–Schwarz cardinal factor is at most `6`, giving `6 · 1024 · Br² M = 6144 · Br² M
≤ 10^4 · Br² M`. -/
private theorem sum_choose_mul_sq_le {n : ℕ} (hn : n ≤ 5) {Br M : ℝ} (hBr : 0 ≤ Br)
    (hM : 0 ≤ M) {A X : ℕ → ℝ} (hA : ∀ b ≤ n, |A b| ≤ Br) (hX : ∀ b ≤ n, X b ^ 2 ≤ M) :
    (∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (A b * X b)) ^ 2
      ≤ 10 ^ 4 * Br ^ 2 * M := by
  -- the sum of the squared binomial coefficients
  have hC : (∑ b ∈ Finset.range (n + 1), ((n.choose b : ℝ)) ^ 2) ≤ 1024 := by
    have h1 : ∀ b ∈ Finset.range (n + 1),
        ((n.choose b : ℝ)) ^ 2 ≤ 32 * ((n.choose b : ℝ)) := by
      intro b _
      have hb2 : n.choose b ≤ 32 := by
        have h : n.choose b ≤ 2 ^ n := Nat.choose_le_two_pow n b
        have h2 : 2 ^ n ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hn
        omega
      have hc0 : (0 : ℝ) ≤ (n.choose b : ℝ) := Nat.cast_nonneg _
      have hc32 : ((n.choose b : ℝ)) ≤ 32 := by exact_mod_cast hb2
      nlinarith
    calc (∑ b ∈ Finset.range (n + 1), ((n.choose b : ℝ)) ^ 2)
        ≤ ∑ b ∈ Finset.range (n + 1), 32 * ((n.choose b : ℝ)) := Finset.sum_le_sum h1
      _ = 32 * ∑ b ∈ Finset.range (n + 1), ((n.choose b : ℝ)) := by rw [Finset.mul_sum]
      _ = 32 * (2 : ℝ) ^ n := by
            rw [← Nat.cast_sum, Nat.sum_range_choose]
            push_cast
            ring
      _ ≤ 1024 := by
            have h2n : (2 : ℝ) ^ n ≤ 2 ^ 5 := pow_le_pow_right₀ (by norm_num) hn
            norm_num at h2n ⊢
            linarith
  -- Cauchy–Schwarz with the binomial weights
  have hcs : (∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b|) ^ 2
      ≤ (∑ b ∈ Finset.range (n + 1), ((n.choose b : ℝ)) ^ 2)
        * ∑ b ∈ Finset.range (n + 1), |X b| ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n + 1)) _ _
  rw [show (∑ b ∈ Finset.range (n + 1), |X b| ^ 2)
      = ∑ b ∈ Finset.range (n + 1), X b ^ 2 from
        Finset.sum_congr rfl fun b _ => sq_abs (X b)] at hcs
  have h2 : (∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b|) ^ 2
      ≤ 1024 * ∑ b ∈ Finset.range (n + 1), X b ^ 2 :=
    le_trans hcs (mul_le_mul_of_nonneg_right hC (Finset.sum_nonneg fun b _ => sq_nonneg _))
  -- each square is bounded by `M`
  have h3 : ∑ b ∈ Finset.range (n + 1), X b ^ 2 ≤ ((n + 1 : ℕ) : ℝ) * M := by
    calc ∑ b ∈ Finset.range (n + 1), X b ^ 2
        ≤ ∑ _b ∈ Finset.range (n + 1), M :=
          Finset.sum_le_sum fun b hb => hX b (by simpa [Finset.mem_range] using hb)
      _ = ((n + 1 : ℕ) : ℝ) * M := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h3' : ∑ b ∈ Finset.range (n + 1), X b ^ 2 ≤ 6 * M := by
    refine le_trans h3 ?_
    have hn6 : ((n + 1 : ℕ) : ℝ) ≤ 6 := by
      have : n + 1 ≤ 6 := by omega
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hn6 hM
  -- the absolute-value bound on the Leibniz sum
  have h1 : |∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (A b * X b)|
      ≤ Br * ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b| := by
    calc |∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (A b * X b)|
        ≤ ∑ b ∈ Finset.range (n + 1), |(n.choose b : ℝ) * (A b * X b)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |A b * X b| := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose b))]
      _ = ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (|A b| * |X b|) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [abs_mul]
      _ ≤ ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (Br * |X b|) := by
          refine Finset.sum_le_sum fun b hb => ?_
          have hb' : b ≤ n := by simpa [Finset.mem_range] using hb
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hA b hb') (abs_nonneg _))
            (Nat.cast_nonneg (n.choose b))
      _ = Br * ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by ring
  calc (∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (A b * X b)) ^ 2
      = |∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (A b * X b)| ^ 2 :=
        (sq_abs _).symm
    _ ≤ (Br * ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = Br ^ 2 * (∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b|) ^ 2 := by ring
    _ ≤ Br ^ 2 * (1024 * ∑ b ∈ Finset.range (n + 1), X b ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg Br)
    _ ≤ Br ^ 2 * (1024 * (6 * M)) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg Br)
        exact mul_le_mul_of_nonneg_left h3' (by norm_num)
    _ ≤ 10 ^ 4 * Br ^ 2 * M := by
        have hB2 : (0 : ℝ) ≤ Br ^ 2 := sq_nonneg Br
        nlinarith [hB2, hM]

/-- A radial factor all of whose `D_z`-iterates of order `≤ 5` are bounded by `Br` is a bounded multiplier on the weighted `ℋ⁵`-integrand. -/
theorem radialBounded5_majorant :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (Br : ℝ),
      Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => r z) →
      Work.FTS.EllipticEst.SmoothOpen g → 0 ≤ Br →
      (∀ b : ℕ, b ≤ 5 → ∀ z : ℝ, 0 ≤ z → |Work.Elliptic.DzdIter b r z| ≤ Br) →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α 5 (fun z θ => r z * g z θ) z θ
          ≤ K * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ := by
  refine ⟨10 ^ 6, by norm_num, ?_⟩
  intro α r g Br hr hg hBr hbdd z θ hz hθ0 hθ1
  have hzI : z ∈ Set.Ioi (0 : ℝ) := hz
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hHg : 0 ≤ Work.Spaces.HkIntegrand α 5 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 5 g z θ
  have hM0 : (0 : ℝ) ≤ 10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Br)) hHg
  -- the pure `D_z` slot, priced by the whole integrand
  have hz1 : ∀ i : ℕ, i ≤ 5 →
      (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ 10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ := by
    intro i hi
    have hleib := Work.FTS.OpenPkg.leibniz_rad_Dz r g hr hg i z hzI θ hθI
    have hfac : (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.DzIter (i - b) g z θ))
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))
        = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z
              * (Work.Spaces.DzIter (i - b) g z θ
                * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hleib, hfac]
    exact sum_choose_mul_sq_le (n := i) hi hBr hHg
      (fun b hb => hbdd b (by omega) z hz.le)
      (fun b hb => Work.Spaces.sq_le_HkIntegrand_z α 5 g z θ (i - b) (by omega))
  -- the mixed slots, priced by the whole integrand
  have hm1 : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 5 →
      (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ 10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ := by
    intro i j hi hij
    have hleib := Work.FTS.OpenPkg.leibniz_rad_mixed r g hr hg j i hi z hzI θ hθI
    have hfac : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i g z θ))
          * Work.Spaces.Wt α z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z
              * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hleib, hfac]
    exact sum_choose_mul_sq_le (n := j) (by omega) hBr hHg
      (fun b hb => hbdd b (by omega) z hz.le)
      (fun b hb => Work.Spaces.sq_le_HkIntegrand_mixed α 5 g z θ i (j - b) hi (by omega))
  -- the two sums
  have hS1 : (∑ i ∈ Finset.range (5 + 1),
        (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 6 * (10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ) := by
    have h := Finset.sum_le_card_nsmul (Finset.range (5 + 1))
      (fun i => (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      (10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ)
      (fun i hi => hz1 i (by have h := Finset.mem_range.mp hi; omega))
    refine le_trans h (le_of_eq ?_)
    rw [Finset.card_range, nsmul_eq_mul]
    norm_num
  have hS2 : (∑ i ∈ Finset.range (5 + 1), ∑ j ∈ Finset.range (5 + 1),
        if 1 ≤ i ∧ i + j ≤ 5 then
          (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ 36 * (10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ) := by
    have hinner : ∀ i : ℕ, (∑ j ∈ Finset.range (5 + 1),
          if 1 ≤ i ∧ i + j ≤ 5 then
            (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ 6 * (10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ) := by
      intro i
      have h := Finset.sum_le_card_nsmul (Finset.range (5 + 1))
        (fun j => if 1 ≤ i ∧ i + j ≤ 5 then
            (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        (10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ)
        (fun j _ => by
          split_ifs with hguard
          · exact hm1 i j hguard.1 hguard.2
          · exact hM0)
      refine le_trans h (le_of_eq ?_)
      rw [Finset.card_range, nsmul_eq_mul]
      norm_num
    calc (∑ i ∈ Finset.range (5 + 1), ∑ j ∈ Finset.range (5 + 1),
          if 1 ≤ i ∧ i + j ≤ 5 then
            (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ _i ∈ Finset.range (5 + 1),
            (6 * (10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ)) :=
          Finset.sum_le_sum fun i _ => hinner i
      _ = 36 * (10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hunf : Work.Spaces.HkIntegrand α 5 (fun z θ => r z * g z θ) z θ
      = (∑ i ∈ Finset.range (5 + 1),
            (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (5 + 1), ∑ j ∈ Finset.range (5 + 1),
            if 1 ≤ i ∧ i + j ≤ 5 then
              (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
            else 0 := rfl
  rw [hunf]
  refine le_trans (add_le_add hS1 hS2) ?_
  have h1 : (0 : ℝ) ≤ Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ :=
    mul_nonneg (sq_nonneg Br) hHg
  nlinarith [h1]

end Work.FTS.StrongEps.H5.Atoms
