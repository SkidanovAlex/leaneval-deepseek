import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.Base
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.TransportS.T2Sup.smainBound
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbSub.slotWeightBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology

/-! ## The `a₁ = a` half of the `A1`-small row

The row `rowA1SmallPair` pairs a leaf weight `ρ` of the transport unfolding with the two
slots `D_z^{b+1-b₁}D_θ^{a-a₁} f` and `D_z^bD_θ^a f` of the level-six datum `f`, under the
"small pair" constraints `a₁ + b₁ ≤ 2`, `a₁ ≥ 1`, `a₁ ≤ a`, `b₁ ≤ b`, `a + b ≤ 6`.

Both slots have total order `≤ 6`: the first because
`(a - a₁) + (b + 1 - b₁) = a + b + 1 - (a₁ + b₁) ≤ a + b ≤ 6`, the second by `hab`.

* In the case `1 ≤ a - a₁` the first slot carries a `θ`-derivative and the statement is
  exactly the already-proved `slotWeightBound` (the leaf weight is dominated by the slot
  weight `slotW α a` of the *second* slot, and both slots are dominated by `HkIntegrand`).
* In the remaining case `a - a₁ = 0` (i.e. `a = a₁`, so `a ≥ 1`) the first slot is a pure
  `D_z`-slot, whose weight is `Whz` rather than `Wm`.  The hypothesis `hne` excludes
  precisely the only combination in which this fails: the leaf weight `w² sin(2θ)^{-γ}`
  (`= leafGam α`, admissible here because `a ≥ 1`) with `a₁ = a`; the exponent `-γ` of that
  leaf weight is then *larger* than the exponent `-(η+γ)/2` available from the AM–GM over
  the two slots.  For the two surviving leaf weights (`w² sin(2θ)^{-η}` and `w²`) the
  `Whz`-route closes exactly as in `slotWeightBound`, the second slot being compared with
  its `Wm`-square via `sin(2θ)^{-η} ≤ sin(2θ)^{-γ}`. -/

/-- `w z ≥ 0` for every real `z` (`w z = (1+z)²/z²` is a quotient of squares). -/
private theorem w_nonneg_l (z : ℝ) : 0 ≤ Work.Spaces.w z :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- `Whz z θ ≥ 0` on the closed quadrant. -/
private theorem Whz_nonneg_l {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.H2.Whz z θ := by
  rw [Work.FTS.H2.Whz_eq]
  exact div_nonneg (w_nonneg_l z)
    (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)

/-- **AM–GM for two slots sharing the weight `W`**: if the two weighted slots are each
dominated by `H` then so is the product of the two slots times `W²`. -/
private theorem amgm_mul_le {X Y W H : ℝ} (hW : 0 ≤ W)
    (hX : (X * W) ^ 2 ≤ H) (hY : (Y * W) ^ 2 ≤ H) :
    |X| * |Y| * W ^ 2 ≤ H := by
  have h1 : |X| * |Y| * W ^ 2 = |X * W| * |Y * W| := by
    simp only [abs_mul, abs_of_nonneg hW]
    ring
  rw [h1]
  nlinarith [sq_nonneg (|X * W| - |Y * W|), sq_abs (X * W), sq_abs (Y * W), hX, hY]

theorem rowA1SmallPair {α : ℝ} {f : ℝ → ℝ → ℝ} {a b a₁ b₁ : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    (ha₁ : 1 ≤ a₁) (ha₁a : a₁ ≤ a) (hb₁ : b₁ ≤ b) (hab₁ : a₁ + b₁ ≤ 2) (hab : a + b ≤ 6)
    (hne : ¬ (a₁ = a ∧ ρ = Work.FTS.TransportS.leafGam α)) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ * |Work.Spaces.mixed (b + 1 - b₁) (a - a₁) f z θ|
        * |Work.Spaces.mixed b a f z θ| ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
  intro z θ _hz hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  by_cases hcase : 1 ≤ a - a₁
  · -- the first slot carries a `θ`-derivative: `slotWeightBound`
    have huv : (a - a₁) + (b + 1 - b₁) ≤ 6 := by omega
    exact Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbSub.slotWeightBound hα a b
      (a - a₁) (b + 1 - b₁) hab hcase huv hleaf z θ _hz hθ0 hθ1
  · -- the first slot is a pure `D_z`-slot: `a₁ = a`, and `hne` rules out `leafGam`
    have hane : a - a₁ = 0 := by omega
    have haneq : a = a₁ := by omega
    have ha1 : 1 ≤ a := by omega
    -- the leaf weight is dominated by `(Whz)²`
    have hρWhz : ρ z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
      have hsq := (Work.FTS.H2.Whz_Wm_sq α hα z θ hθI).1
      rcases hleaf with h | h | ⟨_, hg⟩
      · rw [h]
        exact le_of_eq hsq.symm
      · simp only [h, Work.FTS.TransportS.leafOne]
        rw [hsq]
        have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg ⟨hθ0, hθ1⟩
        simpa using mul_le_mul_of_nonneg_left h1 (sq_nonneg (Work.Spaces.w z))
      · exact absurd ⟨haneq.symm, hg⟩ hne
    -- the two slots, weighted by `Whz`, are dominated by `HkIntegrand α 6 f`
    have hb6 : b + 1 - b₁ ≤ 6 := by omega
    have hX : (Work.Spaces.mixed (b + 1 - b₁) 0 f z θ * Work.FTS.H2.Whz z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      have h := Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ (b + 1 - b₁) hb6
      simpa only [Work.Spaces.mixed_zero_right, Work.FTS.H2.Whz_eq] using h
    have hWm2 : (Work.FTS.H2.Whz z θ) ^ 2 ≤ (Work.FTS.H2.Wm α z θ) ^ 2 := by
      have hsq := Work.FTS.H2.Whz_Wm_sq α hα z θ hθI
      rw [hsq.1, hsq.2]
      exact mul_le_mul_of_nonneg_left (Work.FTS.H2.rpow_eta_le_gam hα hθI) (sq_nonneg _)
    have hY : (Work.Spaces.mixed b a f z θ * Work.FTS.H2.Whz z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
      have hY1 := Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ a b ha1 hab
      have h2 : (Work.Spaces.mixed b a f z θ * Work.FTS.H2.Whz z θ) ^ 2
          ≤ (Work.Spaces.mixed b a f z θ * Work.FTS.H2.Wm α z θ) ^ 2 := by
        rw [mul_pow, mul_pow]
        exact mul_le_mul_of_nonneg_left hWm2 (sq_nonneg _)
      exact le_trans h2 (by simpa only [Work.FTS.H2.Wm_eq] using hY1)
    have hamgm : |Work.Spaces.mixed (b + 1 - b₁) 0 f z θ| * |Work.Spaces.mixed b a f z θ|
        * (Work.FTS.H2.Whz z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
      amgm_mul_le (Whz_nonneg_l hθI) hX hY
    rw [hane]
    calc ρ z θ * |Work.Spaces.mixed (b + 1 - b₁) 0 f z θ|
          * |Work.Spaces.mixed b a f z θ|
        ≤ (Work.FTS.H2.Whz z θ) ^ 2 * |Work.Spaces.mixed (b + 1 - b₁) 0 f z θ|
            * |Work.Spaces.mixed b a f z θ| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hρWhz (abs_nonneg _)) (abs_nonneg _)
      _ = |Work.Spaces.mixed (b + 1 - b₁) 0 f z θ| * |Work.Spaces.mixed b a f z θ|
            * (Work.FTS.H2.Whz z θ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 6 f z θ := hamgm

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
