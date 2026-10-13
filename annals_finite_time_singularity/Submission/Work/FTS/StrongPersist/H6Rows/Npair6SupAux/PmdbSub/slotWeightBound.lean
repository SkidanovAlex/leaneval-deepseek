/-
Copyright: work module for the Elgindi finite-time singularity project.

# `slotWeightBound`: a leaf weight against two `ℋ⁶` slots

For every slot `(a,b)` of the `ℋ⁶` pairing (`a + b ≤ 6`), every further slot `(u,v)`
with `u ≥ 1` and `u + v ≤ 6`, and every *leaf* weight `ρ` of the transport unfolding
(`IsLeafW α a ρ`) — i.e. one of `w² sin(2θ)^{-η}`, `w²`, and (for `a ≥ 1`)
`w² sin(2θ)^{-γ}` — the product of the weight with the two slots is pointwise dominated
by the integrand of the squared `H⁶` norm:

`ρ z θ · |D_z^v D_θ^u g| · |D_z^b D_θ^a g| ≤ HkIntegrand α 6 g z θ`  on the open quadrant.

The proof is purely pointwise.  The leaf weight `ρ` is dominated by the slot weight
`slotW α a` of its own slot (`IsLeafW_le`): `(Whz)² = w² sin(2θ)^{-η}` for `a = 0` and
`(Wm)² = w² sin(2θ)^{-γ}` for `a ≥ 1`.  Each of the two slots is separately dominated by
the matching summand of `HkIntegrand α 6 g` — a squared `Whz`-weighted `D_z`-derivative if
the slot carries no `θ`-derivative, a squared `Wm`-weighted mixed derivative otherwise —
and the product of the two slots is closed by AM–GM
(`2|XY| ≤ X² + Y²`), which costs a factor `1/2` on each of the two summands.  For `a = 0`
the `η`-weight `(Whz)²` is compared with the `γ`-weight `(Wm)²` on the `u ≥ 1` slot via
`sin(2θ)^{-η} ≤ sin(2θ)^{-γ}`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbSub

/-! ## Elementary nonnegativity -/

/-- `w z ≥ 0` (for every `z`). -/
private theorem w_nonneg_l (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- `Whz z θ ≥ 0` on the closed quadrant. -/
private theorem Whz_nonneg_l {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.H2.Whz z θ := by
  rw [Work.FTS.H2.Whz_eq]
  exact div_nonneg (w_nonneg_l z)
    (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)

/-- `Wm α z θ ≥ 0` on the closed quadrant. -/
private theorem Wm_nonneg_l (α : ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.H2.Wm α z θ := by
  rw [Work.FTS.H2.Wm_eq, Work.Spaces.Wt, Work.Spaces.wTheta]
  exact mul_nonneg (w_nonneg_l z)
    (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)

/-! ## Single slots are dominated by `HkIntegrand α 6 g` -/

/-- **Every slot of level `≤ 6`, weighted by `Whz`, is dominated by `HkIntegrand α 6 g`.**
If the slot carries a `θ`-derivative (`i ≥ 1`) this is a mixed summand, compared against
the `γ`-weight via `sin(2θ)^{-η} ≤ sin(2θ)^{-γ}`; if `i = 0` it is the pure `D_z`-summand
`i = j ≤ 6`. -/
private theorem slot_whz_sq_le {α : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hα : 0 < α) (_hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {i j : ℕ} (hij : i + j ≤ 6) :
    (Work.Spaces.mixed j i g z θ * Work.FTS.H2.Whz z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  rcases eq_or_ne i 0 with hi | hi
  · subst hi
    simpa only [Work.Spaces.mixed_zero_right, Work.FTS.H2.Whz_eq] using
      Work.Spaces.sq_le_HkIntegrand_z α 6 g z θ j (by omega)
  · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi
    have hW := Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ i j hi1 hij
    rw [← Work.FTS.H2.Wm_eq] at hW
    have hsq := Work.FTS.H2.Whz_Wm_sq α hα z θ hθI
    have hle : (Work.FTS.H2.Whz z θ) ^ 2 ≤ (Work.FTS.H2.Wm α z θ) ^ 2 := by
      rw [hsq.1, hsq.2]
      exact mul_le_mul_of_nonneg_left (Work.FTS.H2.rpow_eta_le_gam hα hθI) (sq_nonneg _)
    have h2 : (Work.Spaces.mixed j i g z θ * Work.FTS.H2.Whz z θ) ^ 2
        ≤ (Work.Spaces.mixed j i g z θ * Work.FTS.H2.Wm α z θ) ^ 2 := by
      rw [mul_pow, mul_pow]
      exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
    exact le_trans h2 hW

/-- **Every slot of level `≤ 6` carrying a `θ`-derivative is dominated by
`HkIntegrand α 6 g` when weighted by `Wm`.** -/
private theorem slot_wm_sq_le {α : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    {i j : ℕ} (hi1 : 1 ≤ i) (hij : i + j ≤ 6) :
    (Work.Spaces.mixed j i g z θ * Work.FTS.H2.Wm α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  have h := Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ i j hi1 hij
  rwa [← Work.FTS.H2.Wm_eq] at h

/-! ## The AM–GM step -/

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

/-! ## The target -/

theorem slotWeightBound {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} (a b u v : ℕ)
    (hab : a + b ≤ 6) (hu : 1 ≤ u) (huv : u + v ≤ 6) {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ * |Work.Spaces.mixed v u g z θ| * |Work.Spaces.mixed b a g z θ|
        ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  intro z θ hz hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hρle : ρ z θ ≤ Work.FTS.TransportS.slotW α a z θ :=
    (Work.FTS.TransportS.IsLeafW_le α hα hρ).2 z θ hz hθ0 hθ1
  rcases eq_or_ne a 0 with ha | ha
  · -- the slot `(a,b)` is a pure `D_z`-slot: the leaf weight is dominated by `(Whz)²`
    subst ha
    have hρW : ρ z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
      simpa using hρle
    have hW : 0 ≤ Work.FTS.H2.Whz z θ := Whz_nonneg_l hθI
    have hX : (Work.Spaces.mixed v u g z θ * Work.FTS.H2.Whz z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
      slot_whz_sq_le hα hz hθ0 hθ1 (i := u) (j := v) huv
    have hY : (Work.Spaces.mixed b 0 g z θ * Work.FTS.H2.Whz z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
      slot_whz_sq_le hα hz hθ0 hθ1 (i := 0) (j := b) hab
    calc ρ z θ * |Work.Spaces.mixed v u g z θ| * |Work.Spaces.mixed b 0 g z θ|
        ≤ (Work.FTS.H2.Whz z θ) ^ 2 * |Work.Spaces.mixed v u g z θ|
            * |Work.Spaces.mixed b 0 g z θ| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hρW (abs_nonneg _)) (abs_nonneg _)
      _ = |Work.Spaces.mixed v u g z θ| * |Work.Spaces.mixed b 0 g z θ|
            * (Work.FTS.H2.Whz z θ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 6 g z θ := amgm_mul_le hW hX hY
  · -- the slot `(a,b)` carries a `θ`-derivative: the leaf weight is dominated by `(Wm)²`
    have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    have hρW : ρ z θ ≤ (Work.FTS.H2.Wm α z θ) ^ 2 := by
      have h := hρle
      rw [Work.FTS.TransportS.slotW_of_pos' α ha1] at h
      exact h
    have hW : 0 ≤ Work.FTS.H2.Wm α z θ := Wm_nonneg_l α hθI
    have hX : (Work.Spaces.mixed v u g z θ * Work.FTS.H2.Wm α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
      slot_wm_sq_le (i := u) (j := v) hu huv
    have hY : (Work.Spaces.mixed b a g z θ * Work.FTS.H2.Wm α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
      slot_wm_sq_le (i := a) (j := b) ha1 hab
    calc ρ z θ * |Work.Spaces.mixed v u g z θ| * |Work.Spaces.mixed b a g z θ|
        ≤ (Work.FTS.H2.Wm α z θ) ^ 2 * |Work.Spaces.mixed v u g z θ|
            * |Work.Spaces.mixed b a g z θ| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hρW (abs_nonneg _)) (abs_nonneg _)
      _ = |Work.Spaces.mixed v u g z θ| * |Work.Spaces.mixed b a g z θ|
            * (Work.FTS.H2.Wm α z θ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 6 g z θ := amgm_mul_le hW hX hY

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbSub
