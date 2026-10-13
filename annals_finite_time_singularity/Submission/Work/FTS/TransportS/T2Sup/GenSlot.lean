/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TransportS/T2Sup/GenSlot`: slot domination at an arbitrary order

The existing slot-domination lemmas of `SlotT2/Basic.lean` (`canonW_mul_z_le`,
`canonW_mul_mixed_le`) are stated for `HkIntegrand α 4`, i.e. for slots of total order `≤ 4`.
The assembly of the per-slot transport bound `T2Slot` needs the order-`5` analogue for the
single top term `f · D_z(mixed b a g) · mixed b a g` of a slot with `a + b = 4` (the extra
`D_z` coming from the factor `D_z g` of the transport pairing), namely the pointwise
domination

  `canonW q z θ · (mixed j i g z θ)² ≤ HkIntegrand α k g z θ`     (`i + j ≤ k`),

with `q ≤ η` for the pure `D_z`-slots and `q ≤ γ` for the mixed ones.  Together with
`HkMem α 5 g` this makes the top term integrable: the order-`5` slot at `η`/`γ` is a summand
of `HkIntegrand α 5 g`.

The proofs are verbatim copies of `SlotT2.canonW_mul_z_le` / `SlotT2.canonW_mul_mixed_le`
with `4` replaced by the general order `k`.

All declarations here rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.TransportS.SlotT2.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2Sup

set_option autoImplicit false

open Work.FTS.TransportS.SlotT2

/-- **The pure `D_z`-slot at an arbitrary order.**  For `0 < q ≤ η`, `j ≤ k` and
`θ ∈ Iθ`, `canonW q · (D_z^j g)² ≤ HkIntegrand α k g`. -/
theorem canonW_mul_z_le_gen (α : ℝ) (g : ℝ → ℝ → ℝ) {q : ℝ} (hq0 : 0 < q) (k : ℕ)
    (hq : q ≤ Work.Spaces.eta) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (j : ℕ) (hj : j ≤ k) :
    canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hw : canonW q z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
    rw [← canonW_eta_eq z θ hθ]
    exact canonW_mono hq0 hq hθ
  calc canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (Work.FTS.H2.Whz z θ) ^ 2 * (Work.Spaces.DzIter j g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.DzIter j g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [Work.FTS.H2.Whz]; ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α k g z θ j hj

/-- **The mixed slot at an arbitrary order.**  For `0 < q ≤ γ`, `1 ≤ i`, `i + j ≤ k` and
`θ ∈ Iθ`, `canonW q · (mixed j i g)² ≤ HkIntegrand α k g`. -/
theorem canonW_mul_mixed_le_gen (α : ℝ) (g : ℝ → ℝ → ℝ) {q : ℝ} (hq0 : 0 < q) (k : ℕ)
    (hqγ : q ≤ Work.Spaces.gam α) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ k) :
    canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hw : canonW q z θ ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
    rw [← canonW_gam_eq α z θ hθ]
    exact canonW_mono hq0 hqγ hθ
  calc canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.mixed j i g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α k g z θ i j hi hij

/-- `canonW 0 ≤ canonW q` for `0 ≤ q` on the open angular interval. -/
theorem canonW_zero_le {q : ℝ} (hq : 0 ≤ q) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    canonW 0 z θ ≤ canonW q z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have h1 : canonW 0 z θ = (Work.Spaces.w z) ^ 2 := by
    simp only [canonW, neg_zero, Real.rpow_zero, mul_one]
  have h2 : canonW q z θ = (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-q) := rfl
  rw [h1, h2]
  exact le_mul_of_one_le_right (sq_nonneg _) (one_le_rpow_neg hq hθ)

/-- **The pure `D_z`-slot at an arbitrary order, for `0 ≤ q ≤ η`.** -/
theorem canonW_z_slot_le_gen {α : ℝ} (k : ℕ) {q : ℝ} (hqnn : 0 ≤ q) (hq : q ≤ Work.Spaces.eta)
    (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (j : ℕ) (hj : j ≤ k) :
    canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  rcases eq_or_lt_of_le hqnn with h0 | hpos
  · subst h0
    exact le_trans (mul_le_mul_of_nonneg_right (canonW_zero_le Work.Spaces.eta_pos.le hθ)
      (sq_nonneg _)) (canonW_mul_z_le_gen α g Work.Spaces.eta_pos k le_rfl hθI j hj)
  · exact canonW_mul_z_le_gen α g hpos k hq hθI j hj

/-- **The mixed slot at an arbitrary order, for `0 ≤ q ≤ γ`.** -/
theorem canonW_mixed_slot_le_gen {α : ℝ} (hα : 0 < α) (k : ℕ) {q : ℝ} (hqnn : 0 ≤ q)
    (hqγ : q ≤ Work.Spaces.gam α) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ k) :
    canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  rcases eq_or_lt_of_le hqnn with h0 | hpos
  · subst h0
    have hηγ : Work.Spaces.eta ≤ Work.Spaces.gam α := by
      rw [Work.Spaces.gam]
      have : Work.Spaces.eta = 99 / 100 := rfl
      linarith
    exact le_trans (mul_le_mul_of_nonneg_right (canonW_zero_le Work.Spaces.eta_pos.le hθ)
      (sq_nonneg _)) (canonW_mul_mixed_le_gen α g Work.Spaces.eta_pos k hηγ hθI j i hi hij)
  · exact canonW_mul_mixed_le_gen α g hpos k hqγ hθI j i hi hij

end Work.FTS.TransportS.T2Sup
