/-
# `T1Hon/Defs` — the honest-class `T1` transport assembly: definitions and elementary facts

Target (the lead's assignment): the level-4 `T1` transport clause for the coercive inner
product `IP4` in the honest class,

  `|IP4 1 1 1 1 1 1 α (f·D_θg) g| ≤ Ct·α^{-1/2}·|f|_{ℋ⁴}·|g|_{ℋ⁴}²`

(`Submission/Work/FTS/StrongPersist/N6Trans/IP4T1Honest.lean`).  By `IP4T1Aux.IP4_le_leafSum`
it suffices to bound the honest-class `leafSum` of the product `f·D_θg` against `g`:

  `leafSum α (f·D_θg) g ≤ Cb/√(γ-1)·|f|_{ℋ⁴}·HkSq α 4 g`.

The bound is obtained slot by slot: for each slot `(a,b)` (`a + b ≤ 4`) and each leaf weight
`ρ` of `IP4`, the Leibniz expansion of `mixed b a (f·D_θg)` splits the slot pairing into

* the *hard* summand `∫∫ ρ·f·D_θ(mixed b a g)·mixed b a g` (all derivatives on the `g`-block),
  controlled by the angular integration by parts (`HardSlotLemGen`, `HardPairLe`);
* the *easy* summands, whose absolute values are dominated by the Leibniz majorant `EasyLeib`
  of `LeibMajor.lean` — this file provides the per-slot majorant `slotEasySum α f g a b` and
  proves `slotEasySum α f g a b ≤ EasyLeib` pointwise.

This file collects the elementary facts: the definitional identity `DthIter n (D_θ f) =
DthIter (n+1) f`, its consequence `mixed b a (D_θ f) = mixed b (a+1) f`, the commutation
`D_θ (mixed b a g) = mixed b (a+1) g` on the open quadrant, the nonnegativity of `slotW`, the
per-slot majorant `slotEasySum` and its comparison with `EasyLeib`, and a thin wrapper around
Mathlib's `Integrable.prod_right_ae` (a.e. slice integrability out of product integrability).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.Int.Star
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.T1Hon

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

/-! ## The `D_θ`-identities -/

/-- `D_θ`-iteration against a leading `D_θ`: `DthIter n (D_θ f) = DthIter (n+1) f`. -/
theorem DthIter_Dth (n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter n (Work.Spaces.Dth f) = Work.Spaces.DthIter (n + 1) f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show Work.Spaces.Dth (Work.Spaces.DthIter n (Work.Spaces.Dth f))
        = Work.Spaces.Dth (Work.Spaces.DthIter (n + 1) f)
      rw [ih]

/-- `mixed b a (D_θ f) = mixed b (a+1) f`, by definition. -/
theorem mixed_Dth (b a : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed b a (Work.Spaces.Dth f) = Work.Spaces.mixed b (a + 1) f := by
  rw [Work.Spaces.mixed, Work.Spaces.mixed, DthIter_Dth]

/-- **`D_θ` commutes with `mixed b a` on the open quadrant**: for `g` of class `C^∞` on the
open quadrant, `D_θ (D_z^bD_θ^a g) = D_z^bD_θ^{a+1} g = mixed b (a+1) g` there. -/
theorem Dth_mixed_eq {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (b a : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ = Work.Spaces.mixed b (a + 1) g z θ := by
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DthIter a g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n => (hg.DthIter a).forall n
  have h := Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open hsm b 1 hz hθ
  have h1 : Work.Spaces.DthIter 1 (Work.Spaces.DzIter b (Work.Spaces.DthIter a g))
      = Work.Spaces.Dth (Work.Spaces.mixed b a g) := rfl
  have h2 : Work.Spaces.DzIter b (Work.Spaces.DthIter 1 (Work.Spaces.DthIter a g))
      = Work.Spaces.mixed b (a + 1) g := by
    rw [show Work.Spaces.DthIter 1 (Work.Spaces.DthIter a g)
      = Work.Spaces.DthIter (a + 1) g from rfl, Work.Spaces.mixed]
  rw [← h1, ← h2]
  exact h

/-! ## Nonnegativity of the slot weight -/

/-- The slot weight `slotW α a` is nonnegative everywhere. -/
theorem slotW_nonneg (α : ℝ) (a : ℕ) (z θ : ℝ) : 0 ≤ Work.FTS.TransportS.slotW α a z θ := by
  rw [Work.FTS.TransportS.slotW]
  split_ifs <;> exact sq_nonneg _

/-- The binomial coefficient is bounded by `6` for `a ≤ 4`. -/
theorem choose_le_six {a i : ℕ} (ha : a ≤ 4) : a.choose i ≤ 6 := by
  rcases lt_or_ge i (a + 1) with h | h
  · interval_cases a <;> interval_cases i <;> decide
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    norm_num

/-- The product of two binomial coefficients is bounded by `36` for `a, b ≤ 4`. -/
theorem choose_mul_le {a i b j : ℕ} (ha : a ≤ 4) (hb : b ≤ 4) :
    a.choose i * b.choose j ≤ 36 := by
  have h1 := choose_le_six (a := a) (i := i) ha
  have h2 := choose_le_six (a := b) (i := j) hb
  nlinarith

/-! ## The per-slot easy majorant -/

/-- **The easy Leibniz majorant of a single slot.**  For the slot `(a,b)` of the flat
`ℋ⁴`-pairing (`a` angular, `b` radial) and the Leibniz splits `(a1,b1) ≠ (0,0)` of
`mixed b a (f·D_θg)`, this is the sum of the absolute values of the Leibniz summands with the
slot weight `slotW α a` of the corresponding slot of `HkIntegrand α 4` (and without the
binomial coefficients of the Leibniz rule).

It is the single-slot part of the majorant `EasyLeib` of `LeibMajor.lean`. -/
def slotEasySum (α : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
      (if a1 = 0 ∧ b1 = 0 then 0 else
        Work.FTS.TransportS.slotW α a z θ * |Work.Spaces.mixed b1 a1 f z θ|
          * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|
          * |Work.Spaces.mixed b a g z θ|)

theorem slotEasySum_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) (z θ : ℝ) :
    0 ≤ slotEasySum α f g a b z θ := by
  rw [slotEasySum]
  refine Finset.sum_nonneg fun a1 _ => Finset.sum_nonneg fun b1 _ => ?_
  by_cases h : a1 = 0 ∧ b1 = 0
  · rw [if_pos h]
  · rw [if_neg h]
    exact mul_nonneg (mul_nonneg (mul_nonneg (slotW_nonneg α a z θ) (abs_nonneg _))
      (abs_nonneg _)) (abs_nonneg _)

/-- **The single-slot easy majorant is dominated by `EasyLeib`.**  For a slot with `a + b ≤ 4`,
the summand `slotEasySum α f g a b` is one of the summands of the global majorant `EasyLeib`. -/
theorem slotEasySum_le_EasyLeib {α : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ} (hab : a + b ≤ 4)
    (z θ : ℝ) :
    slotEasySum α f g a b z θ ≤ Work.FTS.StrongPersist.N6Trans.EasyLeib α f g z θ := by
  have hFnn : ∀ a' b' : ℕ, 0 ≤ slotEasySum α f g a' b' z θ :=
    fun a' b' => slotEasySum_nonneg α f g a' b' z θ
  rw [Work.FTS.StrongPersist.N6Trans.EasyLeib]
  have hinner : ∀ a' b' : ℕ, 0 ≤ (if a' + b' ≤ 4 then slotEasySum α f g a' b' z θ else 0) := by
    intro a' b'
    by_cases h : a' + b' ≤ 4
    · rw [if_pos h]; exact hFnn a' b'
    · rw [if_neg h]
  have h1 : slotEasySum α f g a b z θ
      ≤ ∑ b' ∈ Finset.range 5, (if a + b' ≤ 4 then slotEasySum α f g a b' z θ else 0) := by
    have hmem : b ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
    have h := Finset.single_le_sum (s := Finset.range 5)
      (f := fun b' => (if a + b' ≤ 4 then slotEasySum α f g a b' z θ else 0))
      (fun b' _ => hinner a b') hmem
    simpa only [if_pos hab] using h
  have hmem2 : a ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
  have h2 := Finset.single_le_sum (s := Finset.range 5)
    (f := fun a' => ∑ b' ∈ Finset.range 5,
      (if a' + b' ≤ 4 then slotEasySum α f g a' b' z θ else 0))
    (fun a' _ => Finset.sum_nonneg fun b' _ => hinner a' b') hmem2
  exact le_trans h1 h2

/-! ## A.e. slice integrability out of product integrability -/

/-- **Almost every slice of a product-integrable function is integrable** (Mathlib's
`Integrable.prod_right_ae`). -/
theorem ae_slice_integrable_of_integrable {G : ℝ × ℝ → ℝ}
    (hG : Integrable G ((volume.restrict Work.Spaces.Iz).prod
      (volume.restrict Work.Spaces.Iθ))) :
    ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      Integrable (fun θ => G (z, θ)) (volume.restrict Work.Spaces.Iθ) :=
  hG.prod_right_ae

end

end Work.FTS.StrongPersist.N6Trans.T1Hon
