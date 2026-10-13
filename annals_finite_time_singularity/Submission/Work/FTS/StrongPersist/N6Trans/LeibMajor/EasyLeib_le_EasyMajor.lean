import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor
import Submission.Work.FTS.H2.T1EasyBound
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.LeibMajor

-- The statement uses `π` (i.e. `Real.pi`); the package sets `autoImplicit = false`, so the
-- scoped `Real` notation has to be opened for `π` to elaborate at all.
open scoped Real Topology
open MeasureTheory Set Filter
open Finset

noncomputable section

/-! ## The matching of the two Leibniz majorants

Both `EasyLeib` (the easy Leibniz majorant of the `D_θ`-transport pairing) and `EasyMajor`
(the workspace majorant of the flat `ℋ⁴`-pairing) are finite sums of *absolute values* of
Leibniz summands, so the comparison is purely combinatorial: the Leibniz summand of the slot
`(a,b)` is literally a summand of `EasyMajor` up to the binomial factor of the Leibniz rule,
and `EasyMajor` retains *at least* every summand that `EasyLeib` keeps.

The proof proceeds through three purely algebraic facts, all pointwise in `(z,θ)` and
independent of the `SmoothOpen` hypotheses:

* `FL_zero_le_ZL` : the `a = 0` slot of `EasyLeib` (the `D_z`-slot) is dominated by the
  `D_z`-part `ZL` of `EasyMajor` (the `xD` summands, with the hard slot `(i,b) = (4,0)`
  removed on both sides);
* `FL_le_MiL` : every slot with `a ≥ 1` (a mixed slot) is dominated by the corresponding
  mixed slot `MiL` (the `yM` summands, with the hard family `(a1,b1) = (0,0)`,
  `i + j = 4` removed on both sides);
* splitting the outer `range 5`-sums with `Finset.sum_range_succ'` and adding. -/

/-- The `a`-th slot sum of `EasyLeib` (the inner double sum over the Leibniz splits). -/
private def FL (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) (a : ℕ) : ℝ :=
  ∑ b ∈ Finset.range 5,
    (if a + b ≤ 4 then
      ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (if a1 = 0 ∧ b1 = 0 then 0 else
          Work.FTS.TransportS.slotW α a z θ * |Work.Spaces.mixed b1 a1 f z θ|
            * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|
            * |Work.Spaces.mixed b a g z θ|)
    else 0)

/-- The `D_z`-part of `EasyMajor` (the `xD` summands). -/
private def ZL (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
    (if i = 4 ∧ b = 0 then 0 else |Work.FTS.H2.xD f g i b z θ|)

/-- The `i`-th mixed slot of `EasyMajor` (the `yM` summands). -/
private def MiL (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 5,
    (if 1 ≤ i ∧ i + j ≤ 4 then
      ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |Work.FTS.H2.yM α f g i j a b z θ|)
    else 0)

private lemma EasyLeib_eq_sum_FL (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.StrongPersist.N6Trans.EasyLeib α f g z θ
      = ∑ a ∈ Finset.range 5, FL α f g z θ a := rfl

private lemma EasyMajor_eq (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.H2.EasyMajor α f g z θ
      = ZL f g z θ + ∑ i ∈ Finset.range 5, MiL α f g z θ i := rfl

/-- The elementary product inequality behind every summand comparison: a nonnegative weight
`W` times three nonnegative factors is dominated by the same expression with the coefficient
`c ≥ 1` in front and the weight `W` moved to the back. -/
private lemma prod_four_le {W c A B C : ℝ} (hW : 0 ≤ W) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hc : 1 ≤ c) : W * A * B * C ≤ c * A * B * C * W := by
  have hX : 0 ≤ A * B * C := by positivity
  have h1 : W ≤ c * W := by nlinarith
  calc W * A * B * C = W * (A * B * C) := by ring
    _ ≤ (c * W) * (A * B * C) := mul_le_mul_of_nonneg_right h1 hX
    _ = c * A * B * C * W := by ring

/-- The `a = 0` summand (`a1 = 0` fixed): the `D_z`-slot Leibniz summand of `EasyLeib` is
dominated by the `xD` summand of `EasyMajor` with the same split `k`, the factor
`(m.choose k) ≥ 1` accounting for the binomial coefficient of the Leibniz rule. -/
private lemma xD_term_le {α : ℝ} {f g : ℝ → ℝ → ℝ} {z θ : ℝ} {m k : ℕ} (hk : k ≤ m) :
    (if (0:ℕ) = 0 ∧ k = 0 then 0 else
      Work.FTS.TransportS.slotW α 0 z θ * |Work.Spaces.mixed k 0 f z θ|
        * |Work.Spaces.mixed (m - k) (0 - 0 + 1) g z θ| * |Work.Spaces.mixed m 0 g z θ|)
      ≤ (if m = 4 ∧ k = 0 then 0 else |Work.FTS.H2.xD f g m k z θ|) := by
  by_cases hk0 : k = 0
  · rw [if_pos ⟨rfl, hk0⟩]
    split_ifs
    · exact le_rfl
    · exact abs_nonneg _
  · rw [if_neg (fun h => hk0 h.2), if_neg (fun h => hk0 h.2)]
    simp only [Work.FTS.TransportS.slotW_zero]
    have hxabs : |Work.FTS.H2.xD f g m k z θ|
        = (m.choose k : ℝ) * |Work.Spaces.DzIter k f z θ|
          * |Work.Spaces.mixed (m - k) 1 g z θ| * |Work.Spaces.DzIter m g z θ|
          * Work.FTS.H2.Whz z θ ^ 2 := by
      unfold Work.FTS.H2.xD
      rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (m.choose k : ℝ) from Nat.cast_nonneg _),
        abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (sq_nonneg (Work.FTS.H2.Whz z θ))]
      ring
    rw [hxabs]
    have hc : (1:ℝ) ≤ (m.choose k : ℝ) := by
      have h := Nat.choose_pos hk
      exact_mod_cast h
    exact prod_four_le (sq_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hc

/-- The `a ≥ 1` summand: the mixed-slot Leibniz summand of `EasyLeib` is dominated by the
`yM` summand of `EasyMajor` with the same split `(a1,b1)`, the binomial product
`(a.choose a1)·(b.choose b1) ≥ 1` accounting for the Leibniz coefficients. -/
private lemma yM_term_le {α : ℝ} {f g : ℝ → ℝ → ℝ} {z θ : ℝ} {a b a1 b1 : ℕ}
    (ha : 1 ≤ a) (ha1 : a1 ≤ a) (hb1 : b1 ≤ b) :
    (if a1 = 0 ∧ b1 = 0 then 0 else
      Work.FTS.TransportS.slotW α a z θ * |Work.Spaces.mixed b1 a1 f z θ|
        * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ| * |Work.Spaces.mixed b a g z θ|)
      ≤ (if a1 = 0 ∧ b1 = 0 ∧ a + b = 4 then 0
          else |Work.FTS.H2.yM α f g a b a1 b1 z θ|) := by
  by_cases h00 : a1 = 0 ∧ b1 = 0
  · rw [if_pos h00]
    split_ifs
    · exact le_rfl
    · exact abs_nonneg _
  · rw [if_neg h00, if_neg (fun h => h00 ⟨h.1, h.2.1⟩)]
    simp only [Work.FTS.TransportS.slotW_of_pos' α ha]
    have hyabs : |Work.FTS.H2.yM α f g a b a1 b1 z θ|
        = ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)) * |Work.Spaces.mixed b1 a1 f z θ|
          * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ| * |Work.Spaces.mixed b a g z θ|
          * Work.FTS.H2.Wm α z θ ^ 2 := by
      unfold Work.FTS.H2.yM
      rw [abs_mul, abs_mul,
        abs_of_nonneg (show (0:ℝ) ≤ (a.choose a1 : ℝ) from Nat.cast_nonneg _),
        abs_of_nonneg (show (0:ℝ) ≤ (b.choose b1 : ℝ) from Nat.cast_nonneg _),
        abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (sq_nonneg (Work.FTS.H2.Wm α z θ))]
      ring
    rw [hyabs]
    have h1 : (1:ℝ) ≤ (a.choose a1 : ℝ) := by
      have h := Nat.choose_pos ha1
      exact_mod_cast h
    have h2 : (1:ℝ) ≤ (b.choose b1 : ℝ) := by
      have h := Nat.choose_pos hb1
      exact_mod_cast h
    have hc : (1:ℝ) ≤ ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)) := by nlinarith
    exact prod_four_le (sq_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hc

/-- The `a = 0` slot of `EasyLeib` is dominated by the `D_z`-part `ZL` of `EasyMajor`. -/
private lemma FL_zero_le_ZL (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    FL α f g z θ 0 ≤ ZL f g z θ := by
  unfold FL ZL
  refine Finset.sum_le_sum fun b hb => ?_
  have hb4 : b ≤ 4 := by have := Finset.mem_range.mp hb; omega
  rw [if_pos (by omega : 0 + b ≤ 4)]
  rw [show (0:ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
  refine Finset.sum_le_sum fun b1 hb1 => ?_
  have hb1' : b1 ≤ b := by have := Finset.mem_range.mp hb1; omega
  exact xD_term_le (α := α) (f := f) (g := g) (z := z) (θ := θ) (m := b) (k := b1) hb1'

/-- Every mixed slot of `EasyMajor` is nonnegative. -/
private lemma MiL_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) (i : ℕ) :
    0 ≤ MiL α f g z θ i := by
  unfold MiL
  refine Finset.sum_nonneg fun j hj => ?_
  split_ifs
  · exact Finset.sum_nonneg fun a ha => Finset.sum_nonneg fun b hb => by
      split_ifs
      · exact le_rfl
      · exact abs_nonneg _
  · exact le_rfl

/-- Every slot of `EasyLeib` with `a ≥ 1` is dominated by the corresponding mixed slot of
`EasyMajor`. -/
private lemma FL_le_MiL (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) (i : ℕ) (hi : 1 ≤ i) :
    FL α f g z θ i ≤ MiL α f g z θ i := by
  unfold FL MiL
  refine Finset.sum_le_sum fun b hb => ?_
  by_cases hg : i + b ≤ 4
  · rw [if_pos hg, if_pos ⟨hi, hg⟩]
    refine Finset.sum_le_sum fun a1 ha1 => Finset.sum_le_sum fun b1 hb1 => ?_
    exact yM_term_le (α := α) (f := f) (g := g) (z := z) (θ := θ) (a := i) (b := b)
      (a1 := a1) (b1 := b1) hi (by have := Finset.mem_range.mp ha1; omega)
      (by have := Finset.mem_range.mp hb1; omega)
  · rw [if_neg hg, if_neg (fun h => hg h.2)]

theorem EasyLeib_le_EasyMajor {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.FTS.StrongPersist.N6Trans.EasyLeib α f g z θ ≤ Work.FTS.H2.EasyMajor α f g z θ := by
  intro z θ hz hθ hθ2
  rw [EasyMajor_eq, EasyLeib_eq_sum_FL]
  have hA : FL α f g z θ 0 ≤ ZL f g z θ := FL_zero_le_ZL α f g z θ
  have hB : (∑ a ∈ Finset.range 4, FL α f g z θ (a + 1))
      ≤ MiL α f g z θ 0 + ∑ a ∈ Finset.range 4, MiL α f g z θ (a + 1) := by
    have h1 : (∑ a ∈ Finset.range 4, FL α f g z θ (a + 1))
        ≤ ∑ a ∈ Finset.range 4, MiL α f g z θ (a + 1) :=
      Finset.sum_le_sum fun a ha => FL_le_MiL α f g z θ (a + 1) (by omega)
    have h2 : (0:ℝ) ≤ MiL α f g z θ 0 := MiL_nonneg α f g z θ 0
    linarith
  have hsplit1 : (∑ a ∈ Finset.range 5, FL α f g z θ a)
      = (∑ a ∈ Finset.range 4, FL α f g z θ (a + 1)) + FL α f g z θ 0 :=
    Finset.sum_range_succ' (fun a => FL α f g z θ a) 4
  have hsplit2 : (∑ i ∈ Finset.range 5, MiL α f g z θ i)
      = (∑ i ∈ Finset.range 4, MiL α f g z θ (i + 1)) + MiL α f g z θ 0 :=
    Finset.sum_range_succ' (fun i => MiL α f g z θ i) 4
  rw [hsplit1, hsplit2]
  linarith

end

end Work.FTS.StrongPersist.N6Trans.LeibMajor
