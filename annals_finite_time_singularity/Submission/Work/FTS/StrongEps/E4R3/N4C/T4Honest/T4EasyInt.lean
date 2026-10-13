import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.Asm
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.OpenTwins
import Submission.Work.FTS.OpenPkg.wmul_field

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C.T4Honest

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.StrongPersist.N6Trans.T1Hon (t1W t1EasyAbs)
open Work.FTS.H2 (Whz Wm)

/-! ## The weight-splitting facts and the AM–GM slot pairings

These are the elementary pieces of the pointwise route: the leaf weight `w²σ^{-q}` of an
admissible slot is dominated by the product `Whz·Wm` of the weights of the two `g`-slots
(when `a = 0`) resp. by `Wm²` (when `a ≥ 1`), and a product of two weighted `g`-slots is
dominated by `HkIntegrand α 4 g`. -/

/-- The leaf weight `t1W q z θ = w(z)² sin(2θ)^{-q}` is nonnegative on the closed quadrant. -/
theorem t1W_nonneg (q : ℝ) (z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) : 0 ≤ t1W q z θ := by
  rw [t1W]
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)

/-- `w²σ^{-q} ≤ Whz²` for `q ≤ η`: the `η`-weight dominates every admissible leaf weight of
a pure `D_z`-slot. -/
theorem t1W_le_Whz_sq {q : ℝ} (hq : q ≤ Work.Spaces.eta) {z θ : ℝ}
    (hs : 0 < Real.sin (2 * θ)) (hs1 : Real.sin (2 * θ) ≤ 1) :
    t1W q z θ ≤ (Whz z θ) ^ 2 := by
  have h1 : Real.sin (2 * θ) ^ (-q) ≤ Real.sin (2 * θ) ^ (-Work.Spaces.eta) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)
  rw [t1W, Work.FTS.H2.Whz_sq z θ hs.le]
  exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)

/-- `w²σ^{-q} ≤ Wm²` for `q ≤ γ`: the `γ`-weight dominates every admissible leaf weight of
a mixed slot. -/
theorem t1W_le_Wm_sq {α q : ℝ} (hα : 0 < α) (hq : q ≤ Work.Spaces.gam α) {z θ : ℝ}
    (hs : 0 < Real.sin (2 * θ)) (hs1 : Real.sin (2 * θ) ≤ 1) :
    t1W q z θ ≤ (Wm α z θ) ^ 2 := by
  have h1 : Real.sin (2 * θ) ^ (-q) ≤ Real.sin (2 * θ) ^ (-Work.Spaces.gam α) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)
  rw [t1W, Work.FTS.H2.Wm_sq α hα z θ hs.le]
  exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)

/-- AM–GM for a mixed slot of order `≤ 4` against a pure `D_z`-slot of order `≤ 4`. -/
theorem pair_eta_HkIntegrand {α : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 4) {k : ℕ} (hk : k ≤ 4) :
    (|Work.Spaces.mixed j i g z θ| * Wm α z θ) * (|Work.Spaces.DzIter k g z θ| * Whz z θ)
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hA : (|Work.Spaces.mixed j i g z θ| * Wm α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    have h := Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij
    simpa only [mul_pow, sq_abs, Wm] using h
  have hB : (|Work.Spaces.DzIter k g z θ| * Whz z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    have h := Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ k hk
    simpa only [mul_pow, sq_abs, Whz] using h
  exact Work.FTS.H2.Transport3Aux.mul_self_le_of_sq_le
    (mul_nonneg (abs_nonneg _) (Work.FTS.H2.Wm_nonneg α hθ))
    (mul_nonneg (abs_nonneg _) (Work.FTS.H2.Whz_nonneg hθ)) hA hB

/-- AM–GM for two mixed slots of order `≤ 4`. -/
theorem pair_gam_HkIntegrand {α : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    {i j i' j' : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 4) (hi' : 1 ≤ i') (hi'j' : i' + j' ≤ 4) :
    (|Work.Spaces.mixed j i g z θ| * Wm α z θ) * (|Work.Spaces.mixed j' i' g z θ| * Wm α z θ)
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hA : (|Work.Spaces.mixed j i g z θ| * Wm α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    have h := Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij
    simpa only [mul_pow, sq_abs, Wm] using h
  have hB : (|Work.Spaces.mixed j' i' g z θ| * Wm α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    have h := Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i' j' hi' hi'j'
    simpa only [mul_pow, sq_abs, Wm] using h
  exact Work.FTS.H2.Transport3Aux.mul_self_le_of_sq_le
    (mul_nonneg (abs_nonneg _) (Work.FTS.H2.Wm_nonneg α hθ))
    (mul_nonneg (abs_nonneg _) (Work.FTS.H2.Wm_nonneg α hθ)) hA hB

/-- **The pointwise bound of the easy Leibniz majorant in the `D`-sup class**: on the open
quadrant, `t1EasyAbs q f g a b ≤ 900·(WDp 4 f·HkIntegrand α 4 g)`, using only
`WDMem 4 f` for the coefficient. -/
theorem t1EasyAbs_le_WDp {α q : ℝ} {f g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hWD : Work.FTS.VocabO.WDMem 4 f) {a b : ℕ} (hab : a + b ≤ 4)
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      t1EasyAbs q f g a b z θ
        ≤ 900 * (Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkIntegrand α 4 g z θ) := by
  intro z θ hz hθ0 hθ1
  set Wf : ℝ := Work.FTS.VocabO.WDp 4 f with hWf
  set H : ℝ := Work.Spaces.HkIntegrand α 4 g z θ with hH
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.H2.sin_two_pos_Qd ⟨hθ0, hθ1⟩
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hW0 : 0 ≤ Wf := by rw [hWf]; exact Work.FTS.OpenPkg.WDp_nonneg 4 f
  have hH0 : 0 ≤ H := by rw [hH]; exact Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hf_le : ∀ b1 a1 : ℕ, b1 + a1 ≤ 4 → |Work.Spaces.mixed b1 a1 f z θ| ≤ Wf := by
    intro b1 a1 h
    rw [hWf]
    exact Work.FTS.OpenPkg.WDMem_of_WDp_le hWD le_rfl b1 a1 h z θ hz hθ0 hθ1
  -- ### the per-index bound on the two `g`-slots
  have hterm_g : ∀ a1 b1 : ℕ, a1 ≤ a → b1 ≤ b → ¬(a1 = 0 ∧ b1 = 0) →
      |t1W q z θ| * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|
        * |Work.Spaces.mixed b a g z θ| ≤ H := by
    intro a1 b1 ha1 hb1 hne
    rw [hH]
    rcases eq_or_ne a 0 with ha | ha
    · subst ha
      have ha1z : a1 = 0 := by omega
      have hb1p : 1 ≤ b1 := by
        by_contra hc
        exact hne ⟨ha1z, by omega⟩
      have hb4 : b ≤ 4 := by omega
      have hidx : 1 + (b - b1) ≤ 4 := by omega
      have hqq : q ≤ Work.Spaces.eta := by
        rcases hq0 rfl with h | h
        · rw [h]; norm_num [Work.Spaces.eta]
        · rw [h]
      have hWle : |t1W q z θ| ≤ Wm α z θ * Whz z θ := by
        rw [abs_of_nonneg (t1W_nonneg q z θ hs.le)]
        exact le_trans (t1W_le_Whz_sq hqq hs hs1) (Work.FTS.H2.Whz_sq_le_Wm_mul α hα hθI)
      have hAB : (|Work.Spaces.mixed (b - b1) 1 g z θ| * Wm α z θ)
          * (|Work.Spaces.DzIter b g z θ| * Whz z θ) ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
        pair_eta_HkIntegrand (α := α) (g := g) hθI (i := 1) (j := b - b1)
          (k := b) (le_refl 1) hidx hb4
      rw [ha1z]
      simp only [Nat.sub_self, Nat.zero_add, Work.Spaces.mixed_zero_right]
      calc |t1W q z θ| * |Work.Spaces.mixed (b - b1) 1 g z θ| * |Work.Spaces.DzIter b g z θ|
          ≤ (Wm α z θ * Whz z θ) * |Work.Spaces.mixed (b - b1) 1 g z θ|
              * |Work.Spaces.DzIter b g z θ| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hWle (abs_nonneg _)) (abs_nonneg _)
        _ = (|Work.Spaces.mixed (b - b1) 1 g z θ| * Wm α z θ)
              * (|Work.Spaces.DzIter b g z θ| * Whz z θ) := by ring
        _ ≤ Work.Spaces.HkIntegrand α 4 g z θ := hAB
    · have ha1pos : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
      have hqq : q ≤ Work.Spaces.gam α := by
        rcases hqa ha1pos with h | h | h
        · rw [h]
          have h1 := Work.Spaces.one_lt_gam hα
          linarith
        · rw [h]
          have h1 := Work.Spaces.one_lt_gam hα
          have h2 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
          linarith
        · rw [h]
      have hWle : |t1W q z θ| ≤ (Wm α z θ) ^ 2 := by
        rw [abs_of_nonneg (t1W_nonneg q z θ hs.le)]
        exact t1W_le_Wm_sq hα hqq hs hs1
      have hidx1 : 1 ≤ a - a1 + 1 := by omega
      have hidx2 : (a - a1 + 1) + (b - b1) ≤ 4 := by omega
      have hAB : (|Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ| * Wm α z θ)
          * (|Work.Spaces.mixed b a g z θ| * Wm α z θ) ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
        pair_gam_HkIntegrand (α := α) (g := g) hθI (i := a - a1 + 1) (j := b - b1)
          (i' := a) (j' := b) hidx1 hidx2 ha1pos hab
      calc |t1W q z θ| * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|
            * |Work.Spaces.mixed b a g z θ|
          ≤ (Wm α z θ) ^ 2 * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|
              * |Work.Spaces.mixed b a g z θ| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hWle (abs_nonneg _)) (abs_nonneg _)
        _ = (|Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ| * Wm α z θ)
              * (|Work.Spaces.mixed b a g z θ| * Wm α z θ) := by ring
        _ ≤ Work.Spaces.HkIntegrand α 4 g z θ := hAB
  -- ### the Leibniz sum: the binomial coefficients and the `f`-derivative bound
  have hsum_le : (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
          |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
            * (Work.Spaces.mixed b1 a1 f z θ
               * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|))
      ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
          36 * Wf * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|) := by
    refine Finset.sum_le_sum fun a1 ha1 => Finset.sum_le_sum fun b1 hb1 => ?_
    have ha1' : a1 ≤ a := by have := Finset.mem_range.mp ha1; omega
    have hb1' : b1 ≤ b := by have := Finset.mem_range.mp hb1; omega
    by_cases h00 : a1 = 0 ∧ b1 = 0
    · rw [if_pos h00, if_pos h00]
    · rw [if_neg h00, if_neg h00]
      have hc : |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))| ≤ 36 := by
        rw [abs_of_nonneg (by positivity)]
        exact_mod_cast Work.FTS.StrongPersist.N6Trans.T1Hon.choose_mul_le (by omega) (by omega)
      have hf' : |Work.Spaces.mixed b1 a1 f z θ| ≤ Wf := hf_le b1 a1 (by omega)
      have h3 : 0 ≤ |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ| := abs_nonneg _
      calc |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
            * (Work.Spaces.mixed b1 a1 f z θ * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|
          = |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))| * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ| := by simp only [abs_mul]; ring
        _ ≤ 36 * Wf * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul hc hf' (abs_nonneg _) (by norm_num)) h3
  -- ### pulling the outer factors into the sum
  have hpull : |t1W q z θ| * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
          36 * Wf * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|))
      * |Work.Spaces.mixed b a g z θ|
      = 36 * Wf * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
          |t1W q z θ| * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|
            * |Work.Spaces.mixed b a g z θ|)) := by
    conv_lhs => rw [Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a1 _ => ?_
    conv_lhs => rw [Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b1 _ => ?_
    by_cases h : a1 = 0 ∧ b1 = 0
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  have hsum3 : (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
          |t1W q z θ| * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|
            * |Work.Spaces.mixed b a g z θ|))
      ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1), H := by
    refine Finset.sum_le_sum fun a1 ha1 => Finset.sum_le_sum fun b1 hb1 => ?_
    by_cases h : a1 = 0 ∧ b1 = 0
    · rw [if_pos h]; exact hH0
    · rw [if_neg h]
      exact hterm_g a1 b1 (by have := Finset.mem_range.mp ha1; omega)
        (by have := Finset.mem_range.mp hb1; omega) h
  have hsumH : (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1), H)
      = (((a + 1) * (b + 1) : ℕ) : ℝ) * H := by
    rw [Finset.sum_const, Finset.sum_const]
    simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  have hcard : (((a + 1) * (b + 1) : ℕ) : ℝ) ≤ 25 := by
    have h : (a + 1) * (b + 1) ≤ 25 := by
      have h1 : a + 1 ≤ 5 := by omega
      have h2 : b + 1 ≤ 5 := by omega
      calc (a + 1) * (b + 1) ≤ 5 * 5 := Nat.mul_le_mul h1 h2
        _ = 25 := by norm_num
    exact_mod_cast h
  calc t1EasyAbs q f g a b z θ
      = |t1W q z θ| * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
            |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
              * (Work.Spaces.mixed b1 a1 f z θ
                 * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|))
          * |Work.Spaces.mixed b a g z θ| := rfl
    _ ≤ |t1W q z θ| * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
            36 * Wf * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|))
          * |Work.Spaces.mixed b a g z θ| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum_le (abs_nonneg _))
          (abs_nonneg _)
    _ = 36 * Wf * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
            |t1W q z θ| * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|
              * |Work.Spaces.mixed b a g z θ|)) := hpull
    _ ≤ 36 * Wf * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1), H) :=
        mul_le_mul_of_nonneg_left hsum3 (mul_nonneg (by norm_num) hW0)
    _ = 36 * Wf * ((((a + 1) * (b + 1) : ℕ) : ℝ) * H) := by rw [hsumH]
    _ ≤ 36 * Wf * (25 * H) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hH0)
          (mul_nonneg (by norm_num) hW0)
    _ = 900 * (Wf * H) := by ring

/-- **The "easy" (Leibniz) part of the `D_θ`-transport slot pairing with a `D`-sup coefficient.**

`T1Hon.t1EasyAbs q f g a b` is the pointwise majorant of the Leibniz summands of
`slotPairing (t1W q) a b (f·D_θg) g` in which at least one derivative falls on `f`
(`Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.SlotData`).  Its product-integral (for the
measure `H2.pm = (volume.restrict Iz).prod (volume.restrict Iθ)`) is bounded by
`C·WDp 4 f·HkSq α 4 g`.

Pointwise route: each summand `|C(a,a₁)C(b,b₁)·D_z^{b₁}D_θ^{a₁}f·D_z^{b−b₁}D_θ^{a−a₁+1}g|`
has `|D_z^{b₁}D_θ^{a₁}f| ≤ WDp 4 f` (`WDMem_of_WDp_le hWD le_rfl b₁ a₁ _`) and
`C(a,a₁)C(b,b₁) ≤ 36` (`T1Hon.choose_mul_le`, `a,b ≤ 4`), and the weight `w²σ^{−q}` is split
into the two `g`-slot weights: writing `Whz = wσ^{−η/2}`, `Wm = wσ^{−γ/2}` (`Wm = Wt α`),
* for `a = 0` (then `a₁ = 0`, `b₁ ≥ 1`): `w²σ^{−q} ≤ Whz·Wm` since `q ≤ η` and
  `Whz² ≤ Wm·Whz` (`Work.FTS.H2.Whz_sq_le_Wm_mul`), and `D_z^bg` is a pure slot
  (`Work.Spaces.sq_le_HkIntegrand_z`) while `D_z^{b−b₁}D_θ g` is a mixed slot of order `≤ 4`
  (`Work.Spaces.sq_le_HkIntegrand_mixed`);
* for `a ≥ 1`: `w²σ^{−q} ≤ Wm²` since `q ≤ γ`, and both `g`-factors are mixed slots of order
  `≤ 4` (the first because `a₁ + b₁ ≥ 1`).
Then `A·B ≤ HkIntegrand α 4 g z θ` for `A,B ≥ 0` with `A²,B² ≤ HkIntegrand`
(`Work.FTS.H2.Transport3Aux.mul_self_le_of_sq_le`), and summing the `≤ (a+1)(b+1) ≤ 25` summands
gives the pointwise bound `t1EasyAbs ... ≤ 900·(WDp 4 f·HkIntegrand α 4 g z θ)` on the open
quadrant.  Integrability is `Integrable.mono'` against the product-integrable
`WDp 4 f·HkIntegrand α 4 g` (`Hon.integrable_HkIntegrand_prod_open`) using the a.e. strong
measurability `H2.aesm_of_Qd (T1Hon.continuousOn_t1EasyAbs hf hg a b q)` and
`Work.FTS.TransportS.ae_of_forall_Qd`; the integral then equals `900·WDp 4 f·HkSq α 4 g` by
`integral_const_mul` and `∫ HkIntegrand = HkSq`. -/
theorem T4EasyInt : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO.WDMem 4 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    ∀ (a b : ℕ), a + b ≤ 4 → ∀ (q : ℝ),
      (a = 0 → q = 0 ∨ q = Work.Spaces.eta) →
      (1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α) →
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => Work.FTS.StrongPersist.N6Trans.T1Hon.t1EasyAbs q f g a b p.1 p.2)
        Work.FTS.H2.pm ∧
      ∫ p, Work.FTS.StrongPersist.N6Trans.T1Hon.t1EasyAbs q f g a b p.1 p.2 ∂Work.FTS.H2.pm
        ≤ C * Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkSq α 4 g := by
  refine ⟨900, by norm_num, ?_⟩
  intro α f g hα hα1 hf hWD hg hmg a b hab q hq0 hqa
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.FTS.StrongPersist.N6Trans.T1Hon.t1EasyAbs q f g a b z θ
        ≤ 900 * (Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkIntegrand α 4 g z θ) :=
    t1EasyAbs_le_WDp (f := f) (g := g) hα hWD hab hq0 hqa
  obtain ⟨hHkint, hHkval⟩ :=
    Work.FTS.StrongPersist.N6Trans.Hon.integrable_HkIntegrand_prod_open hg hmg
  have hA_int : MeasureTheory.Integrable
      (fun p : ℝ × ℝ =>
        900 * (Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkIntegrand α 4 g p.1 p.2))
      Work.FTS.H2.pm := by
    simpa only [Work.FTS.H2.pm, mul_assoc] using
      hHkint.const_mul (900 * Work.FTS.VocabO.WDp 4 f)
  have hHkval' : (∫ p, Work.Spaces.HkIntegrand α 4 g p.1 p.2 ∂Work.FTS.H2.pm)
      = Work.Spaces.HkSq α 4 g := by
    simpa only [Work.FTS.H2.pm] using hHkval
  have hpt' : ∀ᵐ p ∂Work.FTS.H2.pm,
      Work.FTS.StrongPersist.N6Trans.T1Hon.t1EasyAbs q f g a b p.1 p.2
        ≤ 900 * (Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkIntegrand α 4 g p.1 p.2) := by
    simpa only [Work.FTS.H2.pm] using
      (Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
        Work.FTS.StrongPersist.N6Trans.T1Hon.t1EasyAbs q f g a b p.1 p.2
          ≤ 900 * (Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkIntegrand α 4 g p.1 p.2))
        (fun z θ hz hθ0 hθ1 => hpt z θ hz hθ0 hθ1))
  have hEasy_int : MeasureTheory.Integrable
      (fun p : ℝ × ℝ =>
        Work.FTS.StrongPersist.N6Trans.T1Hon.t1EasyAbs q f g a b p.1 p.2)
      Work.FTS.H2.pm :=
    MeasureTheory.Integrable.mono' hA_int
      (Work.FTS.H2.aesm_of_Qd
        (Work.FTS.StrongPersist.N6Trans.T1Hon.continuousOn_t1EasyAbs hf hg a b q))
      (hpt'.mono fun p hp => by
        rw [Real.norm_of_nonneg
          (Work.FTS.StrongPersist.N6Trans.T1Hon.t1EasyAbs_nonneg q f g a b p.1 p.2)]
        exact hp)
  refine ⟨hEasy_int, ?_⟩
  calc ∫ p, Work.FTS.StrongPersist.N6Trans.T1Hon.t1EasyAbs q f g a b p.1 p.2
          ∂Work.FTS.H2.pm
      ≤ ∫ p, 900 * (Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkIntegrand α 4 g p.1 p.2)
          ∂Work.FTS.H2.pm := MeasureTheory.integral_mono_ae hEasy_int hA_int hpt'
    _ = 900 * (Work.FTS.VocabO.WDp 4 f
          * ∫ p, Work.Spaces.HkIntegrand α 4 g p.1 p.2 ∂Work.FTS.H2.pm) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ = 900 * (Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkSq α 4 g) := by rw [hHkval']
    _ = 900 * Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkSq α 4 g := by ring

end Work.FTS.StrongEps.E4R3.N4C.T4Honest
