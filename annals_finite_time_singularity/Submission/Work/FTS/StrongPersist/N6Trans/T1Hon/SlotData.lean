import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.Basic

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
set_option maxHeartbeats 4000000

/-! ## The slot data of the `T1` transport pairing -/

/-- The leaf weight `w²·sin(2θ)^{-q}` of a slot with angular exponent `q`. -/
def t1W (q : ℝ) : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)

/-- The *hard* summand of the slot pairing: all `a + 1` angular derivatives on the `g`-block. -/
def t1Hard (q : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => t1W q z θ * f z θ * Work.Spaces.Dth (Work.Spaces.mixed b a g) z θ
    * Work.Spaces.mixed b a g z θ

/-- The Leibniz sum of the *easy* summands (all splits except `(0,0)`) of the slot pairing,
without the weight. -/
def t1Leib (f g : ℝ → ℝ → ℝ) (a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
    (if a1 = 0 ∧ b1 = 0 then 0 else
      ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
        * (Work.Spaces.mixed b1 a1 f z θ * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ))

/-- The *easy* summands of the slot pairing, in weighted form. -/
def t1Easy (q : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => t1W q z θ * t1Leib f g a b z θ * Work.Spaces.mixed b a g z θ

/-- The pointwise majorant of the easy summands. -/
def t1EasyAbs (q : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => |t1W q z θ| * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
    (if a1 = 0 ∧ b1 = 0 then 0 else
      |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
        * (Work.Spaces.mixed b1 a1 f z θ
           * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|))
    * |Work.Spaces.mixed b a g z θ|

theorem abs_ite_zero_eq (p : Prop) [Decidable p] (x : ℝ) :
    |if p then (0 : ℝ) else x| = if p then 0 else |x| := by
  by_cases h : p <;> simp [h]

theorem t1EasyAbs_nonneg (q : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) (z θ : ℝ) :
    0 ≤ t1EasyAbs q f g a b z θ := by
  rw [t1EasyAbs]
  refine mul_nonneg (mul_nonneg (abs_nonneg _) ?_) (abs_nonneg _)
  refine Finset.sum_nonneg fun a1 _ => Finset.sum_nonneg fun b1 _ => ?_
  by_cases h : a1 = 0 ∧ b1 = 0
  · rw [if_pos h]
  · rw [if_neg h]
    exact abs_nonneg _

theorem abs_t1Leib_le (f g : ℝ → ℝ → ℝ) (a b : ℕ) (z θ : ℝ) :
    |t1Leib f g a b z θ| ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
      (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
        |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
          * (Work.Spaces.mixed b1 a1 f z θ
             * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|) := by
  calc |t1Leib f g a b z θ|
      = |∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
            ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
              * (Work.Spaces.mixed b1 a1 f z θ
                 * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ))| := rfl
    _ ≤ ∑ a1 ∈ Finset.range (a + 1), |∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
            ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
              * (Work.Spaces.mixed b1 a1 f z θ
                 * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          |if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
            ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
              * (Work.Spaces.mixed b1 a1 f z θ
                 * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)| :=
        Finset.sum_le_sum fun a1 _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
            |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
              * (Work.Spaces.mixed b1 a1 f z θ
                 * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|) := by
        refine Finset.sum_congr rfl fun a1 _ => Finset.sum_congr rfl fun b1 _ => ?_
        exact abs_ite_zero_eq _ _

theorem abs_t1Easy_le (q : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ) (z θ : ℝ) :
    |t1Easy q f g a b z θ| ≤ t1EasyAbs q f g a b z θ := by
  rw [t1Easy, t1EasyAbs, abs_mul, abs_mul]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
    (abs_nonneg _)
  exact abs_t1Leib_le f g a b z θ

/-- A summand of `t1EasyAbs` is dominated by `36` times the corresponding unweighted summand. -/
theorem t1EasyAbs_summand_le {α q : ℝ} (hα : 0 < α) {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ}
    (hab : a + b ≤ 4) (ha1 : a1 ≤ a) (hb1 : b1 ≤ b)
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
      |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
        * (Work.Spaces.mixed b1 a1 f z θ
           * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|)
      ≤ 36 * (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
        |Work.Spaces.mixed b1 a1 f z θ|
          * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|) := by
  by_cases h : a1 = 0 ∧ b1 = 0
  · rw [if_pos h, if_pos h]
    norm_num
  · rw [if_neg h, if_neg h]
    have hc : |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))| ≤ 36 := by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast choose_mul_le (a := a) (i := a1) (b := b) (j := b1)
        (by omega) (by omega)
    rw [abs_mul]
    exact mul_le_mul hc (le_of_eq (abs_mul _ _)) (abs_nonneg _) (by norm_num)

theorem t1EasyAbs_le {α q : ℝ} (hα : 0 < α) {f g : ℝ → ℝ → ℝ} {a b : ℕ}
    (hab : a + b ≤ 4)
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    t1EasyAbs q f g a b z θ ≤ 36 * slotEasySum α f g a b z θ := by
  have hW : |t1W q z θ| ≤ Work.FTS.TransportS.slotW α a z θ := by
    rw [show t1W q z θ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) from rfl,
      abs_of_nonneg (weight_nonneg_of_Iθ q ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)]
    exact weight_le_slotW hα hq0 hqa hz hθ
  have hAnonneg : 0 ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
      (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
        |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
          * (Work.Spaces.mixed b1 a1 f z θ
             * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|) :=
    Finset.sum_nonneg fun a1 _ => Finset.sum_nonneg fun b1 _ => by
      by_cases h : a1 = 0 ∧ b1 = 0
      · rw [if_pos h]
      · rw [if_neg h]; exact abs_nonneg _
  have hBnonneg : 0 ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
      (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
        |Work.Spaces.mixed b1 a1 f z θ|
          * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|) :=
    Finset.sum_nonneg fun a1 _ => Finset.sum_nonneg fun b1 _ => by
      by_cases h : a1 = 0 ∧ b1 = 0
      · rw [if_pos h]
      · rw [if_neg h]; exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hA : (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
          |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
            * (Work.Spaces.mixed b1 a1 f z θ
               * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|))
      ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (36 * (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
          |Work.Spaces.mixed b1 a1 f z θ|
            * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|)) :=
    Finset.sum_le_sum fun a1 ha1 => Finset.sum_le_sum fun b1 hb1 =>
      t1EasyAbs_summand_le hα hab (by have := Finset.mem_range.mp ha1; omega)
        (by have := Finset.mem_range.mp hb1; omega) hq0 hqa hz hθ
  have hfac1 : (36 : ℝ) * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
          |Work.Spaces.mixed b1 a1 f z θ|
            * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|))
      = ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (36 * (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
          |Work.Spaces.mixed b1 a1 f z θ|
            * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|)) := by
    simp only [Finset.mul_sum]
  have hfac2 : Work.FTS.TransportS.slotW α a z θ
        * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
            |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|))
        * |Work.Spaces.mixed b a g z θ|
      = ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
          Work.FTS.TransportS.slotW α a z θ * |Work.Spaces.mixed b1 a1 f z θ|
            * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|
            * |Work.Spaces.mixed b a g z θ|) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a1 _ => Finset.sum_congr rfl fun b1 _ => ?_
    by_cases h : a1 = 0 ∧ b1 = 0
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  calc t1EasyAbs q f g a b z θ
      = |t1W q z θ| * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
            |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
              * (Work.Spaces.mixed b1 a1 f z θ
                 * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|))
          * |Work.Spaces.mixed b a g z θ| := rfl
    _ ≤ Work.FTS.TransportS.slotW α a z θ
          * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
              |((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
                * (Work.Spaces.mixed b1 a1 f z θ
                   * Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ)|))
          * |Work.Spaces.mixed b a g z θ| := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hW hAnonneg) (abs_nonneg _)
    _ ≤ Work.FTS.TransportS.slotW α a z θ
          * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            (36 * (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
              |Work.Spaces.mixed b1 a1 f z θ|
                * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|)))
          * |Work.Spaces.mixed b a g z θ| := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA (slotW_nonneg α a z θ)) (abs_nonneg _)
    _ = 36 * (Work.FTS.TransportS.slotW α a z θ
          * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
              |Work.Spaces.mixed b1 a1 f z θ|
                * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|))
          * |Work.Spaces.mixed b a g z θ|) := by rw [← hfac1]; ring
    _ = 36 * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 = 0 ∧ b1 = 0 then (0 : ℝ) else
            Work.FTS.TransportS.slotW α a z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|
              * |Work.Spaces.mixed b a g z θ|)) := by rw [hfac2]
    _ = 36 * slotEasySum α f g a b z θ := by rw [slotEasySum]
end

end Work.FTS.StrongPersist.N6Trans.T1Hon
