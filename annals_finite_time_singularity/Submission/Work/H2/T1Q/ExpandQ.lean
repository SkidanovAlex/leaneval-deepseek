/-
# `Work.FTS.H2.ExpandQ` — the Leibniz expansion of the interior "easy part" `T1Easy`

For `SmoothQuad` data `f`, `g` (genuine `C^∞` on the open quadrant `z > -1`, `0 < θ < π/2`) the
integrand of Elgindi's `D_θ`-transport pairing

  `H4PairInt α (fun z θ => f z θ * D_θ g z θ) g`

is the finite Leibniz sum `∑ xD + ∑ yM` (on the open quadrant), and the five order-five terms
`T1Hard` are the summands `xD f g 4 0` and `yM α f g i j 0 0` with `1 ≤ i`, `i + j = 4`.  Hence
the "easy part" `T1Easy α f g = H4PairInt … - T1Hard α f g` equals `Work.H2.T1Q.EasySumQ α f g`,
a finite sum of products of `ℋ⁴`-slots, and is dominated by `Work.FTS.H2.EasyMajor`.

The proof copies the (closed-quadrant, `SmoothNbhd`) template
`Submission/Work/FTS/H2/T1EasyBound.lean`, replacing the Leibniz rules by their interior versions
`Work.FTS.H2.HQ.DzIter_mul_quad` / `mixed_mul_eq_quad`, and the `D_θ`-`D_z` commutation by
`Work.H2.WPQ.Dth_DzIter_comm_smoothQuad`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.T1EasyBound
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.H2.WPQ.Dth_DzIter_comm_smoothQuad
import Submission.Work.H2.T1Q.QDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The Leibniz expansions -/

/-- The Leibniz expansion of `H4PairInt α (f · D_θ g) g` in the interior class. -/
theorem H4PairInt_expandQ (α : ℝ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      H4PairInt α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g z θ
        = (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), xD f g i b z θ)
          + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then
                ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
                  yM α f g i j a b z θ
               else 0) := by
  intro z hz θ hθ
  have hDz : ∀ i : ℕ, Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dth g z θ) z θ
      = ∑ b ∈ Finset.range (i + 1),
          (i.choose b : ℝ) * (Work.Spaces.DzIter b f z θ
            * Work.Spaces.mixed (i - b) 1 g z θ) := by
    intro i
    rw [Work.FTS.H2.HQ.DzIter_mul_quad i f (Work.Spaces.Dth g) hf (hg.DthIter 1) z hz θ hθ]
    exact Finset.sum_congr rfl fun b _ => rfl
  have hM : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 4 →
      Work.Spaces.mixed j i (fun z θ => f z θ * Work.Spaces.Dth g z θ) z θ
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a f z θ
                * Work.Spaces.mixed (j - b) (i - a + 1) g z θ) := by
    intro i j _ _
    rw [Work.FTS.H2.HQ.mixed_mul_eq_quad j i f (Work.Spaces.Dth g) hf (hg.DthIter 1) z hz θ hθ]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have h2 : Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.Dth g)
        = Work.Spaces.mixed (j - b) (i - a + 1) g := by
      show Work.Spaces.DzIter (j - b) (Work.Spaces.DthIter (i - a) (Work.Spaces.Dth g))
        = Work.Spaces.DzIter (j - b) (Work.Spaces.DthIter (i - a + 1) g)
      rw [show Work.Spaces.Dth g = Work.Spaces.DthIter 1 g from rfl,
        Work.Spaces.DthIter_add_right (i - a) 1 g]
    rw [h2]
  rw [H4PairInt]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [hDz i, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [xD]; ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · rw [if_pos hc, if_pos hc, hM i j hc.1 hc.2, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by simp only [yM]; ring
    · rw [if_neg hc, if_neg hc]

/-- The five summands of `T1Hard`, written with `xD` and `yM`. -/
theorem T1Hard_expandQ (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ)
    (hg : Work.FTS.LocData.SmoothQuad g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      T1Hard α f g z θ
        = xD f g 4 0 z θ
          + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j = 4 then yM α f g i j 0 0 z θ else 0) := by
  intro z hz θ hθ
  have hs : 0 ≤ Real.sin (2 * θ) := le_of_lt (Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
  have hwhz : (Whz z θ) ^ 2 = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
    Whz_sq z θ hs
  have hwm : (Wm α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    Wm_sq α hα z θ hs
  have h4 : Work.Spaces.Dth (Work.Spaces.DzIter 4 g) z θ = Work.Spaces.mixed 4 1 g z θ :=
    Work.H2.WPQ.Dth_DzIter_comm_smoothQuad hg 4 hz hθ
  have hj : ∀ i j : ℕ, Work.Spaces.Dth (Work.Spaces.mixed j i g) z θ
      = Work.Spaces.mixed j (i + 1) g z θ := by
    intro i j
    have h := Work.H2.WPQ.Dth_DzIter_comm_smoothQuad (hg.DthIter i) j hz hθ
    have h2 : Work.Spaces.mixed j 1 (Work.Spaces.DthIter i g)
        = Work.Spaces.mixed j (i + 1) g := by
      show Work.Spaces.DzIter j (Work.Spaces.DthIter 1 (Work.Spaces.DthIter i g))
        = Work.Spaces.DzIter j (Work.Spaces.DthIter (i + 1) g)
      rw [Work.Spaces.DthIter_add_right 1 i g, Nat.one_add]
    rw [← h2]
    exact h
  have hsum : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j = 4 then yM α f g i j 0 0 z θ else 0))
      = yM α f g 1 3 0 0 z θ + yM α f g 2 2 0 0 z θ + yM α f g 3 1 0 0 z θ
        + yM α f g 4 0 0 0 z θ := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    try ring
  rw [T1Hard, h4, hj 1 3, hj 2 2, hj 3 1, hj 4 0, hsum, xD]
  simp only [Whz_sq z θ hs, yM, Wm_sq α hα z θ hs, Nat.choose_zero_right,
    Nat.cast_one, Nat.sub_zero, one_mul]
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
  ring

/-- The interior-class expansion of the "easy part": `T1Easy` is the finite Leibniz sum
`Work.H2.T1Q.EasySumQ`. -/
theorem T1Easy_expandQ (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      T1Easy α f g z θ = Work.H2.T1Q.EasySumQ α f g z θ := by
  intro z hz θ hθ
  have hH := H4PairInt_expandQ α f g hf hg z hz θ hθ
  have hT := T1Hard_expandQ α hα f g hg z hz θ hθ
  -- the `D_z`-part: remove the single hard summand `xD 4 0`
  have hD1 : (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), xD f g i b z θ)
      - xD f g 4 0 z θ
      = ∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
          (if i = 4 ∧ b = 0 then 0 else xD f g i b z θ) := by
    have hsplit : (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), xD f g i b z θ)
        = (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
              (if i = 4 ∧ b = 0 then xD f g i b z θ else 0))
          + ∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
              (if i = 4 ∧ b = 0 then 0 else xD f g i b z θ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by split_ifs <;> ring
    have hsingle : (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
          (if i = 4 ∧ b = 0 then xD f g i b z θ else 0)) = xD f g 4 0 z θ := by
      rw [Finset.sum_eq_single 4]
      · rw [Finset.sum_eq_single 0]
        · simp
        · intro b _ hb0
          rw [if_neg (by rintro ⟨_, h2⟩; exact hb0 h2)]
        · intro h
          exact absurd (Finset.mem_range.mpr (by omega)) h
      · intro i _ hi4
        exact Finset.sum_eq_zero fun b _ => by
          rw [if_neg (by rintro ⟨h1, _⟩; exact hi4 h1)]
      · intro h
        exact absurd (Finset.mem_range.mpr (by norm_num : 4 < 5)) h
    rw [hsplit, hsingle]
    ring
  -- the mixed part: remove the four hard summands `yM i j 0 0` with `i + j = 4`
  have hD2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), yM α f g i j a b z θ
         else 0))
      - (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j = 4 then yM α f g i j 0 0 z θ else 0))
      = ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else yM α f g i j a b z θ)
           else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · rw [if_pos hc, if_pos hc]
      by_cases hd : 1 ≤ i ∧ i + j = 4
      · rw [if_pos hd]
        have hrm : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              yM α f g i j a b z θ) - yM α f g i j 0 0 z θ
            = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
                (if a = 0 ∧ b = 0 then 0 else yM α f g i j a b z θ) := by
          have hsplit : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
                yM α f g i j a b z θ)
              = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
                    (if a = 0 ∧ b = 0 then yM α f g i j a b z θ else 0))
                + ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
                    (if a = 0 ∧ b = 0 then 0 else yM α f g i j a b z θ) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun b _ => by split_ifs <;> ring
          have hsingle : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
                (if a = 0 ∧ b = 0 then yM α f g i j a b z θ else 0))
              = yM α f g i j 0 0 z θ := by
            rw [Finset.sum_eq_single 0]
            · rw [Finset.sum_eq_single 0]
              · simp
              · intro b _ hb0
                rw [if_neg (by rintro ⟨_, h2⟩; exact hb0 h2)]
              · intro h
                exact absurd (Finset.mem_range.mpr (by omega)) h
            · intro a _ ha0
              exact Finset.sum_eq_zero fun b _ => by
                rw [if_neg (by rintro ⟨h1, _⟩; exact ha0 h1)]
            · intro h
              exact absurd (Finset.mem_range.mpr (by omega)) h
          rw [hsplit, hsingle]
          ring
        rw [hrm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        by_cases hab : a = 0 ∧ b = 0
        · rw [if_pos hab, if_pos (by tauto)]
        · rw [if_neg hab, if_neg (by rintro ⟨h1, h2, _⟩; exact hab ⟨h1, h2⟩)]
      · rw [if_neg hd, sub_zero]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [if_neg (by rintro ⟨_, _, h4⟩; exact hd ⟨hc.1, h4⟩)]
    · rw [if_neg hc, if_neg (by rintro ⟨h1, h2⟩; exact hc ⟨h1, by omega⟩), sub_zero, if_neg hc]
  have key : T1Easy α f g z θ
      = ((∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), xD f g i b z θ) - xD f g 4 0 z θ)
        + ((∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then
                ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), yM α f g i j a b z θ
               else 0))
            - (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
                (if 1 ≤ i ∧ i + j = 4 then yM α f g i j 0 0 z θ else 0))) := by
    rw [T1Easy, hH, hT]
    ring
  have key : T1Easy α f g z θ
      = ((∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), xD f g i b z θ) - xD f g 4 0 z θ)
        + ((∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then
                ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), yM α f g i j a b z θ
               else 0))
            - (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
                (if 1 ≤ i ∧ i + j = 4 then yM α f g i j 0 0 z θ else 0))) := by
    rw [T1Easy, hH, hT]
    ring
  rw [key, hD1, hD2]
  rfl

/-- The pointwise majorisation of `T1Easy` by `EasyMajor` on the open quadrant. -/
theorem T1Easy_le_majorQ (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |T1Easy α f g z θ| ≤ EasyMajor α f g z θ := by
  intro z hz θ hθ
  rw [T1Easy_expandQ α hα f g hf hg z hz θ hθ]
  exact Work.H2.T1Q.abs_EasySumQ_le_EasyMajor α f g z θ

end Work.FTS.H2
