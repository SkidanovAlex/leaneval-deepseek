import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.GalBasis.cc.SlotDefs
import Submission.Work.FTS.GalBasis.cc.HkIntegrand_mul_le_slots
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `n.choose k ≤ 2^n ≤ 16` for `n ≤ 4`, hence `(n.choose k : ℝ)² ≤ 256`. -/
private lemma binom_sq_le_256_sharp (n k : ℕ) (hkn : k ≤ n) (hn : n ≤ 4) :
    (n.choose k : ℝ) ^ 2 ≤ 256 := by
  have h1 : n.choose k ≤ 2 ^ n := Nat.choose_le_two_pow n k
  have h2 : n.choose k ≤ 16 := by
    calc n.choose k ≤ 2 ^ n := h1
      _ ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hn
      _ = 16 := by norm_num
  have h3 : (n.choose k : ℝ) ≤ 16 := by exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ (n.choose k : ℝ) := by positivity
  nlinarith [h3, h4]

/-- The pure `D_z`-slots of `HkIntegrand α 4 (χ · f)` are dominated by `mulSlotRHS`. -/
private lemma zSlot_le_sharp {α : ℝ} {χ f : Fn} (hχ : Work.FTS.EllipticEst.SmoothOpen χ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {i : ℕ} (hi : i ≤ 4) {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ) ^ 2
      ≤ 6400 * mulSlotRHS α χ f z θ := by
  have hnn : 0 ≤ mulSlotRHS α χ f z θ := mulSlotRHS_nonneg α χ f z θ
  have hsum : Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ
      = ∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * (Work.Spaces.DzIter b χ z θ
            * Work.Spaces.DzIter (i - b) f z θ * pw z θ)) := by
    rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz i χ f hχ hf z θ hz hθ0 hθ1,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hcs : (Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ) ^ 2
      ≤ ((i + 1 : ℕ) : ℝ) * ∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * (Work.Spaces.DzIter b χ z θ
            * Work.Spaces.DzIter (i - b) f z θ * pw z θ)) ^ 2 := by
    rw [hsum]
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
      (f := fun b => (i.choose b : ℝ) * (Work.Spaces.DzIter b χ z θ
        * Work.Spaces.DzIter (i - b) f z θ * pw z θ))
  have hterm : ∀ b ∈ Finset.range (i + 1),
      ((i.choose b : ℝ) * (Work.Spaces.DzIter b χ z θ
        * Work.Spaces.DzIter (i - b) f z θ * pw z θ)) ^ 2
        ≤ 256 * mulSlotRHS α χ f z θ := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hcb : (i.choose b : ℝ) ^ 2 ≤ 256 := binom_sq_le_256_sharp i b hbi hi
    have hcore : (Work.Spaces.mixed b 0 χ z θ) ^ 2 * (zslot (i - b) f z θ) ^ 2
        ≤ mulSlotRHS α χ f z θ := slotZSum_ge_term α χ f z θ hi (by omega)
    have hcorenn : 0 ≤ (Work.Spaces.mixed b 0 χ z θ) ^ 2 * (zslot (i - b) f z θ) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have h1 : ((i.choose b : ℝ) * (Work.Spaces.DzIter b χ z θ
          * Work.Spaces.DzIter (i - b) f z θ * pw z θ)) ^ 2
        = (i.choose b : ℝ) ^ 2 * ((Work.Spaces.mixed b 0 χ z θ) ^ 2
            * (zslot (i - b) f z θ) ^ 2) := by
      simp only [Work.Spaces.mixed_zero_right, zslot]
      ring
    rw [h1]
    exact le_trans (mul_le_mul_of_nonneg_right hcb hcorenn)
      (mul_le_mul_of_nonneg_left hcore (by norm_num))
  have hsum_bd : ∑ b ∈ Finset.range (i + 1),
        ((i.choose b : ℝ) * (Work.Spaces.DzIter b χ z θ
          * Work.Spaces.DzIter (i - b) f z θ * pw z θ)) ^ 2
      ≤ ((i + 1 : ℕ) : ℝ) * (256 * mulSlotRHS α χ f z θ) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
    simp [nsmul_eq_mul]
  have h256 : (0 : ℝ) ≤ 256 * mulSlotRHS α χ f z θ := mul_nonneg (by norm_num) hnn
  have hfin : ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * (256 * mulSlotRHS α χ f z θ))
      ≤ 6400 * mulSlotRHS α χ f z θ := by
    have hm : ((i + 1 : ℕ) : ℝ) ≤ 5 := by
      have hi4 : (i : ℝ) ≤ 4 := by exact_mod_cast hi
      push_cast
      linarith
    have h1 : ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * (256 * mulSlotRHS α χ f z θ))
        ≤ 5 * (5 * (256 * mulSlotRHS α χ f z θ)) :=
      mul_le_mul hm (mul_le_mul hm (le_refl ((256 : ℝ) * mulSlotRHS α χ f z θ)) h256
        (by norm_num))
        (mul_nonneg (by positivity) h256) (by norm_num)
    have h2 : 5 * (5 * (256 * mulSlotRHS α χ f z θ)) = 6400 * mulSlotRHS α χ f z θ := by
      ring
    linarith [h1, h2]
  calc (Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ) ^ 2
      ≤ ((i + 1 : ℕ) : ℝ) * ∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * (Work.Spaces.DzIter b χ z θ
            * Work.Spaces.DzIter (i - b) f z θ * pw z θ)) ^ 2 := hcs
    _ ≤ ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * (256 * mulSlotRHS α χ f z θ)) :=
        mul_le_mul_of_nonneg_left hsum_bd (by positivity)
    _ ≤ 6400 * mulSlotRHS α χ f z θ := hfin

/-- The mixed slots of `HkIntegrand α 4 (χ · f)` are dominated by `mulSlotRHS`. -/
private lemma mSlot_le_sharp {α : ℝ} {χ f : Fn} (hχ : Work.FTS.EllipticEst.SmoothOpen χ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {i j : ℕ} (hi1 : 1 ≤ i) (hij : i + j ≤ 4)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (Work.Spaces.mixed j i (fun z θ => χ z θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 40960000 * mulSlotRHS α χ f z θ := by
  have hnn : 0 ≤ mulSlotRHS α χ f z θ := mulSlotRHS_nonneg α χ f z θ
  have hi4 : i ≤ 4 := by omega
  have hj4 : j ≤ 4 := by omega
  have hlei := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed j i χ f hχ hf z θ hz hθ0 hθ1
  set Y : ℕ → ℕ → ℝ := fun a b => (i.choose a : ℝ) * (j.choose b : ℝ)
    * (Work.Spaces.mixed b a χ z θ * Work.Spaces.mixed (j - b) (i - a) f z θ
        * Work.Spaces.Wt α z θ) with hYdef
  have hYsplit : (Work.Spaces.mixed j i (fun z θ => χ z θ * f z θ) z θ
        * Work.Spaces.Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), Y a b) ^ 2 := by
    have hkey : Work.Spaces.mixed j i (fun z θ => χ z θ * f z θ) z θ * Work.Spaces.Wt α z θ
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), Y a b := by
      rw [hlei, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [hYdef]
      ring
    rw [hkey]
  have hper : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      (Y a b) ^ 2 ≤ 65536 * mulSlotRHS α χ f z θ := by
    intro a ha b hb
    have hai : a ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hcha : (i.choose a : ℝ) ^ 2 ≤ 256 := binom_sq_le_256_sharp i a hai hi4
    have hchb : (j.choose b : ℝ) ^ 2 ≤ 256 := binom_sq_le_256_sharp j b hbj hj4
    have hch : (i.choose a : ℝ) ^ 2 * (j.choose b : ℝ) ^ 2 ≤ 65536 :=
      calc (i.choose a : ℝ) ^ 2 * (j.choose b : ℝ) ^ 2 ≤ 256 * 256 :=
            mul_le_mul hcha hchb (by positivity) (by norm_num)
        _ = 65536 := by norm_num
    have hYW : (Work.Spaces.mixed (j - b) (i - a) f z θ * Work.Spaces.Wt α z θ) ^ 2
        = (if 1 ≤ i - a then (mslot α (j - b) (i - a) f z θ) ^ 2
            else (zslotW α (j - b) f z θ) ^ 2) := by
      by_cases hcase : 1 ≤ i - a
      · rw [if_pos hcase]
        rfl
      · rw [if_neg hcase]
        have hzero : i - a = 0 := by omega
        rw [hzero]
        simp only [Work.Spaces.mixed_zero_right, zslotW]
    have hY0 : (Y a b) ^ 2 = (i.choose a : ℝ) ^ 2 * (j.choose b : ℝ) ^ 2
        * (Work.Spaces.mixed b a χ z θ) ^ 2
        * (Work.Spaces.mixed (j - b) (i - a) f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      rw [hYdef]
      ring
    have hslot : (Work.Spaces.mixed b a χ z θ) ^ 2 *
        (if 1 ≤ i - a then (mslot α (j - b) (i - a) f z θ) ^ 2
          else (zslotW α (j - b) f z θ) ^ 2) ≤ mulSlotRHS α χ f z θ :=
      slotMSum_ge_term α χ f z θ hi4 hj4 hai hbj hi1 hij
    have hBnn : 0 ≤ (Work.Spaces.mixed b a χ z θ) ^ 2 *
        (if 1 ≤ i - a then (mslot α (j - b) (i - a) f z θ) ^ 2
          else (zslotW α (j - b) f z θ) ^ 2) := by
      by_cases hc : 1 ≤ i - a
      · rw [if_pos hc]; positivity
      · rw [if_neg hc]; positivity
    rw [hY0, hYW]
    rw [mul_assoc ((i.choose a : ℝ) ^ 2 * (j.choose b : ℝ) ^ 2)
      ((Work.Spaces.mixed b a χ z θ) ^ 2)
      (if 1 ≤ i - a then (mslot α (j - b) (i - a) f z θ) ^ 2
        else (zslotW α (j - b) f z θ) ^ 2)]
    exact le_trans (mul_le_mul_of_nonneg_right hch hBnn)
      (mul_le_mul_of_nonneg_left hslot (by norm_num))
  have hcardI : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcardJ : (((Finset.range (j + 1)).card : ℕ) : ℝ) = (j : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hij25 : ((i : ℝ) + 1) * ((j : ℝ) + 1) ≤ 25 := by
    have h1 : (i : ℝ) ≤ 4 := by exact_mod_cast hi4
    have h2 : (j : ℝ) ≤ 4 := by exact_mod_cast hj4
    nlinarith
  have hsum2 : ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (Y a b) ^ 2
      ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          (65536 * mulSlotRHS α χ f z θ) :=
    Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hper a ha b hb
  have hsumconst : ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (65536 * mulSlotRHS α χ f z θ)
      = ((i : ℝ) + 1) * ((j : ℝ) + 1) * (65536 * mulSlotRHS α χ f z θ) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [hYsplit]
  calc (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), Y a b) ^ 2
      ≤ ((i : ℝ) + 1) * ∑ a ∈ Finset.range (i + 1),
          ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1), (Y a b) ^ 2 := by
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
          (f := fun a => ∑ b ∈ Finset.range (j + 1), Y a b)
        rw [hcardI] at hcs
        refine hcs.trans ?_
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => ?_)) (by positivity)
        have hcs2 := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
          (f := fun b => Y a b)
        rwa [hcardJ] at hcs2
    _ = ((i : ℝ) + 1) * ((j : ℝ) + 1)
          * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (Y a b) ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1)
          * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (65536 * mulSlotRHS α χ f z θ) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (((i : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2 * (65536 * mulSlotRHS α χ f z θ) := by
        rw [hsumconst]; ring
    _ ≤ 625 * (65536 * mulSlotRHS α χ f z θ) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h0 : (0 : ℝ) ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1) := by positivity
        nlinarith [hij25, h0]
    _ = 40960000 * mulSlotRHS α χ f z θ := by ring

/-- **The product rule with a `χ`-independent explicit constant**: the same statement as
`Work.FTS.GalBasis.cc.HkIntegrand_mul_le_slots`, but with the constant `1024032001` exposed, so
that it can be used uniformly in a family of multipliers.  (`HkIntegrand_mul_le_slots` proves
exactly this bound, but hides the constant behind an `∃`.) -/
theorem HkIntegrand_mul_le_slots_explicit {α : ℝ} {χ f : Work.FTS.Galerkin.Fn}
    (hχ : Work.FTS.EllipticEst.SmoothOpen χ) (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α 4 (fun z θ => χ z θ * f z θ) z θ
        ≤ 1024032001 * mulSlotRHS α χ f z θ := by
  intro z θ hz hθ0 hθ1
  have hnn : 0 ≤ mulSlotRHS α χ f z θ := mulSlotRHS_nonneg α χ f z θ
  have hZ : (∑ i ∈ Finset.range 5,
        (Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ) ^ 2)
      ≤ 5 * (6400 * mulSlotRHS α χ f z θ) := by
    have hper : ∀ i ∈ Finset.range 5,
        (Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ) ^ 2
          ≤ 6400 * mulSlotRHS α χ f z θ := by
      intro i hi
      exact zSlot_le_sharp hχ hf (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hz hθ0 hθ1
    calc (∑ i ∈ Finset.range 5,
          (Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ) ^ 2)
        ≤ ∑ _i ∈ Finset.range 5, (6400 * mulSlotRHS α χ f z θ) := Finset.sum_le_sum hper
      _ = 5 * (6400 * mulSlotRHS α χ f z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hM : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => χ z θ * f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 25 * (40960000 * mulSlotRHS α χ f z θ) := by
    have hper : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => χ z θ * f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ 40960000 * mulSlotRHS α χ f z θ := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ 4
      · rw [if_pos hc]
        exact mSlot_le_sharp hχ hf hc.1 hc.2 hz hθ0 hθ1
      · rw [if_neg hc]
        exact mul_nonneg (by norm_num) hnn
    calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => χ z θ * f z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ ∑ _i ∈ Finset.range 5, ∑ _j ∈ Finset.range 5,
            (40960000 * mulSlotRHS α χ f z θ) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hper i hi j hj
      _ = 25 * (40960000 * mulSlotRHS α χ f z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hsplit : Work.Spaces.HkIntegrand α 4 (fun z θ => χ z θ * f z θ) z θ
      = (∑ i ∈ Finset.range 5,
            (Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => χ z θ * f z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0) := rfl
  rw [hsplit]
  calc (∑ i ∈ Finset.range 5,
          (Work.Spaces.DzIter i (fun z θ => χ z θ * f z θ) z θ * pw z θ) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => χ z θ * f z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ 5 * (6400 * mulSlotRHS α χ f z θ)
        + 25 * (40960000 * mulSlotRHS α χ f z θ) := add_le_add hZ hM
    _ = 1024032000 * mulSlotRHS α χ f z θ := by ring
    _ ≤ 1024032001 * mulSlotRHS α χ f z θ :=
        mul_le_mul_of_nonneg_right (by norm_num) hnn

end Work.FTS.GalBasis.cc.Subcut
