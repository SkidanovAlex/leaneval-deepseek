import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.TermBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The level-6 `T2` slot: the Leibniz remainder `R` and its bound

`D_z^bD_θ^a(f·D_z g) = f·D_z(D_z^bD_θ^a g) + R`, where `R` collects the Leibniz summands with
at least one derivative on `f` (`SixAux.leibR`).  `leibR_bound` bounds the `canonW q`-weighted
pairing of `R` with `D_z^bD_θ^a g` by `64·(a+1)(b+1)·Λ·|g|²_{ℋ⁶}`, by summing the per-summand
`term_bound`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)
open Work.FTS.StrongPersist.N6Trans.T1SixAux (SlotW6 slotW6_z slotW6_mixed)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- The Leibniz remainder of `D_z^bD_θ^a (f · D_z g)`: the sum over the summands with at least
one derivative falling on `f`. -/
def leibR (a b : ℕ) (f g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
    (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
      * (Work.Spaces.mixed b1 a1 f z θ * Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ)

/-- Splitting off the `(0,0)` summand of a double `Finset.range` sum. -/
theorem sum_range_add_zero {M : Type*} [AddCommGroup M] (Φ : ℕ → ℕ → M) (a b : ℕ) :
    (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1), Φ a1 b1)
      = Φ 0 0 + ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 + b1 = 0 then 0 else Φ a1 b1) := by
  have key : ∀ a1 : ℕ, (∑ b1 ∈ Finset.range (b + 1), Φ a1 b1)
      = (∑ b1 ∈ Finset.range (b + 1), (if a1 + b1 = 0 then Φ a1 b1 else 0))
        + (∑ b1 ∈ Finset.range (b + 1), (if a1 + b1 = 0 then 0 else Φ a1 b1)) := by
    intro a1
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b1 _ => by
      by_cases h : a1 + b1 = 0
      · rw [if_pos h, if_pos h]; simp
      · rw [if_neg h, if_neg h]; simp
  have hb : ∀ a1 : ℕ, (∑ b1 ∈ Finset.range (b + 1), (if a1 + b1 = 0 then Φ a1 b1 else 0))
      = (if a1 = 0 then Φ 0 0 else 0) := by
    intro a1
    by_cases ha : a1 = 0
    · subst ha
      have h1 : (∑ b1 ∈ Finset.range (b + 1), (if (0:ℕ) + b1 = 0 then Φ 0 b1 else 0))
          = ∑ b1 ∈ Finset.range (b + 1), (if b1 = 0 then Φ 0 b1 else 0) := by
        refine Finset.sum_congr rfl fun b1 _ => by rw [zero_add]
      rw [h1]
      rw [Finset.sum_ite_eq' (Finset.range (b + 1)) 0 (fun x => Φ 0 x)]
      simp
    · rw [if_neg ha]
      refine Finset.sum_eq_zero fun b1 _ => ?_
      rw [if_neg (by omega)]
  have ha : (∑ a1 ∈ Finset.range (a + 1), (if a1 = 0 then Φ 0 0 else 0)) = Φ 0 0 := by
    rw [Finset.sum_ite_eq' (Finset.range (a + 1)) 0 (fun _ => Φ 0 0)]
    simp
  calc (∑ a1 ∈ Finset.range (a+1), ∑ b1 ∈ Finset.range (b+1), Φ a1 b1)
      = ∑ a1 ∈ Finset.range (a+1),
          ((∑ b1 ∈ Finset.range (b+1), (if a1 + b1 = 0 then Φ a1 b1 else 0))
          + (∑ b1 ∈ Finset.range (b+1), (if a1 + b1 = 0 then 0 else Φ a1 b1))) :=
        Finset.sum_congr rfl fun a1 _ => key a1
    _ = (∑ a1 ∈ Finset.range (a+1),
            (∑ b1 ∈ Finset.range (b+1), (if a1 + b1 = 0 then Φ a1 b1 else 0)))
          + ∑ a1 ∈ Finset.range (a+1),
            (∑ b1 ∈ Finset.range (b+1), (if a1 + b1 = 0 then 0 else Φ a1 b1)) :=
        Finset.sum_add_distrib
    _ = (∑ a1 ∈ Finset.range (a+1), (if a1 = 0 then Φ 0 0 else 0))
          + ∑ a1 ∈ Finset.range (a+1),
            (∑ b1 ∈ Finset.range (b+1), (if a1 + b1 = 0 then 0 else Φ a1 b1)) :=
        congrArg (· + _) (Finset.sum_congr rfl fun a1 _ => hb a1)
    _ = Φ 0 0 + ∑ a1 ∈ Finset.range (a+1),
            (∑ b1 ∈ Finset.range (b+1), (if a1 + b1 = 0 then 0 else Φ a1 b1)) :=
        congrArg (· + _) ha

/-- `R` is continuous on the open quadrant. -/
theorem leibR_continuousOn {a b : ℕ} {f g : ℝ → ℝ → ℝ}
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hgs : Work.FTS.EllipticEst.SmoothOpen g) :
    ContinuousOn (fun p : ℝ × ℝ => leibR a b f g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hX : ∀ (j i : ℕ), ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := fun j i => (hfs.mixed j i).continuousOn
  have hY : ∀ (j i : ℕ), ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := fun j i => (hgs.mixed j i).continuousOn
  have hmain : ContinuousOn (fun p : ℝ × ℝ => ∑ a1 ∈ Finset.range (a + 1),
      ∑ b1 ∈ Finset.range (b + 1),
        (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
          * (Work.Spaces.mixed b1 a1 f p.1 p.2
            * Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h0 : ContinuousOn (fun _ : ℝ × ℝ => (0:ℝ)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      continuousOn_const
    refine continuousOn_finsetSum _ fun a1 _ => continuousOn_finsetSum _ fun b1 _ => ?_
    have hc : ContinuousOn (fun _ : ℝ × ℝ => ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_const
    have hXY : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b1 a1 f p.1 p.2
        * Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (hX b1 a1).mul (hY (b - b1 + 1) (a - a1))
    by_cases h00 : a1 + b1 = 0
    · rw [if_pos h00]
      exact (h0.mul hXY).congr (fun p _ => by simp only [Pi.mul_apply, zero_mul])
    · rw [if_neg h00]
      exact (hc.mul hXY).congr (fun p _ => by simp only [Pi.mul_apply])
  simpa only [leibR] using hmain

/-- Comparison of `canonW q`-weighted product integrals along a pointwise domination of the
weights (a.e. on the quadrant) against a nonnegative factor. -/
theorem integral_mono_canonW {q q' : ℝ} {T : ℝ × ℝ → ℝ}
    (hqq' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → canonW q z θ ≤ canonW q' z θ)
    (hT : ∀ p : ℝ × ℝ, 0 ≤ T p)
    (hint : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q' p.1 p.2 * T p) pm) :
    (∫ p, canonW q p.1 p.2 * T p ∂pm) ≤ ∫ p, canonW q' p.1 p.2 * T p ∂pm := by
  refine MeasureTheory.integral_mono_of_nonneg ?_ hint ?_
  · filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
        0 ≤ canonW q p.1 p.2 * T p) (fun z θ hz hθ hθ2 => by
          have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
          exact mul_nonneg (canonW_nonneg hθI) (hT (z, θ)))] with p hp
    exact hp
  · filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
        canonW q p.1 p.2 * T p ≤ canonW q' p.1 p.2 * T p) (fun z θ hz hθ hθ2 =>
          mul_le_mul_of_nonneg_right (hqq' z θ hz hθ hθ2) (hT (z, θ)))] with p hp
    exact hp

/-- **The bound on the Leibniz remainder.**  For `0 < q ≤ γ` (`q ≤ η` when `a = 0`), a slot
`a + b ≤ 6`, and a `SupPkg` with `Kf ≤ Λ`, `Kg·|f|_{ℋ⁶} ≤ Λ·|g|_{ℋ⁶}`, the `canonW q`-weighted
pairing of `leibR a b f g` with `D_z^bD_θ^a g` is bounded by `64·(a+1)(b+1)·Λ·|g|²_{ℋ⁶}`. -/
theorem leibR_bound {α Kf Kg q Λ : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.HkMem α 6 f)
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (hpkg : SupPkg α f g Kf Kg) (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg)
    (hΛ1 : Kf ≤ Λ)
    (hΛ2 : Kg * Work.Spaces.HkNorm α 6 f ≤ Λ * Work.Spaces.HkNorm α 6 g)
    (hΛE1 : Real.sqrt (10 * excC11) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f ≤ Λ)
    (hΛE2 : Real.sqrt (10 * excC02) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f ≤ Λ)
    (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
        * |leibR a b f g p.1 p.2| * |Work.Spaces.mixed b a g p.1 p.2|) pm ∧
      (∫ p, canonW q p.1 p.2 * |leibR a b f g p.1 p.2|
          * |Work.Spaces.mixed b a g p.1 p.2| ∂pm)
        ≤ 64 * ((a + 1) * (b + 1) : ℝ) * (Λ * Work.Spaces.HkSq α 6 g) := by
  set B : ℝ := Work.Spaces.HkNorm α 6 g with hB
  have hB2 : B ^ 2 = Work.Spaces.HkSq α 6 g := by
    rw [hB]; exact Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 g)
  have hΛ0 : 0 ≤ Λ := le_trans hKf0 hΛ1
  have hhsk : 0 ≤ Work.Spaces.HkSq α 6 g := Work.Spaces.HkSq_nonneg α 6 g
  -- per-summand bound
  have hterm : ∀ a1 ∈ Finset.range (a + 1), ∀ b1 ∈ Finset.range (b + 1),
      MeasureTheory.Integrable (fun p : ℝ × ℝ =>
          (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
          * (canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
            * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
            * |Work.Spaces.mixed b a g p.1 p.2|)) pm ∧
      (∫ p, (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
          * (canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
            * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
            * |Work.Spaces.mixed b a g p.1 p.2|) ∂pm)
        ≤ 64 * (Λ * Work.Spaces.HkSq α 6 g) := by
    intro a1 ha1' b1 hb1'
    have ha1r : a1 ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha1')
    have hb1r : b1 ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb1')
    by_cases h00 : a1 + b1 = 0
    · rw [if_pos h00]
      simp only [zero_mul]
      refine ⟨MeasureTheory.integrable_zero _ _ pm, ?_⟩
      rw [MeasureTheory.integral_zero]
      exact mul_nonneg (by norm_num) (mul_nonneg hΛ0 hhsk)
    · rw [if_neg h00]
      have hp1 : 1 ≤ a1 + b1 := Nat.one_le_iff_ne_zero.mpr h00
      obtain ⟨hint, hbnd⟩ := term_bound (Kf := Kf) (Kg := Kg) (q := q) (Λ := Λ)
        hα hα1 hfs hfm hgs hgm hpkg hKf0 hKg0 hΛ1 hΛ2 hq0 hqγ hqη ha1r hb1r hp1 hab
        hΛE1 hΛE2
      have hbnd' : (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
            * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
            * |Work.Spaces.mixed b a g p.1 p.2| ∂pm) ≤ Λ * Work.Spaces.HkSq α 6 g := by
        rw [← hB2, hB]
        exact hbnd
      have hI0 : 0 ≤ (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
            * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
            * |Work.Spaces.mixed b a g p.1 p.2| ∂pm) :=
        MeasureTheory.integral_nonneg_of_ae
          (Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
            0 ≤ canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
              * |Work.Spaces.mixed b a g p.1 p.2|) (fun z θ hz hθ hθ2 => by
            have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
            exact mul_nonneg (mul_nonneg (mul_nonneg (canonW_nonneg hθI) (abs_nonneg _))
              (abs_nonneg _)) (abs_nonneg _)))
      refine ⟨hint.const_mul _, ?_⟩
      rw [MeasureTheory.integral_const_mul]
      have hcoef : ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)) ≤ 64 := by
        have h1 : (a.choose a1 : ℝ) ≤ 2 ^ a := by
          exact_mod_cast Nat.choose_le_two_pow a a1
        have h2 : (b.choose b1 : ℝ) ≤ 2 ^ b := by
          exact_mod_cast Nat.choose_le_two_pow b b1
        have h3 : (2 : ℝ) ^ a * 2 ^ b = 2 ^ (a + b) := by rw [← pow_add]
        have h4 : (2 : ℝ) ^ (a + b) ≤ 2 ^ 6 :=
          pow_le_pow_right₀ (by norm_num) hab
        nlinarith [h1, h2, h3.le, h3.ge, h4, pow_pos (by norm_num : (0:ℝ) < 2) a,
          pow_pos (by norm_num : (0:ℝ) < 2) b]
      calc ((a.choose a1 : ℝ) * (b.choose b1 : ℝ))
            * (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
              * |Work.Spaces.mixed b a g p.1 p.2| ∂pm)
          ≤ 64 * (∫ p, canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
              * |Work.Spaces.mixed b a g p.1 p.2| ∂pm) :=
            mul_le_mul_of_nonneg_right hcoef hI0
        _ ≤ 64 * (Λ * Work.Spaces.HkSq α 6 g) :=
            mul_le_mul_of_nonneg_left hbnd' (by norm_num)
  -- the pointwise domination of `|R|` by the sum of the summands
  have hRpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * |leibR a b f g z θ| * |Work.Spaces.mixed b a g z θ|
        ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
            * (canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) := by
    intro z θ hz hθ hθ2
    simp only [leibR]
    have hnn : 0 ≤ canonW q z θ := canonW_nonneg ⟨hθ.le, hθ2.le⟩
    have h1 : |∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
          * (Work.Spaces.mixed b1 a1 f z θ * Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ)|
        ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          |(if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
            * (Work.Spaces.mixed b1 a1 f z θ * Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ)| :=
      le_trans (Finset.abs_sum_le_sum_abs
          (fun a1 => ∑ b1 ∈ Finset.range (b + 1),
            (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
              * (Work.Spaces.mixed b1 a1 f z θ
                * Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ))
          (Finset.range (a + 1)))
        (Finset.sum_le_sum fun a1 _ => Finset.abs_sum_le_sum_abs
          (fun b1 => (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
            * (Work.Spaces.mixed b1 a1 f z θ
              * Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ))
          (Finset.range (b + 1)))
    have h2 : canonW q z θ * |∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
          * (Work.Spaces.mixed b1 a1 f z θ * Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ)|
        * |Work.Spaces.mixed b a g z θ|
        ≤ canonW q z θ * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            |(if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
              * (Work.Spaces.mixed b1 a1 f z θ
                * Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ)|)
          * |Work.Spaces.mixed b a g z θ| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hnn) (abs_nonneg _)
    have h3 : canonW q z θ * (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            |(if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
              * (Work.Spaces.mixed b1 a1 f z θ
                * Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ)|)
          * |Work.Spaces.mixed b a g z θ|
        = ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            canonW q z θ * |(if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
              * (Work.Spaces.mixed b1 a1 f z θ
                * Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ)|
              * |Work.Spaces.mixed b a g z θ| := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a1 _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
    have h4 : ∀ a1 ∈ Finset.range (a + 1), ∀ b1 ∈ Finset.range (b + 1),
        canonW q z θ * |(if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
          * (Work.Spaces.mixed b1 a1 f z θ * Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ)|
          * |Work.Spaces.mixed b a g z θ|
        = (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
            * (canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) := by
      intro a1 _ b1 _
      by_cases h00 : a1 + b1 = 0
      · rw [if_pos h00]
        simp only [zero_mul, abs_zero, mul_zero]
      · rw [if_neg h00]
        have hc : 0 ≤ ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)) := by positivity
        rw [abs_mul, abs_of_nonneg hc, abs_mul]
        ring
    exact le_trans h2 (le_trans (le_of_eq h3) (le_of_eq (Finset.sum_congr rfl fun a1 ha1 =>
      Finset.sum_congr rfl fun b1 hb1 => h4 a1 ha1 b1 hb1)))
  -- integrability of the sum and its integral
  have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => ∑ a1 ∈ Finset.range (a + 1),
      ∑ b1 ∈ Finset.range (b + 1),
        (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
          * (canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
            * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
            * |Work.Spaces.mixed b a g p.1 p.2|)) pm := by
    refine MeasureTheory.integrable_finsetSum _ fun a1 ha1' => ?_
    refine MeasureTheory.integrable_finsetSum _ fun b1 hb1' => ?_
    exact (hterm a1 ha1' b1 hb1').1
  have hstep1 : (∫ p, canonW q p.1 p.2 * |leibR a b f g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2| ∂pm)
      ≤ ∫ p, ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
          * (canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
            * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
            * |Work.Spaces.mixed b a g p.1 p.2|) ∂pm := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hInt ?_
    · filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
          0 ≤ canonW q p.1 p.2 * |leibR a b f g p.1 p.2|
            * |Work.Spaces.mixed b a g p.1 p.2|) (fun z θ hz hθ hθ2 => by
          have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
          exact mul_nonneg (mul_nonneg (canonW_nonneg hθI) (abs_nonneg _)) (abs_nonneg _))]
        with p hp
      exact hp
    · filter_upwards [Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
        canonW q p.1 p.2 * |leibR a b f g p.1 p.2| * |Work.Spaces.mixed b a g p.1 p.2| ≤
          ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
              * (canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
                * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
                * |Work.Spaces.mixed b a g p.1 p.2|)) hRpt] with p hp
      exact hp
  have hstep2 : ∀ a1 ∈ Finset.range (a + 1),
      (∫ p, ∑ b1 ∈ Finset.range (b + 1),
        (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
          * (canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
            * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
            * |Work.Spaces.mixed b a g p.1 p.2|) ∂pm)
        ≤ ∑ _b1 ∈ Finset.range (b + 1), 64 * (Λ * Work.Spaces.HkSq α 6 g) := by
    intro a1 ha1'
    rw [MeasureTheory.integral_finsetSum _ (fun b1 hb1' => (hterm a1 ha1' b1 hb1').1)]
    exact Finset.sum_le_sum fun b1 hb1' => (hterm a1 ha1' b1 hb1').2
  have hstep3 : (∑ _a1 ∈ Finset.range (a + 1), ∑ _b1 ∈ Finset.range (b + 1),
        64 * (Λ * Work.Spaces.HkSq α 6 g)) = ((a + 1) * (b + 1) : ℝ)
          * (64 * (Λ * Work.Spaces.HkSq α 6 g)) := by
    rw [Finset.sum_const, Finset.sum_const]
    simp only [Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have hInt2 : ∀ a1 ∈ Finset.range (a + 1),
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ∑ b1 ∈ Finset.range (b + 1),
        (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
          * (canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
            * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
            * |Work.Spaces.mixed b a g p.1 p.2|)) pm := fun a1 ha1' =>
    MeasureTheory.integrable_finsetSum _ fun b1 hb1' => (hterm a1 ha1' b1 hb1').1
  have hmain : (∫ p, canonW q p.1 p.2 * |leibR a b f g p.1 p.2|
        * |Work.Spaces.mixed b a g p.1 p.2| ∂pm)
      ≤ 64 * ((a + 1) * (b + 1) : ℝ) * (Λ * B ^ 2) := by
    calc (∫ p, canonW q p.1 p.2 * |leibR a b f g p.1 p.2|
          * |Work.Spaces.mixed b a g p.1 p.2| ∂pm)
        ≤ ∫ p, ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
            * (canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
              * |Work.Spaces.mixed b a g p.1 p.2|) ∂pm := hstep1
      _ = ∑ a1 ∈ Finset.range (a + 1),
            (∫ p, ∑ b1 ∈ Finset.range (b + 1),
              (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
                * (canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
                  * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
                  * |Work.Spaces.mixed b a g p.1 p.2|) ∂pm) :=
          MeasureTheory.integral_finsetSum _ hInt2
      _ ≤ ∑ _a1 ∈ Finset.range (a + 1), ∑ _b1 ∈ Finset.range (b + 1),
            64 * (Λ * Work.Spaces.HkSq α 6 g) := Finset.sum_le_sum hstep2
      _ = ((a + 1) * (b + 1) : ℝ) * (64 * (Λ * Work.Spaces.HkSq α 6 g)) := hstep3
      _ = 64 * ((a + 1) * (b + 1) : ℝ) * (Λ * B ^ 2) := by
        rw [hB2]; ring
  -- integrability of the weighted absolute value
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * |leibR a b f g p.1 p.2| * |Work.Spaces.mixed b a g p.1 p.2|) pm :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
          (leibR_continuousOn hfs hgs).abs).mul ((hgs.mixed b a).continuousOn.abs))
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ‖canonW q z θ * |leibR a b f g z θ| * |Work.Spaces.mixed b a g z θ|‖
        ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
          (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
            * (canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|) := by
    intro z θ hz hθ hθ2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (mul_nonneg (canonW_nonneg (⟨hθ.le, hθ2.le⟩ : θ ∈ Work.Spaces.Iθ)) (abs_nonneg _))
      (abs_nonneg _))]
    exact hRpt z θ hz hθ hθ2
  have hint : MeasureTheory.Integrable (fun p : ℝ × ℝ => canonW q p.1 p.2
      * |leibR a b f g p.1 p.2| * |Work.Spaces.mixed b a g p.1 p.2|) pm :=
    MeasureTheory.Integrable.mono' hInt haesm
      (Work.FTS.TransportS.ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
        ‖canonW q p.1 p.2 * |leibR a b f g p.1 p.2|
          * |Work.Spaces.mixed b a g p.1 p.2|‖
          ≤ ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
            (if a1 + b1 = 0 then 0 else ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)))
              * (canonW q p.1 p.2 * |Work.Spaces.mixed b1 a1 f p.1 p.2|
                * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g p.1 p.2|
                * |Work.Spaces.mixed b a g p.1 p.2|)) hpt)
  rw [hB2] at hmain
  exact ⟨hint, hmain⟩

end Work.FTS.StrongPersist.N6Trans.SixAux
