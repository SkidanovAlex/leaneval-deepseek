import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds
import Submission.Work.FTS.StrongLWP.Sobolev.EqcBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif.D5

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## From a Bochner `L¹`-bound on the rectangle to the `lintegral` bound

The statements of the compactness extraction are phrased with `lintegral`s of
`ENNReal.ofReal` over the *product* rectangle `[a,b] × [c,d]`, while the elliptic
estimates of `Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds` are phrased with honest
Bochner integrals (iterated over the two intervals).  The two bridges are

* `ofReal (∫ f) = ∫⁻ ofReal f` for a nonnegative integrable `f`, and
* Fubini for the product rectangle (`eqc_setIntegral_rect_eq`). -/

/-- If `f²` is integrable on the rectangle and its (Bochner) integral is at most `K`, then the
`lintegral` of `ofReal (f²)` over the same rectangle is at most `ofReal K`. -/
private theorem lintegral_ofReal_sq_rect_le {a b c d K : ℝ} {f : ℝ × ℝ → ℝ}
    (hint : IntegrableOn (fun p : ℝ × ℝ => (f p) ^ 2) (Set.Icc a b ×ˢ Set.Icc c d))
    (hM : ∫ p in Set.Icc a b ×ˢ Set.Icc c d, (f p) ^ 2 ≤ K) :
    ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d, ENNReal.ofReal ((f p) ^ 2) ≤ ENNReal.ofReal K := by
  have hms : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d) :=
    measurableSet_Icc.prod measurableSet_Icc
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (MeasureTheory.ae_restrict_of_forall_mem hms (fun p _ => sq_nonneg (f p)))]
  exact ENNReal.ofReal_le_ofReal hM

/-- The `lintegral`-form of a rectangle bound for a single (curried) slot: if the slot is
continuous on the closed rectangle and its iterated Bochner `L²`-integral over the rectangle is at
most `K`, then so is the `lintegral` of `ofReal` of its square. -/
private theorem slot_lintegral_le {a b c d K : ℝ} {g : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d))
    (hbd : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (g z θ) ^ 2 ≤ K) :
    ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d, ENNReal.ofReal ((g p.1 p.2) ^ 2) ≤ ENNReal.ofReal K := by
  have hint : IntegrableOn (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2) (Set.Icc a b ×ˢ Set.Icc c d) :=
    (hcont.pow 2).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  refine lintegral_ofReal_sq_rect_le hint ?_
  rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq hint]
  exact hbd

/-! ## Continuity of the four slots on a rectangle inside the open quadrant -/

/-- The four slots `∂_z G`, `∂_z² G`, `∂_θ G`, `∂_θ² G` of `G = D_z^j D_θ^i F` (for `F` smooth on
the open quadrant) are continuous on every closed rectangle contained in `Q0`, `z > 0`.  This is
because on `Q0` each of them is a quotient of a `mixed` slot by a power of `z` or `sin 2θ`
(`mixed_partials_of_smoothOpen`). -/
private theorem slot_cont {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < π / 2) (j i : ℕ) :
    (ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.mixed j i F) p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d)) ∧
    (ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d)) ∧
    (ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.mixed j i F) p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d)) ∧
    (ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d)) := by
  have hR : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    obtain ⟨hz, hθ⟩ := Set.mem_prod.mp hp
    obtain ⟨hz1, _⟩ := Set.mem_Icc.mp hz
    obtain ⟨hθ1, hθ2⟩ := Set.mem_Icc.mp hθ
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hz1, lt_of_lt_of_le hc hθ1, lt_of_le_of_lt hθ2 hd⟩
  have hne : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d, p.1 ≠ 0 := by
    intro p hp
    obtain ⟨hz, _⟩ := Set.mem_prod.mp hp
    obtain ⟨hz1, _⟩ := Set.mem_Icc.mp hz
    exact ne_of_gt (lt_of_lt_of_le ha hz1)
  have hsne : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d, Real.sin (2 * p.2) ≠ 0 := by
    intro p hp
    obtain ⟨_, hθ⟩ := Set.mem_prod.mp hp
    obtain ⟨hθ1, hθ2⟩ := Set.mem_Icc.mp hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hc, hθ1])
      (by linarith [hθ2, hd, Real.pi_pos]))
  have hsin : Continuous (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_snd)
  have hcos : Continuous (fun p : ℝ × ℝ => Real.cos (2 * p.2)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_snd)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `∂_z (D_z^j D_θ^i F) = D_z^{j+1}D_θ^i F / z`
    have hcont : ContinuousOn
        (fun p : ℝ × ℝ => Work.Spaces.mixed (j + 1) i F p.1 p.2 / p.1)
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      ((hF.mixed (j + 1) i).continuousOn.mono hR).div continuous_fst.continuousOn hne
    exact hcont.congr (fun p hp => pz_mixed_div j i hF p.1 p.2 (hR hp))
  · -- `∂_z ∂_z (D_z^j D_θ^i F) = (D_z^{j+2}D_θ^i F - D_z^{j+1}D_θ^i F) / z²`
    have heq : EqOn (fun p : ℝ × ℝ =>
        Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) p.1 p.2)
        (fun p : ℝ × ℝ =>
          (Work.Spaces.mixed (j + 2) i F p.1 p.2 - Work.Spaces.mixed (j + 1) i F p.1 p.2)
            / p.1 ^ 2) (Set.Icc a b ×ˢ Set.Icc c d) := by
      intro p hp
      change Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) p.1 p.2
        = (Work.Spaces.mixed (j + 2) i F p.1 p.2 - Work.Spaces.mixed (j + 1) i F p.1 p.2)
            / p.1 ^ 2
      have h1 : Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) p.1 p.2
          = Work.Spaces.pz (fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z')
              p.1 p.2 :=
        Work.Spaces.pz_congr_of_isOpen
          (f := Work.Spaces.pz (Work.Spaces.mixed j i F))
          (f' := fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z')
          Work.FTS.EllipticEst.isOpen_Q0
          (fun q hq => pz_mixed_div j i hF q.1 q.2 hq) (hR hp)
      rw [h1]
      exact pz_mixed_div_div j i hF p.1 p.2 (hR hp)
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed (j + 2) i F p.1 p.2 - Work.Spaces.mixed (j + 1) i F p.1 p.2)
          / p.1 ^ 2) (Set.Icc a b ×ˢ Set.Icc c d) :=
      (((hF.mixed (j + 2) i).continuousOn.mono hR).sub
        ((hF.mixed (j + 1) i).continuousOn.mono hR)).div
        (continuous_fst.pow 2).continuousOn (fun p hp => pow_ne_zero 2 (hne p hp))
    exact hcont.congr heq
  · -- `∂_θ (D_z^j D_θ^i F) = D_z^j D_θ^{i+1} F / sin 2θ`
    have hcont : ContinuousOn
        (fun p : ℝ × ℝ => Work.Spaces.mixed j (i + 1) F p.1 p.2 / Real.sin (2 * p.2))
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      ((hF.mixed j (i + 1)).continuousOn.mono hR).div hsin.continuousOn hsne
    exact hcont.congr (fun p hp => pth_mixed_div j i hF p.1 p.2 (hR hp))
  · -- `∂_θ ∂_θ (D_z^j D_θ^i F) = D_z^jD_θ^{i+2}F / sin²2θ - 2cos2θ·D_z^jD_θ^{i+1}F/sin²2θ`
    have heq : EqOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) p.1 p.2)
        (fun p : ℝ × ℝ =>
          Work.Spaces.mixed j (i + 2) F p.1 p.2 / (Real.sin (2 * p.2)) ^ 2
            - 2 * Real.cos (2 * p.2) * Work.Spaces.mixed j (i + 1) F p.1 p.2
                / (Real.sin (2 * p.2)) ^ 2) (Set.Icc a b ×ˢ Set.Icc c d) := by
      intro p hp
      change Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) p.1 p.2
        = Work.Spaces.mixed j (i + 2) F p.1 p.2 / (Real.sin (2 * p.2)) ^ 2
            - 2 * Real.cos (2 * p.2) * Work.Spaces.mixed j (i + 1) F p.1 p.2
                / (Real.sin (2 * p.2)) ^ 2
      rw [Work.Spaces.pth_congr_of_isOpen
        (f := Work.Spaces.pth (Work.Spaces.mixed j i F))
        (f' := fun z' θ' => Work.Spaces.mixed j (i + 1) F z' θ' / Real.sin (2 * θ'))
        Work.FTS.EllipticEst.isOpen_Q0
        (fun x hx => pth_mixed_div j i hF x.1 x.2 hx) (hR hp)]
      exact pth_mixed_angdiv j i hF p.1 p.2 (hR hp)
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.mixed j (i + 2) F p.1 p.2 / (Real.sin (2 * p.2)) ^ 2
          - 2 * Real.cos (2 * p.2) * Work.Spaces.mixed j (i + 1) F p.1 p.2
              / (Real.sin (2 * p.2)) ^ 2) (Set.Icc a b ×ˢ Set.Icc c d) := by
      refine (((hF.mixed j (i + 2)).continuousOn.mono hR).div
        (hsin.pow 2).continuousOn (fun p hp => pow_ne_zero 2 (hsne p hp))).sub ?_
      refine (((continuous_const.mul hcos).continuousOn).mul
        ((hF.mixed j (i + 1)).continuousOn.mono hR)).div
        (hsin.pow 2).continuousOn (fun p hp => pow_ne_zero 2 (hsne p hp))
    exact hcont.congr heq

/-! ## The four-slot rectangle bound -/

/-- Assembly: given the four iterated Bochner `L²`-bounds of the slots carried by
`mixed_rect_L2_bounds` (with a common constant `K`), the corresponding four `lintegral` bounds over
the product rectangle hold with the same constant. -/
private theorem four_slot_lintegral_le {a b c d K : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (ha : 0 < a) (hc : 0 < c) (hd : d < π / 2)
    (j i : ℕ)
    (h1 : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
        (Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ K)
    (h2 : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
        (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ K)
    (h3 : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
        (Work.Spaces.pth (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ K)
    (h4 : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
        (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ K) :
    (∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (Work.Spaces.mixed j i F) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal K) ∧
      (∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F))
          p.1 p.2) ^ 2) ≤ ENNReal.ofReal K) ∧
      (∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.mixed j i F) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal K) ∧
      (∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F))
          p.1 p.2) ^ 2) ≤ ENNReal.ofReal K) := by
  obtain ⟨hc1, hc2, hc3, hc4⟩ := slot_cont hF ha hc hd j i
  exact ⟨slot_lintegral_le hc1 h1, slot_lintegral_le hc2 h2, slot_lintegral_le hc3 h3,
    slot_lintegral_le hc4 h4⟩

/-- `HkSq` is bounded by `B²` as soon as the (square root) `HkNorm` is bounded by `B`. -/
private theorem HkSq_le_sq_of_HkNorm_le {α B : ℝ} {F : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkNorm α 6 F ≤ B) : Work.Spaces.HkSq α 6 F ≤ B ^ 2 := by
  have hnn : 0 ≤ Work.Spaces.HkSq α 6 F := Work.Spaces.HkSq_nonneg α 6 F
  have h2 : Work.Spaces.HkNorm α 6 F ^ 2 = Work.Spaces.HkSq α 6 F := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt hnn]
  rw [← h2]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

theorem deriv_slot_lintegral_bounds {α B : ℝ} (hα : 0 < α)
    {F : ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n, Work.FTS.EllipticEst.SmoothOpen (F n))
    (hmem : ∀ n, Work.Spaces.HkMem α 6 (F n))
    (hb : ∀ n, Work.Spaces.HkNorm α 6 (F n) ≤ B)
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hd : d < π / 2)
    (j i : ℕ) (hji : j + i ≤ 4) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ n, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (Work.Spaces.mixed j i (F n)) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal M) ∧
      (∀ n, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i (F n)))
          p.1 p.2) ^ 2) ≤ ENNReal.ofReal M) ∧
      (∀ n, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.mixed j i (F n)) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal M) ∧
      (∀ n, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i (F n)))
          p.1 p.2) ^ 2) ≤ ENNReal.ofReal M) := by
  classical
  -- the universal rectangle constant of the elliptic estimate
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds ha hab hc hd
  have hMnn : 0 ≤ C * B ^ 2 := mul_nonneg hCpos.le (sq_nonneg B)
  have step : ∀ n, (∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (Work.Spaces.mixed j i (F n)) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal (C * B ^ 2)) ∧
      (∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i (F n)))
          p.1 p.2) ^ 2) ≤ ENNReal.ofReal (C * B ^ 2)) ∧
      (∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.mixed j i (F n)) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal (C * B ^ 2)) ∧
      (∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i (F n)))
          p.1 p.2) ^ 2) ≤ ENNReal.ofReal (C * B ^ 2)) := by
    intro n
    obtain ⟨_, b2, b3, b4, _, _, b7⟩ := hC α hα (F n) (hsm n) (hmem n) j i hji
    obtain ⟨k1, k2, k3, k4⟩ := four_slot_lintegral_le (hsm n) ha hc hd j i b2 b4 b3 b7
    have hmono : ENNReal.ofReal (C * Work.Spaces.HkSq α 6 (F n)) ≤ ENNReal.ofReal (C * B ^ 2) :=
      ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (HkSq_le_sq_of_HkNorm_le (hb n)) hCpos.le)
    exact ⟨k1.trans hmono, k2.trans hmono, k3.trans hmono, k4.trans hmono⟩
  exact ⟨C * B ^ 2, hMnn, fun n => (step n).1, fun n => (step n).2.1,
    fun n => (step n).2.2.1, fun n => (step n).2.2.2⟩

end Work.FTS.StrongEps.LocUnif.D5
