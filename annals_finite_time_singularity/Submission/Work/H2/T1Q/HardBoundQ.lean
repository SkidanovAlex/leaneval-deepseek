import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Have
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.FTS.H2.STHardBound
import Submission.Work.FTS.H2.HkIntegrandSlotSum
import Submission.Work.FTS.H2.T1HardWeightAlg
import Submission.Work.FTS.H2.T1Q.Basic
import Submission.Work.FTS.H2.T1HardSlice
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.H2.T1Q.T1HardAesmQ
import Submission.Work.H2.T1Q.SliceLimit
import Submission.Work.H2.T1Q.Cutoff
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.ShrinkInt
import Submission.Work.H2.T1Q.SlotBoundQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.T1Q

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-! ## Auxiliary facts -/

/-- Almost every point of `Iθ = [0,π/2]` lies in the open interval `(0,π/2)`. -/
lemma ae_Iθ_mem_Ioo : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo 0 (π / 2) := by
  rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc,
    MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0, π / 2} : Set ℝ)) ?_ ?_
  · intro θ hθ
    simp only [Set.mem_setOf_eq] at hθ
    have h1 : θ ∈ Work.Spaces.Iθ := by
      by_contra hcon
      exact hθ (fun h => absurd h hcon)
    have h2 : θ ∉ Set.Ioo 0 (π / 2) := fun hioo => hθ (fun _ => hioo)
    simp only [Work.Spaces.Iθ, Set.mem_Icc] at h1
    rw [Set.mem_Ioo, not_and_or, not_lt] at h2
    rcases h2 with h2 | h2
    · exact Or.inl (le_antisymm h2 h1.1)
    · exact Or.inr (le_antisymm h1.2 (not_lt.mp h2))
  · simpa using (Set.Finite.measure_zero (by simp : ({0, π / 2} : Set ℝ).Finite)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ))

/-- A function which is eventually equal to the constant `1` has vanishing derivative. -/
lemma deriv_eq_zero_of_eventuallyEq_one {χ : ℝ → ℝ} {θ : ℝ}
    (h : χ =ᶠ[𝓝 θ] (fun _ => (1 : ℝ))) : deriv χ θ = 0 := by
  have hd : deriv χ θ = deriv (fun _ : ℝ => (1 : ℝ)) θ := h.deriv_eq
  simpa using hd

/-- The weighted pointwise bound on the `W`-factor of the angular integration by parts:
for `|a| ≤ Kf`, `|b| ≤ Kf` and `|1-q| ≤ 1`,
`|a/2 + (1-q)·cos(2θ)·b| ≤ (3/2)Kf`. -/
lemma Wq_bound {Kf q a b θ : ℝ} (hKf0 : 0 ≤ Kf) (h1 : |a| ≤ Kf) (h2 : |b| ≤ Kf)
    (hq : |1 - q| ≤ 1) :
    |(1 / 2) * a + (1 - q) * Real.cos (2 * θ) * b| ≤ (3 / 2) * Kf := by
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have h3 : |(1 / 2) * a| ≤ Kf / 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have h4 : |(1 - q) * Real.cos (2 * θ) * b| ≤ Kf := by
    rw [abs_mul, abs_mul]
    calc |1 - q| * |Real.cos (2 * θ)| * |b| ≤ 1 * 1 * Kf :=
          mul_le_mul (mul_le_mul hq hc (abs_nonneg _) (by norm_num)) h2 (abs_nonneg _)
            (by norm_num)
      _ = Kf := by ring
  calc |(1 / 2) * a + (1 - q) * Real.cos (2 * θ) * b|
      ≤ |(1 / 2) * a| + |(1 - q) * Real.cos (2 * θ) * b| := abs_add_le _ _
    _ ≤ Kf / 2 + Kf := add_le_add h3 h4
    _ = (3 / 2) * Kf := by ring

/-- The sum of five integrals is the integral of the sum. -/
lemma five_integrals_add {a0 a1 a2 a3 a4 : ℝ → ℝ} {s : Set ℝ}
    (h0 : MeasureTheory.IntegrableOn a0 s) (h1 : MeasureTheory.IntegrableOn a1 s)
    (h2 : MeasureTheory.IntegrableOn a2 s) (h3 : MeasureTheory.IntegrableOn a3 s)
    (h4 : MeasureTheory.IntegrableOn a4 s) :
    (∫ x in s, a0 x) + (∫ x in s, a1 x) + (∫ x in s, a2 x) + (∫ x in s, a3 x)
        + (∫ x in s, a4 x)
      = ∫ x in s, (a0 x + a1 x + a2 x + a3 x + a4 x) := by
  have hae : (∫ x in s, (a0 x + a1 x + a2 x + a3 x + a4 x))
      = ∫ x in s, (a0 x + (a1 x + (a2 x + (a3 x + a4 x)))) := by
    congr 1
    funext x
    ring
  have e4 : (∫ x in s, (a0 x + (a1 x + (a2 x + (a3 x + a4 x)))))
      = (∫ x in s, a0 x) + (∫ x in s, (a1 x + (a2 x + (a3 x + a4 x)))) :=
    MeasureTheory.integral_add h0 (h1.add (h2.add (h3.add h4)))
  have e3 : (∫ x in s, (a1 x + (a2 x + (a3 x + a4 x))))
      = (∫ x in s, a1 x) + (∫ x in s, (a2 x + (a3 x + a4 x))) :=
    MeasureTheory.integral_add h1 (h2.add (h3.add h4))
  have e2 : (∫ x in s, (a2 x + (a3 x + a4 x)))
      = (∫ x in s, a2 x) + (∫ x in s, (a3 x + a4 x)) :=
    MeasureTheory.integral_add h2 (h3.add h4)
  have e1 : (∫ x in s, (a3 x + a4 x)) = (∫ x in s, a3 x) + (∫ x in s, a4 x) :=
    MeasureTheory.integral_add h3 h4
  rw [hae, e4, e3, e2, e1]
  ring

/-- The sum of the five order-four `θ`-slice energies of `g` at `(z,θ)`: the `D_z⁴` block with
its `η`-weight and the four mixed blocks with the `γ`-weight. -/
noncomputable def badSlot (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.DzIter 4 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
    + ((Work.Spaces.mixed 3 1 g z θ) ^ 2 + (Work.Spaces.mixed 2 2 g z θ) ^ 2
        + (Work.Spaces.mixed 1 3 g z θ) ^ 2 + (Work.Spaces.mixed 0 4 g z θ) ^ 2)
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))

lemma badSlot_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ badSlot α g z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.bt_sin_nonneg hθ
  have h1 : 0 ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := Real.rpow_nonneg hs _
  have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs _
  have h3 : 0 ≤ (Work.Spaces.mixed 3 1 g z θ) ^ 2 + (Work.Spaces.mixed 2 2 g z θ) ^ 2
      + (Work.Spaces.mixed 1 3 g z θ) ^ 2 + (Work.Spaces.mixed 0 4 g z θ) ^ 2 := by
    have a := sq_nonneg (Work.Spaces.mixed 3 1 g z θ)
    have b := sq_nonneg (Work.Spaces.mixed 2 2 g z θ)
    have c := sq_nonneg (Work.Spaces.mixed 1 3 g z θ)
    have d := sq_nonneg (Work.Spaces.mixed 0 4 g z θ)
    linarith
  exact add_nonneg (mul_nonneg (sq_nonneg _) h1) (mul_nonneg h3 h2)

/-- **The per-slot bound of the cut-off method.**  From the angular integration by parts with a
cut-off factor `χ`,

`∫_θ sin(2θ)^{-q}·(χ·F)·D_θ(V)·V = -∫_θ sin(2θ)^{-q}·(χ·W + (1/2)·D_θ(χ)·F)·V²`,

the pointwise bounds `|F| ≤ Kf`, `|W| ≤ (3/2)Kf` and `|sin(2θ)·χ'| ≤ B`, and the support
`χ' = 0` off `(0,ζ) ∪ (π/2-ζ, π/2)` one gets

`|∫_θ χ·F·D_θ(V)·V·sin(2θ)^{-q}| ≤ (3/2)Kf·∫_θ V²sin(2θ)^{-q}
   + (Kf·B/2)·(∫_{(0,ζ)} V²sin(2θ)^{-q} + ∫_{(π/2-ζ,π/2)} V²sin(2θ)^{-q})`. -/
lemma slotBound_cutoff {q Kf B ζ : ℝ} {χ F V : ℝ → ℝ}
    (hKf0 : 0 ≤ Kf) (hB0 : 0 ≤ B) (hζ : 0 < ζ) (hζ2 : 2 * ζ ≤ π / 2)
    (hχnn : ∀ θ : ℝ, 0 ≤ χ θ) (hχle : ∀ θ : ℝ, χ θ ≤ 1)
    (hsd : ∀ θ ∈ Set.Ioo 0 (π / 2), |Real.sin (2 * θ) * deriv χ θ|
      ≤ B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
          + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ))
    (hFb : ∀ θ ∈ Set.Ioo 0 (π / 2), |F θ| ≤ Kf)
    (hWb : ∀ θ ∈ Set.Ioo 0 (π / 2),
      |(1 / 2) * (Real.sin (2 * θ) * deriv F θ) + (1 - q) * Real.cos (2 * θ) * F θ|
        ≤ (3 / 2) * Kf)
    (hVint : MeasureTheory.IntegrableOn
      (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) Work.Spaces.Iθ)
    (hAint : MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-q)
      * (χ θ * F θ) * (Real.sin (2 * θ) * deriv V θ) * V θ) Work.Spaces.Iθ)
    (hIBP : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) * (χ θ * F θ)
          * (Real.sin (2 * θ) * deriv V θ) * V θ
        = -∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
                + (1 - q) * Real.cos (2 * θ) * F θ)
              + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ) * (V θ) ^ 2) :
    |∫ θ in Work.Spaces.Iθ, χ θ * (F θ * (Real.sin (2 * θ) * deriv V θ) * V θ
        * (Real.sin (2 * θ)) ^ (-q))|
      ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ,
            (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        + (Kf * B / 2) * ((∫ θ in Set.Ioc 0 (2 * ζ),
              (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            + ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2),
                (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- rewrite the left-hand side as the left-hand side of the integration by parts
  have hAeq : (∫ θ in Work.Spaces.Iθ, χ θ * (F θ * (Real.sin (2 * θ) * deriv V θ) * V θ
        * (Real.sin (2 * θ)) ^ (-q)))
      = ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) * (χ θ * F θ)
          * (Real.sin (2 * θ) * deriv V θ) * V θ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    ring
  rw [hAeq, hIBP, abs_neg]
  -- the pointwise comparison with the majorant
  have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |(Real.sin (2 * θ)) ^ (-q) * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
            + (1 - q) * Real.cos (2 * θ) * F θ)
          + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ) * (V θ) ^ 2|
        ≤ (3 / 2) * Kf * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
          + (Kf * B / 2) * ((Set.Ioc 0 (2 * ζ)).indicator
                (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ
              + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
                (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ) := by
    filter_upwards [ae_Iθ_mem_Ioo] with θ hθ
    have hs : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hsq : 0 ≤ (Real.sin (2 * θ)) ^ (-q) := Real.rpow_nonneg hs _
    have hV2 : 0 ≤ (V θ) ^ 2 := sq_nonneg _
    have hW := hWb θ hθ
    have hF := hFb θ hθ
    have hinner : |χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
          + (1 - q) * Real.cos (2 * θ) * F θ) + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ|
        ≤ (3 / 2) * Kf + (Kf / 2) * |Real.sin (2 * θ) * deriv χ θ| := by
      calc |χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
              + (1 - q) * Real.cos (2 * θ) * F θ)
            + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ|
          ≤ |χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
                + (1 - q) * Real.cos (2 * θ) * F θ)|
            + |(1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ| := abs_add_le _ _
        _ = χ θ * |(1 / 2) * (Real.sin (2 * θ) * deriv F θ)
                + (1 - q) * Real.cos (2 * θ) * F θ|
            + (1 / 2) * |Real.sin (2 * θ) * deriv χ θ| * |F θ| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hχnn θ),
                abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        _ ≤ 1 * ((3 / 2) * Kf) + (1 / 2) * |Real.sin (2 * θ) * deriv χ θ| * Kf := by
              refine add_le_add ?_ ?_
              · exact mul_le_mul (hχle θ) hW (abs_nonneg _) (by linarith)
              · have h2 : 0 ≤ (1 / 2 : ℝ) * |Real.sin (2 * θ) * deriv χ θ| := by positivity
                exact mul_le_mul_of_nonneg_left hF h2
        _ = (3 / 2) * Kf + (Kf / 2) * |Real.sin (2 * θ) * deriv χ θ| := by ring
    have hIA : (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
        * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        = (Set.Ioc 0 (2 * ζ)).indicator (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ := by
      by_cases hm : θ ∈ Set.Ioc 0 (2 * ζ)
      · simp [Set.indicator_of_mem hm]
      · simp [Set.indicator_of_notMem hm]
    have hIB : (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ
        * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        = (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
            (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ := by
      by_cases hm : θ ∈ Set.Ioc (π / 2 - 2 * ζ) (π / 2)
      · simp [Set.indicator_of_mem hm]
      · simp [Set.indicator_of_notMem hm]
    have hnorm : |(Real.sin (2 * θ)) ^ (-q) * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
              + (1 - q) * Real.cos (2 * θ) * F θ)
            + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ) * (V θ) ^ 2|
        = (Real.sin (2 * θ)) ^ (-q)
          * |χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
              + (1 - q) * Real.cos (2 * θ) * F θ)
            + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ| * (V θ) ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hsq, abs_of_nonneg hV2]
    rw [hnorm]
    have hv : 0 ≤ (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) := mul_nonneg hV2 hsq
    calc (Real.sin (2 * θ)) ^ (-q) * |χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
              + (1 - q) * Real.cos (2 * θ) * F θ)
            + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ| * (V θ) ^ 2
        ≤ (Real.sin (2 * θ)) ^ (-q) * ((3 / 2) * Kf
            + (Kf / 2) * |Real.sin (2 * θ) * deriv χ θ|) * (V θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinner hsq) hV2
      _ = (3 / 2) * Kf * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            + (Kf / 2) * |Real.sin (2 * θ) * deriv χ θ|
              * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by ring
      _ ≤ (3 / 2) * Kf * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            + (Kf / 2) * (B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
                + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ))
              * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
          refine add_le_add le_rfl ?_
          have hv' : 0 ≤ (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) := hv
          have hK : 0 ≤ Kf / 2 := by linarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hsd θ hθ) hK) hv'
      _ = (3 / 2) * Kf * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            + (Kf * B / 2) * ((Set.Ioc 0 (2 * ζ)).indicator
                  (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ
                + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
                  (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ) := by
          rw [← hIA, ← hIB]; ring
  -- the majorant is integrable
  have hmaj : MeasureTheory.Integrable (fun θ => (3 / 2) * Kf
        * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      + (Kf * B / 2) * ((Set.Ioc 0 (2 * ζ)).indicator
            (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ
          + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
            (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.add (hVint.const_mul _) (MeasureTheory.Integrable.const_mul ?_ _)
    exact (MeasureTheory.IntegrableOn.indicator hVint measurableSet_Ioc).add
      (MeasureTheory.IntegrableOn.indicator hVint measurableSet_Ioc)
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem hIθ (fun θ _ => abs_nonneg _)) hmaj hpt
  -- evaluate the integral of the majorant
  have hval : (∫ θ in Work.Spaces.Iθ, ((3 / 2) * Kf
        * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      + (Kf * B / 2) * ((Set.Ioc 0 (2 * ζ)).indicator
            (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ
          + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
            (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ)))
      = (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        + (Kf * B / 2) * ((∫ θ in Set.Ioc 0 (2 * ζ),
              (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            + ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2),
                (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := by
    have h1 : MeasureTheory.Integrable (fun θ => (Set.Ioc 0 (2 * ζ)).indicator
          (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.IntegrableOn.indicator hVint measurableSet_Ioc
    have h2 : MeasureTheory.Integrable (fun θ => (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
          (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.IntegrableOn.indicator hVint measurableSet_Ioc
    have hs1 : (∫ θ in Work.Spaces.Iθ, (Set.Ioc 0 (2 * ζ)).indicator
          (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ)
        = ∫ θ in Set.Ioc 0 (2 * ζ), (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) := by
      rw [MeasureTheory.integral_indicator measurableSet_Ioc]
      congr 1
      rw [MeasureTheory.Measure.restrict_restrict measurableSet_Ioc,
        Set.inter_eq_self_of_subset_left]
      intro θ hθ
      exact ⟨le_of_lt hθ.1, le_trans hθ.2 hζ2⟩
    have hs2 : (∫ θ in Work.Spaces.Iθ, (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
          (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ)
        = ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2),
            (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) := by
      rw [MeasureTheory.integral_indicator measurableSet_Ioc]
      congr 1
      rw [MeasureTheory.Measure.restrict_restrict measurableSet_Ioc,
        Set.inter_eq_self_of_subset_left]
      intro θ hθ
      exact ⟨by linarith [hθ.1, hζ, Real.pi_pos], hθ.2⟩
    have e1 : (∫ θ in Work.Spaces.Iθ, ((3 / 2) * Kf
            * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
          + (Kf * B / 2) * ((Set.Ioc 0 (2 * ζ)).indicator
                (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ
              + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
                (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ)))
        = (∫ θ in Work.Spaces.Iθ, (3 / 2) * Kf
              * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
          + (∫ θ in Work.Spaces.Iθ, (Kf * B / 2) * ((Set.Ioc 0 (2 * ζ)).indicator
                (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ
              + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
                (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ)) :=
      MeasureTheory.integral_add (hVint.const_mul _) ((h1.add h2).const_mul _)
    rw [e1, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add h1 h2, hs1, hs2]
  calc |∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
        * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
            + (1 - q) * Real.cos (2 * θ) * F θ)
          + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ) * (V θ) ^ 2|
      ≤ ∫ θ in Work.Spaces.Iθ, |(Real.sin (2 * θ)) ^ (-q)
          * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv F θ)
              + (1 - q) * Real.cos (2 * θ) * F θ)
            + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * F θ) * (V θ) ^ 2| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ θ in Work.Spaces.Iθ, ((3 / 2) * Kf * ((V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
          + (Kf * B / 2) * ((Set.Ioc 0 (2 * ζ)).indicator
                (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ
              + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
                (fun θ => (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) θ)) := hmono
    _ = (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ,
            (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        + (Kf * B / 2) * ((∫ θ in Set.Ioc 0 (2 * ζ),
              (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            + ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2),
                (V θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) := hval

/-- **The pointwise bound for the cut-off version of the hard part.**  For the cut-off `χ ζ` of
the package `Cutoff`, the integral of `χ ζ · T1Hard α f g z ·` over `Iθ` is bounded by
`(3/2)Kf·∫_θ HkIntegrand α 4 g z θ` plus the two shrinking contributions. -/
lemma cutoff_bound (α Kf B : ℝ) (f g : ℝ → ℝ → ℝ) (χ : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hB : 0 < B) (hKf0 : 0 ≤ Kf)
    (hsmf : Work.FTS.LocData.SmoothQuad f) (hsmg : Work.FTS.LocData.SmoothQuad g)
    (hmg : Work.Spaces.HkMem α 4 g)
    (hKf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Kf)
    (hKfd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.Dth f z θ| ≤ Kf)
    (hχsm : ∀ ζ : ℝ, ContDiff ℝ (⊤ : ℕ∞) (χ ζ))
    (hχnn : ∀ ζ θ : ℝ, 0 ≤ χ ζ θ)
    (hχle : ∀ ζ θ : ℝ, χ ζ θ ≤ 1)
    (hχone : ∀ ζ θ : ℝ, 0 < ζ → ζ ≤ θ → θ ≤ π / 2 - ζ → χ ζ θ = 1)
    (hχz0l : ∀ ζ θ : ℝ, 0 < ζ → θ ≤ ζ / 2 → χ ζ θ = 0)
    (hχz0r : ∀ ζ θ : ℝ, 0 < ζ → π / 2 - ζ / 2 ≤ θ → χ ζ θ = 0)
    (hχd0l : ∀ ζ θ : ℝ, 0 < ζ → θ < ζ / 2 → deriv (χ ζ) θ = 0)
    (hχd0r : ∀ ζ θ : ℝ, 0 < ζ → π / 2 - ζ / 2 < θ → deriv (χ ζ) θ = 0)
    (hχbd : ∀ ζ : ℝ, 0 < ζ → ∀ θ : ℝ, |Real.sin (2 * θ) * deriv (χ ζ) θ| ≤ B)
    {z ζ : ℝ} (hz : 0 < z) (hζ : 0 < ζ) (hζ4 : ζ ≤ 1 / 4) :
    |∫ θ in Work.Spaces.Iθ, χ ζ θ * Work.FTS.H2.T1Hard α f g z θ|
      ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + (Kf * B / 2) * (Work.Spaces.w z) ^ 2 *
            ((∫ θ in Set.Ioc 0 (2 * ζ), badSlot α g z θ)
              + ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), badSlot α g z θ) := by
  have hzI : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hζ2 : ζ ≤ π / 2 := by linarith [Real.pi_gt_three, hζ4]
  have hζ2' : 2 * ζ ≤ π / 2 := by linarith [Real.pi_gt_three, hζ4]
  -- the derived support of `deriv (χ ζ)`
  have hχmid : ∀ θ ∈ Set.Ioo ζ (π / 2 - ζ), deriv (χ ζ) θ = 0 := by
    intro θ hθ
    have hev : χ ζ =ᶠ[𝓝 θ] (fun _ => (1 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      exact hχone ζ θ' hζ (le_of_lt hθ'.1) (le_of_lt hθ'.2)
    exact deriv_eq_zero_of_eventuallyEq_one hev
  have hindnn : ∀ θ : ℝ, 0 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
      + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
    intro θ
    have a : 0 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ := by
      by_cases hm : θ ∈ Set.Ioc 0 (2 * ζ)
      · simp [Set.indicator_of_mem hm]
      · simp [Set.indicator_of_notMem hm]
    have b : 0 ≤ (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
      by_cases hm : θ ∈ Set.Ioc (π / 2 - 2 * ζ) (π / 2)
      · simp [Set.indicator_of_mem hm]
      · simp [Set.indicator_of_notMem hm]
    linarith
  have hsd : ∀ θ ∈ Set.Ioo 0 (π / 2), |Real.sin (2 * θ) * deriv (χ ζ) θ|
      ≤ B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
          + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ) := by
    intro θ hθ
    by_cases h1 : θ < ζ / 2
    · rw [hχd0l ζ θ hζ h1, mul_zero, abs_zero]
      exact mul_nonneg hB.le (hindnn θ)
    by_cases h2 : π / 2 - ζ / 2 < θ
    · rw [hχd0r ζ θ hζ h2, mul_zero, abs_zero]
      exact mul_nonneg hB.le (hindnn θ)
    by_cases h3 : θ ≤ 2 * ζ
    · have hA : θ ∈ Set.Ioc 0 (2 * ζ) := ⟨by linarith, h3⟩
      have hind : 1 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
          + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
        have ha : (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ = 1 :=
          Set.indicator_of_mem hA _
        have hb : 0 ≤ (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator
            (fun _ => (1 : ℝ)) θ := by
          by_cases hm : θ ∈ Set.Ioc (π / 2 - 2 * ζ) (π / 2)
          · simp [Set.indicator_of_mem hm]
          · simp [Set.indicator_of_notMem hm]
        rw [ha]; linarith
      calc |Real.sin (2 * θ) * deriv (χ ζ) θ| ≤ B := hχbd ζ hζ θ
        _ = B * 1 := by ring
        _ ≤ B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
              + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ) :=
            mul_le_mul_of_nonneg_left hind hB.le
    · have h3' : 2 * ζ < θ := not_le.mp h3
      by_cases h4 : π / 2 - 2 * ζ < θ
      · have hB' : θ ∈ Set.Ioc (π / 2 - 2 * ζ) (π / 2) :=
          ⟨h4, by linarith [not_lt.mp h2, Real.pi_pos]⟩
        have hind : 1 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
            + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
          have hb : (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ = 1 :=
            Set.indicator_of_mem hB' _
          have ha : 0 ≤ (Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ := by
            by_cases hm : θ ∈ Set.Ioc 0 (2 * ζ)
            · simp [Set.indicator_of_mem hm]
            · simp [Set.indicator_of_notMem hm]
          rw [hb]; linarith
        calc |Real.sin (2 * θ) * deriv (χ ζ) θ| ≤ B := hχbd ζ hζ θ
          _ = B * 1 := by ring
          _ ≤ B * ((Set.Ioc 0 (2 * ζ)).indicator (fun _ => (1 : ℝ)) θ
                + (Set.Ioc (π / 2 - 2 * ζ) (π / 2)).indicator (fun _ => (1 : ℝ)) θ) :=
              mul_le_mul_of_nonneg_left hind hB.le
      · have hmid : deriv (χ ζ) θ = 0 :=
          hχmid θ ⟨by linarith, by linarith [not_lt.mp h4]⟩
        rw [hmid, mul_zero, abs_zero]
        exact mul_nonneg hB.le (hindnn θ)
  -- the pointwise `f`-bound on the open interval
  have hFb : ∀ θ ∈ Set.Ioo 0 (π / 2), |f z θ| ≤ Kf := fun θ hθ => hKf z θ hz hθ.1 hθ.2
  -- the pointwise `W`-bounds
  have hFdb : ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Real.sin (2 * θ) * deriv (fun θ' => f z θ') θ| ≤ Kf := by
    intro θ hθ
    have h := hKfd z θ hz hθ.1 hθ.2
    simpa only [Work.Spaces.Dth, Work.Spaces.pth] using h
  have hWη : ∀ θ ∈ Set.Ioo 0 (π / 2),
      |(1 / 2) * (Real.sin (2 * θ) * deriv (fun θ' => f z θ') θ)
        + (1 - Work.Spaces.eta) * Real.cos (2 * θ) * f z θ| ≤ (3 / 2) * Kf :=
    fun θ hθ => Wq_bound hKf0 (hFdb θ hθ) (hFb θ hθ)
      (by rw [abs_le]; constructor <;> norm_num [Work.Spaces.eta])
  have hWγ : ∀ θ ∈ Set.Ioo 0 (π / 2),
      |(1 / 2) * (Real.sin (2 * θ) * deriv (fun θ' => f z θ') θ)
        + (1 - Work.Spaces.gam α) * Real.cos (2 * θ) * f z θ| ≤ (3 / 2) * Kf := by
    intro θ hθ
    have hg : Work.Spaces.gam α ≤ 11 / 10 := by rw [Work.Spaces.gam]; linarith
    have hg0 : 1 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
    refine Wq_bound hKf0 (hFdb θ hθ) (hFb θ hθ) ?_
    rw [abs_le]
    constructor <;> linarith
  -- smoothness of the slices
  have hFcd : ContDiffOn ℝ 1 (fun θ => f z θ) (Set.Ioo 0 (π / 2)) :=
    (hsmf.curry_θ hzI).of_le (m := (1 : ℕ∞)) (by simp)
  have hV0cd : ContDiffOn ℝ 1 (fun θ => Work.Spaces.DzIter 4 g z θ) (Set.Ioo 0 (π / 2)) :=
    ((hsmg.DzIter 4).curry_θ hzI).of_le (m := (1 : ℕ∞)) (by simp)
  have hV1cd : ContDiffOn ℝ 1 (fun θ => Work.Spaces.mixed 3 1 g z θ)
      (Set.Ioo 0 (π / 2)) :=
    ((hsmg.mixed 3 1).curry_θ hzI).of_le (m := (1 : ℕ∞)) (by simp)
  have hV2cd : ContDiffOn ℝ 1 (fun θ => Work.Spaces.mixed 2 2 g z θ)
      (Set.Ioo 0 (π / 2)) :=
    ((hsmg.mixed 2 2).curry_θ hzI).of_le (m := (1 : ℕ∞)) (by simp)
  have hV3cd : ContDiffOn ℝ 1 (fun θ => Work.Spaces.mixed 1 3 g z θ)
      (Set.Ioo 0 (π / 2)) :=
    ((hsmg.mixed 1 3).curry_θ hzI).of_le (m := (1 : ℕ∞)) (by simp)
  have hV4cd : ContDiffOn ℝ 1 (fun θ => Work.Spaces.mixed 0 4 g z θ)
      (Set.Ioo 0 (π / 2)) :=
    ((hsmg.mixed 0 4).curry_θ hzI).of_le (m := (1 : ℕ∞)) (by simp)
  -- the five slot integrals
  obtain ⟨hS0, hSmix, hSbd⟩ := SlotBoundQ α g hsmg hmg hz
  have hDth_eq (v : ℝ → ℝ → ℝ) (θ : ℝ) :
      Work.Spaces.Dth v z θ = Real.sin (2 * θ) * deriv (fun θ' => v z θ') θ := rfl
  -- the IBP identities
  have hIBP0 := IbpCutoff (q := Work.Spaces.eta) (δ := ζ / 2) Work.Spaces.eta_pos
    (χ := χ ζ) (hf := fun θ => f z θ) (hv := fun θ => Work.Spaces.DzIter 4 g z θ)
    (hχsm ζ) (by linarith) (by linarith [Real.pi_pos]) (fun θ hθ => hχz0l ζ θ hζ hθ)
    (fun θ hθ => hχz0r ζ θ hζ hθ) hFcd hV0cd
  have hIBP1 := IbpCutoff (q := Work.Spaces.gam α) (δ := ζ / 2) (Work.Spaces.gam_pos hα)
    (χ := χ ζ) (hf := fun θ => f z θ) (hv := fun θ => Work.Spaces.mixed 3 1 g z θ)
    (hχsm ζ) (by linarith) (by linarith [Real.pi_pos]) (fun θ hθ => hχz0l ζ θ hζ hθ)
    (fun θ hθ => hχz0r ζ θ hζ hθ) hFcd hV1cd
  have hIBP2 := IbpCutoff (q := Work.Spaces.gam α) (δ := ζ / 2) (Work.Spaces.gam_pos hα)
    (χ := χ ζ) (hf := fun θ => f z θ) (hv := fun θ => Work.Spaces.mixed 2 2 g z θ)
    (hχsm ζ) (by linarith) (by linarith [Real.pi_pos]) (fun θ hθ => hχz0l ζ θ hζ hθ)
    (fun θ hθ => hχz0r ζ θ hζ hθ) hFcd hV2cd
  have hIBP3 := IbpCutoff (q := Work.Spaces.gam α) (δ := ζ / 2) (Work.Spaces.gam_pos hα)
    (χ := χ ζ) (hf := fun θ => f z θ) (hv := fun θ => Work.Spaces.mixed 1 3 g z θ)
    (hχsm ζ) (by linarith) (by linarith [Real.pi_pos]) (fun θ hθ => hχz0l ζ θ hζ hθ)
    (fun θ hθ => hχz0r ζ θ hζ hθ) hFcd hV3cd
  have hIBP4 := IbpCutoff (q := Work.Spaces.gam α) (δ := ζ / 2) (Work.Spaces.gam_pos hα)
    (χ := χ ζ) (hf := fun θ => f z θ) (hv := fun θ => Work.Spaces.mixed 0 4 g z θ)
    (hχsm ζ) (by linarith) (by linarith [Real.pi_pos]) (fun θ hθ => hχz0l ζ θ hζ hθ)
    (fun θ hθ => hχz0r ζ θ hζ hθ) hFcd hV4cd
  -- the five per-slot bounds
  have hb0 := slotBound_cutoff (q := Work.Spaces.eta) (Kf := Kf) (B := B) (ζ := ζ)
    (χ := χ ζ) (F := fun θ => f z θ) (V := fun θ => Work.Spaces.DzIter 4 g z θ)
    hKf0 hB.le hζ hζ2' (fun θ => hχnn ζ θ) (fun θ => hχle ζ θ)
    hsd hFb hWη hS0 hIBP0.1 hIBP0.2
  have hb1 := slotBound_cutoff (q := Work.Spaces.gam α) (Kf := Kf) (B := B) (ζ := ζ)
    (χ := χ ζ) (F := fun θ => f z θ) (V := fun θ => Work.Spaces.mixed 3 1 g z θ)
    hKf0 hB.le hζ hζ2' (fun θ => hχnn ζ θ) (fun θ => hχle ζ θ)
    hsd hFb hWγ (hSmix 3 1 (by norm_num) (by norm_num)) hIBP1.1 hIBP1.2
  have hb2 := slotBound_cutoff (q := Work.Spaces.gam α) (Kf := Kf) (B := B) (ζ := ζ)
    (χ := χ ζ) (F := fun θ => f z θ) (V := fun θ => Work.Spaces.mixed 2 2 g z θ)
    hKf0 hB.le hζ hζ2' (fun θ => hχnn ζ θ) (fun θ => hχle ζ θ)
    hsd hFb hWγ (hSmix 2 2 (by norm_num) (by norm_num)) hIBP2.1 hIBP2.2
  have hb3 := slotBound_cutoff (q := Work.Spaces.gam α) (Kf := Kf) (B := B) (ζ := ζ)
    (χ := χ ζ) (F := fun θ => f z θ) (V := fun θ => Work.Spaces.mixed 1 3 g z θ)
    hKf0 hB.le hζ hζ2' (fun θ => hχnn ζ θ) (fun θ => hχle ζ θ)
    hsd hFb hWγ (hSmix 1 3 (by norm_num) (by norm_num)) hIBP3.1 hIBP3.2
  have hb4 := slotBound_cutoff (q := Work.Spaces.gam α) (Kf := Kf) (B := B) (ζ := ζ)
    (χ := χ ζ) (F := fun θ => f z θ) (V := fun θ => Work.Spaces.mixed 0 4 g z θ)
    hKf0 hB.le hζ hζ2' (fun θ => hχnn ζ θ) (fun θ => hχle ζ θ)
    hsd hFb hWγ (hSmix 0 4 (by norm_num) (by norm_num)) hIBP4.1 hIBP4.2
  -- the five slot integrands and their integrals
  set F : ℝ → ℝ := fun θ => f z θ with hFdef
  set V0 : ℝ → ℝ := fun θ => Work.Spaces.DzIter 4 g z θ with hV0def
  set V1 : ℝ → ℝ := fun θ => Work.Spaces.mixed 3 1 g z θ with hV1def
  set V2 : ℝ → ℝ := fun θ => Work.Spaces.mixed 2 2 g z θ with hV2def
  set V3 : ℝ → ℝ := fun θ => Work.Spaces.mixed 1 3 g z θ with hV3def
  set V4 : ℝ → ℝ := fun θ => Work.Spaces.mixed 0 4 g z θ with hV4def
  set q0 : ℝ := Work.Spaces.eta with hq0def
  set q1 : ℝ := Work.Spaces.gam α with hq1def
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  -- the pointwise identity expressing `T1Hard` through the five slots
  have hpoint : ∀ θ : ℝ, Work.FTS.H2.T1Hard α f g z θ = (Work.Spaces.w z) ^ 2
      * (F θ * (Real.sin (2 * θ) * deriv V0 θ) * V0 θ * (Real.sin (2 * θ)) ^ (-q0)
        + F θ * (Real.sin (2 * θ) * deriv V1 θ) * V1 θ * (Real.sin (2 * θ)) ^ (-q1)
        + F θ * (Real.sin (2 * θ) * deriv V2 θ) * V2 θ * (Real.sin (2 * θ)) ^ (-q1)
        + F θ * (Real.sin (2 * θ) * deriv V3 θ) * V3 θ * (Real.sin (2 * θ)) ^ (-q1)
        + F θ * (Real.sin (2 * θ) * deriv V4 θ) * V4 θ * (Real.sin (2 * θ)) ^ (-q1)) := by
    intro θ
    simp only [hFdef, hV0def, hV1def, hV2def, hV3def, hV4def, hq0def, hq1def,
      Work.FTS.H2.T1Hard, Work.Spaces.Dth, Work.Spaces.pth]
    simp only [Work.Spaces.DzIter, Work.Spaces.mixed]
    ring
  -- the slot integrabilities (with the cut-off inserted)
  have hint0 : MeasureTheory.IntegrableOn (fun θ => χ ζ θ * (F θ
      * (Real.sin (2 * θ) * deriv V0 θ) * V0 θ * (Real.sin (2 * θ)) ^ (-q0)))
      Work.Spaces.Iθ := by
    refine hIBP0.1.congr_fun (fun θ _ => ?_) measurableSet_Icc
    simp only [hFdef, hV0def, hq0def]; ring
  have hint1 : MeasureTheory.IntegrableOn (fun θ => χ ζ θ * (F θ
      * (Real.sin (2 * θ) * deriv V1 θ) * V1 θ * (Real.sin (2 * θ)) ^ (-q1)))
      Work.Spaces.Iθ := by
    refine hIBP1.1.congr_fun (fun θ _ => ?_) measurableSet_Icc
    simp only [hFdef, hV1def, hq1def]; ring
  have hint2 : MeasureTheory.IntegrableOn (fun θ => χ ζ θ * (F θ
      * (Real.sin (2 * θ) * deriv V2 θ) * V2 θ * (Real.sin (2 * θ)) ^ (-q1)))
      Work.Spaces.Iθ := by
    refine hIBP2.1.congr_fun (fun θ _ => ?_) measurableSet_Icc
    simp only [hFdef, hV2def, hq1def]; ring
  have hint3 : MeasureTheory.IntegrableOn (fun θ => χ ζ θ * (F θ
      * (Real.sin (2 * θ) * deriv V3 θ) * V3 θ * (Real.sin (2 * θ)) ^ (-q1)))
      Work.Spaces.Iθ := by
    refine hIBP3.1.congr_fun (fun θ _ => ?_) measurableSet_Icc
    simp only [hFdef, hV3def, hq1def]; ring
  have hint4 : MeasureTheory.IntegrableOn (fun θ => χ ζ θ * (F θ
      * (Real.sin (2 * θ) * deriv V4 θ) * V4 θ * (Real.sin (2 * θ)) ^ (-q1)))
      Work.Spaces.Iθ := by
    refine hIBP4.1.congr_fun (fun θ _ => ?_) measurableSet_Icc
    simp only [hFdef, hV4def, hq1def]; ring
  -- the split of the integral of `χ ζ · T1Hard`
  -- the five slot integrands (with the cut-off inserted)
  set S0 : ℝ → ℝ := fun θ => χ ζ θ * (F θ * (Real.sin (2 * θ) * deriv V0 θ)
    * V0 θ * (Real.sin (2 * θ)) ^ (-q0)) with hS0def
  set S1 : ℝ → ℝ := fun θ => χ ζ θ * (F θ * (Real.sin (2 * θ) * deriv V1 θ)
    * V1 θ * (Real.sin (2 * θ)) ^ (-q1)) with hS1def
  set S2 : ℝ → ℝ := fun θ => χ ζ θ * (F θ * (Real.sin (2 * θ) * deriv V2 θ)
    * V2 θ * (Real.sin (2 * θ)) ^ (-q1)) with hS2def
  set S3 : ℝ → ℝ := fun θ => χ ζ θ * (F θ * (Real.sin (2 * θ) * deriv V3 θ)
    * V3 θ * (Real.sin (2 * θ)) ^ (-q1)) with hS3def
  set S4 : ℝ → ℝ := fun θ => χ ζ θ * (F θ * (Real.sin (2 * θ) * deriv V4 θ)
    * V4 θ * (Real.sin (2 * θ)) ^ (-q1)) with hS4def
  have hir0 : MeasureTheory.IntegrableOn S0 Work.Spaces.Iθ := by
    rw [hS0def]; exact hint0
  have hir1 : MeasureTheory.IntegrableOn S1 Work.Spaces.Iθ := by
    rw [hS1def]; exact hint1
  have hir2 : MeasureTheory.IntegrableOn S2 Work.Spaces.Iθ := by
    rw [hS2def]; exact hint2
  have hir3 : MeasureTheory.IntegrableOn S3 Work.Spaces.Iθ := by
    rw [hS3def]; exact hint3
  have hir4 : MeasureTheory.IntegrableOn S4 Work.Spaces.Iθ := by
    rw [hS4def]; exact hint4
  -- the split of the integral of `χ ζ · T1Hard`
  have hsplit : (∫ θ in Work.Spaces.Iθ, χ ζ θ * Work.FTS.H2.T1Hard α f g z θ)
      = (Work.Spaces.w z) ^ 2 * ((∫ θ in Work.Spaces.Iθ, S0 θ)
          + (∫ θ in Work.Spaces.Iθ, S1 θ) + (∫ θ in Work.Spaces.Iθ, S2 θ)
          + (∫ θ in Work.Spaces.Iθ, S3 θ) + (∫ θ in Work.Spaces.Iθ, S4 θ)) := by
    have hfun1 : (fun θ => χ ζ θ * Work.FTS.H2.T1Hard α f g z θ)
        = fun θ => (Work.Spaces.w z) ^ 2 * (S0 θ + S1 θ + S2 θ + S3 θ + S4 θ) := by
      funext θ
      rw [hpoint θ]
      simp only [hS0def, hS1def, hS2def, hS3def, hS4def]
      ring
    rw [hfun1, MeasureTheory.integral_const_mul]
    congr 1
    exact (five_integrals_add hir0 hir1 hir2 hir3 hir4).symm
  -- the five slot integrals and their bounds
  set J0 : ℝ := ∫ θ in Work.Spaces.Iθ, S0 θ with hJ0
  set J1 : ℝ := ∫ θ in Work.Spaces.Iθ, S1 θ with hJ1
  set J2 : ℝ := ∫ θ in Work.Spaces.Iθ, S2 θ with hJ2
  set J3 : ℝ := ∫ θ in Work.Spaces.Iθ, S3 θ with hJ3
  set J4 : ℝ := ∫ θ in Work.Spaces.Iθ, S4 θ with hJ4
  have hJ0' : |J0| ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, (V0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-q0))
      + (Kf * B / 2) * ((∫ θ in Set.Ioc 0 (2 * ζ), (V0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q0))
        + ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q0)) := by
    rw [hJ0, hS0def]; exact hb0
  have hJ1' : |J1| ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, (V1 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-q1))
      + (Kf * B / 2) * ((∫ θ in Set.Ioc 0 (2 * ζ), (V1 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
        + ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V1 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1)) := by
    rw [hJ1, hS1def]; exact hb1
  have hJ2' : |J2| ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, (V2 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-q1))
      + (Kf * B / 2) * ((∫ θ in Set.Ioc 0 (2 * ζ), (V2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
        + ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1)) := by
    rw [hJ2, hS2def]; exact hb2
  have hJ3' : |J3| ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, (V3 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-q1))
      + (Kf * B / 2) * ((∫ θ in Set.Ioc 0 (2 * ζ), (V3 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
        + ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V3 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1)) := by
    rw [hJ3, hS3def]; exact hb3
  have hJ4' : |J4| ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, (V4 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-q1))
      + (Kf * B / 2) * ((∫ θ in Set.Ioc 0 (2 * ζ), (V4 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
        + ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V4 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1)) := by
    rw [hJ4, hS4def]; exact hb4
  rw [hsplit, abs_mul, abs_of_nonneg hw2]
  rw [hJ0, hJ1, hJ2, hJ3, hJ4] at *
  -- the five slot energies
  have hAint0 : MeasureTheory.IntegrableOn (fun θ => (V0 θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-q0)) Work.Spaces.Iθ := by
    simpa only [hV0def, hq0def] using hS0
  have hAint1 : MeasureTheory.IntegrableOn (fun θ => (V1 θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-q1)) Work.Spaces.Iθ := by
    simpa only [hV1def, hq1def] using hSmix 3 1 (by norm_num) (by norm_num)
  have hAint2 : MeasureTheory.IntegrableOn (fun θ => (V2 θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-q1)) Work.Spaces.Iθ := by
    simpa only [hV2def, hq1def] using hSmix 2 2 (by norm_num) (by norm_num)
  have hAint3 : MeasureTheory.IntegrableOn (fun θ => (V3 θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-q1)) Work.Spaces.Iθ := by
    simpa only [hV3def, hq1def] using hSmix 1 3 (by norm_num) (by norm_num)
  have hAint4 : MeasureTheory.IntegrableOn (fun θ => (V4 θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-q1)) Work.Spaces.Iθ := by
    simpa only [hV4def, hq1def] using hSmix 0 4 (by norm_num) (by norm_num)
  -- the definitional identity for `badSlot`
  have hbad_def : ∀ θ : ℝ, badSlot α g z θ = (V0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q0)
      + ((V1 θ) ^ 2 + (V2 θ) ^ 2 + (V3 θ) ^ 2 + (V4 θ) ^ 2)
        * (Real.sin (2 * θ)) ^ (-q1) := by
    intro θ
    simp only [badSlot, hV0def, hV1def, hV2def, hV3def, hV4def, hq0def, hq1def]
  -- the sum of the five full energies is `∫_θ badSlot`
  have hAsum : (∫ θ in Work.Spaces.Iθ, (V0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q0))
        + (∫ θ in Work.Spaces.Iθ, (V1 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
        + (∫ θ in Work.Spaces.Iθ, (V2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
        + (∫ θ in Work.Spaces.Iθ, (V3 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
        + (∫ θ in Work.Spaces.Iθ, (V4 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
      = ∫ θ in Work.Spaces.Iθ, badSlot α g z θ := by
    rw [five_integrals_add hAint0 hAint1 hAint2 hAint3 hAint4]
    congr 1
    funext θ
    rw [hbad_def θ]
    ring
  -- the sums of the shrinking energies
  have hSint0a : MeasureTheory.IntegrableOn (fun θ => (V0 θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-q0)) (Set.Ioc 0 (2 * ζ)) :=
    MeasureTheory.IntegrableOn.mono_set hAint0
      (fun θ hθ => ⟨le_of_lt hθ.1, le_trans hθ.2 hζ2'⟩)
  have hSint1a : MeasureTheory.IntegrableOn (fun θ => (V1 θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-q1)) (Set.Ioc 0 (2 * ζ)) :=
    MeasureTheory.IntegrableOn.mono_set hAint1
      (fun θ hθ => ⟨le_of_lt hθ.1, le_trans hθ.2 hζ2'⟩)
  have hSint2a : MeasureTheory.IntegrableOn (fun θ => (V2 θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-q1)) (Set.Ioc 0 (2 * ζ)) :=
    MeasureTheory.IntegrableOn.mono_set hAint2
      (fun θ hθ => ⟨le_of_lt hθ.1, le_trans hθ.2 hζ2'⟩)
  have hSint3a : MeasureTheory.IntegrableOn (fun θ => (V3 θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-q1)) (Set.Ioc 0 (2 * ζ)) :=
    MeasureTheory.IntegrableOn.mono_set hAint3
      (fun θ hθ => ⟨le_of_lt hθ.1, le_trans hθ.2 hζ2'⟩)
  have hSint4a : MeasureTheory.IntegrableOn (fun θ => (V4 θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-q1)) (Set.Ioc 0 (2 * ζ)) :=
    MeasureTheory.IntegrableOn.mono_set hAint4
      (fun θ hθ => ⟨le_of_lt hθ.1, le_trans hθ.2 hζ2'⟩)
  have hSint0b : MeasureTheory.IntegrableOn (fun θ => (V0 θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-q0)) (Set.Ioc (π / 2 - 2 * ζ) (π / 2)) :=
    MeasureTheory.IntegrableOn.mono_set hAint0
      (fun θ hθ => ⟨by linarith [hθ.1, hζ, Real.pi_pos], hθ.2⟩)
  have hSint1b : MeasureTheory.IntegrableOn (fun θ => (V1 θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-q1)) (Set.Ioc (π / 2 - 2 * ζ) (π / 2)) :=
    MeasureTheory.IntegrableOn.mono_set hAint1
      (fun θ hθ => ⟨by linarith [hθ.1, hζ, Real.pi_pos], hθ.2⟩)
  have hSint2b : MeasureTheory.IntegrableOn (fun θ => (V2 θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-q1)) (Set.Ioc (π / 2 - 2 * ζ) (π / 2)) :=
    MeasureTheory.IntegrableOn.mono_set hAint2
      (fun θ hθ => ⟨by linarith [hθ.1, hζ, Real.pi_pos], hθ.2⟩)
  have hSint3b : MeasureTheory.IntegrableOn (fun θ => (V3 θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-q1)) (Set.Ioc (π / 2 - 2 * ζ) (π / 2)) :=
    MeasureTheory.IntegrableOn.mono_set hAint3
      (fun θ hθ => ⟨by linarith [hθ.1, hζ, Real.pi_pos], hθ.2⟩)
  have hSint4b : MeasureTheory.IntegrableOn (fun θ => (V4 θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-q1)) (Set.Ioc (π / 2 - 2 * ζ) (π / 2)) :=
    MeasureTheory.IntegrableOn.mono_set hAint4
      (fun θ hθ => ⟨by linarith [hθ.1, hζ, Real.pi_pos], hθ.2⟩)
  have hSsum : ((∫ θ in Set.Ioc 0 (2 * ζ), (V0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q0))
        + (∫ θ in Set.Ioc 0 (2 * ζ), (V1 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
        + (∫ θ in Set.Ioc 0 (2 * ζ), (V2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
        + (∫ θ in Set.Ioc 0 (2 * ζ), (V3 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
        + (∫ θ in Set.Ioc 0 (2 * ζ), (V4 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1)))
      + ((∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q0))
        + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V1 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
        + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
        + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V3 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
        + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V4 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1)))
      = (∫ θ in Set.Ioc 0 (2 * ζ), badSlot α g z θ)
        + ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), badSlot α g z θ := by
    have h1 : (∫ θ in Set.Ioc 0 (2 * ζ), (V0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q0))
          + (∫ θ in Set.Ioc 0 (2 * ζ), (V1 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
          + (∫ θ in Set.Ioc 0 (2 * ζ), (V2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
          + (∫ θ in Set.Ioc 0 (2 * ζ), (V3 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
          + (∫ θ in Set.Ioc 0 (2 * ζ), (V4 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
        = ∫ θ in Set.Ioc 0 (2 * ζ), badSlot α g z θ := by
      rw [five_integrals_add hSint0a hSint1a hSint2a hSint3a hSint4a]
      congr 1
      funext θ
      rw [hbad_def θ]
      ring
    have h2 : (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q0))
          + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V1 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
          + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
          + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V3 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
          + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V4 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
        = ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), badSlot α g z θ := by
      rw [five_integrals_add hSint0b hSint1b hSint2b hSint3b hSint4b]
      congr 1
      funext θ
      rw [hbad_def θ]
      ring
    rw [h1, h2]
  -- assemble
  have htri : |J0 + J1 + J2 + J3 + J4|
      ≤ |J0| + |J1| + |J2| + |J3| + |J4| := by
    have e1 := abs_add_le (J0 + J1 + J2 + J3) J4
    have e2 := abs_add_le (J0 + J1 + J2) J3
    have e3 := abs_add_le (J0 + J1) J2
    have e4 := abs_add_le J0 J1
    linarith
  have hassembled : |J0 + J1 + J2 + J3 + J4|
      ≤ (3 / 2) * Kf * ((∫ θ in Work.Spaces.Iθ, (V0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q0))
          + (∫ θ in Work.Spaces.Iθ, (V1 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
          + (∫ θ in Work.Spaces.Iθ, (V2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
          + (∫ θ in Work.Spaces.Iθ, (V3 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
          + (∫ θ in Work.Spaces.Iθ, (V4 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1)))
        + (Kf * B / 2) * (((∫ θ in Set.Ioc 0 (2 * ζ), (V0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q0))
            + (∫ θ in Set.Ioc 0 (2 * ζ), (V1 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
            + (∫ θ in Set.Ioc 0 (2 * ζ), (V2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
            + (∫ θ in Set.Ioc 0 (2 * ζ), (V3 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
            + (∫ θ in Set.Ioc 0 (2 * ζ), (V4 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1)))
          + ((∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q0))
            + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V1 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
            + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
            + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V3 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
            + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2),
                (V4 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1)))) := by
    refine le_trans htri ?_
    linarith [hJ0', hJ1', hJ2', hJ3', hJ4']
  calc (Work.Spaces.w z) ^ 2 * |J0 + J1 + J2 + J3 + J4|
      ≤ (Work.Spaces.w z) ^ 2 * ((3 / 2) * Kf
          * ((∫ θ in Work.Spaces.Iθ, (V0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q0))
            + (∫ θ in Work.Spaces.Iθ, (V1 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
            + (∫ θ in Work.Spaces.Iθ, (V2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
            + (∫ θ in Work.Spaces.Iθ, (V3 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
            + (∫ θ in Work.Spaces.Iθ, (V4 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1)))
          + (Kf * B / 2) * (((∫ θ in Set.Ioc 0 (2 * ζ), (V0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q0))
              + (∫ θ in Set.Ioc 0 (2 * ζ), (V1 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
              + (∫ θ in Set.Ioc 0 (2 * ζ), (V2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
              + (∫ θ in Set.Ioc 0 (2 * ζ), (V3 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
              + (∫ θ in Set.Ioc 0 (2 * ζ), (V4 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1)))
            + ((∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q0))
              + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V1 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
              + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
              + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V3 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
              + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2),
                  (V4 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))))) :=
        mul_le_mul_of_nonneg_left hassembled hw2
    _ = (3 / 2) * Kf * ((Work.Spaces.w z) ^ 2
          * ((∫ θ in Work.Spaces.Iθ, (V0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q0))
            + (∫ θ in Work.Spaces.Iθ, (V1 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
            + (∫ θ in Work.Spaces.Iθ, (V2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
            + (∫ θ in Work.Spaces.Iθ, (V3 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
            + (∫ θ in Work.Spaces.Iθ, (V4 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))))
        + (Kf * B / 2) * ((Work.Spaces.w z) ^ 2
          * (((∫ θ in Set.Ioc 0 (2 * ζ), (V0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q0))
              + (∫ θ in Set.Ioc 0 (2 * ζ), (V1 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
              + (∫ θ in Set.Ioc 0 (2 * ζ), (V2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
              + (∫ θ in Set.Ioc 0 (2 * ζ), (V3 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
              + (∫ θ in Set.Ioc 0 (2 * ζ), (V4 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1)))
            + ((∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q0))
              + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V1 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
              + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
              + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), (V3 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))
              + (∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2),
                  (V4 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q1))))) := by ring
    _ = (3 / 2) * Kf * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, badSlot α g z θ))
        + (Kf * B / 2) * (Work.Spaces.w z) ^ 2
          * ((∫ θ in Set.Ioc 0 (2 * ζ), badSlot α g z θ)
            + ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), badSlot α g z θ) := by
        rw [hAsum, hSsum]
        ring
    _ ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + (Kf * B / 2) * (Work.Spaces.w z) ^ 2
          * ((∫ θ in Set.Ioc 0 (2 * ζ), badSlot α g z θ)
            + ∫ θ in Set.Ioc (π / 2 - 2 * ζ) (π / 2), badSlot α g z θ) := by
        refine add_le_add ?_ le_rfl
        exact mul_le_mul_of_nonneg_left hSbd (by nlinarith [hKf0])

/-- **The slice bound.**  For `z ∈ Iz` the angular integral of `T1Hard α f g z ·` is bounded by
`(3/2)·Kf·∫_θ HkIntegrand α 4 g z θ`.  The proof cuts `f` off near the two endpoints by the
cut-off `χ ζ` of the package `Cutoff`, applies the angular integration by parts
(`IbpCutoff`) to the five slots, and passes to the limit `ζ → 0⁺` with the dominated
convergence theorem (`SliceLimit`), the boundary contributions being controlled by
`ShrinkInt`. -/
lemma slice_bound (α Kf : ℝ) (f g : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hKf0 : 0 ≤ Kf)
    (hsmf : Work.FTS.LocData.SmoothQuad f) (hsmg : Work.FTS.LocData.SmoothQuad g)
    (hmg : Work.Spaces.HkMem α 4 g)
    (hKf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Kf)
    (hKfd : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.Dth f z θ| ≤ Kf) :
    ∀ z ∈ Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Hard α f g z θ|
      ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    have hzero : (fun θ : ℝ => Work.FTS.H2.T1Hard α f g 0 θ) = fun _ => (0 : ℝ) := by
      funext θ
      simp only [Work.FTS.H2.T1Hard, Work.Spaces.w]
      ring
    rw [hzero, MeasureTheory.integral_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hKf0)
      (MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ)
  · obtain ⟨chi, B, hB, hsm, hnn, hle, hone, hz0l, hz0r, hd0l, hd0r, hbd, hten⟩ := Cutoff
    obtain ⟨hS0int, hSmixint, _⟩ := SlotBoundQ α g hsmg hmg hzpos
    -- integrability of `badSlot`
    have hbad_int : MeasureTheory.IntegrableOn (fun θ => badSlot α g z θ)
        Work.Spaces.Iθ := by
      have h' : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 4 g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
          + (Work.Spaces.mixed 3 1 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          + (Work.Spaces.mixed 2 2 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          + (Work.Spaces.mixed 1 3 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          + (Work.Spaces.mixed 0 4 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          Work.Spaces.Iθ :=
        (((hS0int.add (hSmixint 3 1 (by norm_num) (by norm_num))).add
          (hSmixint 2 2 (by norm_num) (by norm_num))).add
          (hSmixint 1 3 (by norm_num) (by norm_num))).add
          (hSmixint 0 4 (by norm_num) (by norm_num))
      refine h'.congr_fun (fun θ _ => ?_) measurableSet_Icc
      simp only [badSlot]
      ring_nf
    -- the limit of the cut-off parameters
    have hbase : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 4)) Filter.atTop
        (𝓝 0) := by
      have hshift : Filter.Tendsto (fun n : ℕ => n + 3) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_mono (fun n => Nat.le_add_right n 3) Filter.tendsto_id
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hshift
      refine h.congr (fun n => ?_)
      simp only [Function.comp_apply]
      push_cast
      ring_nf
    have hlimeq : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (2 * ((n : ℝ) + 4)))
        Filter.atTop (𝓝 0) := by
      have h2 : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (1 / ((n : ℝ) + 4)))
          Filter.atTop (𝓝 0) := by
        simpa using hbase.const_mul (1 / 2 : ℝ)
      refine h2.congr' ?_
      filter_upwards with n
      have hx : (4 + (n : ℝ)) ≠ 0 := by positivity
      field_simp
    have hlimpos : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (2 * ((n : ℝ) + 4)))
        Filter.atTop (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hlimeq, ?_⟩
      filter_upwards with n
      exact Set.mem_Ioi.mpr (by positivity)
    -- the convergence of the cut-off to `1`
    have hchi_lim : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Filter.Tendsto (fun n : ℕ => chi (1 / (2 * ((n : ℝ) + 4))) θ) Filter.atTop
          (𝓝 1) := by
      filter_upwards [ae_Iθ_mem_Ioo] with θ hθ
      exact (hten θ hθ.1 hθ.2).comp hlimpos
    have hchi_meas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => chi (1 / (2 * ((n : ℝ) + 4))) θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      fun n => (hsm (1 / (2 * ((n : ℝ) + 4)))).continuous.aestronglyMeasurable
    have hchi_le : ∀ (n : ℕ) (θ : ℝ), |chi (1 / (2 * ((n : ℝ) + 4))) θ| ≤ 1 := by
      intro n θ
      rw [abs_of_nonneg (hnn _ θ)]
      exact hle _ θ
    -- the pointwise bound for every cut-off parameter
    have hbd_seq : ∀ n : ℕ,
        |∫ θ in Work.Spaces.Iθ, chi (1 / (2 * ((n : ℝ) + 4))) θ
            * Work.FTS.H2.T1Hard α f g z θ|
          ≤ (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
            + (Kf * B / 2) * (Work.Spaces.w z) ^ 2
              * ((∫ θ in Set.Ioc 0 (1 / ((n : ℝ) + 4)), badSlot α g z θ)
                + ∫ θ in Set.Ioc (π / 2 - 1 / ((n : ℝ) + 4)) (π / 2),
                    badSlot α g z θ) := by
      intro n
      have hζn : 0 < 1 / (2 * ((n : ℝ) + 4)) := by positivity
      have hζn4 : 1 / (2 * ((n : ℝ) + 4)) ≤ 1 / 4 := by
        rw [div_le_iff₀ (by positivity)]
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) n]
      have h := cutoff_bound α Kf B f g chi hα hα1 hB hKf0 hsmf hsmg hmg hKf hKfd
        hsm hnn hle hone hz0l hz0r hd0l hd0r hbd hzpos hζn hζn4
      have h2ζ : 2 * (1 / (2 * ((n : ℝ) + 4))) = 1 / ((n : ℝ) + 4) := by
        have hx : ((n : ℝ) + 4) ≠ 0 := by positivity
        field_simp
      rw [h2ζ] at h
      exact h
    -- the error term tends to zero
    have herr : Filter.Tendsto (fun n : ℕ => (Kf * B / 2) * (Work.Spaces.w z) ^ 2
        * ((∫ θ in Set.Ioc 0 (1 / ((n : ℝ) + 4)), badSlot α g z θ)
          + ∫ θ in Set.Ioc (π / 2 - 1 / ((n : ℝ) + 4)) (π / 2), badSlot α g z θ))
        Filter.atTop (𝓝 0) := by
      have h := ShrinkInt hbad_int
      simpa using h.const_mul ((Kf * B / 2) * (Work.Spaces.w z) ^ 2)
    by_cases hint : MeasureTheory.IntegrableOn (fun θ => Work.FTS.H2.T1Hard α f g z θ)
        Work.Spaces.Iθ
    · exact SliceLimit (M := (3 / 2) * Kf
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
        (φ := fun θ => Work.FTS.H2.T1Hard α f g z θ)
        (chi := fun n θ => chi (1 / (2 * ((n : ℝ) + 4))) θ)
        (err := fun n => (Kf * B / 2) * (Work.Spaces.w z) ^ 2
          * ((∫ θ in Set.Ioc 0 (1 / ((n : ℝ) + 4)), badSlot α g z θ)
            + ∫ θ in Set.Ioc (π / 2 - 1 / ((n : ℝ) + 4)) (π / 2),
                badSlot α g z θ))
        herr hint hchi_meas hchi_le hchi_lim hbd_seq
    · rw [MeasureTheory.integral_undef hint, abs_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hKf0)
        (MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)

/-- The five order-five terms `T1Hard α f g` of the flat pairing of `(f D_theta g, g)`: with Kf a bound for `|f|` and `|D_theta f|` on the open quadrant, the z-integral of the absolute value of the theta-integral of `T1Hard` is at most `C*Kf*|g|^2_H4`, and the inner integral is integrable in z. Each of the five terms is `f * D_theta v * v * sin(2 theta)^{-q}` with v the corresponding order-four g-block and q = eta (the D_z^4 slot) resp. q = gamma (the four mixed slots (j,i) = (3,1),(2,2),(1,3),(0,4)), hence bounded by `C*Kf*int_theta v^2 sin(2 theta)^{-q}` by the interior angular integration-by-parts bound `Work.H2.T1Q.IbpBoundQ` (proved in this same directory; if that file is not available yet, re-derive it by cutting f off near theta = 0 and pi/2, applying the FTC to the primitive `(1/2) sin(2 theta)^{1-q} f v^2` whose endpoint values vanish by the cut-off, bounding uniformly in the cut-off parameter and passing to the limit with Fatou). Each `int_theta v^2 sin(2 theta)^{-q}` times `(w z)^2` is then a summand of `HkIntegrand alpha 4 g z .` (lemmas `slot_energy_dz`, `slot_energy_mixed` in `Submission.Work.FTS.H2.STHardBound`). At z = 0 the integrand vanishes since w 0 = 0. The file `Submission/Work/FTS/H2/T1HardBound.lean` is the `SmoothNbhd` version of this statement and can be adapted. -/
theorem HardBoundQ : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : Work.FTS.Galerkin.Fn) (Kf : ℝ),
    0 < α → α ≤ 1 → Work.FTS.LocData.SmoothQuad f → Work.FTS.LocData.SmoothQuad g →
    Work.Spaces.DecayAll 4 f → Work.Spaces.DecayAll 4 g →
    Work.Spaces.HkMem α 4 f → Work.Spaces.HkMem α 4 g →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Kf) →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.Dth f z θ| ≤ Kf) →
    0 ≤ Kf →
    MeasureTheory.IntegrableOn
        (fun z => |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Hard α f g z θ|) Work.Spaces.Iz ∧
      ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Hard α f g z θ|
        ≤ C * Kf * Work.Spaces.HkSq α 4 g := by
  refine ⟨3 / 2, by norm_num, ?_⟩
  intro α f g Kf hα hα1 hsmf hsmg hdf hdg hmf hmg hKf hKfd hKf0
  have hslice := slice_bound α Kf f g hα hα1 hKf0 hsmf hsmg hmg hKf hKfd
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Hard α f g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (T1HardAesmQ α f g hsmf hsmg).integral_prod_right'
    simpa only using h
  have hdomI : MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmg.2
  have hdom : MeasureTheory.Integrable
      (fun z => (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hdomI.const_mul _
  constructor
  · have h : MeasureTheory.Integrable
        (fun z => ‖∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Hard α f g z θ‖)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Integrable.mono' hdom haesm.norm
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => by
          simpa [Real.norm_eq_abs] using hslice z hz))
    simpa only [MeasureTheory.IntegrableOn, Real.norm_eq_abs] using h
  · have hmono := MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => abs_nonneg _)) hdom
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hslice z hz))
    calc ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Hard α f g z θ|
        ≤ ∫ z in Work.Spaces.Iz,
            (3 / 2) * Kf * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := hmono
      _ = (3 / 2) * Kf * Work.Spaces.HkSq α 4 g := by
          rw [MeasureTheory.integral_const_mul, Work.Spaces.HkSq]

end Work.H2.T1Q
