import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# An integration-by-parts identity in the radial variable `z`

The lemma `aeZWtIBP` is the weak-form integration-by-parts identity used in the
`AngAWeak` chain.  For `W` of class `C²` with compact support vanishing near `0` and
`φ, v` of class `C²` on `(0, ∞)` it states

  ∫ Wφ (-α²z² v'' - α(5+α)z v') v = α² ∫ Wφz² (v')²
      + (α(5+α)/2) ∫ (Wφz)' v² - (α²/2) ∫ (Wφz²)'' v²,

i.e. that the one-dimensional operator `L = -α²z² ∂² - α(5+α)z ∂` is formally
self-adjoint for the weight `W φ`.

The proof goes through the auxiliary function

  `T = -α²(Wφz²)v v' + (α²/2)(Wφz²)' v² - (α(5+α)/2)(Wφz)v²`,

whose derivative is the difference of the two integrands; the fundamental theorem of
calculus on `(0,∞)` (both boundary limits vanish, since everything is supported in
`[a,b]`) gives the identity.
-/

namespace Work.FTS.EllipticEst.AngAWeak

open MeasureTheory Set Filter
open scoped Topology

set_option autoImplicit false

/-- A function which is continuous on a compact interval and vanishes outside of it is
integrable on `(0, ∞)`. -/
private lemma integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off
    {f : ℝ → ℝ} {c d : ℝ} (_hcd : c ≤ d)
    (hcont : ContinuousOn f (Set.Icc c d))
    (hzero : ∀ x, x ∉ Set.Icc c d → f x = 0) :
    IntegrableOn f (Set.Ioi 0) := by
  have h1 : IntegrableOn f (Set.Icc c d) :=
    ContinuousOn.integrableOn_compact isCompact_Icc hcont
  have h2 : Integrable ((Set.Icc c d).indicator f) := h1.integrable_indicator measurableSet_Icc
  have h3 : f = (Set.Icc c d).indicator f := by
    funext x
    by_cases hx : x ∈ Set.Icc c d
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, hzero x hx]
  rw [← h3] at h2
  exact h2.integrableOn

/-- The general integration-by-parts identity.  Here `g` is `C²` on a neighbourhood of
the interval `[a,b]` (`0 < a < b`) and vanishes outside `[a,b]`; `v` is `C²` on `(0,∞)`. -/
private theorem zw_ibp_general (α a b : ℝ) (g v : ℝ → ℝ) (ha : 0 < a) (hab : a < b)
    (hg : ContDiffOn ℝ 2 g (Set.Ioi (a / 2)))
    (hg0 : ∀ z, z ∉ Set.Ioo a b → g z = 0)
    (hv : ContDiffOn ℝ 2 v (Set.Ioi 0)) :
    ∫ z in Set.Ioi 0,
        g z * (-(α ^ 2 * z ^ 2) * deriv (deriv v) z - (α * (5 + α) * z) * deriv v z) * v z
      = α ^ 2 * (∫ z in Set.Ioi 0, g z * z ^ 2 * (deriv v z) ^ 2)
        + (α * (5 + α) / 2)
            * (∫ z in Set.Ioi 0, deriv (fun z => g z * z) z * (v z) ^ 2)
        - (α ^ 2 / 2)
            * (∫ z in Set.Ioi 0, deriv (deriv (fun z => g z * z ^ 2)) z * (v z) ^ 2) := by
  -- ## Step 0: `g` vanishes below `a` and above `b`
  have hg_low : ∀ z, z < a → g z = 0 := fun z hz => hg0 z (by
    simp only [Set.mem_Ioo, not_and]
    exact fun h => absurd h (not_lt.mpr hz.le))
  have hg_high : ∀ z, b < z → g z = 0 := fun z hz => hg0 z (by
    simp only [Set.mem_Ioo, not_and]
    exact fun _ h2 => absurd h2 (not_lt.mpr hz.le))
  -- ## Step 1: off-support vanishing of `z ↦ g z * z²`, `z ↦ g z * z` and of their
  -- derivatives
  have hP_ev : ∀ z, z < a ∨ b < z → (fun w => g w * w ^ 2) =ᶠ[𝓝 z] 0 := by
    intro z hz
    rcases hz with hz | hz
    · filter_upwards [isOpen_Iio.mem_nhds hz] with w hw
      show g w * w ^ 2 = 0
      rw [hg_low w hw]; ring
    · filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      show g w * w ^ 2 = 0
      rw [hg_high w hw]; ring
  have hQ_ev : ∀ z, z < a ∨ b < z → (fun w => g w * w) =ᶠ[𝓝 z] 0 := by
    intro z hz
    rcases hz with hz | hz
    · filter_upwards [isOpen_Iio.mem_nhds hz] with w hw
      show g w * w = 0
      rw [hg_low w hw]; ring
    · filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      show g w * w = 0
      rw [hg_high w hw]; ring
  have hdP : ∀ z, z < a ∨ b < z → deriv (fun w => g w * w ^ 2) z = 0 := fun z hz => by
    simpa using (hP_ev z hz).deriv_eq
  have hdQ : ∀ z, z < a ∨ b < z → deriv (fun w => g w * w) z = 0 := fun z hz => by
    simpa using (hQ_ev z hz).deriv_eq
  have hddP : ∀ z, z < a ∨ b < z → deriv (deriv (fun w => g w * w ^ 2)) z = 0 := by
    intro z hz
    have h : deriv (fun w => g w * w ^ 2) =ᶠ[𝓝 z] 0 := by
      rcases hz with hz | hz
      · filter_upwards [isOpen_Iio.mem_nhds hz] with w hw
        exact hdP w (Or.inl hw)
      · filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact hdP w (Or.inr hw)
    simpa using h.deriv_eq
  -- ## Step 2: smoothness of the auxiliary functions near `[a,b]`
  have hPc : ContDiffOn ℝ 2 (fun z => g z * z ^ 2) (Set.Ioi (a / 2)) := by
    have hz : ContDiffOn ℝ 2 (fun z : ℝ => z ^ 2) (Set.Ioi (a / 2)) := by
      show ContDiffOn ℝ 2 (id ^ 2) (Set.Ioi (a / 2))
      exact contDiffOn_id.pow 2
    exact hg.mul hz
  have hQc : ContDiffOn ℝ 2 (fun z => g z * z) (Set.Ioi (a / 2)) := by
    have hz : ContDiffOn ℝ 2 (fun z : ℝ => z) (Set.Ioi (a / 2)) := by
      show ContDiffOn ℝ 2 id (Set.Ioi (a / 2))
      exact contDiffOn_id
    exact hg.mul hz
  have hPc1 : ContDiffOn ℝ 1 (deriv (fun z => g z * z ^ 2)) (Set.Ioi (a / 2)) :=
    ContDiffOn.deriv_of_isOpen hPc isOpen_Ioi (by norm_num)
  have hQc1 : ContDiffOn ℝ 1 (deriv (fun z => g z * z)) (Set.Ioi (a / 2)) :=
    ContDiffOn.deriv_of_isOpen hQc isOpen_Ioi (by norm_num)
  have hPc0 : ContDiffOn ℝ 0 (deriv (deriv (fun z => g z * z ^ 2))) (Set.Ioi (a / 2)) :=
    ContDiffOn.deriv_of_isOpen hPc1 isOpen_Ioi (by norm_num)
  have hv1 : ContDiffOn ℝ 1 (deriv v) (Set.Ioi 0) :=
    ContDiffOn.deriv_of_isOpen hv isOpen_Ioi (by norm_num)
  have hv0 : ContDiffOn ℝ 0 (deriv (deriv v)) (Set.Ioi 0) :=
    ContDiffOn.deriv_of_isOpen hv1 isOpen_Ioi (by norm_num)
  -- ## Step 3: continuity of the integrands on `[a,b]`
  have hsab : Set.Icc a b ⊆ Set.Ioi (a / 2) := by
    intro x hx
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Ioi]
    linarith [hx.1]
  have hs0 : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    simp only [Set.mem_Icc] at hx
    simp only [Set.mem_Ioi]
    linarith [hx.1]
  have hgc : ContinuousOn g (Set.Icc a b) := hg.continuousOn.mono hsab
  have hvc : ContinuousOn v (Set.Icc a b) := hv.continuousOn.mono hs0
  have hv1c : ContinuousOn (deriv v) (Set.Icc a b) := hv1.continuousOn.mono hs0
  have hv0c : ContinuousOn (deriv (deriv v)) (Set.Icc a b) := hv0.continuousOn.mono hs0
  have hPcc : ContinuousOn (fun z => g z * z ^ 2) (Set.Icc a b) := hPc.continuousOn.mono hsab
  have hPc1c : ContinuousOn (deriv (fun z => g z * z ^ 2)) (Set.Icc a b) :=
    hPc1.continuousOn.mono hsab
  have hQc1c : ContinuousOn (deriv (fun z => g z * z)) (Set.Icc a b) :=
    hQc1.continuousOn.mono hsab
  have hPc0c : ContinuousOn (deriv (deriv (fun z => g z * z ^ 2))) (Set.Icc a b) :=
    hPc0.continuousOn.mono hsab
  have hzsq : ContinuousOn (fun z : ℝ => z ^ 2) (Set.Icc a b) := by
    show ContinuousOn (id ^ 2) (Set.Icc a b)
    exact (continuousOn_id (s := Set.Icc a b)).pow 2
  have hvid : ContinuousOn (fun z : ℝ => z) (Set.Icc a b) := continuousOn_id
  have hv2c : ContinuousOn (fun z => (v z) ^ 2) (Set.Icc a b) := by
    show ContinuousOn (v ^ 2) (Set.Icc a b)
    exact hvc.pow 2
  have hv1sq : ContinuousOn (fun z => (deriv v z) ^ 2) (Set.Icc a b) := by
    show ContinuousOn ((deriv v) ^ 2) (Set.Icc a b)
    exact hv1c.pow 2
  have hf0c : ContinuousOn (fun z => g z * z ^ 2 * (deriv v z) ^ 2) (Set.Icc a b) :=
    hPcc.mul hv1sq
  have hf1c : ContinuousOn (fun z => deriv (fun z => g z * z) z * (v z) ^ 2) (Set.Icc a b) :=
    hQc1c.mul hv2c
  have hf2c : ContinuousOn (fun z => deriv (deriv (fun z => g z * z ^ 2)) z * (v z) ^ 2)
      (Set.Icc a b) := hPc0c.mul hv2c
  have hAcont : ContinuousOn (fun z => -(α ^ 2 * z ^ 2) * deriv (deriv v) z) (Set.Icc a b) :=
    (hzsq.const_mul (α ^ 2)).neg.mul hv0c
  have hBcont : ContinuousOn (fun z => (α * (5 + α) * z) * deriv v z) (Set.Icc a b) :=
    (hvid.const_mul (α * (5 + α))).mul hv1c
  have hABcont : ContinuousOn
      (fun z => -(α ^ 2 * z ^ 2) * deriv (deriv v) z - (α * (5 + α) * z) * deriv v z)
      (Set.Icc a b) := hAcont.sub hBcont
  have hLc : ContinuousOn
      (fun z => g z * (-(α ^ 2 * z ^ 2) * deriv (deriv v) z - (α * (5 + α) * z) * deriv v z)
        * v z) (Set.Icc a b) :=
    (hgc.mul hABcont).mul hvc
  have hRc : ContinuousOn
      (fun z => α ^ 2 * (g z * z ^ 2 * (deriv v z) ^ 2)
        + (α * (5 + α) / 2) * (deriv (fun z => g z * z) z * (v z) ^ 2)
        - (α ^ 2 / 2) * (deriv (deriv (fun z => g z * z ^ 2)) z * (v z) ^ 2))
      (Set.Icc a b) :=
    ((hf0c.const_mul (α ^ 2)).add (hf1c.const_mul (α * (5 + α) / 2))).sub
      (hf2c.const_mul (α ^ 2 / 2))
  -- ## Step 4: off-support vanishing of the integrands
  have hmem : ∀ x, x ∉ Set.Icc a b → x < a ∨ b < x := by
    intro x hx
    by_cases h1 : x < a
    · exact Or.inl h1
    · refine Or.inr ?_
      by_contra h2
      exact hx ⟨le_of_not_gt h1, le_of_not_gt h2⟩
  have hzeroL : ∀ x, x ∉ Set.Icc a b →
      g x * (-(α ^ 2 * x ^ 2) * deriv (deriv v) x - (α * (5 + α) * x) * deriv v x) * v x
        = 0 := by
    intro x hx
    rcases hmem x hx with h | h
    · rw [hg_low x h]; ring
    · rw [hg_high x h]; ring
  have hzero0 : ∀ x, x ∉ Set.Icc a b → g x * x ^ 2 * (deriv v x) ^ 2 = 0 := by
    intro x hx
    rcases hmem x hx with h | h
    · rw [hg_low x h]; ring
    · rw [hg_high x h]; ring
  have hzero1 : ∀ x, x ∉ Set.Icc a b → deriv (fun z => g z * z) x * (v x) ^ 2 = 0 := by
    intro x hx
    rcases hmem x hx with h | h
    · rw [hdQ x (Or.inl h)]; ring
    · rw [hdQ x (Or.inr h)]; ring
  have hzero2 : ∀ x, x ∉ Set.Icc a b →
      deriv (deriv (fun z => g z * z ^ 2)) x * (v x) ^ 2 = 0 := by
    intro x hx
    rcases hmem x hx with h | h
    · rw [hddP x (Or.inl h)]; ring
    · rw [hddP x (Or.inr h)]; ring
  have hzeroR : ∀ x, x ∉ Set.Icc a b →
      α ^ 2 * (g x * x ^ 2 * (deriv v x) ^ 2)
        + (α * (5 + α) / 2) * (deriv (fun z => g z * z) x * (v x) ^ 2)
        - (α ^ 2 / 2) * (deriv (deriv (fun z => g z * z ^ 2)) x * (v x) ^ 2) = 0 := by
    intro x hx
    rw [hzero0 x hx, hzero1 x hx, hzero2 x hx]
    ring
  -- ## Step 5: integrability of the integrands
  have hintL : IntegrableOn
      (fun z => g z * (-(α ^ 2 * z ^ 2) * deriv (deriv v) z - (α * (5 + α) * z) * deriv v z)
        * v z) (Set.Ioi 0) :=
    integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off hab.le hLc hzeroL
  have hint0 : IntegrableOn (fun z => g z * z ^ 2 * (deriv v z) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off hab.le hf0c hzero0
  have hint1 : IntegrableOn (fun z => deriv (fun z => g z * z) z * (v z) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off hab.le hf1c hzero1
  have hint2 : IntegrableOn
      (fun z => deriv (deriv (fun z => g z * z ^ 2)) z * (v z) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off hab.le hf2c hzero2
  have hintR : IntegrableOn
      (fun z => α ^ 2 * (g z * z ^ 2 * (deriv v z) ^ 2)
        + (α * (5 + α) / 2) * (deriv (fun z => g z * z) z * (v z) ^ 2)
        - (α ^ 2 / 2) * (deriv (deriv (fun z => g z * z ^ 2)) z * (v z) ^ 2))
      (Set.Ioi 0) :=
    (IntegrableOn.add (Integrable.const_mul hint0 (α ^ 2))
      (Integrable.const_mul hint1 (α * (5 + α) / 2))).sub
      (Integrable.const_mul hint2 (α ^ 2 / 2))
  have hintLR : IntegrableOn
      (fun z => g z * (-(α ^ 2 * z ^ 2) * deriv (deriv v) z - (α * (5 + α) * z) * deriv v z)
          * v z
        - (α ^ 2 * (g z * z ^ 2 * (deriv v z) ^ 2)
          + (α * (5 + α) / 2) * (deriv (fun z => g z * z) z * (v z) ^ 2)
          - (α ^ 2 / 2) * (deriv (deriv (fun z => g z * z ^ 2)) z * (v z) ^ 2)))
      (Set.Ioi 0) := hintL.sub hintR
  -- ## Step 6: the auxiliary function and the derivative identity
  have hTev : ∀ z, z < a → (fun z => -α ^ 2 * ((g z * z ^ 2) * v z * deriv v z)
      + (α ^ 2 / 2) * (deriv (fun z => g z * z ^ 2) z * (v z) ^ 2)
      - (α * (5 + α) / 2) * ((g z * z) * (v z) ^ 2)) =ᶠ[𝓝 z] 0 := by
    intro z hz
    filter_upwards [isOpen_Iio.mem_nhds hz] with w hw
    show -α ^ 2 * ((g w * w ^ 2) * v w * deriv v w)
        + (α ^ 2 / 2) * (deriv (fun z => g z * z ^ 2) w * (v w) ^ 2)
        - (α * (5 + α) / 2) * ((g w * w) * (v w) ^ 2) = 0
    rw [hg_low w hw, hdP w (Or.inl hw)]
    ring
  have hTtop : (fun z => -α ^ 2 * ((g z * z ^ 2) * v z * deriv v z)
      + (α ^ 2 / 2) * (deriv (fun z => g z * z ^ 2) z * (v z) ^ 2)
      - (α * (5 + α) / 2) * ((g z * z) * (v z) ^ 2)) =ᶠ[Filter.atTop] 0 := by
    filter_upwards [eventually_gt_atTop b] with w hw
    show -α ^ 2 * ((g w * w ^ 2) * v w * deriv v w)
        + (α ^ 2 / 2) * (deriv (fun z => g z * z ^ 2) w * (v w) ^ 2)
        - (α * (5 + α) / 2) * ((g w * w) * (v w) ^ 2) = 0
    rw [hg_high w hw, hdP w (Or.inr hw)]
    ring
  have hT0 : (fun z => -α ^ 2 * ((g z * z ^ 2) * v z * deriv v z)
      + (α ^ 2 / 2) * (deriv (fun z => g z * z ^ 2) z * (v z) ^ 2)
      - (α * (5 + α) / 2) * ((g z * z) * (v z) ^ 2)) 0 = 0 := by
    show -α ^ 2 * ((g 0 * 0 ^ 2) * v 0 * deriv v 0)
        + (α ^ 2 / 2) * (deriv (fun z => g z * z ^ 2) 0 * (v 0) ^ 2)
        - (α * (5 + α) / 2) * ((g 0 * 0) * (v 0) ^ 2) = 0
    rw [hdP 0 (Or.inl ha)]
    ring
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z => -α ^ 2 * ((g z * z ^ 2) * v z * deriv v z)
        + (α ^ 2 / 2) * (deriv (fun z => g z * z ^ 2) z * (v z) ^ 2)
        - (α * (5 + α) / 2) * ((g z * z) * (v z) ^ 2))
      (g x * (-(α ^ 2 * x ^ 2) * deriv (deriv v) x - (α * (5 + α) * x) * deriv v x) * v x
        - (α ^ 2 * (g x * x ^ 2 * (deriv v x) ^ 2)
          + (α * (5 + α) / 2) * (deriv (fun z => g z * z) x * (v x) ^ 2)
          - (α ^ 2 / 2) * (deriv (deriv (fun z => g z * z ^ 2)) x * (v x) ^ 2))) x := by
    intro x hx
    rcases lt_or_ge x a with hxa | hxa
    · -- below `a` both sides vanish
      have hval : g x * (-(α ^ 2 * x ^ 2) * deriv (deriv v) x - (α * (5 + α) * x) * deriv v x)
            * v x
          - (α ^ 2 * (g x * x ^ 2 * (deriv v x) ^ 2)
            + (α * (5 + α) / 2) * (deriv (fun z => g z * z) x * (v x) ^ 2)
            - (α ^ 2 / 2) * (deriv (deriv (fun z => g z * z ^ 2)) x * (v x) ^ 2)) = 0 := by
        rw [hg_low x hxa, hdQ x (Or.inl hxa), hddP x (Or.inl hxa)]
        ring
      rw [hval]
      exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq (hTev x hxa)
    · -- above `a`: assemble the product rule
      have hx2 : x ∈ Set.Ioi (a / 2) := by
        simp only [Set.mem_Ioi]; linarith
      have hx0 : x ∈ Set.Ioi (0 : ℝ) := by
        simp only [Set.mem_Ioi]; linarith
      have hPx : HasDerivAt (fun z => g z * z ^ 2) (deriv (fun z => g z * z ^ 2) x) x :=
        ((hPc.differentiableOn (by norm_num)).differentiableAt
          (isOpen_Ioi.mem_nhds hx2)).hasDerivAt
      have hQx : HasDerivAt (fun z => g z * z) (deriv (fun z => g z * z) x) x :=
        ((hQc.differentiableOn (by norm_num)).differentiableAt
          (isOpen_Ioi.mem_nhds hx2)).hasDerivAt
      have hPx1 : HasDerivAt (deriv (fun z => g z * z ^ 2))
          (deriv (deriv (fun z => g z * z ^ 2)) x) x :=
        ((hPc1.differentiableOn (by norm_num)).differentiableAt
          (isOpen_Ioi.mem_nhds hx2)).hasDerivAt
      have hvx : HasDerivAt v (deriv v x) x :=
        ((hv.differentiableOn (by norm_num)).differentiableAt
          (isOpen_Ioi.mem_nhds hx0)).hasDerivAt
      have hvx1 : HasDerivAt (deriv v) (deriv (deriv v) x) x :=
        ((hv1.differentiableOn (by norm_num)).differentiableAt
          (isOpen_Ioi.mem_nhds hx0)).hasDerivAt
      have hT1 := ((hPx.mul hvx).mul hvx1).const_mul (-α ^ 2)
      have hT2 := (hPx1.mul (hvx.pow 2)).const_mul (α ^ 2 / 2)
      have hT3 := (hQx.mul (hvx.pow 2)).const_mul (α * (5 + α) / 2)
      refine ((hT1.add hT2).sub hT3).congr_deriv ?_
      simp only [Pi.mul_apply, Pi.pow_apply]
      ring
  -- ## Step 7: the fundamental theorem of calculus on `(0,∞)`
  have hTcont : ContinuousWithinAt (fun z => -α ^ 2 * ((g z * z ^ 2) * v z * deriv v z)
      + (α ^ 2 / 2) * (deriv (fun z => g z * z ^ 2) z * (v z) ^ 2)
      - (α * (5 + α) / 2) * ((g z * z) * (v z) ^ 2)) (Set.Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    show Tendsto (fun z => -α ^ 2 * ((g z * z ^ 2) * v z * deriv v z)
      + (α ^ 2 / 2) * (deriv (fun z => g z * z ^ 2) z * (v z) ^ 2)
      - (α * (5 + α) / 2) * ((g z * z) * (v z) ^ 2)) (𝓝 0)
      (𝓝 ((fun z => -α ^ 2 * ((g z * z ^ 2) * v z * deriv v z)
      + (α ^ 2 / 2) * (deriv (fun z => g z * z ^ 2) z * (v z) ^ 2)
      - (α * (5 + α) / 2) * ((g z * z) * (v z) ^ 2)) 0))
    rw [hT0]
    exact Tendsto.congr' (hTev 0 ha).symm tendsto_const_nhds
  -- the same value, in `β`-reduced form, as it appears in the conclusion of the F.T.C.
  have hT0' : -α ^ 2 * ((g 0 * 0 ^ 2) * v 0 * deriv v 0)
      + (α ^ 2 / 2) * (deriv (fun z => g z * z ^ 2) 0 * (v 0) ^ 2)
      - (α * (5 + α) / 2) * ((g 0 * 0) * (v 0) ^ 2) = 0 := hT0
  have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (m := (0 : ℝ))
    (f := fun z => -α ^ 2 * ((g z * z ^ 2) * v z * deriv v z)
      + (α ^ 2 / 2) * (deriv (fun z => g z * z ^ 2) z * (v z) ^ 2)
      - (α * (5 + α) / 2) * ((g z * z) * (v z) ^ 2))
    (f' := fun z => g z * (-(α ^ 2 * z ^ 2) * deriv (deriv v) z - (α * (5 + α) * z) * deriv v z)
          * v z
        - (α ^ 2 * (g z * z ^ 2 * (deriv v z) ^ 2)
          + (α * (5 + α) / 2) * (deriv (fun z => g z * z) z * (v z) ^ 2)
          - (α ^ 2 / 2) * (deriv (deriv (fun z => g z * z ^ 2)) z * (v z) ^ 2)))
    hTcont hderiv hintLR
    (Tendsto.congr' hTtop.symm tendsto_const_nhds)
  rw [hT0', sub_zero] at hftc
  -- ## Step 8: assembly
  have hLR : ∫ z in Set.Ioi 0,
        g z * (-(α ^ 2 * z ^ 2) * deriv (deriv v) z - (α * (5 + α) * z) * deriv v z) * v z
      = ∫ z in Set.Ioi 0,
        α ^ 2 * (g z * z ^ 2 * (deriv v z) ^ 2)
          + (α * (5 + α) / 2) * (deriv (fun z => g z * z) z * (v z) ^ 2)
          - (α ^ 2 / 2) * (deriv (deriv (fun z => g z * z ^ 2)) z * (v z) ^ 2) := by
    have h := hftc
    rw [MeasureTheory.integral_sub hintL hintR] at h
    exact sub_eq_zero.mp h
  have hsplit : ∫ z in Set.Ioi 0,
        α ^ 2 * (g z * z ^ 2 * (deriv v z) ^ 2)
          + (α * (5 + α) / 2) * (deriv (fun z => g z * z) z * (v z) ^ 2)
          - (α ^ 2 / 2) * (deriv (deriv (fun z => g z * z ^ 2)) z * (v z) ^ 2)
      = α ^ 2 * (∫ z in Set.Ioi 0, g z * z ^ 2 * (deriv v z) ^ 2)
        + (α * (5 + α) / 2)
            * (∫ z in Set.Ioi 0, deriv (fun z => g z * z) z * (v z) ^ 2)
        - (α ^ 2 / 2)
            * (∫ z in Set.Ioi 0, deriv (deriv (fun z => g z * z ^ 2)) z * (v z) ^ 2) := by
    have hP1 : IntegrableOn (fun z => α ^ 2 * (g z * z ^ 2 * (deriv v z) ^ 2)) (Set.Ioi 0) :=
      Integrable.const_mul hint0 (α ^ 2)
    have hP2 : IntegrableOn
        (fun z => (α * (5 + α) / 2) * (deriv (fun z => g z * z) z * (v z) ^ 2))
        (Set.Ioi 0) := Integrable.const_mul hint1 (α * (5 + α) / 2)
    have hP3 : IntegrableOn
        (fun z => (α ^ 2 / 2) * (deriv (deriv (fun z => g z * z ^ 2)) z * (v z) ^ 2))
        (Set.Ioi 0) := Integrable.const_mul hint2 (α ^ 2 / 2)
    have hP12 : IntegrableOn
        (fun z => α ^ 2 * (g z * z ^ 2 * (deriv v z) ^ 2)
          + (α * (5 + α) / 2) * (deriv (fun z => g z * z) z * (v z) ^ 2)) (Set.Ioi 0) :=
      IntegrableOn.add hP1 hP2
    rw [MeasureTheory.integral_sub hP12 hP3,
      MeasureTheory.integral_add hP1 hP2,
      MeasureTheory.integral_const_mul (α ^ 2) (fun z => g z * z ^ 2 * (deriv v z) ^ 2),
      MeasureTheory.integral_const_mul (α * (5 + α) / 2)
        (fun z => deriv (fun z => g z * z) z * (v z) ^ 2),
      MeasureTheory.integral_const_mul (α ^ 2 / 2)
        (fun z => deriv (deriv (fun z => g z * z ^ 2)) z * (v z) ^ 2)]
  rw [hLR, hsplit]

theorem aeZWtIBP (α : ℝ) (W φ v : ℝ → ℝ)
    (hW : ContDiff ℝ 2 W) (hcpt : HasCompactSupport W)
    (hW0 : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → W z = 0)
    (hφ : ContDiffOn ℝ 2 φ (Set.Ioi 0))
    (hv : ContDiffOn ℝ 2 v (Set.Ioi 0)) :
    (∫ z in Set.Ioi 0, W z * φ z
        * (-(α ^ 2 * z ^ 2) * deriv (deriv v) z - (α * (5 + α) * z) * deriv v z) * v z)
      = α ^ 2 * (∫ z in Set.Ioi 0, W z * φ z * z ^ 2 * (deriv v z) ^ 2)
        + (α * (5 + α) / 2)
            * (∫ z in Set.Ioi 0, deriv (fun z => W z * φ z * z) z * (v z) ^ 2)
        - (α ^ 2 / 2)
            * (∫ z in Set.Ioi 0, deriv (deriv (fun z => W z * φ z * z ^ 2)) z * (v z) ^ 2) := by
  obtain ⟨δ, hδ, hδ0⟩ := hW0
  obtain ⟨K, hKc, hK0⟩ := exists_compact_iff_hasCompactSupport.mpr hcpt
  have hM : BddAbove K := hKc.bddAbove
  obtain ⟨M, hM'⟩ := hM
  have hMb : ∀ b ∈ K, b ≤ M := fun b hb => hM' hb
  refine zw_ibp_general α δ (max M δ + 1) (fun z => W z * φ z) v hδ ?_ ?_ ?_ hv
  · -- `δ < max M δ + 1`
    have := le_max_right M δ
    linarith
  · -- `C²` of `W φ` on `(δ/2, ∞)`
    have hWc : ContDiffOn ℝ 2 W (Set.Ioi (δ / 2)) := hW.contDiffOn
    have hφc : ContDiffOn ℝ 2 φ (Set.Ioi (δ / 2)) :=
      hφ.mono (fun x hx => by
        simp only [Set.mem_Ioi] at hx ⊢
        linarith)
    exact hWc.mul hφc
  · -- `W φ` vanishes off the interval
    intro z hz
    rw [Set.mem_Ioo] at hz
    by_cases h1 : z ≤ δ
    · rw [hδ0 z h1]; ring
    · have h1' : δ < z := not_le.mp h1
      have h2 : max M δ + 1 ≤ z :=
        le_of_not_gt fun h2 => hz ⟨h1', h2⟩
      have h3 : M < z := by
        have := le_max_left M δ
        linarith
      have hzK : z ∉ K := fun h => absurd (hMb z h) (not_le.mpr h3)
      rw [hK0 z hzK]; ring

end Work.FTS.EllipticEst.AngAWeak
