/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W.PsiSlices.AeBasic`: two measure-theoretic tools for moment conditions a.e.

Both lemmas are about a function `V : ℝ → ℝ` which is interval integrable on the positive
half-line:

* `ae_eq_zero_of_forall_intervalIntegral_eq_zero`: if `∫_s^t V = 0` for **all** `0 < s, t`
  then `V = 0` a.e. on `(0,∞)` (Lebesgue differentiation, on the compact exhaustion
  `(0,∞) = ⋃_n [1/(n+1), n+2]`);

* `ae_eq_zero_of_moment_chain`: if `V` is the (interval-)derivative of a function `W` whose
  a.e. vanishing is known, in the *integrated* form
  `W t - W s = ∫_s^t V` for all `0 < s ≤ t`, then `V = 0` a.e. This is the form in which the
  angular-moment conditions are propagated by the radial differentiation `D_z = z ∂_z`: the
  hypothesis `W = 0` a.e. makes the primitive `z ↦ ∫_1^z V` a.e. constant, hence (by
  continuity) constant on `(0,∞)`, hence `V = 0` a.e.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.PsiSlices

set_option autoImplicit false

/-- **Lebesgue differentiation, interval form.** A function whose integral over every interval
`[s,t] ⊂ (0,∞)` vanishes, vanishes almost everywhere on `(0,∞)`. -/
theorem ae_eq_zero_of_forall_intervalIntegral_eq_zero {V : ℝ → ℝ}
    (hzero : ∀ s t : ℝ, 0 < s → 0 < t → ∫ r in s..t, V r = 0)
    (hInt : ∀ a b : ℝ, 0 < a → a < b → IntervalIntegrable V volume a b) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), V z = 0 := by
  -- the compact exhaustion `(0,∞) = ⋃_n [1/(n+1), n+2]`
  have hcover : Set.Ioi (0 : ℝ) = ⋃ n : ℕ, Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) := by
    ext z
    simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Icc]
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_ge (max (1 / z) z)
      refine ⟨n, ?_, ?_⟩
      · have h1 : 1 / z ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
        rw [div_le_iff₀ hz] at h1
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
        nlinarith
      · have h2 : z ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
        linarith
    · rintro ⟨n, h1, h2⟩
      exact lt_of_lt_of_le (by positivity) h1
  rw [hcover, MeasureTheory.ae_restrict_iUnion_iff]
  intro n
  set a : ℝ := 1 / ((n : ℝ) + 1) with ha
  set b : ℝ := (n : ℝ) + 2 with hb
  have hpos : 0 < a := by rw [ha]; positivity
  have hlt : a < b := by
    rw [ha, hb]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
  have hle : a ≤ b := hlt.le
  have hldt := IntervalIntegrable.ae_hasDerivAt_integral (hInt a b hpos hlt)
  rw [Set.uIcc_of_le (α := ℝ) hle] at hldt
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hldt] with x hx
  intro hxmem
  have hxpos : 0 < x := lt_of_lt_of_le hpos hxmem.1
  have hder : HasDerivAt (fun y : ℝ => ∫ t in a..y, V t) (V x) x :=
    hx hxmem a ⟨le_rfl, hle⟩
  have hev : (fun y : ℝ => ∫ t in a..y, V t) =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hxpos] with y hy
    exact hzero a y hpos hy
  have h0 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (V x) x := hev.hasDerivAt_iff.mp hder
  exact h0.unique (hasDerivAt_const x 0)

/-- Interval integrability on `(0,∞)` does not depend on the order of the two endpoints. -/
theorem intervalIntegrable_pos_of_lt {V : ℝ → ℝ}
    (hInt : ∀ a b : ℝ, 0 < a → a < b → IntervalIntegrable V volume a b) :
    ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable V volume a b := by
  intro a b ha hb
  rcases le_total a b with h | h
  · rcases eq_or_lt_of_le h with rfl | hlt
    · exact IntervalIntegrable.refl
    · exact hInt a b ha hlt
  · rcases eq_or_lt_of_le h with rfl | hlt
    · exact IntervalIntegrable.refl
    · exact (hInt b a hb hlt).symm

/-- **The integrated moment chain propagates a.e. vanishing.** If `W t - W s = ∫_s^t V` for
all `0 < s ≤ t`, `W` vanishes a.e. on `(0,∞)` and `V` is interval integrable on `(0,∞)`, then
`V` vanishes a.e. on `(0,∞)`. -/
theorem ae_eq_zero_of_moment_chain {W V : ℝ → ℝ}
    (hchain : ∀ s t : ℝ, 0 < s → s ≤ t → W t - W s = ∫ r in s..t, V r)
    (hW : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), W z = 0)
    (hInt : ∀ a b : ℝ, 0 < a → a < b → IntervalIntegrable V volume a b) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), V z = 0 := by
  have hInt' := intervalIntegrable_pos_of_lt hInt
  -- the primitive from `1` is `W · - W 1`
  have hP : ∀ z : ℝ, 0 < z → (∫ r in (1 : ℝ)..z, V r) = W z - W 1 := by
    intro z hz
    rcases le_total 1 z with h | h
    · exact (hchain 1 z one_pos h).symm
    · have h' := hchain z 1 hz h
      rw [intervalIntegral.integral_symm]
      linarith
  -- hence it is a.e. constant
  have hae : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      (∫ r in (1 : ℝ)..z, V r) = -(W 1) := by
    filter_upwards [hW, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz hzpos
    rw [hP z hzpos, hz, zero_sub]
  -- and it is continuous on `(0,∞)`
  have hcont : ContinuousOn (fun z : ℝ => ∫ r in (1 : ℝ)..z, V r) (Set.Ioi 0) := by
    intro x hx
    obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ,
        1 / ((n : ℝ) + 1) < x ∧ x < (n : ℝ) + 2 := by
      obtain ⟨n, hn⟩ := exists_nat_ge (max (1 / x) x)
      have h1 : 1 / x ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
      have h2 : x ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
      refine ⟨n, ?_, ?_⟩
      · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
        rw [div_le_iff₀ hx] at h1
        nlinarith
      · linarith
    have ha : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hb : 0 < (n : ℝ) + 2 := by positivity
    have hlt : 1 / ((n : ℝ) + 1) < (n : ℝ) + 2 := lt_trans hn1 hn2
    have hmem : (1 : ℝ) ∈ Set.uIcc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) := by
      rw [Set.uIcc_of_le (α := ℝ) hlt.le]
      refine ⟨?_, ?_⟩
      · rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]; linarith
      · linarith
    have hc := intervalIntegral.continuousOn_primitive_interval' (hInt' _ _ ha hb) hmem
    rw [Set.uIcc_of_le (α := ℝ) hlt.le] at hc
    exact (hc.continuousAt (Icc_mem_nhds hn1 hn2)).continuousWithinAt
  have hconst : Set.EqOn (fun z : ℝ => ∫ r in (1 : ℝ)..z, V r) (fun _ => -(W 1)) (Set.Ioi 0) :=
    MeasureTheory.Measure.eqOn_of_ae_eq hae hcont continuousOn_const
      (fun x hx => by rw [interior_Ioi]; exact subset_closure hx)
  -- hence every interval integral vanishes
  refine ae_eq_zero_of_forall_intervalIntegral_eq_zero (fun s t hs ht => ?_) hInt
  have hs1 : IntervalIntegrable V volume (1 : ℝ) t := hInt' 1 t one_pos ht
  have hs2 : IntervalIntegrable V volume (1 : ℝ) s := hInt' 1 s one_pos hs
  have h1 : ∫ r in (1 : ℝ)..t, V r = -(W 1) := hconst ht
  have h2 : ∫ r in (1 : ℝ)..s, V r = -(W 1) := hconst hs
  have h := intervalIntegral.integral_interval_sub_left (a := (1 : ℝ)) (b := t) (c := s) hs1 hs2
  rw [h1, h2] at h
  linarith [h]

end Work.FTS.EllipticEst.H2W.PsiSlices
