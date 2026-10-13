import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the second weak-curl pairing

This file proves `Work.FTS.PressureOn.weakCurl.int2_integrable`, the measure-theoretic input of the
weak-curl identity `weakCurl_pair`:

> `x ↦ ⟪∂u(·,t)|ₓ (ω x t) − ∂ω(·,t)|ₓ (u x t), A x⟫` is integrable,

for `A` of class `C^∞` with compact support, `u(·,s)` of class `C¹` and `ω(·,t)` continuous, and
the Jacobian `Dω(·,t)` locally integrable.

## Route

The whole integrand `F` is supported in `tsupport A` (it is `⟪…, A x⟫`, so it vanishes where `A`
does), a compact set, so it suffices to dominate it there by a locally integrable function — the
task of the helper `integrable_of_support_subset_compact_of_bound` below.

* The first summand `∂u(·,t)|ₓ (ω x t)` is bounded on the compact `tsupport A`, because `D(u(·,t))`
  is *continuous* (`u(·,t) ∈ C¹`) and `ω(·,t)` is continuous.
* The second summand `∂ω(·,t)|ₓ (u x t)` is not bounded, but on the compact `tsupport A` it is
  dominated by `‖∂ω(·,t)|ₓ‖ · sup ‖u(·,t)‖`, and `‖∂ω(·,t)‖` is locally integrable (hypothesis
  `hωint`), hence integrable over the compact `tsupport A`.
* Almost-everywhere strong measurability of `F` is obtained from
  `LocallyIntegrable.aestronglyMeasurable` for `Dω(·,t)`, continuity of `u(·,t)`, `ω(·,t)`, `A`, and
  continuity of the application map `(L, v) ↦ L v` and of the inner product.

No use is made of `hR` (the uniform support of `ω(·,s)` in `s`) or of `hωdiff` (the differentiability
of `ω(·,t)` off the axis and the plane): the statement only needs `Dω(·,t)` to be locally integrable.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace Work.FTS.PressureOn.weakCurl

/-- **A function supported in a compact set and dominated by a locally integrable function is
integrable.**  If `f : ℝ³ → ℝ` vanishes off the compact `K`, is a.e. strongly measurable, and is
bounded on `K` by `C * (‖g‖ + 1)` for some locally integrable `g` and some constant `C`, then `f` is
integrable.  (No sign condition on `C` is needed: the bound is only used on `K`.) -/
lemma integrable_of_support_subset_compact_of_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : R3 → ℝ} {g : R3 → E} {K : Set R3} (hK : IsCompact K)
    (hf : ∀ x, x ∉ K → f x = 0) (hfm : AEStronglyMeasurable f)
    (hgl : MeasureTheory.LocallyIntegrable g) {C : ℝ}
    (hbd : ∀ x ∈ K, ‖f x‖ ≤ C * (‖g x‖ + 1)) : MeasureTheory.Integrable f := by
  have hbase : IntegrableOn (fun x => C * (‖g x‖ + 1)) K :=
    ((hgl.integrableOn_isCompact hK).norm.add
      (integrableOn_const (μ := volume) (s := K) hK.measure_ne_top)).const_mul C
  have hgi : Integrable (K.indicator (fun x => C * (‖g x‖ + 1))) :=
    (integrable_indicator_iff hK.measurableSet).mpr hbase
  refine hgi.mono' hfm ?_
  filter_upwards with x
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]; exact hbd x hx
  · rw [hf x hx, norm_zero, Set.indicator_of_notMem hx]

-- `hR` and `hωdiff` are part of the requested statement but not needed by the proof (see the
-- module docstring); silence the "unused variable" linter rather than touch the statement.
set_option linter.unusedVariables false in
theorem int2_integrable {u ω : R3 → ℝ → R3} {t : ℝ} {A : R3 → R3}
    (hA : ∀ n : ℕ, ContDiff ℝ n A) (hAcs : HasCompactSupport A)
    (hR : ∃ R : ℝ, 0 ≤ R ∧ ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R)
    (hsnbhd : ∀ s ∈ Set.Ioo (t - 1) (t + 1), ContDiff ℝ 1 (u · s))
    (hωcont : Continuous (fun x => ω x t))
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt (fun x => ω x t) (fderiv ℝ (ω · t) x) x)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ (ω · t) x)) :
    MeasureTheory.Integrable (fun x => inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
      - fderiv ℝ (fun y => ω y t) x (u x t)) (A x)) := by
  have ht : t ∈ Set.Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hu : ContDiff ℝ 1 (fun y => u y t) := hsnbhd t ht
  have hu_cont : Continuous (fun x => u x t) := hu.continuous
  have hu_fd : Continuous (fun x => fderiv ℝ (fun y => u y t) x) :=
    hu.continuous_fderiv (by norm_num)
  have hA_cont : Continuous A := contDiff_zero.mp (hA 0)
  have hK : IsCompact (tsupport A) := hAcs
  -- a.e. strong measurability: the application map and the inner product are continuous
  have hae : AEStronglyMeasurable (fun x => inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
      - fderiv ℝ (fun y => ω y t) x (u x t)) (A x)) := by
    have happ : Continuous (fun p : (R3 →L[ℝ] R3) × R3 => p.1 p.2) :=
      continuous_fst.clm_apply continuous_snd
    have hT1 : AEStronglyMeasurable (fun x => fderiv ℝ (fun y => u y t) x (ω x t)) :=
      happ.comp_aestronglyMeasurable
        (hu_fd.aestronglyMeasurable.prodMk hωcont.aestronglyMeasurable)
    have hDω : AEStronglyMeasurable (fun x => fderiv ℝ (fun y => ω y t) x) :=
      hωint.aestronglyMeasurable
    have hT2 : AEStronglyMeasurable (fun x => fderiv ℝ (fun y => ω y t) x (u x t)) :=
      happ.comp_aestronglyMeasurable (hDω.prodMk hu_cont.aestronglyMeasurable)
    have hT : AEStronglyMeasurable (fun x => fderiv ℝ (fun y => u y t) x (ω x t)
        - fderiv ℝ (fun y => ω y t) x (u x t)) := hT1.sub hT2
    have hpair : AEStronglyMeasurable (fun x => (fderiv ℝ (fun y => u y t) x (ω x t)
        - fderiv ℝ (fun y => ω y t) x (u x t), A x)) :=
      hT.prodMk hA_cont.aestronglyMeasurable
    exact (continuous_inner (𝕜 := ℝ)).comp_aestronglyMeasurable hpair
  -- the integrand vanishes off the (compact) support of `A`
  have hsupp : ∀ x, x ∉ tsupport A → inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
      - fderiv ℝ (fun y => ω y t) x (u x t)) (A x) = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := A) hx, inner_zero_right]
  -- the bounds on the compact support of `A`
  obtain ⟨Cd, hCd0⟩ := IsCompact.exists_bound_of_continuousOn hK hu_fd.continuousOn
  obtain ⟨Cw, hCw0⟩ := IsCompact.exists_bound_of_continuousOn hK hωcont.continuousOn
  obtain ⟨Cu, hCu0⟩ := IsCompact.exists_bound_of_continuousOn hK hu_cont.continuousOn
  obtain ⟨Ca, hCa0⟩ := IsCompact.exists_bound_of_continuousOn hK hA_cont.continuousOn
  have hbd : ∀ x ∈ tsupport A, ‖inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
      - fderiv ℝ (fun y => ω y t) x (u x t)) (A x)‖
      ≤ (max 0 Cd * max 0 Cw * max 0 Ca + max 0 Cu * max 0 Ca)
        * (‖fderiv ℝ (fun y => ω y t) x‖ + 1) := by
    intro x hx
    have hd : ‖fderiv ℝ (fun y => u y t) x‖ ≤ max 0 Cd :=
      le_trans (hCd0 x hx) (le_max_right _ _)
    have hw : ‖ω x t‖ ≤ max 0 Cw := le_trans (hCw0 x hx) (le_max_right _ _)
    have hU : ‖u x t‖ ≤ max 0 Cu := le_trans (hCu0 x hx) (le_max_right _ _)
    have ha : ‖A x‖ ≤ max 0 Ca := le_trans (hCa0 x hx) (le_max_right _ _)
    have h1 : 0 ≤ max 0 Cd := le_max_left _ _
    have h2 : 0 ≤ max 0 Cw := le_max_left _ _
    have h3 : 0 ≤ max 0 Cu := le_max_left _ _
    have h4 : 0 ≤ max 0 Ca := le_max_left _ _
    have hD0 : 0 ≤ ‖fderiv ℝ (fun y => ω y t) x‖ := norm_nonneg _
    have hA0 : 0 ≤ ‖A x‖ := norm_nonneg _
    have step1 : ‖inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
          - fderiv ℝ (fun y => ω y t) x (u x t)) (A x)‖
        ≤ (‖fderiv ℝ (fun y => u y t) x (ω x t)‖
            + ‖fderiv ℝ (fun y => ω y t) x (u x t)‖) * ‖A x‖ := by
      refine le_trans (norm_inner_le_norm _ _) ?_
      exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) hA0
    have step2 : (‖fderiv ℝ (fun y => u y t) x (ω x t)‖
            + ‖fderiv ℝ (fun y => ω y t) x (u x t)‖) * ‖A x‖
        ≤ (max 0 Cd * max 0 Cw + max 0 Cu * ‖fderiv ℝ (fun y => ω y t) x‖)
          * max 0 Ca := by
      apply mul_le_mul
      · refine add_le_add ?_ ?_
        · calc ‖(fderiv ℝ (fun y => u y t) x) (ω x t)‖
              ≤ ‖fderiv ℝ (fun y => u y t) x‖ * ‖ω x t‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ max 0 Cd * max 0 Cw := mul_le_mul hd hw (norm_nonneg _) h1
        · calc ‖fderiv ℝ (fun y => ω y t) x (u x t)‖
              ≤ ‖fderiv ℝ (fun y => ω y t) x‖ * ‖u x t‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ ‖fderiv ℝ (fun y => ω y t) x‖ * max 0 Cu := mul_le_mul_of_nonneg_left hU hD0
            _ = max 0 Cu * ‖fderiv ℝ (fun y => ω y t) x‖ := by ring
      · exact ha
      · exact hA0
      · exact add_nonneg (mul_nonneg h1 h2) (mul_nonneg h3 hD0)
    have step3 : (max 0 Cd * max 0 Cw + max 0 Cu * ‖fderiv ℝ (fun y => ω y t) x‖)
          * max 0 Ca
        ≤ (max 0 Cd * max 0 Cw * max 0 Ca + max 0 Cu * max 0 Ca)
          * (‖fderiv ℝ (fun y => ω y t) x‖ + 1) := by
      have hX : max 0 Cd * max 0 Cw * max 0 Ca
          ≤ max 0 Cd * max 0 Cw * max 0 Ca + max 0 Cu * max 0 Ca :=
        le_add_of_nonneg_right (mul_nonneg h3 h4)
      have hY : max 0 Cu * max 0 Ca
          ≤ max 0 Cd * max 0 Cw * max 0 Ca + max 0 Cu * max 0 Ca :=
        le_add_of_nonneg_left (mul_nonneg (mul_nonneg h1 h2) h4)
      have hYD : ‖fderiv ℝ (fun y => ω y t) x‖ * (max 0 Cu * max 0 Ca)
          ≤ ‖fderiv ℝ (fun y => ω y t) x‖
            * (max 0 Cd * max 0 Cw * max 0 Ca + max 0 Cu * max 0 Ca) :=
        mul_le_mul_of_nonneg_left hY hD0
      have hsum : (max 0 Cd * max 0 Cw + max 0 Cu * ‖fderiv ℝ (fun y => ω y t) x‖)
            * max 0 Ca
          = max 0 Cd * max 0 Cw * max 0 Ca
            + ‖fderiv ℝ (fun y => ω y t) x‖ * (max 0 Cu * max 0 Ca) := by ring
      rw [hsum]
      nlinarith [hX, hYD, hD0]
    linarith
  exact integrable_of_support_subset_compact_of_bound hK hsupp hae hωint hbd

end Work.FTS.PressureOn.weakCurl
