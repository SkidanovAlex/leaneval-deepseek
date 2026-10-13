import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.BiotSavart.TimeDerivContinuous
import Submission.Work.CoreResiduals.BiotSavart.WindowExtDefs
import Submission.Work.CoreResiduals.BiotSavart.exists_holder_bound_add_smul
import Submission.Work.CoreResiduals.BiotSavart.continuousAt_of_norm_sub_le_rpow
import Submission.Work.CoreResiduals.BiotSavart.windowExt_holder_bound
import Submission.Work.CoreResiduals.BiotSavart.windowExt_localBdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals.BiotSavart

/-- **Continuity in `t` of the glued `∂ₜ`-slices.**  `dtExt ω S y ·` is the composition of the
`∂ₜ`-slice `∂ₜω(y,·)` with the clamping map `t ↦ max 0 (min t S)`; since that map is `1`-Lipschitz
and the `∂ₜ`-slice is `α`-Hölder on `Icc 0 S`, the glued slice is `α`-Hölder on all of `ℝ`, hence
continuous everywhere. -/
theorem continuousAt_dtExt {α : NNReal} (hα : 0 < (α : ℝ)) {ω : R3 → ℝ → R3} {S : ℝ}
    (hS : 0 < S) {N₁ : ℝ}
    (hN₁ : ∀ y : R3, ∀ u ∈ Set.Icc (0:ℝ) S, ∀ v ∈ Set.Icc (0:ℝ) S,
      ‖FiniteTimeSingularity.timeDeriv ω y u - FiniteTimeSingularity.timeDeriv ω y v‖
        ≤ N₁ * |u - v| ^ (α : ℝ))
    (y : R3) (t : ℝ) : ContinuousAt (fun s : ℝ => dtExt ω S y s) t := by
  set N₁' := max N₁ 0 with hN₁'def
  have hN₁'nn : 0 ≤ N₁' := le_max_right _ _
  have hb : ∀ s : ℝ, ‖dtExt ω S y s - dtExt ω S y t‖ ≤ N₁' * |s - t| ^ (α : ℝ) := by
    intro s
    have hs_mem : max 0 (min s S) ∈ Set.Icc (0:ℝ) S :=
      ⟨le_max_left _ _, max_le (le_of_lt hS) (min_le_right _ _)⟩
    have ht_mem : max 0 (min t S) ∈ Set.Icc (0:ℝ) S :=
      ⟨le_max_left _ _, max_le (le_of_lt hS) (min_le_right _ _)⟩
    have hclamp : |max 0 (min s S) - max 0 (min t S)| ≤ |s - t| := by
      have h1 := abs_max_sub_max_le_max 0 (min s S) 0 (min t S)
      have h2 := abs_min_sub_min_le_max s S t S
      have h3 : max |0 - (0:ℝ)| |min s S - min t S| = |min s S - min t S| := by
        rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
      have h4 : max |s - t| |S - S| = |s - t| := by
        rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
      rw [h3] at h1
      rw [h4] at h2
      exact le_trans h1 h2
    rw [dtExt_eq_clamp (ω := ω) (S := S) (y := y) (t := s) hS,
        dtExt_eq_clamp (ω := ω) (S := S) (y := y) (t := t) hS]
    refine le_trans (hN₁ y _ hs_mem _ ht_mem) ?_
    have hpow : |max 0 (min s S) - max 0 (min t S)| ^ (α : ℝ) ≤ |s - t| ^ (α : ℝ) :=
      Real.rpow_le_rpow (abs_nonneg _) hclamp (le_of_lt hα)
    calc N₁ * |max 0 (min s S) - max 0 (min t S)| ^ (α : ℝ)
        ≤ N₁' * |max 0 (min s S) - max 0 (min t S)| ^ (α : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _)
      _ ≤ N₁' * |s - t| ^ (α : ℝ) := mul_le_mul_of_nonneg_left hpow hN₁'nn
  exact continuousAt_of_norm_sub_le_rpow (f := fun s : ℝ => dtExt ω S y s) hα hN₁'nn hb

/-- **The two-sided time-extension of a bundled strip vorticity.**

Let `0 < α < 1`, let `S > 0`, let `ω` satisfy the full strip bundle `BSAdmissibleStripFull α ω R S`,
and assume additionally that the `∂ₜ`-slices `x ↦ ∂ₜω(x,t)` are Hölder in `x`, uniformly on the
strip (this is the conclusion of `timeDeriv_xHolderOn_of_stripBundle`; the extension needs it in
order to be `x`-Hölder for `t < 0`).

Conclusion: there is an extension `ω_ext` of `ω` in the time variable, agreeing with `ω` on the
strip, which satisfies

* the *window* admissibility bundle `BSAdmissibleOnWindow ω_ext R (S+1)` — the hypotheses of
  `Work.CoreResiduals.BiotSavart.biotSavartSpacetimeC1_holds` apart from the Lipschitz clause — and
* `Work.CoreResiduals.TimeDerivLocallyContinuous ω_ext (S+1)` — the `∂ₜ`-slices are locally
  continuous in `t`.

**Suggested construction** (glue `ω` to its affine continuation outside the strip):
`ω_ext y t = ω y 0 + t • ∂ₜω(y,0)` for `t ≤ 0`; `= ω y t` for `0 ≤ t ≤ S`;
`= ω y S + (t-S) • ∂ₜω(y,S)` for `t ≥ S`.

Checks needed:

* *agreement* on `Icc 0 S`, and `ω_ext y 0 = ω y 0`, `ω_ext y S = ω y S` at the junctions;
* *support*: for `y ∉ closedBall 0 R` one has `ω y t = 0` for `t ∈ Icc 0 S`, hence `ω y 0 = 0`,
  `ω y S = 0`, and moreover `∂ₜω(y,0) = 0`, `∂ₜω(y,S) = 0`: the strip bundle gives the (two-sided)
  `HasDerivAt` of `s ↦ ω y s` at the endpoint times, while the right (resp. left) difference quotient
  vanishes identically on `(0, min(S,1))` (resp. `(max(S-1,0), S)`), so the derivative is `0` — e.g.
  by combining `h.hasDerivWithinAt` on `Ici 0` with the `HasDerivWithinAt` of the constant `0` and
  `HasDerivWithinAt.unique` (`uniqueDiffWithinAt_Ici`), or by `HasDerivWithinAt.union`;
* the *local clauses of `BSAdmissibleOnWindow`* (for `t₀ ∈ preWindow (S+1) = Ioo (-2) (S+1)`, with a
  locality `ε` chosen so that the window lies in at most one of the three regimes, or straddles a
  junction): local boundedness `M + |t|M₁`; local `x`-Hölder (from the strip clause at times in
  `Icc 0 S`, and from the strip clause at the endpoint together with the extra `∂ₜ`-Hölder
  hypothesis on the affine pieces); local measurability (`AEStronglyMeasurable.add`, `.const_smul`
  of the strip measurability clauses at the endpoint times); local `t`-differentiability with the
  matching `timeDeriv` (the affine pieces give `HasDerivAt ... (∂ₜω(y,0)) t`, and at a junction the
  required statement is `HasDerivAt (fun s => ω_ext y s) (timeDeriv ω_ext y 0) 0` for the *same*
  value, which follows from `HasDerivWithinAt.union` of the two one-sided derivatives — the value
  `timeDeriv ω_ext y 0` is then `∂ₜω(y,0)` by `HasDerivAt.unique`/`HasDerivAt.deriv`);
  local bound `max M₁ 0` on `∂ₜω_ext`; local measurability of the `∂ₜω_ext`-slices; and
* *continuity in `t` of the `∂ₜ`-slices*: on the affine pieces `∂ₜω_ext y ·` is constant, and across
  a junction the strip side converges to the endpoint value by the `α`-Hölder clause of `∂ₜω`
  (`TimeDerivStripHolder` with one of the two times equal to `0` resp. `S`). -/
theorem exists_windowExtension_of_stripBundle {α : NNReal} (hα : 0 < (α : ℝ)) (hα1 : (α : ℝ) < 1)
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S : ℝ} (hS : 0 < S)
    (hbun : BSAdmissibleStripFull α ω R S)
    (hxH : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : Work.LWP.R3, ∀ t ∈ Set.Icc (0:ℝ) S,
      ‖FiniteTimeSingularity.timeDeriv ω a t - FiniteTimeSingularity.timeDeriv ω b t‖
        ≤ C * ‖a - b‖ ^ c) :
    ∃ ω_ext : Work.LWP.R3 → ℝ → Work.LWP.R3,
      (∀ t ∈ Set.Icc (0:ℝ) S, ∀ y : Work.LWP.R3, ω_ext y t = ω y t) ∧
      BSAdmissibleOnWindow ω_ext R (S + 1) ∧
      TimeDerivLocallyContinuous ω_ext (S + 1) := by
  have hstrip := hbun.1
  have hTD := hbun.2.1
  have hTDH := hbun.2.2
  obtain ⟨hRpos, hsupp, hbdd, hholder, htholder, hslices⟩ := hstrip
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨H, hH⟩ := hholder
  have hdiff := hTD.1
  obtain ⟨M₁, hM₁⟩ := hTD.2.1
  have hdtmeas := hTD.2.2
  obtain ⟨N₁, hN₁⟩ := hTDH
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) S := ⟨le_refl 0, le_of_lt hS⟩
  have hSmem : S ∈ Set.Icc (0:ℝ) S := ⟨le_of_lt hS, le_refl S⟩
  refine ⟨windowExt ω S, ?_, ?_, ?_⟩
  · intro t ht y
    exact windowExt_of_mem_Icc ht
  · refine ⟨hRpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t y hy
      by_contra hyb
      exact hy (windowExt_eq_zero_of_notMem_closedBall hS hsupp hdiff hyb t)
    · intro t₀ _
      obtain ⟨M', hM'⟩ := windowExt_localBdd hS hbun t₀
      exact ⟨1, one_pos, M', fun t ht y => hM' t ht y⟩
    · intro t₀ _
      obtain ⟨c, hc, C, hC⟩ := windowExt_holder_bound hα hS hbun hxH t₀
      exact ⟨1, one_pos, c, hc, C, fun t ht a b => hC t ht a b⟩
    · intro t₀ _
      refine ⟨1, one_pos, fun t _ => ?_⟩
      by_cases h : t ≤ 0
      · have heq : (fun y : Work.LWP.R3 => windowExt ω S y t)
            = fun y => ω y 0 + t • FiniteTimeSingularity.timeDeriv ω y 0 := by
          funext y; exact windowExt_of_nonpos h
        rw [heq]
        exact (hslices 0 h0mem).add ((hdtmeas 0 h0mem).const_smul t)
      · by_cases h2 : t ≤ S
        · have heq : (fun y : Work.LWP.R3 => windowExt ω S y t) = fun y => ω y t := by
            funext y; exact windowExt_of_mem_Icc ⟨le_of_lt (lt_of_not_ge h), h2⟩
          rw [heq]
          exact hslices t ⟨le_of_lt (lt_of_not_ge h), h2⟩
        · have heq : (fun y : Work.LWP.R3 => windowExt ω S y t)
              = fun y => ω y S + (t - S) • FiniteTimeSingularity.timeDeriv ω y S := by
            funext y; exact windowExt_of_ge hS (le_of_lt (lt_of_not_ge h2))
          rw [heq]
          exact (hslices S hSmem).add ((hdtmeas S hSmem).const_smul (t - S))
    · intro t₀ _
      refine ⟨1, one_pos, fun t _ y => ?_⟩
      rw [timeDeriv_windowExt hS hdiff y t]
      exact hasDerivAt_windowExt hS hdiff y t
    · intro t₀ _
      refine ⟨1, one_pos, max M₁ 0, fun t _ y => ?_⟩
      rw [timeDeriv_windowExt hS hdiff y t]
      by_cases h : t ≤ 0
      · rw [dtExt_of_nonpos h]
        exact le_trans (hM₁ 0 h0mem y) (le_max_left _ _)
      · by_cases h2 : t ≤ S
        · rw [dtExt_of_mem_Icc ⟨le_of_lt (lt_of_not_ge h), h2⟩]
          exact le_trans (hM₁ t ⟨le_of_lt (lt_of_not_ge h), h2⟩ y) (le_max_left _ _)
        · rw [dtExt_of_ge hS (le_of_lt (lt_of_not_ge h2))]
          exact le_trans (hM₁ S hSmem y) (le_max_left _ _)
    · intro t₀ _
      refine ⟨1, one_pos, fun t _ => ?_⟩
      have heq : (fun y : Work.LWP.R3 => FiniteTimeSingularity.timeDeriv (windowExt ω S) y t)
          = fun y => dtExt ω S y t := by
        funext y; exact timeDeriv_windowExt hS hdiff y t
      rw [heq]
      by_cases h : t ≤ 0
      · have heq2 : (fun y : Work.LWP.R3 => dtExt ω S y t)
            = fun y => FiniteTimeSingularity.timeDeriv ω y 0 := by
          funext y; exact dtExt_of_nonpos h
        rw [heq2]
        exact hdtmeas 0 h0mem
      · by_cases h2 : t ≤ S
        · have heq2 : (fun y : Work.LWP.R3 => dtExt ω S y t)
              = fun y => FiniteTimeSingularity.timeDeriv ω y t := by
            funext y; exact dtExt_of_mem_Icc ⟨le_of_lt (lt_of_not_ge h), h2⟩
          rw [heq2]
          exact hdtmeas t ⟨le_of_lt (lt_of_not_ge h), h2⟩
        · have heq2 : (fun y : Work.LWP.R3 => dtExt ω S y t)
              = fun y => FiniteTimeSingularity.timeDeriv ω y S := by
            funext y; exact dtExt_of_ge hS (le_of_lt (lt_of_not_ge h2))
          rw [heq2]
          exact hdtmeas S hSmem
  · intro t₀ _
    refine ⟨1, one_pos, fun t _ y => ?_⟩
    have heq : (fun s : ℝ => FiniteTimeSingularity.timeDeriv (windowExt ω S) y s)
        = fun s => dtExt ω S y s := by
      funext s; exact timeDeriv_windowExt hS hdiff y s
    rw [heq]
    exact continuousAt_dtExt hα hS hN₁ y t

end Work.CoreResiduals.BiotSavart
