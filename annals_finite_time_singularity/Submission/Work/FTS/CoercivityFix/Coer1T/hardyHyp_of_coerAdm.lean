/-
# `HardyHyp` for the interior class `CoerAdm`

The analytic hypothesis package `Work.Coercivity.HardyHyp` (the hypotheses of Lemma
`HardyWeight` of Elgindi's paper) holds for every datum of the *interior* class
`Work.FTS.Nonlin.CoerAdm α f = RegQ α 5 f ∧ VanishTheta f ∧ axis ∧ L₁₂(f)(0) = 0` with
`0 < α ≤ 10⁻¹⁴`.

The proof splits the seven fields of `HardyHyp` as follows.

* `hslice` — integrability of `θ ↦ K(θ) f z θ / z` on `Iθ` (`Kslice_integrableOn`), from the
  slicewise `L²`-bound `(f z θ)² ≤ HkIntegrand/(w z)²` (`Work.Spaces.sq_le_HkIntegrand_z`).
* `hcont` — continuity of the `L₁₂`-density at every `z > 0` (`Hardy.l12dens_continuousAt`).
* `hint` — `L₁₂dens ∈ L¹((0,∞))` (`Work.FTS.H2.L12densIntegrable`).
* `intB` — `(∫_θ f z θ²)/z^{2j} ∈ L¹((0,∞))` for `j ≤ 2`, dominated by the radial `ℋ⁴`-energy
  density `B4` (`intB_integrableOn`).
* `intA` — `(L₁₂ f)²/z^{2j} ∈ L¹((0,∞))` for `j ≤ 2`: on `(0,1]` by the Hardy-type inequality
  `Ioc_prim_sq_integrable` applied to `Ψ s = s √(B4 s)` together with the pointwise bound
  `|L₁₂ f z| ≤ √3 ∫_{(0,z]} Ψ` (`L12f_sq_div_small`); on `(1,∞)` by the dual Hardy inequality
  `Ioi_tail_sq_integrable` (`L12f_sq_div_large`).
* `bd0`, `bdTop` — the boundary terms at `0⁺` and at `∞` (`L12f_bd0`, `L12f_bdTop`), from the
  growth bounds `(L₁₂ f z)² ≤ 3 z³ ∫_{(0,z]} B4` near `0` and
  `|L₁₂ f z| ≤ √3 √(1/z) √(∫_{(z,∞)} B4)` near `∞`, whose corresponding integrals tend to `0`.
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Vocab
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.FTS.H2.L12densIntegrable
import Submission.Work.FM.Core
import Submission.Work.FM.Core2
import Submission.Work.FTS.CoercivityFix.Coer1T.HardyBasic
import Submission.Work.FTS.CoercivityFix.Coer1T.HardyAlt.l12dens_continuousAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Coer1T

theorem hardyHyp_of_coerAdm (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) :
    Work.Coercivity.HardyHyp f := by
  obtain ⟨hreg, hvan, haxis, hl12⟩ := hf
  obtain ⟨hsm, hmem5, hbdry⟩ := hreg
  have hmem : Work.Spaces.HkMem α 4 f := HkMem_four_of_five α hsm hmem5
  have hα1' : α ≤ 1 := by linarith [hα1]
  have hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0) := by
    have h := Work.FTS.H2.L12densIntegrable α f hα hα1' hsm hmem
    have h2 : Work.Elliptic.L12dens f = Work.FM.L12dens Work.Spaces.K f :=
      funext (fun z => Work.FTS.H2.L12dens_eq_FM_K f z)
    rwa [h2] at h
  have hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z :=
    fun z hz => Work.FTS.CoercivityFix.Coer1T.HardyAlt.l12dens_continuousAt α hsm hmem hz
  have hl12' : Work.Coercivity.L12f f 0 = 0 := by
    simpa [Work.Coercivity.L12f, Work.FM.L12, Work.Construction.L12] using hl12
  have hU : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi (0 : ℝ) := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith [h]
    · intro h
      rcases lt_trichotomy t 1 with h' | h' | h'
      · exact Or.inl ⟨h, h'.le⟩
      · exact Or.inl ⟨h, le_of_eq h'⟩
      · exact Or.inr h'
  refine ⟨?_, ?_, hint, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact Kslice_integrableOn α hsm hmem hz
  · exact hcont
  · intro j hj
    rw [← hU]
    refine MeasureTheory.IntegrableOn.union ?_ ?_
    · exact L12f_sq_div_small α hsm hmem hint hl12' hcont j hj
    · exact L12f_sq_div_large α hsm hmem hint hcont j
  · intro j hj
    exact intB_integrableOn α hsm hmem j hj
  · intro j hj
    exact L12f_bd0 α hsm hmem hint hl12' j hj
  · intro j hj
    exact L12f_bdTop α hsm hmem j

end Work.FTS.CoercivityFix.Coer1T
