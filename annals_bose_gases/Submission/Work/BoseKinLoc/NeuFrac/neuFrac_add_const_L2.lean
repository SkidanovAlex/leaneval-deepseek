import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.NeuFrac.exists_box_bump
import Submission.Work.BoseKinLoc.NeuFrac.trial_value_mul_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.NeuFrac.neuFrac_add_const_L2` — `neuFrac` is blind to an additive constant

The requested lemma

```
lemma neuFrac_add_const (ℓ a2 : ℝ) (ha2 : 0 < a2) (u : ℝ³) (ϕ : ℝ³ → ℝ) (c : ℝ) :
    neuFrac ℓ a2 u (fun z => ϕ z + c) = neuFrac ℓ a2 u ϕ
```

is **false** as stated; the statements proved here are the correct ones, obtained by adding
the integrability hypothesis which makes the `sInf` defining `neuFrac` an honest functional
(exactly as in `Work.BoseKinLoc.NeuFrac.neuFrac_le_box_L2`, where the analogous
un-hypothesised inequality `neuFrac_le_box` is refuted).

## Why the unconditional statement fails

`neuFrac ℓ a2 u ψ` is the `sInf` of the trial values

`c(g) = ∫_Λ ψ² − 2a2∫_Λ ψ·g + a2·(Σ_k ∫_Λ (∂_k g)² + a2·∫_Λ g²)`,   `Λ = lamBox ℓ u`,

over `g` smooth with compact support.  The **first** term is a Bochner integral: for a
non-integrable integrand its value is `0` (`MeasureTheory.integral_undef`), not `∞`.  So if
`ψ² ∉ L¹(Λ)` — while `ψ ∈ L¹(Λ)`, so that the *middle* term is honest — the functional loses
the term `∫_Λ ψ²` and with it the cancellation that makes it blind to an additive constant:
for the shift `h := g + (c/a2)·η` (`η` a bump equal to `1` near the box, so that `h = g + c/a2`
and `∇h = ∇g` on `Λ`) one gets the *exact* identity

`c_ψ(h) = c_ϕ(g) − K`,   `K := 2c∫_Λ ϕ + c²·|Λ|`,

because the expansion of the first term that would supply `K` is replaced by `0 − 0 = 0`.
The map `g ↦ g + (c/a2)η` is a bijection of the set of admissible trials, so for such a `ϕ`
the two trial sets differ by the *translation* `K` and, whenever they are bounded below
(e.g. `ϕ(z) = ‖z − O‖⁻²`, `O` the centre of the box, which lies in `L^{6/5}(Λ) ⊂ H^{-1}(Λ)`,
so that the trial set *is* bounded below by Hölder + the Sobolev embedding
`W^{1,2}(Λ) ↪ L⁶(Λ)`), `csInf` translates with them:

`neuFrac ℓ a2 u (ϕ + 1) = neuFrac ℓ a2 u ϕ − (2∫_Λ ϕ + |Λ|) ≠ neuFrac ℓ a2 u ϕ`.

So `hϕ2` below (`ϕ² ∈ L¹(Λ)`) together with measurability of `ϕ` is exactly the missing
hypothesis: under it the first term is honest, the expansion `c_ψ(h) = c_ϕ(g)` is exact and
the two trial sets coincide.

## Contents

* `neuFracTrialVal` — the functional defining `neuFrac` (its `sInf`);
* `neuFracTrialVal_add_const` — the exact shift identity for admissible trials;
* `neuFrac_add_const_of_integrableOn_sq` — the corrected lemma for `ϕ² ∈ L¹(Λ)`, `ϕ`
  measurable;
* `neuFrac_add_const_of_integrableSq` — the same for `ϕ² ∈ L¹(ℝ³)` (global), matching the
  hypotheses used elsewhere in the layer (`bddBelow_trialSet`, `neuFrac_le_box_of_integrableSq`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.NeuFrac

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- The functional whose `sInf` over admissible trials is `neuFrac` (FS `eq:DefT`, first
term): the value at the trial `g` for the state `ψ`. -/
def neuFracTrialVal (ℓ a2 : ℝ) (u : ℝ³) (ψ g : ℝ³ → ℝ) : ℝ :=
  (∫ z in lamBox ℓ u, (ψ z) ^ 2)
    - 2 * a2 * (∫ z in lamBox ℓ u, ψ z * g z)
    + a2 * ((∑ k : Fin 3, ∫ z in lamBox ℓ u, (fderiv ℝ g z (kcStdBasis k)) ^ 2)
            + a2 * (∫ z in lamBox ℓ u, (g z) ^ 2))

/-- `neuFrac` is by definition the `sInf` of `neuFracTrialVal` over the smooth compactly supported
trials. -/
lemma neuFrac_eq_sInf (ℓ a2 : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    neuFrac ℓ a2 u ψ
      = sInf {y : ℝ | ∃ g : ℝ³ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
          y = neuFracTrialVal ℓ a2 u ψ g} :=
  rfl

/-! ## The moving box is closed, measurable and compact -/

lemma lamBox_isClosed (ℓ : ℝ) (u : ℝ³) : IsClosed (lamBox ℓ u) := by
  have h : lamBox ℓ u = (fun z : ℝ³ => z - ℓ • u) ⁻¹' acube ℓ := rfl
  rw [h]
  exact (acube_isClosed ℓ).preimage (by fun_prop)

lemma lamBox_isCompact (ℓ : ℝ) (u : ℝ³) : IsCompact (lamBox ℓ u) :=
  IsCompact.of_isClosed_subset (isCompact_closedBall (ℓ • u) (2 * (|ℓ| + 1)))
    (lamBox_isClosed ℓ u) (lamBox_subset_closedBall ℓ u)

/-! ## The shift identity

On the box, `g + t·η` agrees, together with its gradient, with `g + t`; hence replacing `ϕ` by
`ϕ + c` (where `c = t·a2`) and `g` by `g + t·η` does not change the functional — **provided
the integrals of `ϕ²` and `(ϕ + c)²` over the box are honest**, which is the hypothesis
`IntegrableOn (fun z => (ϕ z)^2) (lamBox ℓ u)` of the next lemma. -/

lemma abs_le_sq_add_one (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x + 1 / 2)]

lemma neuFracTrialVal_add_const {ℓ a2 R t : ℝ} {u : ℝ³} {ϕ : ℝ³ → ℝ} {c : ℝ}
    (ht : t * a2 = c) (ha2 : 0 < a2) (hϕm : Measurable ϕ)
    (hϕ2 : IntegrableOn (fun z : ℝ³ => (ϕ z) ^ 2) (lamBox ℓ u))
    {g η : ℝ³ → ℝ} (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g)
    (hbox : lamBox ℓ u ⊆ Metric.closedBall 0 R)
    (hη : ∀ z : ℝ³, ‖z‖ ≤ R → η =ᶠ[nhds z] 1) :
    neuFracTrialVal ℓ a2 u (fun z => ϕ z + c) (fun z => g z + t * η z) = neuFracTrialVal ℓ a2 u ϕ g := by
  have hfin : (volume : Measure ℝ³) (lamBox ℓ u) ≠ ⊤ := lamBox_measure_ne_top ℓ u
  have hmeas : MeasurableSet (lamBox ℓ u) := measurableSet_lamBox ℓ u
  have hcomp : IsCompact (lamBox ℓ u) := lamBox_isCompact ℓ u
  have hgc : Continuous g := hg.continuous
  have hgI : IntegrableOn g (lamBox ℓ u) :=
    ContinuousOn.integrableOn_compact hcomp hgc.continuousOn
  have hg2I : IntegrableOn (fun z : ℝ³ => (g z) ^ 2) (lamBox ℓ u) :=
    ContinuousOn.integrableOn_compact hcomp (hgc.pow 2).continuousOn
  -- `ϕ` itself is integrable on the box (dominated by `ϕ² + 1`)
  have hϕI : IntegrableOn ϕ (lamBox ℓ u) := by
    have h1 : Integrable (fun z : ℝ³ => (ϕ z) ^ 2 + 1) (volume.restrict (lamBox ℓ u)) := by
      have h2 : IntegrableOn (fun z : ℝ³ => (ϕ z) ^ 2 + 1) (lamBox ℓ u) :=
        hϕ2.add (integrableOn_const hfin)
      simpa [IntegrableOn] using h2
    show Integrable ϕ (volume.restrict (lamBox ℓ u))
    exact h1.mono' (hϕm.aestronglyMeasurable.restrict) (Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using abs_le_sq_add_one (ϕ z))
  -- `η = 1` pointwise on the box
  have hηbox : ∀ z ∈ lamBox ℓ u, η z = 1 := by
    intro z hz
    have hzR : ‖z‖ ≤ R := by
      have h := hbox hz
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    obtain ⟨s, hs, -, hsz⟩ := _root_.mem_nhds_iff.mp (hη z hzR)
    exact hs hsz
  -- the derivative of the shifted trial equals that of `g` on the box
  have hfd : ∀ z ∈ lamBox ℓ u, ∀ k : Fin 3,
      fderiv ℝ (fun z : ℝ³ => g z + t * η z) z (kcStdBasis k)
        = fderiv ℝ g z (kcStdBasis k) := by
    intro z hz k
    have hzR : ‖z‖ ≤ R := by
      have h := hbox hz
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    have hev : (fun w : ℝ³ => g w + t * η w) =ᶠ[nhds z] (fun w : ℝ³ => g w + t) := by
      filter_upwards [hη z hzR] with w hw
      simp [hw]
    have h1 : HasFDerivAt (fun w : ℝ³ => g w + t) (fderiv ℝ g z) z :=
      (((hg.differentiable (by simp)).differentiableAt).hasFDerivAt).add_const t
    have h2 : HasFDerivAt (fun w : ℝ³ => g w + t * η w) (fderiv ℝ g z) z :=
      h1.congr_of_eventuallyEq hev
    rw [h2.fderiv]
  -- expansion of `∫_Λ (ϕ + c)²`
  have hI1 : (∫ z in lamBox ℓ u, (ϕ z + c) ^ 2)
      = (∫ z in lamBox ℓ u, (ϕ z) ^ 2) + 2 * c * (∫ z in lamBox ℓ u, ϕ z)
        + c ^ 2 * (volume (lamBox ℓ u)).toReal := by
    have hc3 : IntegrableOn (fun z : ℝ³ => 2 * c * ϕ z) (lamBox ℓ u) := hϕI.const_mul (2 * c)
    have hc1 : IntegrableOn (fun z : ℝ³ => (ϕ z) ^ 2 + 2 * c * ϕ z) (lamBox ℓ u) :=
      hϕ2.add hc3
    have hc2 : IntegrableOn (fun _ : ℝ³ => c ^ 2) (lamBox ℓ u) :=
      integrableOn_const hfin
    rw [show (∫ z in lamBox ℓ u, (ϕ z + c) ^ 2)
        = ∫ z in lamBox ℓ u, ((ϕ z) ^ 2 + 2 * c * ϕ z + c ^ 2) from
      setIntegral_congr_fun hmeas (fun z _ => by ring)]
    rw [integral_add (f := fun z : ℝ³ => (ϕ z) ^ 2 + 2 * c * ϕ z)
      (g := fun _ : ℝ³ => c ^ 2) hc1 hc2]
    rw [integral_add (f := fun z : ℝ³ => (ϕ z) ^ 2) (g := fun z : ℝ³ => 2 * c * ϕ z)
      hϕ2 hc3,
      integral_const_mul (2 * c) (fun z : ℝ³ => ϕ z), setIntegral_const (c ^ 2),
      Measure.real_def, smul_eq_mul]
    ring
  -- expansion of `∫_Λ (ϕ + c)·(g + t)`
  have hI2 : (∫ z in lamBox ℓ u, (ϕ z + c) * (g z + t))
      = (∫ z in lamBox ℓ u, ϕ z * g z) + t * (∫ z in lamBox ℓ u, ϕ z)
        + c * (∫ z in lamBox ℓ u, g z)
        + (c * t) * (volume (lamBox ℓ u)).toReal := by
    have hA1 : IntegrableOn (fun z : ℝ³ => ϕ z * g z) (lamBox ℓ u) :=
      hϕI.mul_continuousOn hgc.continuousOn hcomp
    have hA2 : IntegrableOn (fun z : ℝ³ => t * ϕ z) (lamBox ℓ u) :=
      hϕI.const_mul t
    have hB1 : IntegrableOn (fun z : ℝ³ => c * g z) (lamBox ℓ u) := hgI.const_mul c
    have hB2 : IntegrableOn (fun _ : ℝ³ => c * t) (lamBox ℓ u) :=
      integrableOn_const hfin
    have hA : IntegrableOn (fun z : ℝ³ => ϕ z * g z + t * ϕ z) (lamBox ℓ u) := hA1.add hA2
    have hB : IntegrableOn (fun z : ℝ³ => c * g z + c * t) (lamBox ℓ u) := hB1.add hB2
    rw [show (∫ z in lamBox ℓ u, (ϕ z + c) * (g z + t))
        = ∫ z in lamBox ℓ u, ((ϕ z * g z + t * ϕ z) + (c * g z + c * t)) from
      setIntegral_congr_fun hmeas (fun z _ => by ring)]
    rw [integral_add (f := fun z : ℝ³ => ϕ z * g z + t * ϕ z)
      (g := fun z : ℝ³ => c * g z + c * t) hA hB]
    rw [integral_add (f := fun z : ℝ³ => ϕ z * g z) (g := fun z : ℝ³ => t * ϕ z) hA1 hA2,
      integral_add (f := fun z : ℝ³ => c * g z) (g := fun _ : ℝ³ => c * t) hB1 hB2,
      integral_const_mul t (fun z : ℝ³ => ϕ z), integral_const_mul c (fun z : ℝ³ => g z),
      setIntegral_const (c * t), Measure.real_def, smul_eq_mul]
    ring
  -- expansion of `∫_Λ (g + t)²`
  have hI3 : (∫ z in lamBox ℓ u, (g z + t) ^ 2)
      = (∫ z in lamBox ℓ u, (g z) ^ 2) + 2 * t * (∫ z in lamBox ℓ u, g z)
        + t ^ 2 * (volume (lamBox ℓ u)).toReal := by
    have hc3 : IntegrableOn (fun z : ℝ³ => 2 * t * g z) (lamBox ℓ u) := hgI.const_mul (2 * t)
    have hc1 : IntegrableOn (fun z : ℝ³ => (g z) ^ 2 + 2 * t * g z) (lamBox ℓ u) :=
      hg2I.add hc3
    have hc2 : IntegrableOn (fun _ : ℝ³ => t ^ 2) (lamBox ℓ u) :=
      integrableOn_const hfin
    rw [show (∫ z in lamBox ℓ u, (g z + t) ^ 2)
        = ∫ z in lamBox ℓ u, ((g z) ^ 2 + 2 * t * g z + t ^ 2) from
      setIntegral_congr_fun hmeas (fun z _ => by ring)]
    rw [integral_add (f := fun z : ℝ³ => (g z) ^ 2 + 2 * t * g z)
      (g := fun _ : ℝ³ => t ^ 2) hc1 hc2]
    rw [integral_add (f := fun z : ℝ³ => (g z) ^ 2) (g := fun z : ℝ³ => 2 * t * g z)
      hg2I hc3,
      integral_const_mul (2 * t) (fun z : ℝ³ => g z), setIntegral_const (t ^ 2),
      Measure.real_def, smul_eq_mul]
    ring
  -- the shifted trial agrees with `g + t` on the box
  have hI3' : (∫ z in lamBox ℓ u, (g z + t * η z) ^ 2)
      = ∫ z in lamBox ℓ u, (g z + t) ^ 2 := by
    refine setIntegral_congr_fun hmeas fun z hz => ?_
    rw [hηbox z hz]
    ring
  have hI2' : (∫ z in lamBox ℓ u, (ϕ z + c) * (g z + t * η z))
      = ∫ z in lamBox ℓ u, (ϕ z + c) * (g z + t) := by
    refine setIntegral_congr_fun hmeas fun z hz => ?_
    rw [hηbox z hz]
    ring
  have hI4 : (∑ k : Fin 3, ∫ z in lamBox ℓ u,
        (fderiv ℝ (fun z : ℝ³ => g z + t * η z) z (kcStdBasis k)) ^ 2)
      = ∑ k : Fin 3, ∫ z in lamBox ℓ u,
        (fderiv ℝ g z (kcStdBasis k)) ^ 2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    refine setIntegral_congr_fun hmeas fun z hz => ?_
    rw [hfd z hz k]
  unfold neuFracTrialVal
  rw [hI2', hI1, hI2, hI4, hI3', hI3, ← ht]
  ring

/-! ## The corrected statements -/

/-- **`neuFrac` is blind to an additive constant** (corrected form of the requested
`neuFrac_add_const`): if `ϕ` is measurable with `ϕ²` integrable on the box, the trial sets for
`ϕ` and for `ϕ + c` differ by the bijection `g ↦ g + (c/a2)·η` of the admissible trials, along
which the functional is exactly preserved (`neuFracTrialVal_add_const`). -/
theorem neuFrac_add_const_of_integrableOn_sq {ℓ a2 : ℝ} (ha2 : 0 < a2) (u : ℝ³)
    (ϕ : ℝ³ → ℝ) (c : ℝ) (hϕm : Measurable ϕ)
    (hϕ2 : IntegrableOn (fun z : ℝ³ => (ϕ z) ^ 2) (lamBox ℓ u)) :
    neuFrac ℓ a2 u (fun z => ϕ z + c) = neuFrac ℓ a2 u ϕ := by
  obtain ⟨R, η, hbox, hηdiff, hηcs, hη1⟩ := exists_box_bump ℓ u
  set flat : ℝ³ → ℝ := fun z => (c / a2) * η z with hflat
  have ha2ne : a2 ≠ 0 := ne_of_gt ha2
  have hflat_diff : ContDiff ℝ ∞ flat := by
    simpa [hflat] using (contDiff_const.mul hηdiff :
      ContDiff ℝ ∞ (fun z : ℝ³ => (c / a2) * η z))
  have hflat_cs : HasCompactSupport flat := hηcs.mul_left (f := fun _ : ℝ³ => c / a2)
  have hkey : ∀ g : ℝ³ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      neuFracTrialVal ℓ a2 u (fun z => ϕ z + c) (fun z => g z + flat z) = neuFracTrialVal ℓ a2 u ϕ g := by
    intro g hg hgs
    have h := neuFracTrialVal_add_const (ℓ := ℓ) (a2 := a2) (R := R) (t := c / a2) (u := u)
      (ϕ := ϕ) (c := c) (ht := div_mul_cancel₀ c ha2ne) ha2 hϕm hϕ2 hg hgs hbox hη1
    simpa [flat] using h
  have hset : {y : ℝ | ∃ g : ℝ³ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
        y = neuFracTrialVal ℓ a2 u (fun z => ϕ z + c) g}
      = {y : ℝ | ∃ g : ℝ³ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
        y = neuFracTrialVal ℓ a2 u ϕ g} := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro y ⟨h, hhd, hhcs, hy⟩
      have hshift := hkey (h - flat) (hhd.sub hflat_diff) (hhcs.sub hflat_cs)
      have h1 : (fun z : ℝ³ => (h - flat) z + flat z) = h := by funext z; simp
      rw [h1] at hshift
      exact ⟨h - flat, hhd.sub hflat_diff, hhcs.sub hflat_cs, hy.trans hshift⟩
    · rintro y ⟨g, hgd, hgcs, hy⟩
      refine ⟨g + flat, hgd.add hflat_diff, hgcs.add hflat_cs, ?_⟩
      have h1 : (fun z : ℝ³ => g z + flat z) = g + flat := rfl
      rw [hy, ← h1, hkey g hgd hgcs]
  rw [neuFrac_eq_sInf, neuFrac_eq_sInf, hset]

/-- The corrected statement under the *global* square-integrability hypothesis used elsewhere
in this layer (`bddBelow_trialSet`, `neuFrac_le_box_of_integrableSq`). -/
theorem neuFrac_add_const_of_integrableSq {ℓ a2 : ℝ} (ha2 : 0 < a2) (u : ℝ³) (ϕ : ℝ³ → ℝ)
    (c : ℝ) (hϕm : Measurable ϕ) (hϕ : Integrable (fun z : ℝ³ => (ϕ z) ^ 2)) :
    neuFrac ℓ a2 u (fun z => ϕ z + c) = neuFrac ℓ a2 u ϕ :=
  neuFrac_add_const_of_integrableOn_sq ha2 u ϕ c hϕm hϕ.integrableOn

end Work.BoseKinLoc.NeuFrac
