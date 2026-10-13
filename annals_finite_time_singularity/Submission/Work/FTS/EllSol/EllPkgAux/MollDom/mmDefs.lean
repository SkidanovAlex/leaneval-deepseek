/-
# `Work.FTS.EllSol.EllPkgAux.MollDom.mmDefs` — the vocabulary of `mollMaster`

The two-kernel domination estimate `Work.FTS.EllSol.EllPkgAux.MollDom.mollMaster` bounds the
`σ_η`-weighted `w²`-functional of `F` by that of `X`, given the pointwise domination of `|F|`
by the double convolution of `|X|` against the two kernels `sKer δ (log z - ·)` (logarithmic
radial) and `KJ ε θ ·` (angular).

This module fixes the three functionals that the proof manipulates, and the two measurability
facts about them:

* `MmV X t = ∫_{Iθ} (X (e^t) s)² σ_η(s) ds` — the slice functional of `X` in the logarithmic
  radial variable;
* `MmPsi ε X θ t = ∫_{Iθ} KJ ε θ s · |X (e^t) s| ds` — the angular convolution of `|X (e^t) ·|`;
* `MmAp ε X θ t = ∫_{Iθ} KJ ε θ s · (X (e^t) s)² ds` — the same with the square (the Jensen
  upper bound for `MmPsi²`).

Together with `ljOm_one_le` (the weight `Ω(t) = w(e^t)² e^t` is at least `1`, so that `L¹`
statements for `Ω · V` localise to `L¹` statements for `V`) and the a.e. strong measurability
of `MmV X`, `MmPsi ε X θ`, `MmAp ε X θ` and of the `F`-slice `z ↦ ∫_{Iθ} F z θ² σ_η(θ)`,
these are all the auxiliary objects needed by `mollMaster` and by the lemmas
`radSchur`, `radSwap`, `V_ljOm_integrable`, `pointwise_bound`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.KernelDefs
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.kernelJensen
import Submission.Work.FTS.EllSol.EllPkgAux.logJensen
import Submission.Work.FTS.EllSol.EllPkgAux.wExpCmp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open Work.FTS.EllSol.PkgK5.K5c

local notation "Iθ" => Work.Spaces.Iθ

/-- The `σ_η`-weighted slice functional of `X` in the logarithmic radial variable:
`MmV X t = ∫_{Iθ} (X (e^t) s)² σ_η(s) ds`. -/
def MmV (X : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Iθ, (X (Real.exp t) s) ^ 2 * Work.FTS.EllipticEst.thEta s

/-- The angular convolution of `|X (e^t) ·|` with the three-image kernel `KJ ε θ ·`. -/
def MmPsi (ε : ℝ) (X : ℝ → ℝ → ℝ) (θ t : ℝ) : ℝ :=
  ∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |X (Real.exp t) s|

/-- The angular convolution of `(X (e^t) ·)²` with the three-image kernel `KJ ε θ ·`. -/
def MmAp (ε : ℝ) (X : ℝ → ℝ → ℝ) (θ t : ℝ) : ℝ :=
  ∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * (X (Real.exp t) s) ^ 2

/-- The logarithmic weight `Ω(t) = w(e^t)² e^t` is at least `1`.
(Indeed `Ω t = (1 + e^t)⁴ / (e^t)³ ≥ 1` because `(1 + e^t)⁴ ≥ (e^t)⁴ ≥ (e^t)³`.) -/
lemma ljOm_one_le (t : ℝ) : 1 ≤ Work.FTS.EllSol.EllPkgAux.ljOm t := by
  have hpos : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hkey : (Real.exp t) ^ 3 ≤ (1 + Real.exp t) ^ 4 := by
    have h1 : (Real.exp t) ^ 3 ≤ (1 + Real.exp t) ^ 3 :=
      pow_le_pow_left₀ hpos.le (by linarith [hpos]) 3
    have h2 : (1 + Real.exp t) ^ 3 ≤ (1 + Real.exp t) ^ 4 :=
      pow_le_pow_right₀ (by linarith [hpos]) (by norm_num)
    linarith
  have hform : Work.FTS.EllSol.EllPkgAux.ljOm t
      = (1 + Real.exp t) ^ 4 / (Real.exp t) ^ 3 := by
    rw [Work.FTS.EllSol.EllPkgAux.ljOm, Work.Spaces.w]
    field_simp
  rw [hform, le_div_iff₀ (pow_pos hpos 3)]
  simpa using hkey


/-- A.e. strong measurability of the slice functional `MmV X` in the logarithmic radial
variable, from the joint measurability of `(t,s) ↦ X (e^t) s`.  Only the marginal
measurability of a product-measure integrand is used
(`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`), no integrability. -/
theorem MmV_aesm {X : ℝ → ℝ → ℝ}
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Iθ))) :
    AEStronglyMeasurable (fun t : ℝ => MmV X t) volume := by
  have hσ : AEStronglyMeasurable (fun s : ℝ => Work.FTS.EllipticEst.thEta s)
      (volume.restrict Iθ) :=
    Work.FTS.EllipticEst.integrableOn_thEta.1.aestronglyMeasurable
  have hX : AEStronglyMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ)) := hXmeas.aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (X (Real.exp p.1) p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
      (volume.prod (volume.restrict Iθ)) := (hX.pow 2).mul hσ.comp_snd
  have h3 := h2.integral_prod_right' (ν := volume.restrict Iθ)
  simpa only [MmV] using h3

/-- A.e. strong measurability of the angular convolution `MmPsi ε X θ` in the radial variable
`t` (for fixed `θ`), from the joint measurability of `(t,s) ↦ X (e^t) s`. -/
theorem MmPsi_aesm {X : ℝ → ℝ → ℝ}
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Iθ))) (ε θ : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => MmPsi ε X θ t) volume := by
  have hsk : Continuous (fun s : ℝ => sKer ε s) :=
    Work.FTS.EllSol.K5cAux.continuous_sKer ε
  have h1 : AEMeasurable (fun p : ℝ × ℝ => sKer ε (θ - p.2))
      (volume.prod (volume.restrict Iθ)) :=
    (hsk.measurable.comp (measurable_const.sub measurable_snd)).aemeasurable
  have h2 : AEMeasurable (fun p : ℝ × ℝ => sKer ε (θ + p.2))
      (volume.prod (volume.restrict Iθ)) :=
    (hsk.measurable.comp (measurable_const.add measurable_snd)).aemeasurable
  have h3 : AEMeasurable (fun p : ℝ × ℝ => sKer ε (θ + p.2 - Real.pi))
      (volume.prod (volume.restrict Iθ)) :=
    (hsk.measurable.comp
      ((measurable_const.add measurable_snd).sub measurable_const)).aemeasurable
  have hKae : AEMeasurable (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ p.2)
      (volume.prod (volume.restrict Iθ)) :=
    (h1.add h2).add h3
  have h4 : AEMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.EllSol.EllPkgAux.KJ ε θ p.2 * |X (Real.exp p.1) p.2|)
      (volume.prod (volume.restrict Iθ)) := hKae.mul hXmeas.abs
  have h5 := h4.aestronglyMeasurable.integral_prod_right' (ν := volume.restrict Iθ)
  simpa only [MmPsi] using h5

/-- A.e. strong measurability of the angular convolution `MmAp ε X θ` in the radial variable
`t` (for fixed `θ`), from the joint measurability of `(t,s) ↦ X (e^t) s`. -/
theorem MmAp_aesm {X : ℝ → ℝ → ℝ}
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Iθ))) (ε θ : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => MmAp ε X θ t) volume := by
  have hsk : Continuous (fun s : ℝ => sKer ε s) :=
    Work.FTS.EllSol.K5cAux.continuous_sKer ε
  have h1 : AEMeasurable (fun p : ℝ × ℝ => sKer ε (θ - p.2))
      (volume.prod (volume.restrict Iθ)) :=
    (hsk.measurable.comp (measurable_const.sub measurable_snd)).aemeasurable
  have h2 : AEMeasurable (fun p : ℝ × ℝ => sKer ε (θ + p.2))
      (volume.prod (volume.restrict Iθ)) :=
    (hsk.measurable.comp (measurable_const.add measurable_snd)).aemeasurable
  have h3 : AEMeasurable (fun p : ℝ × ℝ => sKer ε (θ + p.2 - Real.pi))
      (volume.prod (volume.restrict Iθ)) :=
    (hsk.measurable.comp
      ((measurable_const.add measurable_snd).sub measurable_const)).aemeasurable
  have hKae : AEMeasurable (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ p.2)
      (volume.prod (volume.restrict Iθ)) :=
    (h1.add h2).add h3
  have h4 : AEMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.EllSol.EllPkgAux.KJ ε θ p.2 * (X (Real.exp p.1) p.2) ^ 2)
      (volume.prod (volume.restrict Iθ)) := hKae.mul (hXmeas.pow_const 2)
  have h5 := h4.aestronglyMeasurable.integral_prod_right' (ν := volume.restrict Iθ)
  simpa only [MmAp] using h5

/-- A.e. strong measurability of the `F`-slice functional `z ↦ ∫_{Iθ} F z θ² σ_η(θ)`, from the
joint measurability of `F` on `ℝ × Iθ`. -/
theorem Fslice_aesm {F : ℝ → ℝ → ℝ}
    (hFmeas : AEMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Iθ))) :
    AEStronglyMeasurable (fun z : ℝ =>
      ∫ θ in Iθ, (F z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) volume := by
  have hσ : AEStronglyMeasurable (fun s : ℝ => Work.FTS.EllipticEst.thEta s)
      (volume.restrict Iθ) :=
    Work.FTS.EllipticEst.integrableOn_thEta.1.aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (F p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2) (volume.prod (volume.restrict Iθ)) :=
    ((hFmeas.aestronglyMeasurable).pow 2).mul hσ.comp_snd
  have h3 := h2.integral_prod_right' (ν := volume.restrict Iθ)
  simpa only using h3

end Work.FTS.EllSol.EllPkgAux.MollDom
