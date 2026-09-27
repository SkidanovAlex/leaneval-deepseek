import Mathlib
import Submission.Work.EKLComp.FlowerDefs
import Submission.Work.EKLRelCross.Instances

/-!
# `Work.EKLComp.flower_piece_borel`

The piece of a flower over a *compact* parameter set `K ⊆ U` is Borel.

`collar U R C = (Uball U R) • C` is the special case `K = Uball U R`, but that ball is open
(not compact), whereas the flower construction of the EKL argument is applied with compact
`K` (a closed ball `Ucl U R`, an orbit segment, a `[0,T]`-flow box).  The present lemma treats
that case:  if `K` is compact, lies in `U`, is `e`-small (`∀ v₁ v₂ ∈ K, v₂⁻¹ v₁ ∈ Uball U e`),
if `A` is Borel and `U`-free, and `A` is `e`-separated, then the image of `K × A` under the
action map is Borel.

The proof is the Lusin–Suslin argument:  on `K × A` the action map is *injective* (uniqueness
of the flower coordinates — this is where freeness and separation are used), it is continuous,
the source is Borel in the Polish space `SL₃(ℝ) × X₃`, and a continuous injective map on a
Borel subset of a Polish space has Borel image
(`MeasurableSet.image_of_continuousOn_injOn`).

## Injectivity

Let `(k₁, a₁), (k₂, a₂) ∈ K × A` with `k₁ • a₁ = k₂ • a₂`.  Applying `k₂⁻¹` and using
`hKsmall` gives `a₂ = (k₂⁻¹k₁) • a₁` with `k₂⁻¹k₁ ∈ Uball U e`; `e`-separation of `A` forces
`a₂ = a₁`, and then `k₂⁻¹k₁ ∈ U` fixes `a₁ ∈ A`, so `U`-freeness of `A` gives `k₂⁻¹k₁ = 1`,
i.e. `k₁ = k₂`.
-/

open MeasureTheory Topology Filter
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLComp

open Work.EKLContract

/-- **The `K`-piece of a flower over a measurable separated set is Borel.**  For compact `K ⊆ U`
with `∀ v₁ v₂ ∈ K, v₂⁻¹ v₁ ∈ Uball U e`, a measurable `U`-free `e`-separated set `A`, the set
`K • A = {(k, a) ↦ k • a}` is a Borel subset of `X₃`. -/
theorem flower_piece_borel {U : Subgroup Work.EKLContract.SL3} {e : ℝ}
    {K : Set Work.EKLContract.SL3} (hKc : IsCompact K) (hKU : K ⊆ (U : Set Work.EKLContract.SL3))
    (hKsmall : ∀ v₁ ∈ K, ∀ v₂ ∈ K, v₂⁻¹ * v₁ ∈ Work.EKLComp.Uball U e)
    {A : Set Work.EKLContract.X3} (hA : MeasurableSet A) (hfree : Work.EKLComp.FreeOn U A)
    (hsep : Work.EKLComp.SepOn U e A) :
    MeasurableSet ((fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 => p.1 • p.2) '' (K ×ˢ A)) := by
  haveI : PolishSpace SL3 := Work.EKLContract.Lemmas.polishSpace_specialLinearGroup
  refine MeasurableSet.image_of_continuousOn_injOn ?_ ?_ ?_
  · exact hKc.isClosed.measurableSet.prod hA
  · exact continuous_smul.continuousOn
  -- injectivity of the action map on `K × A`
  rintro ⟨v₁, a₁⟩ ⟨hv₁, ha₁⟩ ⟨v₂, a₂⟩ ⟨hv₂, ha₂⟩ heq
  change v₁ • a₁ = v₂ • a₂ at heq
  -- `a₂ = (v₂⁻¹ v₁) • a₁` with `v₂⁻¹ v₁ ∈ Uball U e`
  have hv : v₂⁻¹ * v₁ ∈ Uball U e := hKsmall v₁ hv₁ v₂ hv₂
  have hsmul : (v₂⁻¹ * v₁) • a₁ = a₂ := by rw [mul_smul, heq, inv_smul_smul]
  -- `e`-separation forces `a₂ = a₁`
  have ha : a₂ = a₁ := hsep a₁ ha₁ a₂ ha₂ (v₂⁻¹ * v₁) hv hsmul.symm
  -- freeness at `a₁` forces `v₂⁻¹ v₁ = 1`
  have hone : v₂⁻¹ * v₁ = 1 :=
    hfree a₁ ha₁ (v₂⁻¹ * v₁) hv.1 (hsmul.trans ha)
  have hvv : v₂ = v₁ := inv_mul_eq_one.mp hone
  have haa : a₁ = a₂ := by rw [hvv] at heq; exact smul_left_cancel v₁ heq
  exact Prod.ext hvv.symm haa

end Work.EKLComp
