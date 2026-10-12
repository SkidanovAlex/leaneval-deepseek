import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBox.potBracketG_eq_potWordU
import Submission.Work.BoseKinLoc.Sector.potWordU_slotComb
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.WordBridgeId`

The **word bridge**: the potential part of the localised box word `potWordU` (FS
`eq:Def_HB`, the multiplicative part of the box Hamiltonian with the ordered pair
convention `Σ_{i<j}` and whole-space fibre integrals) integrated against `Φ²` over the
box configuration space `abox n ℓ` agrees with the analysis-box potential word
`qLHSword` (FS `eq:potDefQ`, the `1/2 Σ_{i≠j}` convention with the **box** fibre
integrals and the χ-renormalised kernels `wPairC`).

This is the *repaired* form of
`Work.BoseFixB2.DvApriori.potWordU_form_eq_qLHSword` (which the present author's
sibling proved FALSE as stated in `Submission/Work/BoseFixB2/DvApriori/
potWordU_form_eq_qLHSword.lean`): the two missing hypotheses are

* `hvrad : BoseGases.IsRadial v` — radiality of the potential makes `v` even, hence the
  localised two-body kernel `wLoc ℓ v 0 = wPairC ℓ v` symmetric, which is exactly the
  condition under which the ordered and unordered pair conventions agree
  (`Work.BoseBox.potBracketG_eq_potWordU`); and
* `hℓ : 0 < ℓ` — the box fibre integral `w1Fibre ℓ (wLoc ℓ g 0) a = ∫_{acube ℓ}` agrees
  with the whole-space fibre integral `potBr ℓ g 0 a = ∫_{ℝ³}` for `ℓ > 0`, because the
  window `χ_0 = χ((ℓ⁻¹)•·)` of `wLoc ℓ g 0` vanishes off `acube ℓ`.

Both hypotheses are in force at the top level (`Challenge.lean`'s `theorem_1_2` carries
`hv_radial : IsRadial v`, and the box side is `ℓ = sideAt μ a > 0`).

The proof is the pointwise bracket identity `Work.BoseBox.potBracketG_eq_potWordU`
together with the definitional identification `wPairC ℓ h = wLoc ℓ h 0` of the two
kernel spellings, after which the two integrands coincide everywhere and the integrals
over `abox n ℓ` agree by `MeasureTheory.integral_congr_ae`.
-/

namespace Work.BoseFixR

open MeasureTheory
open scoped ContDiff Topology Real BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The χ-renormalised two-body kernel `wPairC ℓ h` (the analysis-box spelling) is the
localised kernel `wLoc ℓ h 0` at translation parameter `u = 0` (the Hamiltonian
spelling): both are `χ_ℓ(x) · h(x−y)/(χ⋆χ)_ℓ(x−y) · χ_ℓ(y)`, since `χU ℓ 0 x = χ_ℓ x`. -/
lemma wPairC_eq_wLoc_zero (ℓ : ℝ) (h : EuclideanSpace ℝ (Fin 3) → ℝ)
    (a b : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.wPairC ℓ h a b = Submission.BoseGases.wLoc ℓ h 0 a b := by
  simp [Submission.BoseGases.wPairC, Submission.BoseGases.wPair,
    Submission.BoseGases.wLoc, Submission.BoseGases.wScaled,
    Submission.BoseGases.chiU, Submission.BoseGases.chiScale, sub_zero]

/-- The box fibre integral of the analysis-box kernel agrees with the whole-space fibre
integral of the Hamiltonian kernel (for `ℓ > 0`): `∫_{acube ℓ} wPairC ℓ g a y dy =
∫_{ℝ³} wLoc ℓ g 0 a y dy`.  The window factor `χ_0(y)` of `wLoc ℓ g 0 a y` vanishes off
`acube ℓ`, so the box restricts the integral. -/
lemma w1Fibre_wPairC_eq_potBr {ℓ : ℝ} (hℓ : 0 < ℓ)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (a : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wPairC ℓ g) a
      = Work.BoseBox.potBr ℓ g 0 a := by
  have hfun : Submission.BoseGases.wPairC ℓ g = Submission.BoseGases.wLoc ℓ g 0 := by
    funext a b
    exact wPairC_eq_wLoc_zero ℓ g a b
  rw [hfun]
  unfold Submission.BoseGases.w1Fibre Work.BoseBox.potBr
  refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)
  have hh : Submission.BoseGases.chiU ℓ 0 y = 0 :=
    Work.BoseKinLoc.Sector.chiU_zero_of_notMem_acube hℓ hy
  simp [Submission.BoseGases.wLoc, hh]

/-- **The word bridge.**  See the module docstring: this is the repaired form of
`potWordU_form_eq_qLHSword`, with the two hypotheses `IsRadial v` and `0 < ℓ` restored. -/
theorem WordBridgeId {n : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hvrad : _root_.BoseGases.IsRadial v) {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.XN n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x)
      = Submission.BoseGases.qLHSword (N := n) ℓ μ (Submission.BoseGases.wPairC ℓ v)
          (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) Φ := by
  -- the two fibre integrals agree, and the two kernels agree
  have hfib : ∀ (g : EuclideanSpace ℝ (Fin 3) → ℝ)
      (a : EuclideanSpace ℝ (Fin 3)),
      Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wPairC ℓ g) a
        = Work.BoseBox.potBr ℓ g 0 a :=
    fun g a => w1Fibre_wPairC_eq_potBr hℓ g a
  -- unfold the analysis-box word into its diagonal density
  rw [Submission.BoseGases.qLHSword]
  -- the two integrands agree at every configuration
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  congr 1
  have h1 : (∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
      (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) (x i))
      = ∑ i : Fin n, Work.BoseBox.potBr ℓ (Submission.BoseGases.g0 v h) 0 (x i) :=
    Finset.sum_congr rfl (fun i _ => hfib (Submission.BoseGases.g0 v h) (x i))
  have h2 : (∑ p ∈ Submission.BoseGases.pairSet n,
        Submission.BoseGases.wPairC ℓ v (x p.1) (x p.2))
      = ∑ p ∈ Submission.BoseGases.pairSet n,
        Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2) :=
    Finset.sum_congr rfl (fun p _ => wPairC_eq_wLoc_zero ℓ v (x p.1) (x p.2))
  rw [h1, h2]
  -- the box bracket equals FS's `eq:Def_HB` multiplicative part (radiality of `v`)
  have hb := Work.BoseBox.potBracketG_eq_potWordU (N := n) (ℓ := ℓ) (μ := μ)
    (v := v) (h := h) hvrad 0 x
  unfold Work.BoseBox.potBracketG at hb
  exact hb.symm

end Work.BoseFixR
