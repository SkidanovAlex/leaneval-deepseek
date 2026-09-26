import Mathlib
import Submission.Work.Asymptotics.funnel_tauAtom_second_order
import Submission.Work.Asymptotics.KhatE1Core.E14AtomDeep
import Submission.Work.Asymptotics.KhatE1Core.E2SThirdOrder

/-!
# The `z`-atom references of the `K₊`-half: `E₄`, `E₆`, `E₂ˢ`, `E₁₄`, `E₄⁻³`

This module is the first slice of the `K₊` analogue of `KMinus24Split`: it introduces the
*reference* (cusp-truncated) values of the `z`-atoms occurring in `Sm1, …, Sm5`

  `E4Ref = 1 + 240q + 2160q²`,  `E6Ref = 1 - 504q - 16632q²`,  `E2SRef = S0z - 24q - 72q²`,
  `E14Ref = 1 - 24q - 196632q²`,  `I4Ref = 1 - 720q + 339120q²`   (`q = qParamFun z`)

and the corresponding *deviations* `dE4, dE6, dE2S, dE14, dI4`, defined as the literal
differences.  Consequently the splits `atom = ref + dev` are pure `ring` identities, with no
analysis anywhere.

**Truncation rule.**  Every reference is truncated at `E = Ept z`-degree `≤ 5` (equivalently
`q`-degree `≤ 2`), so every deviation is `O(‖E‖⁶)`.  This is exactly the depth at which a
deviation times a cofactor of weight `‖q(τ)‖⁻¹ (scale τ)^N (1+t)^M` lands on the allowed
remainder shape `‖q(τ)‖⁻¹ ‖E‖⁶` of `Bracket24ExpansionHold`, and it is the depth supplied by the
proved atom layer (`E4Fun_second_order`, `E6Fun_second_order`, `E2SThirdOrder`,
`E14FunFourthOrder`).

The deviation bounds recorded here are therefore stated in the normalised form
`‖d·z‖ ≤ C ‖q(z)‖³` (so that `‖d·z‖ = O(‖E‖⁶)`), and follow immediately from those proved
lemmas.  Only the `E₄⁻³`-deviation `dI4` is left to the (queued) `InvE4cubeFourthOrder`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-! ## The reference atoms -/

/-- Reference value of `E₄(z)` at the cusp. -/
def E4Ref (z : ℍ) : ℂ := 1 + 240 * Work.Kernels.qParamFun z
  + 2160 * (Work.Kernels.qParamFun z) ^ 2

/-- Reference value of `E₆(z)` at the cusp. -/
def E6Ref (z : ℍ) : ℂ := 1 - 504 * Work.Kernels.qParamFun z
  - 16632 * (Work.Kernels.qParamFun z) ^ 2

/-- Reference value of `E₂ˢ(z)` at the cusp. -/
def E2SRef (z : ℍ) : ℂ := Work.Asymptotics.KhatE1.S0z z
  - 24 * Work.Kernels.qParamFun z - 72 * (Work.Kernels.qParamFun z) ^ 2

/-- Reference value of `E₁₄(z) = E₄(z)²E₆(z)` at the cusp. -/
def E14Ref (z : ℍ) : ℂ := 1 - 24 * Work.Kernels.qParamFun z
  - 196632 * (Work.Kernels.qParamFun z) ^ 2

/-- Reference value of `E₄(z)⁻³` at the cusp. -/
def I4Ref (z : ℍ) : ℂ := 1 - 720 * Work.Kernels.qParamFun z
  + 339120 * (Work.Kernels.qParamFun z) ^ 2

/-! ## The deviations -/

/-- Deviation of `E₄(z)` from its cusp reference. -/
def dE4 (z : ℍ) : ℂ := Work.Kernels.E4Fun z - E4Ref z

/-- Deviation of `E₆(z)` from its cusp reference. -/
def dE6 (z : ℍ) : ℂ := Work.Kernels.E6Fun z - E6Ref z

/-- Deviation of `E₂ˢ(z)` from its cusp reference. -/
def dE2S (z : ℍ) : ℂ := Work.Kernels.E2S z - E2SRef z

/-- Deviation of `E₁₄(z)` from its cusp reference. -/
def dE14 (z : ℍ) : ℂ := Work.Kernels.E14Fun z - E14Ref z

/-- Deviation of `E₄(z)⁻³` from its cusp reference (written with `E₄(z)^3` inverted, which is
the form in which it occurs in `K24F.Phi = Pfun - Vfun / E₄(z)^3`). -/
def dI4 (z : ℍ) : ℂ := (Work.Kernels.E4Fun z)⁻¹ ^ 3 - I4Ref z

/-! ## The splits (pure `ring`) -/

lemma E4Fun_ref_split (z : ℍ) : Work.Kernels.E4Fun z = E4Ref z + dE4 z := by
  simp only [dE4]; ring

lemma E6Fun_ref_split (z : ℍ) : Work.Kernels.E6Fun z = E6Ref z + dE6 z := by
  simp only [dE6]; ring

lemma E2S_ref_split (z : ℍ) : Work.Kernels.E2S z = E2SRef z + dE2S z := by
  simp only [dE2S]; ring

lemma E14Fun_ref_split (z : ℍ) : Work.Kernels.E14Fun z = E14Ref z + dE14 z := by
  simp only [dE14]; ring

lemma E4Fun_inv_cube_ref_split (z : ℍ) :
    (Work.Kernels.E4Fun z)⁻¹ ^ 3 = I4Ref z + dI4 z := by
  simp only [dI4]; ring

/-! ## The deviation bounds (from the proved atom layer) -/

/-- `‖dE4 z‖ = O(‖q(z)‖³)` (i.e. `O(‖Ept z‖⁶)`). -/
lemma dE4_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖dE4 z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E4Fun_second_order
  refine ⟨C, hC, fun z hz => ?_⟩
  have key : dE4 z = Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z
      - 2160 * (Work.Kernels.qParamFun z) ^ 2 := by
    simp only [dE4, E4Ref]; ring
  rw [key]; exact h z hz

/-- `‖dE6 z‖ = O(‖q(z)‖³)`. -/
lemma dE6_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖dE6 z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E6Fun_second_order
  refine ⟨C, hC, fun z hz => ?_⟩
  have key : dE6 z = Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z
      + 16632 * (Work.Kernels.qParamFun z) ^ 2 := by
    simp only [dE6, E6Ref]; ring
  rw [key]; exact h z hz

/-- `‖dE2S z‖ = O(‖q(z)‖³)`. -/
lemma dE2S_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖dE2S z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := E2SThirdOrder
  exact ⟨C, hC, fun z hz => by simpa only [dE2S, E2SRef] using h z hz⟩

/-- `‖dE14 z‖ = O(‖q(z)‖³)`. -/
lemma dE14_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖dE14 z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := E14FunFourthOrder
  exact ⟨C, hC, fun z hz => by simpa only [dE14, E14Ref] using h z hz⟩

end

end Work.Asymptotics.KhatE1Core
