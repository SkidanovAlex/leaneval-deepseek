/-
Copyright: work module for the Elgindi finite-time singularity project.

# The seven-slot honesty transfer from a *vanishing* family

The elliptic `ℋ^k`-estimate is applied to the three derivatives

  `z²∂_z²Ψ`,   `∂_θ²Ψ`,   `z ∂_z∂_θ²Ψ`

so their `HkNorm α 7` must be honest (`Work.Spaces.HkMem α 7`).  The sibling
`HkMem_seven_slots_of_plain_family` derives this from the *plain* family
`∀ j m, j ≤ 9 → m ≤ 9 → HkMem α 0 (D_z^j ∂_θ^m Ψ)`.  Here the hypothesis is the sharp one
available in the elliptic node: only the *pure* radial slots are honest against the singular
weight `σ = sin(2θ)^{-η}` up to angular order `2`,

  `hσ : ∀ l m, l ≤ 9 → m ≤ 2 → HkMem α 0 (D_z^l ∂_θ^m Ψ)`,

while the angular slots of order `3 ≤ t ≤ 9` are only known to be integrable against the
*vanishing* weights `sin(2θ)^{2t-4-γ}` (`0 < 2t-4-γ`),

  `hV : 3 ≤ t ≤ 9 → l ≤ 9 → ∫_θ (D_z^l ∂_θ^t Ψ · w)² sin(2θ)^{2t-4-γ} < ∞`.

This is exactly the sharpened reduction `HkMem_of_pure_and_vanishing`, whose input families are
the level-`0` honesty of the pure radial slots and the integrability of the vanishing-weight
slots `vig α f r j` (`1 ≤ r`, `r + j ≤ k`).  The proof has three layers:

* **pointwise slot reduction** (`HkIntegrand_le_pure_vanishing`): the `ℋ^7`-integrand is
  dominated by the pure radial level-`0` integrands plus the `vanC`-weighted vanishing slots;
* **per-slot bounds against the grid majorant** `vanGrid α Ψ` (the sum of all the integrands
  whose integrability `hσ` and `hV` provide): for each of the three functions every pure slot
  and every vanishing slot is dominated by `4 · vanGrid α Ψ`;
* **assembly** (`HkMem_seven_of_grid`): `HkMem_of_majorant_ae` with the majorant
  `K · vanGrid α Ψ`, where the constant `K` collects the `vanC`'s and the two slot bounds.

Everything here is `sorry`-free.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.HkMem_of_pure_and_vanishing
import Submission.Work.FTS.ClassC.VanishFamilyDefs
import Submission.Work.FTS.ClassC.VanishWeightDom
import Submission.Work.FTS.ClassC.PureVanishingReduction
import Submission.Work.FTS.ClassC.vanGrid_integrable
import Submission.Work.FTS.ClassC.HkIntegrand_seven_le_of_bounds_Ioo
import Submission.Work.FTS.ClassC.HkIntegrand_zero_DzIter_zsqPz2_le
import Submission.Work.FTS.ClassC.vig_zsqPz2_le
import Submission.Work.FTS.ClassC.HkIntegrand_zero_DzIter_pthIter_two_le
import Submission.Work.FTS.ClassC.VigPthIter2Bound
import Submission.Work.FTS.ClassC.HkIntegrand_zero_DzIter_Dz_pthIter_two_le
import Submission.Work.FTS.ClassC.vig_Dz_pthIter_two_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The assembly step.**  If the grid majorant `vanGrid α Ψ` is integrable on the angular
interval and in the outer `z`-variable, and if for a function `f` (smooth on the open quadrant)
every pure radial level-`0` slot and every vanishing-weight angular slot of level `7` is
dominated on the open quadrant by `4 · vanGrid α Ψ`, then `f ∈ ℋ⁷`. -/
theorem HkMem_seven_of_grid {α : ℝ} (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {Ψ : ℝ → ℝ → ℝ}
    (hG : (∀ z ∈ Work.Spaces.Iz,
        IntegrableOn (fun θ => vanGrid α Ψ z θ) Work.Spaces.Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, vanGrid α Ψ z θ) Work.Spaces.Iz)
    {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (h0 : ∀ j : ℕ, j ≤ 7 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ ≤ 4 * vanGrid α Ψ z θ)
    (h1 : ∀ j r : ℕ, 1 ≤ r → r + j ≤ 7 → ∀ z : ℝ, 0 < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → vig α f r j z θ ≤ 4 * vanGrid α Ψ z θ) :
    Work.Spaces.HkMem α 7 f := by
  have hKpos : (0 : ℝ) < 32 + 32 * vanSum α hα hγ f hsm 7 := by
    have := vanSum_nonneg α hα hγ f hsm 7
    linarith
  refine Work.FTS.EllipticEst.HkMem_of_majorant_ae (M := fun z θ =>
      (32 + 32 * vanSum α hα hγ f hsm 7) * vanGrid α Ψ z θ) α 7
    (hsm.continuousOn_HkIntegrand α 7) ?_ ?_ ?_
  · intro z hz
    exact (hG.1 z hz).const_mul (32 + 32 * vanSum α hα hγ f hsm 7)
  · refine IntegrableOn.congr_fun
      (hG.2.const_mul (32 + 32 * vanSum α hα hγ f hsm 7)) (fun z _ => ?_) measurableSet_Ici
    exact (MeasureTheory.integral_const_mul _ _).symm
  · intro z hz
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      rw [Work.FTS.LocData.HkIntegrand_zero_fst]
      exact mul_nonneg (le_of_lt hKpos)
        (vanGrid_nonneg α Ψ 0 ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    · exact HkIntegrand_seven_le_of_bounds_Ioo hα hγ hsm
        (fun z θ hθ' => vanGrid_nonneg α Ψ z ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩) h0 h1 hzpos hθ

/-- **The seven-slot honesty transfer from a vanishing family.**  If `Ψ` is `C^∞` on the open
quadrant, all the *pure* radial slots `D_z^l ∂_θ^m Ψ` (`l ≤ 9`, `m ≤ 2`) are honest at level `0`
(singular `η`-weight), and all the angular slots of order `3 ≤ t ≤ 9` are integrable against the
*vanishing* weights `sin(2θ)^{2t-4-γ}` (both slicewise and in the outer `z`-integral), then the
three derivatives `z²∂_z²Ψ`, `∂_θ²Ψ` and `z ∂_z∂_θ²Ψ` lie in `ℋ⁷`. -/
theorem HkMem_seven_slots_of_vanishing_family {α : ℝ} (hα : 0 < α)
    (hγ : Work.Spaces.gam α ≤ 3 / 2) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hσ : ∀ l m : ℕ, l ≤ 9 → m ≤ 2 →
      Work.Spaces.HkMem α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)))
    (hV : ∀ t l : ℕ, 3 ≤ t → t ≤ 9 → l ≤ 9 →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t Ψ) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t Ψ) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iz)
    : Work.Spaces.HkMem α 7 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ∧
      Work.Spaces.HkMem α 7 (Work.Spaces.pthIter 2 Ψ) ∧
      Work.Spaces.HkMem α 7 (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) := by
  have hG := vanGrid_integrable hα hγ hΨ hσ hV
  refine ⟨?_, ?_, ?_⟩
  · -- conjunct 1: `z² ∂_z² Ψ`
    refine HkMem_seven_of_grid hα hγ hG ((hΨ.pzIter 2).zsq_mul) ?_ ?_
    · intro j hj z hz θ hθ
      exact HkIntegrand_zero_DzIter_zsqPz2_le hγ hΨ j hj z hz θ hθ
    · intro j r hr hrj z hz θ hθ
      exact vig_zsqPz2_le hγ hΨ j r hr hrj z hz θ hθ
  · -- conjunct 2: `∂_θ² Ψ`
    refine HkMem_seven_of_grid hα hγ hG (SmoothOpen_pthIter_classC hΨ 2) ?_ ?_
    · intro j hj z hz θ hθ
      exact HkIntegrand_zero_DzIter_pthIter_two_le hγ hΨ j hj z hz θ hθ
    · intro j r hr hrj z hz θ hθ
      exact pthIter2_vig_le hγ hΨ j r hr hrj z hz θ hθ
  · -- conjunct 3: `z ∂_z ∂_θ² Ψ`
    refine HkMem_seven_of_grid hα hγ hG ((SmoothOpen_pthIter_classC hΨ 2).Dz) ?_ ?_
    · intro j hj z hz θ hθ
      exact HkIntegrand_zero_DzIter_Dz_pthIter_two_le hγ hΨ j hj z hz θ hθ
    · intro j r hr hrj z hz θ hθ
      exact vig_Dz_pthIter_two_le hγ hΨ j r hr hrj z hz θ hθ

end Work.FTS.ClassC
