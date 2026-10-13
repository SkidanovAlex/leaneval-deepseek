/-
# `FTS/PhiStar/Honesty/SlotsLimit/IBP_subSlot`

Integration by parts for the sub-slot operators `subSlot r j i = D_z^j D_θ^i ∘ slot_r` on the open
quadrant `Q0 = (0,∞) × (0,π/2)`.

The infrastructure lives in the sibling modules

* `Submission/Work/FTS/PhiStar/Honesty/SlotsLimit/IBPsub/Closure.lean` — closure of the class
  `TestQ0` of test functions (globally `C^∞`, compactly supported, support strictly inside `Q0`)
  under `∂_z`, `∂_θ`, multiplication by a globally `C^∞` factor, and hence under the transposes
  `DzStar`, `DthStar` and their iterates;
* `.../IBPsub/Master.lean` — the master integral lemma (`∫_{ℝ²} ∂_z F = 0` and `∫_{ℝ²} ∂_θ F = 0`
  for `F` of class `C¹` with compact support, by Fubini and the one-dimensional fundamental
  theorem of calculus) and the plain integration-by-parts identities derived from it;
* `.../IBPsub/Iterate.lean` — the iterated identities and the mixed transposition
  `∫ mixed j i g · φ = ∫ g · mixedStar j i φ`;
* `.../IBPsub/Slots.lean` — the transposes of the three slots `z²∂_z²`, `∂_θ²` and `D_z ∂_θ²`.

Here the pieces are assembled: the integral over the open quadrant is identified with the integral
over `ℝ²` (every integrand vanishes outside `Q0`), the mixed transposition is applied first, and
the slot transpositions afterwards.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.IBPsub.Slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

set_option autoImplicit false
set_option maxHeartbeats 2000000

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-- **Integration by parts for the sub-slot operators.**  For `f` smooth on the open quadrant and `φ` a test function on `Q0`, the formal transpose `subSlotStar r j i` moves `subSlot r j i = D_z^j D_θ^i ∘ slot_r` off `f` and onto `φ`, and the transposed test function is again a test function.  (This is the composition of `IBP_mixed` with the elementary identity `∫ (z² ∂_z² f) φ = ∫ f (∂_z² (z² φ))` for the first slot, two-dimensional integration by parts for `∂_θ²` for the second, and their combination with `D_z = z ∂_z` for the third.) -/
theorem IBP_subSlot (r j i : ℕ) {f φ : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hφ : TestQ0 φ) :
    TestQ0 (subSlotStar r j i φ) ∧
      (∫ p in Work.FTS.EllipticEst.Q0,
          subSlot r j i f p.1 p.2 * φ p.1 p.2
        = ∫ p in Work.FTS.EllipticEst.Q0,
          f p.1 p.2 * subSlotStar r j i φ p.1 p.2) := by
  have hmix : TestQ0 (mixedStar j i φ) := testQ0_mixedStar hφ j i
  have hstar : TestQ0 (subSlotStar r j i φ) := by
    rcases r with _ | _ | r
    · exact testQ0_slot1Star hmix
    · exact testQ0_slot2Star hmix
    · exact testQ0_slot3Star hmix
  refine ⟨hstar, ?_⟩
  have hL : ∫ p in Q0, subSlot r j i f p.1 p.2 * φ p.1 p.2
      = ∫ p : ℝ × ℝ, Work.Spaces.mixed j i (slot r f) p.1 p.2 * φ p.1 p.2 := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => ?_)
    have hφ0 : φ p.1 p.2 = 0 := by
      by_contra hne
      exact hp (hφ.tsupp (subset_closure (Function.mem_support.mpr hne)))
    rw [hφ0, mul_zero]
  have hR : ∫ p in Q0, f p.1 p.2 * subSlotStar r j i φ p.1 p.2
      = ∫ p : ℝ × ℝ, f p.1 p.2 * subSlotStar r j i φ p.1 p.2 := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => ?_)
    have h0 : subSlotStar r j i φ p.1 p.2 = 0 := by
      by_contra hne
      exact hp (hstar.tsupp (subset_closure (Function.mem_support.mpr hne)))
    rw [h0, mul_zero]
  rw [hL, hR]
  exact integral_mixed_subSlot r j i hf hφ

end Work.FTS.PhiStar.Honesty.SlotsLimit
