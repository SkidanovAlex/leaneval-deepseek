import Submission.ZagierHoffmanProof.StepL139
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L140: ★ `maink_g5_aSide_weight` — the G5 a-side weight (b) (SESSION 259j)

The symbolic-count version of `g5c1_aSide_weight` (StepL78), with the two
template changes the SESSION 259i caveat predicted:
  • the statement quantifies over `i : D.ιA` and excludes the `iterIdx` image of
    `u` (NOT over `R0.ιA` — the symbolic-ιA elaboration trap);
  • the count-1 template's `dsimp …; rfl` facts are replaced by the transport
    `i₀ := Eq.mpr (BCqIter_ιA …).symm i` (with `iterIdx … i₀ = i` by
    `eq_mpr_symm_id`) and the ITERATED-weight lemma `RelData.BCqIter_cA_weight`
    (`weight (D.cA (iterIdx i₀)) = n·q + weight (R0.cA i₀)`), which was already
    in the library;
  • the arithmetic is banked: `maink_g5_psum_front` + `psum_self s` + `omega`.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The G5 a-side a-members have weight `weight r s`. -/
theorem maink_g5_aSide_weight (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hwtA : ∀ i : R0.ιA, i ≠ u →
      weight (R0.depA i) (R0.cA i) = psum s r - psum s (k - 1)) :
    let D := RelData.BCqIter F (k - 1) (toData F R0)
    ∀ i : D.ιA, i ≠ RelData.iterIdx F (k - 1) (toData F R0) u →
      weight (D.depA i) (D.cA i) = weight r s := by
  classical
  intro D i hi
  let i₀ : R0.ιA := Eq.mpr (RelData.BCqIter_ιA F (k - 1) (toData F R0)).symm i
  have hiter : RelData.iterIdx F (k - 1) (toData F R0) i₀ = i := by
    dsimp only [RelData.iterIdx, i₀]
    exact eq_mpr_symm_id (RelData.BCqIter_ιA F (k - 1) (toData F R0)) i
  have hw := BCqIter_cA_weight F (k - 1) (toData F R0) i₀
  rw [hiter] at hw
  have hwt' : weight ((toData F R0).depA i₀) ((toData F R0).cA i₀)
      = psum s r - psum s (k - 1) := hwtA i₀ (by intro hc; exact hi (by rw [← hiter, hc]))
  rw [hw, hwt']
  rw [show (k - 1) * Nat.card F = psum s (k - 1) from
    (maink_g5_psum_front F r s k hallq).symm]
  rw [show weight r s = psum s r from (psum_self s).symm]
  have hle : psum s (k - 1) ≤ psum s r := psum_mono s (by omega)
  omega

end ZagierHoffmanPositiveChar
