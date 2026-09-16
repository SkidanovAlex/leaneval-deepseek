import Submission.ZagierHoffmanProof.StepL182

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L183: `AdmExpTieD` — the DEPTH-INVARIANT-carrying expansion, its splice and its tower

StepL181 showed that `ambNu` is THE recursion measure, and that the chain members descend under
it as soon as `depth input ≤ depth member` (the committed `*_dep_ge` facts).  StepL182 closed the
one base case of the DEPTH-INVARIANT OF EXPANSIONS (the level-1 base's `(1 :: cb j)` members,
plus the paper's general Remark `dep_ge_of_weight_eq_of_psum_le`).  This module packages the
invariant as a predicate and carries it through the splice and the tower:
  • `AdmExpTieD w j Λ s` — `AdmExpTie`'s data plus `∀ i, depth s ≤ dep i` (every output is at
    least as deep as the input);
  • `admExpTieD_self` (equal depths); `admExpTieD_to_admExpTie`;
  • ★★ `admExpTieD_combine` — the splice: the composite's depths are the sub-expansions' depths,
    so the member depth bounds (`hdep`) and the sub-expansions' invariances compose;
  • ★★ `Ak_from_Ak1_maink_tieD` — the TOWER STEP with the invariant (the same proof as
    StepL177's `Ak_from_Ak1_maink_tie`, with the depth bound transported: the `self`-dispatch
    inherits the parent's bound `r ≤ dep (c i)`, the recursive dispatch uses the sub-invariant).
CONSEQUENCE: the recursion of PLAN SESSION 272 can now run on `ambNu` with the
invariant-carrying handler, and case (b) is dispatched by StepL181's
`ambNu_lt_of_mainkStep3_of_dep_le` (chain members) and by the depth component of `ambNu` for the
tower outputs — the residual being only the equal-depth saturation sub-case.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- An expansion at level `j` carrying the ambient-`Λ` tie invariant AND the DEPTH INVARIANT
(every output is at least as deep as the input). -/
def AdmExpTieD (w j Λ : ℕ) {r : ℕ} (s : Fin r → ℕ+) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (dep : ι → ℕ) (hdep : ∀ i : ι, 0 < dep i)
    (c : ∀ i : ι, Fin (dep i) → ℕ+) (a : ι → RatFunc F),
    (∀ i : ι, weight (dep i) (c i) = w) ∧
    (∀ i : ι, kAdmissible (Nat.card F) (c i) j) ∧
    (∀ i : ι, r ≤ dep i) ∧
    (∀ i : ι, ∀ ℓ : ℕ, j ≤ ℓ → psum (c i) ℓ ≤ psum s ℓ) ∧
    (∀ i : ι, psum (c i) Λ = psum s Λ →
      initVal (Nat.card F) w s ≤ initVal (Nat.card F) w (c i)) ∧
    ζ_A F s = ∑ i : ι, ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (c i)

/-- Forget the invariants (down to `AdmExpT`). -/
lemma admExpTieD_to_admExpT (w j Λ : ℕ) {r : ℕ} (s : Fin r → ℕ+) (h : AdmExpTieD F w j Λ s) :
    AdmExpT F w j s := by
  classical
  rcases h with ⟨ι, finι, dep, hdep, c, a, hw, hadm, -, horder, -, hid⟩
  exact ⟨ι, finι, dep, hdep, c, a, hw, hadm, horder, hid⟩

/-- Forget the depth invariant (down to `AdmExpTie`). -/
lemma admExpTieD_to_admExpTie (w j Λ : ℕ) {r : ℕ} (s : Fin r → ℕ+) (h : AdmExpTieD F w j Λ s) :
    AdmExpTie F w j Λ s := by
  classical
  rcases h with ⟨ι, finι, dep, hdep, c, a, hw, hadm, -, horder, htie, hid⟩
  exact ⟨ι, finι, dep, hdep, c, a, hw, hadm, horder, htie, hid⟩

/-- A `j`-admissible tuple is its own depth-invariant expansion. -/
lemma admExpTieD_self (w j Λ : ℕ) {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hadm : kAdmissible (Nat.card F) s j) : AdmExpTieD F w j Λ s := by
  classical
  refine ⟨PUnit, inferInstance, fun _ => r, fun _ => hr, fun _ => s, fun _ => 1,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hw
  · intro i
    exact hadm
  · intro i
    exact le_rfl
  · intro i ℓ hkℓ
    exact le_rfl
  · intro i _
    exact le_rfl
  · simp [completion_coe_one]

/-- ★★ Splice: the composite's depths are the sub-expansions' depths, so the member depth bounds
(`hdep`) and the sub-expansions' depth invariances compose. -/
lemma admExpTieD_combine (w j Λ : ℕ) (hjΛ : j ≤ Λ) {r : ℕ} (s : Fin r → ℕ+)
    {ι : Type} [Fintype ι] (dep : ι → ℕ) (hdep : ∀ i : ι, 0 < dep i)
    (c : ∀ i : ι, Fin (dep i) → ℕ+) (a : ι → RatFunc F)
    (hid : ζ_A F s = ∑ i : ι, ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (c i))
    (hdepr : ∀ i : ι, r ≤ dep i)
    (horder : ∀ i : ι, ∀ ℓ : ℕ, j ≤ ℓ → psum (c i) ℓ ≤ psum s ℓ)
    (htie : ∀ i : ι, psum (c i) Λ = psum s Λ →
      initVal (Nat.card F) w s ≤ initVal (Nat.card F) w (c i))
    (e : ∀ i : ι, AdmExpTieD F w j Λ (c i)) :
    AdmExpTieD F w j Λ s := by
  classical
  choose ι' fin' dep' hdep' c' a' hw' hadm' hdepinv' horder' htie' hid' using e
  let κ : ι → Type := ι'
  letI : ∀ i : ι, Fintype (κ i) := fun i => fin' i
  refine ⟨Σ i : ι, κ i, inferInstance,
    fun p => dep' p.1 p.2, fun p => hdep' p.1 p.2,
    fun p => c' p.1 p.2,
    fun p => a p.1 * a' p.1 p.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact hw' p.1 p.2
  · intro p
    exact hadm' p.1 p.2
  · intro p
    exact le_trans (hdepr p.1) (hdepinv' p.1 p.2)
  · intro p ℓ hkℓ
    exact le_trans (horder' p.1 p.2 ℓ hkℓ) (horder p.1 ℓ hkℓ)
  · intro p hp
    have h1 : psum (c' p.1 p.2) Λ ≤ psum (c p.1) Λ := horder' p.1 p.2 Λ hjΛ
    have h2 : psum (c p.1) Λ ≤ psum s Λ := horder p.1 Λ hjΛ
    have h3 : psum (c p.1) Λ = psum s Λ := le_antisymm h2 (by rw [← hp]; exact h1)
    have h4 : psum (c' p.1 p.2) Λ = psum (c p.1) Λ :=
      le_antisymm h1 (by rw [h3]; exact le_of_eq hp.symm)
    exact le_trans (htie p.1 h3) (htie' p.1 p.2 h4)
  · calc
      ζ_A F s = ∑ i : ι, ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (c i) := hid
      _ = ∑ i : ι, ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) *
            (∑ k : κ i, ((a' i k : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (c' i k)) := by
            apply Finset.sum_congr rfl
            intro i _
            congr 1
            exact hid' i
      _ = ∑ i : ι, ∑ k : κ i,
            (((a i : RatFunc F) * a' i k : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (c' i k) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            have hcast : (((a i : RatFunc F) * a' i k : RatFunc F) :
                RatFunc.CompletionAtInfty F) =
                ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) *
                  ((a' i k : RatFunc F) : RatFunc.CompletionAtInfty F) := by
              change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (a i * a' i k)) =
                (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (a i)) *
                  (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (a' i k))
              rw [map_mul]
            rw [hcast]
            ring
      _ = ∑ p : Σ i : ι, κ i,
            (((a p.1 : RatFunc F) * a' p.1 p.2 : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (c' p.1 p.2) := by
            exact (Fintype.sum_sigma (f := fun p : Σ i : ι, κ i =>
              (((a p.1 : RatFunc F) * a' p.1 p.2 : RatFunc F) : RatFunc.CompletionAtInfty F) *
                ζ_A F (c' p.1 p.2))).symm

/-- ★★ The TOWER STEP with both invariants: from the level-`(j−1)` invariant statement and the
level-`j` in-domain handler (both depth-invariant), every weight-`w` tuple has a level-`j`
depth-and-tie-invariant expansion. -/
theorem Ak_from_Ak1_maink_tieD (w : ℕ) (hw0 : 0 < w) (Λ : ℕ) (j : ℕ) (hj1 : 1 ≤ j) (hjΛ : j ≤ Λ)
    (Ak1 : ∀ (r : ℕ) (s : Fin r → ℕ+), weight r s = w → AdmExpTieD F w (j - 1) Λ s)
    (maink : ∀ (r : ℕ) (s : Fin r → ℕ+), weight r s = w →
      kAdmissible (Nat.card F) s (j - 1) → ¬ kAdmissible (Nat.card F) s j →
      AdmExpTieD F w j Λ s) :
    ∀ (r : ℕ) (s : Fin r → ℕ+), weight r s = w → AdmExpTieD F w j Λ s := by
  classical
  intro r s hw
  by_cases hk : kAdmissible (Nat.card F) s j
  · have hr : 0 < r := weight_pos_hr s hw hw0
    exact admExpTieD_self F w j Λ hr s hw hk
  · by_cases hk1 : kAdmissible (Nat.card F) s (j - 1)
    · exact maink r s hw hk1 hk
    · rcases Ak1 r s hw with ⟨ι, finι, dep, hdep, c, a, hw', hadm1, hdepinv, horder1, htie1, hid⟩
      letI : Fintype ι := finι
      refine admExpTieD_combine F w j Λ hjΛ s dep hdep c a hid hdepinv ?_ ?_ ?_
      · intro i ℓ hℓ
        exact horder1 i ℓ (by omega)
      · intro i hci
        exact htie1 i hci
      · intro i
        by_cases hki : kAdmissible (Nat.card F) (c i) j
        · exact admExpTieD_self F w j Λ (hdep i) (c i) (hw' i) hki
        · exact maink (dep i) (c i) (hw' i) (hadm1 i) hki

end ZagierHoffmanPositiveChar
