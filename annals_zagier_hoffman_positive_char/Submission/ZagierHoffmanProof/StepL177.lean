import Submission.ZagierHoffmanProof.StepL176
import Submission.ZagierHoffmanProof.StepL150

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L177: `AdmExpTie` — the TIE-INVARIANT strengthened expansion (route (Γ), the surviving
endgame architecture of PLAN SESSION 271)

The single missing ingredient of the theorem_A span endgame is the paper's ITERATION
invariant: along the tower's refinements, an output `c` that does NOT strictly drop the
prefix sum at the ambient level `Λ` (`psum c Λ = psum input Λ`) must not have a smaller
initial tuple (`initVal input ≤ initVal c`).  This module:
  • defines `AdmExpTie w j Λ s` — an `AdmExpT`-shaped expansion at level `j` carrying
    additionally the tie-invariant at `Λ`
      `∀ i, psum (c i) Λ = psum s Λ → initVal (Nat.card F) w s ≤ initVal (Nat.card F) w (c i)`;
  • `admExpTie_self` — a `j`-admissible tuple is its own tie-invariant expansion;
  • ★ `admExpTie_combine` — the splice: it carries the invariant through a composition
    (the tie at `Λ` propagates: `psum d Λ ≤ psum c Λ ≤ psum s Λ`, so equality at the ends
    forces both equalities, and the two invariants chain);
  • ★★ `Ak_from_Ak1_maink_tie` — the TOWER STEP with the invariant: from the level-`(j−1)`
    invariant statement and the level-`j` in-domain handler (also carrying the invariant),
    every weight-`w` tuple has a level-`j` tie-invariant expansion.
CONSEQUENCE (see PLAN SESSION 271 cont.): combined with the per-chain tie facts
(type-1: `type1_Init`, type-3: `InitLt`, type-2: strict prefix drops at every `ℓ ≥ j`,
so a tie at `Λ ≥ j` is IMPOSSIBLE for a type-2 member) this closes the recursion step that
`MainkStep3` alone cannot order — the CK2′/C3 tie of `PlAN SESSION 271 §4`.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- An expansion at level `j` carrying the ambient-`Λ` TIE INVARIANT: an output that does
not strictly drop the prefix-`Λ` sum has a `initVal` at least the input's. -/
def AdmExpTie (w j Λ : ℕ) {r : ℕ} (s : Fin r → ℕ+) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (dep : ι → ℕ) (hdep : ∀ i : ι, 0 < dep i)
    (c : ∀ i : ι, Fin (dep i) → ℕ+) (a : ι → RatFunc F),
    (∀ i : ι, weight (dep i) (c i) = w) ∧
    (∀ i : ι, kAdmissible (Nat.card F) (c i) j) ∧
    (∀ i : ι, ∀ ℓ : ℕ, j ≤ ℓ → psum (c i) ℓ ≤ psum s ℓ) ∧
    (∀ i : ι, psum (c i) Λ = psum s Λ →
      initVal (Nat.card F) w s ≤ initVal (Nat.card F) w (c i)) ∧
    ζ_A F s = ∑ i : ι, ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (c i)

/-- A `j`-admissible tuple is its own tie-invariant expansion. -/
lemma admExpTie_self (w j Λ : ℕ) {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hadm : kAdmissible (Nat.card F) s j) : AdmExpTie F w j Λ s := by
  classical
  refine ⟨PUnit, inferInstance, fun _ => r, fun _ => hr, fun _ => s, fun _ => 1,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hw
  · intro i
    exact hadm
  · intro i ℓ hkℓ
    exact le_rfl
  · intro i _
    exact le_rfl
  · simp [completion_coe_one]

/-- Forget the tie-invariant. -/
lemma admExpTie_to_admExpT (w j Λ : ℕ) {r : ℕ} (s : Fin r → ℕ+) (h : AdmExpTie F w j Λ s) :
    AdmExpT F w j s := by
  classical
  rcases h with ⟨ι, finι, dep, hdep, c, a, hw, hadm, horder, -, hid⟩
  exact ⟨ι, finι, dep, hdep, c, a, hw, hadm, horder, hid⟩

/-- ★ Splice tie-invariant expansions of the outputs of an identity into one of the input:
the tie-invariant at `Λ` propagates through the two per-output orders at `ℓ = Λ`. -/
lemma admExpTie_combine (w j Λ : ℕ) (hjΛ : j ≤ Λ) {r : ℕ} (s : Fin r → ℕ+)
    {ι : Type} [Fintype ι] (dep : ι → ℕ) (hdep : ∀ i : ι, 0 < dep i)
    (c : ∀ i : ι, Fin (dep i) → ℕ+) (a : ι → RatFunc F)
    (hid : ζ_A F s = ∑ i : ι, ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (c i))
    (horder : ∀ i : ι, ∀ ℓ : ℕ, j ≤ ℓ → psum (c i) ℓ ≤ psum s ℓ)
    (htie : ∀ i : ι, psum (c i) Λ = psum s Λ →
      initVal (Nat.card F) w s ≤ initVal (Nat.card F) w (c i))
    (e : ∀ i : ι, AdmExpTie F w j Λ (c i)) :
    AdmExpTie F w j Λ s := by
  classical
  choose ι' fin' dep' hdep' c' a' hw' hadm' horder' htie' hid' using e
  let κ : ι → Type := ι'
  letI : ∀ i : ι, Fintype (κ i) := fun i => fin' i
  refine ⟨Σ i : ι, κ i, inferInstance,
    fun p => dep' p.1 p.2, fun p => hdep' p.1 p.2,
    fun p => c' p.1 p.2,
    fun p => a p.1 * a' p.1 p.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact hw' p.1 p.2
  · intro p
    exact hadm' p.1 p.2
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

/-- ★★ The TOWER STEP with the tie-invariant: from the level-`(j−1)` tie-invariant statement
and the level-`j` in-domain handler (also tie-invariant), every weight-`w` tuple has a level-`j`
tie-invariant expansion.  (Same proof as `Ak_from_Ak1_maink`, with `htie` carried through the
per-output composition.) -/
theorem Ak_from_Ak1_maink_tie (w : ℕ) (hw0 : 0 < w) (Λ : ℕ) (j : ℕ) (hj1 : 1 ≤ j) (hjΛ : j ≤ Λ)
    (Ak1 : ∀ (r : ℕ) (s : Fin r → ℕ+), weight r s = w → AdmExpTie F w (j - 1) Λ s)
    (maink : ∀ (r : ℕ) (s : Fin r → ℕ+), weight r s = w →
      kAdmissible (Nat.card F) s (j - 1) → ¬ kAdmissible (Nat.card F) s j →
      AdmExpTie F w j Λ s) :
    ∀ (r : ℕ) (s : Fin r → ℕ+), weight r s = w → AdmExpTie F w j Λ s := by
  classical
  intro r s hw
  by_cases hk : kAdmissible (Nat.card F) s j
  · have hr : 0 < r := weight_pos_hr s hw hw0
    exact admExpTie_self F w j Λ hr s hw hk
  · by_cases hk1 : kAdmissible (Nat.card F) s (j - 1)
    · exact maink r s hw hk1 hk
    · -- refine the level-`(j−1)` expansion
      rcases Ak1 r s hw with ⟨ι, finι, dep, hdep, c, a, hw', hadm1, horder1, htie1, hid⟩
      letI : Fintype ι := finι
      refine admExpTie_combine F w j Λ hjΛ s dep hdep c a hid ?_ ?_ ?_
      · intro i ℓ hℓ
        exact horder1 i ℓ (by omega)
      · intro i hci
        exact htie1 i hci
      · intro i
        by_cases hki : kAdmissible (Nat.card F) (c i) j
        · have hdi : 0 < dep i := hdep i
          exact admExpTie_self F w j Λ hdi (c i) (hw' i) hki
        · exact maink (dep i) (c i) (hw' i) (hadm1 i) hki

end ZagierHoffmanPositiveChar
