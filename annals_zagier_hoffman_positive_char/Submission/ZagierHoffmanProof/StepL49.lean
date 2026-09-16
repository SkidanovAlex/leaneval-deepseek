import Submission.ZagierHoffmanProof.StepL48
import Submission.ZagierHoffmanProof.StepL36

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L49: AdmExpT — the strengthened (H'_k) expansion with prefix-orders

`AdmExpT F w k s` is the (H'_k) conclusion at a concrete tuple: `ζ_A s` is a finite
`K`-linear combination of `ζ_A(c)`'s with `c` `k`-admissible of weight `w`, and each
`c` additionally satisfies the prefix-order `psum c ℓ ≤ psum s ℓ` for every
`ℓ ≥ k` (the per-member orders of StepL47/48 for CASE-1, automatic for CASE-2).
This is the strengthened inductive invariant the Prop-3.2 recursion needs: when
`AdmExpT (k−1)` is applied to a level-`k` member `t`, its outputs `d` inherit
`psum d ℓ ≤ psum t ℓ` for `ℓ ≥ k−1` — in particular `ℓ = k` control on `prefix-k(d)`.
Infrastructure (mirrors StepL36's AdmExp): the trivial self-expansion, the splice
combinator (`admExpT_combine`, with per-output order transitivity through the
per-member orders), and the forgetful map to the bare `AdmExp` (the theorem-A
consumption).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ (H'_k) at a concrete tuple: expansion into `k`-admissible weight-`w` outputs
each prefix-`≤ s` at every position `ℓ ≥ k`. -/
def AdmExpT (w k : ℕ) {r : ℕ} (s : Fin r → ℕ+) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (dep : ι → ℕ) (hdep : ∀ i : ι, 0 < dep i)
    (c : ∀ i : ι, Fin (dep i) → ℕ+) (a : ι → RatFunc F),
    (∀ i : ι, weight (dep i) (c i) = w) ∧
    (∀ i : ι, kAdmissible (Nat.card F) (c i) k) ∧
    (∀ i : ι, ∀ ℓ : ℕ, k ≤ ℓ → psum (c i) ℓ ≤ psum s ℓ) ∧
    ζ_A F s = ∑ i : ι, ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (c i)

/-- A `k`-admissible weight-`w` tuple is trivially its own strengthened expansion. -/
lemma admExpT_self (w k : ℕ) {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hadm : kAdmissible (Nat.card F) s k) : AdmExpT F w k s := by
  classical
  refine ⟨PUnit, inferInstance, fun _ => r, fun _ => hr, fun _ => s, fun _ => 1,
    ?_, ?_, ?_, ?_⟩
  · intro i
    exact hw
  · intro i
    exact hadm
  · intro i ℓ hkℓ
    exact le_rfl
  · simp [completion_coe_one]

/-- Forget the prefix-orders: `AdmExpT` is an `AdmExp`. -/
lemma admExpT_to_AdmExp (w k : ℕ) {r : ℕ} (s : Fin r → ℕ+) (h : AdmExpT F w k s) :
    AdmExp F w k s := by
  classical
  rcases h with ⟨ι, finι, dep, hdep, c, a, hw, hadm, horder, hid⟩
  refine ⟨ι, finι, dep, hdep, c, a, hw, hadm, hid⟩

/-- ★ Splice strengthened expansions of the outputs of an identity into an expansion
of the input, carrying the prefix-orders through the per-output orders `horder`. -/
lemma admExpT_combine (w k : ℕ) {r : ℕ} (s : Fin r → ℕ+)
    {ι : Type} [Fintype ι] (dep : ι → ℕ) (hdep : ∀ i : ι, 0 < dep i)
    (c : ∀ i : ι, Fin (dep i) → ℕ+) (a : ι → RatFunc F)
    (hid : ζ_A F s = ∑ i : ι, ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (c i))
    (horder : ∀ i : ι, ∀ ℓ : ℕ, k ≤ ℓ → psum (c i) ℓ ≤ psum s ℓ)
    (e : ∀ i : ι, AdmExpT F w k (c i)) :
    AdmExpT F w k s := by
  classical
  choose ι' fin' dep' hdep' c' a' hw' hadm' horder' hid' using e
  let κ : ι → Type := ι'
  letI : ∀ i : ι, Fintype (κ i) := fun i => fin' i
  refine ⟨Σ i : ι, κ i, inferInstance,
    fun p => dep' p.1 p.2, fun p => hdep' p.1 p.2,
    fun p => c' p.1 p.2,
    fun p => a p.1 * a' p.1 p.2, ?_, ?_, ?_, ?_⟩
  · intro p
    exact hw' p.1 p.2
  · intro p
    exact hadm' p.1 p.2
  · intro p ℓ hkℓ
    -- psum (c' p.1 p.2) ℓ ≤ psum (c p.1) ℓ ≤ psum s ℓ
    exact le_trans (horder' p.1 p.2 ℓ hkℓ) (horder p.1 ℓ hkℓ)
  · calc
      ζ_A F s = ∑ i : ι, ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (c i) := hid
      _ = ∑ i : ι, ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) *
            (∑ j : κ i, ((a' i j : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (c' i j)) := by
            apply Finset.sum_congr rfl
            intro i hi
            congr 1
            exact hid' i
      _ = ∑ i : ι, ∑ j : κ i,
            (((a i : RatFunc F) * a' i j : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (c' i j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            have hcast : (((a i : RatFunc F) * a' i j : RatFunc F) : RatFunc.CompletionAtInfty F) =
                ((a i : RatFunc F) : RatFunc.CompletionAtInfty F) *
                  ((a' i j : RatFunc F) : RatFunc.CompletionAtInfty F) := by
              change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (a i * a' i j)) =
                (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (a i)) *
                  (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (a' i j))
              rw [map_mul]
            rw [hcast]
            ring
      _ = ∑ p : Σ i : ι, κ i,
            (((a p.1 : RatFunc F) * a' p.1 p.2 : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (c' p.1 p.2) := by
            exact (Fintype.sum_sigma (f := fun p : Σ i : ι, κ i =>
              (((a p.1 : RatFunc F) * a' p.1 p.2 : RatFunc F) : RatFunc.CompletionAtInfty F) *
                ζ_A F (c' p.1 p.2))).symm

end ZagierHoffmanPositiveChar
