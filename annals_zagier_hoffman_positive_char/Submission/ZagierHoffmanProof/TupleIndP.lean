import Submission.ZagierHoffmanProof.TheoremB
import Submission.ZagierHoffmanProof.BridgeP2

/-!
# The `𝒯'`-indexed induction statement (Dac's Theorem 6.2)

Dac's Theorem D for `q < w ≤ 2q-2` runs the induction of `TheoremB.lean` on the LARGER family
`𝒯'_w` of MZV's whose entries are not divisible by `q` (ND21 Theorem 6.2), i.e. on the datum of
Anderson–Thakur polynomials `Q_j = H_{s_j} = ambH F s_j`.  This module states the corresponding
induction predicate `TupleIndP` and provides the base case `w ≤ q` by reduction to Theorem B
(there every entry is `< q`, hence `H_s = 1` and `𝒯'_w = 𝒯0_w`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial PowerSeries Finset
open scoped WithZero Topology

universe u

namespace ZagierHoffmanPositiveChar

variable (F : Type u) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The `𝒯'`-indexed induction statement of Dac's Theorem 6.2: for every finite injective family of
exponent tuples of common weight `w` with NO entry divisible by `q`, the MZV's `ζ_A 𝔰` are
`RatFunc F`-independent. -/
def TupleIndP (F : Type u) [Field F] [Finite F] [DecidableEq (RatFunc F)]
    (ι : Type u) (w : ℕ) : Prop :=
  ∀ (𝔰 : ι → Σ r : ℕ, Fin r → ℕ+),
    (∀ i j, ¬ Nat.card F ∣ ((𝔰 i).2 j : ℕ)) →
    (∀ i, ∑ j : Fin (𝔰 i).1, ((𝔰 i).2 j : ℕ) = w) →
    (∀ i j, tupleListHP F ((𝔰 i).2) = tupleListHP F ((𝔰 j).2) → i = j) →
    LinearIndependent (RatFunc F) (fun i => ζ_A F ((𝔰 i).2))

/-- **The base case `w ≤ q` of `TupleIndP`.**  If `Σ s_j = w ≤ q` and `q ∤ s_j`, then every
`s_j ≤ w - 1 < q`, so `H_{s_j} = 1`, `𝒯'`-tuples are `𝒯0`-tuples, and Theorem B applies. -/
theorem tupleIndP_of_le {w : ℕ} (hw1 : 1 ≤ w) (hwq : w ≤ Nat.card F)
    (ι : Type u) [Fintype ι] [DecidableEq ι] : TupleIndP (F := F) ι w := by
  classical
  intro 𝔰 hnd hwt hlinj
  have hlt : ∀ i j, ((𝔰 i).2 j : ℕ) < Nat.card F := by
    intro i j
    have hle : ((𝔰 i).2 j : ℕ) ≤ ∑ j' : Fin (𝔰 i).1, ((𝔰 i).2 j' : ℕ) :=
      Finset.single_le_sum (f := fun j' => ((𝔰 i).2 j' : ℕ))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h1 := hwt i
    have h2 := hnd i j
    have h3 : ((𝔰 i).2 j : ℕ) ≠ Nat.card F := fun h =>
      h2 (by simpa [h] using dvd_refl (Nat.card F))
    omega
  have hHP : ∀ i, tupleListHP F ((𝔰 i).2) = tupleListP F ((𝔰 i).2) := by
    intro i
    simp only [tupleListHP, tupleListP]
    congr 1
    funext j
    simp only [ambH_of_le F (le_of_lt (hlt i j))]
  have hlinj' : ∀ i j, tupleListP F ((𝔰 i).2) = tupleListP F ((𝔰 j).2) → i = j :=
    fun i j h => hlinj i j ((hHP i).trans (h.trans (hHP j).symm))
  exact tuple_independent (F := F) w hw1 ι 𝔰 hlt hwt hlinj'

end ZagierHoffmanPositiveChar
