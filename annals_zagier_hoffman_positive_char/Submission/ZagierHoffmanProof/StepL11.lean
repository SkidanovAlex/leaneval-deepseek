import Submission.ZagierHoffmanProof.StepL10

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L11: ζ_A-reindex bridge (Prop 2.12's (2.11) leading-value identification)

`zeta_reindex_eq` is the equivariance of `ζ_A` under reindexing a tuple along an
equality of depths (`Fin.cast` preserves the order, so the monic-strictly-anti-degree
sums coincide term-by-term).  `zeta_iter_leading` applies it to `iter_leading_tuple`
(StepL10): the ζ_A-value of the leading `a`-output after `n` `BC_q`-steps equals the
ζ_A-value of the `n`-`q`-prepend of the original tuple — the bridge between the
`qsTuple` value identification and the actual ζ_A-value used in Prop 2.12's (2.11).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ ζ_A is invariant under reindexing a tuple along an equality of depths
(`Fin.cast` preserves the order, so the monic-strictly-anti-degree sums match):
`ζ_A(𝔰 ∘ Fin.cast h) = ζ_A(𝔰)` for `h : r = s`. -/
lemma zeta_reindex_eq {r s : ℕ} (h : r = s) (𝔰 : Fin s → ℕ+) :
    ζ_A F (fun i : Fin r => 𝔰 (Fin.cast h i)) = ζ_A F 𝔰 := by
  subst h
  simp



/-- ★ The ζ_A-value of the leading tuple after `n` `BC_q`-steps equals the ζ_A-value
of the `n`-`q`-prepend of the original tuple — the reindex bridge applied to
`iter_leading_tuple`. -/
lemma zeta_iter_leading (n : ℕ) (R : BinaryRel F) (u : R.ιA) :
    ζ_A F ((RelData.BCqIter F n (toData F R)).cA (RelData.iterIdx F n (toData F R) u)) =
      ζ_A F (qsTuple F n (R.depA u) (R.cA u)) := by
  rw [iter_leading_tuple F n R u]
  exact zeta_reindex_eq F (RelData.BCqIter_depA_at F n (toData F R) u)
    (qsTuple F n (R.depA u) (R.cA u))


end ZagierHoffmanPositiveChar
