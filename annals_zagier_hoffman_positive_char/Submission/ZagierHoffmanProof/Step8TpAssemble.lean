import Submission.ZagierHoffmanProof.Step7Endgame
import Submission.ZagierHoffmanProof.TpCount
import Submission.ZagierHoffmanProof.ZetaShuffle

/-!
# The `𝒯'`-assembly: `d(w) ≤ dim_K 𝒵_w` from the two-term endgame

Dac's Theorem 6.2 gives the `K`-independence of the family
`𝒯'_w = {ζ_A 𝔰 : q ∤ s_i, Σ s_i = w}` for `w ≤ 2q-2`, and `|𝒯'_w| = d(w)`
(`TpCount.card_TpType`).  Together with Theorem A (`rank 𝒵_w ≤ d(w)`) this pins down
`rank 𝒵_w = d(w)` and hence makes the Hoffmann set `𝒯_w` a `K`-basis of `𝒵_w` (Theorem D).

This module performs that assembly.  The only input is the two-term endgame
(`Step7Endgame.TwoTermIndP`, equivalently `Step7Endgame.TwRowFalse`), so it is stated
conditionally.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open Polynomial Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

universe u

variable {F : Type u} [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The exponent tuple of a `q ∤`-tuple -/

/-- The exponent tuple encoded by an element of `TpType F w` (the type of `q ∤`-tuples of weight
`w`, in the shape of the commons counting lemmas). -/
noncomputable def TpTuple (w : ℕ) (x : TpType F w) : Σ r : ℕ, Fin r → ℕ+ :=
  ⟨(x.1.1 : ℕ), fun j => ⟨((x.1.2 j : Fin (2 * Nat.card F)) : ℕ), x.2.1 j⟩⟩

lemma TpTuple_weight (w : ℕ) (x : TpType F w) :
    ∑ j : Fin (TpTuple w x).1, ((TpTuple w x).2 j : ℕ) = w :=
  x.2.2.2

lemma TpTuple_nd (w : ℕ) (x : TpType F w) (j : Fin (TpTuple w x).1) :
    ¬ Nat.card F ∣ ((TpTuple w x).2 j : ℕ) :=
  x.2.2.1 j

/-- ★ The exponent tuple is injective on `TpType F w` — the `hlinj` hypothesis of `TupleIndP`. -/
lemma TpTuple_tupleListHP_injective (w : ℕ) (x y : TpType F w)
    (h : tupleListHP F (TpTuple w x).2 = tupleListHP F (TpTuple w y).2) : x = y := by
  obtain ⟨⟨rx, xs⟩, hx⟩ := x
  obtain ⟨⟨ry, ys⟩, hy⟩ := y
  simp only [TpTuple] at h ⊢
  have hmap : List.ofFn (fun j : Fin (rx : ℕ) => ((xs j : Fin (2 * Nat.card F)) : ℕ))
      = List.ofFn (fun j : Fin (ry : ℕ) => ((ys j : Fin (2 * Nat.card F)) : ℕ)) := by
    have h1 := congrArg (List.map Prod.fst) h
    simpa [tupleListHP, List.map_ofFn, Function.comp_def] using h1
  have hlen : (rx : ℕ) = (ry : ℕ) := by
    have h2 := congrArg List.length hmap
    simpa using h2
  have hrf : rx = ry := Fin.ext hlen
  subst hrf
  have hxs : xs = ys := by
    funext j
    exact Fin.ext (congrFun (List.ofFn_inj.mp hmap) j)
  subst hxs
  rfl

/-! ## §2. The `𝒯'`-independence and the rank lower bound -/

/-- ★★★ **`𝒯'_w` is `K`-independent** (Dac's Theorem 6.2, from the two-term endgame): the MZV's of
the `q ∤`-tuples of weight `w ≤ 2q-2` are `RatFunc F`-linearly independent. -/
theorem tp_independent {w : ℕ} (hw1 : 1 ≤ w) (hw2 : w ≤ 2 * Nat.card F - 2)
    (h : ∀ w' : ℕ, Nat.card F < w' → w' ≤ 2 * Nat.card F - 2 → TwoTermIndP (F := F) w') :
    LinearIndependent (RatFunc F)
      (fun x : ULift.{u, 0} (TpType F w) => ζ_A F ((TpTuple w x.down).2)) := by
  classical
  haveI : Fintype (ULift.{u, 0} (TpType F w)) := Fintype.ofFinite _
  exact (tupleIndP_of_twoTerm (F := F) w hw1 hw2 h (ULift.{u, 0} (TpType F w)))
    (fun x => TpTuple w x.down) (fun x => TpTuple_nd w x.down)
    (fun x => TpTuple_weight w x.down)
    (fun x y hxy => congrArg ULift.up (TpTuple_tupleListHP_injective w x.down y.down hxy))

/-- ★★★ **`d(w) ≤ dim_K 𝒵_w`** — the "in particular" of Theorem D, from the two-term endgame and
`TpCount.card_TpType`. -/
theorem rank_ge_d {w : ℕ} (hw1 : 1 ≤ w) (hw2 : w ≤ 2 * Nat.card F - 2)
    (h : ∀ w' : ℕ, Nat.card F < w' → w' ≤ 2 * Nat.card F - 2 → TwoTermIndP (F := F) w') :
    (d F w : Cardinal) ≤ Module.rank (RatFunc F) (𝒵 F w) := by
  classical
  haveI : Fintype (TpType F w) := Fintype.ofFinite _
  have hli := tp_independent (F := F) hw1 hw2 h
  have hliZU : LinearIndependent (RatFunc F)
      (fun x : ULift.{u, 0} (TpType F w) =>
        (⟨ζ_A F ((TpTuple w x.down).2),
          zeta_mem_Z F ((TpTuple w x.down).2) (TpTuple_weight w x.down)⟩ : 𝒵 F w)) :=
    hli.of_comp (Submodule.subtype (𝒵 F w))
  haveI : Fintype (ULift.{u, 0} (TpType F w)) := Fintype.ofFinite _
  calc (d F w : Cardinal)
      = (Nat.card (TpType F w) : Cardinal) := by rw [card_TpType F w hw1 hw2]
    _ = (Fintype.card (TpType F w) : Cardinal) := by rw [Nat.card_eq_fintype_card]
    _ = (Fintype.card (ULift.{u, 0} (TpType F w)) : Cardinal) := by
        congr 1
        exact (Fintype.card_congr Equiv.ulift).symm
    _ = Cardinal.mk (ULift.{u, 0} (TpType F w)) := by rw [Cardinal.mk_fintype]
    _ ≤ Module.rank (RatFunc F) (𝒵 F w) := hliZU.cardinal_le_rank

/-- ★★★ **`dim_K 𝒵_w = d(w)` for `w ≤ 2q-2`** (Dac's Theorem D, dimension form), from the row
obstruction: Theorem A gives `≤` and `rank_ge_d` gives `≥`. -/
theorem rank_eq_d_of_TwRowFalse {w : ℕ} (hw1 : 1 ≤ w) (hw2 : w ≤ 2 * Nat.card F - 2)
    (hrow : ∀ w' : ℕ, Nat.card F < w' → w' ≤ 2 * Nat.card F - 2 → TwRowFalse F w') :
    Module.rank (RatFunc F) (𝒵 F w) = (d F w : Cardinal) :=
  le_antisymm (theorem_A_amb F ⟨w, hw1⟩).2
    (rank_ge_d (F := F) hw1 hw2 (twoTermIndP_of_rowFalse (F := F) hrow))

/-- The same, directly from `TwoTermIndP`. -/
theorem rank_eq_d_of_twoTermIndP {w : ℕ} (hw1 : 1 ≤ w) (hw2 : w ≤ 2 * Nat.card F - 2)
    (h : ∀ w' : ℕ, Nat.card F < w' → w' ≤ 2 * Nat.card F - 2 → TwoTermIndP (F := F) w') :
    Module.rank (RatFunc F) (𝒵 F w) = (d F w : Cardinal) :=
  le_antisymm (theorem_A_amb F ⟨w, hw1⟩).2 (rank_ge_d (F := F) hw1 hw2 h)

end ZagierHoffmanPositiveChar
