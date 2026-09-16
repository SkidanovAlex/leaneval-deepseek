import Submission.ZagierHoffmanProof.Step8TpAssemble
import Submission.Commons.LinearAlgebra.Dimension.linearIndependent_of_span_eq_top_of_ncard_eq_rank

/-!
# `𝒯_w` is a `K`-basis of `𝒵_w` from the rank equality (Dac's Theorem D, bookkeeping)

Dac's Theorem D for `w ≤ 2q-2` has two halves: the dimension formula `dim_K 𝒵_w = d(w)`
(`Step8TpAssemble.rank_eq_d_of_TwRowFalse`, i.e. Theorem A + the `𝒯'`-independence) and the
statement that the *Hoffman* set `𝒯_w` is a `K`-basis.  The second half is pure linear algebra
given three inputs, all of which are already in the build:

* `𝒯_w` spans `𝒵_w` (`StepL193.theoremA_span_amb`, i.e. Theorem A, already proved);
* `|𝒯_w| = d(w)` (`DegCountAnyF.ncard_T_eq_d`);
* `dim_K 𝒵_w = d(w)`.

The passage is `Commons.LinearAlgebra.Dimension.linearIndependent_of_span_eq_top_of_ncard_eq_rank`,
applied to the submodule `𝒵_w` and the image of `𝒯_w` inside it; the only bookkeeping needed is the
`ncard` of that image (a bijection with `𝒯_w`).  This module performs it, so that `theorem_D`
becomes exactly `rank_eq_d_of_TwRowFalse` plus this lemma.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
open Polynomial
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

universe u

variable {F : Type u} [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★★ **The Hoffman set is `K`-independent as soon as `dim_K 𝒵_w = d(w)`.**  Note that this needs
*no* hypothesis beyond the rank equality: the spanning statement is Theorem A (`theoremA_span_amb`)
and `|𝒯_w| = d(w)` is `ncard_T_eq_d`. -/
theorem linearIndependent_T_of_rank_eq_d {w : ℕ} (hw : 1 ≤ w)
    (hrank : Module.rank (RatFunc F) (𝒵 F w) = (d F w : Cardinal)) :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯 F w → RatFunc.CompletionAtInfty F) := by
  classical
  haveI : Fintype (𝒯 F w) := (T_finite F w hw).fintype
  -- the image of `𝒯 F w` inside the submodule `𝒵 F w`
  let g : 𝒯 F w → 𝒵 F w := fun x => ⟨x.1, 𝒯_subset_𝒵 F w x.2⟩
  have hg : Function.Injective g := fun a b hab =>
    Subtype.ext (congrArg (fun z : 𝒵 F w => (z : RatFunc.CompletionAtInfty F)) hab)
  have hrange : Submodule.subtype (𝒵 F w) '' Set.range g
      = (𝒯 F w : Set (RatFunc.CompletionAtInfty F)) := by
    ext y; constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact x.2
    · intro hy
      exact ⟨(⟨y, 𝒯_subset_𝒵 F w hy⟩ : 𝒵 F w), ⟨(⟨y, hy⟩ : 𝒯 F w), rfl⟩, rfl⟩
  -- the image spans `𝒵_w`
  have hkey : Submodule.map (Submodule.subtype (𝒵 F w))
      (Submodule.span (RatFunc F) (Set.range g)) = 𝒵 F w := by
    rw [Submodule.map_span, hrange, ← theoremA_span_amb F w (by omega)]
  have hspan : Submodule.span (RatFunc F) (Set.range g) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro v
    have hmem : (v : RatFunc.CompletionAtInfty F)
        ∈ Submodule.map (Submodule.subtype (𝒵 F w))
            (Submodule.span (RatFunc F) (Set.range g)) := by
      rw [hkey]; exact v.2
    obtain ⟨x, hx, hxv⟩ := Submodule.mem_map.mp hmem
    have hxv' : x = v := Subtype.ext hxv
    rwa [hxv'] at hx
  have hfin : (Set.range g).Finite := by
    rw [← Set.image_univ]
    exact Set.finite_univ.image g
  -- and has exactly `d(w)` elements
  have hncard : (Set.range g).ncard = d F w := by
    rw [← ncard_T_eq_d F w hw]
    refine Set.ncard_congr
      (fun (a : 𝒵 F w) (_ : a ∈ Set.range g) => (a : RatFunc.CompletionAtInfty F)) ?_ ?_ ?_
    · intro a ha; obtain ⟨x, rfl⟩ := ha; exact x.2
    · intro a₁ a₂ _ _ hab; exact Subtype.ext hab
    · intro b hb; exact ⟨g ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, rfl⟩
  have hrank' : Module.rank (RatFunc F) (𝒵 F w) = ((Set.range g).ncard : Cardinal) := by
    rw [hncard, hrank]
  have hvli := Commons.LinearAlgebra.Dimension.linearIndependent_of_span_eq_top_of_ncard_eq_rank
    (K := RatFunc F) (V := 𝒵 F w) (s := Set.range g) hfin hspan hrank'
  -- transport back to `𝒯_w`
  have hli : LinearIndependent (RatFunc F) g :=
    hvli.comp (fun x : 𝒯 F w => (⟨g x, ⟨x, rfl⟩⟩ : Set.range g))
      (fun a b hab => hg (Subtype.ext_iff.mp hab))
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc x
  refine hli c ?_ x
  refine Subtype.ext ?_
  simpa [g] using hc

/-- ★★★★ **Dac's Theorem D in the exact form of the challenge statement, from the row
obstruction**: for `1 ≤ w ≤ 2q-2`, `𝒯_w` is a `K`-basis of `𝒵_w` whenever the two-term endgame
`TwRowFalse` holds at every weight `q < w' ≤ 2q-2`.

The hypothesis is stated at `q < w'` on purpose: at `w' ≤ q` the independence is
`TupleIndP.tupleIndP_of_le` (Theorem B), and `TwoTermIndP q` is *false* in general (over `F₂`,
`𝒵_2` is one-dimensional). -/
theorem theorem_D_of_TwRowFalse {w : ℕ} (hw1 : 1 ≤ w) (hw2 : w ≤ 2 * Nat.card F - 2)
    (hrow : ∀ w' : ℕ, Nat.card F < w' → w' ≤ 2 * Nat.card F - 2 → TwRowFalse F w') :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯 F w → RatFunc.CompletionAtInfty F) ∧
    Module.rank (RatFunc F) (𝒵 F w) = (d F w : Cardinal) :=
  ⟨linearIndependent_T_of_rank_eq_d (F := F) hw1
      (rank_eq_d_of_TwRowFalse (F := F) hw1 hw2 hrow),
    rank_eq_d_of_TwRowFalse (F := F) hw1 hw2 hrow⟩

end ZagierHoffmanPositiveChar
