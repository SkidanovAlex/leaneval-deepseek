import Mathlib
import Submission.Work.WilC5.ExtSatAux

noncomputable section
open Classical

namespace Work.WilC5

open FirstOrder Language

/-- **The inverse of a surjective partial elementary map is an elementary embedding.**

If `τ : B → M` (`B ⊆ N`) is elementary and surjective onto `M`, then choosing for every `m ∈ M`
a preimage `pre m ∈ B` and putting `g m := (pre m : N)` gives an *elementary* embedding
`g : M ↪ₑ[L] N` which is a right inverse of `τ` (hence, by injectivity of `τ`, the inverse of `τ`).

Elementarity of `g` is exactly elementarity of `τ` applied to the relabelled formulas: for a
formula `φ` with free variables indexed by `Fin n` and `x : Fin n → M`, the formula
`φ.relabel (fun i => pre (x i))`, with free variables indexed by `B`, has parameters from `B`;
realizing it with the inclusion `B ↪ N` evaluates `φ` at `g ∘ x`, and realizing it with `τ`
evaluates `φ` at `x`. -/
theorem emb_of_surj_elemOn {L : FirstOrder.Language.{0, 0}} {M N : Type} [L.Structure M]
    [L.Structure N] {B : Set N} {τ : B → M}
    (h : @Work.WilC5.ElemOn L M N _ _ B τ) (hsurj : ∀ m : M, ∃ b : B, τ b = m) :
    ∃ g : FirstOrder.Language.ElementaryEmbedding L M N,
      ∀ m : M, ∃ hh : ((g m : N) ∈ B), τ ⟨(g m : N), hh⟩ = m := by
  classical
  choose pre hpre using hsurj
  let g : M → N := fun m => (pre m : N)
  refine ⟨⟨g, ?_⟩, ?_⟩
  · intro n φ x
    -- elementarity of `τ` applied to the relabelled formula
    have key := h (φ.relabel (fun i : Fin n => pre (x i)))
    rw [Formula.realize_relabel, Formula.realize_relabel] at key
    -- the two realizations are the ones of `g ∘ x` and of `x`
    have e1 : φ.Realize ((Subtype.val : B → N) ∘ (fun i : Fin n => pre (x i))) ↔
        φ.Realize (g ∘ x) :=
      iff_of_eq (congrArg (fun v : Fin n → N => φ.Realize v) (by funext i; rfl))
    have e2 : φ.Realize (τ ∘ (fun i : Fin n => pre (x i))) ↔ φ.Realize x :=
      iff_of_eq (congrArg (fun v : Fin n → M => φ.Realize v) (by funext i; exact hpre (x i)))
    exact e1.symm.trans (key.trans e2)
  · intro m
    exact ⟨(pre m).2, hpre m⟩

end Work.WilC5
