import Mathlib
import Submission.Work.WilkiesB.Defs

/-!
# Area B — `ExpExistI` is closed under adding an existential block of coordinates

`ExpExistI_existsBlock` says that if `X ⊆ ℝ^{κ ⊕ μ}` is existentially definable in `ℝ_exp`
(for an arbitrary index type of ambient variables, finite witness type), then so is its
projection along the `μ`-block: `{z : κ → ℝ | ∃ u : μ → ℝ, Sum.elim z u ∈ X}`.

The mathematical content is the associativity of the block decomposition of the variables,
together with the fact that the new existential quantifier over the `μ`-block can simply be
merged with the existing witness block `ν` of the defining exp-polynomial.

Because `ExpExistI` stores its witnesses in `Type 0` while the index type `μ` of the statement
is an arbitrary universe, we first reindex `μ` along `e : μ ≃ Fin (Fintype.card μ)`.

Everything else in `Submission/Work/WilkiesB` may import this file.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.WilkiesB

/-- Reindexing the "input" block `μ` along `e : μ ≃ Fin m` and then reassociating the two
existential blocks: `(κ ⊕ μ) ⊕ ν → κ ⊕ (Fin m ⊕ ν)`. -/
def blockReindex {κ μ ν : Type*} {m : ℕ} (e : μ ≃ Fin m) :
    (κ ⊕ μ) ⊕ ν → κ ⊕ (Fin m ⊕ ν) := fun q =>
  match q with
  | Sum.inl (Sum.inl i) => Sum.inl i
  | Sum.inl (Sum.inr a) => Sum.inr (Sum.inl (e a))
  | Sum.inr k => Sum.inr (Sum.inr k)

/-- Naturality of `Sum.elim` under `blockReindex`: an assignment of the reindexed coordinates
`w` for the block `Fin m ⊕ ν` corresponds to the assignment `(w ∘ inl) ∘ e` for the block `μ`
together with `w ∘ inr` for the block `ν`. -/
theorem sumElim_comp_blockReindex {κ μ ν : Type*} {m : ℕ} (e : μ ≃ Fin m)
    (z : κ → ℝ) (w : Fin m ⊕ ν → ℝ) :
    (Sum.elim z w) ∘ blockReindex e =
      Sum.elim (Sum.elim z ((w ∘ Sum.inl) ∘ ⇑e)) (w ∘ Sum.inr) := by
  funext q
  rcases q with (i | a) | k <;> rfl

/-- **Projection along a block of coordinates.**  If `X ⊆ ℝ^{κ ⊕ μ}` is the projection of the
zero set of a single exp-polynomial along a finite witness type, then the same is true of
`{z : κ → ℝ | ∃ u : μ → ℝ, Sum.elim z u ∈ X}`. -/
theorem ExpExistI_existsBlock {κ μ : Type*} [Fintype μ] {X : Set ((κ ⊕ μ) → ℝ)}
    (hX : ExpExistI X) :
    ExpExistI {z : κ → ℝ | ∃ u : μ → ℝ, Sum.elim z u ∈ X} := by
  obtain ⟨ν, hν, P, hP⟩ := hX
  letI : Fintype ν := hν
  let e : μ ≃ Fin (Fintype.card μ) := Fintype.equivFin μ
  -- Witnesses for the projection: the `μ`-block (reindexed to `Fin (card μ)`) merged with the
  -- old witness block `ν`.
  refine ⟨Fin (Fintype.card μ) ⊕ ν, inferInstance,
    MvPolynomial.rename (polyMap (blockReindex e)) P, ?_⟩
  rw [hP]
  ext z
  simp only [Set.mem_ofPred_eq, ExpZero]
  constructor
  · rintro ⟨u, y, hy⟩
    refine ⟨Sum.elim (u ∘ ⇑e.symm) y, ?_⟩
    rw [expEval_rename, sumElim_comp_blockReindex]
    have hee : (Sum.elim (u ∘ ⇑e.symm) y ∘ Sum.inl) ∘ ⇑e = u := by
      funext a; simp
    rw [hee]
    exact hy
  · rintro ⟨w, hw⟩
    refine ⟨(w ∘ Sum.inl) ∘ ⇑e, w ∘ Sum.inr, ?_⟩
    rw [expEval_rename, sumElim_comp_blockReindex] at hw
    exact hw

end Work.WilkiesB
