import Mathlib
import Submission.Work.FieldTheory.Crossing.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.FieldTheory.Crossing

open scoped Classical

/-- `Equiv.piCongrLeft'` as a `MulEquiv`: reindexing a product along an equivalence of
index types.  It is cast-free because `Equiv.piCongrLeft'` maps `f` to `fun b => f (e.symm b)`. -/
noncomputable def mulEquivPiCongrLeft' {α β : Type*} (M : α → Type*) [∀ a, Mul (M a)]
    (e : α ≃ β) : (∀ a : α, M a) ≃* (∀ b : β, M (e.symm b)) where
  toEquiv := Equiv.piCongrLeft' M e
  map_mul' x y := by funext b; rfl

/-- `Equiv.piOptionEquivProd` as a `MulEquiv`. -/
noncomputable def mulEquivPiOptionEquivProd {α : Type*} (M : Option α → Type*)
    [∀ i, Mul (M i)] :
    (∀ i : Option α, M i) ≃* (M none × ∀ a : α, M (some a)) where
  toEquiv := Equiv.piOptionEquivProd
  map_mul' x y := by ext <;> rfl

/-- Iterating the one-step crossing `H ↦ H × Multiplicative (ZMod m)` over a finite
type-indexed product.  `hstep` is exactly the one-cyclic-factor step
(e.g. `realizableOver_prod_zmod`); this statement is pure group theory and mentions no fields.

Suggested proof: `Fintype.induction_empty_option` on `ι`.
* `PEmpty`: the product is the trivial group; use `Submission.RealizableOver.of_mulEquiv`.
* `Option α`: `Equiv.piOptionEquivProd` identifies `∀ i : Option α, Multiplicative (ZMod (n i))`
  with `Multiplicative (ZMod (n none)) × (∀ a : α, Multiplicative (ZMod (n (some a))))`;
  apply `hstep` to `G` and `n none`, then the induction hypothesis to
  `G × Multiplicative (ZMod (n none))`, and reassociate via `MulEquiv.prodAssoc`.
* `of_equiv` (`e : α ≃ β`): reindex with a `MulEquiv` version of `Equiv.piCongrLeft`. -/
theorem realizableOver_prod_pi (G : Type) [Group G] (ι : Type) [Fintype ι] (n : ι → ℕ)
    (hn : ∀ i, n i ≠ 0)
    (hstep : ∀ (H : Type) [Group H] (m : ℕ), m ≠ 0 →
      Submission.RealizableOver ℚ H → Submission.RealizableOver ℚ (H × Multiplicative (ZMod m)))
    (h : Submission.RealizableOver ℚ G) :
    Submission.RealizableOver ℚ (G × (∀ i, Multiplicative (ZMod (n i)))) := by
  let P : ∀ (α : Type) [Fintype α], Prop := fun α _ =>
    ∀ (G' : Type) [Group G'] (n : α → ℕ), (∀ i, n i ≠ 0) →
      Submission.RealizableOver ℚ G' →
        Submission.RealizableOver ℚ (G' × (∀ i, Multiplicative (ZMod (n i))))
  have key : P ι := by
    refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ ι
    · -- `of_equiv`: reindex the product along `e : α ≃ β`
      intro α β _ e hα G' _ n hn hG
      refine Submission.RealizableOver.of_mulEquiv
        (MulEquiv.prodCongr (MulEquiv.refl G')
          ((mulEquivPiCongrLeft' (fun b : β => Multiplicative (ZMod (n b))) e.symm).symm))
        (hα G' (fun a => n (e a)) (fun a => hn (e a)) hG)
    · -- `PEmpty`: the product over the empty type is trivial
      intro G' _ n _ hG
      exact Submission.RealizableOver.of_mulEquiv
        (MulEquiv.prodUnique (M := G')
          (N := (∀ i : PEmpty, Multiplicative (ZMod (n i))))).symm hG
    · -- `Option α`: peel off the `none` factor using `hstep`
      intro α _ hα G' _ n hn hG
      have h1 : Submission.RealizableOver ℚ (G' × Multiplicative (ZMod (n none))) :=
        hstep G' (n none) (hn none) hG
      have h2 : Submission.RealizableOver ℚ
          ((G' × Multiplicative (ZMod (n none))) ×
            (∀ a : α, Multiplicative (ZMod (n (some a))))) :=
        hα (G' × Multiplicative (ZMod (n none))) (fun a => n (some a))
          (fun a => hn (some a)) h1
      refine Submission.RealizableOver.of_mulEquiv ?_ h2
      exact ((MulEquiv.prodCongr (MulEquiv.refl G')
        (mulEquivPiOptionEquivProd (fun i : Option α => Multiplicative (ZMod (n i))))).trans
        (MulEquiv.prodAssoc).symm).symm
  exact key G n hn h

end Work.FieldTheory.Crossing
