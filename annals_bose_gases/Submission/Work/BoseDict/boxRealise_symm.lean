import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.BoseDict.Defs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict.boxRealise_symm` — the realisation only depends on the multiset

`boxRealise e d Ψ` is a linear combination (over the multi-indices `α` with `|α| = d`) of
the symmetric mode products `modeProd e d α`.  A symmetric mode product is a sum over all
labellings `τ : Fin d → Fin m`, so permuting the particles of the configuration `x`
(`x ↦ x ∘ σ`, `σ : Equiv.Perm (Fin d)`) only reindexes that sum: the occupation
multi-index `modeMult τ` and the product `∏ i, e (τ i) (x i)` are both invariant under the
`σ`-action.  Hence `boxRealise e d Ψ (x ∘ σ) = boxRealise e d Ψ x`.

The proof goes through the two helper facts below:

* `modeMult_comp` — `modeMult (τ ∘ σ) = modeMult τ` (fiber cardinalities are preserved);
* `modeProd_comp_perm` — `modeProd e d α (x ∘ σ) = modeProd e d α x`,
  by reindexing the labelling sum with `Equiv.arrowCongr σ (Equiv.refl _)`
  (`τ ↦ τ ∘ σ⁻¹`) and the particle product with `Equiv.prod_comp`.

Finally `boxRealise` is unfolded through `Finsupp.lsum_apply` / `Finsupp.sum` /
`Finset.sum_apply`, and the equality is applied coefficientwise.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Precomposing a labelling by a permutation does not change its occupation
multi-index: the cardinality of every fiber is preserved. -/
lemma modeMult_comp {m n : ℕ} (τ : Fin n → Fin m) (σ : Equiv.Perm (Fin n)) :
    modeMult (τ ∘ σ) = modeMult τ := by
  unfold modeMult
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  apply Finset.card_bij (fun i _ => σ i)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha
  · intro a1 _ a2 _ h
    exact σ.injective h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact ⟨σ.symm b, by simpa using hb, by simp⟩

/-- The symmetric mode product is invariant under a permutation of the particle labels. -/
lemma modeProd_comp_perm {m d : ℕ} (e : Fin m → Sp → ℂ) (α : Fin m →₀ ℕ)
    (σ : Equiv.Perm (Fin d)) (x : Xn d) :
    modeProd e d α (x ∘ σ) = modeProd e d α x := by
  classical
  unfold modeProd
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl (Fin m)))
    (fun τ : Fin d → Fin m =>
      (if modeMult τ = α then (1 : ℂ) else 0) * ∏ i : Fin d, e (τ i) ((x ∘ σ) i))
    (fun δ : Fin d → Fin m =>
      (if modeMult δ = α then (1 : ℂ) else 0) * ∏ i : Fin d, e (δ i) (x i)) ?_
  intro τ
  have hπ : (Equiv.arrowCongr σ (Equiv.refl (Fin m))) τ = τ ∘ ⇑(σ⁻¹) := by
    funext i
    rw [Equiv.arrowCongr_apply]
    simp
  rw [hπ, modeMult_comp]
  congr 1
  rw [← Equiv.prod_comp σ (fun j => e ((τ ∘ ⇑(σ⁻¹)) j) (x j))]
  simp

theorem boxRealise_symm {m d : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (Ψ : Work.BoseB4.RealFock m) (σ : Equiv.Perm (Fin d)) (x : Work.BoseDict.Xn d) :
    Work.BoseDict.boxRealise e d Ψ (x ∘ σ) = Work.BoseDict.boxRealise e d Ψ x := by
  classical
  conv_lhs => rw [boxRealise, Finsupp.lsum_apply, Finsupp.sum, Finset.sum_apply]
  conv_rhs => rw [boxRealise, Finsupp.lsum_apply, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : c.sum (fun _ k => k) = d
  · rw [if_pos h]
    simp only [LinearMap.toSpanSingleton_apply, Pi.smul_apply]
    rw [modeProd_comp_perm]
  · rw [if_neg h]
    simp

end Work.BoseDict
