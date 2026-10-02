import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.SliceDefs
import Submission.Work.Deep.Sparse.fibreMean_azuma

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Under the uniform colouring, the expectation is the average of the values. -/
lemma colSpace_expect_eq_inv_mul_sum {k : ℕ} [Nonempty (V → Fin k)]
    (X : (V → Fin k) → ℝ) :
    (colSpace (V := V) k).expect X
      = (Fintype.card (V → Fin k) : ℝ)⁻¹ * ∑ f : V → Fin k, X f := by
  rw [FinSpace.expect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun f _ => by rw [colSpace_mass]

/-- **Reindexing the double sum of a grafted random variable.**  Summing `Y (graft A g f)`
over all pairs `(f, g) ∈ (V → Fin k) × (↥A → Fin k)` and then over all of `Y` differ by the
cardinality `k^{|A|}` of the fibre: the involution `(f, g) ↦ (graft A g f, f|_A)`
(`disintSwap`) identifies the pairs with `(V → Fin k) × (↥A → Fin k)` and each value of `Y`
is attained exactly `|↥A → Fin k|` times. -/
lemma sum_graft_eq {k : ℕ} (A : Finset V) (Y : (V → Fin k) → ℝ) :
    (∑ f : V → Fin k, ∑ g : ↥A → Fin k, Y (graft A g f))
      = (Fintype.card (↥A → Fin k) : ℝ) * ∑ h : V → Fin k, Y h := by
  calc ∑ f : V → Fin k, ∑ g : ↥A → Fin k, Y (graft A g f)
      = ∑ p : (V → Fin k) × (↥A → Fin k), Y (graft A p.2 p.1) :=
        (Fintype.sum_prod_type (f := fun p : (V → Fin k) × (↥A → Fin k) =>
          Y (graft A p.2 p.1))).symm
    _ = ∑ q : (V → Fin k) × (↥A → Fin k), Y q.1 :=
        Fintype.sum_equiv (disintSwap A)
          (fun p : (V → Fin k) × (↥A → Fin k) => Y (graft A p.2 p.1))
          (fun q : (V → Fin k) × (↥A → Fin k) => Y q.1)
          (fun p => rfl)
    _ = ∑ h : V → Fin k, ∑ _gA : ↥A → Fin k, Y h :=
        Fintype.sum_prod_type (f := fun q : (V → Fin k) × (↥A → Fin k) => Y q.1)
    _ = ∑ h : V → Fin k, (Fintype.card (↥A → Fin k) : ℝ) * Y h := by
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card (↥A → Fin k) : ℝ) * ∑ h : V → Fin k, Y h := by
        rw [Finset.mul_sum]

/-- **The tower property of the fibre mean.**  Under the uniform colouring `f : V → Fin k`, the
mean of the fibre mean `fibreMean A Y` equals the mean of `Y`: conditional expectation on the
colours outside `A`, averaged over the colours outside `A`, reproduces the unconditional mean.

Expanding with `colSpace_expect_eq_inv_mul_sum` and `fibreMean`, both sides become
`|V → Fin k|⁻¹ · |↥A → Fin k|⁻¹` times a double sum; `sum_graft_eq` identifies the double sum
as `|↥A → Fin k| · ∑ h Y h`, and the fibre cardinalities cancel against the weights. -/
theorem colSpace_expect_fibreMean {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} [Nonempty (V → Fin k)] (A : Finset V) (Y : (V → Fin k) → ℝ) :
    (colSpace (V := V) k).expect (fun f => fibreMean A Y f) = (colSpace (V := V) k).expect Y := by
  classical
  -- The fibre `↥A → Fin k` is nonempty: restrict any colouring of `V` to `A`.
  obtain ⟨f₀⟩ := (inferInstance : Nonempty (V → Fin k))
  haveI hneA : Nonempty (↥A → Fin k) := ⟨fun a => f₀ a.val⟩
  -- The fibre cardinality is `k ^ |A|`, hence nonzero.
  have hcardA : (Fintype.card (↥A → Fin k) : ℝ) = (k : ℝ) ^ A.card := by
    rw [card_colSpace, Fintype.card_coe, Nat.cast_pow]
  have hAne : (Fintype.card (↥A → Fin k) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  -- The fibre mean, expressed through the fibre cardinality.
  have hfm : ∀ f : V → Fin k, fibreMean A Y f
      = (Fintype.card (↥A → Fin k) : ℝ)⁻¹ * ∑ g : ↥A → Fin k, Y (graft A g f) := by
    intro f
    rw [fibreMean, one_div, ← hcardA]
  rw [colSpace_expect_eq_inv_mul_sum (V := V) (k := k) (fun f => fibreMean A Y f),
      colSpace_expect_eq_inv_mul_sum (V := V) (k := k) Y]
  congr 1
  calc ∑ f : V → Fin k, fibreMean A Y f
      = ∑ f : V → Fin k, (Fintype.card (↥A → Fin k) : ℝ)⁻¹ *
          ∑ g : ↥A → Fin k, Y (graft A g f) := by
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [hfm f]
    _ = (Fintype.card (↥A → Fin k) : ℝ)⁻¹ *
          ∑ f : V → Fin k, ∑ g : ↥A → Fin k, Y (graft A g f) := by
        rw [Finset.mul_sum]
    _ = (Fintype.card (↥A → Fin k) : ℝ)⁻¹ *
          ((Fintype.card (↥A → Fin k) : ℝ) * ∑ h : V → Fin k, Y h) := by
        rw [sum_graft_eq]
    _ = ∑ h : V → Fin k, Y h := by
        rw [← mul_assoc, inv_mul_cancel₀ hAne, one_mul]

end Work.Deep.Sparse
