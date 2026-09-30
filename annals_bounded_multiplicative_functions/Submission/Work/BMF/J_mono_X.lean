import Mathlib
import Submission.Vinogradov.ChallengeDeps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Monotonicity of the Vinogradov count `J_{s,k}(X)` in the range `X`

`J_{s,k}(X)` counts the pairs of `s`-tuples with entries in `[1, X]` whose power sums of
degrees `1, …, k` agree.  Enlarging the range `[1, X]` to `[1, X']` (`X ≤ X'`) only adds
candidates, so the count is monotone.  The two solution sets live in different types
(`Fin s → Icc 1 X` versus `Fin s → Icc 1 X'`), so the argument goes through the canonical
injection `bcast` that is the identity on underlying values.
-/

open scoped BigOperators

namespace Work.BMF

/-- The set of solutions of the Vinogradov system with entries in `[1, X]`, in the same
type as in the definition of `J`. -/
private def solSet (s k X : ℕ) :
    Finset ((Fin s → Finset.Icc 1 X) × (Fin s → Finset.Icc 1 X)) :=
  Finset.univ.filter (fun a => ∀ j ≤ k, ∑ i, (a.1 i).1 ^ j = ∑ i, (a.2 i).1 ^ j)

/-- Send a tuple with entries in `[1, X]` to the corresponding tuple with entries in
`[1, X']`, when `X ≤ X'`; the underlying values are unchanged. -/
private def bcast {X X' : ℕ} (h : X ≤ X') (s : ℕ) (x : Fin s → Finset.Icc 1 X) :
    Fin s → Finset.Icc 1 X' :=
  fun i => ⟨(x i).1, by
    have hi := (x i).2
    simp only [Finset.mem_Icc] at hi ⊢
    exact ⟨hi.1, le_trans hi.2 h⟩⟩

private lemma bcast_injective {X X' : ℕ} (h : X ≤ X') (s : ℕ) :
    Function.Injective (bcast (s := s) h) := by
  intro x y hxy
  funext i
  apply Subtype.ext
  have := congrFun hxy i
  simpa only [bcast] using congrArg Subtype.val this

/-- `J` is the cardinality of `solSet`. -/
private lemma J_eq_card (s k X : ℕ) :
    LeanEval.NumberTheory.VinogradovMeanValue.J s k X = ((solSet s k X).card : ℝ) := by
  simp only [LeanEval.NumberTheory.VinogradovMeanValue.J, solSet]

/-- Monotonicity of the Vinogradov count in the range `X`: enlarging `[1,X]` can only add
solutions. -/
theorem J_mono_X (s k : ℕ) {X X' : ℕ} (h : X ≤ X') :
    LeanEval.NumberTheory.VinogradovMeanValue.J s k X
      ≤ LeanEval.NumberTheory.VinogradovMeanValue.J s k X' := by
  rw [J_eq_card s k X, J_eq_card s k X']
  have hcard : (solSet s k X).card ≤ (solSet s k X').card := by
    refine Finset.card_le_card_of_injOn (fun a => (bcast h s a.1, bcast h s a.2)) ?_ ?_
    · intro a ha
      simp only [solSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      simpa only [bcast] using ha
    · intro a _ b _ hab
      have h1 : bcast h s a.1 = bcast h s b.1 := by
        simpa using congrArg Prod.fst hab
      have h2 : bcast h s a.2 = bcast h s b.2 := by
        simpa using congrArg Prod.snd hab
      exact Prod.ext (bcast_injective h s h1) (bcast_injective h s h2)
  exact_mod_cast hcard

end Work.BMF
