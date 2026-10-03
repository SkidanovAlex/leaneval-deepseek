import Mathlib
import Submission.Work.Peluse.UControl.PetStepChain

/-!
# Well-foundedness of the PET weight-vector order

`Work.Peluse.UControl.PetStep.petLt` is the order Peluse uses to prove that the PET chain
(Lemmas 4.7/4.8 of `arXiv:1909.00309`) terminates: at the *largest* index where two weight
vectors `u v : Fin (d+1) → ℕ` differ, the first must be smaller.  In other words it is the
*colexicographic* order on `Fin (d+1) → ℕ`, read from the top coordinate down.

Mathlib knows that the colexicographic order on a finite product of well-founded linear orders is
well-founded (`Pi.Colex.wellFoundedLT`, phrased as the well-foundedness of the `<` of the type
synonym `Colex (∀ i, α i)`, whose `<` instance is by definition `Pi.Lex (· > ·) (· < ·)`).  The
only work here is to identify `petLt` with that relation.
-/

namespace Work.Peluse.UControl

open scoped BigOperators

/-- `petLt` is the colexicographic relation `Pi.Lex (· > ·) (· < ·)` on `Fin (d+1) → ℕ`: the two
relations differ only in the order of the two conjuncts of the existential. -/
lemma petLt_iff_piLex {d : ℕ} (u v : Fin (d + 1) → ℕ) :
    PetStep.petLt u v ↔
      Pi.Lex (fun a b : Fin (d + 1) => b < a) (fun {_} (a b : ℕ) => a < b) u v := by
  constructor
  · rintro ⟨j, hj, hk⟩
    exact ⟨j, fun k hk' => hk k hk', hj⟩
  · rintro ⟨j, hj, hk⟩
    exact ⟨j, hk, fun k hk' => hj k hk'⟩

/-- **The PET weight-vector order is well-founded.**  This is the termination measure of the
iterated PET step: each application of Lemma 4.7/4.8 of Peluse's §4 strictly lowers the vector of
weights in the order `petLt`, so the chain cannot be infinite.

`PetStep.petLt` is the colexicographic order on `Fin (d+1) → ℕ` (`Colex (Fin (d+1) → ℕ)`, whose
`<` is `Pi.Lex (· > ·) (· < ·)`), and Mathlib's `Pi.Colex.wellFoundedLT` proves the latter
well-founded. -/
theorem petChainWF (d : ℕ) : WellFounded (Work.Peluse.UControl.PetStep.petLt (d := d)) := by
  have huniv : WellFoundedLT (Colex (Fin (d + 1) → ℕ)) := Pi.Colex.wellFoundedLT
  have h : WellFounded
      ((· < ·) : Colex (Fin (d + 1) → ℕ) → Colex (Fin (d + 1) → ℕ) → Prop) := huniv
  exact h.mono (fun u v huv => (petLt_iff_piLex u v).mp huv)

end Work.Peluse.UControl
