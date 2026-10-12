import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.Band.Support
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Band.PotSplit` — the few-slot decomposition of `potWordU`

The localised potential word is a sum of terms each of which depends on at most two
configuration variables:

    `potWordU N v g ℓ μ 0 x = -μ Σᵢ potOnePiece N g ℓ i x + Σ_{p : i<j} potPairPiece N v ℓ p x`.

The point of isolating the pieces is the band argument of FS §6 (`lem:LocMatrices`): a
pairing `⟨E_S Φ, W E_T Φ⟩` of two joint sectors against a weight `W` which is *constant along
every slot outside a slot set `A`* vanishes as soon as `S` and `T` differ in a slot outside
`A` (`Work.BoseFixB2.DvApriori.Band.jointProj_pairing_eq_zero_of_free_ne`).  Hence each
summand of `potWordU` — whose dependence is confined to the one or two slots appearing in it
— vanishes in the pairing of two sectors which differ in at least three slots, and so does
their sum.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB2.Band

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The one-body summand of the localised potential word `potWordU` in the slot `i`:
`x ↦ ∫_y wLoc ℓ g 0 (xᵢ) y`.  It depends on the configuration only through `xᵢ`. -/
noncomputable def potOnePiece (N : ℕ) (g : EuclideanSpace ℝ (Fin 3) → ℝ) (ℓ : ℝ)
    (i : Fin N) : Submission.BoseGases.X N → ℝ :=
  fun x => ∫ y : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.wLoc ℓ g 0 (x i) y

/-- The two-body summand of `potWordU` attached to the ordered slot pair `p` with
`p.1 < p.2`: `x ↦ wLoc ℓ v 0 (x_{p.1}) (x_{p.2})`.  It depends on the configuration only
through the two slots `p.1`, `p.2`. -/
noncomputable def potPairPiece (N : ℕ) (v : EuclideanSpace ℝ (Fin 3) → ℝ) (ℓ : ℝ)
    (p : {p : Fin N × Fin N // p.1 < p.2}) : Submission.BoseGases.X N → ℝ :=
  fun x => Submission.BoseGases.wLoc ℓ v 0 (x p.1.1) (x p.1.2)

/-- **`potWordU` is the sum of its few-slot pieces.** -/
theorem potWordU_eq_sum (N : ℕ) (v g : EuclideanSpace ℝ (Fin 3) → ℝ) (ℓ μ : ℝ)
    (x : Submission.BoseGases.X N) :
    Work.BoseKinLoc.potWordU N v g ℓ μ 0 x
      = -μ * (∑ i : Fin N, potOnePiece N g ℓ i x)
        + ∑ p : {p : Fin N × Fin N // p.1 < p.2}, potPairPiece N v ℓ p x := by
  simp only [Work.BoseKinLoc.potWordU, potOnePiece, potPairPiece]
  rfl

/-- The one-body piece is constant along every slot other than its own. -/
theorem potOnePiece_update_eq {N : ℕ} {g : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ : ℝ}
    (i : Fin N) {j : ℕ} (hj : j < N) (hji : j ≠ (i : ℕ))
    (x : Submission.BoseGases.X N) (z : EuclideanSpace ℝ (Fin 3)) :
    potOnePiece N g ℓ i (Function.update x ⟨j, hj⟩ z) = potOnePiece N g ℓ i x := by
  have hne : (⟨j, hj⟩ : Fin N) ≠ i := fun h => hji (by simpa using congrArg Fin.val h)
  have hupd : (Function.update x ⟨j, hj⟩ z) i = x i := by
    rw [Function.update_apply, if_neg (Ne.symm hne)]
  simp only [potOnePiece, hupd]

/-- The two-body piece is constant along every slot outside its two slots. -/
theorem potPairPiece_update_eq {N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ : ℝ}
    (p : {p : Fin N × Fin N // p.1 < p.2}) {j : ℕ} (hj : j < N)
    (hj1 : j ≠ (p.1.1 : ℕ)) (hj2 : j ≠ (p.1.2 : ℕ))
    (x : Submission.BoseGases.X N) (z : EuclideanSpace ℝ (Fin 3)) :
    potPairPiece N v ℓ p (Function.update x ⟨j, hj⟩ z) = potPairPiece N v ℓ p x := by
  have hne1 : (⟨j, hj⟩ : Fin N) ≠ p.1.1 := fun h => hj1 (by simpa using congrArg Fin.val h)
  have hne2 : (⟨j, hj⟩ : Fin N) ≠ p.1.2 := fun h => hj2 (by simpa using congrArg Fin.val h)
  have hupd1 : (Function.update x ⟨j, hj⟩ z) p.1.1 = x p.1.1 := by
    rw [Function.update_apply, if_neg (Ne.symm hne1)]
  have hupd2 : (Function.update x ⟨j, hj⟩ z) p.1.2 = x p.1.2 := by
    rw [Function.update_apply, if_neg (Ne.symm hne2)]
  simp only [potPairPiece, hupd1, hupd2]

end Work.BoseFixB2.Band
