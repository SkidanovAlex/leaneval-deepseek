import Mathlib
import Submission.Work.Peluse.UControl.peluseFamily

namespace Work.Peluse.UControl

/-- The parametrisation `boxVal H : Fin (2H+1) → ℤ`, `k ↦ k - H`, is injective. -/
lemma boxVal_injective (H : ℕ) : Function.Injective (IdxDatum.boxVal H) := by
  intro k₁ k₂ h
  simp only [IdxDatum.boxVal] at h
  have h2 : (k₁ : ℤ) = (k₂ : ℤ) := by omega
  exact Fin.ext (by exact_mod_cast h2)

/-- The cardinality of the parameter box: `parBox` is the image of the product of the boxes
`Fin (2H+1)^{|S j|}` under the (injective) pointwise box parametrisation, so its cardinality is the
product of the fibre cardinalities, i.e. `(2H+1)^{Σ_j |S j|}`. -/
theorem parBox_card (D : IdxDatum) (l H : ℕ) :
    (D.parBox l H).card = (2 * H + 1) ^ (∑ j : Fin l, Fintype.card (D.S j)) := by
  have hinj : Function.Injective
      (fun f : ((j : Fin l) → D.S j → Fin (2 * H + 1)) =>
        fun j s => IdxDatum.boxVal H (f j s)) := by
    intro f g h
    funext j s
    exact boxVal_injective H (congrFun (congrFun h j) s)
  have h1 : ∀ j : Fin l,
      (Fintype.piFinset fun _ : D.S j => (Finset.univ : Finset (Fin (2 * H + 1)))).card
        = (2 * H + 1) ^ Fintype.card (D.S j) := by
    intro j
    rw [Fintype.card_piFinset]
    simp
  rw [IdxDatum.parBox, Finset.card_image_of_injective (s := _) hinj]
  rw [Fintype.card_piFinset]
  simp only [h1]
  rw [Finset.prod_pow_eq_pow_sum]

end Work.Peluse.UControl
