/-
AREA RESOL — the brutal truncation `σ^{≥j}` of a cochain complex of light condensed abelian
groups, together with its inclusion into the original complex.

The point of the *brutal* (as opposed to the smart) truncation is that the successive
quotients `σ^{≥j}K / σ^{≥j+1}K` are the single complexes `single j (K.X j)`, whose terms are
atomic sums; together with `CofibrantClosure.cone` this gives the induction proving that
the truncations of a bounded-above complex with atomic terms are solid-cofibrant.
-/
import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.SigmaSetup

open CategoryTheory Limits
open _root_.LightCondensed

noncomputable section

namespace Work.RESOL

/-- The zero object of `LightCondAb`, as a `Zero` instance (the one provided by
`HasZeroObject` is not registered for this abbreviation). -/
instance instZeroLightCondAb : Zero LightCondAb := HasZeroObject.zero' LightCondAb

/-- The *brutal truncation* `σ^{≥j}K`: same terms as `K` in degrees `≥ j`, zero below. -/
def trunc (j : ℤ) (K : Cpx) : Cpx where
  X n := if j ≤ n then K.X n else 0
  d i n := if h : j ≤ i ∧ j ≤ n ∧ i + 1 = n then
      (eqToHom (by simp [h.1]) ≫ K.d i n ≫ eqToHom (by simp [h.2.1])) else 0
  shape i n hn := by
    rw [dif_neg]
    rintro ⟨h1, h2, h3⟩
    exact hn (by rw [ComplexShape.up_Rel]; exact h3)
  d_comp_d' i n k hin hnk := by
    rw [ComplexShape.up_Rel] at hin hnk
    obtain rfl : n = i + 1 := by omega
    obtain rfl : k = i + 1 + 1 := by omega
    by_cases h : j ≤ i
    · rw [dif_pos (show j ≤ i ∧ j ≤ i + 1 ∧ i + 1 = i + 1 from ⟨h, by omega, rfl⟩),
        dif_pos (show j ≤ i + 1 ∧ j ≤ (i + 1) + 1 ∧ (i + 1) + 1 = i + 1 + 1 from
          ⟨by omega, by omega, rfl⟩)]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        Category.comp_id]
      rw [← Category.assoc (f := K.d i (i + 1)) (g := K.d (i + 1) ((i + 1) + 1)),
        K.d_comp_d i (i + 1) ((i + 1) + 1)]
      simp
    · rw [dif_neg (by rintro ⟨h1, _⟩; exact h h1)]
      simp

end Work.RESOL
