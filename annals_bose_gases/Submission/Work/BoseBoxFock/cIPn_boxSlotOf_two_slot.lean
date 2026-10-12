import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.MB.SlotWeakBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **The `cIPn`-pairing of a two-slot composition, in explicit Fubini form.**

`Work.BoseDict.boxSlotOf e w v j` is the `j`-th slot of the first-quantised rank-one operator
`|η_w⟩⟨η_v|` with `η_w = Σ_l w_l e_l`:  `(boxSlotOf e w v j Ψ) x = η_w(x j)·∫_z conj(η_v z)·Ψ(x[j↦z])`.

Composing the slots `i` and `j` (**distinct** slots) and pairing against `Θ` gives the explicit
triple integral: with `cIPn d A B = ∫_x conj(A x)·B x`,

    `cIPn d Θ (boxSlotOf e w₁ v₁ i (boxSlotOf e w₂ v₂ j Θ))`
      `= ∫_x ∫_s ∫_u conj(Θ x)·η_{w₁}(x i)·conj(η_{v₁} s)·η_{w₂}(x j)·conj(η_{v₂} u)·Θ(x[i↦s][j↦u])` .

The proof is: the inner slot is expanded by its definition; for `i ≠ j` the two `Function.update`s
commute (`(x[i↦s]) j = x j` and `(x[i↦s])[j↦u] = x[i↦s][j↦u]`), so the factor
`η_{w₂}((x[i↦s]) j) = η_{w₂}(x j)` does not depend on `s`; what remains is linearity of the Bochner
integral (the constant pull-outs `integral_const_mul`/`integral_mul_const` are unconditional, so no
integrability or Fubini hypothesis is needed; with the weak bundle every integrand is in fact
integrable, since each `η_w` is bounded with support in the finite-measure box `boxL ℓ` and `Θ` is
measurable and bounded).

This is the step that lets the **mode sums** `Σ_{s∈excited} Σ_{k ∈ PHset}` of the cubic `Q̃₃` row
(and of the `Q₂` pair rows) be moved inside the position integrals, after which the pinning
`η_{f k} = ℓ^{-3/2}qVec(k)` turns them into the lattice sums evaluated by the frame identity
(`Work.BoseBoxFock.latSampling_pair`).  The *diagonal* case `i = j` is not needed by the row
assembly: it is cancelled by the `− boxSlotSum e (T₁ ∘ T₂)` term
(`Work.BoseBoxFock.boxSlotOf_comp_same`). -/
theorem cIPn_boxSlotOf_two_slot {m d : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l))
    (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w₁ v₁ w₂ v₂ : Fin m → ℝ) (i j : Fin d) (hij : i ≠ j)
    (Θ : (Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    Work.BoseDict.cIPn d Θ
        (Work.BoseDict.boxSlotOf e w₁ v₁ i (Work.BoseDict.boxSlotOf e w₂ v₂ j Θ))
      = ∫ x : (Fin d → EuclideanSpace ℝ (Fin 3)),
          ∫ s : EuclideanSpace ℝ (Fin 3),
            ∫ u : EuclideanSpace ℝ (Fin 3),
              (starRingEnd ℂ) (Θ x) * Work.BoseDict.etaOf e w₁ (x i)
                * (starRingEnd ℂ) (Work.BoseDict.etaOf e v₁ s) * Work.BoseDict.etaOf e w₂ (x j)
                * (starRingEnd ℂ) (Work.BoseDict.etaOf e v₂ u)
                * Θ (Function.update (Function.update x i s) j u) := by
  have hji : j ≠ i := fun h => hij h.symm
  -- Expand `cIPn` and the two slots.  At the application `x[i ↦ z]` of the *inner* slot the
  -- update at the *other* slot `j` can be discarded (`i ≠ j`), which is what makes the factor
  -- `η_{w₂}(·)` independent of the slot variable `z`; the double update `x[i↦z][j↦u]` is kept.
  simp only [Work.BoseDict.cIPn, Work.BoseDict.boxSlotOf, Function.update_apply, if_neg hji]
  -- Every remaining factor is a constant for the integral it sits in, so the (unconditional)
  -- constant pull-outs `integral_const_mul` move it under the corresponding binder, and
  -- `mul_assoc` normalises the two sides to the same right-associated product.
  simp only [← MeasureTheory.integral_const_mul, mul_assoc]

end Work.BoseBoxFock
