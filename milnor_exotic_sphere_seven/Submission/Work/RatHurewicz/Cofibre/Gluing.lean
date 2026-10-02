import Mathlib
import Submission.Work.RatHurewicz.Cofibre.Descent

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity on the preimage of the cofibre quotient

The preimage `q ⁻¹' S ⊆ E ⊕ Cone F` of a subset `S` of the cofibre splits, for the two cover
elements (`S = cofibreU ι`, `S = cofibreV ι`), into the two **clopen** summands
`Sum.inl '' univ` and `Sum.inr '' T` (`preimage_cofibreU`, `preimage_cofibreV`,
`isOpen_sumInl_cofibre`, `isOpen_sumInr_cofibre`).

This file records the case in which **both branches are defined on the whole summand**: if `Φ`
agrees with `Sum.elim f g` on `E ⊕ Cone F`, its restriction to the preimage is continuous by
composition — no cover argument, hence no big-union notation (cf. the trap recorded in
`Cofibre/NOTES.md`: `⋃ k : Bool, f k` unfolds to a *set-valued* existential in this Mathlib, so
`rintro ⟨k, hk⟩` binds `k : Set _` and `cases k` cannot be used).

This is exactly what the contraction of `cofibreV ι` needs: there the cone branch is
`cofibreInclCone ι ∘ coneContract`, defined on all of `Cone F`.  The case of `cofibreURetract`,
whose cone branch (`coneBaseLtHalf`) is only defined on the **half-open** cone `{h < 1/2}`, needs
the restricted statement; see `NOTES.md` for the two available routes.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-- **Gluing lemma, global-branch case.**  If `Φ` agrees with `Sum.elim f g` on `E ⊕ Cone F`
(both branches defined on the whole summand), then `a ↦ Φ a.1` is continuous on the preimage of any
`S` with `q ⁻¹' S = Sum.inl '' univ ∪ Sum.inr '' T`. -/
theorem continuous_of_sumElim (ι : C(F, E)) {Z : Type} [TopologicalSpace Z]
    {T : Set (Work.Stems.Cone F)} (f : C(E, Z)) (g : C(Work.Stems.Cone F, Z))
    {Φ : E ⊕ Work.Stems.Cone F → Z}
    (h1 : ∀ e, Φ (Sum.inl e) = f e) (h2 : ∀ y, Φ (Sum.inr y) = g y)
    {S : Set (cofibre ι)}
    (hS : (Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' S
      = Sum.inl '' (Set.univ : Set E) ∪ Sum.inr '' T) :
    Continuous fun a : ↥((Quotient.mk'' : E ⊕ Work.Stems.Cone F → cofibre ι) ⁻¹' S) => Φ a.1 := by
  have hΦ : Φ = fun z : E ⊕ Work.Stems.Cone F => Sum.elim (fun e : E => f e)
      (fun y : Work.Stems.Cone F => g y) z := by
    funext z
    rcases z with e | y
    · exact h1 e
    · exact h2 y
  rw [hΦ]
  exact (f.continuous.sumElim g.continuous).comp continuous_subtype_val

end

end Work.RatHurewicz
