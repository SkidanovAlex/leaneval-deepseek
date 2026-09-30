import Mathlib
import Submission.Work.RatHurewicz.Cofibre.Descent

/-!
# The classes of the gluing relation on the positive-height part of `E ⊕ Cone F`

`cofibre ι` is the quotient of `E ⊕ Cone F` by `EqvGen (cofibreRel ι)`, and `cofibreV ι` is the
image of the punctured cone `Sum.inr '' {0 < coneHeight}` (`preimage_cofibreV`).  To descend a map
of the shape `Sum.elim (const c) Ψ` from the preimage of `cofibreV ι` to `cofibreV ι` one needs:

* **Claim A** (`cofibreEqvGen_pos_iff`): positivity of `cofibreHeightFun` is invariant under the
  gluing relation;
* **Claim B** (`cofibreEqvGen_cone_of_pos`): two related points of positive height are
  `Sum.inr a`, `Sum.inr b` with `a = b` in `Cone F`;
* and hence (`sumElim_const_cone_eq_of_eqvGen`) `Sum.elim (const c) Ψ` takes equal values on them.

The point of Claim A is the `trans` case of the induction: with it, the middle point's positivity
comes for free.  Note that the `rel` step `Sum.inl (ι z) ~ Sum.inr (coneIncl z)` has height `0` on
both sides, so it can never occur between two positive-height points.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-- **Claim A.**  Positivity of `cofibreHeightFun` is invariant under the gluing relation. -/
theorem cofibreEqvGen_pos_iff (ι : C(F, E)) {x y : E ⊕ Work.Stems.Cone F}
    (h : Relation.EqvGen (cofibreRel ι) x y) :
    ((0 : unitInterval) < cofibreHeightFun ι x ↔
      (0 : unitInterval) < cofibreHeightFun ι y) := by
  induction h with
  | rel a b hab =>
    obtain ⟨z, rfl, rfl⟩ := hab
    simp [cofibreHeightFun]
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ihab ihbc => exact ihab.trans ihbc

/-- **Claim B.**  Two related points of positive height lie in the punctured cone, over the same
point of `Cone F`. -/
theorem cofibreEqvGen_cone_of_pos (ι : C(F, E)) {x y : E ⊕ Work.Stems.Cone F}
    (h : Relation.EqvGen (cofibreRel ι) x y)
    (hx : (0 : unitInterval) < cofibreHeightFun ι x) :
    ∃ a b : Work.Stems.Cone F, x = Sum.inr a ∧ y = Sum.inr b ∧ a = b := by
  induction h with
  | rel a b hab =>
    exfalso
    obtain ⟨z, rfl, -⟩ := hab
    exact absurd hx (by simp [cofibreHeightFun])
  | refl a =>
    rcases a with e | y
    · exact absurd hx (by simp [cofibreHeightFun])
    · exact ⟨y, y, rfl, rfl, rfl⟩
  | symm a b hab ih =>
    have ha : (0 : unitInterval) < cofibreHeightFun ι a :=
      (cofibreEqvGen_pos_iff ι hab).mpr hx
    obtain ⟨c, d, hac, hbd, hcd⟩ := ih ha
    exact ⟨d, c, hbd, hac, hcd.symm⟩
  | trans a b c hab hbc ihab ihbc =>
    have hb : (0 : unitInterval) < cofibreHeightFun ι b :=
      (cofibreEqvGen_pos_iff ι hab).mp hx
    obtain ⟨p, q, hap, hbq, hpq⟩ := ihab hx
    obtain ⟨p', q', hbp', hcq', hp'q'⟩ := ihbc hb
    have hqq : q = p' := Sum.inr.inj (hbq.symm.trans hbp')
    exact ⟨p, q', hap, hcq', hpq.trans (hqq.trans hp'q')⟩

/-- The function `Sum.elim (const c) Ψ` is constant on the gluing classes of the positive-height
part of `E ⊕ Cone F` — the well-definedness input for descending it to `cofibreV ι`. -/
theorem sumElim_const_cone_eq_of_eqvGen (ι : C(F, E)) {Z : Type} (c : Z)
    (Ψ : Work.Stems.Cone F → Z) {x y : E ⊕ Work.Stems.Cone F}
    (h : Relation.EqvGen (cofibreRel ι) x y)
    (hx : (0 : unitInterval) < cofibreHeightFun ι x)
    (hy : (0 : unitInterval) < cofibreHeightFun ι y) :
    Sum.elim (fun _ : E => c) Ψ x = Sum.elim (fun _ : E => c) Ψ y := by
  obtain ⟨a, b, rfl, rfl, hab⟩ := cofibreEqvGen_cone_of_pos ι h hx
  rw [hab]

end

end Work.RatHurewicz
