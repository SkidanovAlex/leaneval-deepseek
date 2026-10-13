/-
  `Work.WilLibTS` — corollaries of the projection theorem
  `Work.WilLibTS.TS.SignElimination.polynomialSignSet_projection_finite`
  (module `Submission.Work.WilLibTS.TS.PolynomialSignSetProjection2`).

  The ported theorem is stated for an arbitrary coordinate map `c : X → ι → ℝ`.  Every consumer we
  know of (the Tarski–Seidenberg bridge `C4a_TS1`, the CAD development `WilE4`) works with the
  *identity* coordinate map on `Fin n → ℝ`, and with the coordinates of `Fin (n+1) → ℝ` split as
  `Fin n ⊕ Fin 1` (or `Fin n × ℝ`).  This file records those specialisations, so that a caller
  never has to do the `Sum.elim` bookkeeping by hand.

  Contents.

  * `PolynomialSignSet.congr` — a `PolynomialSignSet` is one after replacing the set by an equal
    set (the inductive gives no `rw` instance).
  * `polynomialSignSet_projection_finite_id` — projection of a `PolynomialSignSet` in
    `(ι → ℝ) × (κ → ℝ)`, identity coordinate map.
  * `polynomialSignSet_projection_one_id` — the one-coordinate case `κ = ℝ`.
  * `polynomialSignSet_projection_sum` — the same in `(ι ⊕ κ) → ℝ` coordinates and
    `Sum.elim`-splitting, i.e. the form matching `Fin (n+1) ≃ Fin n ⊕ Fin 1` bookkeeping.
-/
import Mathlib
import Submission.Work.WilLibTS.TS.PolynomialSignSetFinite2

namespace Work.WilLibTS.TS

noncomputable section

namespace PolynomialSignSet

variable {X ι : Type*} {c : X → ι → ℝ} {S T : Set X}

/-- A `PolynomialSignSet` is still one after replacing the set by an equal set. -/
lemma congr (hS : PolynomialSignSet c S) (h : S = T) : PolynomialSignSet c T :=
  h ▸ hS

end PolynomialSignSet

namespace SignElimination

/-- **Tarski–Seidenberg, identity coordinates.**  The projection of a `PolynomialSignSet` in
`(ι → ℝ) × (κ → ℝ)` onto the first factor, for a finite `κ`. -/
theorem polynomialSignSet_projection_finite_id {ι κ : Type*} [Finite κ]
    {A : Set ((ι → ℝ) × (κ → ℝ))}
    (hA : PolynomialSignSet (fun z : (ι → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2) A) :
    PolynomialSignSet (id : (ι → ℝ) → ι → ℝ) {x : ι → ℝ | ∃ y : κ → ℝ, (x, y) ∈ A} :=
  polynomialSignSet_projection_finite (c := id) hA

/-- **Tarski–Seidenberg, one coordinate, identity coordinates.** -/
theorem polynomialSignSet_projection_one_id {ι : Type*} {A : Set ((ι → ℝ) × ℝ)}
    (hA : PolynomialSignSet (fun z : (ι → ℝ) × ℝ => fun o : Option ι => Option.elim o z.2 z.1)
      A) :
    PolynomialSignSet (id : (ι → ℝ) → ι → ℝ) {x : ι → ℝ | ∃ y : ℝ, (x, y) ∈ A} :=
  polynomialSignSet_projection_one (c := id) hA

/-- **Tarski–Seidenberg with `Sum`-coordinates.**  If a `PolynomialSignSet` on `(ι ⊕ κ) → ℝ` is
given, then the set of `x : ι → ℝ` for which some `y : κ → ℝ` extends it into the set is again a
`PolynomialSignSet`.  (This is the form in which the coordinates of `Fin (n+1) ≃ Fin n ⊕ Fin 1`
arise in the `C4a_TS1` bridge and in CAD.) -/
theorem polynomialSignSet_projection_sum {ι κ : Type*} [Finite κ] {S : Set ((ι ⊕ κ) → ℝ)}
    (hS : PolynomialSignSet (id : ((ι ⊕ κ) → ℝ) → ι ⊕ κ → ℝ) S) :
    PolynomialSignSet (id : (ι → ℝ) → ι → ℝ)
      {x : ι → ℝ | ∃ y : κ → ℝ, (fun v => Sum.elim x y v) ∈ S} := by
  have h : PolynomialSignSet
      (fun z : (ι → ℝ) × (κ → ℝ) => fun v : ι ⊕ κ => Sum.elim z.1 z.2 v)
      {z : (ι → ℝ) × (κ → ℝ) | (fun v => Sum.elim z.1 z.2 v) ∈ S} :=
    hS.coordinate_preimage (fun z : (ι → ℝ) × (κ → ℝ) => fun v : ι ⊕ κ => Sum.elim z.1 z.2 v)
      id (d := fun z : (ι → ℝ) × (κ → ℝ) => fun v : ι ⊕ κ => Sum.elim z.1 z.2 v)
      (by intro z i; rfl)
  exact polynomialSignSet_projection_finite (c := id) h

end SignElimination

end

end Work.WilLibTS.TS
