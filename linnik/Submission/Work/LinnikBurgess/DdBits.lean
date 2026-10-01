import Mathlib

/-! Auxiliary definitions for the `r = 3` sixth-moment bound for moduli divisible by a cube.

These definitions package the "doubly degenerate critical class" condition of
`Submission.Work.NumberTheory.DirichletCharacter.burgess_moment_r3_noncubefree_final`
(`cc6_crit_quad_iff_H_multipleRoot`, `cDD`) in a form convenient for counting. -/

open scoped BigOperators

namespace Work.LinnikBurgess

/-- The six integer shifts attached to a pair `q = (f, g)` of triples of residues: the six
values `f l + 1`, `g l + 1`. -/
def shift6 {H : ℕ} (q : (Fin 3 → Fin H) × (Fin 3 → Fin H)) (i : Fin 6) : ℕ :=
  ![((q.1 0 : ℕ) + 1), ((q.1 1 : ℕ) + 1), ((q.1 2 : ℕ) + 1),
    ((q.2 0 : ℕ) + 1), ((q.2 1 : ℕ) + 1), ((q.2 2 : ℕ) + 1)] i

/-- A pair is a *singleton pair* when one of the six shifts occurs exactly once among them. -/
abbrev IsSingleton6 {H : ℕ} (q : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : Prop :=
  ∃ i : Fin 6, ∀ i' : Fin 6, i' ≠ i → shift6 q i ≠ shift6 q i'

/-- The *doubly degenerate* condition modulo `p ^ j` for a pair `q`: there is a residue class
`r : ZMod p` at which all six shifts are units, the two triples of inverses have the same sum
and the same sum of squares in `ZMod p` (*critical* to second order), and the two sums of
inverses in `ZMod (p ^ j)` agree (i.e. `p ^ j` divides the `p`-adic lift `D(r)` of the
criticality defect). -/
abbrev DDMod {H : ℕ} (p j : ℕ) [Fact p.Prime] (q : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : Prop :=
  ∃ r : ZMod p,
    (∀ l : Fin 3, (r + ((q.1 l : ℕ) : ZMod p)) ≠ 0 ∧ (r + ((q.2 l : ℕ) : ZMod p)) ≠ 0)
    ∧ (∑ l : Fin 3, (r + ((q.1 l : ℕ) : ZMod p))⁻¹)
        = (∑ l : Fin 3, (r + ((q.2 l : ℕ) : ZMod p))⁻¹)
    ∧ (∑ l : Fin 3, ((r + ((q.2 l : ℕ) : ZMod p))⁻¹) ^ 2)
        = (∑ l : Fin 3, ((r + ((q.1 l : ℕ) : ZMod p))⁻¹) ^ 2)
    ∧ ((∑ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ j)) + (q.1 l : ℕ))⁻¹)
        - (∑ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ j)) + (q.2 l : ℕ))⁻¹) = 0)

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- The set of singleton pairs carrying a doubly degenerate class modulo `p ^ j`. -/
noncomputable def ddSet (p j H : ℕ) [Fact p.Prime] :
    Finset ((Fin 3 → Fin H) × (Fin 3 → Fin H)) := by
  classical
  exact Finset.univ.filter (fun q => IsSingleton6 q ∧ DDMod p j q)

/-- The set of singleton pairs. -/
noncomputable def singSet (H : ℕ) : Finset ((Fin 3 → Fin H) × (Fin 3 → Fin H)) := by
  classical
  exact Finset.univ.filter (fun q => IsSingleton6 q)

end Work.LinnikBurgess

namespace Work.LinnikBurgess

/-- The complete cubic correlation sum attached to a pair `(f, g)` of triples of shifts and a
character `χ` modulo `q`: `∑_x χ (∏_l (x + f l + 1)) * conj (χ (∏_l (x + g l + 1)))`. -/
noncomputable def corr6 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) {H : ℕ}
    (f g : Fin 3 → Fin H) : ℂ :=
  ∑ x : ZMod q,
    χ (∏ l : Fin 3, (x + ((((f l : ℕ) + 1 : ℕ)) : ZMod q)))
      * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + ((((g l : ℕ) + 1 : ℕ)) : ZMod q))))

end Work.LinnikBurgess
