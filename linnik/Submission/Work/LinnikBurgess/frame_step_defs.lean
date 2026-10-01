import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs

/-!
# Vocabulary for the frame step of Theorem F (U11)

The frame step fixes `a0, a1` (two entries of the first triple) and the whole second triple `b`,
and asks how many possible third entries `a2` make the pair `![a0,a1,a2]`, `b` pass the
double-critical test modulo `p^k` at some `p`-adic unit `y`.

The predicate involves an unbounded existential `∃ y`, so the corresponding `Finset` filter is
packaged as a `noncomputable def` (with `classical` locally), following the convention used
elsewhere in the workspace (`ddPairSet`, `gcdWeightSum`, ...).
-/

open scoped BigOperators

namespace Work.LinnikBurgess

open Classical

/-- The set of `a2 ∈ [1,H]` for which `![a0,a1,a2]`, `b` admits a unit witness `y` at which both
`critN` and its derivative vanish modulo `p^k`. -/
noncomputable def frameStepSet (p k H : ℕ) (a0 a1 : ℕ) (b : Fin 3 → ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 H).filter (fun a2 : ℕ => ∃ y : ℕ,
    UnitAt p y ![a0, a1, a2] b
      ∧ (((p ^ k : ℕ) : ℤ) ∣ (critN ![a0, a1, a2] b).eval (y : ℤ))
      ∧ (((p ^ k : ℕ) : ℤ) ∣ (Polynomial.derivative (critN ![a0, a1, a2] b)).eval (y : ℤ)))

/-- The `DL_d` version of the frame set: the `a2 ∈ [1,H]` for which `![a0,a1,a2]`, `b` is
`DL_d`-double-critical at some witness `y` which is a `p`-adic unit for every `p ∣ d`. -/
noncomputable def frameStepSetD (d H : ℕ) (a0 a1 : ℕ) (b : Fin 3 → ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 H).filter (fun a2 : ℕ => ∃ y : ℕ,
    (∀ p ∈ d.primeFactors, UnitAt p y ![a0, a1, a2] b)
      ∧ ((d : ℤ) ∣ (critN ![a0, a1, a2] b).eval (y : ℤ))
      ∧ ((d : ℤ) ∣ (Polynomial.derivative (critN ![a0, a1, a2] b)).eval (y : ℤ)))

/-- The left-hand side of `frame_count`, as a function of the unique index `i`. -/
noncomputable def frameSum (H m d g : ℕ) (i : Fin 6) : ℝ :=
  ∑ fg ∈ (Finset.univ : Finset ((Fin 3 → Fin H) × (Fin 3 → Fin H))).filter
      (fun fg => ∀ i', i' ≠ i → shift6 fg i ≠ shift6 fg i'),
    sqrtGcdW m i (shift6 fg) * frameW d g fg

/-- The modulus to which the frame step confines the solved coordinate:
`∏_{p ∣ d} p^(max 0 (v_p(d) - v_p(2) - v_p(a0-a1)))`. -/
noncomputable def frameMod (d a0 a1 : ℕ) : ℕ :=
  ∏ p ∈ d.primeFactors, p ^ (max 0 (d.factorization p - padicValNat p 2
    - padicValNat p (((a0 : ℤ) - (a1 : ℤ)).natAbs)))

end Work.LinnikBurgess
