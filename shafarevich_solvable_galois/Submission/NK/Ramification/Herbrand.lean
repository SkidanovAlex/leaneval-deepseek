import Mathlib.Order.CompletePartialOrder
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.RingTheory.Valuation.RamificationGroup
import Submission.NK.Ramification.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise

namespace NK.Ramification

universe u

noncomputable section

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

/-! ## The lower indices and the Herbrand function -/

/-- The **lower index** `g_i = #G_i` of the ramification filtration.  Under the finiteness
hypothesis `[Finite (A.decompositionSubgroup K)]` this is the honest cardinality of `G_i`. -/
def lowerIndex (A : ValuationSubring L) (i : ℕ) : ℕ :=
  Nat.card ↥(ramificationSubgroup (K := K) A i)

/-- **The Herbrand function** `φ`, evaluated at natural numbers:

  `φ(n) = (g_0 + g_1 + ⋯ + g_{n-1}) / g_0`.

This is `∫_0^n dt/[G_0 : G_t]` for the lower numbering, and determines the piecewise-linear
Herbrand function on all of `[0, ∞)`. -/
def herbrand (A : ValuationSubring L) (n : ℕ) : ℚ :=
  (∑ i ∈ Finset.range n, (lowerIndex (K := K) A i : ℚ)) / (lowerIndex (K := K) A 0 : ℚ)

/-- **The inverse Herbrand function** `ψ`: the least `i` with `v ≤ φ(i)`.

For `v` an integer, `ψ(v)` is the index under which the upper-numbered subgroup `G^v` is the
lower-numbered subgroup of the lower numbering. -/
def herbrandInv (A : ValuationSubring L) (v : ℕ) : ℕ :=
  sInf {i : ℕ | (v : ℚ) ≤ herbrand (K := K) A i}

/-- **The upper-numbered ramification subgroups** `G^v = G_{ψ(v)}`, `v : ℕ`. -/
def upperRamificationSubgroup (A : ValuationSubring L) (v : ℕ) :
    Subgroup (A.decompositionSubgroup K) :=
  ramificationSubgroup A (herbrandInv (K := K) A v)

/-! ## The break sets -/

/-- `i` is a **lower break** of the ramification filtration: the filtration strictly drops from
`G_i` to `G_{i+1}`. -/
def LowerBreak (A : ValuationSubring L) (i : ℕ) : Prop :=
  ramificationSubgroup (K := K) A i ≠ ramificationSubgroup A (i + 1)

/-- `v` is an **upper break** of the ramification filtration. -/
def UpperBreak (A : ValuationSubring L) (v : ℕ) : Prop :=
  upperRamificationSubgroup (K := K) A v ≠ upperRamificationSubgroup A (v + 1)

/-! ## The Hasse–Arf theorem -/

/-- **The Hasse–Arf theorem**, in the integer-indexed formulation: at every lower break `i` the
value `φ(i)` of the Herbrand function is an integer.

Equivalently, the jumps of the upper-numbered filtration `G^v` occur only at integral values of
`v`; this is the form in which Hasse–Arf is usually stated.  The divisibility form of the same
statement, `g_0 ∣ g_0 + ⋯ + g_{i-1}` at every lower break `i`, is
`NK.Ramification.hasseArf_iff_dvd`; the cases proved in this workspace and the honest account of
what remains are collected in `Submission/Work/Ramification/HasseArf.lean`.

The classical proof (Hasse, *Zahlbericht*; Serre, *Local Fields* IV §3) proceeds by first
settling the abelian case through the explicit computation of the Herbrand function against the
unit filtration `U^i ⊆ K^×` and local reciprocity, and then reducing to the abelian case by a
transfer argument.  For the `p`-adic fields of this workspace the abelian case is available
(`NK.LocalCFT`); what is formalised here is the statement and its elementary consequences. -/
def HasseArf (A : ValuationSubring L) : Prop :=
  ∀ i : ℕ, LowerBreak (K := K) A i → ∃ m : ℕ, herbrand (K := K) A i = m

/-! ## Elementary consequences -/

/-- The zeroth lower index is positive as soon as the decomposition subgroup is finite: the
subgroup `G_0` always contains the identity. -/
theorem lowerIndex_zero_pos (A : ValuationSubring L) [Finite (A.decompositionSubgroup K)] :
    0 < lowerIndex (K := K) A 0 := by
  have : Nonempty ↥(ramificationSubgroup (K := K) A 0) :=
    ⟨⟨1, (ramificationSubgroup A 0).one_mem⟩⟩
  exact Nat.card_pos

/-- `φ(0) = 0`. -/
@[simp]
theorem herbrand_zero (A : ValuationSubring L) : herbrand (K := K) A 0 = 0 := by
  simp [herbrand]

/-- `φ(1) = 1` (in the finite case): the Herbrand function fixes the first integer. -/
theorem herbrand_one (A : ValuationSubring L) [Finite (A.decompositionSubgroup K)] :
    herbrand (K := K) A 1 = 1 := by
  have hpos := lowerIndex_zero_pos (K := K) A
  have hne : (lowerIndex (K := K) A 0 : ℚ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp hpos
  simp only [herbrand, Finset.sum_range_one]
  field_simp

/-- **Rationality of the breaks**: `g_0 · φ(n)` is an integer, namely `g_0 + ⋯ + g_{n-1}`.  Hence
the jumps of the upper filtration lie in `(1/g_0)ℤ`. -/
theorem herbrand_mul_lowerIndex_zero (A : ValuationSubring L)
    [Finite (A.decompositionSubgroup K)] (n : ℕ) :
    (lowerIndex (K := K) A 0 : ℚ) * herbrand (K := K) A n =
      ∑ i ∈ Finset.range n, (lowerIndex (K := K) A i : ℚ) := by
  have hne : (lowerIndex (K := K) A 0 : ℚ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp (lowerIndex_zero_pos (K := K) A)
  rw [herbrand]
  field_simp

/-- The value `g_0 · φ(n)` is a nonnegative integer. -/
theorem herbrand_mul_lowerIndex_zero_nat (A : ValuationSubring L)
    [Finite (A.decompositionSubgroup K)] (n : ℕ) :
    ∃ m : ℕ, (lowerIndex (K := K) A 0 : ℚ) * herbrand (K := K) A n = (m : ℚ) := by
  refine ⟨∑ i ∈ Finset.range n, lowerIndex (K := K) A i, ?_⟩
  rw [herbrand_mul_lowerIndex_zero, Nat.cast_sum]

/-- **The Hasse–Arf theorem holds in the tame case**: if the filtration is trivial from level `1`
on (`G_1 = ⊥`, i.e. `L/K` is at most tamely ramified) then the only lower break is `i = 0` and
`φ(0) = 0`, so the Hasse–Arf condition is satisfied. -/
theorem hasseArf_of_tame (A : ValuationSubring L) (h : ramificationSubgroup (K := K) A 1 = ⊥) :
    HasseArf (K := K) A := by
  intro i hi
  cases i with
  | zero => exact ⟨0, herbrand_zero A⟩
  | succ k =>
    exact absurd (by
      have h1 : ramificationSubgroup (K := K) A (k + 1) = ⊥ :=
        le_bot_iff.mp ((ramificationSubgroup_antitone A (by omega)).trans_eq h)
      have h2 : ramificationSubgroup (K := K) A (k + 1 + 1) = ⊥ :=
        le_bot_iff.mp ((ramificationSubgroup_antitone A (by omega)).trans_eq h)
      rw [h1, h2]) hi

/-! ## The upper-numbered filtration: the trivially proved part -/

/-- The upper-numbered ramification subgroups are normal in the decomposition subgroup (they are
lower-numbered subgroups). -/
theorem upperRamificationSubgroup_normal (A : ValuationSubring L) (v : ℕ) :
    (upperRamificationSubgroup (K := K) A v).Normal :=
  ramificationSubgroup_normal A _

/-- The upper-numbered ramification subgroups are contained in the inertia subgroup. -/
theorem upperRamificationSubgroup_le_inertiaSubgroup (A : ValuationSubring L) (v : ℕ) :
    upperRamificationSubgroup (K := K) A v ≤ A.inertiaSubgroup K :=
  ramificationSubgroup_le_inertiaSubgroup A _

/-- `G^0 = G_0 = I` when `ψ(0) = 0`, i.e. when the Herbrand function is strictly increasing from
`0`; without that hypothesis one only knows `G^0 = G_{ψ(0)}` with `ψ(0) = 0` by definition of the
least index. -/
theorem herbrandInv_zero (A : ValuationSubring L) [Finite ↥(A.decompositionSubgroup K)] :
    herbrandInv (K := K) A 0 = 0 := by
  have h : (0 : ℚ) ≤ herbrand (K := K) A 0 := by rw [herbrand_zero]
  refine le_antisymm (Nat.sInf_le h) (Nat.zero_le _)

theorem upperRamificationSubgroup_zero (A : ValuationSubring L)
    [Finite ↥(A.decompositionSubgroup K)] :
    upperRamificationSubgroup (K := K) A 0 = ramificationSubgroup A 0 := by
  rw [upperRamificationSubgroup, herbrandInv_zero A]

end

end NK.Ramification
