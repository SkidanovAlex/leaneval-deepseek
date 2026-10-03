import Mathlib
import Submission.Work.OROneRel.gaugeExtWindowDefs

/-!
# Arithmetic of the upward `x₀`-chain base maps

`gxUpBase d hi j = j - (((j - hi - 1) / d) + 1) * d` and
`gxUpExp d hi j = ((j - hi - 1) / d) + 1`

(`Int` division is Euclidean, so `(j - hi - 1) / d` is the floor of `(j - hi - 1)/d`).
The two closed forms are recognised here through `Int.emod`:

* `gxUpExp d hi j = -((hi - j) / d)`, i.e. it is `⌈(j - hi)/d⌉`;
* `gxUpBase d hi j = hi - (hi - j) % d`, the unique element of `(hi - d, hi]` congruent to `j`
  modulo `d`.

Everything in `gxUpBase_arith` is then immediate: the chain decomposes `j` as its base level plus
`gxUpExp` upward steps of length `d`, the base level stays in `(hi - d, hi]`, and shifting a base
level by a nonnegative multiple of `d` leaves both the base level and the exponent unchanged (the
exponent of the shift being exactly the number of steps taken).
-/

namespace Work.OROneRel

/-- The number of upward `x₀`-steps from `hi` to `j`, read as a floor: shifting `j` down by `1` and
dividing by `d`.  The key rewrite is `(j - hi - 1) / d = -((hi - j) / d) - 1`, i.e.
`⌊(m - 1)/d⌋ = -⌊-m/d⌋ - 1` for `m = j - hi`. -/
private lemma gxUp_ediv_key {d hi j : ℤ} (hd : 0 < d) :
    (j - hi - 1) / d = -((hi - j) / d) - 1 := by
  have hr0 : 0 ≤ (hi - j) % d := Int.emod_nonneg _ hd.ne'
  have hrd : (hi - j) % d < d := Int.emod_lt_of_pos _ hd
  have hmul : (hi - j) % d + d * ((hi - j) / d) = hi - j := Int.emod_add_mul_ediv _ _
  -- `j - hi - 1 = (d - (hi - j) % d - 1) + d * (-((hi - j) / d) - 1)` is a Euclidean division
  -- with the remainder `d - (hi - j) % d - 1 ∈ [0, d)`.
  have hiff := Int.ediv_emod_unique hd (a := j - hi - 1) (b := d)
    (q := -((hi - j) / d) - 1) (r := d - (hi - j) % d - 1)
  refine (hiff.mpr ⟨?_, ?_, ?_⟩).1
  · have hexp : d * (-((hi - j) / d) - 1) = -(d * ((hi - j) / d)) - d := by ring
    rw [hexp]
    linarith
  · linarith
  · linarith

/-- **Closed form of the exponent**: `gxUpExp d hi j = ⌈(j - hi)/d⌉ = -((hi - j) / d)`. -/
lemma gxUpExp_eq_neg {d hi j : ℤ} (hd : 0 < d) :
    gxUpExp d hi j = -((hi - j) / d) := by
  simp only [gxUpExp]
  rw [gxUp_ediv_key hd]
  ring

/-- **Closed form of the base level**: `gxUpBase d hi j` is `hi` minus the least nonnegative
residue of `hi - j` modulo `d`, i.e. the unique element of `(hi - d, hi]` congruent to `j`. -/
lemma gxUpBase_eq_sub_emod {d hi j : ℤ} (hd : 0 < d) :
    gxUpBase d hi j = hi - (hi - j) % d := by
  have hmul : (hi - j) % d + d * ((hi - j) / d) = hi - j := Int.emod_add_mul_ediv _ _
  have hmul' : d * ((hi - j) / d) = (hi - j) - (hi - j) % d := by linarith
  simp only [gxUpBase]
  rw [gxUp_ediv_key hd,
    show (-((hi - j) / d) - 1 + 1) = -((hi - j) / d) by ring,
    show (-((hi - j) / d)) * d = -(d * ((hi - j) / d)) by ring, hmul']
  ring

theorem gxUpBase_arith {d hi j : ℤ} (hd : 0 < d) :
    (Work.OROneRel.gxUpBase d hi j + Work.OROneRel.gxUpExp d hi j * d = j) ∧
    (hi - d + 1 ≤ Work.OROneRel.gxUpBase d hi j ∧ Work.OROneRel.gxUpBase d hi j ≤ hi) ∧
    (∀ m : ℤ, 0 ≤ m → Work.OROneRel.gxUpBase d hi (Work.OROneRel.gxUpBase d hi j + m * d)
      = Work.OROneRel.gxUpBase d hi j) ∧
    (∀ m : ℤ, 0 ≤ m → Work.OROneRel.gxUpExp d hi (Work.OROneRel.gxUpBase d hi j + m * d) = m) ∧
    (hi < j → 1 ≤ Work.OROneRel.gxUpExp d hi j) := by
  have hB : Work.OROneRel.gxUpBase d hi j = hi - (hi - j) % d := gxUpBase_eq_sub_emod hd
  have hr0 : 0 ≤ (hi - j) % d := Int.emod_nonneg _ hd.ne'
  have hrd : (hi - j) % d < d := Int.emod_lt_of_pos _ hd
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- the chain from the base level to `j` consists of `gxUpExp` steps of length `d`
    simp only [Work.OROneRel.gxUpBase, Work.OROneRel.gxUpExp]
    ring
  · rw [hB]; linarith
  · rw [hB]; linarith
  · -- the base level of a base level shifted up by `m` steps is the same base level
    intro m _
    have hB' : Work.OROneRel.gxUpBase d hi (Work.OROneRel.gxUpBase d hi j + m * d)
        = hi - (hi - (Work.OROneRel.gxUpBase d hi j + m * d)) % d := gxUpBase_eq_sub_emod hd
    rw [hB', hB]
    have hmod : ((hi - j) % d - m * d) % d = (hi - j) % d := by
      have hiff := Int.ediv_emod_unique hd (a := (hi - j) % d - m * d) (b := d)
        (q := -m) (r := (hi - j) % d)
      exact (hiff.mpr ⟨by ring, hr0, hrd⟩).2
    have harg : hi - ((hi - (hi - j) % d) + m * d) = (hi - j) % d - m * d := by ring
    rw [harg, hmod]
  · -- shifting the base level up by `m` steps makes the exponent exactly `m`
    intro m _
    have hE' : Work.OROneRel.gxUpExp d hi (Work.OROneRel.gxUpBase d hi j + m * d)
        = -((hi - (Work.OROneRel.gxUpBase d hi j + m * d)) / d) := gxUpExp_eq_neg hd
    rw [hE', hB]
    have hdiv : ((hi - j) % d - m * d) / d = -m := by
      have hiff := Int.ediv_emod_unique hd (a := (hi - j) % d - m * d) (b := d)
        (q := -m) (r := (hi - j) % d)
      exact (hiff.mpr ⟨by ring, hr0, hrd⟩).1
    have harg : hi - ((hi - (hi - j) % d) + m * d) = (hi - j) % d - m * d := by ring
    rw [harg, hdiv]
    ring
  · -- above the window the chain is nonempty
    intro hj
    rw [gxUpExp_eq_neg hd]
    have hlt : (hi - j) / d < 0 := by
      refine (Int.ediv_lt_iff_lt_mul (a := hi - j) (b := 0) (c := d) hd).mpr ?_
      rw [Int.zero_mul]; linarith
    linarith

end Work.OROneRel
