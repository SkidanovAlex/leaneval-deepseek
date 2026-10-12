import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.Order.Star.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.boseDefs` — an honest bosonic Fock space carrying the `B4` interface

`Work.BoseB7.FockData` (`FockDefs.lean`) is an *axiomatisation* of the bosonic
second quantisation of the box Hamiltonian.  This module starts the construction
of a **genuine model**: the free (non-interacting) bosonic Fock space over a
finite mode set `Mode`, in the occupation-number representation, together with

* the annihilation operators `bAnn i` (`a_k`), which act on the occupation
  vector `m` by removing one quantum of mode `i` with weight `√(m i)`;
* the creation operators `bCre i` (`a_k†`), which add one quantum with weight
  `√(m i + 1)`.

With the ℓ² form of `Work.BoseB7.l2Form`,
`⟨bCre i f, g⟩ = ⟨f, bAnn i g⟩`, and the canonical commutation relation
`[bAnn i, bCre j] = δ_{ij}` holds, so these operators instantiate `FockData`
(see `Work.BoseB7.fockModel_nonempty`) with the *non-zero* commutator kernel
`ccrK i j = if i = j then 1 else 0` — i.e. with the genuinely bosonic
commutator, not with a degenerate one.

## Representation

The Fock space is `boseH Mode = occIdx Mode →₀ ℝ`, where an occupation vector
`m : occIdx Mode` assigns to every mode a finite occupation number.  (The
definition is `ULift.{v,u} (Mode →₀ ℕ)` rather than `Mode →₀ ℕ` only so that the
Fock carrier lives in the universe `max u v` of the interface's `H`; the
identification with `Mode →₀ ℕ` is `ULift.down`.)  A state is a *finitely*
supported real function of the occupation vector — the algebraic (finite
particle-number) core, on which all the creation/annihilation operators are
everywhere defined.

The ℓ² form `l2Form` lives in `Work.BoseB7.l2Form`; the pointwise form of the
ladder operators, the commutators and the adjointness are in
`Work.BoseB7.boseApply`, `Work.BoseB7.boseCCR`, `Work.BoseB7.boseAdjoint`.

## Contents

* `occIdx`, `boseH` — the occupation-vector index and the Fock space.
* `occ`, `inc`, `dec` — occupation number, addition/removal of one quantum of a
  mode (the latter with truncated subtraction).
* `bCre`, `bAnn` — the creation/annihilation operators.
* the arithmetic of `inc`/`dec`/`occ` (`occ_inc_self` … `inc_dec_comm`), which is
  the whole combinatorial content of the commutation relations.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

universe u v

/-- Occupation-number vectors of the mode set `Mode`, in the universe of the Fock
carrier.  `occIdx Mode = ULift (Mode →₀ ℕ)`; we use `ULift` so that the Fock space
`boseH Mode` can live in an arbitrary universe. -/
abbrev occIdx (Mode : Type u) : Type (max u v) := ULift.{v, u} (Mode →₀ ℕ)

/-- **The free bosonic Fock space** over `Mode`, in the occupation-number
representation: finitely supported real functions of the occupation vector, i.e.
the algebraic core `⨁_m ℝ·|m⟩` of finite particle number. -/
abbrev boseH (Mode : Type u) : Type (max u v) := occIdx.{u, v} Mode →₀ ℝ

section

variable {Mode : Type u}

/-- The occupation number of the mode `i` in the occupation vector `m`. -/
def occ (i : Mode) (m : occIdx.{u, v} Mode) : ℕ := m.down i

/-- `inc i m`: the occupation vector obtained from `m` by adding one quantum of the
mode `i`. -/
def inc (i : Mode) (m : occIdx.{u, v} Mode) : occIdx.{u, v} Mode :=
  ULift.up (m.down + Finsupp.single i (1 : ℕ))

/-- `dec i m`: the occupation vector obtained from `m` by removing one quantum of
the mode `i` (truncated: if the mode `i` is unoccupied, `dec i m = m`). -/
def dec (i : Mode) (m : occIdx.{u, v} Mode) : occIdx.{u, v} Mode :=
  ULift.up (m.down - Finsupp.single i (1 : ℕ))

/-- **Creation operator** `a_i†` of the mode `i`: with `|m⟩` the occupation-number
basis vector, `bCre i |m⟩ = √(m i + 1)·|inc i m⟩`. -/
def bCre (i : Mode) : boseH.{u, v} Mode →ₗ[ℝ] boseH.{u, v} Mode :=
  Finsupp.lsum ℝ (fun m : occIdx.{u, v} Mode =>
    (Real.sqrt ((occ i m : ℝ) + 1)) • Finsupp.lsingle (inc i m))

/-- **Annihilation operator** `a_i` of the mode `i`: with `|m⟩` the occupation-number
basis vector, `bAnn i |m⟩ = √(m i)·|dec i m⟩`. -/
def bAnn (i : Mode) : boseH.{u, v} Mode →ₗ[ℝ] boseH.{u, v} Mode :=
  Finsupp.lsum ℝ (fun m : occIdx.{u, v} Mode =>
    (Real.sqrt ((occ i m : ℝ))) • Finsupp.lsingle (dec i m))

/-! ## The occupation-number arithmetic of `inc`, `dec`, `occ` -/

lemma occ_inc_self (i : Mode) (m : occIdx.{u, v} Mode) : occ i (inc i m) = occ i m + 1 := by
  simp [occ, inc, Finsupp.add_apply, Finsupp.single_eq_same]

lemma occ_inc_ne {i j : Mode} (h : i ≠ j) (m : occIdx.{u, v} Mode) :
    occ i (inc j m) = occ i m := by
  simp only [occ, inc, ULift.down_up, Finsupp.add_apply, Finsupp.single_eq_of_ne h, add_zero]

lemma occ_dec_ne {i j : Mode} (h : i ≠ j) (m : occIdx.{u, v} Mode) :
    occ i (dec j m) = occ i m := by
  simp only [occ, dec, ULift.down_up, Finsupp.tsub_apply, Finsupp.single_eq_of_ne h, tsub_zero]

lemma occ_dec_self {i : Mode} (m : occIdx.{u, v} Mode) (h : 0 < occ i m) :
    occ i (dec i m) + 1 = occ i m := by
  simp only [occ, dec, ULift.down_up, Finsupp.tsub_apply, Finsupp.single_eq_same] at h ⊢
  omega

/-- Removing a quantum that has just been added gives back the occupation vector. -/
lemma dec_inc_self (i : Mode) (m : occIdx.{u, v} Mode) : dec i (inc i m) = m := by
  simp only [dec, inc, ULift.down_up]
  ext k
  simp only [Finsupp.tsub_apply, Finsupp.add_apply]
  by_cases h : k = i
  · rw [h]; simp
  · rw [Finsupp.single_eq_of_ne h]; simp

/-- Adding a quantum of an occupied mode after removing one gives back the
occupation vector. -/
lemma inc_dec_self {i : Mode} (m : occIdx.{u, v} Mode) (h : 0 < occ i m) :
    inc i (dec i m) = m := by
  simp only [occ, ULift.down_up, Finsupp.tsub_apply, Finsupp.single_eq_same] at h
  simp only [dec, inc, ULift.down_up]
  ext k
  simp only [Finsupp.add_apply, Finsupp.tsub_apply]
  by_cases hk : k = i
  · rw [hk, Finsupp.single_eq_same, tsub_add_cancel_of_le (by omega)]
  · rw [Finsupp.single_eq_of_ne hk]; simp

lemma inc_inc_comm (i j : Mode) (m : occIdx.{u, v} Mode) : inc i (inc j m) = inc j (inc i m) := by
  simp only [inc, ULift.down_up]
  rw [add_assoc, add_assoc, add_comm (Finsupp.single i (1 : ℕ)) (Finsupp.single j (1 : ℕ))]

lemma dec_dec_comm (i j : Mode) (m : occIdx.{u, v} Mode) : dec i (dec j m) = dec j (dec i m) := by
  simp only [dec, ULift.down_up]
  ext k
  simp only [Finsupp.tsub_apply]
  by_cases hki : k = i
  · rw [hki]
    by_cases hij : i = j
    · rw [hij]
    · simp only [Finsupp.single_eq_of_ne hij, Finsupp.single_eq_same, tsub_zero] <;> omega
  · by_cases hkj : k = j
    · rw [hkj]
      simp only [Finsupp.single_eq_of_ne (Ne.symm hki), Finsupp.single_eq_same] <;> omega
    · simp only [Finsupp.single_eq_of_ne hki, Finsupp.single_eq_of_ne hkj, tsub_zero] <;> omega

/-- Adding a quantum of `j` and removing one of `i` (`i ≠ j`) commute: the modes are
independent. -/
lemma inc_dec_comm {i j : Mode} (h : i ≠ j) (m : occIdx.{u, v} Mode) :
    inc j (dec i m) = dec i (inc j m) := by
  simp only [inc, dec, ULift.down_up]
  ext k
  simp only [Finsupp.add_apply, Finsupp.tsub_apply]
  by_cases hki : k = i
  · rw [hki]
    simp only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne h, add_zero] <;> omega
  · by_cases hkj : k = j
    · rw [hkj]
      simp only [Finsupp.single_eq_of_ne (Ne.symm h), Finsupp.single_eq_same, add_zero] <;> omega
    · simp only [Finsupp.single_eq_of_ne hki, Finsupp.single_eq_of_ne hkj, add_zero, tsub_zero]
      <;> omega

end

end Work.BoseB7
