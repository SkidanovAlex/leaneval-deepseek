/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Hasse–Arf theorem

For a finite Galois extension `L/K` of local fields with valuation ring `A ⊆ L`, the classical
**Hasse–Arf theorem** states that the jumps of the *upper*-numbered ramification filtration
`G^v = G_{ψ(v)}` occur only at integral values of `v`; equivalently, that the Herbrand function
`φ` takes integral values at every lower break.  In the formalisation of
`Submission/Work/Ramification/Herbrand.lean` this is the named proposition

`NK.Ramification.HasseArf A  :=  ∀ i, LowerBreak A i → ∃ m : ℕ, φ(i) = m`.

This file collects what is proved about it:

* the **reformulation** `NK.Ramification.hasseArf_iff_dvd`: at every lower break `i`, Hasse–Arf
  says `g_0 ∣ g_0 + g_1 + ⋯ + g_{i-1}`, the divisibility form in which the theorem is often stated;
* the **tamely ramified case** `NK.Ramification.hasseArf_of_tame` (`G_1 = ⊥`): the only lower break
  is `i = 0`, where `φ(0) = 0`;
* the case `G_2 = ⊥` (`NK.Ramification.hasseArf_of_ramificationSubgroup_two_eq_bot`): the only
  lower breaks are `i ∈ {0,1}`, where `φ(0) = 0` and `φ(1) = 1`.

The **general theorem is not proved in this workspace**.  Its classical proof (Hasse, *Zahlbericht*;
Serre, *Local Fields* IV §3) proceeds through the abelian case, where the Herbrand function is
computed explicitly against the unit filtration `U^i = 1 + 𝔪^i ⊆ K^×` via local reciprocity
(`rec_K` carries `U^i` onto `G^i`, Serre XV §2), followed by a transfer argument reducing the
general case to the abelian one.  The workspace has the local reciprocity input
(`Submission/Work/LocalCFT/`); the missing piece is the assembly, together with the tower
multiplicativity of `Submission/Work/Ramification/Tower.lean`.
-/
import Submission.NK.Ramification.Herbrand
import Submission.NK.Ramification.hasseArf_iff_dvd
import Submission.NK.Ramification.hasseArf_of_ramificationSubgroup_two_eq_bot
