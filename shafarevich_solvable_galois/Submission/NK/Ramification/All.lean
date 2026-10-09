/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.Ramification`: the higher ramification theory of a `p`-adic field

Import everything in this chapter with `import Submission.NK.Ramification.All`.

## Contents

* **`Defs`** — the higher ramification subgroups `G_i` in lower numbering for a valuation subring
  `A` of a field extension `L/K` (`NK.Ramification.ramificationSubgroup`), with the classical
  dictionary: `G_0 = I` is Mathlib's `A.inertiaSubgroup K`, the `G_i` are normal and decrease,
  and their intersection is trivial (`iInf_ramificationSubgroup_eq_bot`, Krull).
* **`Herbrand`** — the lower indices `g_i = #G_i`, the Herbrand function `φ`
  (`NK.Ramification.herbrand`), its inverse `ψ` (`herbrandInv`), the upper-numbered filtration
  `G^v = G_{ψ(v)}` (`upperRamificationSubgroup`), the break predicates `LowerBreak`/`UpperBreak`,
  and the Hasse–Arf statement `NK.Ramification.HasseArf` (with the tamely ramified case proved,
  `hasseArf_of_tame`).
* **`Determined`** — what the filtration determines: the Herbrand function and the breaks
  (`herbrand_eq_of_lowerIndex_eq`, `lowerBreak_iff_lowerIndex_lt`), the tameness criterion
  (`IsTamelyRamified`, `herbrand_of_tame`), and the invariance of the filtration, the lower
  indices and `φ` under isomorphisms of valued fields (`lowerIndex_eq_of_map_conj`,
  `herbrand_eq_of_map_conj`).
* **`Adic`** — the specialisation to the local Galois group `Gal(L_q/K_Q)` of the workspace's
  `p`-adic fields (`adicRamificationSubgroup`), with `adicRamificationSubgroup_zero = I`,
  `natCard_ramificationSubgroup_zero_adicCompletion` (`#G_0 = e(q|Q)`) and
  `exists_adicRamificationSubgroup_eq_bot` (the filtration is eventually trivial).
* **`Headline`** — Neukirch's *Kennzeichnung* in the form consumed by this workspace:
  `NK.Ramification.NeukirchKennzeichnung` is Neukirch's local theorem for a *continuous*
  isomorphism of absolute Galois groups, and it is proved equivalent to
  `NK.LocalStructure.LocalFieldFromFiniteExtensionLattice` (and, modulo the existence of lattice
  correspondences, to `NK.LocalStructure.LocalNUExistence`).
* **`Satisfiability`** — the audit that the chapter adds no new false or empty input.

## Result names

The main declarations are

```
NK.Ramification.ramificationSubgroup            -- G_i, lower numbering
NK.Ramification.ramificationSubgroup_zero       -- G_0 = inertia
NK.Ramification.ramificationSubgroup_normal
NK.Ramification.ramificationSubgroup_antitone
NK.Ramification.iInf_ramificationSubgroup_eq_bot
NK.Ramification.exists_ramificationSubgroup_eq_bot
NK.Ramification.lowerIndex                      -- g_i = #G_i
NK.Ramification.herbrand                        -- φ
NK.Ramification.herbrandInv                     -- ψ = φ⁻¹
NK.Ramification.upperRamificationSubgroup       -- G^v
NK.Ramification.HasseArf                        -- Hasse–Arf
NK.Ramification.IsTamelyRamified
NK.Ramification.adicRamificationSubgroup        -- G_i of Gal(L_q/K_Q)
NK.Ramification.NeukirchKennzeichnung           -- the headline
NK.Ramification.neukirchKennzeichnung_iff_localFieldFromFiniteExtensionLattice'
NK.Ramification.localFieldFromFiniteExtensionLattice_of_localNUExistence
NK.Ramification.localFieldFromFiniteExtensionLattice_iff_localNUExistence
NK.Ramification.FiltrationDetectedByLattice                -- Neukirch's hard step
NK.Ramification.RamificationDeterminesLocalField           -- the filtration determines the field
NK.Ramification.localFieldFromFiniteExtensionLattice_of_detection_and_ramification
NK.Ramification.localFieldFromFiniteExtensionLattice_iff_ramificationDeterminesLocalField
NK.Ramification.finiteExtensionIntegers                    -- valuation ring of a finite extension
NK.Ramification.levelIndex / levelIndexOver                -- lower indices g_i of a level
NK.Ramification.FiltrationCorresponds
NK.Ramification.herbrandRat / HerbrandMultiplicativity
NK.Ramification.hasseArf_iff_dvd / hasseArf_of_tame
```

Everything here is `sorry`-free and axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.CommonsBridge
import Submission.NK.Ramification.Herbrand
import Submission.NK.Ramification.Determined
import Submission.NK.Ramification.Adic
import Submission.NK.Ramification.Filtration
import Submission.NK.Ramification.Tower
import Submission.NK.Ramification.hasseArf_of_subsingleton
import Submission.NK.Ramification.hasseArf_of_one_eq_zero_and_three_eq_bot
import Submission.NK.Ramification.herbrandRat_eq_id_of_forall_eq_bot
import Submission.NK.Ramification.herbrandMultiplicativity_bot
import Submission.NK.Ramification.HasseArf
import Submission.NK.Ramification.RamificationKennzeichnung
import Submission.NK.Ramification.Headline
import Submission.NK.Ramification.Satisfiability
import Submission.NK.Ramification.exists_ramificationSubgroup_eq_bot
import Submission.NK.Ramification.exists_adicRamificationSubgroup_eq_bot
import Submission.NK.Ramification.herbrand_strictMono
import Submission.NK.Ramification.herbrandInv_le_iff
import Submission.NK.Ramification.herbrand_of_tame
import Submission.NK.Ramification.lowerBreak_iff_lowerIndex_lt
import Submission.NK.Ramification.lowerIndex_le_zero
import Submission.NK.Ramification.upperRamificationSubgroup_antitone
import Submission.NK.Ramification.ramificationSubgroup_map_conj
import Submission.NK.Ramification.continuous_of_finiteExtensionCorrespondence
import Submission.NK.Ramification.natCard_ramificationSubgroup_zero_adicCompletion
import Submission.NK.Ramification.exists_valuationSubring_finiteDimensional
import Submission.NK.Ramification.hasseArf_iff_dvd
import Submission.NK.Ramification.herbrandInv_monotone
import Submission.NK.Ramification.lowerIndex_eq_one_iff
import Submission.NK.Ramification.ramificationSubgroup_eq_top_of_subsingleton
import Submission.NK.Ramification.isProP_of_natCard_eq_prime_pow
import Submission.NK.Ramification.hasseArf_of_ramificationSubgroup_two_eq_bot
import Submission.NK.Ramification.tame_iff_herbrand_linear
import Submission.NK.Ramification.le_subgroup_of_isProP_of_coprime_quotient
import Submission.NK.Ramification.smul_sub_mem_maximalIdeal_pow
import Submission.NK.Ramification.isWildInertia_ramificationSubgroup_one
import Submission.NK.Ramification.ramificationSubgroup_succ_eq_of_uniformizer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
