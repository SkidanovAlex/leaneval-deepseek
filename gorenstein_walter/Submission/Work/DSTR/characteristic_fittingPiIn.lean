import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.DSTR.map_fittingPiIn_le
import Submission.Work.CORE2A.Defs

set_option linter.style.haveILetI false

namespace Work.DSTR

open Subgroup

/-!
# `F_{2'}(K) = O_{2'}(F(K))` is characteristic in `K`

The `2'`-part `F_π(K) = O_π(F(K))` of the Fitting subgroup of a finite group is built from two
characteristic subgroups:

* `F(K)` is the join of the normal nilpotent subgroups of `K`, and an automorphism permutes those,
  so `F(K)` is characteristic in `K`.  Here we read this off from the fact — already available in
  `Submission.Work.DSTR.map_fittingPiIn_le` — that `F(-)` is transported by a surjection,
  `(F K).map f ≤ F L`; applied to an automorphism this is precisely `Characteristic`.
* `O_π(H)` is characteristic in `H` (it is the `π`-core, already proved as
  `FittingPiImg.piCore_characteristic`);
* a characteristic subgroup of a characteristic subgroup is characteristic
  (`Subgroup.characteristic_of_characteristic_of_characteristic`).

The requested statement is then bookkeeping: `(F_π(K)).subgroupOf K` is *the same subgroup* of
`↥K` as `F_π(↥K)`, because `subgroupOf` is `comap` along `K.subtype` and `K.subtype` is injective.
-/

namespace FittingPiImg

/-- **`F(K)` is characteristic in `K`.**  An automorphism carries normal nilpotent subgroups to
normal nilpotent subgroups, so it permutes the set whose join is the Fitting subgroup; formally,
`(F K).map f ≤ F K` for every automorphism `f`, which is `Characteristic`. -/
theorem fitting_characteristic {G : Type*} [Group G] [Finite G] :
    (Work.GW2.fitting G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  exact fitting_map_le_of_surjective φ.toMonoidHom φ.surjective

/-- **`F_π(K) = O_π(F(K))` is characteristic in `K`.**  It is the image in `K` of the
characteristic subgroup `O_π(F(K))` of the characteristic subgroup `F(K) ≤ K`. -/
theorem fittingPi_characteristic {G : Type*} [Group G] [Finite G] (π : Set ℕ) :
    (Work.GW2.fittingPi π G).Characteristic := by
  haveI hF : (Work.GW2.fitting G).Characteristic := fitting_characteristic
  haveI hP : (Work.GW2.piCore π ↥(Work.GW2.fitting G)).Characteristic :=
    piCore_characteristic π
  exact Subgroup.characteristic_of_characteristic_of_characteristic
    (H := Work.GW2.fitting G) (K := Work.GW2.piCore π ↥(Work.GW2.fitting G))

end FittingPiImg

open FittingPiImg

/-- **`F_{2'}(K) = O_{2'}(F(K))` is characteristic in `K`.**

(Taking `K = C_G(t)`, this supplies the `Characteristic` hypothesis of the crux
`Work.DSTR.conj_le_sup_of_characteristic_odd`, whose instance `A = F_{2'}(C_G(t))` is the target
`Work.DSTR.fittingPiIn_conj_le`.) -/
theorem characteristic_fittingPiIn {G : Type*} [Group G] [Finite G] (K : Subgroup G) :
    ((Work.GW2.fittingPiIn {k : ℕ | k ≠ 2} K).subgroupOf K).Characteristic := by
  -- `(F_{2'}(K)).subgroupOf K` *is* `F_{2'}(↥K)`
  have heq : (Work.GW2.fittingPiIn {k : ℕ | k ≠ 2} K).subgroupOf K
      = Work.GW2.fittingPi {k : ℕ | k ≠ 2} ↥K := by
    show ((Work.GW2.fittingPi {k : ℕ | k ≠ 2} ↥K).map K.subtype).comap K.subtype = _
    rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  rw [heq]
  exact fittingPi_characteristic {k : ℕ | k ≠ 2}

end Work.DSTR
