/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Auxiliary vocabulary for the local Brauer computation at a `p`-adic field

This file collects the *definitions and instances* (no lemmas with proofs by `sorry`) that the
requested lemma `NK.NUV2.ABHN.localBrauerH2Card` and its delegated pieces need:

* `NK.NUV2.ABHN.instAddCommGroupH2Units` — the additive group structure on the units colimit
  `NK.HassePrinciple.H2Units V`, obtained from
  `NK.HassePrinciple.exists_addCommGroup_H2Units`, with the compatibility
  `NK.NUV2.ABHN.H2Units.ofLevel_add` of the structure maps with addition;
* `NK.NUV2.ABHN.instAddCommGroupMuColim` — the same for the `μ_p`-colimit
  `NK.HassePrinciple.MuColim p V`.

Both colimits are `Type`-valued filtered colimits; the additive structure exists by the cited
lemmas (which build it by transport along the comparison with the direct limit of the level system),
but it is not an instance, hence the need for this file.
-/

import Submission.NK.HassePrinciple.exists_addCommGroup_H2Units
import Submission.NK.HassePrinciple.exists_addCommGroup_MuColim

set_option autoImplicit false

universe u

namespace NK.NUV2.ABHN

open NK.HassePrinciple

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The additive group structure on the units colimit `H2Units V`, chosen from
`NK.HassePrinciple.exists_addCommGroup_H2Units`. -/
noncomputable instance instAddCommGroupH2Units (V : Subgroup Gal(K'/K)) :
    AddCommGroup (H2Units (K := K) (K' := K') V) :=
  (exists_addCommGroup_H2Units (K := K) (K' := K') V).choose

/-- The structure maps of the units colimit are additive. -/
theorem H2Units.ofLevel_add (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (a b : UnitsLevelH2 (K := K) (K' := K') V L) :
    H2Units.ofLevel (K := K) (K' := K') V L (a + b) =
      H2Units.ofLevel (K := K) (K' := K') V L a +
        H2Units.ofLevel (K := K) (K' := K') V L b :=
  (exists_addCommGroup_H2Units (K := K) (K' := K') V).choose_spec L a b

/-- The additive group structure on the `μ_p`-colimit `MuColim p V`, chosen from
`NK.HassePrinciple.exists_addCommGroup_MuColim`. -/
noncomputable instance instAddCommGroupMuColim (p : ℕ) (V : Subgroup Gal(K'/K)) :
    AddCommGroup (MuColim (K := K) (K' := K') p V) :=
  (exists_addCommGroup_MuColim (K := K) (K' := K') p V).choose

/-- The structure maps of the `μ_p`-colimit are additive. -/
theorem MuColim.ofLevel_add (p : ℕ) (V : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') (a b : MuLevelH2 (K := K) (K' := K') p V L) :
    MuColim.ofLevel (K := K) (K' := K') p V L (a + b) =
      MuColim.ofLevel (K := K) (K' := K') p V L a +
        MuColim.ofLevel (K := K) (K' := K') p V L b :=
  (exists_addCommGroup_MuColim (K := K) (K' := K') p V).choose_spec L a b

end NK.NUV2.ABHN
