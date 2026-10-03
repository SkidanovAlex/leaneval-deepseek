/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area

# The shift of a coset: `t · (N t^{j-1}) = N t^j`

For `N ≤ G`, `t : G` with `t` normalising `N` (`Work.ORP311.P311.TwistData N t`), the
left translation by `t` of the `N`-coset through `t ^ (j - 1)` is the `N`-coset through `t ^ j`:

`Work.ORP311.cosetShift t (Work.ORP311.coset N t (j - 1)) = Work.ORP311.coset N t j`.

Explicitly, `t * (n * t ^ (j - 1)) = (t * n * t⁻¹) * t ^ j` and conversely
`t * ((t⁻¹ * n * t) * t ^ (j - 1)) = n * t ^ j`, so the two sides have the same elements; this is
the set-level identity underlying `Work.ORP311.regBlk_ell2Sub`/`IsBlockDiag` and the block
decomposition `⊕_{j} ℓ²(N t^j)` used in [JZLA20, Proposition 3.11].
-/
import Mathlib
import Submission.Work.ORP311.P311Defs

set_option autoImplicit false

namespace Work.ORP311

section ExponentBookkeeping

variable {G : Type*} [Group G]

/-- Exponent bookkeeping for a negative shift: `t ^ (j - 1) = t⁻¹ * t ^ j`. -/
private theorem zpow_sub_one_eq_inv_mul (t : G) (j : ℤ) : t ^ (j - 1) = t⁻¹ * t ^ j := by
  rw [← zpow_neg_one t, ← zpow_add]
  congr 1
  ring

end ExponentBookkeeping

/-- **The left shift by `t` maps the coset `N t^{j-1}` onto the coset `N t^j`.**  Conjugating the
`N`-part by `t` (permitted by `TwistData`, which says `t` normalises `N`) accounts exactly for the
missing factor of `t`. -/
theorem cosetShift_coset {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G}
    (h : Work.ORP311.P311.TwistData N t) (j : ℤ) :
    Work.ORP311.cosetShift t (Work.ORP311.coset N t (j - 1)) = Work.ORP311.coset N t j := by
  ext x
  simp only [Work.ORP311.cosetShift, Work.ORP311.coset, Set.mem_ofPred_eq]
  constructor
  · -- `x = t * (n * t ^ (j-1)) = (t * n * t⁻¹) * t ^ j`
    rintro ⟨z, ⟨n, rfl⟩, rfl⟩
    refine ⟨⟨t * (n : G) * t⁻¹, h.conj n n.2⟩, ?_⟩
    rw [zpow_sub_one_eq_inv_mul]
    group
  · -- `x = n * t ^ j = t * ((t⁻¹ * n * t) * t ^ (j-1))`
    rintro ⟨n, rfl⟩
    refine ⟨((⟨t⁻¹ * (n : G) * t, h.conj_inv n n.2⟩ : N) : G) * t ^ (j - 1), ⟨_, rfl⟩, ?_⟩
    rw [zpow_sub_one_eq_inv_mul]
    group

end Work.ORP311
