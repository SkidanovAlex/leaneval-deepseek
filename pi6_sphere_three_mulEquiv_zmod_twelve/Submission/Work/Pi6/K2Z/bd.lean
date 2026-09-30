import Mathlib
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `K2Z` — the bidegree vocabulary of the two-row Serre spectral sequence argument

The cohomological Serre spectral sequence `CohSS 𝕜` (defined in
`Submission/Work/Pi6/Interfaces.lean`) is indexed by pairs `a : ℤ × ℤ` of integers.  In the
`K(ℤ,2)` forcing argument only the bidegrees `(s,q)` with `s q : ℕ` occur, together with the
differentials of bidegree `vr r = (r, 1-r)`.

This file fixes the notation: `bd s q = ((s : ℤ), (q : ℤ))` and the two arithmetic identities
`bd s q + vr 2 = ((s:ℤ)+2, (q:ℤ)-1)`, `bd s q - vr 2 = ((s:ℤ)-2, (q:ℤ)+1)` that describe the
`d₂`-differentials out of and into the bidegree `(s,q)`.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.K2Z

/-- The bidegree `(s,q)` of the spectral sequence, as an element of `ℤ × ℤ`. -/
def bd (s q : ℕ) : ℤ × ℤ := ((s : ℤ), (q : ℤ))

@[simp] theorem bd_fst (s q : ℕ) : (bd s q).1 = (s : ℤ) := rfl
@[simp] theorem bd_snd (s q : ℕ) : (bd s q).2 = (q : ℤ) := rfl

theorem bd_inj {s q s' q' : ℕ} (h : bd s q = bd s' q') : s = s' ∧ q = q' := by
  constructor
  · have h1 := congrArg Prod.fst h
    simp only [bd_fst] at h1
    exact_mod_cast h1
  · have h2 := congrArg Prod.snd h
    simp only [bd_snd] at h2
    exact_mod_cast h2

theorem bd_add (s q s' q' : ℕ) : bd s q + bd s' q' = bd (s + s') (q + q') := by
  ext <;> simp [bd]

theorem bd_zero_zero : bd 0 0 = (0 : ℤ × ℤ) := by ext <;> simp [bd]

theorem vr_two : Work.Pi6.vr 2 = ((2 : ℤ), -1) := rfl

theorem bd_add_vr_two (s q : ℕ) : bd s q + Work.Pi6.vr 2 = ((s : ℤ) + 2, (q : ℤ) - 1) := by
  ext <;> simp [bd, Work.Pi6.vr] <;> ring

theorem bd_sub_vr_two (s q : ℕ) : bd s q - Work.Pi6.vr 2 = ((s : ℤ) - 2, (q : ℤ) + 1) := by
  ext <;> simp [bd, Work.Pi6.vr] <;> ring

/-- The `d₂`-target of the bidegree `(s,0)` has negative second coordinate. -/
theorem bd_zero_add_vr_two_snd (s : ℕ) : (bd s 0 + Work.Pi6.vr 2).2 = -1 := by
  rw [bd_add_vr_two]; simp

/-- The bidegree of the source of the differential into `(s+2,0)`. -/
theorem bd_add_two_zero_sub_vr_two (s : ℕ) :
    bd (s + 2) 0 - Work.Pi6.vr 2 = bd s 1 := by
  rw [bd_sub_vr_two]
  ext <;> simp [bd]

end Work.Pi6.K2Z
