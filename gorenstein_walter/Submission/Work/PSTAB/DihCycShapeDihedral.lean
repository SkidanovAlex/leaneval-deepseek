/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PSTAB area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.PSTAB.Defs
import Submission.Work.Dihedral.Defs

/-!
# `DihedralGroup n` has cyclic-or-dihedral shape (area PSTAB)

Base case of the trio of shape lemmas used by PSTAB to transfer `DihOrCycSylow` to sections:

* `DihCycShapeDihedral` (this file): `DihedralGroup n`;
* `DihCycShapeSubgroup`: subgroups;
* `DihCycShapeSurjective`: quotients (surjective images).

The witness is the rotation subgroup `Work.Dihedral.rot n = ⟨r⟩` (the range of
`i ↦ r i`), whose API lives in `Submission/Work/Dihedral/Defs.lean`:

* `rot_normal n` — `⟨r⟩ ◁ DihedralGroup n` (a reflection conjugates `r i` to `r (-i)`);
* `instIsCyclicRot n` — `⟨r⟩` is cyclic, being a surjective image of `Multiplicative (ZMod n)`;
* `notMem_rot` — the elements outside `⟨r⟩` are exactly the reflections `sr i`;
* `sr_mul_sr_mem_rot` — a product of two reflections is a rotation (`sr i * sr j = r (j - i)`);
* `DihedralGroup.sr_mul_self` — every reflection is an involution.

This holds for every `n : ℕ`, including `n = 0` (infinite dihedral group) and the degenerate
cases `n = 1` (cyclic of order `2`), `n = 2` (Klein four-group).
-/

namespace Work.PSTAB

/-- `DihedralGroup n` has the weak cyclic-or-dihedral shape `DihCycShape` of the area `PSTAB`,
with witness the (normal, cyclic) rotation subgroup `⟨r⟩`: every element outside `⟨r⟩` is a
reflection, hence an involution, and a product of two reflections is a rotation again. -/
theorem DihCycShapeDihedral (n : ℕ) : Work.PSTAB.DihCycShape (DihedralGroup n) := by
  refine ⟨Work.Dihedral.rot n, Work.Dihedral.rot_normal n, Work.Dihedral.instIsCyclicRot n,
    ?_, ?_⟩
  · intro g hg
    obtain ⟨i, rfl⟩ := Work.Dihedral.notMem_rot.mp hg
    rw [pow_two, DihedralGroup.sr_mul_self]
  · intro g h hg hh
    obtain ⟨i, rfl⟩ := Work.Dihedral.notMem_rot.mp hg
    obtain ⟨j, rfl⟩ := Work.Dihedral.notMem_rot.mp hh
    exact Work.Dihedral.sr_mul_sr_mem_rot i j

end Work.PSTAB
