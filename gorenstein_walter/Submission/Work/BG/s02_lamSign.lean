import Mathlib
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.s02_quotCyclic

/-!
# Area BG: a linear character of `H₀/U` taking the value `-1` at `tU`

`H₀/U` is a cyclic `2`-group with a unique involution `q = tU = t·U` (BG §2).  As a finite
abelian group it therefore has a linear character `β : H₀/U →* ℂˣ` with `β q = -1`: take any
linear character not vanishing at `q` (duality of finite abelian groups separates points,
`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`) — its value at the involution `q`
squares to `1` and differs from `1`, hence equals `-1`.

This is the "reflection" character `λ₁` of the proof of BG Lemma 1.7(iii) / the choice
`θ₂(t) = -ν(t)` of Lemma 2.1-d.
-/

namespace Work.BG

set_option linter.style.haveILetI false

theorem s02_lamSign {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G) :
    ∃ β : Work.BG.lamDual C, β (Work.BG.tU C) = -1 := by
  classical
  -- `H₀/U` is abelian (it is cyclic), so it carries a `CommGroup` structure.
  haveI : IsMulCommutative (quotGroup C.P) :=
    ⟨⟨fun x y => mul_comm_quotGroup C x y⟩⟩
  letI : CommGroup (quotGroup C.P) := IsMulCommutative.instCommGroup
  -- Duality separates `tU` from `1`.
  obtain ⟨β, hβ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    (quotGroup C.P) ℂ (a := tU C) (tU_ne_one C)
  refine ⟨β, ?_⟩
  -- `tU` is an involution, so `β (tU)² = 1`, and `β (tU) ≠ 1`, so `β (tU) = -1`.
  have hsq : β (tU C) * β (tU C) = 1 := by
    rw [← map_mul, ← pow_two, tU_sq, map_one]
  have h2 : ((β (tU C) : ℂ)) ^ 2 = 1 := by
    have := congrArg (fun x : ℂˣ => (x : ℂ)) hsq
    simpa [pow_two] using this
  rcases (sq_eq_one_iff.mp h2) with h1 | h1
  · exact absurd h1 (by intro hc'; exact hβ (Units.ext hc'))
  · simpa using h1

end Work.BG
