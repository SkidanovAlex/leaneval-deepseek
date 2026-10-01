import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.OtherCharRepel.completedLFunction_analyticOrderAt_ne_top

namespace Work.LinnikAreas.FarRepel

open DirichletCharacter

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- `completedLFunction` is compatible with rewriting the level of a Dirichlet character along an
equality of levels. -/
private lemma completedLFunction_cast {n m : ℕ} [NeZero n] [NeZero m] (h : n = m)
    (ψ : DirichletCharacter ℂ n) :
    DirichletCharacter.completedLFunction ψ = DirichletCharacter.completedLFunction (h ▸ ψ) := by
  cases h
  rfl

/-- Evaluation of a Dirichlet character whose level has been rewritten along an equality of
levels: it is the original character evaluated at the corresponding cast. -/
private lemma castDirichlet_apply {n m : ℕ} (h : n = m) (ψ : DirichletCharacter ℂ n)
    (y : (ZMod m)ˣ) : (h ▸ ψ) (↑y : ZMod m) = ψ (ZMod.cast (↑y : ZMod m) : ZMod n) := by
  cases h
  simp [ZMod.cast_id]

/-- A primitive character of level `q` (i.e. `χ.conductor = q`) coincides with the primitive
character inducing it, once the latter's level `χ.conductor` is rewritten to `q`. -/
private lemma cast_primitiveCharacter {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (h : χ.conductor = q) : h ▸ χ.primitiveCharacter = χ := by
  ext1 y
  rw [castDirichlet_apply h χ.primitiveCharacter y,
    ← DirichletCharacter.changeLevel_eq_cast_of_dvd χ.primitiveCharacter
      χ.conductor_dvd_level y,
    DirichletCharacter.changeLevel_primitiveCharacter]

/-- **The exceptional zero has multiplicity at least one in `zeroMult`.** (module `Submission.Work.LinnikAreas.FarRepel.zeroMult_beta_one_le`; declare in `namespace Work.LinnikAreas.FarRepel`; import `Submission.Work.LinnikContract.Defs` and `Mathlib`.)

If `χ` is a non-principal **primitive** Dirichlet character mod `q` and `β` is a real zero of its
completed `L`-function, then `β` has multiplicity at least one as a non-trivial zero in the sense of
`Work.LinnikContract.zeroMult` (`= analyticOrderNatAt (completedLFunction χ.primitiveCharacter)`):

`1 ≤ Work.LinnikContract.zeroMult χ (β : ℂ)`.

PROOF ROUTE: `zeroMult χ u = analyticOrderNatAt (completedLFunction χ.primitiveCharacter) u`, and
`χ.primitiveCharacter = χ` because `χ.IsPrimitive` says `conductor χ = q` (for a primitive
character the inducing primitive character is itself: apply
`DirichletCharacter.changeLevel_injective` to `changeLevel_primitiveCharacter`, or use the cast
`completedLFunction_cast` along `χ.conductor = q` — cf. the pattern in
`Submission/Work/A7/completedLFunction_primitiveCharacter_inv.lean`, whose proof shows how to
transport along the level equality using `cases h; rfl`).  Then
`analyticOrderNatAt (completedLFunction χ) β ≠ 0`: `analyticOrderAt f z ≠ 0 ↔ AnalyticAt f z ∧ f z = 0`
(`analyticOrderAt_ne_zero`) and `analyticOrderAt f z ≠ ⊤` since `completedLFunction χ` is entire and
not locally zero (it is nonzero at `2`, `LSeries_ne_zero_of_one_lt_re`); hence the `toNat` is
nonzero, and `Nat.pos_iff_ne_zero` gives `1 ≤ ⋯`. -/
theorem zeroMult_beta_one_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {β : ℝ} (hβ : β < 1)
    (hz : DirichletCharacter.completedLFunction χ (β : ℂ) = 0) :
    1 ≤ Work.LinnikContract.zeroMult χ (β : ℂ) := by
  -- the primitive character inducing a non-principal character is non-principal
  have hpc : χ.primitiveCharacter ≠ 1 := by
    intro h1
    have h2 := χ.changeLevel_primitiveCharacter
    rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at h2
    exact hχ h2.symm
  -- the level of the primitive character is `q`
  have hcond : χ.conductor = q := hprim
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  -- the completed L-functions of `χ` and of its primitive character agree
  have hfun : DirichletCharacter.completedLFunction χ.primitiveCharacter
      = DirichletCharacter.completedLFunction χ := by
    rw [completedLFunction_cast hcond χ.primitiveCharacter]
    rw [cast_primitiveCharacter χ hcond]
  -- hence `β` is a zero of the completed L-function of the primitive character
  have hz' : DirichletCharacter.completedLFunction χ.primitiveCharacter (β : ℂ) = 0 := by
    rw [hfun]
    exact hz
  -- the vanishing order is a positive natural number
  rw [Work.LinnikContract.zeroMult]
  refine ENat.toNat_pos ?_ ?_
  · rw [analyticOrderAt_ne_zero]
    exact ⟨(differentiable_completedLFunction hpc).analyticAt (β : ℂ), hz'⟩
  · exact Work.LinnikAreas.OtherCharRepel.completedLFunction_analyticOrderAt_ne_top
      χ.primitiveCharacter hpc (β : ℂ)

end Work.LinnikAreas.FarRepel
