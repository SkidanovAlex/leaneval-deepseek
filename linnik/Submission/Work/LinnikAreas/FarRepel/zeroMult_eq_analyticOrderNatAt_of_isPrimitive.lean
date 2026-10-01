import Mathlib
import Submission.Work.LinnikContract.Defs

namespace Work.LinnikAreas.FarRepel

open DirichletCharacter

/-- Transport of the completed `L`-function along an equality of levels: if `n = m`, then
the completed `L`-function of a character of level `n` agrees with that of the same character
viewed at level `m` via `changeLevel`. -/
private lemma completedLFunction_changeLevel_of_eq {n m : ℕ} [NeZero n] [NeZero m]
    (h : n = m) (ψ : DirichletCharacter ℂ n) :
    (fun s => completedLFunction (N := n) ψ s)
      = fun s => completedLFunction (N := m) (changeLevel (dvd_of_eq h) ψ) s := by
  cases h
  rw [Subsingleton.elim (dvd_of_eq rfl) (dvd_refl n), changeLevel_self]

/-- If the conductor of `χ` equals its level `q`, then the primitive character inducing `χ`,
transported up to level `q`, is `χ` itself. -/
private lemma changeLevel_conductor_primitiveCharacter {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (h : χ.conductor = q) :
    changeLevel (dvd_of_eq h) χ.primitiveCharacter = χ := by
  rw [Subsingleton.elim (dvd_of_eq h) χ.conductor_dvd_level, changeLevel_primitiveCharacter]

/-- **For a primitive character, `zeroMult` is the vanishing order of `completedLFunction χ` at level `q`.** (module `Submission.Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive`; declare in `namespace Work.LinnikAreas.FarRepel`.)

`Work.LinnikContract.zeroMult χ u` is *defined* as `analyticOrderNatAt (completedLFunction χ.primitiveCharacter) u`, where the primitive character `χ.primitiveCharacter` is a `DirichletCharacter ℂ χ.conductor`, i.e. it lives at the conductor level. When `χ` is primitive (`χ.conductor = q`, `DirichletCharacter.isPrimitive_def`), transporting `χ.primitiveCharacter` along `χ.conductor = q` returns `χ`, so the completed `L`-functions — hence the vanishing orders — agree.

PROOF ROUTE: `zeroMult χ u` unfolds to `analyticOrderNatAt (completedLFunction χ.primitiveCharacter) u` (needs `haveI : NeZero χ.conductor` in scope). Let `h : χ.conductor = q := hprim` (`DirichletCharacter.isPrimitive_def` is `Iff.rfl`). Prove the transport statement for an *arbitrary* equality of levels `h : n = m` — `completedLFunction (h ▸ ψ) s = completedLFunction ψ s`, and likewise for `analyticOrderNatAt` — by `cases h; rfl` (with motive `fun n => DirichletCharacter ℂ n`); and prove `h ▸ χ.primitiveCharacter = χ` via `DirichletCharacter.changeLevel (dvd_of_eq h) χ.primitiveCharacter = χ` using `changeLevel_primitiveCharacter`, proof-irrelevance of the divisibility argument (`Subsingleton.elim`) and `changeLevel_self`. Then combine. (Note: `cases hc` directly on `χ.conductor = q` fails by dependent elimination; use `dvd_of_eq`.) Imports: `Mathlib` and `Submission.Work.LinnikContract.Defs`. -/
theorem zeroMult_eq_analyticOrderNatAt_of_isPrimitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (u : ℂ) :
    Work.LinnikContract.zeroMult χ u
      = analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u := by
  -- the conductor of `χ` is nonzero, since `χ` lives at the nonzero level `q`
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  -- primitivity says precisely that the conductor is the level
  have hc : χ.conductor = q := hprim
  -- transporting the primitive character up to level `q` recovers `χ`
  have hχψ : changeLevel (dvd_of_eq hc) χ.primitiveCharacter = χ :=
    changeLevel_conductor_primitiveCharacter χ hc
  -- and transporting the completed `L`-function along that equality of levels is harmless
  have h1 := congrArg (fun f : ℂ → ℂ => analyticOrderNatAt f u)
    (completedLFunction_changeLevel_of_eq hc χ.primitiveCharacter)
  have h2 := congrArg (fun f : ℂ → ℂ => analyticOrderNatAt f u)
    (by rw [hχψ] :
      (fun s => completedLFunction (N := q) (changeLevel (dvd_of_eq hc) χ.primitiveCharacter) s)
        = (fun s => completedLFunction χ s))
  rw [Work.LinnikContract.zeroMult]
  exact h1.trans h2

end Work.LinnikAreas.FarRepel
