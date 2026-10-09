/-
Copyright (c) 2025. All rights reserved.

# The `𝔽₂^r` (`μ₂^r`) case of the quadratic Grünwald statement

For finitely many **distinct** primes `q i` and prescribed local data
`c i : (ℚ_{q i}ˣ/(ℚ_{q i}ˣ)²)^r` (i.e. `A = 𝔽_2^r = μ_2^r`), there is a *global* square-class
vector `x : (ℚˣ/(ℚˣ)²)^r` with prescribed localisations.  The hypothesis `Function.Injective q`
is what excludes repeated primes: with repeated primes and independent data the statement is
false (see `Submission/Work/QuadraticLocalGlobal/NOTES.md`), which is precisely the correction
recorded for `Work.HilbertSymbol.GrunwaldWang`.
-/
import Submission.Work.AbsoluteKummer.Grunwald.sqClassLocalize_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.Grunwald

/-- **Grünwald in degree `2` for `A = 𝔽₂^r`.**  Prescribed local square-class vectors at finitely
many distinct primes are realised by a global square-class vector. -/
theorem sqClassLocalize_surjective_pi {r : ℕ} {ι : Type*} [Fintype ι] (q : ι → ℕ)
    [∀ i, Fact (q i).Prime] (hq : Function.Injective q) :
    Function.Surjective (fun x : Fin r → Work.AbsoluteKummer.SqClass ℚ =>
      fun i : ι => fun j : Fin r => Work.AbsoluteKummer.sqClassLocalize (q i) (x j)) := by
  intro y
  have h := sqClassLocalize_surjective q hq
  choose x hx using fun j => h (fun i => y i j)
  exact ⟨x, funext fun i => funext fun j => congrFun (hx j) i⟩

end Work.AbsoluteKummer.Grunwald
