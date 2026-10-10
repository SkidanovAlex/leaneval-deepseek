import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Nat.Prime.Defs
import Submission.Work.ProP.finite_freePQuotient
import Submission.Work.ProP.isPGroup_freePQuotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

open Work.Shrinking

/-! ## The projection `F^(n) → F^(n)/F^(n)(ν)` -/

/-- The kernel of the projection `F^(n) → F^(n)/F^(n)(ν)` is the generic kernel `F^(n)(ν)`. -/
theorem freePQuotientMk_ker (p n ν : ℕ) :
    (freePQuotientMk p n ν).ker = pCentralSeries p (FreeGroup (Fin n)) ν :=
  QuotientGroup.ker_mk' _

/-- The `p`-central filtration of the free group is exactly the family of kernels of the
projections onto the generic kernel quotients. -/
theorem pCentralSeries_eq_ker_freePQuotientMk (p n ν : ℕ) :
    pCentralSeries p (FreeGroup (Fin n)) ν = (freePQuotientMk p n ν).ker :=
  (freePQuotientMk_ker p n ν).symm

/-- At level `0` the generic kernel quotient `F^(n)/F^(n)(0)` is trivial. -/
theorem subsingleton_freePQuotient_zero (p n : ℕ) : Subsingleton (FreePQuotient p n 0) :=
  QuotientGroup.subsingleton_quotient_top

instance subsingletonFreePQuotientZero (p n : ℕ) : Subsingleton (FreePQuotient p n 0) :=
  subsingleton_freePQuotient_zero p n

/-- Alias for `Work.ProP.proPCompletion`, under the name by which the pro-`p` completion was
requested.  The API (projections, canonical map, inverse-limit universal property, extension
property) is in the `Work.ProP.proPCompletion` namespace. -/
abbrev ProPCompletion (p n : ℕ) : Subgroup (∀ ν : ℕ, FreePQuotient p n ν) := proPCompletion p n

/-- The canonical map `F^(n) → ProPCompletion p n`. -/
abbrev ProPCompletion.canonical (p n : ℕ) : FreeGroup (Fin n) →* ProPCompletion p n :=
  proPCompletion.canonical p n

/-! ## Instances

Note that `IsPGroup` is a `def` and not a typeclass in this revision of Mathlib, so the
`p`-group property is recorded as a theorem (`Work.ProP.isPGroup_freePQuotient`) rather than an
instance; finiteness, on the other hand, is registered. -/

instance finiteFreePQuotient {p : ℕ} [Fact p.Prime] (n ν : ℕ) : Finite (FreePQuotient p n ν) :=
  Work.ProP.finite_freePQuotient n ν

/-! ## The inverse system -/

/-- The structure maps of the inverse system defining the pro-`p`-completion are surjective. -/
theorem freePQuotientProj_surjective (p n : ℕ) {ν μ : ℕ} (h : ν ≤ μ) :
    Function.Surjective (freePQuotientProj p n h) := by
  intro y
  obtain ⟨x, rfl⟩ := freePQuotientMk_surjective p n ν y
  exact ⟨freePQuotientMk p n μ x, freePQuotientProj_apply p n h x⟩

/-- The pro-`p`-completion is an inverse limit of *surjective* structure maps, as befits a
pro-`p` completion. -/
theorem freePQuotientProj_succ_surjective (p n ν : ℕ) :
    Function.Surjective (freePQuotientProj p n (Nat.le_succ ν)) :=
  freePQuotientProj_surjective p n (Nat.le_succ ν)

end Work.ProP
