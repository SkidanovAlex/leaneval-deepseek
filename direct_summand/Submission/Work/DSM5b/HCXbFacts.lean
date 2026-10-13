import Mathlib
import Submission.Work.DSM5b.H0Defs
import Submission.Work.DSM5b.honestKillFlat
import Submission.Work.DSM5b.locBCRing
import Submission.Work.DSM5b.hCdBaseChange

/-!
# `Work.DSM5b.HCXbFacts` — `HCXb` on cycles and boundaries (first sub-lemmas of the flat transport)

`HCXb t m : HCX t m →ₗ[R₀] HCX (algebraMap ∘ t) m` is the termwise base-change map
(`Submission/Work/DSM5b/locBCRing.lean`) and `hCdBaseChange` (proved, axiom-clean) says it commutes
with the differentials.  The two immediate consequences — the *forwards* half of the flat transport
in `Work.DSM5b.honestKillCoordFlat` — are:

* cycles are carried to cycles;
* boundaries are carried to boundaries.

The *converse* halves (every cycle/boundary over `R` comes from one over `R₀` up to an `R`-linear
combination) are exactly where flatness and `hcxbSpanTop` are used, and are steps 3 of
`honestKillFlat.lean`'s plan.
-/

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

section Facts

variable {R₀ : Type a} [CommRing R₀] {R : Type a} [CommRing R] [Algebra R₀ R]
variable {ι : Type a} [DecidableEq ι]

/-- `HCXb` carries cycles to cycles. -/
lemma HCXb_isCycle (t : ι → R₀) (m : ℕ) {z : HCX t (m + 1)}
    (hz : HCd t (m + 1) z = 0) :
    HCd (fun i => algebraMap R₀ R (t i)) (m + 1) (HCXb (R := R) t (m + 1) z) = 0 := by
  rw [hCdBaseChange, hz, map_zero]

/-- `HCXb` carries boundaries to boundaries. -/
lemma HCXb_mem_range (t : ι → R₀) (m : ℕ) {w : HCX t (m + 1)}
    (hw : w ∈ LinearMap.range (HCd t m)) :
    HCXb (R := R) t (m + 1) w ∈ LinearMap.range (HCd (fun i => algebraMap R₀ R (t i)) m) := by
  obtain ⟨y, rfl⟩ := hw
  exact ⟨HCXb (R := R) t m y, hCdBaseChange t m y⟩

end Facts

end Work.DSM5b
