import Mathlib
import Submission.Work.Serre.DiscPair.cylPairDefs
import Submission.Work.Serre.DiscPair.collarDefs
import Submission.Work.Serre.DiscPair.collarHomeoA2
import Submission.Work.Serre.DiscPair.subPairMapQuasiIso
import Submission.Work.Serre.relKronEquiv
import Submission.Work.Serre.DiscPair.relPairFiveRat
import Submission.Work.Serre.csrExcisionRat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The old-part pair of the disc-pair bundle: vocabulary

This file collects, under short names, the pieces of the "old part" identification proved in
`Submission/Work/Serre/DiscPair/oldPartRelCohIso.lean`:

* `oldA = A₂ ∩ {λ = 0}` is the relative part `range (cylIncl q)` of the target pair, viewed as a
  subset of `↥(cylPairA₂ q)`;
* `oldU₀ = A₂ ∩ {λ < 1/2}` is the collar-piece of `A₂` (which contains `oldA`);
* `oldIncl : oldA ↪ oldU₀` is the inclusion, and `oldUBot ↪ oldUU₀` the same inclusion inside the
  sub-space `U = cylPairU q`.

The geometric content (the bottom of the collar is a deformation retract of the collar, hence a
homotopy equivalence) is isolated in `oldPart_collarIncl` / `oldPart_collarInclU`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.DiscPair

noncomputable section

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)} {X : Type} [TopologicalSpace X]

/-! ## Elementary inclusions of the collar sets -/

/-- The bottom copy `range (cylIncl q)` lies in the collar `{λ < 1/2}`. -/
theorem cylPairBot_subset_cylU₀ (q : C(X, CylZ D Γ ι f)) : cylPairBot q ⊆ cylU₀ q := by
  intro y hy
  rw [mem_cylU₀_iff, (cylLam_eq_zero_iff q y).mpr hy]
  norm_num

/-- The collar-piece `{λ < 1/2}` lies in `A₂` together with the bottom. -/
theorem cylU₀A₂_subset_cylPairA₂ (q : C(X, CylZ D Γ ι f)) :
    {x : ↥(cylPairA₂ q) | (x : cyl q) ∈ cylU₀ q} ⊆ Set.univ := fun _ _ => Set.mem_univ _

/-- `A₂ ∩ {λ = 0}` is exactly the bottom copy. -/
theorem cylPairBot_eq_cylU₀A₂InterU₁ (q : C(X, CylZ D Γ ι f)) :
    {x : ↥(cylPairA₂ q) | (x : cyl q) ∈ cylPairBot q}
      = {x : ↥(cylPairA₂ q) | (x : cyl q) ∈ cylU₀ q ∧ (x : cyl q) ∉ cylU₁ q} := by
  ext x
  constructor
  · intro hx
    refine ⟨cylPairBot_subset_cylU₀ q hx, ?_⟩
    intro hx1
    rw [mem_cylU₁_iff, (cylLam_eq_zero_iff q x.1).mpr hx] at hx1
    exact lt_irrefl 0 hx1
  · rintro ⟨h₀, h₁⟩
    by_contra hx
    have hpos : 0 < (cylLam q x.1 : ℝ) := lt_cylLam_of_not_mem q hx
    exact h₁ ((mem_cylU₁_iff q x.1).mpr hpos)

/-! ## The old-part pair inside `A₂` -/

/-- The relative part of the target pair, inside `A₂`. -/
abbrev oldA (q : C(X, CylZ D Γ ι f)) : Set ↥(cylPairA₂ q) :=
  {x | (x : cyl q) ∈ cylPairBot q}

/-- The collar-piece of `A₂`. -/
abbrev oldU₀ (q : C(X, CylZ D Γ ι f)) : Set ↥(cylPairA₂ q) := cylU₀A₂ q

/-- The open collar-piece of `A₂`. -/
abbrev oldU₁ (q : C(X, CylZ D Γ ι f)) : Set ↥(cylPairA₂ q) := cylU₁A₂ q

/-- The sub-space `U` of the mapping cylinder, inside `A₂`. -/
abbrev oldU (q : C(X, CylZ D Γ ι f)) : Set ↥(cylPairA₂ q) := cylPairUinA₂ q

/-- `oldA ⊆ oldU₀`. -/
theorem oldA_subset_oldU₀ (q : C(X, CylZ D Γ ι f)) : oldA q ⊆ oldU₀ q :=
  fun _ hx => cylPairBot_subset_cylU₀ q hx

/-- The inclusion `oldA ↪ oldU₀` (the bottom of the collar). -/
def oldIncl (q : C(X, CylZ D Γ ι f)) : C(↥(oldA q), ↥(oldU₀ q)) :=
  restrictPair (oldA q) (oldU₀ q) (ContinuousMap.id ↥(cylPairA₂ q)) (oldA_subset_oldU₀ q)

@[simp] theorem oldIncl_coe (q : C(X, CylZ D Γ ι f)) (x : ↥(oldA q)) :
    ((oldIncl q x : ↥(oldU₀ q)) : ↥(cylPairA₂ q)) = x.1 := rfl

/-! ## The old-part pair inside `U = cylPairU q` -/

/-- The bottom copy, as a subset of the sub-space `U`. -/
abbrev oldUBot (q : C(X, CylZ D Γ ι f)) : Set ↥(cylPairU q) :=
  {x | (x : cyl q) ∈ cylPairBot q}

/-- The collar-piece `{λ < 1/2}`, as a subset of the sub-space `U`. -/
abbrev oldUU₀ (q : C(X, CylZ D Γ ι f)) : Set ↥(cylPairU q) :=
  {x | (x : cyl q) ∈ cylU₀ q}

/-- `oldUBot ⊆ oldUU₀`. -/
theorem oldUBot_subset_oldUU₀ (q : C(X, CylZ D Γ ι f)) : oldUBot q ⊆ oldUU₀ q :=
  fun _ hx => cylPairBot_subset_cylU₀ q hx

/-- The inclusion `oldUBot ↪ oldUU₀` (the bottom of the collar inside `U`). -/
def oldUIncl (q : C(X, CylZ D Γ ι f)) : C(↥(oldUBot q), ↥(oldUU₀ q)) :=
  restrictPair (oldUBot q) (oldUU₀ q) (ContinuousMap.id ↥(cylPairU q)) (oldUBot_subset_oldUU₀ q)

@[simp] theorem oldUIncl_coe (q : C(X, CylZ D Γ ι f)) (x : ↥(oldUBot q)) :
    ((oldUIncl q x : ↥(oldUU₀ q)) : ↥(cylPairU q)) = x.1 := rfl

end

end Work.Serre.DiscPair
