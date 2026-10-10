import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.GroupExtension.Defs
import Submission.Work.AbsoluteGalois.twisted_splitting_iff_mem_B2
import Submission.Work.GroupCohomology.H2pi_eq_zero_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

set_option linter.style.haveILetI false

/-- A `2`-cocycle `c` normalized at `(1, 1)` whose associated extension `ofNormalized Q A c`
admits a splitting is a `2`-coboundary.

Indeed, a splitting is a monoid homomorphism `s : Q →* A × Q` with `(s q).2 = q` for all `q`,
which is exactly the data used by `twisted_splitting_iff_mem_B2`. -/
theorem normCocycle_mem_B2_of_splitting {Q : Type*} {A : Type*} [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] (c : Q × Q → A) (hc : c ∈ Z2 Q A) (h1 : c (1, 1) = 0)
    (h : Nonempty (Extension.Splitting (Extension.ofNormalized Q A c hc h1))) :
    c ∈ B2 Q A := by
  obtain ⟨s⟩ := h
  letI := (Extension.ofNormalized Q A c hc h1).groupE
  apply (Work.AbsoluteGalois.twisted_splitting_iff_mem_B2 c hc h1).mp
  exact ⟨s.toMonoidHom, fun q => s.rightHom_splitting q⟩

/-- The difference between a `2`-cocycle `c` and its normalization `normCocycle c` is the
`2`-coboundary `d¹ (q ↦ c (q, 1))`: indeed `normCocycle c (q, r) = c (q, r) - c (q, 1)`, so
`c - normCocycle c` is the function `(q, r) ↦ c (q, 1) = q • c (1, 1)`, which is the coboundary
of the `1`-cochain `q ↦ c (q, 1)`. -/
theorem subl_normCocycle_mem_B2 {Q : Type*} {A : Type*} [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] (c : Z2 Q A) :
    (c : Q × Q → A) - normCocycle Q A (c : Q × Q → A) ∈ B2 Q A := by
  rw [mem_B2_iff]
  refine ⟨fun q => (c : Q × Q → A) (q, 1), ?_⟩
  funext p
  obtain ⟨q, r⟩ := p
  have hr : (c : Q × Q → A) (r, 1) = r • (c : Q × Q → A) (1, 1) := Z2.map_one_snd Q A c.2 r
  have hqr : (c : Q × Q → A) (q * r, 1) = (q * r) • (c : Q × Q → A) (1, 1) :=
    Z2.map_one_snd Q A c.2 (q * r)
  simp only [Pi.sub_apply, d1_apply, normCocycle_apply]
  rw [hr, hqr, mul_smul]
  abel

/-- A `2`-cocycle `c` is a `2`-coboundary as soon as its normalization `normCocycle c` is: the
difference `c - normCocycle c` is itself a coboundary. -/
theorem mem_B2_of_normCocycle_mem_B2 {Q : Type*} {A : Type*} [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] (c : Z2 Q A)
    (h : normCocycle Q A (c : Q × Q → A) ∈ B2 Q A) :
    (c : Q × Q → A) ∈ B2 Q A := by
  have hsub := subl_normCocycle_mem_B2 (Q := Q) (A := A) c
  have hsum := add_mem h hsub
  have heq : normCocycle Q A (c : Q × Q → A)
      + ((c : Q × Q → A) - normCocycle Q A (c : Q × Q → A)) = (c : Q × Q → A) := by abel
  rwa [heq] at hsum

theorem class_zero_of_splits_ofCocycle {Q : Type*} {A : Type*} [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] (c : Work.GroupCohomology.Z2 Q A)
    (h : Nonempty (Work.GroupCohomology.Extension.Splitting
      (Work.GroupCohomology.Extension.ofCocycle Q A c))) :
    Work.GroupCohomology.H2π Q A c = 0 := by
  rw [H2pi_eq_zero_iff]
  refine mem_B2_of_normCocycle_mem_B2 c ?_
  exact normCocycle_mem_B2_of_splitting (normCocycle Q A (c : Q × Q → A))
    (normCocycle_mem Q A (c : Q × Q → A) c.2) (normCocycle_one Q A (c : Q × Q → A)) h

end Work.GroupCohomology
