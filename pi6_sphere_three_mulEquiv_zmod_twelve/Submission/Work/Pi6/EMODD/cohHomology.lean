import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Cohomology.kronH_bijective_field
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The field-coefficient duality between cohomology and homology (area EMODD)

Over a field `𝕜` the Kronecker pairing `Hⁿ(X;𝕜) → (Hₙ(X;𝕜))ᵛ` is an isomorphism
(`Work.Cohomology.kronH_bijective_field`), and for a vector space `V` one has `V = 0 ↔ Vᵛ = 0`.
Hence the category-theoretic vanishing of `Hⁿ(X;𝕜)` (`CategoryTheory.Limits.IsZero`, which is what
the spectral-sequence forcing arguments produce) is equivalent to the `Subsingleton`-vanishing of
the homology `Hₙ(X;𝕜)` (which is what the `EMOdd` statement asks for).

This is the conversion step used by `Work.Pi6.emOdd`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EMODD

noncomputable section

/-- A vector space is a subsingleton iff its dual is.  (One direction is trivial; for the other,
a non-zero `v` has a functional not vanishing on it, by `Module.forall_dual_apply_eq_zero_iff`.) -/
theorem subsingleton_dual_iff {𝕜 : Type} [Field 𝕜] (V : Type) [AddCommGroup V] [Module 𝕜 V] :
    Subsingleton (V →ₗ[𝕜] 𝕜) ↔ Subsingleton V := by
  constructor
  · intro h
    refine ⟨fun v w => ?_⟩
    have hv : v = 0 := (Module.forall_dual_apply_eq_zero_iff (V := V) 𝕜 v).mp
      (fun φ => by rw [Subsingleton.elim φ 0, LinearMap.zero_apply])
    have hw : w = 0 := (Module.forall_dual_apply_eq_zero_iff (V := V) 𝕜 w).mp
      (fun φ => by rw [Subsingleton.elim φ 0, LinearMap.zero_apply])
    rw [hv, hw]
  · intro h
    refine ⟨fun f g => LinearMap.ext fun v => ?_⟩
    rw [show v = 0 from Subsingleton.elim v 0, map_zero, map_zero]

/-- **Cohomology vanishes iff homology does** (over a field, in a fixed degree). -/
theorem isZero_cohomology_iff_subsingleton_homology (𝕜 : Type) [Field 𝕜]
    (X : Type) [TopologicalSpace X] (n : ℕ) :
    CategoryTheory.Limits.IsZero (Work.Pi6.Coh 𝕜 X n) ↔ Subsingleton (Work.Pi6.HR 𝕜 X n) := by
  have e : ↥(Work.Pi6.Coh 𝕜 X n) ≃ₗ[𝕜] (↥(Work.Pi6.HR 𝕜 X n) →ₗ[𝕜] 𝕜) :=
    LinearEquiv.ofBijective (Work.Cohomology.kronH 𝕜 (TopCat.toSSet.obj (TopCat.of X)) n)
      (Work.Cohomology.kronH_bijective_field 𝕜 (TopCat.toSSet.obj (TopCat.of X)) n)
  rw [ModuleCat.isZero_iff_subsingleton]
  exact (Equiv.subsingleton_congr e.toEquiv).trans
    (subsingleton_dual_iff (𝕜 := 𝕜) ↥(Work.Pi6.HR 𝕜 X n))

end

end Work.Pi6.EMODD
