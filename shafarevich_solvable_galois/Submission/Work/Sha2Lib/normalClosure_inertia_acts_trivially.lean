import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.detectorInterface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Sha2Lib

open CategoryTheory

set_option linter.style.haveILetI false

/-- **The general form: the normal closure of a set acting trivially acts trivially.**

If every element of a set `S ⊆ G` acts trivially on a `G`-module `A`, then so does every element of
the normal closure of `S`.  The point is that `{g | ∀ a, A.ρ g a = a}` is the kernel of the monoid
homomorphism `A.ρ`, hence a normal subgroup.

(Stated for an arbitrary `Group G` and `A : Rep.{0} R G`, so that it can be applied directly to the
inertia set of the main statement.) -/
theorem normalClosure_acts_trivially_of_trivial_on {R : Type*} [Semiring R] {G : Type*} [Group G]
    (A : Rep.{0} R G) (S : Set G) (hS : ∀ g ∈ S, ∀ a : A, A.ρ g a = a) :
    ∀ g ∈ Subgroup.normalClosure S, ∀ a : A, A.ρ g a = a := by
  -- The set of elements acting trivially on `A` is a subgroup ...
  let H : Subgroup G :=
    { carrier := {g | ∀ m : A, A.ρ g m = m}
      one_mem' := by intro m; simp
      mul_mem' := by intro x y hx hy m; rw [map_mul, Module.End.mul_apply]; rw [hy, hx]
      inv_mem' := by
        intro x hx m
        have h1 : A.ρ x (A.ρ x⁻¹ m) = m := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        rw [hx (A.ρ x⁻¹ m)] at h1
        exact h1 }
  -- ... and it is normal, being a kernel.
  have hHN : H.Normal := by
    refine ⟨fun n hn g m => ?_⟩
    have h1 : A.ρ g (A.ρ g⁻¹ m) = m := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    show A.ρ (g * n * g⁻¹) m = m
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hn (A.ρ g⁻¹ m), h1]
  haveI := hHN
  intro g hg m
  exact Subgroup.normalClosure_le_normal (N := H) (fun g hg => hS g hg) hg m

/-- **The normal closure of the inertia at `q` acts trivially on `M`.**

`k ⊆ K` number fields with `K/k` finite Galois, `q` a place of `K`, `M` a `Gal(K/k)`-module on which
every inertia element at `q` acts trivially (the target's `hI`).  Then every element of the normal
closure `N := Subgroup.normalClosure {σ | IsInertiaAt q σ}` acts trivially on `M`.

Step 1 of the C6 route (`_lead_design/ssg_pt_design_1002/DESIGN.md` §2): this is what makes `res_N M`
a *trivial* `N`-module, i.e. exactly the hypothesis `hWtriv` of the dispatched
`Work.Sha2Lib.unramifiedDetector_indNormal` (line 110 of its file), so the caller needs no reshaping.

Proof (both reviewers: a few lines, no hours): `S := {g | ∀ m, M.ρ g m = m}` is the kernel of the
monoid homomorphism `M.ρ : (K ≃ₐ[k] K) →* (M →+ M)`, hence a *normal* subgroup (`ρ (x * g * x⁻¹) =
ρ x ∘ ρ g ∘ ρ x⁻¹ = id` whenever `ρ g = id`, using only multiplicativity); `hI` puts the whole
inertia set inside `S`; so `Subgroup.normalClosure_le` yields `normalClosure {σ | IsInertiaAt q σ} ≤
S`, which is the claim.  The natural general form
`∀ (S : Set G), (∀ g ∈ S, ∀ a, A.ρ g a = a) → ∀ g ∈ Subgroup.normalClosure S, ∀ a, A.ρ g a = a`
for arbitrary `G` and `A : Rep Coeff G` is a legitimate intermediate and can be extracted first.
The `p`/`[Fact p.Prime]` binders are unused (kept for consistency with the family). -/
theorem normalClosure_inertia_acts_trivially (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (g : K ≃ₐ[k] K)
    (hg : g ∈ Subgroup.normalClosure {σ : K ≃ₐ[k] K | SSGRoute.PTExt.IsInertiaAt q σ}) :
    ∀ m : M, M.ρ g m = m :=
  normalClosure_acts_trivially_of_trivial_on M {σ : K ≃ₐ[k] K | SSGRoute.PTExt.IsInertiaAt q σ}
    hI g hg

end Work.Sha2Lib
