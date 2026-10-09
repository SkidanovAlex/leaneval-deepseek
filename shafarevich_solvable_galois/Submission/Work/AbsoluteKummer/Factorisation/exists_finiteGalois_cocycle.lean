import Mathlib
import Submission.Work.AbsoluteKummer.Defs
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.AbsoluteKummer.Coefficients
import Submission.Work.AbsoluteKummer.Factorisation.exists_finiteGalois_le_ker
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.Factorisation

open scoped Topology

/-- **Every class in `H¹(G_k, M)` is represented by a cocycle which is right-invariant on the
cosets of the fixing subgroup of a finite Galois intermediate field.**

Given a continuous `1`-cocycle `f : G_k → M`, the crossed-homomorphism relation
`f (σ * τ) = σ • f τ + f σ` shows that right-invariance of `f` on `L.fixingSubgroup` is equivalent
to the *vanishing* of `f` there.  Since `f` is locally constant and `f 1 = 0`, some finite Galois
intermediate field `L` has `f = 0` on `L.fixingSubgroup`, whence the claim. -/
theorem exists_finiteGalois_cocycle {k : Type*} [Field k] [IsGalois k (AlgebraicClosure k)]
    {M : Type*} [AddCommGroup M] [DistribMulAction (Work.AbsoluteKummer.G k) M]
    (x : Work.AbsoluteKummer.H1 (Work.AbsoluteKummer.G k) M) :
    ∃ (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
      (f : Work.AbsoluteKummer.Z1 (Work.AbsoluteKummer.G k) M),
      Work.AbsoluteKummer.H1π (Work.AbsoluteKummer.G k) M f = x ∧
        ∀ σ τ : Work.AbsoluteKummer.G k, τ ∈ L.fixingSubgroup →
          (f : Work.AbsoluteKummer.G k → M) (σ * τ) = (f : Work.AbsoluteKummer.G k → M) σ := by
  classical
  -- `H¹ = Z¹ ⧸ B¹` is a quotient, so pick a cocycle representative of `x`.
  obtain ⟨f, hf⟩ :=
    QuotientAddGroup.mk'_surjective
      ((Work.AbsoluteKummer.B1 (Work.AbsoluteKummer.G k) M).comap
        (Work.AbsoluteKummer.Z1 (Work.AbsoluteKummer.G k) M).subtype) x
  have hfπ : Work.AbsoluteKummer.H1π (Work.AbsoluteKummer.G k) M f = x := hf
  -- Unpack the cocycle condition and local constancy of `f`.
  have hmem := f.2
  obtain ⟨hcross, hlc⟩ := (Work.AbsoluteKummer.mem_Z1_iff (f : Work.AbsoluteKummer.G k → M)).mp hmem
  -- `f 1 = 0` for a crossed homomorphism.
  have halg : (f : Work.AbsoluteKummer.G k → M) ∈
      Work.GroupCohomology.Z1 (Work.AbsoluteKummer.G k) M :=
    (Work.GroupCohomology.mem_Z1_iff (Work.AbsoluteKummer.G k) M
      (f : Work.AbsoluteKummer.G k → M)).mpr hcross
  have h1 : (f : Work.AbsoluteKummer.G k → M) 1 = 0 :=
    Work.GroupCohomology.Z1.map_one _ _ halg
  -- Choose a finite Galois intermediate field on whose fixing subgroup `f` is constant.
  obtain ⟨L, hL⟩ := exists_finiteGalois_le_ker (k := k) hlc
  refine ⟨L, f, hfπ, ?_⟩
  intro σ τ hτ
  have hτ0 : (f : Work.AbsoluteKummer.G k → M) τ = 0 := by
    rw [hL τ hτ, h1]
  calc (f : Work.AbsoluteKummer.G k → M) (σ * τ)
      = σ • (f : Work.AbsoluteKummer.G k → M) τ + (f : Work.AbsoluteKummer.G k → M) σ :=
        hcross σ τ
    _ = σ • 0 + (f : Work.AbsoluteKummer.G k → M) σ := by rw [hτ0]
    _ = (f : Work.AbsoluteKummer.G k → M) σ := by rw [smul_zero, zero_add]

end Work.AbsoluteKummer.Factorisation
