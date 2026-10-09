import Mathlib
import Submission.Work.SSGRoute.ZDataMup.mupLocalVocab
import Submission.Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

open scoped Topology

/-!
# Vanishing of a locally constant character killing the Artin image

Let `R : NK.LocalCFT.ArtinReciprocity F F'` be the canonical local Artin reciprocity datum for a
field `F` with a Galois extension `F'`, so that `R.artin : Fˣ →* Gal(F^ab/F)` is the local Artin
map.  We prove that a **locally constant** group homomorphism

`x : Gal(F^ab/F) →* Multiplicative (ZMod p)`

which is trivial on the image of `R.artin` is trivial on all of `Gal(F^ab/F)`.  In other words, the
image of the local Artin map is *dense* in `Gal(F^ab/F)` in the strongest sense relevant for
characters: the continuous characters of `Gal(F^ab/F)` that kill it are exactly the trivial one.

This is the "non-degeneracy in the first variable" input of the `μ_p` local Tate pairing
(`mupLocalForm.lean`).

## The argument

1. `x` locally constant means that its kernel is open: it is the preimage of the point `1` under
   `x` (`isOpen_ker_of_isLocallyConstant`).
2. An open subgroup of a Galois group contains the fixing subgroup `Gal(F^ab/M)` of a
   finite-dimensional *normal* intermediate field `M ≤ F^ab`
   (`Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le`).
3. `Gal(F^ab/F)` is abelian, so `Gal(M/F)` is abelian
   (`NK.LocalCFT.NormGroup.normGroup_eq_iff_commutative_gal`), and hence the reciprocity datum
   applies at the level `M`: `Fˣ →* Gal(M/F)` is surjective.
4. Given any `σ : Gal(F^ab/F)`, choose `a : Fˣ` with `artin a` and `σ` having the same image in
   `Gal(M/F)`.  Then `σ * (artin a)⁻¹ ∈ ker (Gal(F^ab/F) → Gal(M/F)) = Gal(F^ab/M) ≤ ker x`, so
   `x σ = x (artin a) = 1`.
-/

/-- **A locally constant homomorphism into `Multiplicative (ZMod p)` has open kernel.**

`MonoidHom.ker x` is the preimage of the point `1` under `x`, and `IsLocallyConstant x` says that
the preimage of *any* set is open. -/
theorem isOpen_ker_of_isLocallyConstant {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    (x : G →* Multiplicative (ZMod p)) (hx : IsLocallyConstant x) :
    IsOpen ((MonoidHom.ker x : Subgroup G) : Set G) := by
  rw [show (MonoidHom.ker x : Set G) = x ⁻¹' ({1} : Set (Multiplicative (ZMod p))) from by
    ext y; simp [MonoidHom.mem_ker]]
  exact hx {1}

/-- **A locally constant character killing the image of the local Artin map is trivial.**

`R.artin(Fˣ)` is dense in `Gal(F^ab/F)` (the density itself is `denseRange_artin`), and a locally
constant (equivalently continuous) character into the finite discrete group
`Multiplicative (ZMod p)` which is trivial on a dense subgroup is trivial.

The proof below realises the density argument at a single finite level rather than by a closure
argument: it only needs that the artin map is surjective onto every finite abelian level. -/
theorem eq_one_of_forall_artin_eq_one {p : ℕ} [Fact p.Prime] {F F' : Type*}
    [Field F] [Field F'] [Algebra F F'] [IsGalois F F']
    (R : NK.LocalCFT.ArtinReciprocity F F')
    (x : NK.LocalCFT.AbGal F F' →* Multiplicative (ZMod p))
    (hx : IsLocallyConstant x)
    (h : ∀ a : Fˣ, x (R.artin a) = 1) : x = 1 := by
  -- ## 1. the kernel of `x` is open
  have hker : IsOpen ((MonoidHom.ker x : Subgroup (NK.LocalCFT.AbGal F F')) :
      Set (NK.LocalCFT.AbGal F F')) := isOpen_ker_of_isLocallyConstant x hx
  -- ## 2. it contains the fixing subgroup of a finite normal intermediate field `M ≤ F^ab`
  obtain ⟨M, hMfin, hMnorm, hMsub⟩ :=
    Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le (MonoidHom.ker x) hker
  have hMfin' : FiniteDimensional F M := hMfin
  have hMnorm' : Normal F M := hMnorm
  -- ## 3. `Gal(M/F)` is abelian, so reciprocity applies at the level `M`
  have hcomm : ∀ σ τ : ↥M ≃ₐ[F] ↥M, σ * τ = τ * σ :=
    NK.LocalCFT.NormGroup.normGroup_eq_iff_commutative_gal M
  have hker_level : MonoidHom.ker (NK.LocalCFT.levelRestrict M) = M.fixingSubgroup := by
    rw [NK.LocalCFT.levelRestrict]
    exact IntermediateField.restrictNormalHom_ker M
  -- ## 4. `x` is constant on the cosets of `Gal(F^ab/M)`, which the Artin image meets
  refine MonoidHom.ext fun σ => ?_
  obtain ⟨a, ha⟩ := (R.isLevelIso M hcomm).1 (NK.LocalCFT.levelRestrict M σ)
  have ha' : NK.LocalCFT.levelRestrict M (R.artin a) = NK.LocalCFT.levelRestrict M σ := ha
  have hmem : σ * (R.artin a)⁻¹ ∈ MonoidHom.ker (NK.LocalCFT.levelRestrict M) := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ha', mul_inv_cancel]
  rw [hker_level] at hmem
  have hmemx : σ * (R.artin a)⁻¹ ∈ MonoidHom.ker x := hMsub hmem
  have hx1 : x (σ * (R.artin a)⁻¹) = 1 := MonoidHom.mem_ker.mp hmemx
  have h2 : x σ = x (R.artin a) := by
    rw [map_mul, map_inv] at hx1
    exact mul_inv_eq_one.mp hx1
  rw [h2, h a, MonoidHom.one_apply]

end Work.SSGRoute.ZDataMup
