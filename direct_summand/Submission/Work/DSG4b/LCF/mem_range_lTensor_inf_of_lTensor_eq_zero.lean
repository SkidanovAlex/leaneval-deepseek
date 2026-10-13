import Mathlib
import Submission.Work.DSG4b.LCF.Basic

/-!
# A kernel computation for `M ⊗ -`

Let `R` be a commutative ring, `M` an `R`-module and `I, J ⊆ R` ideals.  If the natural map
`M ⊗ (I ⊔ J) → M ⊗ R` is injective, then every element of `M ⊗ I` whose image in `M ⊗ R`
vanishes lies in the image of `M ⊗ (I ⊓ J) → M ⊗ I`:

`Work.DSG4b.LCF.mem_range_lTensor_inf_of_lTensor_eq_zero`.

The proof is the exactness (right exactness of `M ⊗ -`) of the second isomorphism theorem:
the composite
`I ⊓ J → I → (I ⊔ J)/J ≅ I/(I ⊓ J)`
is exact, hence after tensoring with `M`,
`range (M ⊗ (I ⊓ J) → M ⊗ I) = ker (M ⊗ I → M ⊗ ((I ⊔ J)/J))`.
Moreover `I → (I ⊔ J)/J` factors through `I → I ⊔ J`, so the kernel of
`M ⊗ I → M ⊗ (I ⊔ J)` is contained in that of `M ⊗ I → M ⊗ ((I ⊔ J)/J)`.
-/

namespace Work.DSG4b.LCF

open TensorProduct LinearMap

theorem mem_range_lTensor_inf_of_lTensor_eq_zero {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (I J : Ideal R)
    (hinj : Function.Injective (LinearMap.lTensor M (Submodule.subtype (I ⊔ J))))
    (ξ : TensorProduct R M I) (hξ : LinearMap.lTensor M (Submodule.subtype I) ξ = 0) :
    ξ ∈ LinearMap.range (LinearMap.lTensor M (Submodule.inclusion (inf_le_left : I ⊓ J ≤ I))) := by
  -- Step 1: `lTensor M (subtype I)` factors through `lTensor M (inclusion I ≤ I ⊔ J)`.
  have hfac : LinearMap.lTensor M (Submodule.subtype (I : Submodule R R)) =
      (LinearMap.lTensor M (Submodule.subtype ((I ⊔ J) : Submodule R R))) ∘ₗ
        (LinearMap.lTensor M (Submodule.inclusion (le_sup_left : I ≤ I ⊔ J))) := by
    rw [← LinearMap.lTensor_comp, Submodule.subtype_comp_inclusion]
  -- Hence `ξ` is killed already by `M ⊗ (I ⊔ J) → M ⊗ R` composed with the inclusion,
  -- so by injectivity it is killed by `M ⊗ I → M ⊗ (I ⊔ J)`.
  have hξ' : LinearMap.lTensor M (Submodule.inclusion (le_sup_left : I ≤ I ⊔ J)) ξ = 0 := by
    have h2 : LinearMap.lTensor M (Submodule.subtype (I ⊔ J))
        (LinearMap.lTensor M (Submodule.inclusion (le_sup_left : I ≤ I ⊔ J)) ξ) = 0 := by
      rw [← LinearMap.comp_apply, ← hfac, hξ]
    exact hinj h2
  -- Step 2: write `I ⊓ J ⊆ I` as the kernel of `I → (I ⊔ J)/J`.
  -- `N` is `I ⊓ J` viewed inside `I`.
  let N : Submodule R ↥(I : Submodule R R) :=
    Submodule.comap (Submodule.subtype (I : Submodule R R)) (I : Submodule R R) ⊓
      Submodule.comap (Submodule.subtype (I : Submodule R R)) (J : Submodule R R)
  let hf : ↥(I ⊓ J) →ₗ[R] ↥(I : Submodule R R) := Submodule.inclusion (inf_le_left : I ⊓ J ≤ I)
  have hrange : LinearMap.range hf = N := by
    rw [Submodule.range_inclusion]
    rfl
  have hker : LinearMap.ker N.mkQ = LinearMap.range hf := by
    rw [Submodule.ker_mkQ, hrange]
  have hex : Function.Exact (hf : ↥(I ⊓ J) → ↥(I : Submodule R R))
      (N.mkQ : ↥(I : Submodule R R) → ↥(I : Submodule R R) ⧸ N) := LinearMap.exact_iff.mpr hker
  -- Right exactness of `M ⊗ -` turns this exactness into
  -- `range (M ⊗ (I ⊓ J) → M ⊗ I) = ker (M ⊗ I → M ⊗ (I ⧸ N))`.
  have hLT : Function.Exact (LinearMap.lTensor M hf) (LinearMap.lTensor M N.mkQ) :=
    lTensor_exact M hex (Submodule.mkQ_surjective N)
  have hkerLT : LinearMap.ker (LinearMap.lTensor M N.mkQ) = LinearMap.range (LinearMap.lTensor M hf) :=
    LinearMap.exact_iff.mp hLT
  -- Step 3: the second isomorphism theorem identifies `I ⧸ N` with `(I ⊔ J)/J`, compatibly with
  -- the maps `I → I⧸N` and `I → I ⊔ J → (I ⊔ J)/J`.
  let J' : Submodule R ↥((I ⊔ J) : Submodule R R) :=
    Submodule.comap (Submodule.subtype ((I ⊔ J) : Submodule R R)) (J : Submodule R R)
  let e := LinearMap.quotientInfEquivSupQuotient (I : Submodule R R) (J : Submodule R R)
  have heq : (N.mkQ : ↥(I : Submodule R R) →ₗ[R] ↥(I : Submodule R R) ⧸ N) =
      (e.symm : (↥((I ⊔ J) : Submodule R R) ⧸ J') →ₗ[R] (↥(I : Submodule R R) ⧸ N)) ∘ₗ
        (J'.mkQ ∘ₗ
          Submodule.inclusion (le_sup_left : (I : Submodule R R) ≤ ((I ⊔ J) : Submodule R R))) := by
    ext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    have htmp : J'.mkQ
        (Submodule.inclusion (le_sup_left : (I : Submodule R R) ≤ ((I ⊔ J) : Submodule R R)) x) =
        e (N.mkQ x) := by
      rw [Submodule.mkQ_apply]
      exact (LinearMap.quotientInfEquivSupQuotient_apply_mk (I : Submodule R R) (J : Submodule R R)
        x).symm
    rw [htmp]
    exact (LinearEquiv.symm_apply_apply e (N.mkQ x)).symm
  -- Step 4: conclude.
  have hx0 : LinearMap.lTensor M N.mkQ ξ = 0 := by
    rw [heq, LinearMap.lTensor_comp, LinearMap.lTensor_comp, LinearMap.comp_apply,
      LinearMap.comp_apply, hξ', map_zero, map_zero]
  have hx1 : ξ ∈ LinearMap.ker (LinearMap.lTensor M N.mkQ) := LinearMap.mem_ker.mpr hx0
  rw [hkerLT] at hx1
  exact hx1

end Work.DSG4b.LCF
