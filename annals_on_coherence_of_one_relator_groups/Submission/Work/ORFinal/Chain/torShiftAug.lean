import Mathlib
import Submission.Work.ORHomAlg.Tor.torDimensionShift
import Submission.Work.ORBridgeTor.TrivMod
import Submission.Work.ORFP2.mem_augIdeal_iff

/-!
# Shifting Tor past the augmentation ideal

The short exact sequence of `K[G]`-modules
`0 → I_K[G] → K[G] → K → 0`
with middle term the (free, hence projective) module `K[G]` and right-hand term `K` carrying the
trivial module structure (`instTrivLeftModule`) produces, via the horseshoe
(`Work.ORHomAlg.Tor.torDimensionShift`), an isomorphism
`Tor_{n+2}(X, K) ≃ Tor_{n+1}(X, I_K[G])`
for every right `K[G]`-module `X`.
-/

universe u

namespace Work.ORFinal.Chain

/-- The augmentation `K[G] → K` viewed as a `K[G]`-linear map, where `K` carries the trivial
module structure `Work.ORBridgeTor.instTrivLeftModule` (`x • k = ε(x) · k`). -/
noncomputable def augLinMap (K : Type u) [Field K] (G : Type u) [Group G] :
    MonoidAlgebra K G →ₗ[MonoidAlgebra K G] K where
  toFun := Work.ORFP2.augmentation K G
  map_add' x y := map_add _ x y
  map_smul' c x := by
    rw [Work.ORBridgeTor.instTrivLeftModule_smul]
    rw [show c • x = c * x from rfl, map_mul]
    simp only [RingHom.id_apply]
    rfl

theorem torShiftAug (K : Type u) [Field K] (G : Type u) [Group G]
    (X : Type u) [AddCommGroup X] [Module (MonoidAlgebra K G)ᵐᵒᵖ X] (n : ℕ) :
    Nonempty (Work.ORHomAlg.Tor (R := MonoidAlgebra K G) (n + 2) X K ≃ₗ[ℤ]
      Work.ORHomAlg.Tor (R := MonoidAlgebra K G) (n + 1) X ↥(Work.ORFP2.augIdeal K G)) := by
  let g := augLinMap K G
  let f : ↥(Work.ORFP2.augIdeal K G) →ₗ[MonoidAlgebra K G] MonoidAlgebra K G :=
    (Work.ORFP2.augIdeal K G).subtype
  have hf : Function.Injective f := fun a b h => Subtype.ext h
  have hker : LinearMap.ker g = Work.ORFP2.augIdeal K G := by
    ext x
    rw [LinearMap.mem_ker, Work.ORFP2.mem_augIdeal_iff]
    rfl
  have h : Function.Exact f g := by
    rw [LinearMap.exact_iff, hker, Submodule.range_subtype]
  have hg : Function.Surjective g := by
    intro k
    exact ⟨MonoidAlgebra.single (1 : G) k, by
      show Work.ORFP2.augmentation K G (MonoidAlgebra.single 1 k) = k
      simp⟩
  exact Work.ORHomAlg.Tor.torDimensionShift (R := MonoidAlgebra K G) (M := X)
    (N₁ := ↥(Work.ORFP2.augIdeal K G)) (N₂ := MonoidAlgebra K G) (N₃ := K) f g hf h hg n

end Work.ORFinal.Chain
