import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.Matrix

open Module

/-- **Sylvester's rank inequality**, linear-map form: for linear maps `f : W →ₗ[K] V` and
`g : U →ₗ[K] W` with `W` finite dimensional,
`finrank (range f) + finrank (range g) ≤ finrank W + finrank (range (f ∘ g))`. -/
theorem finrank_range_add_finrank_range_le {K : Type*} [Field K]
    {V W U : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup U] [Module K U] [FiniteDimensional K W]
    (f : W →ₗ[K] V) (g : U →ₗ[K] W) :
    finrank K (LinearMap.range f) + finrank K (LinearMap.range g) ≤
      finrank K W + finrank K (LinearMap.range (f.comp g)) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (f.comp (LinearMap.range g).subtype)
  have hrange : LinearMap.range (f.comp (LinearMap.range g).subtype) =
      LinearMap.range (f.comp g) := by
    simp only [LinearMap.range_comp, Submodule.range_subtype]
  have hker : LinearMap.ker (f.comp (LinearMap.range g).subtype) =
      Submodule.comap (LinearMap.range g).subtype (LinearMap.ker f) := by
    rw [LinearMap.ker_comp]
  have hkerfin : finrank K (LinearMap.ker (f.comp (LinearMap.range g).subtype)) =
      finrank K ↥(LinearMap.range g ⊓ LinearMap.ker f) := by
    rw [hker, ← Submodule.map_comap_subtype (LinearMap.range g) (LinearMap.ker f),
      Submodule.finrank_map_subtype_eq]
  have hle : finrank K ↥(LinearMap.range g ⊓ LinearMap.ker f) ≤ finrank K (LinearMap.ker f) :=
    Submodule.finrank_mono inf_le_right
  have hf := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hkerfin] at hrn
  omega

/-- **Sylvester's rank inequality** for matrices: for `A : Matrix (Fin l) (Fin m) K` and
`B : Matrix (Fin m) (Fin n) K` over a field, `rank A + rank B - m ≤ rank (A * B)`. -/
theorem rank_mul_ge_add_sub {K : Type*} [Field K] {l m n : ℕ}
    (A : Matrix (Fin l) (Fin m) K) (B : Matrix (Fin m) (Fin n) K) :
    A.rank + B.rank - m ≤ (A * B).rank := by
  have h := finrank_range_add_finrank_range_le A.mulVecLin B.mulVecLin
  rw [← Matrix.mulVecLin_mul] at h
  rw [Module.finrank_pi, Fintype.card_fin] at h
  change finrank K (LinearMap.range A.mulVecLin) + finrank K (LinearMap.range B.mulVecLin) - m ≤
    finrank K (LinearMap.range (A * B).mulVecLin)
  omega

end Commons.LinearAlgebra.Matrix