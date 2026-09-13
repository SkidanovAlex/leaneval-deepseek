import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open LinearMap Module

namespace Commons.LinearAlgebra.LinearMap

/-- **Factorization of a linear map through a space of dimension at most `d`.**

If the range of `f : M →ₗ[K] N` has dimension at most `d`, then `f` factors as
`h ∘ g` with `g : M →ₗ[K] (Fin d → K)` and `h : (Fin d → K) →ₗ[K] N`.

The construction picks a basis `b` of `W = range f` (whose index set `Fin r` satisfies
`r ≤ d`), embeds `K^r` into `K^d` along `Fin.castLE`, and reads off the coordinates of
`f x` in that basis. -/
theorem exists_factor_of_finrank_range_le {K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Module.Finite K N]
    (f : M →ₗ[K] N) (d : ℕ) (h : Module.finrank K (LinearMap.range f) ≤ d) :
    ∃ (g : M →ₗ[K] (Fin d → K)) (h' : (Fin d → K) →ₗ[K] N), f = h'.comp g := by
  classical
  let W : Submodule K N := LinearMap.range f
  let r : ℕ := Module.finrank K W
  have hr : r ≤ d := h
  let b : Basis (Fin r) K W := Module.finBasis K W
  let β : W →ₗ[K] (Fin r → K) := b.equivFun
  let β' : (Fin r → K) →ₗ[K] W := b.equivFun.symm
  have hββ' : ∀ w : W, β' (β w) = w := by
    intro w; exact b.equivFun.symm_apply_apply w
  -- The "pad by zero" map `K^r → K^d` along the inclusion `Fin r → Fin d`.
  let s : (Fin r → K) →ₗ[K] (Fin d → K) :=
    ∑ i : Fin r, (LinearMap.single K (fun _ : Fin d => K) (Fin.castLE hr i)).comp
      (LinearMap.proj i)
  have hs_apply : ∀ (c : Fin r → K) (j : Fin r), s c (Fin.castLE hr j) = c j := by
    intro c j
    have hsum : s c = ∑ i : Fin r, Pi.single (Fin.castLE hr i) (c i) := by
      simp only [s, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        LinearMap.single_apply]
    rw [hsum, Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      exact Pi.single_eq_of_ne (M := fun _ : Fin d => K) (i := Fin.castLE hr i)
        (i' := Fin.castLE hr j)
        (fun hcontra => (Ne.symm hij) (Fin.castLE_injective hr hcontra)) (c i)
    · intro hj; exact absurd (Finset.mem_univ j) hj
  let e : (Fin d → K) →ₗ[K] (Fin r → K) := LinearMap.funLeft K K (Fin.castLE hr)
  have he : ∀ c : Fin r → K, e (s c) = c := by
    intro c
    funext j
    rw [LinearMap.funLeft_apply]
    exact hs_apply c j
  have hir : W.subtype ∘ₗ f.rangeRestrict = f := by
    apply LinearMap.ext; intro x; rfl
  refine ⟨s ∘ₗ β ∘ₗ f.rangeRestrict, W.subtype ∘ₗ β' ∘ₗ e, ?_⟩
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [he (β (f.rangeRestrict x)), hββ' (f.rangeRestrict x)]
  exact congr_fun (congr_arg DFunLike.coe hir) x

end Commons.LinearAlgebra.LinearMap

namespace Commons.LinearAlgebra.Matrix

open LinearMap Module

/-- **A matrix has rank at most `d` iff it factors through `K^d`.**

A (possibly rectangular) matrix `A : Matrix m n K` over a field can be written as
`B * C` with `B : Matrix m (Fin d) K` and `C : Matrix (Fin d) n K` exactly when its rank
is at most `d`. -/
theorem rank_le_iff_exists_factor {m n : Type*} [Fintype m] [Fintype n] {K : Type*} [Field K]
    (A : Matrix m n K) (d : ℕ) :
    A.rank ≤ d ↔ ∃ (B : Matrix m (Fin d) K) (C : Matrix (Fin d) n K), A = B * C := by
  classical
  constructor
  · intro h
    obtain ⟨g, h', hf⟩ :=
      Commons.LinearAlgebra.LinearMap.exists_factor_of_finrank_range_le A.mulVecLin d h
    refine ⟨LinearMap.toMatrix' h', LinearMap.toMatrix' g, ?_⟩
    rw [← LinearMap.toMatrix'_comp, ← hf, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  · rintro ⟨B, C, rfl⟩
    calc (B * C).rank ≤ B.rank := Matrix.rank_mul_le_left B C
      _ ≤ Fintype.card (Fin d) := Matrix.rank_le_card_width B
      _ = d := Fintype.card_fin d

end Commons.LinearAlgebra.Matrix