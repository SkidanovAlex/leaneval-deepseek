import Mathlib
import Submission.Work.AbsoluteKummer.Kummer
import Submission.Work.AbsoluteKummer.Coefficients
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.Kummer

/-- **Injectivity of the Kummer map.**

The Kummer map attaches to `x : kˣ` (modulo `n`-th powers) the class in `H¹(G_k, μ_n)` of the
crossed homomorphism `σ ↦ σ α / α`, where `α` is a chosen `n`-th root of `x` in `k̄`.

Its kernel is trivial: if the class of `x` is zero, then (because the Galois action on `μ_n` is
trivial, so that `B¹(G_k, μ_n) = 0`, see `H1π_rootsOfUnity_injective`) the *cochain* `σ ↦ σ α / α`
vanishes identically.  Hence `α` is fixed by every `k`-automorphism of `k̄`, so `α` lies in `k`
(infinitely many automorphisms still detect `k` inside `k̄`, `InfiniteGalois.mem_range_algebraMap_iff_fixed`),
and `x = α ^ n` is an `n`-th power in `kˣ`. -/
theorem kummerMap_injective {k : Type*} [Field k] [IsGalois k (AlgebraicClosure k)] {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n) : Function.Injective (Work.AbsoluteKummer.kummerMap hζ) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  refine le_antisymm (fun x hx => ?_) bot_le
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Work.Kummer.nthPowerSubgroup n kˣ) x
  rw [MonoidHom.mem_ker, Work.AbsoluteKummer.kummerMap_mk] at hx
  -- The class of the Kummer cocycle is zero.
  have hclass : Work.AbsoluteKummer.kummerClassFun hζ y = 0 := by
    have h := hx
    rw [show (1 : Multiplicative (Work.AbsoluteKummer.H1 (Work.AbsoluteKummer.G k)
      (Additive (rootsOfUnity n (AlgebraicClosure k))))) = Multiplicative.ofAdd 0 from rfl] at h
    exact Multiplicative.ofAdd.injective h
  -- Since the action on `μ_n` is trivial, `H¹π` is injective, so the cocycle itself is zero.
  have hcoc : Work.AbsoluteKummer.kummerCocycle hζ y = 0 := by
    refine Work.AbsoluteKummer.H1π_rootsOfUnity_injective k hζ ?_
    rw [show Work.AbsoluteKummer.H1π (Work.AbsoluteKummer.G k)
        (Additive (rootsOfUnity n (AlgebraicClosure k)))
        (Work.AbsoluteKummer.kummerCocycle hζ y) = 0 from hclass, map_zero]
  have hfun : Work.AbsoluteKummer.kummerCocycleFun hζ y = 0 := by
    have := congrArg (fun z : Work.AbsoluteKummer.Z1 (Work.AbsoluteKummer.G k)
        (Additive (rootsOfUnity n (AlgebraicClosure k))) =>
          (z : Work.AbsoluteKummer.G k → Additive (rootsOfUnity n (AlgebraicClosure k)))) hcoc
    simpa using this
  -- Hence the chosen `n`-th root `α` of `y` is fixed by all of `G_k`.
  have hfix : ∀ σ : Work.AbsoluteKummer.G k,
      σ ((Work.AbsoluteKummer.kummerRootUnit (n := n) y : (AlgebraicClosure k)ˣ) :
          AlgebraicClosure k) =
        ((Work.AbsoluteKummer.kummerRootUnit (n := n) y : (AlgebraicClosure k)ˣ) :
          AlgebraicClosure k) := by
    intro σ
    have h2 : Work.AbsoluteKummer.kummerCocycleFun hζ y σ = 0 := by rw [hfun]; rfl
    have h3 := congrArg (fun z : Additive (rootsOfUnity n (AlgebraicClosure k)) =>
      ((Additive.toMul z : rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ)) h2
    rw [Work.AbsoluteKummer.kummerCocycleFun_toMul] at h3
    rw [show ((Additive.toMul (0 : Additive (rootsOfUnity n (AlgebraicClosure k))) :
        rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ) = 1 from rfl] at h3
    rw [Work.Kummer.kummerRatio] at h3
    have h4 : Work.Kummer.algEquivUnitsMap σ (Work.AbsoluteKummer.kummerRootUnit (n := n) y) =
        Work.AbsoluteKummer.kummerRootUnit (n := n) y := div_eq_one.mp h3
    have h5 := congrArg (fun u : (AlgebraicClosure k)ˣ => (u : AlgebraicClosure k)) h4
    simpa [Work.Kummer.algEquivUnitsMap_coe] using h5
  -- So `α` comes from an element `a : kˣ`, and `y = a ^ n`.
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
    ((Work.AbsoluteKummer.kummerRootUnit (n := n) y : (AlgebraicClosure k)ˣ) : AlgebraicClosure k)).mpr hfix
  have ha0 : a ≠ 0 := by
    intro h0
    have hz : ((Work.AbsoluteKummer.kummerRootUnit (n := n) y : (AlgebraicClosure k)ˣ) :
        AlgebraicClosure k) = 0 := by rw [← ha, h0, map_zero]
    exact (Work.AbsoluteKummer.kummerRootUnit (n := n) y).ne_zero hz
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨Units.mk0 a ha0, ?_⟩
  have hmap : Units.map (algebraMap k (AlgebraicClosure k)) (Units.mk0 a ha0) =
      Work.AbsoluteKummer.kummerRootUnit (n := n) y := by
    ext
    simp [ha]
  refine Units.map_injective (algebraMap k (AlgebraicClosure k)).injective ?_
  calc (Units.map (algebraMap k (AlgebraicClosure k))) ((Units.mk0 a ha0)^n)
      = ((Units.map (algebraMap k (AlgebraicClosure k))) (Units.mk0 a ha0))^n :=
        map_pow _ _ _
    _ = (Work.AbsoluteKummer.kummerRootUnit (n := n) y)^n := congrArg (fun u => u^n) hmap
    _ = (Units.map (algebraMap k (AlgebraicClosure k))) y :=
        Work.AbsoluteKummer.kummerRootUnit_pow y

end Work.AbsoluteKummer.Kummer
