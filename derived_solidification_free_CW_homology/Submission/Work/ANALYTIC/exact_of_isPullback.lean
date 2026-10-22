import Mathlib

namespace Work.ANALYTIC

/-! ## A pullback square with a monomorphic right edge is exact

If in an abelian category the square `b ≫ d = a ≫ c` is a pullback and `c` is a monomorphism, then
`A --b--> B --d ≫ cokernel.π c--> cokernel c` is exact: `b` exhibits `A` as the kernel of
`d ≫ cokernel.π c`.

Proof route: `Abelian.monoIsKernelOfCokernel` says that `c` (a mono) is a kernel of `cokernel.π c`;
hence for `k : T ⟶ B` with `k ≫ (d ≫ cokernel.π c) = 0` the map `k ≫ d` factors as
`m ≫ c` with `m := Abelian.monoLift c (k ≫ d) _` (`Abelian.monoLift_comp`), and then the pullback
property `hp.lift k m _` (with `hp.lift_fst`) gives `l : T ⟶ A` with `l ≫ b = k`.  Conclude with
`ShortComplex.exact_of_f_is_kernel` and `KernelFork.IsLimit.ofι'` (using
`hp.mono_fst_of_mono` to get `Mono b`). -/
open CategoryTheory CategoryTheory.Limits in
theorem exact_of_isPullback {C : Type*} [Category C] [Abelian C]
    {A B X D : C} (b : A ⟶ B) (a : A ⟶ X) (d : B ⟶ D) (c : X ⟶ D)
    (hp : IsPullback b a d c) [Mono c]
    (hzero : b ≫ (d ≫ cokernel.π c) = 0) :
    (CategoryTheory.ShortComplex.mk b (d ≫ cokernel.π c) hzero).Exact := by
  apply ShortComplex.exact_of_f_is_kernel
  -- `b` is a monomorphism: it is the pullback of the monomorphism `c`
  haveI : Mono b := hp.mono_fst_of_mono
  -- it suffices to lift every `k : T ⟶ B` killing `d ≫ cokernel.π c` through `b`
  refine KernelFork.IsLimit.ofι' b hzero (fun {T} k hk => ?_)
  have hk' : (k ≫ d) ≫ cokernel.π c = 0 := by
    rw [Category.assoc]
    exact hk
  -- `k ≫ d` factors through the mono `c`, and then the pullback property applies
  exact ⟨hp.lift k (Abelian.monoLift c (k ≫ d) hk')
      (Abelian.monoLift_comp c (k ≫ d) hk').symm, hp.lift_fst _ _ _⟩

end Work.ANALYTIC
