import Mathlib
import Submission.Work.SSGRoute.ELFDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of the `p`-quotient of a free representation

For a finite group `G` and a finite type `α`, the free `ℤ[G]`-representation
`Rep.free (ULift ℤ) G α` has the property that its quotient by the range of multiplication by
`p ≠ 0` is finite: additively it is the free abelian group on the finite set `α × G`, so its
`p`-quotient is the free `ℤ/p`-module on `α × G`.

The argument is staged:

* `Work.SSGRoute.FreeRepQuot.finite_quot_nsmul_finsupp_int`: the base case `ι →₀ ℤ` for finite
  `ι`, proved by exhibiting the explicit isomorphism
  `(ι →₀ ℤ) ⧸ p·(ι →₀ ℤ) ≅ ι → ZMod p`;
* `Work.SSGRoute.FreeRepQuot.finite_quot_nsmul_of_surjective`: the class of additive groups
  whose `p`-quotient is finite is closed under quotients;
* `Work.SSGRoute.FreeRepQuot.freeQuotSurj`: an explicit surjection of additive groups
  `(α × G →₀ ℤ) →+ Rep.free k G α` (coefficient extraction, `k ≃+ ℤ`, and currying).

The target `Work.SSGRoute.freeRep_quot_nsmul_finite` combines these three.
-/

namespace Work.SSGRoute

noncomputable section

universe u v w

namespace FreeRepQuot

/-- The additive isomorphism `ULift ℤ ≃+ ℤ` given by `ULift.down`. -/
def uliftIntAddEquiv : ULift.{u} ℤ ≃+ ℤ where
  toFun x := x.down
  invFun x := ULift.up x
  left_inv x := by cases x; rfl
  right_inv x := rfl
  map_add' x y := by cases x; cases y; rfl

/-- **Base case.** For a finite index type `ι` and `p ≠ 0`, the quotient of the free abelian
group `ι →₀ ℤ` by the range of multiplication by `p` is finite.

Indeed the additive map `f ↦ (i ↦ (f i : ZMod p))` has kernel exactly `p • (ι →₀ ℤ)`, and its
range lies in the finite type `ι → ZMod p`. -/
theorem finite_quot_nsmul_finsupp_int (ι : Type) [Finite ι] (p : ℕ) (hp : p ≠ 0) :
    Finite ((ι →₀ ℤ) ⧸ (nsmulAddHom p (ι →₀ ℤ)).range) := by
  classical
  haveI : NeZero p := ⟨hp⟩
  let ψ : (ι →₀ ℤ) →+ (ι → ZMod p) :=
    { toFun := fun f => fun i => (f i : ZMod p)
      map_zero' := by ext i; simp
      map_add' := by intro f g; ext i; simp [Finsupp.add_apply] }
  have hψ : ∀ (f : ι →₀ ℤ) (i : ι), ψ f i = (f i : ZMod p) := fun f i => rfl
  have hker : ψ.ker = (nsmulAddHom p (ι →₀ ℤ)).range := by
    ext f
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · intro hf
      have hfi : ∀ i, (f i : ZMod p) = 0 := fun i => by
        have := congrFun hf i
        rwa [hψ] at this
      refine ⟨f.mapRange (fun z => z / (p : ℤ)) (by simp), ?_⟩
      ext i
      rw [nsmulAddHom_apply, Finsupp.nsmul_apply, Finsupp.mapRange_apply]
      have hdvd : (p : ℤ) ∣ f i := (ZMod.intCast_zmod_eq_zero_iff_dvd (f i) p).mp (hfi i)
      rw [nsmul_eq_mul, Int.mul_ediv_cancel' hdvd]
    · rintro ⟨g, rfl⟩
      funext i
      rw [hψ, nsmulAddHom_apply, Finsupp.nsmul_apply]
      simp
  rw [← hker]
  exact Finite.of_injective (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv (Equiv.injective _)

/-- **Descent along a surjection.** If the `p`-quotient of an additive group `M` is finite, then
so is the `p`-quotient of every additive quotient `N` of `M`. -/
theorem finite_quot_nsmul_of_surjective {M : Type u} {N : Type v} [AddCommGroup M]
    [AddCommGroup N] (f : M →+ N) (hf : Function.Surjective f) (p : ℕ)
    [Finite (M ⧸ (nsmulAddHom p M).range)] :
    Finite (N ⧸ (nsmulAddHom p N).range) := by
  let H : AddSubgroup M := (nsmulAddHom p M).range
  let H' : AddSubgroup N := (nsmulAddHom p N).range
  haveI : Finite (M ⧸ H) := ‹Finite (M ⧸ (nsmulAddHom p M).range)›
  let φ : M →+ N ⧸ H' := (QuotientAddGroup.mk' H').comp f
  have hle : H ≤ φ.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker]
    obtain ⟨y, hy⟩ : ∃ y, nsmulAddHom p M y = x := by simpa [H] using hx
    rw [← hy]
    show (QuotientAddGroup.mk' H') (f (nsmulAddHom p M y)) = 0
    rw [nsmulAddHom_apply, map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact AddMonoidHom.mem_range.mpr ⟨f y, rfl⟩
  let g : M ⧸ H →+ N ⧸ H' := QuotientAddGroup.lift H φ hle
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨n, rfl⟩ := QuotientAddGroup.mk_surjective y
    obtain ⟨m, rfl⟩ := hf n
    exact ⟨QuotientAddGroup.mk m, by rw [QuotientAddGroup.lift_mk]; rfl⟩
  have hfin : Finite (N ⧸ H') := Finite.of_surjective g hg
  simpa [H'] using hfin

/-- For a commutative ring `k` additively isomorphic to `ℤ` and a group `G`, the underlying
additive group of `Rep.free k G α` is a quotient of the free abelian group on `α × G`: a function
on `α × G` is sent to the `k[G]`-element with the corresponding coefficients. -/
def freeQuotSurj (k G α : Type*) [CommRing k] [Group G] (e : k ≃+ ℤ) :
    (α × G →₀ ℤ) →+ (↥(Rep.free k G α)) :=
  ((Finsupp.mapRange.addEquiv MonoidAlgebra.coeffAddEquiv.symm).toAddMonoidHom.comp
    ((Finsupp.mapRange.addEquiv (Finsupp.mapRange.addEquiv e.symm)).toAddMonoidHom.comp
      Finsupp.curryAddEquiv.toAddMonoidHom))

theorem freeQuotSurj_surjective (k G α : Type*) [CommRing k] [Group G] (e : k ≃+ ℤ) :
    Function.Surjective (freeQuotSurj k G α e) :=
  (Finsupp.mapRange.addEquiv MonoidAlgebra.coeffAddEquiv.symm).surjective.comp
    ((Finsupp.mapRange.addEquiv (Finsupp.mapRange.addEquiv e.symm)).surjective.comp
      Finsupp.curryAddEquiv.surjective)

end FreeRepQuot

theorem freeRep_quot_nsmul_finite (G α : Type) [Group G] [Finite G] [Finite α] (p : ℕ) (hp : p ≠ 0) :
    Finite (↥(Rep.free (ULift ℤ) G α) ⧸
      (Work.SSGRoute.nsmulAddHom p ↥(Rep.free (ULift ℤ) G α)).range) := by
  haveI : Finite (α × G) := inferInstance
  haveI : Finite ((α × G →₀ ℤ) ⧸ (nsmulAddHom p (α × G →₀ ℤ)).range) :=
    FreeRepQuot.finite_quot_nsmul_finsupp_int (α × G) p hp
  exact FreeRepQuot.finite_quot_nsmul_of_surjective
    (FreeRepQuot.freeQuotSurj (ULift ℤ) G α FreeRepQuot.uliftIntAddEquiv)
    (FreeRepQuot.freeQuotSurj_surjective (ULift ℤ) G α FreeRepQuot.uliftIntAddEquiv) p

end

end Work.SSGRoute
