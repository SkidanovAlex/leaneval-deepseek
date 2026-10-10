import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV.CTAux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

theorem exists_algHom_ratFunc_of_image_X {𝕜 M F : Type*} [Field 𝕜] [Field M] [Algebra 𝕜 M]
    [Field F] [Algebra 𝕜 F] [Algebra (RatFunc 𝕜) F] [IsScalarTower 𝕜 (RatFunc 𝕜) F]
    (ι : F →ₐ[𝕜] RatFunc M) (m : M)
    (hm : algebraMap M (RatFunc M) m = ι (algebraMap (RatFunc 𝕜) F (RatFunc.X : RatFunc 𝕜))) :
    ∃ χ : RatFunc 𝕜 →ₐ[𝕜] M, χ (RatFunc.X : RatFunc 𝕜) = m ∧
      ∀ k : RatFunc 𝕜, ι (algebraMap (RatFunc 𝕜) F k) = algebraMap M (RatFunc M) (χ k) := by
  -- `ψ` is the structural map `M → M(y)`, `Φ` the composite `𝕜(t) → F → M(y)`.
  let ψ : M →ₐ[𝕜] RatFunc M := IsScalarTower.toAlgHom 𝕜 M (RatFunc M)
  let Φ : RatFunc 𝕜 →ₐ[𝕜] RatFunc M := ι.comp (IsScalarTower.toAlgHom 𝕜 (RatFunc 𝕜) F)
  -- `hm` says that the two algebra homomorphisms agree at the generator `t = X`.
  have hψm : ψ m = Φ (RatFunc.X : RatFunc 𝕜) := by
    show algebraMap M (RatFunc M) m = _; rw [hm]; rfl
  -- Hence `ψ ∘ (eval at m) = Φ ∘ (polynomial → rational function)` on `𝕜[X]`.
  have hcomm : (ψ.comp (Polynomial.aeval m : Polynomial 𝕜 →ₐ[𝕜] M))
      = Φ.comp (IsScalarTower.toAlgHom 𝕜 (Polynomial 𝕜) (RatFunc 𝕜)) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.coe_comp, Function.comp_apply, Polynomial.aeval_X,
      IsScalarTower.toAlgHom_apply, RatFunc.algebraMap_X]
    exact hψm
  have hcomm' : ∀ p : Polynomial 𝕜,
      ψ ((Polynomial.aeval m) p) = Φ (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) p) :=
    fun p => DFunLike.congr_fun hcomm p
  have hΦinj : Function.Injective Φ := fun _ _ h => RingHom.injective Φ.toRingHom h
  -- Consequently `m` is transcendental over `𝕜`: evaluation at `m` is injective.
  have hinj : Function.Injective (Polynomial.aeval m : Polynomial 𝕜 →ₐ[𝕜] M) := by
    intro p q hpq
    have h2 : ψ ((Polynomial.aeval m) p) = ψ ((Polynomial.aeval m) q) := by rw [hpq]
    rw [hcomm' p, hcomm' q] at h2
    exact RatFunc.algebraMap_injective 𝕜 (hΦinj h2)
  -- The universal property of the fraction field turns evaluation at `m` into `χ`.
  let χ : RatFunc 𝕜 →ₐ[𝕜] M :=
    IsFractionRing.liftAlgHom (g := (Polynomial.aeval m : Polynomial 𝕜 →ₐ[𝕜] M)) hinj
  have hχX : χ (RatFunc.X : RatFunc 𝕜) = m := by
    rw [← RatFunc.algebraMap_X]
    rw [show χ (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) Polynomial.X)
        = IsFractionRing.lift (g := ((Polynomial.aeval m : Polynomial 𝕜 →ₐ[𝕜] M).toRingHom)) hinj
          (algebraMap (Polynomial 𝕜) (RatFunc 𝕜) Polynomial.X) from rfl]
    rw [IsFractionRing.lift_algebraMap
      (g := ((Polynomial.aeval m : Polynomial 𝕜 →ₐ[𝕜] M).toRingHom)) hinj Polynomial.X]
    exact Polynomial.aeval_X m
  refine ⟨χ, hχX, ?_⟩
  intro k
  -- `ψ ∘ χ = Φ` since both are `𝕜`-algebra maps `𝕜(t) → M(y)` agreeing at `t`.
  have hcomp : ψ.comp χ = Φ := by
    apply Work.MotV.ratFunc_algHom_ext
    simp only [AlgHom.coe_comp, Function.comp_apply]
    rw [hχX]
    exact hψm
  change Φ k = ψ (χ k)
  exact (DFunLike.congr_fun hcomp k).symm

end Work.MotV
