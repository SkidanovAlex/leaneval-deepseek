import Mathlib
import Submission.Work.SSGRoute.PTdualControl.archimedeanReduction_via_cruxA
import Submission.Work.SSGRoute.PTdualControl.exists_witness_cocycle_of_e1cMap_PhiE
import Submission.Work.SSGRoute.PTdualControl.exists_invariant_extension_of_d0_resZ1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The infinite-place exactness step: an invariant extension of `ΨE y` from the vanishing of
`resH1 D (e1cMap R (PhiE R y))`

The `E1c` dictionary sends the `PhiE`-generator of `Ext¹_G(R,Kˣ)` to `H¹(Γ, Hom_ℤ(R,Ωˣ))`; by
`e1cMap_Phi` its value is `betaEquiv⁻¹ (mk' (ΨE y))`, so the *only* information the hypothesis
`resH1 D (e1cMap R (PhiE R y)) = 0` carries is an equation in `H¹(D, Hom_ℤ(R,Ωˣ))`.  The proof
therefore

* lifts `PsiEMap (E1cR1 R) y` along `π = piH` to `n : Hom_ℤ(F,Ωˣ)` together with a cocycle
  `c ∈ Z¹(Γ, Hom_ℤ(R,Ωˣ))` whose class is `e1cMap R (PhiE R y)` and which satisfies
  `ι ∘ c = d⁰ n` (`exists_witness_cocycle_of_e1cMap_PhiE`; note that no finiteness of the *type*
  `R.V` is needed, only `[Module.Finite ℤ R.V]`, because the lift is built by `exists_good_lift`),
* rewrites the hypothesis as `d⁰ m = c|_D` for some `m : Hom_ℤ(R,Ωˣ)`
  (`resH1_H1π`, `H1π_eq_zero_iff`, `mem_B1_iff`),
* and concludes by abstract algebra alone: `Φ := n - ι m` is `D`-invariant and still lifts
  `ΨE y` (`exists_invariant_extension_of_d0_resZ1`).

This is the exactness of the dualised canonical resolution
`0 → Hom_ℤ(R,Ωˣ) → Hom_ℤ(F,Ωˣ) → Hom_ℤ(R₁,Ωˣ) → 0` at `H⁰` over the subgroup `D`, obtained
*without* the middle term `Hom_ℤ(F,Ωˣ)` having to be discrete — which is exactly what fails for an
infinite index set `R.V`, i.e. what excludes the `[Finite R.V]` versions of the same statement
(`archimedeanCruxA.exists_extension_of_resH1_e1cMap_PhiE_eq_zero`,
`E1aClean.exists_invariant_extension_of_resH1_e1cMap_eq_zero`).
-/

namespace Work.SSGRoute.PTdualControl

theorem exists_invariant_extension_of_resH1_e1cMap_eq_zero_inf
    {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (D : Subgroup (Ω ≃ₐ[k] Ω))
    (y : CategoryTheory.Abelian.Ext (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R)
      (SSGRoute.PTExt.unitsK k K) 0)
    (h : Work.SSGRoute.PT.H2Fin.resH1 D (Work.SSGRoute.homCoind k Ω K R)
      (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap R
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE R y)) = 0) :
    ∃ Φ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) R,
      Φ ∈ Work.AbsoluteKummer.H0 ↥D
          (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) R) ∧
      Φ.comp (Work.SSGRoute.ExtChain.E1cGeneric.kappa R)
        = (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) y).1 := by
  -- a witnessing cocycle for the class of `e1cMap R (PhiE R y)`, with a lift of `ΨE y`
  obtain ⟨n, c, hn, hc, hcl⟩ :=
    exists_witness_cocycle_of_e1cMap_PhiE (k := k) (Ω := Ω) (K := K) R y
  -- the hypothesis becomes `d⁰ m = c|_D`
  rw [← hcl] at h
  rw [Work.SSGRoute.PT.H2Fin.resH1_H1π D (Work.SSGRoute.homCoind k Ω K R) c] at h
  rw [Work.AbsoluteKummer.H1π_eq_zero_iff] at h
  obtain ⟨m, hm⟩ := (Work.AbsoluteKummer.mem_B1_iff (G := ↥D)
    (M := Work.SSGRoute.homCoind k Ω K R) _).mp h
  -- `Φ := n - ι m` is `D`-invariant and lifts `ΨE y`
  exact exists_invariant_extension_of_d0_resZ1 (k := k) (Ω := Ω) (K := K) R D
    (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K)
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) y) n c hn hc m hm

end Work.SSGRoute.PTdualControl
