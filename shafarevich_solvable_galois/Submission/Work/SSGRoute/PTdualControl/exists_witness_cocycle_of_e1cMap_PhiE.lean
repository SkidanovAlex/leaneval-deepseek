import Mathlib
import Submission.Work.SSGRoute.E1cGeneric.Canonical
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A witnessing cocycle for `e1cMap R (PhiE R y)`, with a good lift

The `E1c` dictionary `e1cMap R : Ext¹_G(R,Kˣ) → H¹(Γ, Hom_ℤ(R,Ωˣ))` is *defined* as
`betaEquiv⁻¹ ∘ e2LocMap ∘ e1Loc` (`E1cGeneric/Canonical.lean`), so a class in its image is not
by itself equipped with a representative `1`-cocycle.  This file produces, for the `PhiE`-generators
of the coefficient `R₁ = E1cR1 R`, an explicit cocycle `c ∈ Z¹(Γ, Hom_ℤ(R,Ωˣ))` representing the
class `e1cMap R (PhiE R y)`, together with a lift `n : Hom_ℤ(F,Ωˣ)` of `ΨE y` along `π` whose
coboundary `d⁰n` is `ι ∘ c`:

* `π n = (ΨE y)` (the `H⁰`-element `PsiEMap (E1cR1 R) y`), and
* `ι (c γ) = cnj γ n - n` for every `γ : Γ`, i.e. `ι ∘ c = d⁰ n`.

This is the `H¹`-level input of the exactness argument for the *subgroup* restriction
(`resH1 D`): the two displayed properties are exactly what turns `resH1 D (e1cMap R (PhiE R y)) = 0`,
i.e. `d⁰ m = c|_D`, into a `D`-invariant lift `n - ι m` of `ΨE y`; see
`PTdualControl.exists_invariant_extension_of_resH1_e1cMap_eq_zero_inf`.

The construction is the one already used in `betaH_surjective`
(`E1cGeneric/Canonical.lean`): `exists_good_lift` supplies a lift `n` of `ΨE y` *with an open
subgroup fixing it*, which makes `γ ↦ ι⁻¹(cnj γ n - n)` locally constant without any discreteness
hypothesis on `Hom_ℤ(F,Ωˣ)` (this is why `[Finite R.V]` is not needed here, only
`[Module.Finite ℤ R.V]` for `exists_good_lift`), and the class of that cocycle is computed by
`betaH_mk` + `betaRaw_congr`, whence the third clause by injectivity of `betaH`.
-/

namespace Work.SSGRoute.PTdualControl

open CategoryTheory SSGRoute.PTExt
open Work.SSGRoute.ExtChain.E1cGeneric

noncomputable section

variable {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

theorem exists_witness_cocycle_of_e1cMap_PhiE
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (y : CategoryTheory.Abelian.Ext (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R)
      (SSGRoute.PTExt.unitsK k K) 0) :
    ∃ (n : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (k := k) (Ω := Ω) (K := K) R)
      (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R))),
      Work.SSGRoute.ExtChain.E1cGeneric.piH (k := k) (Ω := Ω) (K := K) R n
        = (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap (k := k) (Ω := Ω) (K := K)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) y).1 ∧
      (∀ γ : Ω ≃ₐ[k] Ω,
        Work.SSGRoute.ExtChain.E1cGeneric.iotaH (k := k) (Ω := Ω) (K := K) R
            ((c : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K R) γ)
          = Work.SSGRoute.ExtChain.E1cGeneric.cnj (k := k) (Ω := Ω) (K := K) R γ n - n) ∧
      Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) c
        = Work.SSGRoute.ExtChain.E1cGeneric.e1cMap (k := k) (Ω := Ω) (K := K) R
            (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) R y) := by
  classical
  obtain ⟨n, hn, U, hUopen, hUn⟩ := exists_good_lift (k := k) (Ω := Ω) (K := K) R
    (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R) y).1
    (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R) y).2
  have hmem : ∀ γ : Ω ≃ₐ[k] Ω,
      cnj (k := k) (Ω := Ω) (K := K) R γ n - n
        ∈ (iotaH (k := k) (Ω := Ω) (K := K) R).range := by
    intro γ
    rw [iotaH_range_eq_piH_ker (k := k) (Ω := Ω) (K := K) R]
    rw [AddMonoidHom.mem_ker, map_sub, piH_cnj, hn,
      (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R) y).2 γ, sub_self]
  let c : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K R := fun γ => Classical.choose (hmem γ)
  have hc : ∀ γ, iotaH (k := k) (Ω := Ω) (K := K) R (c γ)
      = cnj (k := k) (Ω := Ω) (K := K) R γ n - n := fun γ =>
    Classical.choose_spec (hmem γ)
  have hcross : Work.GroupCohomology.IsCrossedHom (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K R) c := by
    intro γ δ
    apply iotaH_injective (k := k) (Ω := Ω) (K := K) R
    rw [map_add, hc (γ * δ), iotaH_smul, hc δ, hc γ, cnj_sub, cnj_cnj]
    abel
  have hloc : Work.AbsoluteKummer.IsLocallyConstant c := by
    intro γ₀
    refine ⟨(fun y => γ₀⁻¹ * y) ⁻¹' U, hUopen.preimage
      (continuous_const.mul continuous_id), ?_, ?_⟩
    · show γ₀⁻¹ * γ₀ ∈ U
      rw [inv_mul_cancel]
      exact Subgroup.one_mem U
    · intro y hy
      rw [Set.mem_preimage] at hy
      have hy' : y = γ₀ * (γ₀⁻¹ * y) := by group
      have htau : c (γ₀⁻¹ * y) = 0 := by
        apply iotaH_injective (k := k) (Ω := Ω) (K := K) R
        rw [map_zero, hc]
        rw [show cnj (k := k) (Ω := Ω) (K := K) R (γ₀⁻¹ * y) n = n
          from hUn (γ₀⁻¹ * y) hy, sub_self]
      rw [hy', hcross γ₀ (γ₀⁻¹ * y), htau]
      rw [show (γ₀ • (0 : Work.SSGRoute.homCoind k Ω K R)) = 0 from by
        show (Work.SSGRoute.homCoind.smulHom γ₀).comp ((0 : Work.SSGRoute.homCoind k Ω K R).comp
          ((R.ρ (SSGRoute.res k K γ₀)⁻¹).toAddMonoidHom)) = 0
        rw [AddMonoidHom.zero_comp, AddMonoidHom.comp_zero], zero_add]
  have hz1 : c ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) :=
    (Work.AbsoluteKummer.mem_Z1_iff c).mpr ⟨hcross, hloc⟩
  let cZ : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)) := ⟨c, hz1⟩
  -- `betaH` of the class of `cZ` is `mk' (ΨE y)`
  have hbeta : betaH (k := k) (Ω := Ω) (K := K) R
        (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) cZ)
      = QuotientAddGroup.mk'
          (piH0 (k := k) (Ω := Ω) (K := K) R).range
          (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R) y) := by
    rw [show Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) cZ
        = QuotientAddGroup.mk'
            ((Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)).comap
              (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω)
                (Work.SSGRoute.homCoind k Ω K R)).subtype) cZ from rfl]
    rw [betaH_mk]
    have hdn : Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω)
        (E1cN (k := k) (Ω := Ω) (K := K) R) n =
        ((Work.AbsoluteKummer.mapZ1 (iotaH (k := k) (Ω := Ω) (K := K) R)
            (iotaH_equivariant (k := k) (Ω := Ω) (K := K) R) cZ :
          ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω)
            (E1cN (k := k) (Ω := Ω) (K := K) R))) :
            (Ω ≃ₐ[k] Ω) → E1cN (k := k) (Ω := Ω) (K := K) R) := by
      funext γ
      rw [Work.AbsoluteKummer.mapZ1_apply, d0_cnj]
      exact (hc γ).symm
    have hcongr := betaRaw_congr (k := k) (Ω := Ω) (K := K) R cZ n hdn
    rw [← hcongr]
    congr 1
    apply Subtype.ext
    exact hn
  refine ⟨n, cZ, hn, fun γ => hc γ, ?_⟩
  -- the class of `cZ` is `e1cMap R (PhiE R y)`
  apply betaH_injective (k := k) (Ω := Ω) (K := K) R
  rw [hbeta,
    e1cMap_Phi (k := k) (Ω := Ω) (K := K) R y,
    ← betaEquiv_apply (k := k) (Ω := Ω) (K := K) R
      ((betaEquiv (k := k) (Ω := Ω) (K := K) R).symm
        (QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
          (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R) y)))]
  exact (AddEquiv.apply_symm_apply (betaEquiv (k := k) (Ω := Ω) (K := K) R)
    (QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
      (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R) y))).symm

end

end Work.SSGRoute.PTdualControl
