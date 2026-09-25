import Mathlib
import Submission.NK.Reconstruct.torsionFreeGamma
import Submission.NK.Reconstruct.gammaBaseChange_toAdditive_mem_torsion

/-!
# Lifting a continuous homomorphism `Γ_{K₁} → Γ_{K₂}` to the torsion-free quotients

The ℓ-adic abelianisation `NK.Reconstruct.Gamma K K' ℓ = G_K^{ab,(ℓ)}` of
`GammaObject.lean` is the *pro-ℓ* group, and its `ℤ_ℓ`-module structure
(`GammaModule.lean`) makes it a quotient of the torsion-free group
`NK.Reconstruct.GammaTF K K' ℓ = G_K^{ab,(ℓ),/\tor}` of Shimizu's §4.

The content of this file is that the quotient map is *natural* for an arbitrary
*continuous* homomorphism of the ℓ-adic abelianisations: every such `f` descends to a
continuous additive homomorphism `g` of the torsion-free quotients, satisfying

  `g ∘ mk₁ = mk₂ ∘ f`   (additively).

Two points are worth isolating, because neither needs the continuity hypothesis at the
level of *existence*:

* **Torsion is preserved by any homomorphism.**  An element of `Γ_K` is `ℤ_ℓ`-torsion as
  soon as it is killed by a non-zero natural number
  (`NK.Reconstruct.exists_nat_nsmul_eq_zero_of_mem_gammaTorsion`), and any additive map
  commutes with `n`-fold sums.  Moreover the `ℤ_ℓ`-scalar action of the natural number `n`
  *is* the `n`-fold sum (`Nat.cast_smul_eq_nsmul`), so `f` carries `ℤ_ℓ`-torsion into
  `ℤ_ℓ`-torsion.  Hence `mk₂ ∘ f` vanishes on `GammaTorsion`, and `g` exists by the
  universal property of the quotient (`QuotientAddGroup.lift`).
* **Continuity is automatic from the quotient topology.**  `Γ_K` carries the quotient
  topology of the projection `mk₁` (`isQuotientMap_quotient_mk'`), so `g` is continuous iff
  `g ∘ mk₁ = mk₂ ∘ f` is, which it is because `f` is.

## Contents

* `NK.Reconstruct.gammaTorsion_toAdditive_mem` — a homomorphism of ℓ-adic
  abelianisations carries `ℤ_ℓ`-torsion into `ℤ_ℓ`-torsion;
* `NK.Reconstruct.exists_gammaTF_lift` — the descent of a continuous `f` to the
  torsion-free quotients, together with its continuity.
-/

set_option linter.unusedSectionVars false

namespace NK.Reconstruct

open scoped Pointwise

section Torsion

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsGalois K K'] {M : Type*} [Field M] [NumberField M] {M' : Type*} [Field M']
  [Algebra M M'] [IsGalois M M'] {ℓ : ℕ} [Fact ℓ.Prime]

/-- **A homomorphism of ℓ-adic abelianisations carries `ℤ_ℓ`-torsion into `ℤ_ℓ`-torsion.**

A torsion element of `Additive (Gamma K K' ℓ)` is killed by some non-zero natural number `n`
(`NK.Reconstruct.exists_nat_nsmul_eq_zero_of_mem_gammaTorsion`).  The additive homomorphism
underlying `f` commutes with `n`-fold sums, and the `ℤ_ℓ`-scalar action of `n` is the `n`-fold
sum (`Nat.cast_smul_eq_nsmul`), so the image is again torsion. -/
theorem gammaTorsion_toAdditive_mem (f : Gamma K K' ℓ →* Gamma M M' ℓ)
    {x : Additive (Gamma K K' ℓ)} (hx : x ∈ GammaTorsion (K := K) (K' := K') ℓ) :
    MonoidHom.toAdditive f x ∈ GammaTorsion (K := M) (K' := M') ℓ := by
  obtain ⟨n, hn, hzero⟩ :=
    exists_nat_nsmul_eq_zero_of_mem_gammaTorsion (K := K) (K' := K') hx
  refine mem_gammaTorsion_of_nat_smul_eq_zero (K := M) (K' := M') hn ?_
  rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, hzero, map_zero]

end Torsion

/-- **A continuous homomorphism of ℓ-adic abelianisations descends to the torsion-free
quotients.**  The descended map is the additive quotient map induced by `f`
(`QuotientAddGroup.lift`), it satisfies `g ∘ mk₁ = mk₂ ∘ f`, and it is continuous because `Γ_K`
carries the quotient topology of `mk₁`.

Note that the existence of `g` — and the commutation `g ∘ mk₁ = mk₂ ∘ f` — does not use the
continuity of `f`; only the continuity of `g` does. -/
theorem exists_gammaTF_lift {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] {K₁' K₂' : Type*} [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsGalois K₁ K₁'] [IsGalois K₂ K₂'] (ℓ : ℕ) [Fact ℓ.Prime]
    (f : Gamma K₁ K₁' ℓ →* Gamma K₂ K₂' ℓ) (hf : Continuous ⇑f) :
    ∃ g : GammaTF (K := K₁) (K' := K₁') ℓ →+ GammaTF (K := K₂) (K' := K₂') ℓ,
      (∀ x : Additive (Gamma K₁ K₁' ℓ),
        g (gammaTFMk (K := K₁) (K' := K₁') (ℓ := ℓ) x)
          = gammaTFMk (K := K₂) (K' := K₂') (ℓ := ℓ) (MonoidHom.toAdditive f x)) ∧
      Continuous (fun y => g y) := by
  -- The composite `mk₂ ∘ f` vanishes on the torsion submodule, so `f` descends.
  have hker : (GammaTorsion (K := K₁) (K' := K₁') ℓ).toAddSubgroup ≤
      ((gammaTFMk (K := K₂) (K' := K₂') (ℓ := ℓ)).toAddMonoidHom.comp
        (MonoidHom.toAdditive f)).ker := by
    intro x hx
    refine AddMonoidHom.mem_ker.mpr ?_
    change (GammaTorsion (K := K₂) (K' := K₂') ℓ).mkQ (MonoidHom.toAdditive f x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact gammaTorsion_toAdditive_mem f hx
  set g : GammaTF (K := K₁) (K' := K₁') ℓ →+ GammaTF (K := K₂) (K' := K₂') ℓ :=
    QuotientAddGroup.lift (GammaTorsion (K := K₁) (K' := K₁') ℓ).toAddSubgroup
      ((gammaTFMk (K := K₂) (K' := K₂') (ℓ := ℓ)).toAddMonoidHom.comp
        (MonoidHom.toAdditive f)) hker
  have hcomm : ∀ x : Additive (Gamma K₁ K₁' ℓ),
      g (gammaTFMk (K := K₁) (K' := K₁') (ℓ := ℓ) x)
        = gammaTFMk (K := K₂) (K' := K₂') (ℓ := ℓ) (MonoidHom.toAdditive f x) :=
    fun x => QuotientAddGroup.lift_mk _ hker x
  refine ⟨g, hcomm, ?_⟩
  -- Continuity: `Γ_{K₁}` carries the quotient topology of `mk₁`.
  have hq : Topology.IsQuotientMap (gammaTFMk (K := K₁) (K' := K₁') (ℓ := ℓ)) :=
    isQuotientMap_quotient_mk'
  rw [hq.continuous_iff]
  have hcomp : ((fun y : GammaTF (K := K₁) (K' := K₁') ℓ => g y)
      ∘ gammaTFMk (K := K₁) (K' := K₁') (ℓ := ℓ))
      = fun x : Additive (Gamma K₁ K₁' ℓ) =>
          gammaTFMk (K := K₂) (K' := K₂') (ℓ := ℓ) (MonoidHom.toAdditive f x) :=
    funext fun x => hcomm x
  rw [hcomp]
  exact continuous_quotient_mk'.comp hf

end NK.Reconstruct
