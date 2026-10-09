import Mathlib
import Submission.Work.SSGRoute.PTCore.H2_level_defs
import Submission.Work.SSGRoute.Nakayama.exists_level_of_locallyConstant_isGalois
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Covering of `H²(G_F, k̄ˣ)` by its finite levels

Every class of `H²(G_F, k̄ˣ)` is the inflation of a class of a finite Galois level.

Given a locally constant `2`-cocycle `c` representing the class, the compactness lemma
`Work.SSGRoute.Nakayama.exists_level_of_locallyConstant_isGalois` produces a finite Galois level
`L` such that `c (g * σ, h * τ) = c (g, h)` for `σ, τ ∈ Gal(k̄/L)` and all values of `c` lie in
`Lˣ`.  Choosing a section `sec` of `Gal(L/F) → G_F`, the descended cochain
`d (γ, δ) = inclL⁻¹ (c (sec γ, sec δ))` is well defined, lands in `Lˣ`, satisfies the level
`2`-cocycle identity (by the cocycle identity for `c` together with the bi-invariance), and its
inflation is literally `c`; hence `psiTilde L [d] = [c] = x`.
-/

noncomputable section

open scoped Classical
open Work.AbsoluteKummer

namespace Work.SSGRoute.PTCore

variable {F : Type} [Field F] [IsGalois F (AlgebraicClosure F)]

/-- **Covering of `H²(G_F, k̄ˣ)` by its finite levels.**  Every class is the inflation of a class
of a finite Galois level. -/
theorem H2_level_cover_alt (x : Work.AbsoluteKummer.H2 (Work.AbsoluteKummer.G F)
    (Additive (AlgebraicClosure F)ˣ)) :
    ∃ L : FiniteGaloisIntermediateField F (AlgebraicClosure F),
      x ∈ Set.range (psiTilde (F := F) L) := by
  classical
  -- a locally constant `2`-cocycle representing the class
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((B2 (Work.AbsoluteKummer.G F) (UnitsK F)).comap
      (Z2 (Work.AbsoluteKummer.G F) (UnitsK F)).subtype) x
  let cf : AbsGal F × AbsGal F → UnitsK F :=
    (c : Work.AbsoluteKummer.G F × Work.AbsoluteKummer.G F → UnitsK F)
  have hcross : ∀ g h k : AbsGal F,
      cf (g * h, k) + cf (g, h) = g • cf (h, k) + cf (g, h * k) :=
    ((mem_Z2_iff (c : Work.AbsoluteKummer.G F × Work.AbsoluteKummer.G F → UnitsK F)).mp c.2).1
  have hloc : Work.AbsoluteKummer.IsLocallyConstant cf :=
    ((mem_Z2_iff (c : Work.AbsoluteKummer.G F × Work.AbsoluteKummer.G F → UnitsK F)).mp c.2).2
  -- the level of bi-invariance and of values supplied by compactness
  obtain ⟨L, hbi, hval⟩ :=
    Work.SSGRoute.Nakayama.exists_level_of_locallyConstant_isGalois F cf hloc
  have hval' : ∀ g h : AbsGal F, ∃ y : (↥L)ˣ,
      Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom y = Additive.toMul (cf (g, h)) :=
    fun g h => hval g h
  -- a section of the restriction
  set sec : LevelGal L → AbsGal F := fun γ => Classical.choose (resL_surjective L γ) with hsec_def
  have hsec : ∀ γ : LevelGal L, resL L (sec γ) = γ :=
    fun γ => Classical.choose_spec (resL_surjective L γ)
  -- the descended cochain
  set dFun : LevelGal L × LevelGal L → UnitsL L :=
    fun p => Additive.ofMul (Classical.choose (hval' (sec p.1) (sec p.2))) with hdFun_def
  have hdFun_spec : ∀ p : LevelGal L × LevelGal L,
      inclL L (dFun p) = cf (sec p.1, sec p.2) := by
    intro p
    have h := Classical.choose_spec (hval' (sec p.1) (sec p.2))
    show Additive.ofMul (Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom
      (Classical.choose (hval' (sec p.1) (sec p.2)))) = cf (sec p.1, sec p.2)
    rw [h, ofMul_toMul]
  -- the descended cochain is a level `2`-cocycle
  have hcorr : ∀ γ δ : LevelGal L,
      ((sec (γ * δ))⁻¹ * (sec γ * sec δ)) ∈ lvlFix L := by
    intro γ δ
    rw [← mem_ker_resL_iff L]
    rw [map_mul, map_mul, map_inv, hsec (γ * δ), hsec γ, hsec δ]
    group
  have hcoc : dFun ∈ LevelCocycles L := by
    rw [mem_cocycles₂_iff_add]
    intro γ δ ε
    have h1 := hcross (sec γ) (sec δ) (sec ε)
    have hu : ((sec (γ * δ))⁻¹ * (sec γ * sec δ)) ∈ lvlFix L := hcorr γ δ
    have hv : ((sec (δ * ε))⁻¹ * (sec δ * sec ε)) ∈ lvlFix L := hcorr δ ε
    have e1 : cf (sec γ * sec δ, sec ε) = cf (sec (γ * δ), sec ε) := by
      have h := hbi (sec (γ * δ)) (sec ε) ((sec (γ * δ))⁻¹ * (sec γ * sec δ)) 1 hu
        (Subgroup.one_mem _)
      rw [show sec (γ * δ) * ((sec (γ * δ))⁻¹ * (sec γ * sec δ)) = sec γ * sec δ from by group,
        mul_one] at h
      exact h
    have e2 : cf (sec γ, sec δ * sec ε) = cf (sec γ, sec (δ * ε)) := by
      have h := hbi (sec γ) (sec (δ * ε)) 1 ((sec (δ * ε))⁻¹ * (sec δ * sec ε))
        (Subgroup.one_mem _) hv
      rw [mul_one,
        show sec (δ * ε) * ((sec (δ * ε))⁻¹ * (sec δ * sec ε)) = sec δ * sec ε from by group] at h
      exact h
    apply inclL_injective L
    rw [map_add, map_add]
    show inclL L (dFun (γ * δ, ε)) + inclL L (dFun (γ, δ))
      = inclL L ((LevelRep L).ρ γ (dFun (δ, ε))) + inclL L (dFun (γ, δ * ε))
    simp only [hdFun_spec]
    rw [show (LevelRep L).ρ γ (dFun (δ, ε))
        = (LevelRep L).ρ (resL L (sec γ)) (dFun (δ, ε)) from by rw [hsec γ],
      inclL_rho L (sec γ) (dFun (δ, ε))]
    simp only [hdFun_spec]
    rw [← e1, ← e2]
    exact h1
  -- the inflation of the descended cocycle is literally `c`
  have hcoin : inflCo (F := F) L ⟨dFun, hcoc⟩ = c := by
    apply Subtype.ext
    funext p
    obtain ⟨g, h⟩ := p
    show inclL L (dFun (resL L g, resL L h)) = cf (g, h)
    rw [hdFun_spec (resL L g, resL L h)]
    have hu : ((sec (resL L g))⁻¹ * g) ∈ lvlFix L := by
      rw [← mem_ker_resL_iff L]
      rw [map_mul, map_inv, hsec (resL L g)]
      group
    have hv : ((sec (resL L h))⁻¹ * h) ∈ lvlFix L := by
      rw [← mem_ker_resL_iff L]
      rw [map_mul, map_inv, hsec (resL L h)]
      group
    have e3 := hbi (sec (resL L g)) (sec (resL L h)) ((sec (resL L g))⁻¹ * g)
      ((sec (resL L h))⁻¹ * h) hu hv
    rw [show (sec (resL L g) * ((sec (resL L g))⁻¹ * g),
        sec (resL L h) * ((sec (resL L h))⁻¹ * h)) = (g, h) from by
      rw [show sec (resL L g) * ((sec (resL L g))⁻¹ * g) = g from by group,
        show sec (resL L h) * ((sec (resL L h))⁻¹ * h) = h from by group]] at e3
    exact e3.symm
  refine ⟨L, ?_⟩
  refine ⟨QuotientAddGroup.mk' _ ⟨dFun, hcoc⟩, ?_⟩
  rw [psiTilde_mk, hcoin]
  exact hc

end Work.SSGRoute.PTCore
