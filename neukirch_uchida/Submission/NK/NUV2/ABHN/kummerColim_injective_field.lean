/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Injectivity of the Kummer map on the colimits, over a characteristic-zero base field

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4 item 1, §10.4), and
`Submission/Work/NUV2/ABHN/`.

`NK.HassePrinciple.kummerColim_injective` proves that the Kummer map on the colimits

`kummerColim p V : MuColim p V → H2Units V`

is injective for a **number field** `K`.  The proof never uses anything arithmetic about `K`:
the only field-theoretic input is that the prime `p` is invertible at every level
(`IsSepClosed.exists_pow_nat_eq`, applied in the separably closed `K'`) and Hilbert 90 for the
finite Galois levels, which is valid over an arbitrary field.  This file records that the
statement therefore holds over an arbitrary **characteristic-zero** field `K` with separable
closure `K'`, which is the form in which the ABHN (Albert–Brauer–Hasse–Noether) development of
`Submission/Work/NUV2/ABHN/` consumes it — there the base field of the Kummer limit is the
`p`-adic completion of a number field, i.e. a characteristic-zero field that is *not* a number
field.

The two ingredients of the proof are copied from `kummerColim_injective.lean` verbatim, with
`[NumberField K]` weakened to `[CharZero K]`:

* `kummerLevel_kernel_dies_charZero` — **(★)** a level-wise `μ_p`-class killed by the level-wise
  Kummer map is killed by the transition map to a larger level;
* `kummerColim_injective_charZero` — the colimit statement, deduced from (★) and the normal form
  for equality in the colimit (`LevelSystem.ofLevel_eq_iff`).

The requested theorem `kummerColim_injective_field` is the specialisation to `K, K' : Type`.
-/

import Mathlib
import Submission.NK.HassePrinciple.kummerColim_injective

open CategoryTheory
namespace NK.NUV2.ABHN
open NK.HassePrinciple
open NK.BrauerHasse
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
universe u

/-! ## The level-wise kernel-dies statement over a characteristic-zero field -/

set_option maxHeartbeats 3200000 in
theorem kummerLevel_kernel_dies_charZero {K K' : Type u} [Field K] [CharZero K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (hp : p.Prime) (V : Subgroup (K' ≃ₐ[K] K'))
    (L : FiniteGaloisIntermediateField K K') (w : MuLevelH2 p V L)
    (hw : (kummerLevel p V L).hom w = 0) :
    ∃ (L' : FiniteGaloisIntermediateField K K') (h : L ≤ L'),
      (muLevelMap p V h).hom w = 0 := by
  revert hw
  refine groupCohomology.H2_induction_on w fun x hx => ?_
  set z : groupCohomology.cocycles₂ (unitsLevelRep V L) :=
    (groupCohomology.mapCocycles₂ (MonoidHom.id (LevelGroup V L)) (muToUnits p V L)) x with hz
  set zm : LevelGroup V L → LevelGroup V L → (↥L)ˣ := fun g h => (z (g,h)).toMul with hzm
  have hx₁ : (groupCohomology.H2π (unitsLevelRep V L)) z = 0 := by
    rw [hz, ← groupCohomology.H2π_comp_map_apply (MonoidHom.id (LevelGroup V L))
      (muToUnits p V L) x]
    exact hx
  obtain ⟨βm, hβ⟩ := exists_mul_cochain_of_H2π_eq_zero V L z hx₁
  -- relation
  have hrel : ∀ g h : LevelGroup V L,
      (levelGroupRestrictHom V L g : ↥L ≃ₐ[K] ↥L) • βm h / βm (g * h) * βm g = zm g h := by
    intro g h
    have h2 : (groupCohomology.d₁₂ (unitsLevelRep V L)).hom (fun g => Additive.ofMul (βm g)) (g,h)
        = z (g,h) := congrFun hβ (g,h)
    rw [show (groupCohomology.d₁₂ (unitsLevelRep V L)).hom (fun g => Additive.ofMul (βm g)) (g,h)
        = Additive.ofMul ((levelGroupRestrictHom V L g : ↥L ≃ₐ[K] ↥L) • βm h / βm (g*h) * βm g)
        from rfl] at h2
    rw [show z (g,h) = Additive.ofMul (zm g h) from rfl] at h2
    exact Additive.ofMul.injective h2
  have hzp : ∀ g h : LevelGroup V L, (zm g h) ^ p = 1 := by
    intro g h
    have h1 : z (g,h) = (muToUnits p V L).hom (x (g,h)) := by
      rw [hz, coe_mapCocycles₂_apply]
      rfl
    have h2 : zm g h = Additive.toMul (α := (↥L)ˣ) ((muToUnits p V L).hom (x (g,h))) := by
      show (z (g,h)).toMul = _
      rw [h1]
      rfl
    rw [h2]
    exact muToUnits_toMul_pow.{u, u} p V L (x (g,h))
  set c : LevelGroup V L → (↥L)ˣ := fun g => (βm g) ^ p with hc
  have hcocycle : ∀ g h : LevelGroup V L,
      c (g * h) = Units.map (levelGroupRestrictHom V L g : ↥L ≃ₐ[K] ↥L) (c h) * c g := by
    intro g h
    have h4 : ((levelGroupRestrictHom V L g : ↥L ≃ₐ[K] ↥L) • βm h / βm (g * h) * βm g) ^ p = 1 := by
      rw [hrel g h, hzp g h]
    have h5 : ((levelGroupRestrictHom V L g : ↥L ≃ₐ[K] ↥L) • βm h) ^ p * (βm g) ^ p
        / (βm (g * h)) ^ p = 1 := by
      simpa [div_mul_eq_mul_div, mul_pow, div_pow] using h4
    have h6 : ((levelGroupRestrictHom V L g : ↥L ≃ₐ[K] ↥L) • βm h) ^ p * (βm g) ^ p
        = (βm (g * h)) ^ p := by
      have := congrArg (fun y => y * (βm (g * h)) ^ p) h5
      simpa [div_mul_cancel, mul_comm, mul_assoc] using this
    show (βm (g*h))^p = Units.map (levelGroupRestrictHom V L g : ↥L ≃ₐ[K] ↥L) ((βm h)^p) * (βm g)^p
    rw [← h6]
    congr 1
    rw [map_pow, AlgEquiv.smul_units_def]
  obtain ⟨x₀, hx₀⟩ := hilbert90_levelGroup V L c hcocycle
  -- the level L'
  haveI : IsSepClosed K' := IsSepClosure.sep_closed K
  haveI : NeZero (p : K') := ⟨by
    intro h0
    have h1 : algebraMap K K' (p : K) = 0 := by rw [map_natCast, h0]
    have h2 : (p : K) = 0 := (algebraMap K K').injective (by simpa using h1)
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) h2⟩
  obtain ⟨a, ha⟩ := IsSepClosed.exists_pow_nat_eq (k := K') ((x₀ : ↥L) : K') p
  let L' : FiniteGaloisIntermediateField K K' :=
    FiniteGaloisIntermediateField.adjoin K ({a} : Set K') ⊔ L
  have hle : L ≤ L' := le_sup_right
  have ha_mem : a ∈ (L' : IntermediateField K K') := by
    have h1 : a ∈ (FiniteGaloisIntermediateField.adjoin K ({a} : Set K') : IntermediateField K K') :=
      FiniteGaloisIntermediateField.subset_adjoin K {a} (by simp)
    exact (show (FiniteGaloisIntermediateField.adjoin K ({a} : Set K') : IntermediateField K K')
        ≤ (L' : IntermediateField K K') from le_sup_left) h1
  have ha_ne : a ≠ 0 := by
    intro h0
    have h1 : ((x₀ : ↥L) : K') = 0 := by rw [← ha, h0, zero_pow hp.ne_zero]
    exact Units.ne_zero x₀ (Subtype.ext h1)
  let aE : ↥L' := ⟨a, ha_mem⟩
  let ã : (↥L')ˣ := Units.mk0 aE (by
    intro h0
    exact ha_ne (by simpa [aE] using congrArg (fun x : ↥L' => (x : K')) h0))
  let f : LevelGroup V L' →* LevelGroup V L := levelQuotHom (U := V) hle
  let βt : LevelGroup V L' → (↥L')ˣ := fun g =>
    Units.map (IntermediateField.inclusion hle).toMonoidHom (βm (f g))
  let uunit : LevelGroup V L' → (↥L')ˣ := fun g =>
    βt g * ã / Units.map (levelGroupRestrictHom V L' g : ↥L' ≃ₐ[K] ↥L') ã
  have hcomp : ∀ (g : LevelGroup V L') (y : (↥L)ˣ),
      Units.map (IntermediateField.inclusion hle).toMonoidHom
          (Units.map (levelGroupRestrictHom V L (f g) : ↥L ≃ₐ[K] ↥L) y)
        = Units.map (levelGroupRestrictHom V L' g : ↥L' ≃ₐ[K] ↥L')
          (Units.map (IntermediateField.inclusion hle).toMonoidHom y) := by
    intro g y
    induction g using QuotientGroup.induction_on with
    | H v =>
      rw [levelGroupRestrictHom_mk]
      rw [show (levelQuotHom (U := V) hle) (QuotientGroup.mk v) = QuotientGroup.mk v from rfl,
        levelGroupRestrictHom_mk]
      refine Units.ext (Subtype.ext ?_)
      simp only [Units.coe_map, MonoidHom.coe_coe]
      exact (IntermediateField.coe_inclusion hle
            (((levelRestrict L (v : Gal(K'/K))) ((y : (↥L)ˣ) : ↥L)))).trans
        ((AlgEquiv.restrictNormalHom_apply (L := (L : IntermediateField K K'))
            (v : Gal(K'/K)) ((y : (↥L)ˣ) : ↥L)).trans
        ((congrArg (fun z : K' => (v : Gal(K'/K)) z)
            (IntermediateField.coe_inclusion hle ((y : (↥L)ˣ) : ↥L)).symm).trans
        ((AlgEquiv.restrictNormalHom_apply (L := (L' : IntermediateField K K'))
            (v : Gal(K'/K)) ((IntermediateField.inclusion hle) ((y : (↥L)ˣ) : ↥L))).symm)))
  have hU : ã ^ p = Units.map (IntermediateField.inclusion hle).toMonoidHom x₀ := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val]
    rw [show ((ã : (↥L')ˣ) : ↥L') = aE from rfl]
    rw [show ((Units.map (IntermediateField.inclusion hle).toMonoidHom x₀ : (↥L')ˣ) : ↥L')
        = ((IntermediateField.inclusion hle) ((x₀ : (↥L)ˣ) : ↥L)) from rfl]
    refine Subtype.ext ?_
    push_cast
    rw [show ((aE : ↥L') : K') = a from rfl]
    rw [IntermediateField.coe_inclusion]
    exact ha
  have hgh : ∀ g h : LevelGroup V L',
      Units.map ((levelGroupRestrictHom V L' g : ↥L' ≃ₐ[K] ↥L') : ↥L' →* ↥L')
        (Units.map ((levelGroupRestrictHom V L' h : ↥L' ≃ₐ[K] ↥L') : ↥L' →* ↥L') ã)
        = Units.map ((levelGroupRestrictHom V L' (g*h) : ↥L' ≃ₐ[K] ↥L') : ↥L' →* ↥L') ã := by
    intro g h
    refine Units.ext (Subtype.ext ?_)
    show (((levelGroupRestrictHom V L' g : ↥L' ≃ₐ[K] ↥L')
        (((levelGroupRestrictHom V L' h : ↥L' ≃ₐ[K] ↥L') ((ã : (↥L')ˣ) : ↥L')) : ↥L')) : K')
        = (((levelGroupRestrictHom V L' (g*h) : ↥L' ≃ₐ[K] ↥L') ((ã : (↥L')ˣ) : ↥L')) : K')
    rw [← AlgEquiv.mul_apply, ← map_mul (levelGroupRestrictHom V L') g h]
  have huunit : ∀ g : LevelGroup V L', (uunit g) ^ p = 1 := by
    intro g
    have hb : (βm (f g)) ^ p
        = Units.map (levelGroupRestrictHom V L (f g) : ↥L ≃ₐ[K] ↥L) x₀ / x₀ :=
      (hx₀ (f g)).symm
    have hβp : (βt g) ^ p
        = Units.map (IntermediateField.inclusion hle).toMonoidHom
              (Units.map (levelGroupRestrictHom V L (f g) : ↥L ≃ₐ[K] ↥L) x₀)
          / Units.map (IntermediateField.inclusion hle).toMonoidHom x₀ := by
      show (Units.map (IntermediateField.inclusion hle).toMonoidHom (βm (f g))) ^ p = _
      rw [← map_pow, hb, map_div]
    have hc := hcomp g x₀
    have hcalc : (βt g * ã / Units.map (levelGroupRestrictHom V L' g : ↥L' ≃ₐ[K] ↥L') ã) ^ p
        = (Units.map (levelGroupRestrictHom V L' g : ↥L' ≃ₐ[K] ↥L')
              (Units.map (IntermediateField.inclusion hle).toMonoidHom x₀)
            / Units.map (IntermediateField.inclusion hle).toMonoidHom x₀)
          * ã ^ p
          / (Units.map (levelGroupRestrictHom V L' g : ↥L' ≃ₐ[K] ↥L') ã) ^ p := by
      rw [div_pow, mul_pow, hβp, hc]
    show (uunit g) ^ p = 1
    rw [hcalc, ← hU, ← map_pow]
    apply Additive.ofMul.injective
    simp only [ofMul_div, ofMul_mul, ofMul_one]
    abel
  refine ⟨L', hle, ?_⟩
  have hmap : (muLevelMap p V hle).hom (groupCohomology.H2π (muLevelRep p V L) x)
      = (groupCohomology.H2π (muLevelRep p V L'))
          ((groupCohomology.mapCocycles₂ (levelQuotHom (U := V) hle)
            (muLevelMapCoeff.{u, u} p V hle)) x) :=
    groupCohomology.H2π_comp_map_apply (levelQuotHom (U := V) hle) (muLevelMapCoeff.{u, u} p V hle) x
  rw [hmap, groupCohomology.H2π_eq_zero_iff]
  let uM : LevelGroup V L' → rootsOfUnity p ↥L' := fun g =>
    ⟨uunit g, (mem_rootsOfUnity p (uunit g)).mpr (huunit g)⟩
  rw [show groupCohomology.coboundaries₂ (muLevelRep p V L')
      = LinearMap.range (groupCohomology.d₁₂ (muLevelRep p V L')).hom from rfl]
  refine ⟨fun g => Additive.ofMul (uM g), ?_⟩
  funext gh
  obtain ⟨g, h⟩ := gh
  have key : (Additive.toMul (α := rootsOfUnity p ↥L')
        (((groupCohomology.d₁₂ (muLevelRep p V L')) (fun g => Additive.ofMul (uM g)) (g,h)))
        : rootsOfUnity p ↥L')
      = (Additive.toMul (α := rootsOfUnity p ↥L')
        (((groupCohomology.mapCocycles₂ (levelQuotHom (U := V) hle)
            (muLevelMapCoeff.{u, u} p V hle)) x (g,h))) : rootsOfUnity p ↥L') := by
    refine Subtype.ext ?_
    have hd1 : (Additive.toMul (α := rootsOfUnity p ↥L')
          (((groupCohomology.d₁₂ (muLevelRep p V L')) (fun g => Additive.ofMul (uM g))
            (g,h))) : (↥L')ˣ)
        = (Units.map (levelGroupRestrictHom V L' g : ↥L' ≃ₐ[K] ↥L') (uunit h))
            / (uunit (g*h)) * (uunit g) := rfl
    have hd2 : (Additive.toMul (α := rootsOfUnity p ↥L')
          (((groupCohomology.mapCocycles₂ (levelQuotHom (U := V) hle)
              (muLevelMapCoeff.{u, u} p V hle)) x (g,h))) : (↥L')ˣ)
        = ((muLevelIncl p L L' hle
              (Additive.toMul (α := rootsOfUnity p ↥L) (x (f g, f h)))
              : rootsOfUnity p ↥L') : (↥L')ˣ) := by
      rw [coe_mapCocycles₂_apply]
      show (Additive.toMul (α := rootsOfUnity p ↥L')
          ((muLevelMapCoeff.{u, u} p V hle).hom (x (f g, f h))) : (↥L')ˣ) = _
      change (Additive.toMul (α := rootsOfUnity p ↥L')
          ((muLevelMapCoeff.{u, u} p V hle).hom.toLinearMap (x (f g, f h))) : (↥L')ˣ)
        = ((muLevelIncl p L L' hle
              (Additive.toMul (α := rootsOfUnity p ↥L) (x (f g, f h)))
              : rootsOfUnity p ↥L') : (↥L')ˣ)
      rw [muLevelMapCoeff_apply.{u, u, u}]
      rfl
    rw [hd1, hd2]
    have hstep2 : Units.map (levelGroupRestrictHom V L' g : ↥L' ≃ₐ[K] ↥L') (βt h)
        = Units.map (IntermediateField.inclusion hle).toMonoidHom
            (Units.map (levelGroupRestrictHom V L (f g) : ↥L ≃ₐ[K] ↥L) (βm (f h))) := by
      show Units.map ((levelGroupRestrictHom V L' g : ↥L' ≃ₐ[K] ↥L') : ↥L' →* ↥L')
          (Units.map (IntermediateField.inclusion hle).toMonoidHom (βm (f h))) = _
      exact (hcomp g (βm (f h))).symm
    have hstep3 : Units.map (IntermediateField.inclusion hle).toMonoidHom
          (Units.map (levelGroupRestrictHom V L (f g) : ↥L ≃ₐ[K] ↥L) (βm (f h)))
          * βt g / βt (g*h)
        = Units.map (IntermediateField.inclusion hle).toMonoidHom (zm (f g) (f h)) := by
      have hrel' := hrel (f g) (f h)
      rw [show (levelGroupRestrictHom V L (f g) : ↥L ≃ₐ[K] ↥L) • βm (f h)
          = Units.map (levelGroupRestrictHom V L (f g) : ↥L ≃ₐ[K] ↥L) (βm (f h)) from
        AlgEquiv.smul_units_def _ _] at hrel'
      rw [show βt g = Units.map (IntermediateField.inclusion hle).toMonoidHom (βm (f g))
          from rfl]
      rw [show βt (g*h) = Units.map (IntermediateField.inclusion hle).toMonoidHom
            (βm (f (g*h))) from rfl]
      rw [show f (g*h) = f g * f h from map_mul f g h]
      rw [← map_mul, ← map_div]
      congr 1
      rw [← hrel']
      apply Additive.ofMul.injective
      simp only [ofMul_div, ofMul_mul]
      abel
    have hstep4 : Units.map (IntermediateField.inclusion hle).toMonoidHom (zm (f g) (f h))
        = Units.map (IntermediateField.inclusion hle).toMonoidHom
            ((Additive.toMul (α := rootsOfUnity p ↥L) (x (f g, f h)) : rootsOfUnity p ↥L)
              : (↥L)ˣ) := by
      congr 1
    have hA : ∀ y : LevelGroup V L', uunit y
        = βt y * ã / Units.map (levelGroupRestrictHom V L' y : ↥L' ≃ₐ[K] ↥L') ã := fun y => rfl
    have hLHS : Units.map (levelGroupRestrictHom V L' g : ↥L' ≃ₐ[K] ↥L') (uunit h)
          / uunit (g*h) * uunit g
        = Units.map (levelGroupRestrictHom V L' g : ↥L' ≃ₐ[K] ↥L') (βt h)
            * βt g / βt (g*h) := by
      rw [hA h, hA (g*h), hA g, map_div, map_mul, hgh g h]
      apply Additive.ofMul.injective
      simp only [ofMul_div, ofMul_mul]
      abel
    rw [hLHS, hstep2, hstep3, hstep4]
    rw [show ((muLevelIncl p L L' hle
          (Additive.toMul (α := rootsOfUnity p ↥L) (x (f g, f h))) : rootsOfUnity p ↥L')
          : (↥L')ˣ)
        = Units.map (IntermediateField.inclusion hle).toMonoidHom
            ((Additive.toMul (α := rootsOfUnity p ↥L) (x (f g, f h)) : rootsOfUnity p ↥L)
              : (↥L)ˣ) from rfl]

  exact (Additive.toMul (α := rootsOfUnity p ↥L')).injective key


theorem kummerColim_injective_charZero {K K' : Type u} [Field K] [CharZero K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (hp : p.Prime) (V : Subgroup (K' ≃ₐ[K] K')) :
    Function.Injective (NK.HassePrinciple.kummerColim p V) := by
  intro x y hxy
  -- the naturality of the level-wise Kummer maps, in the `μ_p`/units vocabulary
  have hnat : ∀ {L₁ L₂ : FiniteGaloisIntermediateField K K'}
      (h : (L₁ : IntermediateField K K') ≤ (L₂ : IntermediateField K K')) (c : MuLevelH2 p V L₁),
      (unitsLevelMap V h).hom ((kummerLevel p V L₁).hom c)
        = (kummerLevel p V L₂).hom ((muLevelMap p V h).hom c) := by
    intro L₁ L₂ h c
    have hh := congrArg (fun f => f.hom c) (kummerLevel_naturality p V h)
    change (unitsLevelMap V h).hom ((kummerLevel p V L₁).hom c)
      = (kummerLevel p V L₂).hom ((muLevelMap p V h).hom c) at hh
    exact hh
  -- the computation rule for `kummerColim`, in the unfolded `LevelSystem.ofLevel` vocabulary
  have hcol : ∀ (L : FiniteGaloisIntermediateField K K') (a : (muLevelSystem p V).obj L),
      kummerColim p V ((muLevelSystem p V).ofLevel L a)
        = (unitsLevelSystem V).ofLevel L ((kummerLevel p V L).hom a) :=
    fun L a => kummerColim_ofLevel p V L a
  obtain ⟨L, a, ha⟩ := (muLevelSystem p V).ofLevel_surjective x
  obtain ⟨L', b, hb⟩ := (muLevelSystem p V).ofLevel_surjective y
  -- move both representatives to a common upper level `M`
  let M : FiniteGaloisIntermediateField K K' := L ⊔ L'
  have hLM : L ≤ M := le_sup_left
  have hL'M : L' ≤ M := le_sup_right
  have hLMi : (L : IntermediateField K K') ≤ (M : IntermediateField K K') :=
    (FiniteGaloisIntermediateField.le_iff L M).mp hLM
  have hL'Mi : (L' : IntermediateField K K') ≤ (M : IntermediateField K K') :=
    (FiniteGaloisIntermediateField.le_iff L' M).mp hL'M
  let A : MuLevelH2 p V M := (muLevelMap p V hLMi).hom a
  let B : MuLevelH2 p V M := (muLevelMap p V hL'Mi).hom b
  have hAc : (muLevelSystem p V).ofLevel L a = (muLevelSystem p V).ofLevel M A :=
    ((muLevelSystem p V).ofLevel_map hLM a).symm
  have hBc : (muLevelSystem p V).ofLevel L' b = (muLevelSystem p V).ofLevel M B :=
    ((muLevelSystem p V).ofLevel_map hL'M b).symm
  have key1 : (unitsLevelSystem V).ofLevel M ((kummerLevel p V M).hom A)
      = (unitsLevelSystem V).ofLevel L ((kummerLevel p V L).hom a) := by
    rw [← hnat hLMi a]
    exact (unitsLevelSystem V).ofLevel_map hLM ((kummerLevel p V L).hom a)
  have key2 : (unitsLevelSystem V).ofLevel M ((kummerLevel p V M).hom B)
      = (unitsLevelSystem V).ofLevel L' ((kummerLevel p V L').hom b) := by
    rw [← hnat hL'Mi b]
    exact (unitsLevelSystem V).ofLevel_map hL'M ((kummerLevel p V L').hom b)
  have hxy' : (unitsLevelSystem V).ofLevel M ((kummerLevel p V M).hom A)
      = (unitsLevelSystem V).ofLevel M ((kummerLevel p V M).hom B) := by
    have h := hxy
    rw [← ha, ← hb, hcol, hcol] at h
    rw [← key1, ← key2] at h
    exact h
  -- the same class at a larger level `N ≥ M`
  obtain ⟨N, h₁, h₂, hN⟩ :=
    (NK.BrauerTwist.LevelSystem.ofLevel_eq_iff (unitsLevelSystem V) _ _).mp hxy'
  have h₁i : (M : IntermediateField K K') ≤ (N : IntermediateField K K') :=
    (FiniteGaloisIntermediateField.le_iff M N).mp h₁
  have hN' : (unitsLevelMap V h₁i).hom ((kummerLevel p V M).hom A)
      = (unitsLevelMap V h₁i).hom ((kummerLevel p V M).hom B) := by
    rw [show h₂ = h₁ from Subsingleton.elim h₂ h₁] at hN
    exact hN
  have hN'' : (kummerLevel p V N).hom ((muLevelMap p V h₁i).hom A)
      = (kummerLevel p V N).hom ((muLevelMap p V h₁i).hom B) := by
    rw [← hnat h₁i A, ← hnat h₁i B]
    exact hN'
  -- the `μ_p` class that dies at a larger level
  have hw : (kummerLevel p V N).hom
      ((muLevelMap p V h₁i).hom A - (muLevelMap p V h₁i).hom B) = 0 := by
    rw [map_sub, hN'', sub_self]
  obtain ⟨N', hNN', hw'⟩ := kummerLevel_kernel_dies_charZero p hp V N
    ((muLevelMap p V h₁i).hom A - (muLevelMap p V h₁i).hom B) hw
  have heq : (muLevelMap p V hNN').hom ((muLevelMap p V h₁i).hom A)
      = (muLevelMap p V hNN').hom ((muLevelMap p V h₁i).hom B) := by
    rw [map_sub, sub_eq_zero] at hw'
    exact hw'
  have hcomp := congrArg (fun f => f.hom A) (muLevelMap_comp p V h₁i hNN')
  change (muLevelMap p V hNN').hom ((muLevelMap p V h₁i).hom A)
      = (muLevelMap p V (h₁i.trans hNN')).hom A at hcomp
  have hcomp₂ := congrArg (fun f => f.hom B) (muLevelMap_comp p V h₁i hNN')
  change (muLevelMap p V hNN').hom ((muLevelMap p V h₁i).hom B)
      = (muLevelMap p V (h₁i.trans hNN')).hom B at hcomp₂
  have hfinal : (muLevelMap p V (h₁i.trans hNN')).hom A
      = (muLevelMap p V (h₁i.trans hNN')).hom B :=
    hcomp.symm.trans (heq.trans hcomp₂)
  -- assemble
  have hMN'' : M ≤ N' := h₁.trans ((FiniteGaloisIntermediateField.le_iff N N').mpr hNN')
  have hA' : (muLevelSystem p V).ofLevel L a
      = (muLevelSystem p V).ofLevel N' ((muLevelMap p V (h₁i.trans hNN')).hom A) :=
    hAc.trans ((muLevelSystem p V).ofLevel_map hMN'' A).symm
  have hB' : (muLevelSystem p V).ofLevel L' b
      = (muLevelSystem p V).ofLevel N' ((muLevelMap p V (h₁i.trans hNN')).hom B) :=
    hBc.trans ((muLevelSystem p V).ofLevel_map hMN'' B).symm
  rw [← ha, ← hb, hA', hB']
  exact congrArg (fun z => (muLevelSystem p V).ofLevel N' z) hfinal



/-! ## The requested theorem -/

theorem kummerColim_injective_field {K K' : Type} [Field K] [CharZero K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (hp : p.Prime) (V : Subgroup Gal(K'/K)) :
    Function.Injective (NK.HassePrinciple.kummerColim (K := K) (K' := K') p V) :=
  kummerColim_injective_charZero p hp V

end NK.NUV2.ABHN
