import Mathlib
import Submission.Work.AbsoluteKummer.All
import Submission.Work.SSGRoute.cocycles_iso_Z2
import Submission.Work.SSGRoute.groupCohomology_two_iso_cocycles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level structure of `H²(G_F, k̄ˣ)` — definitions

For a field `F` with algebraic closure `k̄ = AlgebraicClosure F`, Galois over `F`
(`IsGalois F k̄`), and a finite Galois level `L : FiniteGaloisIntermediateField F k̄`, this file
sets up the vocabulary for the level structure of the continuous cohomology `H²(G_F, k̄ˣ)`:

* `resL L : G_F →* Gal(L/F)` — the restriction;
* `inclL L : Lˣ →+ k̄ˣ` — the inclusion of the units of the level, equivariant for `resL`;
* `LevelH2 L` — Mathlib's `H²(Gal(L/F), Lˣ)` as the quotient of the `2`-cocycles by the
  `2`-coboundaries;
* `inflCo L` — the inflation of a level `2`-cocycle to a locally constant `2`-cocycle of `G_F`;
* `psiTilde L : LevelH2 L →+ H²(G_F, k̄ˣ)` — the induced map on cohomology.
-/

noncomputable section

open scoped Classical
open Work.AbsoluteKummer

namespace Work.SSGRoute.PTCore

/-- The absolute Galois group `G_F`. -/
abbrev AbsGal (F : Type) [Field F] : Type := AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F

/-- The units of `k̄`, as an additive group. -/
abbrev UnitsK (F : Type) [Field F] : Type := Additive ((AlgebraicClosure F)ˣ)

variable {F : Type} [Field F] [IsGalois F (AlgebraicClosure F)]

/-- The Galois group `Gal(L/F)` of a finite Galois level. -/
abbrev LevelGal (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) : Type :=
  (↥L : Type) ≃ₐ[F] ↥L

/-- The fixing subgroup `Gal(k̄/L)`. -/
abbrev lvlFix (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) : Subgroup (AbsGal F) :=
  (L : IntermediateField F (AlgebraicClosure F)).fixingSubgroup

/-- The representation `Lˣ` of `Gal(L/F)`. -/
abbrev LevelRep (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) : Rep ℤ (LevelGal L) :=
  Rep.ofAlgebraAutOnUnits F ↥L

/-- The units of a level, as an additive group. -/
abbrev UnitsL (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) : Type := ↥(LevelRep L)

/-! ## The restriction and the coefficient inclusion -/

/-- The restriction `G_F →* Gal(L/F)`. -/
noncomputable def resL (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
    AbsGal F →* LevelGal L :=
  AlgEquiv.restrictNormalHom ↥(L : IntermediateField F (AlgebraicClosure F))

theorem resL_apply (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) (σ : AbsGal F)
    (x : ↥L) : ((resL L σ) x : AlgebraicClosure F) = σ x :=
  AlgEquiv.restrictNormalHom_apply (L : IntermediateField F (AlgebraicClosure F)) σ x

theorem resL_surjective (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
    Function.Surjective (resL L) := by
  have h := AlgEquiv.restrictNormalHom_surjective (F := F) (E := AlgebraicClosure F)
    (K₁ := ↥(L : IntermediateField F (AlgebraicClosure F)))
  simpa [resL] using h

theorem mem_ker_resL_iff (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (σ : AbsGal F) : resL L σ = 1 ↔ σ ∈ lvlFix L := by
  have hker : (resL L).ker = lvlFix L :=
    IntermediateField.restrictNormalHom_ker (L : IntermediateField F (AlgebraicClosure F))
  have hmem : resL L σ = 1 ↔ σ ∈ (resL L).ker := MonoidHom.mem_ker
  rw [hmem, hker]

/-- Two Galois automorphisms congruent modulo `Gal(k̄/L)` have the same restriction to `L`. -/
theorem resL_mul_mem_lvlFix (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    {p q : AbsGal F} (h : p⁻¹ * q ∈ lvlFix L) : resL L q = resL L p := by
  have h1 : resL L (p⁻¹ * q) = 1 := (mem_ker_resL_iff L _).mpr h
  rw [map_mul, map_inv] at h1
  have h3 : (resL L p)⁻¹ * resL L q = 1 := h1
  have h4 : resL L q = resL L p := by
    have := congrArg (fun z => resL L p * z) h3
    rwa [mul_inv_cancel_left, mul_one] at this
  exact h4

theorem isLocallyConstant_resL (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
    Work.AbsoluteKummer.IsLocallyConstant (resL L) := by
  intro g
  refine ⟨{y : AbsGal F | g⁻¹ * y ∈ lvlFix L}, ?_, ?_, ?_⟩
  · exact (IntermediateField.fixingSubgroup_isOpen
      (L : IntermediateField F (AlgebraicClosure F))).preimage (continuous_const.mul continuous_id)
  · show g⁻¹ * g ∈ lvlFix L
    rw [inv_mul_cancel]
    exact Subgroup.one_mem _
  · intro y hy
    exact resL_mul_mem_lvlFix L hy

/-- Pull-back along `resL` of an arbitrary function on `Gal(L/F) × Gal(L/F)` is locally constant. -/
theorem isLocallyConstant_comp_pairResL (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    {N : Type} (Φ : LevelGal L × LevelGal L → N) :
    Work.AbsoluteKummer.IsLocallyConstant
      (fun p : AbsGal F × AbsGal F => Φ (resL L p.1, resL L p.2)) := by
  intro p
  refine ⟨{q : AbsGal F × AbsGal F | p.1⁻¹ * q.1 ∈ lvlFix L ∧ p.2⁻¹ * q.2 ∈ lvlFix L},
    ?_, ?_, ?_⟩
  · have hF : IsOpen ((lvlFix L : Set (AbsGal F))) :=
      IntermediateField.fixingSubgroup_isOpen (L : IntermediateField F (AlgebraicClosure F))
    exact (hF.preimage (continuous_const.mul continuous_fst)).inter
      (hF.preimage (continuous_const.mul continuous_snd))
  · exact ⟨by rw [inv_mul_cancel]; exact Subgroup.one_mem _,
      by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
  · rintro ⟨q₁, q₂⟩ ⟨h₁, h₂⟩
    show Φ (resL L q₁, resL L q₂) = Φ (resL L p.1, resL L p.2)
    rw [resL_mul_mem_lvlFix L h₁, resL_mul_mem_lvlFix L h₂]

/-- The inclusion `Lˣ →+ k̄ˣ` of the units of a level. -/
noncomputable def inclL (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
    UnitsL L →+ UnitsK F where
  toFun x := Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom x
  map_zero' := by
    show Additive.ofMul (Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom
      (1 : (↥L : Type)ˣ)) = Additive.ofMul (1 : (AlgebraicClosure F)ˣ)
    rw [map_one]
  map_add' x y := by
    show Additive.ofMul (Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom
        ((Additive.toMul x : (↥L : Type)ˣ) * (Additive.toMul y : (↥L : Type)ˣ)))
      = Additive.ofMul (Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom
            (Additive.toMul x : (↥L : Type)ˣ)
          * Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom
            (Additive.toMul y : (↥L : Type)ˣ))
    rw [map_mul]

@[simp] theorem inclL_ofMul (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (u : (↥L : Type)ˣ) :
    inclL L (Additive.ofMul u) =
      Additive.ofMul (Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom u) := rfl

theorem inclL_injective (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
    Function.Injective (inclL L) := by
  intro a b hab
  have h : Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom (Additive.toMul a)
      = Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom (Additive.toMul b) :=
    congrArg Additive.toMul hab
  exact Additive.toMul.injective
    (Units.map_injective (algebraMap ↥L (AlgebraicClosure F)).injective h)

/-- The defining property of `inclL`. -/
theorem inclL_eq_iff (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (x : UnitsL L) (v : UnitsK F) :
    inclL L x = v ↔
      Additive.toMul v = Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom
        (Additive.toMul x) := by
  constructor
  · intro h
    exact (congrArg Additive.toMul h).symm
  · intro h
    show Additive.ofMul
      (Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom (Additive.toMul x)) = v
    rw [← h]
    exact ofMul_toMul v

/-- `algEquivUnitsMap` on the units of a level is the action of the restricted automorphism. -/
theorem algEquivUnitsMap_inclL (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (g : AbsGal F) (u : (↥L : Type)ˣ) :
    Work.AbsoluteKummer.algEquivUnitsMap F g
        (Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom u)
      = Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom (Units.map (resL L g) u) := by
  apply Units.ext
  rw [Work.AbsoluteKummer.algEquivUnitsMap]
  change g ((u : ↥L) : AlgebraicClosure F) = (((resL L g) (u : ↥L)) : AlgebraicClosure F)
  rw [resL_apply]

/-- Equivariance of the coefficient inclusion for the action of `G_F` (through `resL`). -/
theorem inclL_rho (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) (g : AbsGal F)
    (x : UnitsL L) : inclL L ((LevelRep L).ρ (resL L g) x) = g • inclL L x := by
  suffices h : ∀ u : (↥L : Type)ˣ,
      inclL L ((LevelRep L).ρ (resL L g) (Additive.ofMul u)) =
        g • inclL L (Additive.ofMul u) by
    rw [show x = Additive.ofMul (Additive.toMul x) from (ofMul_toMul x).symm]
    exact h x.toMul
  intro u
  show Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom (Units.map (resL L g) u)
    = Work.AbsoluteKummer.algEquivUnitsMap F g
        (Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom u)
  exact (algEquivUnitsMap_inclL L g u).symm

/-- Every unit of `k̄` fixed by `Gal(k̄/L)` is a unit of `L`. -/
theorem exists_eq_inclL_of_fixed (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (v : UnitsK F) (hv : ∀ σ ∈ lvlFix L, σ • v = v) :
    ∃ x : UnitsL L, inclL L x = v := by
  have hfix : ((Additive.toMul v : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) ∈
      (L : IntermediateField F (AlgebraicClosure F)) := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup
      (L : IntermediateField F (AlgebraicClosure F)), IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h2 : Work.AbsoluteKummer.algEquivUnitsMap F σ (Additive.toMul v) = Additive.toMul v := by
      have h3 := congrArg Additive.toMul (hv σ hσ)
      rwa [show Additive.toMul (σ • v) =
        Work.AbsoluteKummer.algEquivUnitsMap F σ (Additive.toMul v)
          from Work.AbsoluteKummer.addUnits_smul_toMul F σ v] at h3
    have h4 := congrArg (fun z : (AlgebraicClosure F)ˣ => (z : AlgebraicClosure F)) h2
    rwa [Work.AbsoluteKummer.algEquivUnitsMap_coe] at h4
  refine ⟨(Units.mk0 ⟨(Additive.toMul v : (AlgebraicClosure F)ˣ), hfix⟩ ?_ : UnitsL L), ?_⟩
  · intro hz
    exact Units.ne_zero (Additive.toMul v) (Subtype.ext_iff.mp hz)
  · show Additive.ofMul (Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom
        (Units.mk0 ⟨(Additive.toMul v : (AlgebraicClosure F)ˣ), hfix⟩ _))
      = Additive.ofMul (Additive.toMul v)
    rw [show Units.map (algebraMap ↥L (AlgebraicClosure F)).toMonoidHom
        (Units.mk0 ⟨(Additive.toMul v : (AlgebraicClosure F)ˣ), hfix⟩ _)
        = Additive.toMul v from by
      apply Units.ext
      show algebraMap ↥L (AlgebraicClosure F)
          ⟨(Additive.toMul v : (AlgebraicClosure F)ˣ), hfix⟩
        = ((Additive.toMul v : (AlgebraicClosure F)ˣ) : AlgebraicClosure F)
      rfl]

/-! ## The level `2`-cocycles and the inflation map -/

abbrev LevelCocycles (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :=
  groupCohomology.cocycles₂ (LevelRep L)

abbrev LevelCob (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :=
  groupCohomology.coboundaries₂ (LevelRep L)

/-- `H²(Gal(L/F), Lˣ)`, as the quotient of the `2`-cocycles by the `2`-coboundaries. -/
abbrev LevelH2 (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) : Type :=
  ↥(LevelCocycles L) ⧸ ((LevelCob L).comap (LevelCocycles L).subtype).toAddSubgroup

/-- The `2`-cocycle condition in the shape used by `Work.GroupCohomology`. -/
theorem mem_cocycles₂_iff_add (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (c : LevelGal L × LevelGal L → UnitsL L) :
    c ∈ LevelCocycles L ↔ ∀ g h k : LevelGal L,
      c (g * h, k) + c (g, h) = (LevelRep L).ρ g (c (h, k)) + c (g, h * k) :=
  groupCohomology.mem_cocycles₂_iff (A := LevelRep L) c

/-- The inflation of a level `2`-cocycle to a locally constant `2`-cocycle of `G_F`. -/
noncomputable def inflCo (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
    ↥(LevelCocycles L) →+ Work.AbsoluteKummer.Z2 (AbsGal F) (UnitsK F) where
  toFun c := ⟨fun p => inclL L (c (resL L p.1, resL L p.2)), by
    rw [Work.AbsoluteKummer.mem_Z2_iff]
    refine ⟨?_, ?_⟩
    · intro g h k
      have h1 := (mem_cocycles₂_iff_add L (c : LevelGal L × LevelGal L → UnitsL L)).mp c.2
        (resL L g) (resL L h) (resL L k)
      show inclL L (c (resL L (g * h), resL L k)) + inclL L (c (resL L g, resL L h))
        = g • inclL L (c (resL L h, resL L k)) + inclL L (c (resL L g, resL L (h * k)))
      rw [map_mul, map_mul, ← map_add, h1, map_add, inclL_rho]
    · exact isLocallyConstant_comp_pairResL L (fun q => inclL L (c q))⟩
  map_zero' := by
    apply Subtype.ext
    funext p
    show inclL L (0 : UnitsL L) = Additive.ofMul (1 : (AlgebraicClosure F)ˣ)
    rw [map_zero, ofMul_one]
  map_add' c d := by
    apply Subtype.ext
    funext p
    show inclL L (c (resL L p.1, resL L p.2) + d (resL L p.1, resL L p.2))
      = inclL L (c (resL L p.1, resL L p.2)) + inclL L (d (resL L p.1, resL L p.2))
    rw [map_add]

/-- The inflation of a level `2`-coboundary is a locally constant `2`-coboundary. -/
theorem inflCo_mem_B2 (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (c : ↥(LevelCocycles L)) (hc : (c : LevelGal L × LevelGal L → UnitsL L) ∈ LevelCob L) :
    (fun p : AbsGal F × AbsGal F => inclL L (c (resL L p.1, resL L p.2)))
      ∈ Work.AbsoluteKummer.B2 (AbsGal F) (UnitsK F) := by
  rw [Work.AbsoluteKummer.mem_B2_iff]
  rw [LevelCob, groupCohomology.coboundaries₂, LinearMap.mem_range] at hc
  obtain ⟨f, hf⟩ := hc
  refine ⟨fun g => inclL L (f (resL L g)), (isLocallyConstant_resL L).map (fun x => inclL L (f x)),
    ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  have hf' := congrFun hf (resL L g, resL L h)
  rw [groupCohomology.d₁₂_hom_apply] at hf'
  show (Work.GroupCohomology.d1 (AbsGal F) (UnitsK F)) (fun g => inclL L (f (resL L g))) (g, h)
    = inclL L (c (resL L g, resL L h))
  rw [Work.GroupCohomology.d1_apply, map_mul, ← hf']
  simp only [map_sub, map_add, inclL_rho]

/-- **The level map**: inflation `H²(Gal(L/F), Lˣ) → H²(G_F, k̄ˣ)`. -/
noncomputable def psiTilde (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
    LevelH2 L →+ Work.AbsoluteKummer.H2 (AbsGal F) (UnitsK F) :=
  QuotientAddGroup.lift ((LevelCob L).comap (LevelCocycles L).subtype).toAddSubgroup
    ((Work.AbsoluteKummer.H2π (AbsGal F) (UnitsK F)).comp (inflCo L)) (by
      intro x hx
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, Work.AbsoluteKummer.H2π_eq_zero_iff]
      exact inflCo_mem_B2 L x (Submodule.mem_comap.mp hx))

theorem psiTilde_mk (L : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (c : ↥(LevelCocycles L)) :
    psiTilde L (QuotientAddGroup.mk' _ c) =
      Work.AbsoluteKummer.H2π (AbsGal F) (UnitsK F) (inflCo L c) :=
  QuotientAddGroup.lift_mk' _ _ c

end Work.SSGRoute.PTCore
