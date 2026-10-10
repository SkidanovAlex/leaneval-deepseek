import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.nsmul_phiAt_extToClasses_eq_zero
import Submission.Work.SSGRoute.PT.vfShared

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute.PT

/-! ## Auxiliary lemmas for `archPair_level_independent_loc` -/

/-- **The restriction maps of nested decomposition groups compose.** -/
theorem archPair_decompKRestrict_comp {K L L' : Type} [Field K] [Field L] [Field L']
    {k : Type} [Field k] [NumberField k] [NumberField K] [NumberField L] [NumberField L']
    [Algebra k K] [Algebra k L] [Algebra k L'] [Algebra K L] [Algebra K L']
    [IsScalarTower k K L] [IsScalarTower k K L'] [Algebra L L'] [IsScalarTower k L L']
    [IsScalarTower K L L'] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L] [FiniteDimensional k L'] [IsGalois k L']
    (w : NK.GlobalCFT.Place K) (u : NK.GlobalCFT.Place L) (u' : NK.GlobalCFT.Place L')
    (hu : NK.GlobalCFT.Place.LiesOver u w) (hu'u : NK.GlobalCFT.Place.LiesOver u' u)
    (hu'w : NK.GlobalCFT.Place.LiesOver u' w) :
    Work.SSGRoute.decompKRestrict k K L' w u' hu'w
      = (Work.SSGRoute.decompKRestrict k K L w u hu).comp
          (Work.SSGRoute.decompKRestrict k L L' u u' hu'u) := by
  apply MonoidHom.ext
  intro σ
  apply Subtype.ext
  change SSGRoute.PTExt.galRes k K L' (σ : L' ≃ₐ[k] L')
      = SSGRoute.PTExt.galRes k K L (SSGRoute.PTExt.galRes k L L' (σ : L' ≃ₐ[k] L'))
  exact (SSGRoute.PTExt.galRes_trans (σ : L' ≃ₐ[k] L')).symm

/-- **`eCoh`/`H1π` naturality.**  For a group homomorphism `r : H →* G`, a `G`-module `A`, an
`H`-module `B`, a coefficient morphism `φ : Rep.res r A ⟶ B` and cocycles `z ∈ Z¹(G, A)`,
`z' ∈ Z¹(H, B)` with `z' g = φ (z (r g))`, the classes of `z'` and of `z` correspond under the
inflation `extHMap r φ` of the `E0b` isomorphism `eCoh`. -/
theorem archPair_eCoh_H1pi_rho {G H : Type} [Group G] [Group H] (r : H →* G)
    (A : Rep.{0} Coeff G) (B : Rep.{0} Coeff H) (φ : Rep.res r A ⟶ B)
    (z : groupCohomology.cocycles₁ A) (z' : groupCohomology.cocycles₁ B)
    (hz : ∀ g : H, (z' : H → B.V) g = (Rep.Hom.hom φ) (z (r g))) :
    SSGRoute.PTExt.eCoh 1 H B ((groupCohomology.H1π B).hom z')
      = SSGRoute.PTExt.extHMap r φ
          (SSGRoute.PTExt.eCoh 1 G A ((groupCohomology.H1π A).hom z)) := by
  have hmapz : (groupCohomology.mapCocycles₁ r φ).hom z = z' := by
    apply groupCohomology.cocycles₁_ext
    intro g
    rw [groupCohomology.coe_mapCocycles₁]
    show (Rep.Hom.hom φ) (z (r g)) = (z' : H → B.V) g
    exact (hz g).symm
  rw [← Work.SSGRoute.eCoh_map 1 G H r A B φ ((groupCohomology.H1π A).hom z),
    groupCohomology.H1π_comp_map_apply r φ z, hmapz]

/-- **`eCoh`/`H1π` naturality, identity-coefficient form**: the inflation of the class of a cocycle
is the class of the restricted cocycle. -/
theorem archPair_eCoh_H1pi_rho_id {G H : Type} [Group G] [Group H] (r : H →* G)
    (A : Rep.{0} Coeff G) (z : groupCohomology.cocycles₁ A)
    (z' : groupCohomology.cocycles₁ (Rep.res r A))
    (hz : ∀ g : H, (z' : H → (Rep.res r A).V) g = (z : G → A.V) (r g)) :
    SSGRoute.PTExt.eCoh 1 H (Rep.res r A) ((groupCohomology.H1π _).hom z')
      = SSGRoute.PTExt.extHMap r (𝟙 (Rep.res r A))
          (SSGRoute.PTExt.eCoh 1 G A ((groupCohomology.H1π A).hom z)) := by
  refine archPair_eCoh_H1pi_rho r A (Rep.res r A) (𝟙 (Rep.res r A)) z z' ?_
  intro g
  rw [Rep.id_apply]
  exact hz g

/-- **A generic `p`-torsion lemma**: `Extⁿ` with `p`-torsion first variable is `p`-torsion. -/
theorem archPair_ext_nsmul_eq_zero_of_ptorsion_left {C : Type*} [Category* C] [Abelian C]
    [HasExt C] {X Y : C} {n : ℕ} (p : ℕ) (hX : p • (𝟙 X) = 0) (x : Abelian.Ext X Y n) :
    p • x = 0 := by
  have key : ∀ k : ℕ, (Abelian.Ext.mk₀ (k • (𝟙 X))).comp x (zero_add n) = k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [succ_nsmul', Abelian.Ext.mk₀_add, Abelian.Ext.add_comp, ih,
          Abelian.Ext.mk₀_id_comp, succ_nsmul']
  rw [← key p, hX, Abelian.Ext.mk₀_zero]
  simp

/-- **The local identity `hz'`, in the generalised form.**
`f''` is an abstract hom `D_{u'} → D_w` which is *propositionally* the composite
`(decompKRestrict K L w u) ∘ (decompKRestrict L L' u u')`, `ι''` its own units map with the spec
`hι''`; the level-`L` side is the concrete one.  After `subst hcomp` all the `Rep.res` spellings
become definitionally equal, so the units identity is `localAlgebraMapUnits_comp_rep` and the class
identity is the `eCoh`/`H1π` naturality of a restricted cocycle `archPair_eCoh_H1pi_rho_id`; the
reassembly is `Y3Key.levelPair_restrict'`. -/
theorem archPair_hz'_aux (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (↥K ≃ₐ[k] ↥K) T]
    [SMulCommClass (↥K ≃ₐ[k] ↥K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (↥K ≃ₐ[k] ↥K) M]
    [SMulCommClass (↥K ≃ₐ[k] ↥K) (ZMod p) M] [Finite M]
    (L L' : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k L] [IsGalois k L]
    [NumberField ↥L'] [FiniteDimensional k L'] [IsGalois k L']
    (hKL : K ≤ L) (hKL' : K ≤ L') (hLL : L ≤ L')
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    [Algebra ↥K ↥L'] [IsScalarTower k ↥K ↥L'] [IsScalarTower ↥K ↥L' Ω]
    [Algebra ↥L ↥L'] [IsScalarTower k ↥L ↥L'] [IsScalarTower ↥L ↥L' Ω] [IsScalarTower ↥K ↥L ↥L']
    (w : NK.GlobalCFT.Place ↥K) (u : NK.GlobalCFT.Place ↥L) (u' : NK.GlobalCFT.Place ↥L')
    (hu : NK.GlobalCFT.Place.LiesOver u w) (hu'u : NK.GlobalCFT.Place.LiesOver u' u)
    (hu'w : NK.GlobalCFT.Place.LiesOver u' w)
    (x : CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) w) 1)
    (f'' : ↥(SSGRoute.PTExt.decompK (k := k) u') →* ↥(SSGRoute.PTExt.decompK (k := k) w))
    (ι'' : Rep.res f'' (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) w) ⟶
      NK.HassePrinciple.localUnitsRep k ↥L' u')
    (hι'' : ∀ y : (NK.GlobalCFT.Place.localField ↥K w)ˣ,
      ι''.hom (Additive.ofMul y)
        = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits u' w hu'w y))
    (hcomp : f'' = (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu).comp
      (Work.SSGRoute.decompKRestrict k ↥L ↥L' u u' hu'u))
    (z : groupCohomology.cocycles₁ (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))))
    (z' : groupCohomology.cocycles₁ (Rep.res f''
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))))
    (hzz' : ∀ g : ↥(SSGRoute.PTExt.decompK (k := k) u'),
      (z' : ↥(SSGRoute.PTExt.decompK (k := k) u') → Work.SSGRoute.PT.VFcoef p M T) g =
        (z : ↥(SSGRoute.PTExt.decompK (k := k) u) → Work.SSGRoute.PT.VFcoef p M T)
          (Work.SSGRoute.decompKRestrict k ↥L ↥L' u u' hu'u g)) :
    SSGRoute.PTExt.levelPair f'' ι'' x
        (SSGRoute.PTExt.eCoh 1 (↥(SSGRoute.PTExt.decompK (k := k) u'))
          (Rep.res f''
            (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
              (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))))
          ((groupCohomology.H1π _).hom z'))
      = SSGRoute.PTExt.extHMap (Work.SSGRoute.decompKRestrict k ↥L ↥L' u u' hu'u)
          (Work.SSGRoute.localUnitsMap k ↥L ↥L' u u' hu'u)
          (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
            (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) x
            (SSGRoute.PTExt.eCoh 1 (↥(SSGRoute.PTExt.decompK (k := k) u))
              (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
                (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
                  (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))))
              ((groupCohomology.H1π _).hom z))) := by
  classical
  subst hcomp
  let Mmod : Rep.{0} Coeff (↥(SSGRoute.PTExt.decompK (k := k) w)) :=
    Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))
  let f : ↥(SSGRoute.PTExt.decompK (k := k) u) →* ↥(SSGRoute.PTExt.decompK (k := k) w) :=
    Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu
  let ρ : ↥(SSGRoute.PTExt.decompK (k := k) u') →* ↥(SSGRoute.PTExt.decompK (k := k) u) :=
    Work.SSGRoute.decompKRestrict k ↥L ↥L' u u' hu'u
  -- the units identity
  have hι : Rep.resMap ρ (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) ≫
      (Work.SSGRoute.localUnitsMap k ↥L ↥L' u u' hu'u) = ι'' :=
    Work.SSGRoute.localAlgebraMapUnits_comp_rep k ↥K ↥L ↥L' w u u' hu hu'u hu'w
      (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Work.SSGRoute.decompKRestrict k ↥L ↥L' u u' hu'u)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu)
      (Work.SSGRoute.localUnitsMap_spec k ↥K ↥L w u hu)
      (Work.SSGRoute.localUnitsMap k ↥L ↥L' u u' hu'u)
      (Work.SSGRoute.localUnitsMap_spec k ↥L ↥L' u u' hu'u) ι'' hι''
  let y : SSGRoute.PTExt.extH (Rep.res f Mmod) 1 :=
    SSGRoute.PTExt.eCoh 1 (↥(SSGRoute.PTExt.decompK (k := k) u))
      (Rep.res f Mmod) ((groupCohomology.H1π _).hom z)
  let y'' : SSGRoute.PTExt.extH (Rep.res (f.comp ρ) Mmod) 1 :=
    SSGRoute.PTExt.eCoh 1 (↥(SSGRoute.PTExt.decompK (k := k) u'))
      (Rep.res (f.comp ρ) Mmod) ((groupCohomology.H1π _).hom z')
  -- the class identity
  have hclass : y'' = SSGRoute.PTExt.extHMap ρ (𝟙 (Rep.res ρ (Rep.res f Mmod))) y :=
    archPair_eCoh_H1pi_rho_id ρ (Rep.res f Mmod) z z' (fun g => hzz' g)
  -- the reassembly
  refine (?_ : SSGRoute.PTExt.levelPair (f.comp ρ) ι'' x y''
      = SSGRoute.PTExt.levelPair (f.comp ρ)
          (Rep.resMap ρ (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) ≫
            (Work.SSGRoute.localUnitsMap k ↥L ↥L' u u' hu'u)) x
          (SSGRoute.PTExt.extHMap ρ (𝟙 (Rep.res ρ (Rep.res f Mmod))) y)).trans
    (Y3Key.levelPair_restrict' (f := f) (g := ρ)
      (ι := Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu)
      (ιg := Work.SSGRoute.localUnitsMap k ↥L ↥L' u u' hu'u)
      (ι' := Rep.resMap ρ (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) ≫
        Work.SSGRoute.localUnitsMap k ↥L ↥L' u u' hu'u)
      (x := x) (h := y) rfl).symm
  rw [← hι, ← hclass]

/-- **Level independence of the local pairing for LOCAL classes** (the core of
`archPair_level_independent`; any place `w`).  For places `u' | u | w` at levels `K ≤ L ≤ L'`, let
`z` be a `1`-cocycle on `D_u` and `z'` one on `D_{u'}` with `z' = z ∘ (D_{u'} → D_u)` pointwise.  Then
`χ_L (ι_u (levelPair_{u/w} x [z])) = χ_{L'} (ι_{u'} (levelPair_{u'/w} x [z']))`.

The G1⁺ hub needs this form because its involution pairing is defined from a LOCAL cocycle on
`⟨c⟩` (the class is not the restriction of a global one).  `archPair_level_independent` (the
`levelClassOf` form) follows from it by `extHRestrict_levelClassOf_eq_of_eqOn` on both sides.

Route.  The coherence `hχcompat` (in the `inflLevel` spelling) is applied directly, and the
remaining level transport `inflLevel (ι_u z) = ι_{u'} z'` is the chain
`iotaLift_idleRepMap`/`extToClasses_idleRepMap` (the body of `PT.chi_iota_eq_of_localInflation`).
The local identity `hz'` is `archPair_hz'_aux`.  The ambient `Algebra ↥L ↥L'`-instance is forced to
be the canonical one by the scalar tower `IsScalarTower ↥L ↥L' Ω`, so it is replaced by it
(`cases hinst`); this makes all the `Rep.res`/`inflC` spellings syntactically compatible. -/
theorem archPair_level_independent_loc (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (↥K ≃ₐ[k] ↥K) T]
    [SMulCommClass (↥K ≃ₐ[k] ↥K) (ZMod p) T]
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L'] [FiniteDimensional k L']
      [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
      (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (↥K ≃ₐ[k] ↥K) M]
    [SMulCommClass (↥K ≃ₐ[k] ↥K) (ZMod p) M] [Finite M]
    (L L' : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k L] [IsGalois k L]
    [NumberField ↥L'] [FiniteDimensional k L'] [IsGalois k L']
    (hKL : K ≤ L) (hKL' : K ≤ L') (hLL : L ≤ L')
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    [Algebra ↥K ↥L'] [IsScalarTower k ↥K ↥L'] [IsScalarTower ↥K ↥L' Ω]
    [Algebra ↥L ↥L'] [IsScalarTower k ↥L ↥L'] [IsScalarTower ↥L ↥L' Ω] [IsScalarTower ↥K ↥L ↥L']
    (w : NK.GlobalCFT.Place ↥K) (u : NK.GlobalCFT.Place ↥L) (u' : NK.GlobalCFT.Place ↥L')
    (hu : NK.GlobalCFT.Place.LiesOver u w) (hu'u : NK.GlobalCFT.Place.LiesOver u' u)
    (hu'w : NK.GlobalCFT.Place.LiesOver u' w)
    (x : CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) w) 1)
    (z : groupCohomology.cocycles₁ (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))))
    (z' : groupCohomology.cocycles₁ (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L' w u' hu'w)
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))))
    (hzz' : ∀ g : ↥(SSGRoute.PTExt.decompK (k := k) u'),
      (z' : ↥(SSGRoute.PTExt.decompK (k := k) u') → Work.SSGRoute.PT.VFcoef p M T) g =
        (z : ↥(SSGRoute.PTExt.decompK (k := k) u) → Work.SSGRoute.PT.VFcoef p M T)
          (Work.SSGRoute.decompKRestrict k ↥L ↥L' u u' hu'u g)) :
    χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L) u
        (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
          (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) x
          (SSGRoute.PTExt.eCoh 1 _ _ ((groupCohomology.H1π _).hom z)))) =
      χ L' hKL' (Work.SSGRoute.PT.iota (k := k) (L := ↥L') u'
        (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L' w u' hu'w)
          (Work.SSGRoute.localUnitsMap k ↥K ↥L' w u' hu'w) x
          (SSGRoute.PTExt.eCoh 1 _ _ ((groupCohomology.H1π _).hom z')))) := by
  classical
  -- the ambient `Algebra ↥L ↥L'`-instance is forced to be the canonical one
  have hinst : (IntermediateField.inclusion hLL).toAlgebra = (inferInstance : Algebra ↥L ↥L') := by
    refine Algebra.algebra_ext _ _ (fun x => Subtype.ext ?_)
    exact IsScalarTower.algebraMap_apply ↥L ↥L' Ω (x := x)
  cases hinst
  letI : Algebra ↥L ↥L' := (IntermediateField.inclusion hLL).toAlgebra
  haveI : IsScalarTower k ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- the level change of the decomposition groups
  have hcomp : Work.SSGRoute.decompKRestrict k ↥K ↥L' w u' hu'w
      = (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu).comp
          (Work.SSGRoute.decompKRestrict k ↥L ↥L' u u' hu'u) :=
    archPair_decompKRestrict_comp (k := k) w u u' hu hu'u hu'w
  -- the local identity
  have hz' : SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L' w u' hu'w)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L' w u' hu'w) x
      (SSGRoute.PTExt.eCoh 1 (↥(SSGRoute.PTExt.decompK (k := k) u'))
        (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L' w u' hu'w) (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))))
        ((groupCohomology.H1π _).hom z'))
      = SSGRoute.PTExt.extHMap (Work.SSGRoute.decompKRestrict k ↥L ↥L' u u' hu'u)
          (Work.SSGRoute.localUnitsMap k ↥L ↥L' u u' hu'u)
          (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) x
      (SSGRoute.PTExt.eCoh 1 (↥(SSGRoute.PTExt.decompK (k := k) u))
        (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu) (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))))
        ((groupCohomology.H1π _).hom z))) :=
    archPair_hz'_aux (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (L := L) (L' := L')
      (hKL := hKL) (hKL' := hKL') (hLL := hLL) (w := w) (u := u) (u' := u')
      (hu := hu) (hu'u := hu'u) (hu'w := hu'w) (x := x)
      (f'' := Work.SSGRoute.decompKRestrict k ↥K ↥L' w u' hu'w)
      (ι'' := Work.SSGRoute.localUnitsMap k ↥K ↥L' w u' hu'w)
      (hι'' := Work.SSGRoute.localUnitsMap_spec k ↥K ↥L' w u' hu'w)
      (hcomp := hcomp) (z := z) (z' := z') (hzz' := hzz')
  -- `p`-torsion of the level-`L` class
  have hptor : p • (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) x
      (SSGRoute.PTExt.eCoh 1 (↥(SSGRoute.PTExt.decompK (k := k) u))
        (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu) (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))))
        ((groupCohomology.H1π _).hom z))) = 0 := by
    have hA : ∀ a : Work.SSGRoute.PT.VFcoef p M T, p • a = 0 := by
      intro a
      rw [← Nat.cast_smul_eq_nsmul (ZMod p) p a, ZMod.natCast_self, zero_smul]
    have hpy : p • (SSGRoute.PTExt.eCoh 1 (↥(SSGRoute.PTExt.decompK (k := k) u))
        (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu) (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))))
        ((groupCohomology.H1π _).hom z)) = 0 :=
      PT.extH_nsmul_eq_zero_of_ptorsion _ hA _
    rw [SSGRoute.PTExt.levelPair, ← PT.nsmul_comp_aux_pt p _ _ rfl, hpy]
    simp
  -- `p`-torsion of `ι_u z`
  have hiota : ∀ n : ℕ, n • Work.SSGRoute.PT.iota (k := k) (L := ↥L) u (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) x
      (SSGRoute.PTExt.eCoh 1 (↥(SSGRoute.PTExt.decompK (k := k) u))
        (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu) (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))))
        ((groupCohomology.H1π _).hom z)))
      = Work.SSGRoute.PT.iota (k := k) (L := ↥L) u (n • (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) x
      (SSGRoute.PTExt.eCoh 1 (↥(SSGRoute.PTExt.decompK (k := k) u))
        (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu) (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))))
        ((groupCohomology.H1π _).hom z)))) := by
    intro n
    exact (map_nsmul (AddMonoidHom.mk' (Work.SSGRoute.PT.iota (k := k) (L := ↥L) u)
      (Work.SSGRoute.PT.iota_add (k := k) (L := ↥L) u)) n _).symm
  have hptor' : p • Work.SSGRoute.PT.iota (k := k) (L := ↥L) u (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) x
      (SSGRoute.PTExt.eCoh 1 (↥(SSGRoute.PTExt.decompK (k := k) u))
        (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu) (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))))
        ((groupCohomology.H1π _).hom z))) = 0 := by
    rw [hiota, hptor, Work.SSGRoute.PT.iota_zero]
  -- the coherence, and the level transport
  rw [← hχcompat L hKL L' hKL' hLL
    (Work.SSGRoute.PT.iota (k := k) (L := ↥L) u (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) x
      (SSGRoute.PTExt.eCoh 1 (↥(SSGRoute.PTExt.decompK (k := k) u))
        (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu) (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))))
        ((groupCohomology.H1π _).hom z)))) hptor']
  refine congrArg (fun v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k ↥L') 2 =>
    χ L' hKL' v) ?_
  rw [show Work.SSGRoute.PT.iota (k := k) (L := ↥L') u' (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L' w u' hu'w)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L' w u' hu'w) x
      (SSGRoute.PTExt.eCoh 1 (↥(SSGRoute.PTExt.decompK (k := k) u'))
        (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L' w u' hu'w) (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))))
        ((groupCohomology.H1π _).hom z')))
      = SSGRoute.PTExt.extToClasses
          (Work.SSGRoute.PT.iotaLift (k := k) (L := ↥L') u' (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L' w u' hu'w)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L' w u' hu'w) x
      (SSGRoute.PTExt.eCoh 1 (↥(SSGRoute.PTExt.decompK (k := k) u'))
        (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L' w u' hu'w) (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))))
        ((groupCohomology.H1π _).hom z')))) from rfl]
  rw [hz']
  rw [Work.SSGRoute.PT.iotaLift_idleRepMap k (↥L) (↥L') u u' hu'u
    (Work.SSGRoute.localUnitsMap k ↥L ↥L' u u' hu'u)
    (Work.SSGRoute.localUnitsMap_spec k ↥L ↥L' u u' hu'u) (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) x
      (SSGRoute.PTExt.eCoh 1 (↥(SSGRoute.PTExt.decompK (k := k) u))
        (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu) (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))))
        ((groupCohomology.H1π _).hom z)))]
  rw [Work.SSGRoute.PT.extToClasses_idleRepMap k (↥L) (↥L')
    (Work.SSGRoute.PT.iotaLift (k := k) (L := ↥L) u (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) x
      (SSGRoute.PTExt.eCoh 1 (↥(SSGRoute.PTExt.decompK (k := k) u))
        (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu) (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))))
        ((groupCohomology.H1π _).hom z))))]
  rfl

end Work.SSGRoute.PT
