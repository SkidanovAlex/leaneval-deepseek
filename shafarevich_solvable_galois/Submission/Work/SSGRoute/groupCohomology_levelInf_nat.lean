import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Have
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Submission.Work.SSGRoute.phi1_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Level naturality of the pairing against `Φ_F` (`D5'`)

This file proves `Work.SSGRoute.groupCohomology_levelInf_nat`: the value of the level pairing
`x ↦ (h ↦ h ∘ infl x)` against a coefficient class `Φ_F : ℤ → C_F` is compatible with inflation of
the level: pairing `Φ_F` at the base level `F` and then applying the class-group inclusion is the
same as applying `res Φ_F ≫ classIncl` at the higher level to the inflated class.

The mathematical content is the compatibility of the Bockstein connecting map
`δ : H¹(·, 𝔽_p) → H²(·, ℤ)` of the coefficient sequence `0 → ℤ --p--> ℤ → 𝔽_p → 0` with the
restriction `Gal(L/k) → Gal(F/k)`, together with associativity of the multiplication by a
degree-zero coefficient class.

Everything is reduced to the *carry cocycle* description of `δ` (`δ₁_apply` of Mathlib): an
integral lift `Y : G → ℤ` of a `1`-cocycle `z` with values in `𝔽_p` has `d₁₂ Y` divisible by `p`,
and `p·(d₁₂ Y)/p = d₁₂ Y` makes `(d₁₂ Y)/p` a `2`-cocycle with integral coefficients representing
`δ z`.  Since the construction only uses an integral lift of `z`, it is compatible with the
restriction of groups.

* `carryCocycle_compat_aux`: `p • Z` is the differential of the lifted cochain `Y`;
* `delta_eq_H2π_carry_aux`: the connecting map on the class of a cocycle is the class of the carry
  cocycle;
* `coe_mapCocycles₂_apply_aux`, `coe_mapCocycles₁_trivResInv_aux`: the underlying functions of the
  cocycle-level maps `mapCocycles₁`, `mapCocycles₂`;
* `delta_trivResInv`: the connecting map of the coefficient sequence commutes with restriction;
* `groupCohomology_levelInf_nat`: the statement of the file.
-/

open CategoryTheory

namespace Work.SSGRoute

open SSGRoute.PTExt in
/-- The `p`-multiple of the carry cocycle `Z` is the differential `d₁₂` of the lifted `1`-cochain
`Y`, so `Z` is a `2`-cocycle with coefficients in `Coeff = ULift ℤ`. -/
lemma carryCocycle_compat_aux (G : Type) [Group G] (p : ℕ) (Y : G → ℤ) (Z : G × G → ℤ)
    (hZ : ∀ g h, (p : ℤ) * Z (g, h) = Y h - Y (g * h) + Y g) :
    (⇑(Rep.Hom.hom (SSGRoute.Phi1.coeffSES G p).f)) ∘
        (fun q : G × G => (ULift.up (Z q) : Coeff))
      = ⇑(groupCohomology.d₁₂ (Rep.trivial Coeff G Coeff))
          (fun g : G => (ULift.up (Y g) : Coeff)) := by
  funext q
  obtain ⟨g₁, g₂⟩ := q
  show (p : Coeff) * ULift.up (Z (g₁, g₂)) =
    (groupCohomology.d₁₂ (Rep.trivial Coeff G Coeff))
      (fun g : G => (ULift.up (Y g) : Coeff)) (g₁, g₂)
  rw [groupCohomology.d₁₂_hom_apply, Rep.trivial_ρ_apply]
  apply ULift.ext
  simp only [ULift.mul_down, ULift.add_down, ULift.sub_down]
  rw [show (((p : Coeff)).down : ℤ) = (p : ℤ) from rfl, hZ g₁ g₂]

open SSGRoute.PTExt in
/-- **The connecting map computed by the carry cocycle.**  If `Y : G → ℤ` is an integral lift of
the `1`-cocycle `z` (with values in `𝔽_p`) and `Z` is a `2`-cochain with `p·Z = d₁₂ Y`, then `Z` is
a `2`-cocycle with integral coefficients representing `δ z`. -/
theorem delta_eq_H2π_carry_aux (G : Type) [Group G] (p : ℕ) [Fact p.Prime]
    (z : groupCohomology.cocycles₁ (Rep.trivial Coeff G (ZMod p))) (Y : G → ℤ)
    (hY : ∀ g, ((Y g : ℤ) : ZMod p) = z g)
    (Z : G × G → ℤ) (hZ : ∀ g h, (p : ℤ) * Z (g, h) = Y h - Y (g * h) + Y g) :
    (groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom
        ((ConcreteCategory.hom (groupCohomology.H1π (Rep.trivial Coeff G (ZMod p)))) z) =
      (ConcreteCategory.hom (groupCohomology.H2π (Rep.trivial Coeff G Coeff)))
        ⟨(fun q : G × G => (ULift.up (Z q) : Coeff)),
          groupCohomology.mem_cocycles₂_of_comp_eq_d₁₂ (SSGRoute.Phi1.coeffSES_shortExact G p)
            (carryCocycle_compat_aux G p Y Z hZ)⟩ := by
  refine groupCohomology.δ₁_apply (SSGRoute.Phi1.coeffSES_shortExact G p) z
    (fun g => (ULift.up (Y g) : Coeff)) ?_ (fun q => (ULift.up (Z q) : Coeff))
    (carryCocycle_compat_aux G p Y Z hZ)
  funext g
  exact hY g

open SSGRoute.PTExt in
/-- The underlying function of `mapCocycles₂` is the obvious restriction of a `2`-cochain. -/
lemma coe_mapCocycles₂_apply_aux {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep Coeff G} {B : Rep Coeff H} (φ : Rep.res f A ⟶ B)
    (x : groupCohomology.cocycles₂ A) (q : H × H) :
    (↑((ConcreteCategory.hom (groupCohomology.mapCocycles₂ f φ)) x) : H × H → B) q
      = φ.hom (x (f q.1, f q.2)) := by
  rw [groupCohomology.coe_mapCocycles₂]
  rfl

open SSGRoute.PTExt in
/-- The underlying function of `mapCocycles₁` along `trivResInv` is precomposition with `f`. -/
lemma coe_mapCocycles₁_trivResInv_aux {G H : Type} [Group G] [Group H] (f : H →* G)
    (p : ℕ) (z : groupCohomology.cocycles₁ (Rep.trivial Coeff G (ZMod p))) :
    ⇑((ConcreteCategory.hom (groupCohomology.mapCocycles₁ f (SSGRoute.PTExt.trivResInv f (ZMod p)))) z)
      = fun h : H => z (f h) := by
  funext h
  rw [groupCohomology.coe_mapCocycles₁]
  rfl

open SSGRoute.PTExt in
/-- **The Bockstein commutes with restriction.**  For a group homomorphism `f : H →* G`, the
connecting map of the coefficient sequence `0 → ℤ --p--> ℤ → 𝔽_p → 0` is compatible with
restriction: the `δ` of the inflated class is the restriction of `δ` of the class. -/
theorem delta_trivResInv {G H : Type} [Group G] [Group H] (f : H →* G) (p : ℕ) [Fact p.Prime]
    (h : groupCohomology (Rep.trivial Coeff G (ZMod p)) 1) :
    (ConcreteCategory.hom (groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact H p) 1 2 rfl))
        ((ConcreteCategory.hom (groupCohomology.map f (SSGRoute.PTExt.trivResInv f (ZMod p)) 1)) h)
      = (ConcreteCategory.hom (groupCohomology.map f
          ((Rep.resFunctor f).map (𝟙 (SSGRoute.PTExt.unitRep G))) 2))
        ((ConcreteCategory.hom (groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl)) h) := by
  induction h using groupCohomology.H1_induction_on with
  | h z =>
    classical
    have hcoc : ∀ g h' : G, z (g * h') = z h' + z g := by
      intro g h'
      have h1 := (groupCohomology.mem_cocycles₁_iff (⇑z)).1 z.2 g h'
      simpa using h1
    let Y : G → ℤ := fun g => Classical.choose (ZMod.intCast_surjective (z g))
    have hY : ∀ g, ((Y g : ℤ) : ZMod p) = z g :=
      fun g => Classical.choose_spec (ZMod.intCast_surjective (z g))
    have hdvd : ∀ g h' : G, (p : ℤ) ∣ Y h' - Y (g * h') + Y g := by
      intro g h'
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hcast : ((Y h' - Y (g * h') + Y g : ℤ) : ZMod p) = z h' - z (g * h') + z g := by
        rw [Int.cast_add, Int.cast_sub, hY h', hY (g * h'), hY g]
      rw [hcast, hcoc g h']
      ring
    let Z : G × G → ℤ := fun q => (Y q.2 - Y (q.1 * q.2) + Y q.1) / p
    have hZ : ∀ g h' : G, (p : ℤ) * Z (g, h') = Y h' - Y (g * h') + Y g :=
      fun g h' => Int.mul_ediv_cancel' (hdvd g h')
    let cG : groupCohomology.cocycles₂ (Rep.trivial Coeff G Coeff) :=
      ⟨(fun q : G × G => (ULift.up (Z q) : Coeff)),
        groupCohomology.mem_cocycles₂_of_comp_eq_d₁₂ (SSGRoute.Phi1.coeffSES_shortExact G p)
          (carryCocycle_compat_aux G p Y Z hZ)⟩
    have hδG : (ConcreteCategory.hom (groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl))
        ((ConcreteCategory.hom (groupCohomology.H1π (Rep.trivial Coeff G (ZMod p)))) z)
        = (ConcreteCategory.hom (groupCohomology.H2π (Rep.trivial Coeff G Coeff))) cG :=
      delta_eq_H2π_carry_aux G p z Y hY Z hZ
    let T := SSGRoute.PTExt.trivResInv f (ZMod p)
    let z' : groupCohomology.cocycles₁ (Rep.trivial Coeff H (ZMod p)) :=
      groupCohomology.mapCocycles₁ f T z
    have hz' : ⇑z' = fun h' : H => z (f h') := coe_mapCocycles₁_trivResInv_aux f p z
    let Y' : H → ℤ := fun h' => Y (f h')
    have hY' : ∀ h', ((Y' h' : ℤ) : ZMod p) = z' h' := by
      intro h'
      rw [hz']
      exact hY (f h')
    have hcoc' : ∀ g h' : H, z' (g * h') = z' h' + z' g := by
      intro g h'
      have h1 := (groupCohomology.mem_cocycles₁_iff (⇑z')).1 z'.2 g h'
      simpa using h1
    have hdvd' : ∀ g h' : H, (p : ℤ) ∣ Y' h' - Y' (g * h') + Y' g := by
      intro g h'
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hcast : ((Y' h' - Y' (g * h') + Y' g : ℤ) : ZMod p) = z' h' - z' (g * h') + z' g := by
        rw [Int.cast_add, Int.cast_sub, hY' h', hY' (g * h'), hY' g]
      rw [hcast, hcoc' g h']
      ring
    let Z' : H × H → ℤ := fun q => (Y' q.2 - Y' (q.1 * q.2) + Y' q.1) / p
    have hZ' : ∀ g h' : H, (p : ℤ) * Z' (g, h') = Y' h' - Y' (g * h') + Y' g :=
      fun g h' => Int.mul_ediv_cancel' (hdvd' g h')
    let cH : groupCohomology.cocycles₂ (Rep.trivial Coeff H Coeff) :=
      ⟨(fun q : H × H => (ULift.up (Z' q) : Coeff)),
        groupCohomology.mem_cocycles₂_of_comp_eq_d₁₂ (SSGRoute.Phi1.coeffSES_shortExact H p)
          (carryCocycle_compat_aux H p Y' Z' hZ')⟩
    have hδH : (ConcreteCategory.hom (groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact H p) 1 2 rfl))
        ((ConcreteCategory.hom (groupCohomology.H1π (Rep.trivial Coeff H (ZMod p)))) z')
        = (ConcreteCategory.hom (groupCohomology.H2π (Rep.trivial Coeff H Coeff))) cH :=
      delta_eq_H2π_carry_aux H p z' Y' hY' Z' hZ'
    rw [groupCohomology.H1π_comp_map_apply f T z, hδH, hδG,
      groupCohomology.H2π_comp_map_apply f
        ((Rep.resFunctor f).map (𝟙 (SSGRoute.PTExt.unitRep G))) cG]
    have hZeq : ∀ q : H × H, Z' q = Z (f q.1, f q.2) := by
      intro q
      simp only [Z', Z, Y', map_mul]
    have hfun : ⇑cH = ⇑(groupCohomology.mapCocycles₂ f
        ((Rep.resFunctor f).map (𝟙 (SSGRoute.PTExt.unitRep G))) cG) := by
      funext q
      rw [coe_mapCocycles₂_apply_aux]
      show (ULift.up (Z' q) : Coeff) =
        ((Rep.resFunctor f).map (𝟙 (SSGRoute.PTExt.unitRep G))).hom (ULift.up (Z (f q.1, f q.2)))
      rw [hZeq q]
      rfl
    congr 1
    exact Subtype.ext hfun

theorem groupCohomology_levelInf_nat (k F L : Type) [Field k] [NumberField k] [Field F] [NumberField F] [Field L] [NumberField L] [Algebra k F] [Algebra F L] [Algebra k L] [IsScalarTower k F L] [FiniteDimensional k F] [IsGalois k F] (p : ℕ) [Fact p.Prime] (Φ_F : SSGRoute.PTExt.unitRep (F ≃ₐ[k] F) ⟶ SSGRoute.PTExt.classesK k F) (h_F : groupCohomology (Rep.trivial SSGRoute.PTExt.Coeff (F ≃ₐ[k] F) (ZMod p)) 1) : groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L)) (CategoryTheory.CategoryStruct.comp ((Rep.resFunctor (SSGRoute.PTExt.galRes k F L)).map Φ_F) (SSGRoute.PTExt.classIncl k F L)) 2 ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (L ≃ₐ[k] L) p) 1 2 rfl).hom ((groupCohomology.map (SSGRoute.PTExt.galRes k F L) (SSGRoute.PTExt.trivResInv (SSGRoute.PTExt.galRes k F L) (ZMod p)) 1).hom h_F)) = (groupCohomology.map (SSGRoute.PTExt.galRes k F L) (SSGRoute.PTExt.classIncl k F L) 2).hom ((groupCohomology.map (MonoidHom.id (F ≃ₐ[k] F)) Φ_F 2).hom ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (F ≃ₐ[k] F) p) 1 2 rfl).hom h_F)) := by
  classical
  let Ψ : Rep.res (SSGRoute.PTExt.galRes k F L) (SSGRoute.PTExt.unitRep (F ≃ₐ[k] F)) ⟶
      SSGRoute.PTExt.classesK k L :=
    CategoryTheory.CategoryStruct.comp ((Rep.resFunctor (SSGRoute.PTExt.galRes k F L)).map Φ_F)
      (SSGRoute.PTExt.classIncl k F L)
  show (ConcreteCategory.hom (groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L))
          (A := Rep.res (SSGRoute.PTExt.galRes k F L) (SSGRoute.PTExt.unitRep (F ≃ₐ[k] F)))
          (B := SSGRoute.PTExt.classesK k L) Ψ 2))
        ((ConcreteCategory.hom (groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (L ≃ₐ[k] L) p) 1 2 rfl))
          ((ConcreteCategory.hom (groupCohomology.map (SSGRoute.PTExt.galRes k F L)
            (SSGRoute.PTExt.trivResInv (SSGRoute.PTExt.galRes k F L) (ZMod p)) 1)) h_F))
      = (ConcreteCategory.hom (groupCohomology.map (SSGRoute.PTExt.galRes k F L)
          (SSGRoute.PTExt.classIncl k F L) 2))
        ((ConcreteCategory.hom (groupCohomology.map (MonoidHom.id (F ≃ₐ[k] F)) Φ_F 2))
          ((ConcreteCategory.hom (groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (F ≃ₐ[k] F) p) 1 2 rfl)) h_F))
  have hsq := delta_trivResInv (SSGRoute.PTExt.galRes k F L) p h_F
  have hcomp : (groupCohomology.map (SSGRoute.PTExt.galRes k F L)
        (A := SSGRoute.PTExt.unitRep (F ≃ₐ[k] F)) (B := SSGRoute.PTExt.classesK k L) Ψ 2)
      = (groupCohomology.map (MonoidHom.id (F ≃ₐ[k] F)) Φ_F 2) ≫
        (groupCohomology.map (SSGRoute.PTExt.galRes k F L)
          (SSGRoute.PTExt.classIncl k F L) 2) :=
    groupCohomology.map_comp (k := SSGRoute.PTExt.Coeff)
      (A := SSGRoute.PTExt.unitRep (F ≃ₐ[k] F))
      (B := SSGRoute.PTExt.classesK k F)
      (C := SSGRoute.PTExt.classesK k L)
      (MonoidHom.id (F ≃ₐ[k] F)) (SSGRoute.PTExt.galRes k F L)
      Φ_F (SSGRoute.PTExt.classIncl k F L) 2
  have hcomp2 : (groupCohomology.map (SSGRoute.PTExt.galRes k F L)
        (A := SSGRoute.PTExt.unitRep (F ≃ₐ[k] F))
        (B := Rep.res (SSGRoute.PTExt.galRes k F L) (SSGRoute.PTExt.unitRep (F ≃ₐ[k] F)))
        ((Rep.resFunctor (SSGRoute.PTExt.galRes k F L)).map
          (𝟙 (SSGRoute.PTExt.unitRep (F ≃ₐ[k] F)))) 2) ≫
      (groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L))
        (A := Rep.res (SSGRoute.PTExt.galRes k F L) (SSGRoute.PTExt.unitRep (F ≃ₐ[k] F)))
        (B := SSGRoute.PTExt.classesK k L) Ψ 2)
      = (groupCohomology.map (SSGRoute.PTExt.galRes k F L)
          (A := SSGRoute.PTExt.unitRep (F ≃ₐ[k] F)) (B := SSGRoute.PTExt.classesK k L) Ψ 2) :=
    (groupCohomology.map_comp (k := SSGRoute.PTExt.Coeff)
      (A := SSGRoute.PTExt.unitRep (F ≃ₐ[k] F))
      (B := Rep.res (SSGRoute.PTExt.galRes k F L) (SSGRoute.PTExt.unitRep (F ≃ₐ[k] F)))
      (C := SSGRoute.PTExt.classesK k L)
      (SSGRoute.PTExt.galRes k F L) (MonoidHom.id (L ≃ₐ[k] L))
      ((Rep.resFunctor (SSGRoute.PTExt.galRes k F L)).map
        (𝟙 (SSGRoute.PTExt.unitRep (F ≃ₐ[k] F))))
      Ψ 2).symm
  have hcomp2_app :
      (ConcreteCategory.hom (groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L))
        (A := Rep.res (SSGRoute.PTExt.galRes k F L) (SSGRoute.PTExt.unitRep (F ≃ₐ[k] F)))
        (B := SSGRoute.PTExt.classesK k L) Ψ 2))
        ((ConcreteCategory.hom (groupCohomology.map (SSGRoute.PTExt.galRes k F L)
          ((Rep.resFunctor (SSGRoute.PTExt.galRes k F L)).map
            (𝟙 (SSGRoute.PTExt.unitRep (F ≃ₐ[k] F)))) 2))
          ((ConcreteCategory.hom (groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (F ≃ₐ[k] F) p) 1 2 rfl)) h_F))
      = (ConcreteCategory.hom (groupCohomology.map (SSGRoute.PTExt.galRes k F L)
          (A := SSGRoute.PTExt.unitRep (F ≃ₐ[k] F)) (B := SSGRoute.PTExt.classesK k L) Ψ 2))
          ((ConcreteCategory.hom (groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (F ≃ₐ[k] F) p) 1 2 rfl)) h_F) :=
    congrArg (fun (M : groupCohomology (SSGRoute.PTExt.unitRep (F ≃ₐ[k] F)) 2 ⟶
        groupCohomology (SSGRoute.PTExt.classesK k L) 2) =>
      (ConcreteCategory.hom M)
        ((ConcreteCategory.hom (groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (F ≃ₐ[k] F) p) 1 2 rfl)) h_F)) hcomp2
  have hcomp_app :
      (ConcreteCategory.hom (groupCohomology.map (SSGRoute.PTExt.galRes k F L)
          (SSGRoute.PTExt.classIncl k F L) 2))
        ((ConcreteCategory.hom (groupCohomology.map (MonoidHom.id (F ≃ₐ[k] F)) Φ_F 2))
          ((ConcreteCategory.hom (groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (F ≃ₐ[k] F) p) 1 2 rfl)) h_F))
      = (ConcreteCategory.hom (groupCohomology.map (SSGRoute.PTExt.galRes k F L)
          (A := SSGRoute.PTExt.unitRep (F ≃ₐ[k] F)) (B := SSGRoute.PTExt.classesK k L) Ψ 2))
          ((ConcreteCategory.hom (groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (F ≃ₐ[k] F) p) 1 2 rfl)) h_F) :=
    (congrArg (fun (M : groupCohomology (SSGRoute.PTExt.unitRep (F ≃ₐ[k] F)) 2 ⟶
        groupCohomology (SSGRoute.PTExt.classesK k L) 2) =>
      (ConcreteCategory.hom M)
        ((ConcreteCategory.hom (groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (F ≃ₐ[k] F) p) 1 2 rfl)) h_F)) hcomp).symm
  rw [hsq, hcomp2_app, hcomp_app]

end Work.SSGRoute
