import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `Ext`-level pairing calculus for the canonical Poitou–Tate pairing (G1, clause (1))

This file starts node `G1` of `Submission/Work/SSGRoute/DESIGN_PT.md` /
`Submission/Work/SSGRoute/DESIGN_EXT.md` §2 (the canonical local Tate pairing) in the
**generator-free form** of `DESIGN_EXT.md` §2: all pairings take their values in
`H^{s+r}(G, C_K) = extH (classesK k K) (s + r)` itself, computed by the Yoneda product
(`yonedaPair`, `pairK`) of `Submission/Work/SSGRoute/PTDefs.lean`.  Nothing (`inv`, `ℚ/ℤ`, a
fundamental class) is chosen, so the pairing is canonical and the reciprocity clause is a
consequence of the exactness of the class formation `Kˣ → 𝕀_K → C_K` (see
`DESIGN_EXT.md` §2, "Reciprocity becomes free").

The local pairing at a place `w` is the same Yoneda product at the level of the decomposition group
`D_w` (`Ext^1_{D_w}(M', K_wˣ) × H^1(D_w, M) → H^2(D_w, K_wˣ)`), and the `w`-component of the global
pairing is obtained from it by Shapiro's lemma followed by `𝕀_K → C_K` (node E2/E7c).  Those
identifications and the non-degeneracy clauses (1d),(1e) (nodes E7b + E8') are separate; what is
proved here is the *calculus*: bilinearity of the pairing in both variables, vanishing on the zero
class, and the compatibility of that calculus with change of group (`extRes`), with the coefficient
maps into `𝕀_K` and `C_K` (`extToIdeles`, `extToClasses`, `extLoc`), which is what clauses (1a),
(1b) and the "zero on a coboundary" half of (1c) of the target statement need once the bridges
`Hⁿ(G, A) ≅ Extⁿ_G(ℤ, A)` (node E0b) and the local Hilbert-90 bridge (node E7a) are in place.

The passage from this `C_K`-valued calculus to the `ZMod p`-valued statement is the fixed
isomorphism `χ : H²(Gal(K₀/k), C_{K₀})[p] ≅ ZMod p` of `DESIGN_EXT.md` §2, which is additive and
therefore preserves the calculus below.
-/

open CategoryTheory
open scoped TensorProduct

namespace SSGRoute.PTExt

/-! ## Bilinearity of the Yoneda pairing -/

/-- The Yoneda pairing is additive in its `Hˢ` variable. -/
theorem yonedaPair_add_left {G : Type} [Group G] {M A : Rep.{0} Coeff G} {r s : ℕ}
    (x : Abelian.Ext.{0} M A r) (h h' : extH M s) :
    yonedaPair x (h + h') = yonedaPair x h + yonedaPair x h' := by
  simpa only [yonedaPair] using Abelian.Ext.add_comp h h' x rfl

/-- The Yoneda pairing is additive in its `Extʳ` variable. -/
theorem yonedaPair_add_right {G : Type} [Group G] {M A : Rep.{0} Coeff G} {r s : ℕ}
    (x x' : Abelian.Ext.{0} M A r) (h : extH M s) :
    yonedaPair (x + x') h = yonedaPair x h + yonedaPair x' h := by
  simpa only [yonedaPair] using Abelian.Ext.comp_add h x x' rfl

/-- The Yoneda pairing kills the zero class in its `Hˢ` variable. -/
theorem yonedaPair_zero_left {G : Type} [Group G] {M A : Rep.{0} Coeff G} {r s : ℕ}
    (x : Abelian.Ext.{0} M A r) : yonedaPair x (0 : extH M s) = 0 := by
  simpa only [yonedaPair] using Abelian.Ext.zero_comp (unitRep G) s x (s + r) rfl

/-- The Yoneda pairing kills the zero class in its `Extʳ` variable. -/
theorem yonedaPair_zero_right {G : Type} [Group G] {M A : Rep.{0} Coeff G} {r s : ℕ}
    (h : extH M s) : yonedaPair (0 : Abelian.Ext.{0} M A r) h = 0 := by
  simpa only [yonedaPair] using Abelian.Ext.comp_zero h A r (s + r) rfl

/-! ## Change of group -/

/-- `extRes` (restriction/inflation of `Ext` along `f : H →* G`) is additive. -/
theorem extRes_add {G H : Type} [Group G] [Group H] (f : H →* G)
    {X Y : Rep.{0} Coeff G} {n : ℕ} (x x' : Abelian.Ext.{0} X Y n) :
    extRes f (x + x') = extRes f x + extRes f x' := by
  simpa only [extRes] using Abelian.Ext.mapExactFunctor_add (Rep.resFunctor f) X Y n x x'

/-- `extRes` kills the zero class. -/
theorem extRes_zero {G H : Type} [Group G] [Group H] (f : H →* G)
    {X Y : Rep.{0} Coeff G} {n : ℕ} :
    extRes f (0 : Abelian.Ext.{0} X Y n) = 0 := by
  simpa only [extRes] using Abelian.Ext.mapExactFunctor_zero (Rep.resFunctor f) X Y n

/-- `extHMap` is additive. -/
theorem extHMap_add {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) {n : ℕ}
    (y y' : extH A n) : extHMap f ι (y + y') = extHMap f ι y + extHMap f ι y' := by
  simp only [extHMap]
  rw [extRes_add, Abelian.Ext.add_comp, Abelian.Ext.comp_add]

/-- `extHMap` kills the zero class. -/
theorem extHMap_zero {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) {n : ℕ} :
    extHMap f ι (0 : extH A n) = 0 := by
  simp only [extHMap]
  rw [extRes_zero, Abelian.Ext.zero_comp, Abelian.Ext.comp_zero]

/-- Restriction `extHRestrict` is additive. -/
theorem extHRestrict_add {G : Type} [Group G] (D : Subgroup G) {A : Rep.{0} Coeff G} {n : ℕ}
    (y y' : extH A n) : extHRestrict D (y + y') = extHRestrict D y + extHRestrict D y' := by
  simpa only [extHRestrict] using extHMap_add D.subtype (𝟙 _) y y'

/-! ## The coefficient maps `Kˣ → 𝕀_K → C_K` at one level -/

section Level

open NK.GlobalCFT NK.HassePrinciple

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- `extToIdeles` is additive. -/
theorem extToIdeles_add {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (x x' : Abelian.Ext.{0} M (unitsK k K) r) :
    extToIdeles (x + x') = extToIdeles x + extToIdeles x' := by
  simpa only [extToIdeles] using
    Abelian.Ext.add_comp x x' (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleIncl k K)) (add_zero r)

/-- `extToIdeles` kills the zero class. -/
theorem extToIdeles_zero {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r : ℕ} :
    extToIdeles (0 : Abelian.Ext.{0} M (unitsK k K) r) = 0 := by
  simpa only [extToIdeles] using
    Abelian.Ext.zero_comp M r (Abelian.Ext.mk₀ (NK.HassePrinciple.ideleIncl k K)) r (add_zero r)

/-- `extToClasses` is additive. -/
theorem extToClasses_add {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (y y' : Abelian.Ext.{0} M (idelesK k K) r) :
    extToClasses (y + y') = extToClasses y + extToClasses y' := by
  simpa only [extToClasses] using
    Abelian.Ext.add_comp y y' (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k K)) (add_zero r)

/-- `extToClasses` kills the zero class. -/
theorem extToClasses_zero {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r : ℕ} :
    extToClasses (0 : Abelian.Ext.{0} M (idelesK k K) r) = 0 := by
  simpa only [extToClasses] using
    Abelian.Ext.zero_comp M r (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k K)) r
      (add_zero r)

/-- **The exactness input of the reciprocity clause.**  The `C_K`-valued pairing kills the image of
the multiplicative group: the composite `Kˣ → 𝕀_K → C_K` is zero, so pushing a `Kˣ`-valued class
into `𝕀_K` and then into `C_K` gives `0`.  In the generator-free route of `DESIGN_EXT.md` §2 this is
what makes *reciprocity free*: the sum over the places of the local values of a global pair is
(by Shapiro, node E2) the image of the global cup product `a ∪ b ∈ H²(G, Kˣ)` in `H²(G, C_K)`, and
that image is zero by this lemma. -/
theorem extToClasses_extToIdeles {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (z : Abelian.Ext.{0} M (unitsK k K) r) :
    extToClasses (extToIdeles z) = 0 := by
  simp only [extToIdeles, extToClasses]
  rw [Abelian.Ext.comp_assoc]
  · rw [Abelian.Ext.mk₀_comp_mk₀, NK.HassePrinciple.ideleIncl_comp_classGroupMap,
      Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
  all_goals simp [Nat.add_assoc]

/-! ## The pairing at the level `K` -/

/-- `pairK` is additive in its `Hˢ` variable. -/
theorem pairK_add_left {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r s : ℕ}
    (x : Abelian.Ext.{0} M (classesK k K) r) (h h' : extH M s) :
    pairK x (h + h') = pairK x h + pairK x h' := by
  simpa only [pairK] using yonedaPair_add_left x h h'

/-- `pairK` is additive in its `Extʳ` variable. -/
theorem pairK_add_right {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r s : ℕ}
    (x x' : Abelian.Ext.{0} M (classesK k K) r) (h : extH M s) :
    pairK (x + x') h = pairK x h + pairK x' h := by
  simpa only [pairK] using yonedaPair_add_right x x' h

/-- `pairK` kills the zero class in its `Hˢ` variable. -/
theorem pairK_zero_left {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r s : ℕ}
    (x : Abelian.Ext.{0} M (classesK k K) r) : pairK x (0 : extH M s) = 0 := by
  simpa only [pairK] using yonedaPair_zero_left (G := K ≃ₐ[k] K) (M := M) (A := classesK k K)
    (r := r) (s := s) x

/-- `pairK` kills the zero class in its `Extʳ` variable. -/
theorem pairK_zero_right {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r s : ℕ}
    (h : extH M s) : pairK (0 : Abelian.Ext.{0} M (classesK k K) r) h = 0 := by
  simpa only [pairK] using yonedaPair_zero_right (G := K ≃ₐ[k] K) (M := M) (A := classesK k K)
    (r := r) (s := s) h

end Level

/-! ## Localisation at a place -/

section LocalPlace

open NK.GlobalCFT NK.HassePrinciple

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- `extLoc` is additive (localisation of the idèle-class group at a place is additive). -/
theorem extLoc_add (w : Place K) {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (x x' : Abelian.Ext.{0} M (idelesK k K) r) :
    extLoc w (x + x') = extLoc w x + extLoc w x' := by
  simp only [extLoc]
  rw [extRes_add, Abelian.Ext.add_comp]

/-- `extLoc` kills the zero class. -/
theorem extLoc_zero (w : Place K) {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r : ℕ} :
    extLoc w (0 : Abelian.Ext.{0} M (idelesK k K) r) = 0 := by
  simp only [extLoc]
  rw [extRes_zero, Abelian.Ext.zero_comp]

end LocalPlace

/-! ## Naturality of the Yoneda pairing under coefficient maps -/

/-- The Yoneda pairing is compatible with postcomposition in its `Extʳ` variable — the formal
content of `Ext.comp_assoc`, and the naturality of the pairing under coefficient maps. -/
theorem yonedaPair_comp {G : Type} [Group G] {M A B : Rep.{0} Coeff G} {r r' s : ℕ}
    (x : Abelian.Ext.{0} M A r) (β : Abelian.Ext.{0} A B r') (h : extH M s) :
    yonedaPair (x.comp β (rfl : r + r' = r + r')) h =
      (yonedaPair x h).comp β (Nat.add_assoc s r r') := by
  simpa only [yonedaPair] using
    (Abelian.Ext.comp_assoc h x β (rfl : s + r = s + r) (rfl : r + r' = r + r')
      (Nat.add_assoc s r r')).symm

/-! ## Reciprocity at the level `K` -/

section Level

open NK.GlobalCFT NK.HassePrinciple

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- **Reciprocity at level `K`, generator-free form.**  The canonical pairing `pairK` kills every
class that comes from the multiplicative group `Kˣ`: the composite `Kˣ → 𝕀_K → C_K` of the class
formation is zero, hence so is the composite of the induced maps on `Ext`.

This is the formal content of "reciprocity becomes free" in `DESIGN_EXT.md` §2: the sum over the
places of the local values of a global pair is (by Shapiro, node E2) the image of the global cup
product `a ∪ b ∈ H²(G, Kˣ)` in `H²(G, C_K)`, and that image is `0` by this lemma. -/
theorem pairK_extToClasses_extToIdeles_zero {M : Rep.{0} Coeff (K ≃ₐ[k] K)} {r s : ℕ}
    (z : Abelian.Ext.{0} M (unitsK k K) r) (h : extH M s) :
    pairK (extToClasses (extToIdeles z)) h = 0 := by
  rw [extToClasses_extToIdeles]
  simpa only [pairK] using
    yonedaPair_zero_right (G := K ≃ₐ[k] K) (M := M) (A := classesK k K) (r := r) (s := s) h

end Level

end SSGRoute.PTExt
