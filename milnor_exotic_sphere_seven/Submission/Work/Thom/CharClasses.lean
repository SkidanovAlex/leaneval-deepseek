import Mathlib
import Submission.Work.Thom.Gysin
import Submission.Work.TangentClasses.Pontryagin

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# Characteristic classes from the Thom class: Stiefel–Whitney and Pontryagin classes

This module draws the consequences of `Submission/Work/Thom/ThomClass.lean` for *characteristic
classes*.

## Coefficients

Everything in the Thom chapter is stated for singular cohomology with coefficients in a commutative
ring, so the same constructions give

* the **Euler class** `e(E) ∈ H^n(B;ℤ)` of an oriented rank-`n` real bundle (coefficients `ℤ`,
  `Work.Thom.eulerClass`), and
* the **top Stiefel–Whitney class** `w_n(E) ∈ H^n(B;ℤ/2)` of an arbitrary rank-`n` real bundle
  (coefficients `ℤ/2`, `Work.Thom.stiefelWhitney`), with no orientability needed.

The vanishing theorem `e = 0` for a bundle with a nowhere-zero section, proved for `ℤ` in
`Submission/Work/Thom/Euler.lean`, holds verbatim for `ℤ/2`, where it is the classical statement
`w_n(E) = 0` for a rank-`n` bundle with a nowhere-zero section:
`Work.Thom.eulerClassGen_eq_zero_of_nowhereZeroSection`.

## Pontryagin classes

For a real bundle `E` the Pontryagin classes are `p_i(E) = (-1)^i c_{2i}(E ⊗ ℂ)`, so their
construction needs the Chern classes of the complexification — a complex-bundle version of the
Thom isomorphism story, not built in this chapter.  What *is* available, and is what the workspace's
endgame consumes, is:

* `Work.Thom.p1Presentation_unique` — the first Pontryagin class of a **clutching presentation**
  (a finite Whitney sum of rank-`4` bundles pulled back from `S⁴`, the shape in which the
  workspace computes) is *characterised* by naturality, Whitney additivity and the normalisation
  `p₁(b) = pontryagin1 b` on `S⁴`.  In particular `p₁` of a presented bundle is a *function* of the
  presentation, which is what makes the repaired interface of
  `Submission/Work/Thom/Interface.lean` honest (no free class).

The naturality/additivity/stability of that class are proved in
`Submission/Work/TangentClasses/Pontryagin.lean` (`p1_comp`, `p1_append`, `p1_of_trivial`,
`p1_prod_model`); they are not duplicated here.
-/

namespace Work.Thom

open CategoryTheory
open Work.TangentClasses
open Work.CharacteristicClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## The Euler class with arbitrary coefficients -/

/-- **The Euler class with coefficients in a commutative ring `R`**: the pullback of a class of the
Thom pair `(E,E∖0)` along the zero section.  For `R = ℤ` this is `Work.Thom.eulerClass`. -/
def eulerClassGen (R : Type) [CommRing R] (Z : RealBundle B F ι) (n : ℕ)
    (τ : RelCoh R n Z.TotalSpace (zeroComplement Z)) : Coh R n B :=
  (CohMap (zeroSection Z) R n).hom ((relToAbs R (zeroComplement Z) n).hom τ)

/-- The abstract cohomological vanishing step, with coefficients in any commutative ring: if
`z, σ : B → X` are homotopic and `σ` factors through `A ⊆ X`, then `z^*` kills every class of
`H^n(X,A;R)`.  (The `R = ℤ` case is `Work.Thom.CohMap_eq_zero_of_homotopic_of_factors`.) -/
theorem CohMap_eq_zero_of_homotopic_of_factors_gen (R : Type) [CommRing R] {X : Type}
    [TopologicalSpace X] (A : Set X) {B : Type} [TopologicalSpace B] {z σ : C(B, X)}
    (h : ContinuousMap.Homotopic z σ) (σ' : C(B, A)) (hfac : ∀ b, ((σ' b : A) : X) = σ b)
    (n : ℕ) (τ : RelCoh R n X A) :
    (CohMap z R n).hom ((relToAbs R A n).hom τ) = 0 := by
  have hσeq : σ = (subtypeMap A).comp σ' := by
    ext b
    exact (hfac b).symm
  have hzero : ((CohMap (subtypeMap A) R n).hom).comp ((relToAbs R A n).hom) = 0 := by
    rw [← ModuleCat.hom_comp, relToAbs_comp_CohMap_subtype R A n, ModuleCat.hom_zero]
  have hh : ((CohMap (subtypeMap A) R n).hom) ((relToAbs R A n).hom τ) = 0 := by
    have h1 := congrArg (fun l : RelCoh R n X A →ₗ[R] Coh R n A => l τ) hzero
    simpa using h1
  have hσ' : (CohMap σ R n).hom =
      ((CohMap σ' R n).hom).comp ((CohMap (subtypeMap A) R n).hom) := by
    rw [hσeq, CohMap_comp, ModuleCat.hom_comp]
  rw [CohMap_homotopic h R n, hσ', LinearMap.comp_apply, hh, map_zero]

/-- **The Euler class (with any coefficients) vanishes on a bundle with a nowhere-zero continuous
section.** -/
theorem eulerClassGen_eq_zero_of_nowhereZeroSection (R : Type) [CommRing R] (Z : RealBundle B F ι)
    (σ : C(B, Z.TotalSpace)) (hσ : ∀ x, (σ x).1 = x) (hσ0 : ∀ x, (σ x).2 ≠ 0) (n : ℕ)
    (τ : RelCoh R n Z.TotalSpace (zeroComplement Z)) : eulerClassGen R Z n τ = 0 := by
  classical
  have hmem : ∀ x, σ x ∈ zeroComplement Z := fun x => by
    rw [mem_zeroComplement]
    exact hσ0 x
  let σ' : C(B, zeroComplement Z) :=
    ⟨fun x => ⟨σ x, hmem x⟩, σ.continuous.subtype_mk hmem⟩
  have hfac : ∀ b, ((σ' b : zeroComplement Z) : Z.TotalSpace) = σ b := fun b => rfl
  have hcont : Continuous (fun p : unitInterval × B =>
      (⟨(σ p.2).1, ((p.1 : unitInterval) : ℝ) • (σ p.2).2⟩ : Z.TotalSpace)) :=
    continuous_smul_section Z (σ.comp ⟨Prod.snd, continuous_snd⟩)
      ⟨fun p : unitInterval × B => ((p.1 : unitInterval) : ℝ),
        continuous_subtype_val.comp continuous_fst⟩
  have hhom : ContinuousMap.Homotopic (zeroSection Z) σ := by
    refine ⟨ContinuousMap.Homotopy.mk ⟨_, hcont⟩ ?_ ?_⟩
    · intro x
      show (⟨(σ x).1, ((0 : unitInterval) : ℝ) • (σ x).2⟩ : Z.TotalSpace) = zeroSection Z x
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_smul, zeroSection_apply, hσ x]
    · intro x
      show (⟨(σ x).1, ((1 : unitInterval) : ℝ) • (σ x).2⟩ : Z.TotalSpace) = σ x
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, one_smul]
  exact CohMap_eq_zero_of_homotopic_of_factors_gen R (zeroComplement Z) hhom σ' hfac n τ

/-! ## The top Stiefel–Whitney class -/

/-- **The top Stiefel–Whitney class** `w_n(E) ∈ H^n(B;ℤ/2)` of a rank-`n` real bundle, from a
mod-`2` class `τ ∈ H^n(E,E∖0;ℤ/2)` of the Thom pair: its pullback along the zero section.  With
`ℤ/2` coefficients no orientability is needed, and when `τ` is the mod-`2` Thom class (the
orientation-free Thom isomorphism) this is `w_n(E)`. -/
def stiefelWhitney (Z : RealBundle B F ι) (n : ℕ)
    (τ : RelCoh (ZMod 2) n Z.TotalSpace (zeroComplement Z)) : Coh (ZMod 2) n B :=
  eulerClassGen (ZMod 2) Z n τ

/-- **`w_n(E) = 0` for a bundle with a nowhere-zero section** — the Stiefel–Whitney form of the
Euler-class vanishing theorem. -/
theorem stiefelWhitney_eq_zero_of_nowhereZeroSection (Z : RealBundle B F ι)
    (σ : C(B, Z.TotalSpace)) (hσ : ∀ x, (σ x).1 = x) (hσ0 : ∀ x, (σ x).2 ≠ 0) (n : ℕ)
    (τ : RelCoh (ZMod 2) n Z.TotalSpace (zeroComplement Z)) : stiefelWhitney Z n τ = 0 :=
  eulerClassGen_eq_zero_of_nowhereZeroSection (ZMod 2) Z σ hσ hσ0 n τ

/-- **`w(E ⊕ ε¹) = 0`**: a bundle containing a trivial line summand has vanishing top
Stiefel–Whitney class (the section `x ↦ ⟨x,(0,1)⟩`, as in
`Work.Thom.eulerClass_sum_trivial_eq_zero`). -/
theorem stiefelWhitney_sum_trivial_eq_zero {ι' : Type} [Inhabited ι']
    (Z : RealBundle B F ι) (n : ℕ)
    (τ : RelCoh (ZMod 2) n (Z.sum (RealBundle.trivial B (Fin 1 → ℝ) ι')).TotalSpace
      (zeroComplement (Z.sum (RealBundle.trivial B (Fin 1 → ℝ) ι')))) :
    stiefelWhitney (Z.sum (RealBundle.trivial B (Fin 1 → ℝ) ι')) n τ = 0 := by
  let W := Z.sum (RealBundle.trivial B (Fin 1 → ℝ) ι')
  have hcont : Continuous (fun x : B =>
      (⟨x, ((0 : F), (fun _ : Fin 1 => (1 : ℝ)))⟩ : W.TotalSpace)) := by
    refine continuous_section_mk _ (ContinuousMap.id B)
      (ContinuousMap.const B ((0 : F), (fun _ : Fin 1 => (1 : ℝ)))) ?_
    intro x i j hx
    dsimp only [W]
    simp
  let σ : C(B, W.TotalSpace) :=
    ⟨fun x => ⟨x, ((0 : F), (fun _ : Fin 1 => (1 : ℝ)))⟩, hcont⟩
  have hne : ∀ x, (σ x).2 ≠ 0 := by
    intro x h
    have h2 : (fun _ : Fin 1 => (1 : ℝ)) = 0 := congrArg Prod.snd h
    have := congrFun h2 0
    norm_num at this
  exact stiefelWhitney_eq_zero_of_nowhereZeroSection W σ (fun x => rfl) hne n τ

/-! ## The first Pontryagin class of a clutching presentation is determined by its axioms -/

/-- A **clutching presentation** of a real bundle over `B`: a finite list of rank-`4` real bundles
over `S⁴` pulled back along maps `B → S⁴`, read as their Whitney sum
(`Work.TangentClasses.ClutchPresentation`). -/
abbrev P1Presentation (B : Type) [TopologicalSpace B] : Type _ :=
  ClutchPresentation B

/-- The **rank** of a clutching presentation: every summand is a rank-`4` real bundle, so the
presented bundle has rank `4 * pres.length`.  (A presentation of the tangent bundle of an
`8`-manifold therefore has two summands.) -/
def P1Presentation.Rank {B : Type} [TopologicalSpace B] (pres : P1Presentation B) : ℕ :=
  4 * pres.length

@[simp] theorem P1Presentation.Rank_nil {B : Type} [TopologicalSpace B] :
    P1Presentation.Rank ([] : P1Presentation B) = 0 := rfl

@[simp] theorem P1Presentation.Rank_cons {B : Type} [TopologicalSpace B]
    (p : C(B, S4) × SpinBundle) (P : P1Presentation B) :
    P1Presentation.Rank (p :: P) = P1Presentation.Rank P + 4 := by
  simp [P1Presentation.Rank, List.length_cons, Nat.mul_succ]

/-- The **first Pontryagin class of a presentation**, with a chosen generator `G` of
`H⁴(S⁴;ℤ) ≅ ℤ`. -/
def P1Presentation.p1 (G : H 4 S4) {B : Type} [TopologicalSpace B]
    (P : P1Presentation B) : H 4 B :=
  ClutchPresentation.p1 G P

/-- **Naturality** of the first Pontryagin class of a presentation. -/
theorem p1Presentation_natural (G : H 4 S4) {B B' : Type} [TopologicalSpace B]
    [TopologicalSpace B'] (P : P1Presentation B) (f : C(B', B)) :
    P1Presentation.p1 G (P.map (fun p => (p.1.comp f, p.2))) =
      (HMap f 4).hom (P1Presentation.p1 G P) :=
  ClutchPresentation.p1_comp G P f

/-- **Whitney additivity** for presentations: concatenation adds the classes. -/
theorem p1Presentation_append (G : H 4 S4) {B : Type} [TopologicalSpace B]
    (P Q : P1Presentation B) :
    P1Presentation.p1 G (P ++ Q) = P1Presentation.p1 G P + P1Presentation.p1 G Q :=
  ClutchPresentation.p1_append G P Q

/-- **Stability**: a presentation whose summands are all trivial has vanishing first Pontryagin
class. -/
theorem p1Presentation_of_trivial (G : H 4 S4) {B : Type} [TopologicalSpace B]
    (P : P1Presentation B) (hP : ∀ p ∈ P, p.2 = SpinBundle.trivial) :
    P1Presentation.p1 G P = 0 :=
  ClutchPresentation.p1_of_trivial G P hP

/-- **The first Pontryagin class of a presentation is determined by naturality, Whitney
additivity, and the normalisation on `S⁴`.**  If a class function `Φ` on presentations is natural
under pullback, additive under concatenation, and takes the value `p₁(b) · G` on the bundles over
`S⁴` themselves, then it is `ClutchPresentation.p1`. -/
theorem p1Presentation_unique (G : H 4 S4)
    (Φ : ∀ {B : Type} [TopologicalSpace B], ClutchPresentation B → H 4 B)
    (hnat : ∀ {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] (P : ClutchPresentation B)
      (f : C(B', B)), Φ (P.map (fun p => (p.1.comp f, p.2))) = (HMap f 4).hom (Φ P))
    (hadd : ∀ {B : Type} [TopologicalSpace B] (P Q : ClutchPresentation B),
      Φ (P ++ Q) = Φ P + Φ Q)
    (hnorm : ∀ b : SpinBundle, Φ [(ContinuousMap.id S4, b)] = (b.pontryagin1 : ℤ) • G) :
    ∀ {B : Type} [TopologicalSpace B] (P : ClutchPresentation B),
      Φ P = ClutchPresentation.p1 G P := by
  intro B _ P
  induction P with
  | nil =>
    have h := hadd (B := B) [] []
    simp only [List.nil_append] at h
    have h2 : (0 : H 4 B) = Φ ([] : ClutchPresentation B) := by
      have h3 := congrArg (fun x : H 4 B => x - Φ ([] : ClutchPresentation B)) h
      simpa using h3
    rw [← h2]
    rfl
  | cons p P ih =>
    have hsplit : (p :: P : ClutchPresentation B) = [p] ++ P := rfl
    have hsingle : Φ [(p.1, p.2)] = p1Pulled G p.1 p.2 := by
      have hmap : ([(p.1, p.2)] : ClutchPresentation B)
          = ([(ContinuousMap.id S4, p.2)] : ClutchPresentation S4).map
              (fun q => (q.1.comp p.1, q.2)) := by simp
      rw [hmap, hnat, hnorm p.2]
      rfl
    rw [hsplit, hadd, ih, hsingle, ClutchPresentation.p1_append, ClutchPresentation.p1_singleton]

end

end Work.Thom
