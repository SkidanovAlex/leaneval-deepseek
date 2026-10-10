import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotA.Spread
import Submission.Work.MotA.SpreadAux
import Submission.Work.MotA.coheight_eq_one_iff
import Submission.Work.MotA.resEquiv_iff_fractionRing
import Submission.Work.MotA.divCount_rename
import Submission.Work.MotA.awayAlgEquiv_stab
import Submission.Work.MotA.exists_spread_awayAlgEquiv
import Submission.Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv
import Submission.Work.MotV.ratFunc_cancel
import Submission.Work.MotV5.fractionRing_mvPoly_one
import Submission.Work.MotV.SpreadLib
import Submission.Work.MotV5.fractionRing_stab
import Submission.Work.MotV5.class_of_comap_spread
import Submission.Work.MotV5.census_G_alt
import Submission.Work.MotV5.census_F_alt

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false
open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

/-!
# Class transfer for node `SPREAD` (`certN_of_linkCert`)

This file collects the class-level bookkeeping that turns the two censuses
(`Submission/Work/MotV5/census_G.lean`, `census_F.lean`) and the class computation
(`Submission/Work/MotV5/class_of_comap_spread.lean`) into the statement that the horizontal lift
`z` of the distinguished point `L.zP` of the `K`-level link is the *only* prime divisor of `V(G')`
(or `V(F')`) whose residue field class is that of `z`, once one has stabilised to `n = 4 + k`
variables.

The vocabulary is that of `Submission/Work/MotV/Defs.lean`: `ConstantsOnly`, `GeomRuled`,
`LinkCert`, and `Work.MotA.resEquiv_iff_fractionRing` turns `ResEquiv` into an isomorphism of the
fraction fields of the coordinate quotients.
-/

noncomputable section

namespace Work.MotV

variable {𝕜 : Type} [Field 𝕜]

/-! ## §1 Fraction fields of polynomial algebras -/

/-- `FractionRing` is functorial in the coefficient ring of a polynomial algebra. -/
theorem nonempty_fractionRing_mapAlgEquiv {A B : Type} [CommRing A] [CommRing B] [IsDomain A]
    [IsDomain B] [Algebra 𝕜 A] [Algebra 𝕜 B] (σ : Type) (e : A ≃ₐ[𝕜] B) :
    Nonempty (FractionRing (MvPolynomial σ A) ≃ₐ[𝕜] FractionRing (MvPolynomial σ B)) :=
  ⟨IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.mapAlgEquiv σ e)⟩

/-- `F(x₁,…,x_m)(y) = F(x₁,…,x_m,y)`: the `m`-variable rational function field over `RatFunc F` is
the `(m+1)`-variable one over `F`. -/
theorem nonempty_fractionRing_ratFunc (F : Type) [Field F] [Algebra 𝕜 F] (m : ℕ) :
    Nonempty (FractionRing (MvPolynomial (Fin m) (RatFunc F)) ≃ₐ[𝕜]
      FractionRing (MvPolynomial (Fin (m + 1)) F)) :=
  ⟨(Classical.choice (nonempty_fractionRing_mapAlgEquiv (𝕜 := 𝕜) (σ := Fin m)
      (Classical.choice (Work.MotV5.fractionRing_mvPoly_one (𝕜 := 𝕜) (F := F))).symm)).trans
    (Classical.choice (fracMvPoly_fin_add (𝕜 := 𝕜) (F := F) m 1)).symm⟩

/-! ## §2 Constants-only is preserved by isomorphisms -/

/-- `ConstantsOnly` is an isomorphism invariant. -/
theorem ConstantsOnly.of_algEquiv {F F' : Type} [Field F] [Field F'] [Algebra 𝕜 F]
    [Algebra 𝕜 F'] (e : F ≃ₐ[𝕜] F') (h : ConstantsOnly 𝕜 F) : ConstantsOnly 𝕜 F' := by
  intro M _ _ ι x
  obtain ⟨c, hc⟩ := h M (ι.comp e.toAlgHom) (e.symm x)
  exact ⟨c, by simpa using hc⟩

/-- A geometrically ruled field is not constants-only (`ConstantsOnly 𝕜 F` is exactly
`¬ GeomRuled 𝕜 F`). -/
theorem not_constantsOnly_of_geomRuled (F : Type) [Field F] [Algebra 𝕜 F]
    (h : GeomRuled 𝕜 F) : ¬ ConstantsOnly 𝕜 F := by
  rintro hc
  obtain ⟨M, hM, hA, ι, x, hx⟩ := h
  letI := hM
  letI := hA
  obtain ⟨c, hc'⟩ := hc M ι x
  exact hx c hc'

/-- A `K`-algebra isomorphism between `K`-algebras that are also `𝕜`-algebras with scalar towers is
`𝕜`-linear. -/
theorem nonempty_algEquiv_restrictScalars {K F G : Type} [Field K] [Algebra 𝕜 K] [Field F]
    [Algebra K F] [Algebra 𝕜 F] [IsScalarTower 𝕜 K F] [Field G] [Algebra K G] [Algebra 𝕜 G]
    [IsScalarTower 𝕜 K G] (e : F ≃ₐ[K] G) : Nonempty (F ≃ₐ[𝕜] G) :=
  have hc : ∀ c : 𝕜, e (algebraMap 𝕜 F c) = algebraMap 𝕜 G c := fun c => by
    rw [IsScalarTower.algebraMap_apply 𝕜 K F, IsScalarTower.algebraMap_apply 𝕜 K G, e.commutes]
  ⟨AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun c => hc c)⟩

/-! ## §3 The class of a stabilised point -/

/-- **Class transfer under stabilisation.**  From the class `Frac(𝕜[Fin 4] ⧸ p) ≅ RatFunc F₀` of a
height-one prime of `𝔸⁴_𝕜`, the class of the stabilised point `p.map (rename (Fin.castAdd k))` of
`𝔸^{4+k}_𝕜` is `Frac(MvPolynomial (Fin (k+1)) F₀)`: the stabilisation adds `k` rational variables
(`fractionRing_stab`) and the passage from `RatFunc F₀ = F₀(y)` to `F₀` adds one more. -/
theorem class_stab_of_class (k : ℕ) (p : Ideal (MvPolynomial (Fin 4) 𝕜)) [p.IsPrime]
    {F₀ : Type} [Field F₀] [Algebra 𝕜 F₀]
    (h : Nonempty (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ p) ≃ₐ[𝕜] RatFunc F₀)) :
    Nonempty (FractionRing (MvPolynomial (Fin (4 + k)) 𝕜 ⧸
        p.map (MvPolynomial.rename (Fin.castAdd k))) ≃ₐ[𝕜]
      FractionRing (MvPolynomial (Fin (k + 1)) F₀)) := by
  obtain ⟨e1⟩ := Work.MotV5.fractionRing_stab (𝕜 := 𝕜) k p
  obtain ⟨e2⟩ := nonempty_fractionRing_mapAlgEquiv (𝕜 := 𝕜) (σ := Fin k) (Classical.choice h)
  obtain ⟨e3⟩ := nonempty_fractionRing_ratFunc (𝕜 := 𝕜) F₀ k
  exact ⟨e1.trans (e2.trans e3)⟩

/-- The same, with the stabilised point presented by its ideal instead of by `p.map`. -/
theorem class_stab_of_class_map {k : ℕ} (p : Ideal (MvPolynomial (Fin 4) 𝕜)) [p.IsPrime]
    {P : Work.MotA.polySpec 𝕜 (4 + k)}
    (hP : P.asIdeal = p.map (MvPolynomial.rename (Fin.castAdd k)))
    {F₀ : Type} [Field F₀] [Algebra 𝕜 F₀]
    (h : Nonempty (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ p) ≃ₐ[𝕜] RatFunc F₀)) :
    Nonempty (FractionRing (MvPolynomial (Fin (4 + k)) 𝕜 ⧸ P.asIdeal) ≃ₐ[𝕜]
      FractionRing (MvPolynomial (Fin (k + 1)) F₀)) := by
  rw [hP]
  exact class_stab_of_class k p h

/-- **The class of the horizontal lift of `L.zP`.**  The contraction of `L.zP` along the spread map
has, at the level of `𝔸⁴_𝕜`, the same class as `L.zP` over `K`, namely `RatFunc F₁`. -/
theorem class_comap_zP {F₁ F₂ : Type} [Field F₁] [Field F₂] [Algebra (RatFunc 𝕜) F₁]
    [Algebra (RatFunc 𝕜) F₂] [Algebra 𝕜 F₁] [Algebra 𝕜 F₂]
    [IsScalarTower 𝕜 (RatFunc 𝕜) F₁] [IsScalarTower 𝕜 (RatFunc 𝕜) F₂]
    (L : LinkCert (RatFunc 𝕜) F₁ F₂) :
    Nonempty (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸
        Ideal.comap (Work.MotA.spreadMap 𝕜 3) L.zP.asIdeal) ≃ₐ[𝕜] RatFunc F₁) := by
  haveI : L.zP.asIdeal.IsPrime := L.zP.isPrime
  obtain ⟨e1⟩ := (Work.MotV5.class_of_comap_spread (𝕜 := 𝕜) L.zP.asIdeal).2
  obtain ⟨e2⟩ := nonempty_algEquiv_restrictScalars (𝕜 := 𝕜) (K := RatFunc 𝕜)
    (Classical.choice L.zP_res)
  exact ⟨e1.trans e2⟩

/-! ## §4 The class separation -/

/-- **The separator (junk case).**  An isomorphism of `m`-variable rational function fields over a
constants-only field and over a field that is *not* constants-only is impossible: `CAN`
(`Submission/Work/MotV5/fracMvPoly_cancel.lean`) would produce an isomorphism of the base fields,
which would transfer constants-only-ness. -/
theorem not_nonempty_fracMvPoly_algEquiv_of_not_constantsOnly {F₁ F₀ : Type} [Field F₁] [Field F₀]
    [Algebra 𝕜 F₁] [Algebra 𝕜 F₀] {m : ℕ} (h₁ : ConstantsOnly 𝕜 F₁)
    (h₀ : ¬ ConstantsOnly 𝕜 F₀) :
    ¬ Nonempty (FractionRing (MvPolynomial (Fin m) F₀) ≃ₐ[𝕜]
        FractionRing (MvPolynomial (Fin m) F₁)) := by
  rintro ⟨e⟩
  exact h₀ (ConstantsOnly.of_algEquiv
    (Classical.choice (ratFunc_cancel h₁ m e.symm)) h₁)

/-- **The separator (`F₂` case).**  An isomorphism of `m`-variable rational function fields over two
fields that are not isomorphic is impossible, by `CAN`
(`Submission/Work/MotV5/fracMvPoly_cancel.lean`). -/
theorem not_nonempty_fracMvPoly_algEquiv_of_isEmpty {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Algebra 𝕜 F₁] [Algebra 𝕜 F₂] {m : ℕ} (h₁ : ConstantsOnly 𝕜 F₁)
    (hR : IsEmpty (F₁ ≃ₐ[𝕜] F₂)) :
    ¬ Nonempty (FractionRing (MvPolynomial (Fin m) F₂) ≃ₐ[𝕜]
        FractionRing (MvPolynomial (Fin m) F₁)) := by
  rintro ⟨e⟩
  exact hR.false (Classical.choice (ratFunc_cancel h₁ m e.symm))

/-- **Separation from a junk-class point.**  A point `x` of `𝔸^{4+k}_𝕜` whose class is
`Frac(MvPolynomial (Fin (k+1)) F₀)` with `F₀` not constants-only cannot have the class of the
distinguished point `z` (whose class is `Frac(MvPolynomial (Fin (k+1)) F₁)`, `F₁` constants-only). -/
theorem not_resEquiv_of_class_stab {k : ℕ} {F₁ : Type} [Field F₁] [Algebra 𝕜 F₁]
    (hCO : ConstantsOnly 𝕜 F₁) {F₀ : Type} [Field F₀] [Algebra 𝕜 F₀]
    (h₀ : ¬ ConstantsOnly 𝕜 F₀) {x z : Work.MotA.polySpec 𝕜 (4 + k)}
    (hz : Nonempty (FractionRing (MvPolynomial (Fin (4 + k)) 𝕜 ⧸ z.asIdeal) ≃ₐ[𝕜]
      FractionRing (MvPolynomial (Fin (k + 1)) F₁)))
    (hx : Nonempty (FractionRing (MvPolynomial (Fin (4 + k)) 𝕜 ⧸ x.asIdeal) ≃ₐ[𝕜]
      FractionRing (MvPolynomial (Fin (k + 1)) F₀))) :
    ¬ ResEquiv 𝕜 x z := by
  intro hres
  obtain ⟨e1⟩ := hx
  obtain ⟨e2⟩ := hz
  obtain ⟨e3⟩ := (Work.MotA.resEquiv_iff_fractionRing 𝕜 (4 + k) (4 + k) x z).mp hres
  exact not_nonempty_fracMvPoly_algEquiv_of_not_constantsOnly (𝕜 := 𝕜) (m := k + 1) hCO h₀
    ⟨e1.symm.trans (e3.trans e2)⟩

/-- **Separation from an `F₂`-class point.** -/
theorem not_resEquiv_of_class_stab_F₂ {k : ℕ} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Algebra 𝕜 F₁] [Algebra 𝕜 F₂] (hCO : ConstantsOnly 𝕜 F₁) (hR : IsEmpty (F₁ ≃ₐ[𝕜] F₂))
    {x z : Work.MotA.polySpec 𝕜 (4 + k)}
    (hz : Nonempty (FractionRing (MvPolynomial (Fin (4 + k)) 𝕜 ⧸ z.asIdeal) ≃ₐ[𝕜]
      FractionRing (MvPolynomial (Fin (k + 1)) F₁)))
    (hx : Nonempty (FractionRing (MvPolynomial (Fin (4 + k)) 𝕜 ⧸ x.asIdeal) ≃ₐ[𝕜]
      FractionRing (MvPolynomial (Fin (k + 1)) F₂))) :
    ¬ ResEquiv 𝕜 x z := by
  intro hres
  obtain ⟨e1⟩ := hx
  obtain ⟨e2⟩ := hz
  obtain ⟨e3⟩ := (Work.MotA.resEquiv_iff_fractionRing 𝕜 (4 + k) (4 + k) x z).mp hres
  exact not_nonempty_fracMvPoly_algEquiv_of_isEmpty (𝕜 := 𝕜) (m := k + 1) hCO hR
    ⟨e1.symm.trans (e3.trans e2)⟩

end Work.MotV
