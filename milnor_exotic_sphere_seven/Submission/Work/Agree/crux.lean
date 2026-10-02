import Mathlib
import Submission.Work.Agree.Basic
import Submission.Work.Agree.VkCharts
import Submission.Work.Thom.chernClass_BundleIso
import Submission.Work.Thom.chernClass_homeo
import Submission.Work.Thom.chernClass_comap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-! # AREA AGREE: the exact remaining content of `agreeAll`, split into two halves

`Submission/Work/Agree/Basic.lean` reduces the target `Work.Drive.AgreeAll` to
`Work.Agree.DiscRestriction`: the restriction of the *defined* class
`p₁(TX) = Work.Thom.p1Tangent'` to the disc bundle `D(ξ) = Vk (-2)` is `± 6 · τ`.

By `cappedRestriction_p1Tangent'` that restriction is `- c₂` of the pulled-back complexified
tangent bundle of `X`, so `DiscRestriction` is the conjunction of two independent statements:

* **`GeomSplitting`** — the *geometric/plumbing* half: the pulled-back complexified tangent bundle of
  `X` has the same second Chern class as the pullback, along the bundle projection `π : D(ξ) → S⁴`,
  of the complexified rank-`4` real bundle `ξ = L²R⁻¹`.  This is the chain
  *model transfer* (`Work.Agree.modelTransfer`) → *plumbing* (`Work.Agree.plumb`) →
  *tangent restriction* (`Work.Agree.tangentRestriction`) → *splitting* of the tangent bundle of the
  total space of a vector bundle (`T D(ξ) = π^*(TS⁴ ⊕ ξ)`, the block-triangular Jacobian of the
  glueing and the gauge that makes it block-diagonal) → *stability* (`TS⁴ ⊕ ε ≅ ε⁵`, so `TS⁴`
  contributes nothing).

* **`Crux`** — the *characteristic-class* half, over `S⁴` itself: for every `a b : ℤ` the second
  Chern class of the complexification of `L^a R^b` is `± 2(a - b)` times any generator of
  `H⁴(S⁴;ℤ)` (equivalently: the Chern-defined `p₁ = -c₂` agrees with the characteristic-classes
  chapter's `p₁(L^aR^b) = 2(a-b)`).  This is the classical identification *"`c₂` of a quaternionic
  line bundle over `S⁴` is the degree of its clutching function"* (the Bott invariant), which the
  chapter `Submission/Work/CharacteristicClasses/` uses as *definitional* input (`chern2` *is* the
  degree) and which is not yet derived from `Work.Thom.chernClass`.

The two halves are independent: `GeomSplitting` is pure calculus/plumbing (the honest bookkeeping of
`Work.Thom.chernClass` under bundle isomorphisms and pullbacks), while `Crux` is the new
characteristic-classes chapter.

The main theorem of this file, `agreeAll_of_crux_geom`, assembles them:

    Work.Drive.AgreeAll  ⟸  Crux ∧ GeomSplitting.
-/

open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## The characteristic-class crux over `S⁴` -/

/-- **THE CHARACTERISTIC-CLASS CRUX.**  For all `a b : ℤ` and every generator `G` of
`H⁴(S⁴;ℤ)` normalised by `π^* G = τ` (`π = discProj` the bundle projection of the disc bundle,
`τ = Work.Milnor.tauD` the chapter's generator of `H⁴(D(ξ);ℤ) ≅ ℤ`), the second Chern class of the
complexification of the rank-`4` real bundle `L^a R^b = clutchBundle a b` is `± 2(a-b) · G`.

Equivalently (global signs being immaterial): the Chern-defined first Pontryagin class
`- c₂(E ⊗_ℝ ℂ)` of `L^a R^b` agrees with the characteristic-classes chapter's
`p₁(L^aR^b) = 2(a-b)`, i.e. with `2 · (c₂ L^a + c₂ R^b)`, the classical "Bott invariant" statement
for quaternionic line bundles over `S⁴`.

The extreme case `(a,b) = (1,1)` is `TS⁴ = L¹R¹`, which is stably trivial, so `c₂ = 0 = 2(1-1)`;
`(a,b) = (0,0)` is the trivial bundle. -/
def Crux : Prop :=
  ∀ (a b : ℤ) (G : H 4 S4),
    (HMap discProj 4).hom G = Work.Milnor.tauD →
    (Work.Thom.chernClass 4 2 (Work.Thom.complexificationCore (clutchBundle a b))
        = (2 * (a - b)) • G ∨
     Work.Thom.chernClass 4 2 (Work.Thom.complexificationCore (clutchBundle a b))
        = -((2 * (a - b)) • G))

/-- `c₂` of the complexification of Milnor's bundle `ξ = L²R⁻¹`, as a class over `S⁴`. -/
def xiC2 : H 4 S4 :=
  Work.Thom.chernClass 4 2 (Work.Thom.complexificationCore (clutchBundle 2 (-1)))

/-- The crux at Milnor's bundle `ξ = L²R⁻¹`: `c₂(ξ ⊗_ℝ ℂ) = ± 6 · G`. -/
theorem crux_xi (h : Crux) (G : H 4 S4) (hG : (HMap discProj 4).hom G = Work.Milnor.tauD) :
    xiC2 = (6 : ℤ) • G ∨ xiC2 = -((6 : ℤ) • G) := by
  have h1 := h 2 (-1) G hG
  rw [show (2 * ((2 : ℤ) - (-1))) = 6 from by norm_num] at h1
  exact h1

/-- The crux in the *restricted* form used by `DiscRestriction`: the pullback of `c₂(ξ ⊗ ℂ)` along
the bundle projection of the disc bundle is `± 6 τ`. -/
theorem crux_restriction (h : Crux) :
    (HMap discProj 4).hom xiC2 = (6 : ℤ) • Work.Milnor.tauD ∨
    (HMap discProj 4).hom xiC2 = -((6 : ℤ) • Work.Milnor.tauD) := by
  have hG : (HMap discProj 4).hom discTangentSplitting.G = Work.Milnor.tauD :=
    discTangentSplitting_G_pullback
  rcases crux_xi h discTangentSplitting.G hG with h1 | h1
  · left
    rw [h1, map_zsmul, hG]
  · right
    rw [h1, map_neg, map_zsmul, hG]

/-! ## The geometric/plumbing half -/

/-- The second Chern class of the pulled-back complexified tangent bundle of `X = D(ξ) ∪_F D⁸`. -/
def restrictedC2 (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8)
    (hF : Work.Milnor.IsCappingDiffeo F) : H 4 (Submission.Milnor.Vk (-2)) :=
  letI := Work.Milnor.cappedChartedSpace (Work.Milnor.cappedDatum F hF)
  letI : IsManifold Work.Milnor.mE8 1
      (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) :=
    (Work.Milnor.capped_isManifold (Work.Milnor.cappedDatum F hF)).of_le (by simp)
  letI : CompactSpace (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) :=
    Work.Milnor.isCompact_capped F hF
  Work.Thom.chernClass (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8))) 2
    (Work.Thom.bundleComap
      (Work.Thom.complexifiedTangentBundleFinite 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
        (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
      (incl F hF))

/-- **THE GEOMETRIC/PLUMBING HALF OF `DiscRestriction`.**  The second Chern class of the pullback to
the disc bundle of the canonical complexified tangent bundle presentation of `X = D(ξ) ∪_F D⁸` is the
pullback along the bundle projection `π : D(ξ) → S⁴` of the second Chern class of `ξ ⊗_ℝ ℂ`.

This is the whole geometric content of `DiscRestriction` *minus* the classical Bott invariant
`Crux`: it is the chain model transfer + plumbing + tangent restriction + the splitting
`T D(ξ) = π^*(TS⁴ ⊕ ξ)` + stability of `TS⁴`. -/
def GeomSplitting : Prop :=
  ∀ (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8) (hF : Work.Milnor.IsCappingDiffeo F),
    restrictedC2 F hF = (HMap discProj 4).hom xiC2 ∨
    restrictedC2 F hF = -((HMap discProj 4).hom xiC2)

/-! ## THE TRANSGRESSION BRICK: the Euler class of a clutched bundle is the degree -/

/-- **THE TRANSGRESSION BRICK** (the primitive missing chapter; the project lead's item (i)).

For the two-chart rank-`4` real bundle `clutchBundle a b` over `S⁴ = D₊ ∪ D₋` (clutching
`v ↦ q^a · v · q^b` on the overlap, `q` the unit direction), the Euler class of **any** Thom class
`T` of it — `e = z^*(τ)`, `Work.Thom.ThomClass.eulerClass` — pulls back to `± (a+b) · τ` along the
bundle projection of the disc bundle.

Equivalently: the Euler class of a rank-`4` real bundle over `S⁴` given by a two-chart clutching
`f : S³ → SO(4)` is `± deg(ev₁ ∘ f)` times a generator, where `ev₁` evaluates at the fixed vector
`1 ∈ ℍ`.  Here `ev₁ ∘ f = q ↦ q^a · 1 · q^b = q^{a+b}`, whose degree is `a + b`
(`Work.CharacteristicClasses.SpinBundle.chern2_zPowCm`).

Consistency: `(a,b) = (1,1)` is `TS⁴` and gives `e = 2 = χ(S⁴)`; `(a,b) = (2,-1)` is Milnor's `ξ`
and gives `e = 1` (`Submission/NOTES.md` §9.1).

This is the input of the Bott normalisation `BottHopf` (route (i) → (ii) of the lead's plan: a
quaternionic line `L^a = clutchBundle a 0` has `L^a ⊗_ℝ ℂ ≅ E ⊕ Ē` with `c₂(E) = e(L^a)` the top
Chern class `chernClass_succ_top'`, and the degree-`2` Whitney formula gives
`c₂(L^a ⊗_ℝ ℂ) = 2 c₂(E)`), and of the general `Crux` (together with additivity in the clutching
class). -/
def EulerClutch : Prop :=
  ∀ (a b : ℤ) (T : Work.Thom.ThomClass (clutchBundle a b) 4),
    (HMap discProj 4).hom T.eulerClass = (a + b) • Work.Milnor.tauD ∨
    (HMap discProj 4).hom T.eulerClass = -((a + b) • Work.Milnor.tauD)

/-! ## The Bott normalisation: the quaternionic line bundles `L^a = clutchBundle a 0` -/

/-- **THE BOTT NORMALISATION** (the essential sub-case of `Crux`, strictly weaker than it): for the
quaternionic line bundles `L^a = clutchBundle a 0` over `S⁴` (clutching `v ↦ q^a v`) the
Chern-defined `c₂` of the complexification is `± 2a` times the generator.  Equivalently
`p₁(L^a) = -c₂(L^a ⊗_ℝ ℂ) = ∓ 2a`, i.e. the characteristic-classes chapter's
`pontryagin1_ofQuaternionicLine : p₁(L^f) = 2 · chern2 f` evaluated at `f = q ↦ q^a`
(`chern2_zPowCm : chern2 (q ↦ q^a) = a`).

This is the *normalisation* of the classical Bott invariant; the general `Crux` follows from it
together with additivity of the Chern-defined `p₁` in the clutching class (the degree-`2` Whitney
formula), since `L^aR^b` and `L^{a} ⊕ L^{-b}`-type sums have the same stable class.

It is stated with the same `±` as `Crux`, and is implied by it (`bottHopf_of_crux`). -/
def BottHopf : Prop :=
  ∀ (a : ℤ) (G : H 4 S4),
    (HMap discProj 4).hom G = Work.Milnor.tauD →
    (Work.Thom.chernClass 4 2 (Work.Thom.complexificationCore (clutchBundle a 0))
        = (2 * a) • G ∨
     Work.Thom.chernClass 4 2 (Work.Thom.complexificationCore (clutchBundle a 0))
        = -((2 * a) • G))

/-- The general crux implies the Bott normalisation. -/
theorem bottHopf_of_crux (h : Crux) : BottHopf := by
  intro a G hG
  have h1 := h a 0 G hG
  rwa [show (2 * (a - 0)) = 2 * a from by ring] at h1

/-! ## The `(a,b)`-shift: route (iii) is not needed -/

/-- **The `(a,b)`-shift isomorphism.**  The complexification of `L^a R^b` is isomorphic to the
complexification of `L^{a-b}`: on `ℍ ⊗_ℝ ℂ` the transition `L_{q^a}R_{q^b}` and the transition
`L_{q^{a-b}}` differ by the *point-dependent* factor `(L_qR_q)^{-b}`, whose oscillation at the two
chart centres is a gauge coboundary, so the two *complex* bundles are isomorphic (the
complexification is insensitive to the `R`-twist except through the shift `a ↦ a - b`; the *real*
bundles `L^aR^b` and `L^{a-b}` are genuinely non-isomorphic, e.g. `(1,1)` vs `(0,0)`).

This is the bundle-level form of `p₁(L^aR^b) = 2(a-b)` (`Work.CharacteristicClasses.pontyagin1_laRb`). -/
def ComplexificationShift : Prop :=
  ∀ (a b : ℤ), Nonempty (Work.Thom.BundleIso
    (Work.Thom.complexificationCore (clutchBundle a b))
    (Work.Thom.complexificationCore (clutchBundle (a - b) 0)))

/-- **The general crux follows from the Bott normalisation and the shift isomorphism**, by
isomorphism-invariance of the Chern classes (`Work.Thom.chernClass_BundleIso`).  So the pinch-map /
Mayer–Vietoris additivity in the clutching class (route (iii) of the plan) is *not* needed: the
whole of AGREE reduces to `EulerClutch` (transgression), `BottHopf`, `ComplexificationShift` and the
degree-`2` Whitney formula. -/
theorem crux_of_bottHopf_shift (hb : BottHopf) (hs : ComplexificationShift) : Crux := by
  intro a b G hG
  obtain ⟨e⟩ := hs a b
  have h1 := Work.Thom.chernClass_BundleIso (j := 2)
    (Work.Thom.complexificationCore (clutchBundle a b))
    (Work.Thom.complexificationCore (clutchBundle (a - b) 0)) e
  rcases hb (a - b) G hG with h | h
  · left
    rw [h1, h]
  · right
    rw [h1, h]

/-! ## Geometry B: the splitting of the tangent bundle of the disc bundle -/

/-- **GEOMETRY B.**  The tangent bundle of the total space `D(ξ) = Vk (-2)` of Milnor's rank-`4`
real bundle `ξ = L²R⁻¹`, in the two-chart presentation `vkTangent` along the cover `vkCover`
(charts at the two distinguished points), is isomorphic to the pullback along the bundle projection
`π = discProj` of the Whitney sum `TS⁴ ⊕ ξ` of the two-chart descriptions of the tangent bundle of
`S⁴` (`TS⁴ = L¹R¹ = clutchBundle 1 1`) and of `ξ`.

Mathematically this is the standard splitting `T D(ξ) ≅ π^*(TS⁴ ⊕ ξ)` for the total space of a
vector bundle: the Jacobian of the glueing map `vMap (-2)` is block triangular
`[[d invBase, 0], [B, vTwist 2]]`, and the gauge `[[1, 0], [B (d invBase)^{-1}, 1]]` on the second
chart (the identity on the first) makes it block diagonal; the diagonal blocks are the clutching
functions of `TS⁴` and of `ξ`. -/
def GeometryB : Prop :=
  ∀ (h : ∀ x : Vk, ∃ i : Fin 2,
      x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i)),
    Nonempty (Work.Thom.BundleIso (vkTangent h)
      (Work.Thom.bundleComap
        (Work.TangentClasses.RealBundle.sum (clutchBundle 1 1) (clutchBundle 2 (-1)))
        discProj))

/-! ## Assembly -/

/-- **The two halves imply `DiscRestriction`.** -/
theorem discRestriction_of_crux_geom (hc : Crux) (hg : GeomSplitting) : DiscRestriction := by
  intro F hF
  have hcr := crux_restriction hc
  have key : -((HMap discProj 4).hom xiC2) = (6 : ℤ) • Work.Milnor.tauD ∨
      -((HMap discProj 4).hom xiC2) = -((6 : ℤ) • Work.Milnor.tauD) := by
    rcases hcr with h | h
    · right; rw [h]
    · left; rw [h, neg_neg]
  rw [cappedRestriction_p1Tangent' F hF]
  change -restrictedC2 F hF = (6 : ℤ) • Work.Milnor.tauD ∨
      -restrictedC2 F hF = -((6 : ℤ) • Work.Milnor.tauD)
  rcases hg F hF with h | h
  · have h2 : -restrictedC2 F hF = -((HMap discProj 4).hom xiC2) := by rw [h]
    rw [h2]; exact key
  · have h2 : -restrictedC2 F hF = (HMap discProj 4).hom xiC2 := by rw [h, neg_neg]
    rw [h2]; exact hcr

/-- **THE ASSEMBLY**: the two halves of the remaining content prove the target. -/
theorem agreeAll_of_crux_geom (hc : Crux) (hg : GeomSplitting) : Work.Drive.AgreeAll :=
  agreeAll_of_discRestriction (discRestriction_of_crux_geom hc hg)

end

end Work.Agree
