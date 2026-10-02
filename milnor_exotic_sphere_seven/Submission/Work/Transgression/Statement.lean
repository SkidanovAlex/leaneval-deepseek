import Mathlib
import Submission.Work.Transgression.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# SUBPROJECT TRANSGRESSION: the exact statements

This module states, in the workspace's own vocabulary, (a) the general **transgression theorem**
("the Euler class of a bundle over `Sⁿ` given by a two-chart clutching is `± deg(ev ∘ f)` times a
generator"), (b) its rank-`4`, `S⁴` instance (the model of the bundles `clutchBundle a b` of
`Submission/Work/Agree/S4Bundle.lean`), and (c) the **punctured-cohomology input**
`PuncturedCoh`, the single remaining topological computation on which the deliverable

  `Work.Agree.EulerClutch : ∀ a b T, (HMap discProj 4).hom T.eulerClass = ± ((a+b) • tauD)`

is reduced (`Submission/Work/Transgression/Gysin.lean`).

## The statements, in words

* `TwoChartEuler` (general rank `m+1` over `S^{m+1}`): let `Z` be a rank-`(m+1)` real bundle over
  `S^{m+1} = sphTop (m+2)`, trivial over the two caps `capA (m+1)`, `capB (m+1)` of
  `Submission/Work/Cohomology/SphDefs.lean`, whose transition function over the equatorial band
  `band (m+1) ≃ S^m` is the clutching function `f : S^m → GL⁺(m+1)` composed with a direction map
  `d : band → S^m`.  Then the Euler class of **any** Thom class of `Z` is
  `± deg(ev ∘ f)` times **any** generator `G` of `H^{m+1}(S^{m+1};ℤ)`, where `ev` is the evaluation
  at a fixed unit vector (`Work.Transgression.evalVec`) and `deg` is `sphSelfDegree`.

* `TwoChartEuler4` (rank 4 over `S⁴ = OnePoint ℝ⁴`, the model of `clutchBundle`): same statement
  with the two hemispheres `hemi0`, `hemi1` and the direction map `Work.Agree.uDir : S⁴ → S³`, the
  clutching being a continuous `f : S³ → GL(4)`.  The Euler class is `± clutchDegree f` times any
  generator, `clutchDegree` being the degree of `q ↦ f q · 1` in the quaternionic model.

* `PuncturedCoh a b`: `H⁴` of the punctured total space (equivalently the sphere bundle) of
  `clutchBundle a b` is cyclic of order `|a + b|`.  This is the transgression/Mayer–Vietoris
  computation of the sphere bundle `(D⁴ × S³) ∪_{q ↦ q^a · q^b} (D⁴ × S³)`, and it is the exact
  topological input from which the Euler-class statement follows through the Gysin sequence.
-/

namespace Work.Transgression

open Work.TangentClasses

noncomputable section

/-! ## The general transgression theorem -/

/-- **THE TRANSGRESSION THEOREM (general rank, two charts)** — the chapter's main statement,
recorded as a `Prop`.  See the module docstring for the precise reading of the hypotheses. -/
def TwoChartEuler : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m)
    (Z : RealBundle ↥(Work.Cohomology.sphTop (m + 2)) (EuclideanSpace ℝ (Fin (m + 1))) Bool)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1, GLpos (m + 1)))
    (d : C(↥(Work.Cohomology.band (m + 1)),
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)),
    Z.baseSet false = Work.Cohomology.capA (m + 1) →
    Z.baseSet true = Work.Cohomology.capB (m + 1) →
    (∀ x : ↥(Work.Cohomology.band (m + 1)),
      Z.coordChange false true (x : ↥(Work.Cohomology.sphTop (m + 2))) = (f (d x)).1) →
    ∀ (G : Work.Thom.Coh ℤ (m + 1) ↥(Work.Cohomology.sphTop (m + 2))),
      (∀ z : Work.Thom.Coh ℤ (m + 1) ↥(Work.Cohomology.sphTop (m + 2)),
        ∃ c : ℤ, z = c • G) →
      ∀ T : Work.Thom.ThomClass Z (m + 1),
        T.eulerClass = (clutchDegreeN m hm f) • G ∨
        T.eulerClass = -((clutchDegreeN m hm f) • G)

/-! ## The rank-4 instance over `S⁴ = OnePoint ℝ⁴` (the model of `clutchBundle a b`) -/

/-- **THE TRANSGRESSION THEOREM, rank 4 over `S⁴`** — the instance the paper's core theorem needs.
`Z` is a rank-`4` real bundle over `S⁴ = OnePoint ℝ⁴` trivial over the two hemispheres `hemi0`,
`hemi1`, whose transition function over `hemi0 ∩ hemi1 = ℝ⁴ ∖ 0` is the clutching function
`f : S³ → GL(4)` composed with the direction map `uDir : S⁴ → S³`.  Then the Euler class of any Thom
class of `Z` is `± clutchDegree f` times any generator of `H⁴(S⁴;ℤ)`.

(`clutchBundle a b` satisfies the three hypotheses with `f = qTwistGL a b`, see
`Work.Transgression.clutchBundle_clutching`.) -/
def TwoChartEuler4 : Prop :=
  ∀ (Z : RealBundle S4 (EuclideanSpace ℝ (Fin 4)) Bool)
    (f : C(Work.CharacteristicClasses.S3, GLend 4)),
    Z.baseSet false = Work.Agree.hemi0 →
    Z.baseSet true = Work.Agree.hemi1 →
    (∀ p : S4, Z.coordChange false true p = (f (uDirS3 p)).1) →
    ∀ (G : Work.Thom.Coh ℤ 4 S4), (∀ z : Work.Thom.Coh ℤ 4 S4, ∃ c : ℤ, z = c • G) →
      ∀ T : Work.Thom.ThomClass Z 4,
        T.eulerClass = (clutchDegree f) • G ∨ T.eulerClass = -((clutchDegree f) • G)

/-- `clutchBundle a b` has the clutching function `qTwistGL a b` in the sense of
`Work.Transgression.TwoChartEuler4`: its cover is the two hemispheres and its transition from the
second chart to the first is exactly `q ↦ (v ↦ qᵃ v qᵇ)` evaluated at `uDir p`. -/
theorem clutchBundle_clutching (a b : ℤ) :
    (Work.Agree.clutchBundle a b).baseSet false = Work.Agree.hemi0 ∧
    (Work.Agree.clutchBundle a b).baseSet true = Work.Agree.hemi1 ∧
    (∀ p : S4, (Work.Agree.clutchBundle a b).coordChange false true p
      = (qTwistGL a b (uDirS3 p)).1) :=
  ⟨rfl, rfl, fun p => rfl⟩

/-! ## The punctured (sphere bundle) cohomology — the remaining topological input -/

/-- **THE REMAINING TOPOLOGICAL INPUT.**  `H⁴` of the punctured total space of `clutchBundle a b`
(equivalently, of its unit sphere bundle) is cyclic of order `|a + b|`.

This is the transgression (Mayer–Vietoris) computation of the sphere bundle
`S(clutchBundle a b) = (D⁴ × S³) ∪_{S³×S³} (D⁴ × S³)` glued by `(x, w) ↦ (x, xᵃ w xᵇ)`; the
Mayer–Vietoris sequence of the two pieces, together with the computation of the class of the gluing
map on `H³(S³ × S³) = ℤ ⊕ ℤ` as `(a+b) α + β` (`Work.Transgression.clutchDegree_qTwist` is the
`k`-dependence of that class), gives the cokernel `ℤ/(a+b)`. -/
def PuncturedCoh (a b : ℤ) : Prop :=
  Nonempty (↥(Work.Thom.Coh ℤ 4 ↥(Work.Thom.zeroComplement (Work.Agree.clutchBundle a b)))
    ≃ₗ[ℤ] ZMod (Int.natAbs (a + b)))

/-- **The remaining topological input, in cardinality form.**  `H⁴` of the punctured total space
of `clutchBundle a b` has `|a + b|` elements.  This is the *consequence* of `PuncturedCoh` that the
Gysin reduction actually consumes (the reduction `Work.Transgression.PuncturedGysin` only uses the
order of the group), so a proof by Mayer–Vietoris that computes the order of the cokernel of the
connecting map suffices. -/
def PuncturedCohCard (a b : ℤ) : Prop :=
  Nat.card ↥(Work.Thom.Coh ℤ 4 ↥(Work.Thom.zeroComplement (Work.Agree.clutchBundle a b)))
    = Int.natAbs (a + b)

/-! ## The generator of `H⁴(S⁴;ℤ)` -/

/-- **`H⁴(S⁴;ℤ) ≅ ℤ`**, from the computation of the cohomology of the standard sphere
`S⁴ = Metric.sphere (0 : ℝ⁵) 1` (`Work.Cohomology.sphereCohomologyTop`) and the homeomorphism
`Work.Agree.homeoS4Sphere`. -/
def H4S4Iso : Work.Thom.Coh ℤ 4 S4 ≅ ModuleCat.of ℤ ℤ :=
  (Work.Cohomology.cohomologyIso_of_homotopyEquiv Work.Agree.homeoS4Sphere.toHomotopyEquiv 4).some
    ≪≫ (Work.Cohomology.sphereCohomologyTop 4 (by norm_num)).some

/-- **The chosen generator `G` of `H⁴(S⁴;ℤ) ≅ ℤ`**: the class sent to `1` by `H4S4Iso`. -/
def G4 : Work.Thom.Coh ℤ 4 S4 := ModuleCat.Hom.hom H4S4Iso.inv (1 : ℤ)

@[simp] lemma H4S4Iso_G4 : ModuleCat.Hom.hom H4S4Iso.hom G4 = 1 := by
  have h := congrArg ModuleCat.Hom.hom H4S4Iso.inv_hom_id
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  exact LinearMap.congr_fun h 1

/-- Every class of `H⁴(S⁴;ℤ)` is an integral multiple of the chosen generator: `x = φ(x) • G4`. -/
lemma smul_G4 (x : Work.Thom.Coh ℤ 4 S4) :
    x = (ModuleCat.Hom.hom H4S4Iso.hom x) • G4 := by
  have h1 : ModuleCat.Hom.hom H4S4Iso.inv (ModuleCat.Hom.hom H4S4Iso.hom x) = x := by
    have h := congrArg ModuleCat.Hom.hom H4S4Iso.hom_inv_id
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact LinearMap.congr_fun h x
  have h2 : ModuleCat.Hom.hom H4S4Iso.inv (ModuleCat.Hom.hom H4S4Iso.hom x)
      = (ModuleCat.Hom.hom H4S4Iso.hom x) • ModuleCat.Hom.hom H4S4Iso.inv (1 : ℤ) := by
    simpa using map_zsmul (ModuleCat.Hom.hom H4S4Iso.inv)
      (ModuleCat.Hom.hom H4S4Iso.hom x) (1 : ℤ)
  have h3 : ModuleCat.Hom.hom H4S4Iso.hom (ModuleCat.Hom.hom H4S4Iso.inv (1 : ℤ)) = 1 := by
    have h := congrArg ModuleCat.Hom.hom H4S4Iso.inv_hom_id
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact LinearMap.congr_fun h (1 : ℤ)
  rw [← h1, h2, show G4 = ModuleCat.Hom.hom H4S4Iso.inv (1 : ℤ) from rfl, map_zsmul, h3]
  simp

/-! ## The power maps of `S³`, in both models -/

/-- The homeomorphism `S³ = Sp(1) ≅ {x : ℝ⁴ | ‖x‖ = 1}` given by the isometry `ℍ ≅ ℝ⁴`. -/
def sphHom : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ≃ₜ Work.CharacteristicClasses.S3 :=
  Work.CharacteristicClasses.s3Homeo.symm

/-- **The power map `q ↦ qᵐ` on the standard model `S³ ⊆ ℝ⁴`** (of the general transgression
statement `TwoChartEuler`), i.e. the transport of `Work.CharacteristicClasses.s3ZPowCm` along the
isometry `ℍ ≅ ℝ⁴`. -/
def sphPow (m : ℤ) : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  (⟨sphHom.symm, sphHom.symm.continuous⟩ : C(Work.CharacteristicClasses.S3,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)).comp
    ((Work.CharacteristicClasses.s3ZPowCm m).comp ⟨sphHom, sphHom.continuous⟩)

@[simp] lemma sphPow_apply (m : ℤ) (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    sphPow m x = sphHom.symm (Work.CharacteristicClasses.s3ZPowCm m (sphHom x)) := rfl

/-- **The Euler-class statement in generator form**: for every `a b` and every Thom class of
`clutchBundle a b`, the Euler class is `± (a+b)` times the chosen generator `G4`.  This is
`Work.Agree.EulerClutch` before pulling back along `π = discProj`. -/
def EulerClutchGen : Prop :=
  ∀ (a b : ℤ) (T : Work.Thom.ThomClass (Work.Agree.clutchBundle a b) 4),
    T.eulerClass = ((a + b : ℤ)) • G4 ∨ T.eulerClass = -(((a + b : ℤ)) • G4)

end

end Work.Transgression
