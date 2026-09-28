import Mathlib
import Submission.Work.Cohomology.DiskPairBasic
import Submission.Work.Cohomology.HomologyPairSequence

set_option synthInstance.maxHeartbeats 400000

/-!
# The pair `(S³ × D⁴, S³ × S³)`

Notation for the pair whose relative homology is computed in
`Submission/Work/Cohomology/sphere3DiscPairHomology.lean`:

* `Sph3T` — the standard unit sphere `S³ = {x : ℝ⁴ | ‖x‖ = 1}`;
* `Disc4T` — the closed unit ball `D⁴`;
* `PairXT = S³ × D⁴` — the total space;
* `PairAT = S³ × S³ ⊆ S³ × D⁴` — the sphere bundle;
* the projections `pj1X`, `pj1A`, `pj2A` and the inclusion `inclA`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.Cohomology

noncomputable section

/-- The standard `3`-sphere `S³ = {x : ℝ⁴ | ‖x‖ = 1}`. -/
abbrev Sph3T : TopCat := TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

/-- The closed unit ball `D⁴ ⊆ ℝ⁴`. -/
abbrev Disc4T : TopCat := diskUnit 4

/-- The total space `S³ × D⁴` of the trivial `D⁴`-bundle over `S³`. -/
abbrev PairXT : TopCat := TopCat.of (↥Sph3T × ↥Disc4T)

/-- The sphere bundle `S³ × S³ = S³ × ∂D⁴ ⊆ S³ × D⁴`. -/
abbrev PairAT : Set ↥PairXT := {p : ↥Sph3T × ↥Disc4T | p.2 ∈ sphereInUnit 4}

/-- The projection `S³ × D⁴ ⟶ S³` onto the first factor. -/
def pj1X : PairXT ⟶ Sph3T := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- The inclusion `S³ × S³ ⟶ S³ × D⁴`. -/
def inclA : TopCat.of PairAT ⟶ PairXT :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The projection `S³ × S³ ⟶ S³` onto the first factor. -/
def pj1A : TopCat.of PairAT ⟶ Sph3T :=
  TopCat.ofHom ⟨fun p => p.1.1, continuous_fst.comp continuous_subtype_val⟩

/-- The projection `S³ × S³ ⟶ S³ = ∂D⁴` onto the second factor. -/
def pj2A : TopCat.of PairAT ⟶ TopCat.of (sphereInUnit 4) :=
  TopCat.ofHom ⟨fun p => ⟨p.1.2, p.2⟩,
    Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) (fun p => p.2)⟩

@[simp] theorem pj1X_apply (p : ↥PairXT) : pj1X p = p.1 := rfl
@[simp] theorem pj1A_apply (p : ↥PairAT) : pj1A p = p.1.1 := rfl
@[simp] theorem pj2A_apply (p : ↥PairAT) : (pj2A p : ↥Disc4T) = p.1.2 := rfl
@[simp] theorem inclA_apply (p : ↥PairAT) : inclA p = p.1 := rfl

/-- The first projection of the sphere bundle is the composite of the inclusion and the projection
of the total space. -/
theorem pj1A_eq_incl_pj1X : pj1A = inclA ≫ pj1X := by
  apply TopCat.hom_ext
  ext p
  rfl

end

end Work.Cohomology

/-!
## Intended routes for the three delegated lemmas

`pjPairInjectiveThree` (the pair of the two projections of `PairAT = S³ × S³` is injective on
`H₃`): transport along the homeomorphism `PairAT ≅ PSph 3 3 = S³ × S³` to the model, where the
statement is that `biprod.lift (H₃ proj₁) (H₃ proj₂)` is injective.  For the model: since
`proj_iY = inclY ≫ proj_i`, we have
`biprod.lift (H proj₁Y) (H proj₂Y) = H₃(inclY) ≫ biprod.lift (H proj₁) (H proj₂)`.
`biprod.lift (H proj₁Y) (H proj₂Y)` is injective by `Work.Cohomology.proj_pair_injective 3 3 3`
(the punctured product `Yset 3 3`), and `H₃(inclY)` is an isomorphism: by
`Work.Cohomology.isIso_mvRightX_YV_low 3 3 2` the Mayer–Vietoris map
`H₃(Yset) ⊞ H₃(Vset) → H₃(PSph 3 3)` is an isomorphism, and `H₃(Vset 3 3) = 0` since `Vset` is
contractible (`Work.Cohomology.contractible_Vset`, `Work.Cohomology.homologyContractible`), so
`biprod.inl ≫ mvRightX = H₃(inclY)` is an isomorphism.  Hence the model statement, and transport
(injectivity is preserved by composing on the left with an isomorphism).

`inclAThreeSurjective` (`H₃(inclA)` is onto): `inclA ≫ pj1X = pj1A` and `H₃(pj1X)` is an
isomorphism (projection `S³ × D⁴ → S³` is a homotopy equivalence, `D⁴` contractible:
`Work.Cohomology.homotopyEquiv_prod_fst`), so it suffices that `H₃(pj1A)` is onto; this holds
because `pj1A` has the section `x ↦ (x, y₀)`.

`inclAThreeKerIso` (`ker H₃(inclA) ≅ ℤ`): let `ψ := biprod.lift (H₃ pj1A) (H₃ pj2A)`, injective by
the crux above.  The section `s₂ : y ↦ (x₀, y)` of `pj2A` gives `H₃(s₂) ≫ H₃(pj2A) = id`, and
`s₂ ≫ inclA` factors through the contractible disc `D⁴`, so `H₃(s₂ ≫ inclA) = 0`; hence
`H₃(s₂)(H₃ S³) ⊆ ker H₃(inclA)` and `H₃(pj2A)` is onto that kernel.  It is also injective there:
if `x ∈ ker H₃(inclA)` and `H₃(pj2A) x = 0` then `H₃(pj1A) x = H₃(pj1X)(H₃(inclA) x) = 0`, so
`ψ x = 0` and `x = 0`.  So `ker H₃(inclA) ≅ H₃(S³) ≅ ℤ` (`Work.Cohomology.sphereHomologyTop`).
-/
