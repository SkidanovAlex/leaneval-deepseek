import Mathlib
import Submission.Work.StemsB.CubePairHomology
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.StemsB.SphLoopRelPair
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.Stems.HurewiczMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative Hurewicz map

Area **RATHUREWICZ** (`Submission/Work/RatHurewicz/`).  The relative Hurewicz homomorphism of a pair
`(X,A)` is

`π_{n+1}(X,A,x₀) ⟶ H_{n+1}(X,A;ℤ)`,   `[f] ↦ f_*[I^{n+1}, ∂I^{n+1}]`,

the push-forward of the relative fundamental class of the cube along a representative of the class.
This module builds it by hand:

* `cubeTop n`, `cubeBdrySet n` — the cube `Iⁿ` and its boundary `∂Iⁿ`;
* `relCubeGen n` — the relative fundamental class of the cube, a generator of
  `H_{n+1}(I^{n+1},∂I^{n+1};ℤ) ≅ ℤ`, obtained from the relative Künneth computation of the cube pair
  (`Work.StemsB.cubePair_iso`, through the `PUnit`-parametrised model of the area STEMS-B) and the
  generator `1` of `H₀(pt;ℤ) ≅ ℤ`;
* `relHurewiczClass n g hg` — the class of a *map of pairs* `g : (I^{n+1},∂I^{n+1}) → (X,A)`;
* `cubeToPair n i a₀ p` — the map of pairs attached to a based cube in the homotopy fibre
  `homotopyFibre i a₀`, i.e. to a relative homotopy class of the pair `(X,A)`.

The properties that turn this into the relative Hurewicz *map on homotopy groups* — invariance under
homotopies of pairs (`relHurewiczClass_eq_of_homotopic`), its compatibility with the connecting
homomorphism of the pair (`relHurewiczClass_boundary`) and the descent to `RelHomotopyGroup` — are
delegated and live in separate modules of this directory.

## Conventions

A point of `homotopyFibre i a₀` is a pair `(a,γ)` with `γ` a path in `X` from `i a₀` to `i a`
(`Work.RatHurewicz.homotopyFibre`).  A based cube `p : Ω^ (Fin n) (homotopyFibre i a₀) _` is
therefore the same data as a map `(I^{n+1}, ∂I^{n+1}) → (X, A)` whose first face is the constant path
at `i a₀` and whose second face lands in `A` — the classical model of `π_{n+1}(X,A,x₀)`.  The map
`cubeToPair` performs this conversion: for `z : I^{n+1}`,

`cubeToPair n i a₀ p z = γ_{z|_n}(z (last n))`,

where `z|_n = fun j : Fin n ↦ z j.castSucc`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology Topology.Homotopy unitInterval

namespace Work.RatHurewicz

noncomputable section

/-! ## The cube pair `(Iⁿ, ∂Iⁿ)` -/

/-- The cube `Iⁿ` (`I = [0,1]`), as a topological space. -/
abbrev cubeTop (n : ℕ) : TopCat := TopCat.of (Fin n → unitInterval)

/-- The boundary `∂Iⁿ ⊆ Iⁿ`, i.e. the set of points with some coordinate equal to `0` or `1`. -/
abbrev cubeBdrySet (n : ℕ) : Set (cubeTop n) := Cube.boundary (Fin n)

/-- The homeomorphism `Iⁿ × pt ≃ₜ Iⁿ` forgetting the (unique) point of the parameter space.  It
carries `∂Iⁿ × pt` onto `∂Iⁿ`. -/
def cubePUnitHomeo (n : ℕ) : (Work.StemsB.CubeP PUnit n) ≃ₜ (Fin n → unitInterval) where
  toFun p := p.1
  invFun v := (v, ⟨⟩)
  left_inv p := by
    obtain ⟨v, u⟩ := p
    cases u
    rfl
  right_inv v := rfl
  continuous_toFun := continuous_fst
  continuous_invFun := continuous_id.prodMk continuous_const

/-- The homeomorphism `Iⁿ × pt ≃ₜ Iⁿ` matches the two boundaries. -/
theorem cubePUnitHomeo_mem (n : ℕ) (p : Work.StemsB.CubeP PUnit n) :
    p ∈ Work.StemsB.cubeBdryK PUnit n ↔ cubePUnitHomeo n p ∈ cubeBdrySet n :=
  Iff.rfl

/-! ## The relative fundamental class of the cube -/

/-- **The zeroth singular homology of a point is `ℤ`** (through Mathlib's augmentation
`TopCat.singularHomology₀ε`, an isomorphism for every path-connected space). -/
theorem h0PUnit_iso :
    Nonempty ((Work.Cohomology.singularChains ℤ (TopCat.of PUnit)).homology 0 ≅
      ModuleCat.of ℤ ℤ) := by
  haveI hne : Nonempty (ZerothHomotopy (TopCat.of PUnit)) :=
    ⟨ZerothHomotopy.mk PUnit.unit⟩
  haveI : Subsingleton (ZerothHomotopy (TopCat.of PUnit)) :=
    ⟨fun a b => Quotient.inductionOn₂ a b (fun x y => by rw [Subsingleton.elim x y])⟩
  haveI huniq : Unique (ZerothHomotopy (TopCat.of PUnit)) :=
    { default := Classical.choice hne
      uniq := fun a => Subsingleton.elim a _ }
  refine ⟨TopCat.singularHomology₀Iso (TopCat.of PUnit) (ModuleCat.of ℤ ℤ) ≪≫ ?_⟩
  exact coproductUniqueIso (fun _ : ZerothHomotopy (TopCat.of PUnit) => ModuleCat.of ℤ ℤ)

/-- **The relative homology `H_{n+1}(I^{n+1},∂I^{n+1};ℤ)` is `ℤ`.**  Composed of the isomorphism of
pairs induced by `Iⁿ × pt ≃ₜ Iⁿ`, the relative Künneth computation of the cube pair
(`Work.StemsB.cubePair_iso` in degree `0`) and `H₀(pt) ≅ ℤ`. -/
def relCubeGenIso (n : ℕ) :
    ((Work.Cohomology.relChains (cubeTop (n+1)) (cubeBdrySet (n+1))).homology (n+1)) ≅
      ModuleCat.of ℤ ℤ :=
  (Classical.choice (Work.StemsB.nonempty_relChains_homology_iso_of_homeomorph
      (X := Work.StemsB.CubeSpace (Y := PUnit) (n+1)) (Y := cubeTop (n+1))
      (cubePUnitHomeo (n+1)) (Work.StemsB.cubeBdryK PUnit (n+1)) (cubeBdrySet (n+1))
      (cubePUnitHomeo_mem (n+1)) (n+1))).symm
    ≪≫ eqToIso (congrArg (fun m : ℕ => (Work.Cohomology.relChains
          (Work.StemsB.CubeSpace (Y := PUnit) (n+1))
          (Work.StemsB.cubeBdryK PUnit (n+1))).homology m) (Nat.zero_add (n+1)).symm)
    ≪≫ (Classical.choice (Work.StemsB.cubePair_iso (n+1) PUnit 0))
    ≪≫ (Classical.choice (h0PUnit_iso))

/-- **The relative fundamental class of the cube**: the generator of
`H_{n+1}(I^{n+1},∂I^{n+1};ℤ) ≅ ℤ` corresponding to `1` under `relCubeGenIso`. -/
def relCubeGen (n : ℕ) :
    (Work.Cohomology.relChains (cubeTop (n+1)) (cubeBdrySet (n+1))).homology (n+1) :=
  (relCubeGenIso n).inv (1 : ℤ)

/-- `relCubeGenIso` sends the relative fundamental class of the cube to `1`. -/
theorem relCubeGenIso_relCubeGen (n : ℕ) : (relCubeGenIso n).hom (relCubeGen n) = 1 := by
  rw [relCubeGen]
  exact CategoryTheory.Iso.inv_hom_id_apply (relCubeGenIso n) 1

/-- The classes of the relative homology of the cube pair are the integral multiples of the relative
fundamental class: `H_{n+1}(I^{n+1},∂I^{n+1};ℤ)` is generated by `relCubeGen n`. -/
theorem relCubeGen_span (n : ℕ) (v :
    (Work.Cohomology.relChains (cubeTop (n+1)) (cubeBdrySet (n+1))).homology (n+1)) :
    ∃ k : ℤ, v = k • relCubeGen n := by
  refine ⟨(relCubeGenIso n).hom v, ?_⟩
  rw [relCubeGen, ← map_zsmul]
  have h : (relCubeGenIso n).hom v • (1 : ℤ) = (relCubeGenIso n).hom v := by simp
  rw [h, CategoryTheory.Iso.hom_inv_id_apply]

/-! ## The relative Hurewicz class of a map of pairs -/

/-- The restriction of a map of pairs `(I^{n+1},∂I^{n+1}) → (X,A)` to the boundary, as a map
`∂I^{n+1} → A`. -/
def bdryRestrict (n : ℕ) {X : Type} [TopologicalSpace X] {A : Set X}
    (g : C(cubeTop (n+1), X)) (hg : ∀ z : cubeTop (n+1), z ∈ cubeBdrySet (n+1) → g z ∈ A) :
    C(TopCat.of (cubeBdrySet (n+1)), TopCat.of A) where
  toFun z := ⟨g z.1, hg z.1 z.2⟩
  continuous_toFun :=
    Continuous.subtype_mk (g.continuous.comp continuous_subtype_val) (fun z => hg z.1 z.2)

/-- The two composites defining a map of pairs agree: the inclusion of the boundary followed by `g`
is the restriction to the boundary followed by the inclusion of `A`. -/
theorem bdryRestrict_comm (n : ℕ) {X : Type} [TopologicalSpace X] {A : Set X}
    (g : C(cubeTop (n+1), X)) (hg : ∀ z : cubeTop (n+1), z ∈ cubeBdrySet (n+1) → g z ∈ A) :
    Work.Cohomology.subtypeIncl (cubeTop (n+1)) (cubeBdrySet (n+1)) ≫ TopCat.ofHom g =
      TopCat.ofHom (bdryRestrict n g hg) ≫ Work.Cohomology.subtypeIncl (TopCat.of X) A := by
  apply TopCat.hom_ext
  ext z
  rfl

/-- **The relative Hurewicz class of a map of pairs.**  For a continuous map
`g : I^{n+1} → X` whose restriction to the boundary lands in `A ⊆ X`, this is the push-forward
`g_*[I^{n+1},∂I^{n+1}] ∈ H_{n+1}(X,A;ℤ)` of the relative fundamental class of the cube along the
induced map of relative chain complexes:
`relChainsMapOf` of the map of pairs `(g, g|_{∂I^{n+1}})`, applied to `relCubeGen n`. -/
def relHurewiczClass (n : ℕ) {X : Type} [TopologicalSpace X] {A : Set X}
    (g : C(cubeTop (n+1), X)) (hg : ∀ z : cubeTop (n+1), z ∈ cubeBdrySet (n+1) → g z ∈ A) :
    (Work.Cohomology.relChains (TopCat.of X) A).homology (n+1) :=
  HomologicalComplex.homologyMap
    (Work.Cohomology.relChainsMapOf (cubeTop (n+1)) (TopCat.of X) (cubeBdrySet (n+1)) A
      (TopCat.ofHom g) (TopCat.ofHom (bdryRestrict n g hg)) (bdryRestrict_comm n g hg)) (n+1)
    (relCubeGen n)

/-! ## The relative cube of a based cube in the homotopy fibre -/

/-- **The map of pairs attached to a based cube in the homotopy fibre.**  For `i : C(A,X)`,
`a₀ : A` and `p : Ω^ (Fin n) (homotopyFibre i a₀) _`, the map
`cubeToPair n i a₀ p : I^{n+1} → X` sends `z` to `γ_{z|_n}(z (last n))`, where `z|_n` is the first
`n` coordinates of `z`.  Its first face is the constant path at `i a₀`, its second face lands in
`A`, and its remaining boundary is the base point — so it represents the classical relative class
`π_{n+1}(X,A,x₀)` corresponding to `p`. -/
def cubeToPair (n : ℕ) {X : Type} [TopologicalSpace X] {A : Type} [TopologicalSpace A]
    (i : C(A, X)) (a₀ : A)
    (p : Ω^ (Fin n) (homotopyFibre i a₀) (homotopyFibreBasepoint i a₀)) :
    C(cubeTop (n+1), X) where
  toFun z := (p.1 (fun j : Fin n => z j.castSucc)).1.2.1 (z (Fin.last n))
  continuous_toFun := by
    have hφ : Continuous (fun z : Fin (n+1) → unitInterval => fun j : Fin n => z j.castSucc) :=
      continuous_pi (fun j => continuous_apply (Fin.castSucc j))
    have hΨ : Continuous (fun z : Fin (n+1) → unitInterval =>
        (p.1 (fun j : Fin n => z j.castSucc)).1.2) :=
      (Work.StemsB.bundlePullbackSnd (X := X) (x₀ := i a₀) A i).continuous.comp
        (p.1.continuous.comp hφ)
    have hpair : Continuous (fun z : Fin (n+1) → unitInterval =>
        ((p.1 (fun j : Fin n => z j.castSucc)).1.2, z (Fin.last n))) :=
      hΨ.prodMk (continuous_apply (Fin.last n))
    have hev : Continuous (fun q : Work.StemsB.PathSpace X (i a₀) × unitInterval =>
        q.1.1 q.2) := by
      have hsub : Continuous (fun q : Work.StemsB.PathSpace X (i a₀) × unitInterval =>
          (q.1.1 : C(unitInterval, X))) :=
        (continuous_subtype_val (p := fun (γ : C(unitInterval, X)) => γ 0 = i a₀)).comp
          continuous_fst
      exact continuous_eval.comp (hsub.prodMk continuous_snd)
    exact hev.comp hpair

end

end Work.RatHurewicz
