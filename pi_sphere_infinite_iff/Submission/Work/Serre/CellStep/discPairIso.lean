import Mathlib
import Submission.Work.Serre.CellStep.Defs
import Submission.Work.Serre.cubeRelIso
import Submission.Work.Serre.cubeDiskHomeo

set_option synthInstance.maxHeartbeats 400000


set_option linter.style.haveILetI false

/-!
# The disc form of `(P_D)`

`Work.Serre.cubeRelIso` proves statement `(P_D)`: for a Serre fibration `p : E → B`, a map
`τ : I^D → B` and a fibre which is homologically `f`-connected over every point of the cube, the
map of pairs `(τ^*E, τ^*E|_{∂I^D}) → (I^D, ∂I^D)` induced by the fibration is an isomorphism on
homology in degrees `< D + f`.

Here we transport it along the homeomorphism `I^{n+2} ≅ D^{n+2}` of `Work.Serre.cubeDiskHomeo` to
obtain the same statement for the model cell `D^{n+2} = cellDisk n` and its boundary sphere
`cellSphereSet n`, i.e. for the map of pairs `Work.Serre.discPairMap n p τ`.

The transport is formal.  The homeomorphism `e : I^{n+2} ≅ D^{n+2}` induces

* a homeomorphism of pairs `(I^{n+2}, ∂I^{n+2}) ≅ (D^{n+2}, S^{n+1})`, and
* a homeomorphism of pairs `((τ ∘ e)^*E, (τ ∘ e)^*E|_{∂I^{n+2}}) ≅ (τ^*E, τ^*E|_{S^{n+1}})` over it,

and the two model maps of pairs form a commutative square with these two homeomorphisms.  A square
whose vertical maps are isomorphisms of chain complexes transfers the quasi-isomorphism property.
-/

namespace Work.Serre.CellStep

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits
open Work.RatHurewicz

noncomputable section

/-! ## The cube–disk homeomorphism and its boundary behaviour -/

/-- The cube `I^{n+2}` is homeomorphic to the closed model cell `D^{n+2} = cellDisk n`. -/
abbrev cellHomeo (n : ℕ) : Work.Stems.Cubical.IC (n + 2) ≃ₜ cellDisk n :=
  Classical.choose (Work.Serre.cubeDiskHomeo (n + 2))

/-- The homeomorphism carries the boundary of the cube onto the boundary sphere of the cell. -/
theorem cellHomeo_boundary (n : ℕ) (x : Work.Stems.Cubical.IC (n + 2)) :
    x ∈ Work.Serre.cubeBdryS (n + 2) ↔ cellHomeo n x ∈ cellSphereSet n := by
  have h := Classical.choose_spec (Work.Serre.cubeDiskHomeo (n + 2)) x
  show x ∈ Cube.boundary (Fin (n + 2)) ↔
    (Classical.choose (Work.Serre.cubeDiskHomeo (n + 2))) x ∈ cellSphereSet n
  rw [mem_cellSphereSet]
  simpa only [Metric.mem_sphere, dist_zero_right] using h

/-- The homeomorphism as a continuous map. -/
abbrev cellHomeoHom (n : ℕ) : C(Work.Stems.Cubical.IC (n + 2), cellDisk n) :=
  ⟨cellHomeo n, (cellHomeo n).continuous_toFun⟩

/-- The base map of the cube model: `τ` precomposed with the cube–disk homeomorphism. -/
abbrev tauCube (n : ℕ) {B : Type} [TopologicalSpace B]
    (τ : C(cellDisk n, B)) : C(Work.Stems.Cubical.IC (n + 2), B) :=
  τ.comp (cellHomeoHom n)

/-! ## The homeomorphism of pullbacks -/

/-- **The homeomorphism of pullbacks** `(τ ∘ e)^*E ≅ τ^*E` covering the cube–disk homeomorphism
`e`. -/
def pbHomeo (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(cellDisk n, B)) :
    Work.StemsB.Pullback p (tauCube n τ) ≃ₜ Work.StemsB.Pullback p τ where
  toFun x := ⟨(x.1.1, cellHomeo n x.1.2), x.2⟩
  invFun y := ⟨(y.1.1, (cellHomeo n).symm y.1.2), by
    show p y.1.1 = τ (cellHomeo n ((cellHomeo n).symm y.1.2))
    rw [Homeomorph.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext (by ext <;> simp)
  right_inv y := Subtype.ext (by ext <;> simp)
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.fst.prodMk
      ((cellHomeo n).continuous.comp continuous_subtype_val.snd)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.fst.prodMk
      ((cellHomeo n).symm.continuous.comp continuous_subtype_val.snd)

/-- The homeomorphism of pairs on the boundaries. -/
theorem pbHomeo_mem_boundary (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(cellDisk n, B)) (x : Work.StemsB.Pullback p (tauCube n τ)) :
    x ∈ Work.Serre.pbPre p (tauCube n τ) (Work.Serre.cubeBdryS (n + 2)) ↔
      pbHomeo n p τ x ∈ Work.Serre.discPre n p τ (cellSphereSet n) :=
  cellHomeo_boundary n x.1.2

/-! ## Transport of relative chain complexes along a homeomorphism of pairs -/

/-- **A homeomorphism of pairs induces an isomorphism of relative chain complexes.**

This is `Work.StemsB.isIso_relChainsMapOf_homeomorph` with the two membership conditions supplied
separately, which is the form used below (the generic compatibility proofs do not have to be
`Work.StemsB.homeoPairMem`). -/
theorem isIso_relChainsMapOf_homeo {X Y : TopCat} (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (hAB : ∀ x ∈ A, (Work.StemsB.sphHomeoHom e) x ∈ B)
    (hBA : ∀ y ∈ B, (Work.StemsB.sphHomeoHom e.symm) y ∈ A)
    (w : Work.Cohomology.subtypeIncl X A ≫ Work.StemsB.sphHomeoHom e
      = Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e) A B hAB
        ≫ Work.Cohomology.subtypeIncl Y B) :
    IsIso (Work.Cohomology.relChainsMapOf X Y A B (Work.StemsB.sphHomeoHom e)
      (Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e) A B hAB) w) := by
  haveI hq : IsIso (Work.Cohomology.chainMap ℤ X Y (Work.StemsB.sphHomeoHom e)) :=
    Work.StemsB.isIso_chainMap_sphHomeoHom e
  have h1 : Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e) A B hAB
      ≫ Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e.symm) B A hBA
      = 𝟙 (TopCat.of A) := by
    apply TopCat.hom_ext
    ext a
    exact e.symm_apply_apply a.1
  have h2 : Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e.symm) B A hBA
      ≫ Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e) A B hAB
      = 𝟙 (TopCat.of B) := by
    apply TopCat.hom_ext
    ext b
    exact e.apply_symm_apply b.1
  haveI hp : IsIso (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B)
      (Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e) A B hAB)) :=
    IsIso.mk ⟨Work.Cohomology.chainMap ℤ (TopCat.of B) (TopCat.of A)
        (Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e.symm) B A hBA),
      by rw [Work.StemsB.chainMap_comp, h1, Work.StemsB.chainMap_id],
      by rw [Work.StemsB.chainMap_comp, h2, Work.StemsB.chainMap_id]⟩
  exact inferInstanceAs (IsIso (cokernel.map (Work.Cohomology.inclChains X A)
    (Work.Cohomology.inclChains Y B)
    (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B)
      (Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e) A B hAB))
    (Work.Cohomology.chainMap ℤ X Y (Work.StemsB.sphHomeoHom e))
    (Work.StemsB.inclChains_comp_chainMap (Work.StemsB.sphHomeoHom e) A B hAB)))

/-- **The relative chain map depends only on the underlying map of pairs**: two choices of the
compatibility proof, and equal maps, give equal chain maps. -/
theorem relChainsMapOf_congr {X Y : TopCat} (A : Set X) (B : Set Y)
    {f₁ f₂ : X ⟶ Y} {g₁ g₂ : TopCat.of ↑A ⟶ TopCat.of ↑B}
    (hf : f₁ = f₂) (hg : g₁ = g₂)
    (w₁ : Work.Cohomology.subtypeIncl X A ≫ f₁ = g₁ ≫ Work.Cohomology.subtypeIncl Y B)
    (w₂ : Work.Cohomology.subtypeIncl X A ≫ f₂ = g₂ ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.Cohomology.relChainsMapOf X Y A B f₁ g₁ w₁
      = Work.Cohomology.relChainsMapOf X Y A B f₂ g₂ w₂ := by
  cases hf
  cases hg
  rfl

/-! ## The disc statement, by transport from the cube -/

theorem discPairIso (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (τ : C(Work.RatHurewicz.cellDisk n, B))
    (φ : ℕ)
    (hfib : ∀ y : Work.RatHurewicz.cellDisk n, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre p (τ y)))).homology j))
    (h0 : ∀ y : Work.RatHurewicz.cellDisk n,
      CategoryTheory.IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre p (τ y)))
        (ModuleCat.of ℤ ℤ)))
    (i : ℕ) (hi : i < (n + 2) + φ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Serre.discPairMap n p τ) i) := by
  -- the cube form of `(P_D)`, applied to `τ ∘ e`
  haveI hCh : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.cubePairMap (n + 2) p (tauCube n τ)) i) :=
    Work.Serre.cubeRelIso (n + 2) E B p hp (tauCube n τ) φ
      (fun y j hj hjφ => hfib (cellHomeo n y) j hj hjφ)
      (fun y => h0 (cellHomeo n y)) i hi
  -- the two relative chain complexes and the model maps of pairs
  let A₁ : Set (Work.StemsB.Pullback p (tauCube n τ)) :=
    Work.Serre.pbPre p (tauCube n τ) (Work.Serre.cubeBdryS (n + 2))
  let B₁ : Set (Work.StemsB.Pullback p τ) :=
    Work.Serre.discPre n p τ (cellSphereSet n)
  let Bs : Set (Work.Stems.Cubical.IC (n + 2)) := Work.Serre.cubeBdryS (n + 2)
  let Bd : Set (cellDisk n) := cellSphereSet n
  let P : TopCat := TopCat.of (Work.StemsB.Pullback p (tauCube n τ))
  let Q : TopCat := TopCat.of (Work.StemsB.Pullback p τ)
  let X : TopCat := TopCat.of (Work.Stems.Cubical.IC (n + 2))
  let Y : TopCat := TopCat.of (cellDisk n)
  let Φm : P ⟶ Q := Work.StemsB.sphHomeoHom (pbHomeo n p τ)
  let hcb : ∀ x ∈ A₁, Φm x ∈ B₁ := fun x hx => (pbHomeo_mem_boundary n p τ x).mp hx
  let hcb' : ∀ y : Work.StemsB.Pullback p τ, y ∈ B₁ →
      Work.StemsB.sphHomeoHom (X := Q) (Y := P) (pbHomeo n p τ).symm y ∈ A₁ := fun y hy =>
    (pbHomeo_mem_boundary n p τ ((pbHomeo n p τ).symm y)).mpr (by
      rw [Homeomorph.apply_symm_apply]; exact hy)
  let Φb : TopCat.of A₁ ⟶ TopCat.of B₁ := Work.StemsB.pairRestrict Φm A₁ B₁ hcb
  let wΦ : Work.Cohomology.subtypeIncl P A₁ ≫ Φm
      = Φb ≫ Work.Cohomology.subtypeIncl Q B₁ :=
    Work.StemsB.pairRestrict_comp_subtypeIncl Φm A₁ B₁ hcb
  let Gm : Q ⟶ Y := TopCat.ofHom (Work.StemsB.pullbackSnd p τ)
  let Gb : TopCat.of B₁ ⟶ TopCat.of Bd :=
    TopCat.ofHom (Work.Serre.discPairMapRel n p τ)
  let wG : Work.Cohomology.subtypeIncl Q B₁ ≫ Gm
      = Gb ≫ Work.Cohomology.subtypeIncl Y Bd := by ext x; rfl
  let Fm : P ⟶ X := TopCat.ofHom (Work.StemsB.pullbackSnd p (tauCube n τ))
  let Fb : TopCat.of A₁ ⟶ TopCat.of Bs :=
    TopCat.ofHom (Work.Serre.cubePairMapRel (n + 2) p (tauCube n τ))
  let wF : Work.Cohomology.subtypeIncl P A₁ ≫ Fm
      = Fb ≫ Work.Cohomology.subtypeIncl X Bs := by ext x; rfl
  let Em : X ⟶ Y := Work.StemsB.sphHomeoHom (cellHomeo n)
  let hbd : ∀ x : Work.Stems.Cubical.IC (n + 2), x ∈ Bs ↔ cellHomeo n x ∈ Bd :=
    fun x => cellHomeo_boundary n x
  let heb : ∀ x ∈ Bs, Em x ∈ Bd := fun x hx => (hbd x).mp hx
  let heb' : ∀ y : cellDisk n, y ∈ Bd →
      Work.StemsB.sphHomeoHom (X := Y) (Y := X) (cellHomeo n).symm y ∈ Bs := fun y hy =>
    (hbd ((cellHomeo n).symm y)).mpr (by rw [Homeomorph.apply_symm_apply]; exact hy)
  let Eb : TopCat.of Bs ⟶ TopCat.of Bd := Work.StemsB.pairRestrict Em Bs Bd heb
  let wE : Work.Cohomology.subtypeIncl X Bs ≫ Em
      = Eb ≫ Work.Cohomology.subtypeIncl Y Bd :=
    Work.StemsB.pairRestrict_comp_subtypeIncl Em Bs Bd heb
  -- the identifications of the two model maps of pairs with `relChainsMapOf`
  have hD : Work.Serre.discPairMap n p τ
      = Work.Cohomology.relChainsMapOf Q Y B₁ Bd Gm Gb wG := rfl
  have hC : Work.Serre.cubePairMap (n + 2) p (tauCube n τ)
      = Work.Cohomology.relChainsMapOf P X A₁ Bs Fm Fb wF := rfl
  -- the two trivial commutativities of maps of pairs
  have hsquare : Φm ≫ Gm = Fm ≫ Em := by
    apply TopCat.hom_ext
    ext x
    rfl
  have hsquareB : Φb ≫ Gb = Fb ≫ Eb := by
    apply TopCat.hom_ext
    ext x
    rfl
  -- the two compatibility proofs for the middle term, and the square of chain complexes
  have w₁ : Work.Cohomology.subtypeIncl P A₁ ≫ (Φm ≫ Gm)
      = (Φb ≫ Gb) ≫ Work.Cohomology.subtypeIncl Y Bd := by ext x; rfl
  have w₂ : Work.Cohomology.subtypeIncl P A₁ ≫ (Fm ≫ Em)
      = (Fb ≫ Eb) ≫ Work.Cohomology.subtypeIncl Y Bd := by ext x; rfl
  have h1 := Work.Cohomology.relChainsMapOf_comp A₁ B₁ Bd Φm Φb wΦ Gm Gb wG w₁
  have h2 := Work.Cohomology.relChainsMapOf_comp A₁ Bs Bd Fm Fb wF Em Eb wE w₂
  have hm := relChainsMapOf_congr A₁ Bd hsquare hsquareB w₁ w₂
  have hrel : Work.Cohomology.relChainsMapOf P Q A₁ B₁ Φm Φb wΦ
        ≫ Work.Cohomology.relChainsMapOf Q Y B₁ Bd Gm Gb wG
      = Work.Cohomology.relChainsMapOf P X A₁ Bs Fm Fb wF
        ≫ Work.Cohomology.relChainsMapOf X Y Bs Bd Em Eb wE :=
    h1.trans (hm.trans h2.symm)
  -- the vertical maps are isomorphisms of chain complexes
  haveI hE₁ : IsIso (Work.Cohomology.relChainsMapOf P Q A₁ B₁ Φm Φb wΦ) :=
    isIso_relChainsMapOf_homeo (X := P) (Y := Q) (pbHomeo n p τ) A₁ B₁ hcb hcb' wΦ
  haveI hE₂ : IsIso (Work.Cohomology.relChainsMapOf X Y Bs Bd Em Eb wE) :=
    isIso_relChainsMapOf_homeo (X := X) (Y := Y) (cellHomeo n) Bs Bd heb heb' wE
  haveI : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf P X A₁ Bs Fm Fb wF) i) := hCh
  -- transfer the quasi-isomorphism along the square
  have hw := congrArg (fun ψ => HomologicalComplex.homologyMap ψ i) hrel
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hw
  exact IsIso.of_isIso_fac_left hw

end

end Work.Serre.CellStep
