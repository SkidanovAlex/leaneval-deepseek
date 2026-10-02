import Mathlib
import Submission.Work.Serre.CellStep.Defs
import Submission.Work.Serre.cubeRelIso
import Submission.Work.Serre.cubeDiskHomeo
import Submission.Work.Cohomology.relChainsMapOf_isIso
import Submission.Work.StemsB.SphLoopRelPair

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

/-!
# The strong form of statement `(P_D)` for the model cell

`Work.Serre.cubeRelIso` (and its strong form `Work.Serre.SPC.cubePairStrong`) proves the cube pair
statement.  Here it is transported along the homeomorphism `I^{n+2} ≅ D^{n+2}` of
`Work.Serre.cubeDiskHomeo` to the model cell `D^{n+2} = cellDisk n` and its boundary sphere
`cellSphereSet n`, i.e. to the map of pairs `Work.Serre.discPairMap n p τ`.

The transport is a diamond of maps of pairs: the cube-disc homeomorphism `e`, the induced
homeomorphism of pullbacks `(τ ∘ e)^*E ≅ τ^*E`, and the fact that the pair maps of the cube and the
disc correspond under both.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC

noncomputable section

/-! ## Transfer of `IsIso` and of surjectivity along a commutative square -/

/-- **`IsIso` transfers across a commutative square whose vertical maps are isomorphisms.** -/
theorem isIso_iff_of_comm_square {A B C D : ModuleCat ℤ} (h : A ⟶ B) (f : C ⟶ D) (u : C ⟶ A)
    (v : D ⟶ B) (hsq : u ≫ h = f ≫ v) [IsIso u] [IsIso v] : IsIso h ↔ IsIso f := by
  constructor
  · intro hh
    have h2 : IsIso (u ≫ h) := inferInstance
    rw [hsq] at h2
    haveI := h2
    exact IsIso.of_isIso_comp_right f v
  · intro hf
    have h2 : IsIso (f ≫ v) := inferInstance
    rw [← hsq] at h2
    haveI := h2
    exact IsIso.of_isIso_comp_left u h

/-- **Surjectivity transfers across a commutative square whose vertical maps are isomorphisms.** -/
theorem surjective_iff_of_comm_square {A B C D : ModuleCat ℤ} (h : A ⟶ B) (f : C ⟶ D)
    (u : C ⟶ A) (v : D ⟶ B) (hsq : u ≫ h = f ≫ v) [IsIso u] [IsIso v] :
    Function.Surjective (ModuleCat.Hom.hom h) ↔ Function.Surjective (ModuleCat.Hom.hom f) := by
  have hcomp : ∀ c, ModuleCat.Hom.hom h (ModuleCat.Hom.hom u c)
      = ModuleCat.Hom.hom v (ModuleCat.Hom.hom f c) := by
    intro c
    have h1 : ModuleCat.Hom.hom (u ≫ h) c = ModuleCat.Hom.hom (f ≫ v) c := by rw [hsq]
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
      at h1
    exact h1
  have hv : Function.Surjective (ModuleCat.Hom.hom v) :=
    (ModuleCat.epi_iff_surjective v).mp (IsIso.epi_of_iso v)
  have hvinj : Function.Injective (ModuleCat.Hom.hom v) :=
    (ModuleCat.mono_iff_injective v).mp (IsIso.mono_of_iso v)
  have hu : Function.Surjective (ModuleCat.Hom.hom u) :=
    (ModuleCat.epi_iff_surjective u).mp (IsIso.epi_of_iso u)
  constructor
  · intro hh d
    obtain ⟨a, ha⟩ := hh (ModuleCat.Hom.hom v d)
    obtain ⟨c, rfl⟩ := hu a
    exact ⟨c, hvinj (by rw [← hcomp c]; exact ha)⟩
  · intro hf b
    obtain ⟨d, hd⟩ := hv b
    obtain ⟨c, hc⟩ := hf d
    exact ⟨ModuleCat.Hom.hom u c, by rw [hcomp c, hc, hd]⟩

/-! ## The cube–disc homeomorphism -/

/-- The cube `I^{n+2}` is homeomorphic to the closed model cell `D^{n+2} = cellDisk n`. -/
abbrev cHomeo (n : ℕ) : Work.Stems.Cubical.IC (n + 2) ≃ₜ Work.RatHurewicz.cellDisk n :=
  Classical.choose (Work.Serre.cubeDiskHomeo (n + 2))

/-- The homeomorphism carries the boundary of the cube onto the boundary sphere of the cell. -/
theorem cHomeo_mem_bdry (n : ℕ) (x : Work.Stems.Cubical.IC (n + 2)) :
    x ∈ Work.Serre.cubeBdryS (n + 2) ↔ cHomeo n x ∈ Work.Serre.cellSphereSet n := by
  have h := Classical.choose_spec (Work.Serre.cubeDiskHomeo (n + 2)) x
  rw [Work.Serre.mem_cellSphereSet]
  simpa only [Work.Serre.cubeBdryS, cHomeo, Metric.mem_sphere, dist_zero_right] using h

/-- The homeomorphism as a continuous map. -/
def cHomeoHom (n : ℕ) : C(Work.Stems.Cubical.IC (n + 2), Work.RatHurewicz.cellDisk n) :=
  ⟨cHomeo n, (cHomeo n).continuous_toFun⟩

@[simp] theorem cHomeoHom_apply (n : ℕ) (x : Work.Stems.Cubical.IC (n + 2)) :
    cHomeoHom n x = cHomeo n x := rfl

/-- The base map of the cube model: `τ` precomposed with the cube–disc homeomorphism. -/
def tauC (n : ℕ) {B : Type} [TopologicalSpace B]
    (τ : C(Work.RatHurewicz.cellDisk n, B)) : C(Work.Stems.Cubical.IC (n + 2), B) :=
  τ.comp (cHomeoHom n)

@[simp] theorem tauC_apply (n : ℕ) {B : Type} [TopologicalSpace B]
    (τ : C(Work.RatHurewicz.cellDisk n, B)) (x : Work.Stems.Cubical.IC (n + 2)) :
    tauC n τ x = τ (cHomeo n x) := rfl

/-- **The homeomorphism of pullbacks** `(τ ∘ e)^*E ≅ τ^*E` covering the cube–disc
homeomorphism. -/
def pbH (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(Work.RatHurewicz.cellDisk n, B)) :
    Work.StemsB.Pullback p (tauC n τ) ≃ₜ Work.StemsB.Pullback p τ where
  toFun x := ⟨(x.1.1, cHomeo n x.1.2), x.2⟩
  invFun y := ⟨(y.1.1, (cHomeo n).symm y.1.2), by
    show p y.1.1 = τ (cHomeo n ((cHomeo n).symm y.1.2))
    rw [Homeomorph.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext (by ext <;> simp)
  right_inv y := Subtype.ext (by ext <;> simp)
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.fst.prodMk
      ((cHomeo n).continuous.comp continuous_subtype_val.snd)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.fst.prodMk
      ((cHomeo n).symm.continuous.comp continuous_subtype_val.snd)

@[simp] theorem pbH_apply (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(Work.RatHurewicz.cellDisk n, B))
    (x : Work.StemsB.Pullback p (tauC n τ)) :
    pbH n p τ x = ⟨(x.1.1, cHomeo n x.1.2), x.2⟩ := rfl

/-- The pullback homeomorphism respects the preimages of the boundary. -/
theorem pbH_mem (n : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(Work.RatHurewicz.cellDisk n, B))
    (x : Work.StemsB.Pullback p (tauC n τ)) :
    x ∈ Work.Serre.pbPre p (tauC n τ) (Work.Serre.cubeBdryS (n + 2))
      ↔ pbH n p τ x ∈ Work.Serre.discPre n p τ (Work.Serre.cellSphereSet n) :=
  cHomeo_mem_bdry n x.1.2

/-- The relative chain map depends only on the underlying pair of maps. -/
theorem relChainsMapOf_congr' {X Y : TopCat} (A : Set X) (B : Set Y)
    {f₁ f₂ : X ⟶ Y} {g₁ g₂ : TopCat.of ↑A ⟶ TopCat.of ↑B}
    (hf : f₁ = f₂) (hg : g₁ = g₂)
    (w₁ : Work.Cohomology.subtypeIncl X A ≫ f₁ = g₁ ≫ Work.Cohomology.subtypeIncl Y B)
    (w₂ : Work.Cohomology.subtypeIncl X A ≫ f₂ = g₂ ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.Cohomology.relChainsMapOf X Y A B f₁ g₁ w₁
      = Work.Cohomology.relChainsMapOf X Y A B f₂ g₂ w₂ := by
  cases hf
  cases hg
  rfl


/-- **A homeomorphism of pairs induces an isomorphism of relative chain complexes** (form with the
two membership conditions supplied separately, so that the compatibility proofs do not have to be
`Work.StemsB.homeoPairMem`). -/
theorem isIso_relChainsMapOf_homeo' {X Y : TopCat} (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (hAB : ∀ x ∈ A, (Work.StemsB.sphHomeoHom e) x ∈ B)
    (hBA : ∀ y ∈ B, (Work.StemsB.sphHomeoHom (X := Y) (Y := X) e.symm) y ∈ A) :
    IsIso (Work.Cohomology.relChainsMapOf X Y A B (Work.StemsB.sphHomeoHom e)
      (Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e) A B hAB)
      (Work.StemsB.pairRestrict_comp_subtypeIncl (Work.StemsB.sphHomeoHom e) A B hAB)) := by
  haveI hq : IsIso (Work.Cohomology.chainMap ℤ X Y (Work.StemsB.sphHomeoHom e)) :=
    Work.StemsB.isIso_chainMap_sphHomeoHom (X := X) (Y := Y) e
  have h1 : Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e) A B hAB
      ≫ Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom (X := Y) (Y := X) e.symm) B A hBA
      = 𝟙 (TopCat.of A) := by
    apply TopCat.hom_ext
    ext a
    exact e.symm_apply_apply a.1
  have h2 : Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom (X := Y) (Y := X) e.symm) B A hBA
      ≫ Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e) A B hAB
      = 𝟙 (TopCat.of B) := by
    apply TopCat.hom_ext
    ext b
    exact e.apply_symm_apply b.1
  haveI hp : IsIso (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B)
      (Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e) A B hAB)) :=
    IsIso.mk ⟨Work.Cohomology.chainMap ℤ (TopCat.of B) (TopCat.of A)
        (Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom (X := Y) (Y := X) e.symm) B A hBA),
      by rw [Work.StemsB.chainMap_comp, h1, Work.StemsB.chainMap_id],
      by rw [Work.StemsB.chainMap_comp, h2, Work.StemsB.chainMap_id]⟩
  exact inferInstanceAs (IsIso (cokernel.map (Work.Cohomology.inclChains X A)
    (Work.Cohomology.inclChains Y B)
    (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B)
      (Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e) A B hAB))
    (Work.Cohomology.chainMap ℤ X Y (Work.StemsB.sphHomeoHom e))
    (Work.StemsB.inclChains_comp_chainMap (Work.StemsB.sphHomeoHom e) A B hAB)))

/-! ## The strong disc statement -/

end

end Work.Serre.SPC
