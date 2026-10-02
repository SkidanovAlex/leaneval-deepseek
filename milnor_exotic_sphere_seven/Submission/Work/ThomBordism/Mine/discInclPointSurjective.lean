import Mathlib
import Submission.Work.ThomBordism.Mine.Vocab
import Submission.Work.ThomBordism.radialRescale_homologyMap_id
import Submission.Work.ThomBordism.ambientLocalDefs2
import Submission.Work.ThomBordism.normalTotal_locH_surjective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory

namespace Work.ThomBordism.Mine

/-- **The inclusion of the disc bundle is surjective on the local homology at a zero-section
point.**

The radial capping `p ↦ (proj p, min(1, ε/‖p‖) • vec p)` maps the normal total space into the disc
bundle `D_ε(ν)` and is the identity on it; it is homotopic to the identity through positive radial
rescalings, which preserve the complement of `0_x` at every time.  Hence the inclusion of the disc
bundle has a right homotopy inverse through maps of the pair `(ν, ν∖{0_x})`, and a homotopy
retraction induces a surjection on relative homology. -/
theorem discInclPointSurjective {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k]
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    Function.Surjective (Work.PTGeometric.HOF.RelHmapOf (7 + k + 1)
      (Work.ThomBordism.Mine.discIncl E ε)
      ({Work.ThomBordism.Mine.zeroSecDisc (E := E) C.eps_pos x} : Set (Work.Tubular.NormalDiscSub E ε))
      ({Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E))
      (Work.ThomBordism.Mine.discIncl_not_mem_point E C x)) := by
  classical
  have hε : 0 < ε := C.eps_pos
  let ι : TopCat.of (Work.Tubular.NormalDiscSub E ε) ⟶ TopCat.of (Work.Tubular.NormalTotal E) :=
    Work.ThomBordism.Mine.discIncl E ε
  let cT : TopCat.of (Work.Tubular.NormalTotal E) ⟶ TopCat.of (Work.Tubular.NormalDiscSub E ε) :=
    TopCat.ofHom (Work.ThomBordism.capToDisc (E := E) hε)
  -- the capping sends the complement of `0_x` into the complement of `0_x`
  have hg : ∀ p : Work.Tubular.NormalTotal E,
      p ∉ ({Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E)) →
      cT p ∉ ({Work.ThomBordism.Mine.zeroSecDisc (E := E) C.eps_pos x} :
        Set (Work.Tubular.NormalDiscSub E ε)) := by
    intro p hp hcon
    apply hp
    have h1 : ((cT p : Work.Tubular.NormalDiscSub E ε) : Work.Tubular.NormalTotal E)
        = Work.Tubular.zeroSectionNormal E x := by
      rw [hcon]
    exact (Work.ThomBordism.cap_eq_zeroSection_iff (E := E) hε x p).mp h1
  -- the capping composed with the inclusion is homotopic to the identity
  let Hf : TopCat.Homotopy (cT ≫ ι) (𝟙 (TopCat.of (Work.Tubular.NormalTotal E))) :=
    { toContinuousMap := Work.ThomBordism.radialRescaleHomotopy E (Work.ThomBordism.capCoeff ε)
        (Work.ThomBordism.continuous_capCoeff hε)
      map_zero_left := fun p => by
        show Work.ThomBordism.radialRescaleHomotopyFun E (Work.ThomBordism.capCoeff ε)
          ((0 : unitInterval), p) = (cT ≫ ι) p
        rw [Work.ThomBordism.radialRescaleHomotopyFun_zero]
        rfl
      map_one_left := fun p => by
        show Work.ThomBordism.radialRescaleHomotopyFun E (Work.ThomBordism.capCoeff ε)
          ((1 : unitInterval), p) = (𝟙 (TopCat.of (Work.Tubular.NormalTotal E))) p
        rw [Work.ThomBordism.radialRescaleHomotopyFun_one]
        rfl }
  have hHf : ∀ t y, y ∉ ({Work.Tubular.zeroSectionNormal E x} :
      Set (Work.Tubular.NormalTotal E)) →
      Hf (t, y) ∉ ({Work.Tubular.zeroSectionNormal E x} :
        Set (Work.Tubular.NormalTotal E)) :=
    fun t y hy => Work.ThomBordism.capEndHomotopy_ne_zeroSection (E := E) hε x hy
  exact Work.ThomBordism.surjective_relHmapOf_of_homotopy_retract (n := 7 + k + 1) ι cT
    (Work.ThomBordism.Mine.discIncl_not_mem_point E C x) hg Hf hHf

end Work.ThomBordism.Mine
