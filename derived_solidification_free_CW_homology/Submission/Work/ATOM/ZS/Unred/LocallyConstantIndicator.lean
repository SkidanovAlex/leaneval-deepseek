import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.zdesc
import Submission.Work.ATOM.ZS.Unred.LCZ
import Submission.Work.ATOM.ZS.Unred.LCZ_map_ptAt
import Submission.Work.ATOM.ZS.Unred.LCZ_generator

/-!
# Locally constant functions give the "integration" functional `ℤ[T] ⟶ ℤ[*]`

For a light profinite set `T` and a locally constant function `f : ↥T ⟶ ℤ` we produce a morphism
`φ : ℤ[T] ⟶ ℤ[*]` with `zmap (ptAt t) ≫ φ = f t • 𝟙 (ℤ[*])` for every `t : ↥T`.

Transport the section `f ∈ LCZ(T) = LocallyConstant ↥T ℤ` along a morphism
`j : LCZ ⟶ ℤ[*]` whose value at the point is the canonical generator `e₁` of `ℤ[*](*)`
(`LCZ_generator`), and apply `homFreeEquiv`:

`φ := (homFreeEquiv T ℤ[*]).symm (j_T f)`.

The pointwise statement follows by naturality of `homFreeEquiv` (`homFreeEquiv_naturality`),
naturality of `j`, `LCZ_map_ptAt` (the restriction map of `LCZ` evaluates a section at a point),
`section_map_smul` (`ℤ`-linearity of section maps) and `smul_id_section` (the endomorphism `a • 𝟙`
acts on sections as multiplication by `a`).
-/

namespace Work.ATOM.ZS.Unred

open CategoryTheory MonoidalCategory LightCondensed
open _root_.LightCondensed
open Opposite

open CategoryTheory MonoidalCategory LightCondensed in
theorem LocallyConstantIndicator (T : LightProfinite.{0}) (f : LocallyConstant ↥T ℤ) : ∃ φ : Work.ATOM.zfree T ⟶ Work.ATOM.zfree Work.ATOM.pt, ∀ t : ↥T, Work.ATOM.zmap (Work.ATOM.ptAt t) ≫ φ = f t • 𝟙 (Work.ATOM.zfree Work.ATOM.pt) := by
  obtain ⟨j, hj⟩ := LCZ_generator
  refine ⟨(Work.ATOM.homFreeEquiv T (Work.ATOM.zfree Work.ATOM.pt)).symm
    (j.hom.app (op T) f), fun t => ?_⟩
  -- the value of `f t • 𝟙` at the generic point
  have key : Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree Work.ATOM.pt)
      (f t • 𝟙 (Work.ATOM.zfree Work.ATOM.pt)) = f t • e1 := by
    rw [← Category.id_comp (f t • 𝟙 (Work.ATOM.zfree Work.ATOM.pt)),
      homFreeEquiv_comp (𝟙 (Work.ATOM.zfree Work.ATOM.pt)) (f t • 𝟙 (Work.ATOM.zfree Work.ATOM.pt))]
    exact smul_id_section (Work.ATOM.zfree Work.ATOM.pt) Work.ATOM.pt (f t) e1
  apply (Work.ATOM.homFreeEquiv Work.ATOM.pt (Work.ATOM.zfree Work.ATOM.pt)).injective
  rw [Work.ATOM.homFreeEquiv_naturality (Work.ATOM.ptAt t)]
  rw [Equiv.apply_symm_apply]
  rw [show (Work.ATOM.zfree Work.ATOM.pt).obj.map (Work.ATOM.ptAt t).op
        (j.hom.app (op T) f)
      = j.hom.app (op Work.ATOM.pt) (LCZ.obj.map (Work.ATOM.ptAt t).op f) from
    (j.hom.naturality_apply (Work.ATOM.ptAt t).op f).symm]
  rw [LCZ_map_ptAt T t f]
  rw [section_map_smul _ _ j _ (f t) oneLCZ]
  rw [hj]
  rw [key]

end Work.ATOM.ZS.Unred
