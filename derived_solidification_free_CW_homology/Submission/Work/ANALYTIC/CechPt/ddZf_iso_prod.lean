import Mathlib
import Submission.Work.ANALYTIC.CechPt.CoordDefs
import Submission.Work.ANALYTIC.CechPt.DdZfAux
import Submission.Work.ANALYTIC.CechPt.DdZfAssembly
import Submission.Work.ANALYTIC.CechPt.gamma_phiT
import Submission.Work.ANALYTIC.CechPt.lamHat_lamJ
import Submission.Work.ANALYTIC.CechPt.lamHat_lamInf
import Submission.Work.ANALYTIC.CechPt.cdisc_coproduct_basis
import Submission.Work.ANALYTIC.CechPt.isIso_piLift_pre_sigma_unit

/-!
# `dd (ℤ[T]) ≅ 𝟙 ⊞ ∏_ℕ ℤ` with the Haar coordinates

For an infinite light profinite set `T`, the double dual `dd (ℤ[T]) = ℤ■[T] = ihom(C(T,ℤ)_disc,ℤ)`
is the biproduct of `𝟙 = ℤ` and `∏_ℕ ℤ`, with coordinates the dual elements `lamInf T` (the
augmentation, dual to the constant function `1`) and `lamJ T n` (dual to the cylinder `fCyl T n`).

The proof is the assembly `ddZf_iso_prod_of_pieces` (see
`Submission/Work/ANALYTIC/CechPt/DdZfAssembly.lean`) from the five pieces

* `gamma_phiT` — the canonical isomorphism `phiT : sd (ℤ[T]) ≅ Cdisc T` is the evaluation pairing;
* `lamHat_lamJ`, `lamHat_lamInf` — the dual elements are the Haar basis elements;
* `cdisc_coproduct_basis` — `Cdisc T` is the coproduct `∐_{ℕ∪{∞}} 𝟙` with the Haar basis as its
  inclusions;
* `isIso_piLift_pre_sigma_unit` — the transposed coproduct comparison `(∐_j 𝟙 ⟹ 𝟙) ≅ ∏_j 𝟙`.
-/

namespace Work.ANALYTIC.CechPt

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

set_option backward.isDefEq.respectTransparency false

theorem ddZf_iso_prod (T : LightProfinite.{0}) [Infinite T] :
    ∃ e : Work.ANALYTIC.CechPt.dd (Work.ANALYTIC.CechPt.zf T) ≅
        (𝟙_ LightCondAb ⊞ Work.ANALYTIC.prodZ),
      (e.hom ≫ CategoryTheory.Limits.biprod.fst =
        Work.ANALYTIC.CechPt.coordMap (Work.ANALYTIC.CechPt.zf T)
          (Work.ANALYTIC.CechPt.lamInf T)) ∧
      (∀ j : ℕ, e.hom ≫ CategoryTheory.Limits.biprod.snd ≫
          CategoryTheory.Limits.Pi.π (fun _ : ℕ => 𝟙_ LightCondAb) j =
        Work.ANALYTIC.CechPt.coordMap (Work.ANALYTIC.CechPt.zf T)
          (Work.ANALYTIC.CechPt.lamJ T j)) := by
  obtain ⟨e, h1, h2⟩ := ddZf_iso_prod_of_pieces T (gamma_phiT T)
    (fun n => lamHat_lamJ T n) (lamHat_lamInf T) (cdisc_coproduct_basis T)
    (isIso_piLift_pre_sigma_unit Haar.JIdx)
  exact ⟨e, h1, h2⟩

end Work.ANALYTIC.CechPt
