import Mathlib
import Submission.Work.RatHurewicz.Cofibre.Basic
import Submission.Work.RatHurewicz.Cofibre.Cover
import Submission.Work.RatHurewicz.Cofibre.BMHyp
import Submission.Work.RatHurewicz.ExcisionSetup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Hypothesis (B) of the Blakers–Massey application with the cover `(cofibreV ι, cofibreU ι)`

`Work.RatHurewicz.Cofibre.subsingleton_relPi_VVU`: the relative homotopy groups of the pair
`(cofibreV ι, cofibreV ι ∩ cofibreU ι)` vanish in degree `J` as soon as `π_J` of the intersection
and `π_{J+1}` of `cofibreV ι` vanish.  This is the mirror of `subsingleton_relPi_interInclRight`
with the two sets interchanged.

This lemma used to live in `Cofibre/compressRel_cofibre_range.lean`; it was moved here because it
needs the Blakers–Massey vocabulary (`Cofibre.BMHyp`), which is incompatible (duplicate `pushT`)
with `ThomBordism.Grassmann.chartPieceCompressFarCrux` that the current proof of
`compressRel_cofibre_range` imports.  It is not used by that proof.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Cofibre

noncomputable section
variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-- **Hypothesis (B) of the BM application with the cover `(V,U)`**: the pair `(V, V∩U)`.

Mirror of `subsingleton_relPi_interInclRight` with the two sets interchanged. -/
theorem subsingleton_relPi_VVU (ι : C(F, E)) (J : ℕ)
    (y₀ : ↥(cofibreV ι ∩ cofibreU ι))
    (hinter : Subsingleton (HomotopyGroup (Fin J) ↥(cofibreV ι ∩ cofibreU ι) y₀))
    (hV : Subsingleton (HomotopyGroup (Fin (J + 1)) ↥(cofibreV ι)
      ⟨y₀.1, y₀.2.1⟩)) :
    Subsingleton (RelHomotopyGroup (interInclLeft (cofibreV ι) (cofibreU ι)) y₀ J) := by
  have hA : Subsingleton (HomotopyGroup (Fin J)
      ↥{z : ↥(cofibreV ι) | (z : cofibre ι) ∈ cofibreU ι}
      ((interHomeo (cofibreV ι) (cofibreU ι)) y₀)) :=
    subsingleton_homotopyGroup_of_homeo (interHomeo (cofibreV ι) (cofibreU ι)) y₀ hinter
  have hset : Subsingleton (RelHomotopyGroup
      (setIncl {z : ↥(cofibreV ι) | (z : cofibre ι) ∈ cofibreU ι})
      ((interHomeo (cofibreV ι) (cofibreU ι)) y₀) J) :=
    relPiVanishingOfPiInjSurj J ((interHomeo (cofibreV ι) (cofibreU ι)) y₀)
      (fun x y _ => hA.elim x y)
      (fun b => ⟨Classical.arbitrary _, hV.elim _ _⟩)
  have hbridge := subsingleton_relPi_of_homeo
    (g := setIncl {z : ↥(cofibreV ι) | (z : cofibre ι) ∈ cofibreU ι})
    (interHomeo (cofibreV ι) (cofibreU ι)) y₀ J hset
  convert hbridge using 3
  ext x
  rfl

end

end Work.RatHurewicz.Cofibre
