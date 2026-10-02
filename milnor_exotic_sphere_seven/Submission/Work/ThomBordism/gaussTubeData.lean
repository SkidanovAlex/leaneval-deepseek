import Mathlib
import Submission.Work.ThomBordism.tubeConnProved
import Submission.Work.PTGeometric.AmbientCoords
import Submission.Work.PTGeometric.TubeAmbient
import Submission.Work.PTGeometric.PadAmb
import Submission.Work.Tubular.Gauss
import Submission.Work.ThomBordism._gtd.P4
import Submission.Work.ThomBordism.gtdFrameProj_padEuc
import Submission.Work.ThomBordism._gtd.A0

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The per-member Gauss/tube data of the Pontryagin–Thom construction

The target below is the **geometry producer** demanded by area PTGEOMETRIC: for a connected closed
oriented smooth `8`-manifold `V`, an embedding `E : V ↪ ℝ^{8+k}` (`k ≥ 11` odd), a tube chart `C`
with its metric-free collapse `g`, it produces the Gauss/classifying map
`J : ν⁺ → Th γ_{k,10}` **whose coordinates are the tube data** (the plane is
`padEndEuc (tubeNormalProj E C y)` and the vector is `padEuc ((normalBlowUp E ε (C.inv y)).1.2)`),
together with a `TubeThomRep` whose collapse *is* TUBULAR's concrete collapse
`alphaV C hR hbox D.t₀ J hJ g hg`.

## Status (see `Submission/Work/ThomBordism/NOTE_gaussTubeData.md` for the full route)

Proved and importable (see the two imports above, plus the module `_gtd/P1`–`_gtd/P4`):

* `Work.ThomBordism.Grassmann.ogFlip` — the orientation reversal of a plane (the explicit analogue
  of `Gauss.ogIncl`); `projOfPlane_ogFlip` (the projection is orientation-blind), `ogFlip_idem`;
* `Work.ThomBordism.Grassmann.span_gframe` — the σ-corrected frame spans the normal space;
* `Work.ThomBordism.Grassmann.padGaussFun` (with `padGFrame`, `padGaussStiefel`,
  `padGaussFun_eq`, `continuous_padGaussFun`) — the **explicitly padded** Gauss map
  `V → G̃r_k(ℝ^{k+10})`, avoiding the opaque `Classical.choose`-padding of
  `gaussClassifyingNDPad`;
* `Work.ThomBordism.Grassmann.projOfPlane_padGauss` — **the plane identity**: the projection of the
  padded Gauss plane is `padEndEuc` of the orthogonal projection onto `normalSpace E x` (this is the
  hard geometric input of the coordinate clause of the target);
* `Work.ThomBordism.gtdFrameProj_padEuc` — the padding/‖·‖-compatibility of `frameProj`.

Delegated (in flight; import and use):
`Work.ThomBordism.gtdThomClass_flipPairs` (the orientation flip negates the tautological Thom class),
`Work.ThomBordism.gtdGaussCandidate` (the candidate bundle map `G`/one-point extension `J` with the
plane/vector/nonzero fields and the fibrewise clause), `Work.ThomBordism.gtdNuPairing` (the two
ν-side pairing identities from the local-degree characterisation of the class `gtdU`).

## How the pieces assemble

Let `ND` be the normal data of `E` (`exists_normalData_of_immersion`).  The candidate maps are built
from `padGaussFun E ND` (plain) and `ogFlip k 10 ∘ padGaussFun E ND` (orientation flipped); both
satisfy the fibrewise clause of the target (`gtdGaussCandidate`).  Their classes
`gtdU E ND G hgm` are generators of the free rank-one module `H^k(ν,ν∖0)`, so each is `±U_gen` for
the local-degree class `U_gen` of `localDegreeSpan`; by the flip lemma the two classes are opposite,
so **one** of the two candidates has class `U_gen`, and for that candidate `gtdNuPairing` gives the
two pairings.  `Work.Tubular.tubeThomRep_of_nuPairing` then produces the representative with the
required collapse, and the target follows (the fibrewise clause is the `gtdGaussCandidate` one,
transported along `eucNormalHomeomorph`).
-/

namespace Work.ThomBordism

theorem gaussTubeData {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 11 ≤ k) (hodd : Odd k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (N : Work.ThomBordism.PontryaginThom.NormalBundlData V)
    {ε : ℝ} (hε : 0 < ε) (C : Work.Tubular.TubeChart E ε)
    (q : Work.Tubular.NormalSphSub E ε) (hU : IsCompact C.U)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))) :
    ∃ (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
        G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
      (hldLD : ∀ x : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)),
        Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E) (k + 8)
          ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
            (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k x
            (Work.ThomBordism.gtdU E ND G hgm)))
          (Work.Tubular.collapseRelK8 C g hg hR hbox)
        = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
            ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom x) V.c)
      (J : C(OnePoint (Work.Tubular.NormalTotal E),
        (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).T))
      (hJ : J OnePoint.infty =
        (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).t₀)
      (rep : Work.Tubular.TubeThomRep k
        (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))) V N),
      rep.collapse = GenLoop.congr
        (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).t₀
        (finCongr (Nat.add_comm 8 k))
        (Work.Tubular.alphaV C hR hbox
          (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))).t₀
          J hJ g hg) ∧
      (∀ y ∈ C.openTube, ∃ p : (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace,
        J (OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))) = OnePoint.some p ∧
        Work.PTGeometric.projOfPlane k 10
            ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj p) =
          Work.PTGeometric.padEndEuc k 10 (by norm_num) (Work.PTGeometric.tubeNormalProj E C y) ∧
        Work.ThomBordism.Grassmann.evalVec p =
          Work.PTGeometric.padEuc k 10 (by norm_num)
            ((Work.Tubular.normalBlowUp E ε (C.inv y)).1.2) ∧
        p = G (Work.Tubular.normalToBundle E ND
          (Work.Tubular.normalBlowUp E ε (C.inv y)))) ∧
      ∃ (σ : ℤ), (σ = 1 ∨ σ = -1) ∧
        (∀ p : (Work.Tubular.normalBundle E ND).TotalSpace,
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
            = (if σ = 1 then id else Work.ThomBordism.Grassmann.ogFlip k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND p.1)) ∧
        (∀ p : (Work.Tubular.normalBundle E ND).TotalSpace,
          Work.ThomBordism.Grassmann.evalVec (G p)
            = Work.PTGeometric.padEuc k 10 (by norm_num)
                (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p))) := by
  exact gaussTubeDataAux (V := V) (k := k) hk hodd E N hε C q hU hR hbox g hg hg2

end Work.ThomBordism
