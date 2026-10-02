import Mathlib
import Submission.Work.PTGeometric.exists_model_tube_data_strong
import Submission.Work.Tubular.exists_euclidean_normalBundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The normal data of a piece recorded by the *tie*, and the tube model pinned to its frame

`Work.PTGeometric.GenuineTubeGeometry` carries, for every piece `i`, the field

`tie i : TiedGaussNormal ... (pulledThom i) mU hmU gauss`

which asserts that the Thom class `pulledThom i` of the piece is the `gtdU` of an *explicit* normal
datum `ND`, and that the oriented Gauss data of the collapse are the padded Gauss plane of that same
`ND` (up to `ogFlip`).  This file names that normal datum (`tiedND`) and proves the tube-model datum
`Work.PTGeometric.exists_model_tube_data_strong` with the reading map pinned to the *frame*
`Work.Tubular.readCLM (G.emb i) (tiedND G i) j z` of that normal datum.

This is the tie-aware form of `Work.ThomBordism.exists_model_tube_data_strong_frame` (which pins the
reading map to the frame of an *arbitrary* normal datum): the consumer of the source construction
(`Work.ThomBordism.sourceRawAmbientData_tied`) needs the prescribed charts of the produced ambient
data to be the frame coordinates of the normal data **whose Thom class is `pulledThom`**, so that
the induced coorientation of the level set can be compared with the piece's given orientation class
through TUBULAR's local degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.ThomBordism

noncomputable section

/-- **The normal data of the piece `i` recorded by the tie of `G`.**  `G.tie i` is the existential
assertion that `pulledThom i` is the `gtdU` of some normal datum; this is that datum. -/
def tiedND {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8} (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam)
    (i : ι) : Work.ThomBordism.PontryaginThom.NormalData (Fam i) k (G.emb i).e :=
  Classical.choose (G.tie i)

/-- **The model tube data, with the reading map pinned to the frame of the tied normal data.**

Same conclusion as `Work.PTGeometric.exists_model_tube_data_strong`, with the reading map
`ℓ = Work.Tubular.readCLM (G.emb i) (tiedND G i) j z` (the frame coordinates of the orthonormal
frame `Work.Tubular.orthFrame (G.emb i) (tiedND G i) j z` of the normal space at the foot `z`). -/
theorem exists_model_tube_data_strong_frame_tied
    {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (y₀ : EuclideanSpace ℝ (Fin ((8 + k) + 1))) (hy₀ : y₀ 0 = 0)
    (hc : Work.PTGeometric.flatSourceHomotopy8 (k := k)
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y₀ ∈ G.core) :
    ∃ (i : ι) (z : (Fam i).pt)
      (j : Work.ThomBordism.PontryaginThom.CoverIdx (Fam i) k)
      (hx : z ∈ (Work.ThomBordism.tiedND G i).D.baseSet j)
      (ℓ : Work.Tubular.Euc (8 + k) →L[ℝ] EuclideanSpace ℝ (Fin k))
      (hpin : ℓ = Work.Tubular.readCLM (G.emb i) (Work.ThomBordism.tiedND G i) j z)
      (W : Set (EuclideanSpace ℝ (Fin ((8 + k) + 1))))
      (p : EuclideanSpace ℝ (Fin ((8 + k) + 1)) → Work.Tubular.Euc (8 + k)),
      IsOpen W ∧ y₀ ∈ W ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p W ∧
      (∀ y ∈ W, p y ∈ (G.chart i).openTube) ∧
      p y₀ = (G.emb i).e z ∧
      (∀ (a : Fin k), ℓ (Work.Tubular.orthFrame (G.emb i) (Work.ThomBordism.tiedND G i) j z a) =
        EuclideanSpace.single a 1) ∧
      (∀ z' ∈ Work.Tubular.normalSpace (G.emb i) z, ℓ z' = 0 → z' = 0) ∧
      (∀ y ∈ W, Function.Surjective (fderiv ℝ p y)) ∧
      (∀ y ∈ W, fderiv ℝ p y (PiLp.single 2 (0 : Fin ((8 + k) + 1)) 1) = 0) ∧
      (∀ y ∈ W, ∀ (h : Work.PTGeometric.flatSourceHomotopy8 (k := k)
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y ≠ D.t₀),
        G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
            (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
            (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y, h⟩ =
          (Work.PTGeometric.padEndEuc k G.mU G.hmU
              (Work.PTGeometric.tubeNormalProj (G.emb i) (G.chart i) (p y)),
           Work.PTGeometric.padEuc k G.mU G.hmU
              (Work.PTGeometric.tubeNormalCoord (G.emb i) (G.chart i) (p y)))) := by
  classical
  obtain ⟨i, z, _ℓ₀, W, p, hW, hyW, hsm, htube, hpz, _hker, hsurj, hsingle, hcoord⟩ :=
    Work.PTGeometric.exists_model_tube_data_strong (G := G) m hpow y₀ hy₀ hc
  let ND : Work.ThomBordism.PontryaginThom.NormalData (Fam i) k (G.emb i).e :=
    Work.ThomBordism.tiedND G i
  refine ⟨i, z, ND.D.indexAt z, ND.D.mem_baseSet_at z,
    Work.Tubular.readCLM (G.emb i) ND (ND.D.indexAt z) z, rfl, W, p, ?_⟩
  refine ⟨hW, hyW, hsm, htube, hpz, ?_, ?_, hsurj, hsingle, hcoord⟩
  · intro a
    rw [← Work.Tubular.insCLM_single (G.emb i) ND (ND.D.indexAt z) z a,
      Work.Tubular.readCLM_insCLM (G.emb i) ND (ND.D.indexAt z) (ND.D.mem_baseSet_at z)
        (EuclideanSpace.single a 1)]
  · intro z' hz' h0
    have h := Work.Tubular.insCLM_readCLM_of_mem (G.emb i) ND (ND.D.indexAt z)
      (ND.D.mem_baseSet_at z) hz'
    rw [h0, map_zero] at h
    exact h.symm

end

end Work.ThomBordism
