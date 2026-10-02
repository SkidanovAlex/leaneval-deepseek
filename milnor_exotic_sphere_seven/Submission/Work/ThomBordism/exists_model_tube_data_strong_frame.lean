import Mathlib
import Submission.Work.PTGeometric.exists_model_tube_data_strong

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The model tube data, with the *specific* reading map of the normal frame

`Work.PTGeometric.exists_model_tube_data_strong` produces, for a genuine tube geometry `G` and a
point `y₀` of the core, a member `i`, a point `z` of the piece, an open neighbourhood `W ∋ y₀` and
a smooth model map `p : ℝ^{8+k+1} → ℝ^{8+k}` with all the properties needed by the source
construction — but the reading map `ℓ : ℝ^{8+k} → ℝ^k` it returns is an arbitrary linear
isomorphism onto the normal space `ν_z` (built from `ContinuousLinearEquiv.ofFinrankEq`), not the
one that the normal-bundle data of the embedding provides.

This file proves the *framed* form: the same data can be produced with
`ℓ = Work.Tubular.readCLM (G.emb i) ND j z`, the reading map in the orthonormal frame
`Work.Tubular.orthFrame (G.emb i) ND j z` of the normal space (`ND : NormalData (Fam i) k (G.emb i).e`
any normal-bundle datum of the embedding, `j` an index of its cover over `z`).  The two extra
conclusions are exactly the defining properties of that reading map:

* it reads the orthonormal frame off as the standard basis of `ℝ^k` (i.e. `ℓ` *is* the frame
  read-out), and
* its kernel on the normal space is trivial.

Both follow from `Work.Tubular.readCLM_insCLM` (the insertion `insCLM` is a right inverse of
`readCLM` on the normal space) and `Work.Tubular.insCLM_single`; no further geometry is involved.
-/

namespace Work.ThomBordism

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

noncomputable section

theorem exists_model_tube_data_strong_frame
    {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (y₀ : EuclideanSpace ℝ (Fin ((8 + k) + 1))) (hy₀ : y₀ 0 = 0)
    (hc : Work.PTGeometric.flatSourceHomotopy8 (k := k)
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y₀ ∈ G.core) :
    ∃ (i : ι) (z : (Fam i).pt)
      (ND : Work.ThomBordism.PontryaginThom.NormalData (Fam i) k (G.emb i).e)
      (j : Work.ThomBordism.PontryaginThom.CoverIdx (Fam i) k)
      (hx : z ∈ ND.D.baseSet j)
      (ℓ : Work.Tubular.Euc (8 + k) →L[ℝ] EuclideanSpace ℝ (Fin k))
      (hpin : ℓ = Work.Tubular.readCLM (G.emb i) ND j z)
      (W : Set (EuclideanSpace ℝ (Fin ((8 + k) + 1))))
      (p : EuclideanSpace ℝ (Fin ((8 + k) + 1)) → Work.Tubular.Euc (8 + k)),
      IsOpen W ∧ y₀ ∈ W ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p W ∧
      (∀ y ∈ W, p y ∈ (G.chart i).openTube) ∧
      p y₀ = (G.emb i).e z ∧
      (∀ (a : Fin k), ℓ (Work.Tubular.orthFrame (G.emb i) ND j z a) = EuclideanSpace.single a 1) ∧
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
  -- the model data from the unframed form
  obtain ⟨i, z, _ℓ₀, W, p, hW, hyW, hsm, htube, hpz, _hker, hsurj, hsingle, hcoord⟩ :=
    Work.PTGeometric.exists_model_tube_data_strong (G := G) m hpow y₀ hy₀ hc
  -- a normal-bundle datum of the member embedding
  obtain ⟨ND⟩ := Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion (V := Fam i) (k := k)
    (G.emb i).e ((G.emb i).smooth.of_le (by simp)) (G.emb i).injective_mfderiv
  refine ⟨i, z, ND, ND.D.indexAt z, ND.D.mem_baseSet_at z,
    Work.Tubular.readCLM (G.emb i) ND (ND.D.indexAt z) z, rfl, W, p, ?_⟩
  refine ⟨hW, hyW, hsm, htube, hpz, ?_, ?_, hsurj, hsingle, hcoord⟩
  · -- the reading map reads the orthonormal frame off as the standard basis
    intro a
    rw [← Work.Tubular.insCLM_single (G.emb i) ND (ND.D.indexAt z) z a,
      Work.Tubular.readCLM_insCLM (G.emb i) ND (ND.D.indexAt z) (ND.D.mem_baseSet_at z)
        (EuclideanSpace.single a 1)]
  · -- the reading map is injective on the normal space
    intro z' hz' h0
    have h := Work.Tubular.insCLM_readCLM_of_mem (G.emb i) ND (ND.D.indexAt z)
      (ND.D.mem_baseSet_at z) hz'
    rw [h0, map_zero] at h
    exact h.symm

end

end Work.ThomBordism
