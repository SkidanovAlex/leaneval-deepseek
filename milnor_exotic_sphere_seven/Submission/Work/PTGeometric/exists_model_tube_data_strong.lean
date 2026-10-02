import Mathlib
import Submission.Work.PTGeometric.exists_model_submersion_at_mem_core

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.PTGeometric

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

variable {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}

theorem exists_model_tube_data_strong {k : ℕ}
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (y₀ : EuclideanSpace ℝ (Fin ((8 + k) + 1))) (hy₀ : y₀ 0 = 0)
    (hc : Work.PTGeometric.flatSourceHomotopy8 (k := k)
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y₀ ∈ G.core) :
    ∃ (i : ι) (z : (Fam i).pt)
      (ℓ : Work.Tubular.Euc (8 + k) →L[ℝ] EuclideanSpace ℝ (Fin k))
      (W : Set (EuclideanSpace ℝ (Fin ((8 + k) + 1))))
      (p : EuclideanSpace ℝ (Fin ((8 + k) + 1)) → Work.Tubular.Euc (8 + k)),
      IsOpen W ∧ y₀ ∈ W ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p W ∧
      (∀ y ∈ W, p y ∈ (G.chart i).openTube) ∧
      p y₀ = (G.emb i).e z ∧
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
  obtain ⟨k₀, j₀, hj₀, iχ, hiχ, hk₀, hξlo, hξhi, hηlo, hηhi, htube₀, z, hzy₀⟩ :=
    exists_block_data (G := G) m hpow y₀ hy₀ hc
  have hR : G.R ≠ 0 := ne_of_gt (tube_radius_pos (G := G) iχ)
  let ν : Submodule ℝ (Work.Tubular.Euc (8 + k)) := Work.Tubular.normalSpace (G.emb iχ) z
  have hfr : Module.finrank ℝ ν = k := by
    rw [show ν = Work.Tubular.normalSpace (G.emb iχ) z from rfl,
      Work.Tubular.finrank_normalSpace]
    omega
  let eL : ν ≃L[ℝ] EuclideanSpace ℝ (Fin k) :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := ν) (F := EuclideanSpace ℝ (Fin k))
      (by rw [hfr, finrank_euclideanSpace_fin])
  let ℓ : Work.Tubular.Euc (8 + k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    eL.toContinuousLinearMap.comp ν.orthogonalProjectionOnto
  let p : EuclideanSpace ℝ (Fin ((8 + k) + 1)) → Work.Tubular.Euc (8 + k) :=
    modelEuc G (cZero k) (cOne k) k₀ j₀
  refine ⟨iχ, z, ℓ, localSet G k₀ j₀ iχ, p, ?_⟩
  have hpz : p y₀ = (G.emb iχ).e z := hzy₀
  have hWopen : IsOpen (localSet G k₀ j₀ iχ) := isOpen_localSet G k₀ j₀ iχ
  have hy₀W : y₀ ∈ localSet G k₀ j₀ iχ :=
    ⟨by rw [hy₀]; norm_num, hξlo, hξhi, hηlo, hηhi, htube₀⟩
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p (localSet G k₀ j₀ iχ) :=
    (contMDiff_iff_contDiff.mp (contMDiff_modelEuc G (cZero k) (cOne k) k₀ j₀)).contDiffOn.mono
      (fun _ _ => trivial)
  have htubeW : ∀ y ∈ localSet G k₀ j₀ iχ, p y ∈ (G.chart iχ).openTube :=
    fun y hy => hy.2.2.2.2.2
  refine ⟨hWopen, hy₀W, hsm, htubeW, hpz, ?_, ?_, ?_, ?_⟩
  · -- the kernel of `ℓ` meets the normal space trivially
    intro z' hz' hz'0
    have h1 : ℓ z' = eL.toContinuousLinearMap ⟨z', hz'⟩ := by
      rw [show ℓ z' = eL.toContinuousLinearMap (ν.orthogonalProjectionOnto z') from rfl,
        Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨z', hz'⟩]
    rw [h1] at hz'0
    have h2 : eL ⟨z', hz'⟩ = 0 := hz'0
    have h3 : (⟨z', hz'⟩ : ν) = 0 := LinearEquiv.map_eq_zero_iff eL.toLinearEquiv |>.1 h2
    simpa using congrArg Subtype.val h3
  · -- surjectivity of the derivative at every point of the local set
    intro y _
    exact fderiv_modelEuc_surjective (G := G) k₀ j₀ hR y
  · -- the time direction is killed by the derivative at every point of the local set
    intro y _
    exact fderiv_modelEuc_single_zero (G := G) k₀ j₀ y
  · -- the coordinate identity on `localSet`
    intro y hy h
    have hblock : alphaFamily (D := D) (Fam := Fam) G m (collPt k y)
        = (G.rep iχ).collapse (clipPt k (cZero k) (cOne k) k₀ j₀ y) := by
      rw [hiχ]
      exact alphaFamily_eq_collapse_of_block (G := G) m k₀ j₀ hk₀ hj₀ y hy.2.1 hy.2.2.1
        hy.2.2.2.1 hy.2.2.2.2.1
    exact coord_eq_model (G := G) hpow k₀ j₀ iχ y hy.1 hy.2.2.2.2.2 hblock hy.2.1 hy.2.2.1
      hy.2.2.2.1 hy.2.2.2.2.1 h

end

end Work.PTGeometric
