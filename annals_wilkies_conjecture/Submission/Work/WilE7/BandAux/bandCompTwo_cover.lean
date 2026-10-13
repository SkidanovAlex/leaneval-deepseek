/-
  WilE7 (`Work.WilE7.BandAux.bandCompTwo_cover`): coverage of the two-strata band.

  Let `S₁ S₂ : Stratum p (m+1)`, `Z : SemiPf (p+(m+1))`, `C = π_p (connectedComponentIn Z.set u₀)`
  and let `s₁ : Fin k₁ → C → ℝ^{m+1}`, `s₂ : Fin k₂ → C → ℝ^{m+1}` be continuous families of
  sheets lying in `S₁.X.set`, resp. `S₂.X.set`.  Write
  `p₀ = bandPt u₀ (s₁ i x₀) (s₂ j x₀) t₀`, `x₀ = π_p u₀`, for a vertical coordinate `t₀` lying on
  the sheets `s₁ i` and `s₂ j` of the two-strata band `bandS3two Z S₁ S₂`, and let `O` be the
  connected component of `p₀` in `(bandS3two Z S₁ S₂).set`.

  The lemma: every point `y` of the band `{y | Fin.init y ∈ C, s₁ i < y (last) < s₂ j}` is the
  image under `bandExtract` of a point of `O`.

  The argument is the one of `Work.WilE7.BandAux.bandComp_cover` (the one-strata case), with the
  parametrisation `bandPhiTwo` of the two-strata band: `bandHtwo Z s₁ s₂ i j u₀` is preconnected
  (it is the vertical band over the preconnected base component of `Z`, cut by the two continuous
  levels), every one of its points parametrises a point of `bandS3two Z S₁ S₂`, and the image of
  a preconnected set under a continuous map lies in the connected component of the image of any
  of its points (`imageSubsetConnectedComponentIn`).  Choosing a lift `u ∈ connectedComponentIn
  Z.set u₀` of `Fin.init y` and `q = (u, y (Fin.last p))` produces the required point.

  The supporting pieces live in the sibling files
  * `Work.WilE7.BandAux.bandHtwo_preconn`      : preconnectedness of the vertical band,
  * `Work.WilE7.BandAux.bandPhiTwo_mem`        : the parametrised points lie in `bandS3two`,
  * `Work.WilE7.BandAux.continuousOn_bandPhiGen` : continuity of the parametrisation.
-/
import Mathlib
import Submission.Work.WilE7.BandAux.BandDefsTwo
import Submission.Work.WilE7.BandAux.bandBaseTwo
import Submission.Work.WilE7.BandAux.bandCoverTwo_defs
import Submission.Work.WilE7.BandAux.bandHtwo_preconn
import Submission.Work.WilE7.BandAux.bandPhiTwo_mem
import Submission.Work.WilE7.BandAux.continuousOn_bandPhiGen
import Submission.Work.WilE7.imageSubsetConnectedComponentIn

namespace Work.WilE7.BandAux

open Work.WilE7 WilkiesDesign WilkiesDesign.E

theorem bandCompTwo_cover {p m : ℕ} (S₁ S₂ : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (u₀ : Fin (p + (m + 1)) → ℝ) (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k₁ : ℕ) (s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont₁ : ∀ i, ContinuousOn (s₁ i) C)
    (hsub₁ : ∀ i : Fin k₁, ∀ x ∈ C, Fin.append x (s₁ i x) ∈ S₁.X.set)
    (k₂ : ℕ) (s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont₂ : ∀ i, ContinuousOn (s₂ i) C)
    (hsub₂ : ∀ i : Fin k₂, ∀ x ∈ C, Fin.append x (s₂ i x) ∈ S₂.X.set)
    (i : Fin k₁) (j : Fin k₂) (t₀ : ℝ)
    (hp₀ : Work.WilE7.bandPt u₀ (s₁ i (WilkiesDesign.E.projFirst p (m + 1) u₀))
        (s₂ j (WilkiesDesign.E.projFirst p (m + 1) u₀)) t₀
      ∈ (Work.WilE7.bandS3two Z S₁ S₂).set)
    (hlvl : ∀ x ∈ C, (s₁ i x) (Fin.last m) < (s₂ j x) (Fin.last m))
    (y : Fin (p + 1) → ℝ) (hy : Fin.init y ∈ C)
    (h1 : (s₁ i (Fin.init y)) (Fin.last m) < y (Fin.last p))
    (h2 : y (Fin.last p) < (s₂ j (Fin.init y)) (Fin.last m)) :
    ∃ w ∈ connectedComponentIn (Work.WilE7.bandS3two Z S₁ S₂).set
        (Work.WilE7.bandPt u₀ (s₁ i (WilkiesDesign.E.projFirst p (m + 1) u₀))
          (s₂ j (WilkiesDesign.E.projFirst p (m + 1) u₀)) t₀),
      Work.WilE7.bandExtract w = y := by
  classical
  set p₀ : Fin (bandDim p m) → ℝ :=
    bandPt u₀ (s₁ i (projFirst p (m + 1) u₀)) (s₂ j (projFirst p (m + 1) u₀)) t₀ with hp₀def
  have hp₀S3 : p₀ ∈ (bandS3two Z S₁ S₂).set := by rw [hp₀def]; exact hp₀
  obtain ⟨hz1, -, -, -, -, -, -, -, hpv2, hpv2'⟩ := (bandS3two_mem_iff Z S₁ S₂ p₀).mp hp₀S3
  have hu₀Z : u₀ ∈ Z.set := by
    have h := hz1
    rwa [hp₀def, bandZ1_bandPt] at h
  -- the base point of the component lies in the vertical band
  have hLu₀ : bandLevel s₁ i u₀ < (t₀ : EReal) := by
    have h := hpv2
    rw [hp₀def, bandV2_bandPt, bandT_bandPt] at h
    change ((s₁ i (projFirst p (m + 1) u₀)) (Fin.last m) : EReal) < (t₀ : EReal)
    exact EReal.coe_lt_coe_iff.mpr h
  have hLu₀' : (t₀ : EReal) < bandLevel s₂ j u₀ := by
    have h := hpv2'
    rw [hp₀def, bandV2'_bandPt, bandT_bandPt] at h
    change (t₀ : EReal) < ((s₂ j (projFirst p (m + 1) u₀)) (Fin.last m) : EReal)
    exact EReal.coe_lt_coe_iff.mpr h
  have hHbase : ((u₀, t₀) : (Fin (p + (m + 1)) → ℝ) × ℝ) ∈ bandHtwo Z s₁ s₂ i j u₀ := by
    rw [bandHtwo_mem_iff]
    exact ⟨mem_connectedComponentIn hu₀Z, hLu₀, hLu₀'⟩
  have hphi₀ : bandPhiTwo s₁ s₂ i j (u₀, t₀) = p₀ := by
    rw [bandPhiTwo_apply, hp₀def]
  -- the vertical band over the base component is preconnected
  have hHpc : IsPreconnected (bandHtwo Z s₁ s₂ i j u₀) :=
    bandHtwo_preconn Z u₀ C hC k₁ s₁ hcont₁ k₂ s₂ hcont₂ i j hlvl
  -- every parametrised point lies in `bandS3two`
  have hF : ∀ q ∈ bandHtwo Z s₁ s₂ i j u₀,
      bandPhiTwo s₁ s₂ i j q ∈ (bandS3two Z S₁ S₂).set :=
    bandPhiTwo_mem S₁ S₂ Z u₀ C hC k₁ s₁ hsub₁ k₂ s₂ hsub₂ i j
  -- the parametrisation is continuous on the vertical band
  have hcont : ContinuousOn (bandPhiTwo s₁ s₂ i j) (bandHtwo Z s₁ s₂ i j u₀) :=
    continuousOn_bandPhiGen (C := C) (A := bandHtwo Z s₁ s₂ i j u₀)
      (g₁ := s₁ i) (g₂ := s₂ j)
      (fun q hq => by
        rw [bandHtwo_mem_iff] at hq
        rw [hC]
        exact ⟨q.1, hq.1, rfl⟩)
      (hcont₁ i) (hcont₂ j)
  -- choose a lift of `Fin.init y` in the base component of `Z`
  obtain ⟨u, huZc, hux⟩ : ∃ u ∈ bandZc Z u₀, projFirst p (m + 1) u = Fin.init y := by
    rw [hC] at hy
    exact hy
  set q : (Fin (p + (m + 1)) → ℝ) × ℝ := (u, y (Fin.last p)) with hqdef
  have hqH : q ∈ bandHtwo Z s₁ s₂ i j u₀ := by
    rw [bandHtwo_mem_iff]
    refine ⟨?_, ?_, ?_⟩
    · show u ∈ bandZc Z u₀
      exact huZc
    · show bandLevel s₁ i u < (y (Fin.last p) : EReal)
      simp only [bandLevel, hux]
      exact EReal.coe_lt_coe_iff.mpr h1
    · show (y (Fin.last p) : EReal) < bandLevel s₂ j u
      simp only [bandLevel, hux]
      exact EReal.coe_lt_coe_iff.mpr h2
  have hcomp : bandPhiTwo s₁ s₂ i j q ∈ connectedComponentIn (bandS3two Z S₁ S₂).set p₀ := by
    have h := imageSubsetConnectedComponentIn hHpc hcont hHbase hF q hqH
    rwa [hphi₀] at h
  refine ⟨bandPhiTwo s₁ s₂ i j q, hcomp, ?_⟩
  have hz1' : bandZ1 (bandPhiTwo s₁ s₂ i j q) = q.1 := by
    rw [bandPhiTwo_apply, bandZ1_bandPt]
  have hzt : bandT (bandPhiTwo s₁ s₂ i j q) = q.2 := by
    rw [bandPhiTwo_apply, bandT_bandPt]
  rw [bandExtract_eq_snoc, hz1', hzt, hqdef]
  rw [hux]
  exact Fin.snoc_init_self y

end Work.WilE7.BandAux
