import Submission.Commons.Geometry.Moebius.escape_of_shared_endpoint
import Submission.Commons.Analysis.InnerProduct.exists_perp_decomp
import Submission.Commons.Geometry.Euclidean.escape_of_disjoint_segments
import Submission.Commons.LinearAlgebra.CrossProduct.cross_dot_eq_zero_mem_span
import Submission.Commons.Geometry.Moebius.image_segment_affine

open Topology ContDiff Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

noncomputable section

namespace Commons.Geometry.Moebius

open Commons.PaperMoebius

/-! ## Auxiliary facts -/

private lemma one_le_norm_sub {A B : ℝ²} (hA : A 0 = 0) (hB : B 0 = 1) : 1 ≤ ‖B - A‖ := by
  have h0 : (B - A) 0 = 1 := by simp [hA, hB]
  have hsq : ‖B - A‖ ^ 2 = 1 + ((B - A) 1) ^ 2 := by
    rw [norm_sq_coord_sum, h0]; ring
  nlinarith [sq_nonneg ((B - A) 1), norm_nonneg (B - A)]

private lemma mem_unitStrip_of_left {p : ℝ²} (hp : p 0 = 0) : p ∈ unitStrip := by
  show p 0 ∈ Set.Icc (0 : ℝ) 1
  rw [hp]; exact ⟨le_refl 0, by norm_num⟩

private lemma mem_unitStrip_of_right {p : ℝ²} (hp : p 0 = 1) : p ∈ unitStrip := by
  show p 0 ∈ Set.Icc (0 : ℝ) 1
  rw [hp]; exact ⟨by norm_num, le_refl 1⟩

/-- The unit image direction of a leaf has norm one. -/
private lemma imageDir_unit {a : ℝ} {f : ℝ² → ℝ³}
    {hf : IsMoebiusEmbedding a f} (F : BandFoliation a f hf) (y : ℝ) :
    ‖F.imageDir y‖ = 1 := by
  have hne : ‖F.leafVec y‖ ≠ 0 := norm_ne_zero_iff.mpr (leafVec_ne_zero F y)
  show ‖(‖F.leafVec y‖)⁻¹ • F.leafVec y‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ hne]

/-! ## Main theorem -/

theorem tpattern_escape_of_disjoint_chords {a : ℝ} {f : ℝ² → ℝ³}
    (hf : Commons.PaperMoebius.IsMoebiusEmbedding a f) (ha : 0 < a)
    (F : Commons.PaperMoebius.BandFoliation a f hf)
    {y δ : ℝ}
    (hdisj : ∀ v w : ℝ²,
      (∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧
        v = (1 - s) • (F.chord y).A + s • (F.chord y).B) →
      (∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧
        w = (1 - s) • (F.chord (y + δ)).A + s • (F.chord (y + δ)).B) →
      f v ≠ f w)
    (hδ0 : 0 < δ) (hδa : δ < a)
    (hperp : WithLp.ofLp (F.imageDir y) ⬝ᵥ WithLp.ofLp (F.imageDir (y + δ)) = 0)
    (hcop : WithLp.ofLp (F.imageMid y - F.imageMid (y + δ)) ⬝ᵥ
        (WithLp.ofLp (F.imageDir y) ⨯₃ WithLp.ofLp (F.imageDir (y + δ))) = 0) :
    (∃ c : ℝ, ∃ n : ℝ³,
        f ((F.chord (y + δ)).A) - (1 / 2 : ℝ) • (f ((F.chord y).B) + f ((F.chord y).A))
          = c • (f ((F.chord y).B) - f ((F.chord y).A)) + n ∧
        inner ℝ n (f ((F.chord y).B) - f ((F.chord y).A)) = 0 ∧ 1 < ‖n‖)
    ∨ (∃ c : ℝ, ∃ n : ℝ³,
        f ((F.chord (y + δ)).B) - (1 / 2 : ℝ) • (f ((F.chord y).B) + f ((F.chord y).A))
          = c • (f ((F.chord y).B) - f ((F.chord y).A)) + n ∧
        inner ℝ n (f ((F.chord y).B) - f ((F.chord y).A)) = 0 ∧ 1 < ‖n‖)
    ∨ (∃ c : ℝ, ∃ n : ℝ³,
        f ((F.chord y).A) - (1 / 2 : ℝ) • (f ((F.chord (y + δ)).B) + f ((F.chord (y + δ)).A))
          = c • (f ((F.chord (y + δ)).B) - f ((F.chord (y + δ)).A)) + n ∧
        inner ℝ n (f ((F.chord (y + δ)).B) - f ((F.chord (y + δ)).A)) = 0 ∧ 1 < ‖n‖)
    ∨ (∃ c : ℝ, ∃ n : ℝ³,
        f ((F.chord y).B) - (1 / 2 : ℝ) • (f ((F.chord (y + δ)).B) + f ((F.chord (y + δ)).A))
          = c • (f ((F.chord (y + δ)).B) - f ((F.chord (y + δ)).A)) + n ∧
        inner ℝ n (f ((F.chord (y + δ)).B) - f ((F.chord (y + δ)).A)) = 0 ∧ 1 < ‖n‖) := by
  have hA₁ : (F.chord y).A ∈ unitStrip :=
    mem_unitStrip_of_left (F.chord y).left_coord
  have hB₁ : (F.chord y).B ∈ unitStrip :=
    mem_unitStrip_of_right (F.chord y).right_coord
  have hA₂ : (F.chord (y + δ)).A ∈ unitStrip :=
    mem_unitStrip_of_left (F.chord (y + δ)).left_coord
  have hB₂ : (F.chord (y + δ)).B ∈ unitStrip :=
    mem_unitStrip_of_right (F.chord (y + δ)).right_coord
  have hlen₁ : 1 ≤ ‖f ((F.chord y).B) - f ((F.chord y).A)‖ := by
    rw [F.preBend y]
    exact one_le_norm_sub (F.chord y).left_coord (F.chord y).right_coord
  have hlen₂ : 1 ≤ ‖f ((F.chord (y + δ)).B) - f ((F.chord (y + δ)).A)‖ := by
    rw [F.preBend (y + δ)]
    exact one_le_norm_sub (F.chord (y + δ)).left_coord (F.chord (y + δ)).right_coord
  set ℓ₁ : ℝ := ‖f ((F.chord y).B) - f ((F.chord y).A)‖ with hℓ₁
  set ℓ₂ : ℝ := ‖f ((F.chord (y + δ)).B) - f ((F.chord (y + δ)).A)‖ with hℓ₂
  have hne₁ : ℓ₁ ≠ 0 := by linarith
  have hne₂ : ℓ₂ ≠ 0 := by linarith
  have hvec₁ : f ((F.chord y).B) - f ((F.chord y).A) = ℓ₁ • F.imageDir y := by
    simpa [hℓ₁, BandFoliation.leafVec, BandFoliation.A, BandFoliation.B] using
      leafVec_eq_norm_smul F y
  have hvec₂ : f ((F.chord (y + δ)).B) - f ((F.chord (y + δ)).A) =
      ℓ₂ • F.imageDir (y + δ) := by
    simpa [hℓ₂, BandFoliation.leafVec, BandFoliation.A, BandFoliation.B] using
      leafVec_eq_norm_smul F (y + δ)
  have hunit₁ : ‖F.imageDir y‖ = 1 := imageDir_unit F y
  have hunit₂ : ‖F.imageDir (y + δ)‖ = 1 := imageDir_unit F (y + δ)
  have hinner : inner ℝ (F.imageDir y) (F.imageDir (y + δ)) = 0 := by
    rw [real_inner_comm]
    exact inner_imageDir_eq_zero F hperp
  have hperp_raw : inner ℝ (f ((F.chord y).B) - f ((F.chord y).A))
      (f ((F.chord (y + δ)).B) - f ((F.chord (y + δ)).A)) = 0 := by
    rw [hvec₁, hvec₂, real_inner_smul_left, real_inner_smul_right, hinner]
    ring
  -- ### coplanarity gives the decomposition of the midpoint difference
  have hdecomp : ∃ α β : ℝ,
      F.imageMid y - F.imageMid (y + δ) =
      α • (f ((F.chord y).B) - f ((F.chord y).A)) +
        β • (f ((F.chord (y + δ)).B) - f ((F.chord (y + δ)).A)) := by
    set U := WithLp.ofLp (F.imageDir y) with hU
    set V := WithLp.ofLp (F.imageDir (y + δ)) with hV
    set DD := WithLp.ofLp (F.imageMid y - F.imageMid (y + δ)) with hDD
    have hU1 : U ⬝ᵥ U = 1 := by
      have h := EuclideanSpace.inner_eq_star_dotProduct (F.imageDir y) (F.imageDir y)
      simp only [star_trivial] at h
      rw [← h, real_inner_self_eq_norm_sq, hunit₁]
      norm_num
    have hV1 : V ⬝ᵥ V = 1 := by
      have h := EuclideanSpace.inner_eq_star_dotProduct (F.imageDir (y + δ))
        (F.imageDir (y + δ))
      simp only [star_trivial] at h
      rw [← h, real_inner_self_eq_norm_sq, hunit₂]
      norm_num
    have hcross : DD ⬝ᵥ (U ⨯₃ V) = 0 := hcop
    have hUV : U ⬝ᵥ V = 0 := hperp
    have hB := Commons.LinearAlgebra.CrossProduct.cross_dot_eq_zero_mem_span hU1 hV1 hUV hcross
    have hunit : F.imageMid y - F.imageMid (y + δ) =
        (DD ⬝ᵥ U) • F.imageDir y + (DD ⬝ᵥ V) • F.imageDir (y + δ) := by
      have h := congrArg (WithLp.toLp 2) hB
      simpa using h
    refine ⟨(DD ⬝ᵥ U) / ℓ₁, (DD ⬝ᵥ V) / ℓ₂, ?_⟩
    rw [hunit, hvec₁, hvec₂, smul_smul, smul_smul, div_mul_cancel₀ _ hne₁,
      div_mul_cancel₀ _ hne₂]
  -- ### disjointness of the two image segments
  have himgDisj : ∀ z : ℝ³,
      z ∈ segment ℝ (f ((F.chord y).A)) (f ((F.chord y).B)) →
      z ∈ segment ℝ (f ((F.chord (y + δ)).A)) (f ((F.chord (y + δ)).B)) → False := by
    intro z hz₁ hz₂
    rw [segment_eq_image] at hz₁ hz₂
    obtain ⟨t, ht, hzt⟩ := hz₁
    obtain ⟨s, hs, hzs⟩ := hz₂
    have e1 : f ((1 - t) • (F.chord y).A + t • (F.chord y).B) = z := by
      rw [image_segment_affine hf hA₁ hB₁ (F.preBend y) ht, ← hzt]
    have e2 : f ((1 - s) • (F.chord (y + δ)).A + s • (F.chord (y + δ)).B) = z := by
      rw [image_segment_affine hf hA₂ hB₂ (F.preBend (y + δ)) hs, ← hzs]
    exact hdisj _ _
      ⟨t, ht, rfl⟩
      ⟨s, hs, rfl⟩
      (by rw [e1, e2])
  -- ### the abstract escape
  rcases Commons.Geometry.Euclidean.escape_of_disjoint_segments
      (x₁ := f ((F.chord y).A)) (x₂ := f ((F.chord y).B))
      (x₃ := f ((F.chord (y + δ)).A)) (x₄ := f ((F.chord (y + δ)).B))
      himgDisj hdecomp hperp_raw hlen₁ hlen₂ with
    ⟨c, n, h1, h2, h3⟩ | ⟨c, n, h1, h2, h3⟩ | ⟨c, n, h1, h2, h3⟩ | ⟨c, n, h1, h2, h3⟩
  · exact Or.inl ⟨c, n, by
      rw [add_comm (f ((F.chord y).B)) (f ((F.chord y).A))]; exact h1, h2, h3⟩
  · exact Or.inr (Or.inl ⟨c, n, by
      rw [add_comm (f ((F.chord y).B)) (f ((F.chord y).A))]; exact h1, h2, h3⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, n, by
      rw [add_comm (f ((F.chord (y + δ)).B)) (f ((F.chord (y + δ)).A))]; exact h1, h2, h3⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨c, n, by
      rw [add_comm (f ((F.chord (y + δ)).B)) (f ((F.chord (y + δ)).A))]; exact h1, h2, h3⟩))

end Commons.Geometry.Moebius
