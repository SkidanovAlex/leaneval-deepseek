import Mathlib.Analysis.Calculus.MeanValue
import Submission.Commons.Geometry.Moebius.escape_of_shared_endpoint
import Submission.Commons.Geometry.Euclidean.escape_of_disjoint_segments
import Submission.Commons.LinearAlgebra.CrossProduct.cross_dot_eq_zero_mem_span

/-
# T-pattern escape of disjoint bends

For two perpendicular, coplanar bends `[A(y),B(y)]`, `[A(y+δ),B(y+δ)]` of a band
foliation whose IMAGE segments are disjoint, at least one of the four endpoints of
one bend is at perpendicular distance `> 1` from the line through the other bend's
endpoints.  (The "T-pattern" of the optimal paper Möbius band.)

The proof has three ingredients.

* **The image of a chord is the straight segment between the image endpoints.**
  `f` is `1`-Lipschitz on the (convex) strip and `preBend` says the image chord
  has the length of the preimage chord, so equality holds in the triangle
  inequality along the segment; the inner-product computation in
  `image_segment_affine` turns this into the affine formula
  `f ((1-t)•A + t•B) = (1-t)•f A + t•f B`.
* **Disjointness is inherited by the image segments.**  `hdisj` says that the
  images of the two preimage chords are disjoint; by the previous point these
  images are the straight segments `[f A(y), f B(y)]` and
  `[f A(y+δ), f B(y+δ)]`.
* **Plane geometry of two disjoint segments** (commons
  `Geometry/Euclidean/escape_of_disjoint_segments`): perpendicularity and
  coplanarity of the midpoints put the midpoint difference in the span of the
  two directions (commons `LinearAlgebra/CrossProduct/cross_dot_eq_zero_mem_span`),
  and then disjointness forces one of the two coefficients `α`, `β` to exceed
  `1/2` in absolute value; the corresponding endpoint escapes by
  `(α ± 1/2) • (x₂ - x₁)`, whose norm is `> 1` because `‖x₂ - x₁‖ ≥ 1`.

The interface (`Commons.PaperMoebius.IsMoebiusEmbedding`, `BandFoliation`,
`leafVec`, `imageDir`, `imageMid`) and the supporting lemmas
(`leafVec_ne_zero`, `leafVec_eq_norm_smul`, `inner_imageDir_eq_zero`,
`norm_sq_coord_sum`) live in the commons module
`Submission.Commons.Geometry.Moebius.escape_of_shared_endpoint`.
-/


open Topology ContDiff Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

noncomputable section

namespace Commons.Geometry.Moebius

open Commons.PaperMoebius

/-! ## Elementary analytic facts about the embedding -/

private lemma unitStrip_convex : Convex ℝ unitStrip := by
  unfold unitStrip Convex
  intro x hx y hy a b ha hb hab
  constructor
  · have h1 : 0 ≤ a * (x 0) + b * (y 0) := by
      nlinarith [mul_nonneg ha hx.1, mul_nonneg hb hy.1]
    simpa using h1
  · have h2 : a * (x 0) + b * (y 0) ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]
    simpa using h2

/-- `f` is `1`-Lipschitz on the unit strip: its within-derivative is a linear
isometry, hence of operator norm one. -/
private lemma embedding_lipschitz {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) :
    ∀ ⦃x⦄, x ∈ unitStrip → ∀ ⦃y⦄, y ∈ unitStrip →
      ‖f y - f x‖ ≤ ‖y - x‖ := by
  have hderiv : ∀ x ∈ unitStrip, ∀ v : ℝ²,
      ‖fderivWithin ℝ f unitStrip x v‖ = ‖v‖ := by
    intro x hx v
    exact (hf.isometry x hx).norm_map_of_map_zero (map_zero _) v
  have hop : ∀ x ∈ unitStrip,
      ‖fderivWithin ℝ f unitStrip x‖ ≤ 1 := by
    intro x hx
    rw [ContinuousLinearMap.opNorm_le_iff (by norm_num : (0 : ℝ) ≤ 1)]
    intro v
    rw [hderiv x hx v]
    simp
  intro x hx y hy
  have hle := Convex.norm_image_sub_le_of_norm_fderivWithin_le
    (f := f) (s := unitStrip) (x := x) (y := y)
    (hf.smooth.differentiableOn (by simp)) hop unitStrip_convex hx hy
  simpa using hle

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

/-- **The image of a chord is the straight segment between the image endpoints.**
Because `f` is `1`-Lipschitz on the convex strip and the image chord has the
length of the preimage chord, equality holds in the triangle inequality along
the whole chord, forcing the image to be affine on it. -/
private lemma image_segment_affine {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f)
    {A B : ℝ²} (hA : A ∈ unitStrip) (hB : B ∈ unitStrip)
    (hpre : ‖f B - f A‖ = ‖B - A‖) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    f ((1 - t) • A + t • B) = (1 - t) • f A + t • f B := by
  set v : ℝ² := (1 - t) • A + t • B with hv
  have hvmem : v ∈ unitStrip :=
    (convex_iff_add_mem.mp unitStrip_convex) hA hB
      (by linarith [ht.2]) ht.1 (by ring)
  have h1 : ‖f v - f A‖ ≤ ‖v - A‖ := embedding_lipschitz hf hA hvmem
  have h2 : ‖f B - f v‖ ≤ ‖B - v‖ := embedding_lipschitz hf hvmem hB
  have hvA : v - A = t • (B - A) := by rw [hv]; module
  have hBv : B - v = (1 - t) • (B - A) := by rw [hv]; module
  set L : ℝ := ‖B - A‖ with hL
  have h1' : ‖f v - f A‖ ≤ t * L := by
    calc ‖f v - f A‖ ≤ ‖v - A‖ := h1
      _ = ‖t • (B - A)‖ := by rw [hvA]
      _ = t * L := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have h2' : ‖f B - f v‖ ≤ (1 - t) * L := by
    calc ‖f B - f v‖ ≤ ‖B - v‖ := h2
      _ = ‖(1 - t) • (B - A)‖ := by rw [hBv]
      _ = (1 - t) * L := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
  have hsum : ‖f B - f v‖ + ‖f v - f A‖ = L := by
    have htri : ‖f B - f A‖ ≤ ‖f B - f v‖ + ‖f v - f A‖ := by
      have he : f B - f A = (f B - f v) + (f v - f A) := by abel
      rw [he]; exact norm_add_le _ _
    rw [← hpre]
    linarith
  have hna : ‖f v - f A‖ = t * L := by linarith
  have hnb : ‖f B - f v‖ = (1 - t) * L := by linarith
  set aa : ℝ³ := f v - f A with haa
  set bb : ℝ³ := f B - f v with hbb
  have hna' : ‖aa‖ = t * L := by rw [haa]; exact hna
  have hnb' : ‖bb‖ = (1 - t) * L := by rw [hbb]; exact hnb
  have hab : aa + bb = f B - f A := by rw [haa, hbb]; abel
  have hnab : ‖aa + bb‖ = L := by rw [hab, hpre]
  have hin : inner ℝ aa bb = t * (1 - t) * L ^ 2 := by
    have hexp := norm_add_sq_real aa bb
    rw [hnab, hna', hnb'] at hexp
    nlinarith [hexp]
  have hinner_aab : inner ℝ aa (aa + bb) = t * L ^ 2 := by
    rw [inner_add_right, real_inner_self_eq_norm_sq, hna', hin]; ring
  have hzsq : ‖aa - t • (aa + bb)‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real]
    have e1 : inner ℝ aa (t • (aa + bb)) = t * (t * L ^ 2) := by
      rw [inner_smul_right, hinner_aab]
    have e2 : ‖t • (aa + bb)‖ = t * L := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, hnab]
    rw [e1, show ‖aa‖ = t * L from hna', e2]
    ring
  have hzero : aa - t • (aa + bb) = 0 := by
    have hnorm : ‖aa - t • (aa + bb)‖ = 0 := by
      nlinarith [norm_nonneg (aa - t • (aa + bb))]
    exact norm_eq_zero.mp hnorm
  have haeq : aa = t • (aa + bb) := sub_eq_zero.mp hzero
  have hae : f v - f A = t • (f B - f A) := by
    rw [haa, hbb] at haeq
    have hsimp : f v - f A + (f B - f v) = f B - f A := by abel
    rwa [hsimp] at haeq
  calc f v = f A + (f v - f A) := by abel
    _ = f A + t • (f B - f A) := by rw [hae]
    _ = (1 - t) • f A + t • f B := by module

/-- The unit image direction of a leaf has norm one. -/
private lemma imageDir_unit {a : ℝ} {f : ℝ² → ℝ³}
    {hf : IsMoebiusEmbedding a f} (F : BandFoliation a f hf) (y : ℝ) :
    ‖F.imageDir y‖ = 1 := by
  have hne : ‖F.leafVec y‖ ≠ 0 := norm_ne_zero_iff.mpr (leafVec_ne_zero F y)
  show ‖(‖F.leafVec y‖)⁻¹ • F.leafVec y‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ hne]

/-! ## Main theorem -/

/-- **T-pattern escape of disjoint bends.**  For two perpendicular, coplanar
bends `[A(y),B(y)]`, `[A(y+δ),B(y+δ)]` whose image segments are disjoint, some
endpoint of one bend is at perpendicular distance greater than `1` from the line
through the other bend's endpoints. -/
theorem tpattern_escape_of_disjoint {a : ℝ} {f : ℝ² → ℝ³}
    (hf : Commons.PaperMoebius.IsMoebiusEmbedding a f) (ha : 0 < a)
    (F : Commons.PaperMoebius.BandFoliation a f hf)
    {y δ : ℝ}
    (hdisj : ∀ v w : ℝ², v ∈ Set.range (fun s : ℝ =>
        (1 - s) • (F.chord y).A + s • (F.chord y).B) →
      w ∈ Set.range (fun s : ℝ =>
        (1 - s) • (F.chord (y + δ)).A + s • (F.chord (y + δ)).B) →
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
      have h := EuclideanSpace.inner_eq_star_dotProduct (F.imageDir (y + δ)) (F.imageDir (y + δ))
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
    exact hdisj _ _ ⟨t, rfl⟩ ⟨s, rfl⟩ (by rw [e1, e2])
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