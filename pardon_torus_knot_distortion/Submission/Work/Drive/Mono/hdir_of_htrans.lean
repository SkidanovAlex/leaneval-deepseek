import Mathlib
import Submission.Work.Drive.EpsForm.SweepGenericity
import Submission.Work.BoxShrink.Pinch.Basic
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.LocalSurface.fderiv_pullback_faceLin_apply_vertexDir
import Submission.Work.Drive.EpsForm.tiltedSweepGenericity_holds

/-!
# The direction into the box at a wall ∩ box-sphere junction

At a point `z` of the box sphere `{boxNorm c σ · = s}` of level `lam` of the sweep height `ℓ`, the
box-sphere trace and the wall trace meet.  For the local model of that junction one needs the
statement `hdir` of `frontier_tiltedLevelRemoved_wallSphereJunction`: at every point `y` of the box
sphere near `z` with `ℓ y = lam` there are points of the *open* box arbitrarily close to `y` with
`ℓ ≥ lam`, i.e. points of the removed set of the level.

The content is the existence of a single point of the open box with `ℓ`-value strictly above `lam`:
if `w ∈ PBox s c σ` has `ℓ w > lam`, then for every `y ∈ closure (PBox s c σ)` with `ℓ y = lam` the
segment `θ • w + (1 - θ) • y` (`θ ∈ (0,1)`) lies in the open box (convexity) and has
`ℓ = θ ℓ w + (1-θ) lam > lam`, and it tends to `y` as `θ → 0`.

The point `w` is found on the *surface*: the two real functions `B = boxNorm c σ ∘ par ψ` and
`H = sweepHeight ψ ℓ` are differentiable at `p` (the parameter of `z`), `B p = s`, `H p = lam`, the
derivative of `B` is nonzero (`hD`) and the derivative of `H` is not a multiple of it (`htrans`).
Hence the derivative of the pair `(B, H)` at `p` is onto, so there is a direction `v` with
`dB_p v < 0 < dH_p v`; for small `t > 0` the point `par ψ (p + t v)` is in the open box and has
`ℓ`-value `> lam`.

Both the two analytic inputs and the convexity are independent of the knot theory: the whole
argument is the local behaviour of two `ℝ`-valued functions near a point.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Filter
open scoped Topology

namespace Work.Drive.Mono

noncomputable section

/-! ## The linear algebra: two independent functionals can be made of opposite signs -/

/-- **Two linear functionals on `ℝ²`, one nonzero and neither a multiple of the other, take values
of opposite signs somewhere.** -/
lemma hdir_exists_neg_pos_of_indep (f g : (ℝ × ℝ) →L[ℝ] ℝ) (hf : f ≠ 0)
    (h : ∀ t : ℝ, g ≠ t • f) : ∃ v : ℝ × ℝ, f v < 0 ∧ 0 < g v := by
  obtain ⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf (ContinuousLinearMap.ext hc)
  set v₁ : ℝ × ℝ := (f v₀)⁻¹ • v₀ with hv₁
  have hfv₁ : f v₁ = 1 := by
    rw [hv₁, map_smul, smul_eq_mul, inv_mul_cancel₀ hv₀]
  have hker : ∃ w : ℝ × ℝ, f w = 0 ∧ g w ≠ 0 := by
    by_contra hc
    push Not at hc
    have hgf : g = (g v₁) • f := by
      refine ContinuousLinearMap.ext (fun u => ?_)
      have hsplit : (f u) • v₁ + (u - (f u) • v₁) = u := by abel
      have hk : f (u - (f u) • v₁) = 0 := by rw [map_sub, map_smul, hfv₁]; ring
      have hgu : g u = g ((f u) • v₁ + (u - (f u) • v₁)) := by rw [hsplit]
      rw [hgu, map_add, map_smul, hc _ hk, add_zero]
      simp only [smul_apply, smul_eq_mul]
      ring
    exact h (g v₁) hgf
  obtain ⟨w, hwf, hwg⟩ := hker
  refine ⟨-v₁ + ((1 + g v₁) / (g w)) • w, ?_, ?_⟩
  · have h1 : f (-v₁) = -1 := by rw [map_neg, hfv₁]
    have h2 : f (((1 + g v₁) / (g w)) • w) = 0 := by rw [map_smul, hwf]; ring
    rw [map_add, h1, h2]
    norm_num
  · have h1 : g (-v₁) = -g v₁ := by rw [map_neg]
    have h2 : g (((1 + g v₁) / (g w)) • w) = 1 + g v₁ := by
      rw [map_smul, smul_eq_mul]
      field_simp
    rw [map_add, h1, h2]
    linarith

/-! ## The one-sided Taylor expansion -/

/-- **A differentiable function decreases along a direction of negative derivative.** -/
lemma hdir_eventually_lt_of_hasFDerivAt {F : ℝ × ℝ → ℝ} {f : ℝ × ℝ →L[ℝ] ℝ} {x v : ℝ × ℝ}
    (hF : HasFDerivAt F f x) (hv : f v < 0) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), F (x + t • v) < F x := by
  have hpath : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hF' : HasFDerivAt F f (x + (0 : ℝ) • v) := by simpa using hF
  have hderiv : HasDerivAt (fun t : ℝ => F (x + t • v)) (f v) 0 := by
    simpa [Function.comp_def] using hF'.comp_hasDerivAt 0 hpath
  have hslope := hderiv.tendsto_slope_zero_right
  have hmem : Set.Iio (0 : ℝ) ∈ 𝓝 (f v) := isOpen_Iio.mem_nhds hv
  filter_upwards [hslope.eventually hmem, self_mem_nhdsWithin] with t ht hpos
  have h1 : t⁻¹ * (F (x + t • v) - F x) < 0 := by simpa using ht
  have h2 : (0 : ℝ) < t := hpos
  have h3 : 0 < t⁻¹ := inv_pos.mpr h2
  nlinarith [h1, h3]

/-- **A differentiable function increases along a direction of positive derivative.** -/
lemma hdir_eventually_gt_of_hasFDerivAt {F : ℝ × ℝ → ℝ} {f : ℝ × ℝ →L[ℝ] ℝ} {x v : ℝ × ℝ}
    (hF : HasFDerivAt F f x) (hv : 0 < f v) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), F x < F (x + t • v) := by
  have hpath : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hF' : HasFDerivAt F f (x + (0 : ℝ) • v) := by simpa using hF
  have hderiv : HasDerivAt (fun t : ℝ => F (x + t • v)) (f v) 0 := by
    simpa [Function.comp_def] using hF'.comp_hasDerivAt 0 hpath
  have hslope := hderiv.tendsto_slope_zero_right
  have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 (f v) := isOpen_Ioi.mem_nhds hv
  filter_upwards [hslope.eventually hmem, self_mem_nhdsWithin] with t ht hpos
  have h1 : 0 < t⁻¹ * (F (x + t • v) - F x) := by simpa using ht
  have h2 : (0 : ℝ) < t := hpos
  have h3 : 0 < t⁻¹ := inv_pos.mpr h2
  nlinarith [h1, h3]

/-! ## Convex combinations with a point of the closed box -/

/-- **The open box is convex, with strictness coming from the interior point.** -/
lemma hdir_convex_combo_mem_PBox {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {y₁ y₂ : R3}
    (h₁ : y₁ ∈ Submission.PBox s c σ)
    (h₂ : ∀ i : Fin 3, |y₂ (σ i) - c (σ i)| ≤ Submission.boxSide i * s)
    {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1) : θ • y₁ + (1 - θ) • y₂ ∈ Submission.PBox s c σ := by
  rw [Submission.mem_PBox] at h₁ ⊢
  intro i
  have h1i : |y₁ (σ i) - c (σ i)| < Submission.boxSide i * s := h₁ i
  have h2i : |y₂ (σ i) - c (σ i)| ≤ Submission.boxSide i * s := h₂ i
  calc |(θ • y₁ + (1 - θ) • y₂) (σ i) - c (σ i)|
      = |θ * (y₁ (σ i) - c (σ i)) + (1 - θ) * (y₂ (σ i) - c (σ i))| := by
        congr 1
        simp
        ring
    _ ≤ |θ * (y₁ (σ i) - c (σ i))| + |(1 - θ) * (y₂ (σ i) - c (σ i))| := abs_add_le _ _
    _ = θ * |y₁ (σ i) - c (σ i)| + (1 - θ) * |y₂ (σ i) - c (σ i)| := by
        rw [abs_mul, abs_mul, abs_of_pos hθ, abs_of_pos (by linarith : (0 : ℝ) < 1 - θ)]
    _ < θ * (Submission.boxSide i * s) + (1 - θ) * (Submission.boxSide i * s) := by
        have hlt : θ * |y₁ (σ i) - c (σ i)| < θ * (Submission.boxSide i * s) :=
          mul_lt_mul_of_pos_left h1i hθ
        have hle : (1 - θ) * |y₂ (σ i) - c (σ i)| ≤ (1 - θ) * (Submission.boxSide i * s) :=
          mul_le_mul_of_nonneg_left h2i (by linarith)
        linarith
    _ = Submission.boxSide i * s := by ring

/-! ## The direction into the box at a wall ∩ box-sphere junction -/

theorem hdir_of_htrans {ψ : Submission.Diffeo} {s u : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {lam : ℝ}
    {z : LeanEval.KnotTheory.PardonDistortion.R3} {p : ℝ × ℝ}
    (hs : 0 < s) (hℓne : ℓ ≠ 0) (hz : Submission.boxNorm c σ z = s) (hzl : ℓ z = lam)
    (hp : Work.BoxShrink.Pinch.par ψ p = z)
    (hD : fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (htrans : ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
      t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : LeanEval.KnotTheory.PardonDistortion.R3, dist y z < δ →
      Submission.boxNorm c σ y = s → ℓ y = lam → ∀ ε : ℝ, 0 < ε →
      ∃ y' : LeanEval.KnotTheory.PardonDistortion.R3, dist y' y < ε ∧
        Submission.boxNorm c σ y' < s ∧ ℓ y' ≥ lam := by
  set B : ℝ × ℝ → ℝ := fun q => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) with hB
  set G : ℝ × ℝ → ℝ := Work.Drive.EpsForm.sweepHeight ψ ℓ with hG
  have hBp : B p = s := by
    rw [hB]
    change Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s
    rw [hp]
    exact hz
  have hGp : G p = lam := by
    rw [hG]
    change ℓ (Work.BoxShrink.Pinch.par ψ p) = lam
    rw [hp, hzl]
  have hfne : fderiv ℝ B p ≠ 0 := by rw [hB]; exact hD
  have hfdB : HasFDerivAt B (fderiv ℝ B p) p := by
    by_cases hd : DifferentiableAt ℝ B p
    · exact hd.hasFDerivAt
    · exact absurd (fderiv_zero_of_not_differentiableAt hd) hfne
  have hGdiff : DifferentiableAt ℝ G p := by
    rw [hG]
    exact ((Work.Drive.EpsForm.sweepHeight_contDiff_two ψ ℓ).contDiffAt).differentiableAt
      (by norm_num)
  have hfdG : HasFDerivAt G (fderiv ℝ G p) p := hGdiff.hasFDerivAt
  have htrans' : ∀ t : ℝ, fderiv ℝ G p ≠ t • fderiv ℝ B p := by
    intro t
    rw [hB, hG]
    exact htrans t
  obtain ⟨vv, hvv1, hvv2⟩ :=
    hdir_exists_neg_pos_of_indep (fderiv ℝ B p) (fderiv ℝ G p) hfne htrans'
  have hBev : ∀ᶠ t in 𝓝[>] (0 : ℝ), B (p + t • vv) < B p :=
    hdir_eventually_lt_of_hasFDerivAt hfdB hvv1
  have hGev : ∀ᶠ t in 𝓝[>] (0 : ℝ), G p < G (p + t • vv) :=
    hdir_eventually_gt_of_hasFDerivAt hfdG hvv2
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ B (p + t • vv) < s ∧ lam < G (p + t • vv) := by
    filter_upwards [self_mem_nhdsWithin, hBev, hGev] with t htpos htB htG
    exact ⟨htpos, by rwa [hBp] at htB, by rwa [hGp] at htG⟩
  obtain ⟨t, htpos, htB, htG⟩ :=
    @Filter.Eventually.exists ℝ _ _ (nhdsGT_neBot (0 : ℝ)) hall
  set w : R3 := Work.BoxShrink.Pinch.par ψ (p + t • vv) with hw
  have hwB : Submission.boxNorm c σ w < s := by
    rw [hB] at htB
    rw [hw]
    simpa using htB
  have hwL : lam < ℓ w := by
    rw [hG] at htG
    change lam < ℓ (Work.BoxShrink.Pinch.par ψ (p + t • vv)) at htG
    rw [hw]
    exact htG
  have hwPBox : w ∈ Submission.PBox s c σ := (Submission.mem_PBox_iff s c σ w).mpr hwB
  refine ⟨1, one_pos, ?_⟩
  intro y _hy1 hy2 hy3 ε hε
  have hybnd : ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s := by
    intro i
    have h1 : Work.Smooth.BoxGeneric.faceNorm c σ i y ≤ Submission.boxNorm c σ y :=
      Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ i y
    rw [hy2] at h1
    rw [Work.Smooth.BoxGeneric.faceNorm_apply, div_le_iff₀ (Submission.boxSide_pos i)] at h1
    linarith [h1]
  have hwy : 0 < ‖w - y‖ := by
    rw [norm_pos_iff]
    intro hzero
    have hwyeq : w = y := sub_eq_zero.mp hzero
    have hlt : Submission.boxNorm c σ y < s := by rw [← hwyeq]; exact hwB
    rw [hy2] at hlt
    exact lt_irrefl s hlt
  set θ : ℝ := min (1 / 2) (ε / (2 * (‖w - y‖ + 1))) with hθ
  have hθpos : 0 < θ := by rw [hθ]; exact lt_min (by norm_num) (by positivity)
  have hθlt : θ < 1 := by
    rw [hθ]
    exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hθε : θ * ‖w - y‖ < ε := by
    rw [hθ]
    have hbound : ε / (2 * (‖w - y‖ + 1)) * ‖w - y‖ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (‖w - y‖ + 1))]
      nlinarith [norm_nonneg (w - y)]
    calc min (1 / 2) (ε / (2 * (‖w - y‖ + 1))) * ‖w - y‖
        ≤ (ε / (2 * (‖w - y‖ + 1))) * ‖w - y‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
      _ < ε := hbound
  refine ⟨θ • w + (1 - θ) • y, ?_, ?_, ?_⟩
  · rw [dist_eq_norm]
    have hsub : θ • w + (1 - θ) • y - y = θ • (w - y) := by module
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hθpos]
    exact hθε
  · exact (Submission.mem_PBox_iff s c σ _).mp
      (hdir_convex_combo_mem_PBox hwPBox hybnd hθpos hθlt)
  · have hsplit : ℓ (θ • w + (1 - θ) • y) = θ * ℓ w + (1 - θ) * ℓ y := by
      simp [map_add, map_smul, smul_eq_mul]
    rw [hsplit, hy3]
    have h1 : θ * lam < θ * ℓ w := mul_lt_mul_of_pos_left hwL hθpos
    linarith

end

end Work.Drive.Mono
