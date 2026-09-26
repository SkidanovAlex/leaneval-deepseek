import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.LocalSurface.fderiv_pullback_faceLin_apply_vertexDir
import Submission.Work.Smooth.OneManifold.Plane.Basic

/-!
# The box-norm/face-plane corner at a sphere/face junction: vocabulary

At a point `z` of the surface which lies simultaneously on the box sphere
(`boxNorm c σ z = s`) and on the upper face of the tilted slab
(`inner ℝ v z = inner ℝ v c + u + h`), and strictly behind the level wall
(`ℓ z < lam`), the removed set of the level is, near `z`, the intersection
`PBox ∩ {inner ℝ v · > inner ℝ v c + u + h}`; its frontier is the "corner"
`∂PBox ∩ cl{inner ℝ v · > a + h}` ∪ `{inner ℝ v · = a + h} ∩ cl PBox`.

This file collects the pulled-back functions in which that corner is read in the parameter
plane of the surface, together with the elementary lemmas about them:

* `boxH` — the pulled-back box norm shifted by `s`;
* `faceW i ε` — the pulled-back signed face `(i, ε)` shifted by `s`;
* `faceMaxW i` — the maximum of the two pulled-back signed faces of `i` (the pulled-back face
  norm shifted by `s`);
* `planeG` — the pulled-back slab-face coordinate `⟪v, ·⟫ - (⟪v,c⟫ + u + h)`.

The pointwise identity `boxH = max (max (faceMaxW 0) (faceMaxW 1)) (faceMaxW 2)` is the exact
statement that the box norm is the maximum of the three face norms, and
`fderiv_faceW_apply` computes the derivative of a pulled-back signed face.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Filter
open scoped Topology

namespace Work.Drive.Mono

noncomputable section

/-- The pulled-back box norm, shifted by the level `s`:
`q ↦ boxNorm c σ (par ψ q) - s`. -/
def boxH (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) : ℝ × ℝ → ℝ :=
  fun q => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) - s

/-- The pulled-back signed face `(i, ε)`, shifted by the level `s`:
`q ↦ ε * (par ψ q (σ i) - c (σ i)) / boxSide i - s`. -/
def faceW (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    (ε : ℝ) : ℝ × ℝ → ℝ :=
  fun q => Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.BoxShrink.Pinch.par ψ q) - s

/-- The maximum of the two pulled-back signed faces of `i` — the pulled-back face norm of `i`,
shifted by the level `s`. -/
def faceMaxW (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    ℝ × ℝ → ℝ :=
  fun q => max (faceW ψ s c σ i 1 q) (faceW ψ s c σ i (-1) q)

/-- The pulled-back slab-face coordinate: `q ↦ ⟪v, par ψ q⟫ - (⟪v,c⟫ + u + h)`. -/
def planeG (ψ : Submission.Diffeo) (c : R3) (v : R3) (u h : ℝ) : ℝ × ℝ → ℝ :=
  fun q => inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u + h)

@[simp] theorem boxH_apply (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (q : ℝ × ℝ) :
    boxH ψ s c σ q = Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) - s := rfl

@[simp] theorem faceW_apply (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) (ε : ℝ) (q : ℝ × ℝ) :
    faceW ψ s c σ i ε q = Work.Smooth.BoxGeneric.faceLin c σ i ε
      (Work.BoxShrink.Pinch.par ψ q) - s := rfl

@[simp] theorem faceMaxW_apply (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (q : ℝ × ℝ) :
    faceMaxW ψ s c σ i q = max (faceW ψ s c σ i 1 q) (faceW ψ s c σ i (-1) q) := rfl

@[simp] theorem planeG_apply (ψ : Submission.Diffeo) (c : R3) (v : R3) (u h : ℝ)
    (q : ℝ × ℝ) :
    planeG ψ c v u h q = inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u + h) :=
  rfl

/-- `max (a - c) (b - c) = max a b - c`. -/
theorem max_sub_right (a b c : ℝ) : max (a - c) (b - c) = max a b - c := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, ← max_add]

/-- The pulled-back face norm of `i`, shifted by `s`, is the maximum of the two pulled-back
signed faces. -/
theorem faceMaxW_eq_faceNorm (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (q : ℝ × ℝ) :
    faceMaxW ψ s c σ i q =
      Work.Smooth.BoxGeneric.faceNorm c σ i (Work.BoxShrink.Pinch.par ψ q) - s := by
  unfold faceMaxW faceW
  rw [Work.Smooth.BoxGeneric.faceNorm_eq_max_faceLin, max_sub_right]

/-- **The box norm is the maximum of the three face norms**, in the parameter plane. -/
theorem boxH_eq_max_three (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (q : ℝ × ℝ) :
    boxH ψ s c σ q = max (max (faceMaxW ψ s c σ 0 q) (faceMaxW ψ s c σ 1 q))
      (faceMaxW ψ s c σ 2 q) := by
  rw [boxH_apply, faceMaxW_eq_faceNorm, faceMaxW_eq_faceNorm, faceMaxW_eq_faceNorm]
  rw [max_sub_right, max_sub_right, ← Work.Smooth.BoxGeneric.boxNorm_eq_max_faceNorm]

/-- A pulled-back signed face is at most the pulled-back box norm. -/
theorem faceW_le_boxH (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (q : ℝ × ℝ) :
    faceW ψ s c σ i ε q ≤ boxH ψ s c σ q := by
  have hle : faceW ψ s c σ i ε q ≤ faceMaxW ψ s c σ i q := by
    rcases hε with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  have h2 : faceMaxW ψ s c σ i q ≤ max (max (faceMaxW ψ s c σ 0 q) (faceMaxW ψ s c σ 1 q))
      (faceMaxW ψ s c σ 2 q) := by
    fin_cases i
    · exact le_trans (le_max_left _ _) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
    · exact le_max_right _ _
  rw [boxH_eq_max_three]
  exact le_trans hle h2

/-- The pulled-back signed faces are `C^∞`. -/
theorem contDiff_faceW (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (faceW ψ s c σ i ε) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (Work.Smooth.BoxGeneric.faceLin c σ i ε) :=
    Work.Smooth.BoxGeneric.contDiff_faceLin c σ i ε
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (Work.BoxShrink.Pinch.par ψ) :=
    Work.BoxShrink.Pinch.par_contDiff ψ
  have h3 : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => Work.Smooth.BoxGeneric.faceLin c σ i ε
        (Work.BoxShrink.Pinch.par ψ q)) := h1.comp h2
  exact h3.sub contDiff_const

/-- The derivative of a pulled-back signed face, evaluated on a direction of the parameter
plane. -/
theorem fderiv_faceW_apply (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (p v : ℝ × ℝ) :
    (fderiv ℝ (faceW ψ s c σ i ε) p) v =
      ε * ((fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p v) (σ i) / Submission.boxSide i) := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (Work.Smooth.BoxGeneric.faceLin c σ i ε) :=
    Work.Smooth.BoxGeneric.contDiff_faceLin c σ i ε
  have hcd' : ContDiff ℝ (⊤ : ℕ∞) (Work.BoxShrink.Pinch.par ψ) :=
    Work.BoxShrink.Pinch.par_contDiff ψ
  have hdiff : DifferentiableAt ℝ (Work.BoxShrink.Pinch.par ψ) p :=
    (hcd'.differentiable (by simp)).differentiableAt
  have hdiff2 : DifferentiableAt ℝ (Work.Smooth.BoxGeneric.faceLin c σ i ε)
      (Work.BoxShrink.Pinch.par ψ p) :=
    (hcd.differentiable (by simp)).differentiableAt
  have hchain : fderiv ℝ (fun q : ℝ × ℝ => Work.Smooth.BoxGeneric.faceLin c σ i ε
      (Work.BoxShrink.Pinch.par ψ q)) p =
      (fderiv ℝ (Work.Smooth.BoxGeneric.faceLin c σ i ε) (Work.BoxShrink.Pinch.par ψ p)).comp
        (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p) :=
    (hdiff2.hasFDerivAt.comp p hdiff.hasFDerivAt).fderiv
  have hsub : fderiv ℝ (faceW ψ s c σ i ε) p =
      fderiv ℝ (fun q : ℝ × ℝ => Work.Smooth.BoxGeneric.faceLin c σ i ε
        (Work.BoxShrink.Pinch.par ψ q)) p := fderiv_sub_const s
  rw [hsub, hchain, ContinuousLinearMap.comp_apply,
    Work.Smooth.BoxGeneric.LocalSurface.fderiv_faceLin_apply]

/-! ## Elementary linear algebra of two linear functionals on the plane

The two lemmas below are the algebraic input of the corner analysis: a pair of functionals
`L, M : ℝ² →L[ℝ] ℝ` with `M ≠ 0` and `L` not a multiple of `M` has invertible product (and every
pair of values `(a, b)` is attained), by Cramer's rule. -/

/-- A continuous linear functional on `ℝ × ℝ` is determined by its values on the standard basis. -/
theorem clm_apply_eq (L : (ℝ × ℝ) →L[ℝ] ℝ) (v : ℝ × ℝ) :
    L v = L (1, 0) * v.1 + L (0, 1) * v.2 := by
  conv_lhs => rw [show v = v.1 • ((1,0) : ℝ × ℝ) + v.2 • ((0,1) : ℝ × ℝ) from by ext <;> simp]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- If `M ≠ 0` and `L` is not a multiple of `M`, the determinant of the matrix of the two
functionals in the standard basis does not vanish. -/
theorem det_ne_zero_of_forall_ne_smul {L M : (ℝ × ℝ) →L[ℝ] ℝ} (hM : M ≠ 0)
    (h : ∀ t : ℝ, L ≠ t • M) :
    L (1,0) * M (0,1) - L (0,1) * M (1,0) ≠ 0 := by
  intro h0
  have hm : (M (1,0), M (0,1)) ≠ 0 := by
    intro hz
    have h1 : M (1,0) = 0 := by simpa using congrArg Prod.fst hz
    have h2 : M (0,1) = 0 := by simpa using congrArg Prod.snd hz
    apply hM
    apply ContinuousLinearMap.ext
    intro v
    rw [clm_apply_eq M v, h1, h2]
    simp
  obtain ⟨t, ht1, ht2⟩ : ∃ t : ℝ, L (1,0) = t * M (1,0) ∧ L (0,1) = t * M (0,1) := by
    rcases eq_or_ne (M (1,0)) 0 with hm1 | hm1
    · have hm2 : M (0,1) ≠ 0 := by
        intro h2; exact hm (by simp [hm1, h2])
      have hL0 : L (1,0) = 0 := by
        rw [hm1, mul_zero, sub_zero] at h0
        exact (mul_eq_zero.mp h0).resolve_right hm2
      exact ⟨L (0,1) / M (0,1), by rw [hL0, hm1, mul_zero], by rw [div_mul_cancel₀ _ hm2]⟩
    · refine ⟨L (1,0) / M (1,0), by rw [div_mul_cancel₀ _ hm1], ?_⟩
      rw [div_mul_eq_mul_div, eq_div_iff hm1]
      linarith
  apply h t
  apply ContinuousLinearMap.ext
  intro v
  rw [clm_apply_eq L v, ht1, ht2, ContinuousLinearMap.smul_apply, clm_apply_eq M v]
  ring

/-- **Cramer's rule**: two functionals `L`, `M`, with `M ≠ 0` and `L` not a multiple of `M`,
attain every prescribed pair of values. -/
theorem exists_apply_eq_pair_of_forall_ne_smul {L M : (ℝ × ℝ) →L[ℝ] ℝ} (hM : M ≠ 0)
    (h : ∀ t : ℝ, L ≠ t • M) (a b : ℝ) : ∃ r : ℝ × ℝ, L r = a ∧ M r = b := by
  set h1 : ℝ := L (1,0) with hh1
  set h2 : ℝ := L (0,1) with hh2
  set m1 : ℝ := M (1,0) with hm1
  set m2 : ℝ := M (0,1) with hm2
  have hΔ : h1 * m2 - h2 * m1 ≠ 0 := by
    simpa only [← hh1, ← hh2, ← hm1, ← hm2] using det_ne_zero_of_forall_ne_smul hM h
  set D : ℝ := h1 * m2 - h2 * m1 with hD
  have hDδ : D ≠ 0 := by rw [hD]; exact hΔ
  refine ⟨((m2 * a - h2 * b) / D, (-m1 * a + h1 * b) / D), ?_, ?_⟩
  · rw [clm_apply_eq L, ← hh1, ← hh2]
    field_simp
    rw [hD]
    ring
  · rw [clm_apply_eq M, ← hm1, ← hm2]
    field_simp
    rw [hD]
    ring

/-- The product of two functionals on the plane, with `M ≠ 0` and `L` not a multiple of `M`, is an
invertible continuous linear map. -/
theorem isInvertible_prod_of_forall_ne_smul {L M : (ℝ × ℝ) →L[ℝ] ℝ} (hM : M ≠ 0)
    (h : ∀ t : ℝ, L ≠ t • M) : (L.prod M).IsInvertible := by
  set h1 : ℝ := L (1,0) with hh1
  set h2 : ℝ := L (0,1) with hh2
  set m1 : ℝ := M (1,0) with hm1
  set m2 : ℝ := M (0,1) with hm2
  have hΔ : h1 * m2 - h2 * m1 ≠ 0 := by
    simpa only [← hh1, ← hh2, ← hm1, ← hm2] using det_ne_zero_of_forall_ne_smul hM h
  have hker : ∀ w : ℝ × ℝ, (L.prod M) w = 0 → w = 0 := by
    intro w hw
    have hL : L w = 0 := by
      have := congrArg Prod.fst hw; simpa using this
    have hM' : M w = 0 := by
      have := congrArg Prod.snd hw; simpa using this
    have e1 : h1 * w.1 + h2 * w.2 = 0 := by
      rw [hh1, hh2, ← clm_apply_eq L w]; exact hL
    have e2 : m1 * w.1 + m2 * w.2 = 0 := by
      rw [hm1, hm2, ← clm_apply_eq M w]; exact hM'
    have hw1 : w.1 = 0 := by
      have : (h1 * m2 - h2 * m1) * w.1 = 0 := by linear_combination m2 * e1 - h2 * e2
      exact (mul_eq_zero.mp this).resolve_left hΔ
    have hw2 : w.2 = 0 := by
      have hne : m1 * h2 - h1 * m2 ≠ 0 := by
        intro h0; exact hΔ (by linarith)
      have : (m1 * h2 - h1 * m2) * w.2 = 0 := by linear_combination m1 * e1 - h1 * e2
      exact (mul_eq_zero.mp this).resolve_left hne
    exact Prod.ext hw1 hw2
  have hinj : Function.Injective (L.prod M) := by
    intro u v huv
    have h0 : (L.prod M) (u - v) = 0 := by rw [map_sub, huv, sub_self]
    exact sub_eq_zero.mp (hker (u - v) h0)
  have hsurj : Function.Surjective (L.prod M) := by
    intro z
    obtain ⟨r, hr1, hr2⟩ := exists_apply_eq_pair_of_forall_ne_smul hM h z.1 z.2
    exact ⟨r, Prod.ext hr1 hr2⟩
  exact ⟨ContinuousLinearEquiv.ofBijective (L.prod M)
      (by rw [LinearMap.ker_eq_bot]; exact hinj)
      (by rw [LinearMap.range_eq_top]; exact hsurj),
    ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- **The sign of a function near a point, from the sign of a directional derivative.**  If `F`
is differentiable at `p` and `(fderiv F p) r < 0`, then `F (p + t • r) < F p` for all sufficiently
small positive `t`. -/
theorem eventually_lt_self_of_fderiv_smul_neg {F : ℝ × ℝ → ℝ} {p r : ℝ × ℝ}
    (hF : HasFDerivAt F (fderiv ℝ F p) p) (h : (fderiv ℝ F p) r < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), F (p + t • r) < F p := by
  have hcurve : HasDerivAt (fun t : ℝ => p + t • r) r 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • r) r 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).smul_const r
    simpa using h1.const_add p
  have hF' : HasFDerivAt F (fderiv ℝ F p) (p + (0:ℝ) • r) := by simpa using hF
  have hderiv : HasDerivAt (fun t : ℝ => F (p + t • r)) ((fderiv ℝ F p) r) 0 :=
    hF'.comp_hasDerivAt 0 hcurve
  have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
  set c : ℝ := (fderiv ℝ F p) r with hc
  have hlim : Tendsto (slope (fun t : ℝ => F (p + t • r)) 0) (𝓝[>] (0:ℝ)) (𝓝 c) :=
    hslope.mono_left (nhdsWithin_mono _ (fun t (ht : t ∈ Set.Ioi (0:ℝ)) => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt ht))
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), slope (fun t : ℝ => F (p + t • r)) 0 t < c / 2 :=
    hlim.eventually_lt_const (by rw [hc] at h ⊢; linarith)
  filter_upwards [hev, self_mem_nhdsWithin] with t ht htmem
  have htpos : 0 < t := htmem
  have hsl : slope (fun t : ℝ => F (p + t • r)) 0 t = (F (p + t • r) - F p) / t := by
    simp only [slope, sub_zero, zero_smul, add_zero, vsub_eq_sub, smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm]
  rw [hsl] at ht
  have h2 : F (p + t • r) - F p < (c / 2) * t := by
    rw [div_lt_iff₀ htpos] at ht
    linarith
  have h3 : (c / 2) * t < 0 := by
    have hc' : c < 0 := by rw [hc] at h; exact h
    exact mul_neg_of_neg_of_pos (by linarith) htpos
  linarith

end

end Work.Drive.Mono
