import Mathlib
import Submission.Work.Drive.N2.saddlePsi_helpers

/-!
# The wide collar of the saddle model (item (1) of `N2Lead/NOTES_LEAD_saddlePacket.md` §0)

`Work.Drive.N2.saddleCollar η δ` is `{|Re z²| ≤ η ∧ 2 - 2δ ≤ |Im z²| ≤ 2}`.  The two-piece saddle
window with the *wide* band `c ± lam·ηb` (anchor `c - lam·ηs` interior, `ηb > ηs`) needs the collar
rows with the hypothesis `Z y ∈ saddleCollar ηb δ`: a strip-frontier point of the wide band has
`Re (Z y)² = c₀ - 1`-ish, i.e. `|Re|` up to `lam·ηb`, which exceeds `ηs`.

On the wide collar the model is *still* the flow-foot of the level `-ηs`:

* `saddlePsi_sq_of_im_mem_collar` — `(Ψ z)² = -η + i·Im z²` needs only `|Im z²| ∈ [2 - 2δ, 2]`
  (the plateau `saddleM δ w = 1`), and *not* the bound on `|Re z²|`; consequently
* `saddlePsi_idempotent_of_mem_collarWide` — `Ψ (Ψ z) = Ψ z` for `z` in the wide collar, because
  `Ψ z` has `Re ((Ψ z)²) = -η` exactly, so that `Ψ z` lies in the *narrow* collar and the sharp
  idempotence `Work.Drive.N2.saddlePsi_idempotent_of_mem_collar` applies.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set

/-- **The model square on the wide collar.**  For `|Im z²| ∈ [2 - 2δ, 2]` (with *any* real part) the
model is the flow-foot of the level `-η`: `(saddlePsi η δ z)² = -η + i·Im z²`. -/
theorem saddlePsi_sq_of_im_mem_collar {η δ : ℝ} (hδ : 0 < δ) (h2 : 0 ≤ 2 - 4 * δ) {z : ℂ}
    (hw₁ : 2 - 2 * δ ≤ |(z ^ 2).im|) (hw₂ : |(z ^ 2).im| ≤ 2) :
    (Work.Drive.N2.saddlePsi η δ z) ^ 2 = (-η : ℂ) + ((z ^ 2).im : ℂ) * Complex.I := by
  rw [Work.Drive.N2.saddlePsi_sq hδ h2 z, Work.Drive.N2.saddlePhi,
    Work.Drive.N2.saddleSigma_eq_neg_eta (η := η) (δ := δ) (s := (z ^ 2).re) (w := (z ^ 2).im)
      hδ hw₁ hw₂]
  norm_num

/-- **Idempotency of the model on the wide collar.**  `Ψ z ∈ saddleCollar η δ` for every `z` of the
wide collar, so the sharp idempotence applies. -/
theorem saddlePsi_idempotent_of_mem_collarWide {η δ ηb : ℝ} (hη : 0 < η) (hη' : η < 1 / 10)
    (hηb : η ≤ ηb) (hδ : 0 < δ) (hδ' : δ < 1 / 10) {w : ℂ}
    (_hw : |(w ^ 2).re| ≤ ηb) (hw₁ : 2 - 2 * δ ≤ |(w ^ 2).im|) (hw₂ : |(w ^ 2).im| ≤ 2) :
    Work.Drive.N2.saddlePsi η δ (Work.Drive.N2.saddlePsi η δ w)
      = Work.Drive.N2.saddlePsi η δ w := by
  have h2 : (0 : ℝ) ≤ 2 - 4 * δ := by linarith
  have h1 : (Work.Drive.N2.saddlePsi η δ w) ^ 2 = (-η : ℂ) + ((w ^ 2).im : ℂ) * Complex.I :=
    saddlePsi_sq_of_im_mem_collar hδ h2 hw₁ hw₂
  have him : ((Work.Drive.N2.saddlePsi η δ w) ^ 2).im = (w ^ 2).im := by rw [h1]; simp
  have hre : ((Work.Drive.N2.saddlePsi η δ w) ^ 2).re = -η := by rw [h1]; simp
  have hw' : Work.Drive.N2.saddlePsi η δ w ∈ Work.Drive.N2.saddleCollar η δ := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hre, abs_neg, abs_of_nonneg hη.le]
    · rw [him]; exact hw₁
    · rw [him]; exact hw₂
  have h2s := Work.Drive.N2.saddlePsi_collar hη hη' hδ hδ' hw'.1 hw'.2.1 hw'.2.2
  have hsq : (Work.Drive.N2.saddlePsi η δ (Work.Drive.N2.saddlePsi η δ w)) ^ 2
      = (Work.Drive.N2.saddlePsi η δ w) ^ 2 := by
    rw [h2s.1, h1]
    simp
  have hz0 : Work.Drive.N2.saddlePsi η δ w ≠ 0 := by
    intro h0
    have hsq0 : (Work.Drive.N2.saddlePsi η δ w) ^ 2 = 0 := by rw [h0]; ring
    rw [h1] at hsq0
    have him0 := congrArg Complex.im hsq0
    simp at him0
    have habs : |(w ^ 2).im| = 0 := by rw [him0]; simp
    have hle := hw₁
    rw [habs] at hle
    linarith
  have hfac : (Work.Drive.N2.saddlePsi η δ (Work.Drive.N2.saddlePsi η δ w)
        - Work.Drive.N2.saddlePsi η δ w) *
      (Work.Drive.N2.saddlePsi η δ (Work.Drive.N2.saddlePsi η δ w)
        + Work.Drive.N2.saddlePsi η δ w) = 0 := by
    have h' : Work.Drive.N2.saddlePsi η δ (Work.Drive.N2.saddlePsi η δ w) ^ 2
        - Work.Drive.N2.saddlePsi η δ w ^ 2 = 0 := by
      rw [hsq]; ring
    linear_combination h'
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hneg : Work.Drive.N2.saddlePsi η δ (Work.Drive.N2.saddlePsi η δ w)
        = -Work.Drive.N2.saddlePsi η δ w := eq_neg_of_add_eq_zero_left h
    rw [hneg] at h2s
    have hpos := h2s.2
    rw [neg_mul, Complex.neg_re] at hpos
    have hnorm : (Work.Drive.N2.saddlePsi η δ w * (starRingEnd ℂ)
        (Work.Drive.N2.saddlePsi η δ w)).re
        = Complex.normSq (Work.Drive.N2.saddlePsi η δ w) := by
      rw [Complex.mul_conj]
      simp
    rw [hnorm] at hpos
    have hpos' : 0 < Complex.normSq (Work.Drive.N2.saddlePsi η δ w) :=
      Complex.normSq_pos.mpr hz0
    linarith

/-- **Constancy of the model on the wide collar.**  If a continuous path has `|Im (γ ·)²|` in
`[2 - 2δ, 2]` (with *any* real part) and constant `Im (γ ·)²`, then `saddlePsi η δ` takes the same
value at its ends.  This is `Work.Drive.N2.saddlePsi_collar_eq_of_continuousOn` with the bound on
`|Re (γ ·)²|` dropped. -/
theorem saddlePsi_const_of_im_mem_collar {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) (h2 : 0 < 2 - 4 * δ)
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Set.Icc (0 : ℝ) 1))
    (hγC : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      2 - 2 * δ ≤ |((γ s) ^ 2).im| ∧ |((γ s) ^ 2).im| ≤ 2)
    (him : ∀ s ∈ Set.Icc (0 : ℝ) 1, ((γ s) ^ 2).im = ((γ 0) ^ 2).im) :
    Work.Drive.N2.saddlePsi η δ (γ 1) = Work.Drive.N2.saddlePsi η δ (γ 0) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hne : (Work.Drive.N2.saddlePsi η δ (γ 0)) ^ 2 ≠ 0 := by
    rw [saddlePsi_sq_of_im_mem_collar hδ h2.le (hγC 0 h0).1 (hγC 0 h0).2]
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  refine Work.Drive.N2.collarConstancy_of_sq_depends_on_im
    (C := {z : ℂ | 2 - 2 * δ ≤ |(z ^ 2).im| ∧ |(z ^ 2).im| ≤ 2})
    (P := fun w : ℝ => -(η : ℂ) + (w : ℂ) * Complex.I) hγ hγC ?_ ?_ him hne
  · exact (Work.Drive.N2.contDiff_saddlePsi η δ hδ (by linarith : δ < 1 / 2)).continuous.continuousOn
  · intro z hz
    exact saddlePsi_sq_of_im_mem_collar hδ h2.le hz.1 hz.2

/-- **Constancy of the model on the wide collar, chart form.** -/
theorem saddlePsi_collar_eq_of_continuousOnWide {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {U : Set M} {Z : M → ℂ}
    (hZ : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z U)
    {γ : ℝ → M} (hγ : ContinuousOn γ (Set.Icc (0 : ℝ) 1))
    (hγU : ∀ s ∈ Set.Icc (0 : ℝ) 1, γ s ∈ U)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) (h2 : 0 < 2 - 4 * δ)
    (hγC : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      2 - 2 * δ ≤ |((Z (γ s)) ^ 2).im| ∧ |((Z (γ s)) ^ 2).im| ≤ 2)
    (him : ∀ s ∈ Set.Icc (0 : ℝ) 1, ((Z (γ s)) ^ 2).im = ((Z (γ 0)) ^ 2).im) :
    Work.Drive.N2.saddlePsi η δ (Z (γ 1)) = Work.Drive.N2.saddlePsi η δ (Z (γ 0)) :=
  saddlePsi_const_of_im_mem_collar hη hδ h2 (hZ.continuousOn.comp hγ hγU) hγC him


end Work.Drive.N2Lead
