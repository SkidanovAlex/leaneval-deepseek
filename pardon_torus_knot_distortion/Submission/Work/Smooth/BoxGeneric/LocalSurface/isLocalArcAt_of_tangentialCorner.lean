import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.LocalArc.local_arc_of_max_of_isInvertible
import Submission.Work.Smooth.BoxGeneric.LocalArc.local_arc_of_max_of_tangential
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_uniqueActiveFace
import Submission.Work.Smooth.Morse.Surface.param_local_injective
import Submission.Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen
import Submission.Work.Smooth.Morse.Flow.exists_descentRate_lower_bound
import Submission.Work.Core.torusMap_eq_iff

/-!
# The box-norm level set is locally an arc at a *tangential* corner

This is the third local model of the box-norm chapter, complementing
`LocalSurface/isLocalArcAt_of_uniqueActiveFace.lean` (one tight face) and
`LocalSurface/isLocalArcAt_of_corner.lean` (a transversal corner).

At a corner of the box sphere of level `s` at which the two tight signed faces `(i, ε)` and
`(j, ε')` have *proportional* derivatives along the surface, the transverse model of
`isLocalArcAt_of_corner` does not apply.  The present file handles the case that occurs in the
generality argument: the two face cuts are *tangent* to each other — the derivative of the
difference `faceLin i ε - faceLin j ε'`, read in the parameter plane, vanishes — while the active
face cut itself is regular.

Writing `f`, `g` for the two pulled-back face functions shifted to the level `s`, the vanishing of
the derivative of `f - g` together with the regularity of `f` is exactly the hypothesis of the
ℝ² model `Work.Smooth.BoxGeneric.LocalArc.local_arc_of_max_of_tangential`, which produces a local
arc of the set `{max f g = 0}` in the parameter plane.  Near the corner the box norm agrees with
`max (faceLin i ε) (faceLin j ε')`, so pushing the arc forward along the parametrisation gives the
local arc of the surface level set, exactly as in `isLocalArcAt_of_corner`.

The two hypotheses `htang` and `hreg` are stated at (possibly) different parameters over `y`; since
the parametrisation is invariant under the period lattice `2πℤ²`, the derivative conditions are the
same at every parameter over `y`, and the first step of the proof reconciles the two.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Filter
open scoped Topology

namespace Work.Smooth.BoxGeneric.LocalSurface

noncomputable section

/-- If the signed face `faceLin c σ i ε` is nonnegative at `y` (the sign `ε` is the sign of the
coordinate at `y`) then it agrees with the face norm `faceNorm c σ i y`. -/
private theorem faceNorm_eq_faceLin_of_nonneg {c : R3} {σ : Equiv.Perm (Fin 3)} {i : Fin 3}
    {ε : ℝ} {y : R3} (hε : ε = 1 ∨ ε = -1)
    (h : 0 ≤ Work.Smooth.BoxGeneric.faceLin c σ i ε y) :
    Work.Smooth.BoxGeneric.faceNorm c σ i y = Work.Smooth.BoxGeneric.faceLin c σ i ε y := by
  have habs : |ε| = 1 := by rcases hε with h | h <;> simp [h]
  have hmul : |ε * Work.Smooth.BoxGeneric.signedFace c σ i y|
      = |Work.Smooth.BoxGeneric.signedFace c σ i y| := by
    rw [abs_mul, habs, one_mul]
  have h2 : |ε * Work.Smooth.BoxGeneric.signedFace c σ i y|
      = ε * Work.Smooth.BoxGeneric.signedFace c σ i y := by
    have := abs_of_nonneg h
    simpa only [Work.Smooth.BoxGeneric.faceLin_apply] using this
  rw [Work.Smooth.BoxGeneric.faceNorm_eq_abs_signedFace, Work.Smooth.BoxGeneric.faceLin_apply,
    ← hmul]
  exact h2

theorem isLocalArcAt_of_tangentialCorner {ψ : Submission.Diffeo} {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ} {y : LeanEval.KnotTheory.PardonDistortion.R3} {i j : Fin 3} {ε ε' : ℝ} (hs : 0 < s) (hij : i ≠ j) (hε : ε = 1 ∨ ε = -1) (hε' : ε' = 1 ∨ ε' = -1) (hy : y ∈ (Work.Smooth.Morse.torus ψ).carrier) (hacti : Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε y) (hactj : Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s j ε' y) (huniq : ∀ k : Fin 3, k ≠ i → k ≠ j → Work.Smooth.BoxGeneric.faceNorm c σ k y < s) (htang : ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧ fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun z : LeanEval.KnotTheory.PardonDistortion.R3 => Work.Smooth.BoxGeneric.faceLin c σ i ε z - Work.Smooth.BoxGeneric.faceLin c σ j ε' z)) p = 0) (hreg : ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧ fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε)) p ≠ 0) : ∃ U : Set LeanEval.KnotTheory.PardonDistortion.R3, Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) U ∧ y ∈ U ∧ ∃ (I : Set ℝ) (s₀ : ℝ) (ρ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3), IsOpen I ∧ s₀ ∈ I ∧ ContinuousOn ρ I ∧ ρ s₀ = y ∧ Set.InjOn ρ I ∧ (∀ t ∈ I, ρ t ∈ Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) ∧ (∀ z, z ∈ Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s → z ∈ U → ∃ t ∈ I, ρ t = z) := by
  -- the regular parameter and the tangential parameter
  obtain ⟨p, hp, hregp⟩ := hreg
  obtain ⟨p', hp', htangp'⟩ := htang
  -- the two parameters over `y` differ by an element of the period lattice
  have hper : Work.Core.torusMap p.1 p.2 = Work.Core.torusMap p'.1 p'.2 := by
    apply ψ.injective
    simpa only [Work.Smooth.Morse.param_def] using hp.trans hp'.symm
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := (Work.Core.torusMap_eq_iff p.1 p.2 p'.1 p'.2).mp hper
  -- hence the tangential condition holds at `p` as well
  have htangp : fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun z : R3 => Work.Smooth.BoxGeneric.faceLin c σ i ε z - Work.Smooth.BoxGeneric.faceLin c σ j ε' z)) p = 0 := by
    have hpeq : p = (p'.1 + (k : ℝ) * (2 * Real.pi), p'.2 + (l : ℝ) * (2 * Real.pi)) := by
      exact Prod.ext hk hl
    rw [hpeq, Work.Smooth.Morse.Flow.fderiv_pullback_add_lattice ψ _ p' k l]
    exact htangp'
  -- the two face functions, shifted down to the level `s`
  let f : ℝ × ℝ → ℝ :=
    fun q => Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) q - s
  let g : ℝ × ℝ → ℝ :=
    fun q => Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε') q - s
  have hfp : f p = 0 := by
    show Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) p - s = 0
    have h0 : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) p = s := by
      show Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ p) = s
      rw [hp]; exact hacti.1
    rw [h0, sub_self]
  have hgp : g p = 0 := by
    show Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε') p - s = 0
    have h0 : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε') p = s := by
      show Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ p) = s
      rw [hp]; exact hactj.1
    rw [h0, sub_self]
  have hf_deriv : fderiv ℝ f p
      = fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε)) p := by
    show fderiv ℝ (fun q : ℝ × ℝ =>
      Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) q - s) p = _
    exact fderiv_sub_const s
  have hg_deriv : fderiv ℝ g p
      = fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε')) p := by
    show fderiv ℝ (fun q : ℝ × ℝ =>
      Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε') q - s) p = _
    exact fderiv_sub_const s
  -- the two unshifted face functions have the same derivative at `p`
  have hdi : DifferentiableAt ℝ
      (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε)) p :=
    ((Work.Smooth.BoxGeneric.pullback_faceLin_contDiff ψ c σ i ε).differentiable
      (by simp)).differentiableAt
  have hdj : DifferentiableAt ℝ
      (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε')) p :=
    ((Work.Smooth.BoxGeneric.pullback_faceLin_contDiff ψ c σ j ε').differentiable
      (by simp)).differentiableAt
  have hpi : fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε)) p
      = fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε')) p := by
    have hsplit : Work.Smooth.Morse.pullback ψ
          (fun z : R3 => Work.Smooth.BoxGeneric.faceLin c σ i ε z
            - Work.Smooth.BoxGeneric.faceLin c σ j ε' z)
        = (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε))
          - (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε')) := by
      funext q
      simp only [Work.Smooth.Morse.pullback, Pi.sub_apply]
    have h0 : fderiv ℝ ((Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε))
          - (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε'))) p = 0 := by
      rw [← hsplit]
      exact htangp
    rw [fderiv_sub hdi hdj] at h0
    exact sub_eq_zero.mp h0
  have htangfg : fderiv ℝ f p = fderiv ℝ g p := by rw [hf_deriv, hg_deriv, hpi]
  have hregf : fderiv ℝ f p ≠ 0 := by rw [hf_deriv]; exact hregp
  have hf_cd : ContDiff ℝ 1 f :=
    ((Work.Smooth.BoxGeneric.pullback_faceLin_contDiff ψ c σ i ε).sub contDiff_const).of_le (by simp)
  have hg_cd : ContDiff ℝ 1 g :=
    ((Work.Smooth.BoxGeneric.pullback_faceLin_contDiff ψ c σ j ε').sub contDiff_const).of_le (by simp)
  -- the local arc of `{max f g = 0}` in the parameter plane
  obtain ⟨ε₀, hε₀pos, arc, harc0, harccont, harcinj, harclev, harccov⟩ :=
    Work.Smooth.BoxGeneric.LocalArc.local_arc_of_max_of_tangential hf_cd hg_cd hfp hgp htangfg hregf
  -- the identity `boxNorm = max (faceLin i ε) (faceLin j ε')` near `p`
  have hmaxf : ∀ q : ℝ × ℝ, max (f q) (g q)
      = max (Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ q))
          (Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ q)) - s := by
    intro q
    show max (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) q - s)
        (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε') q - s) = _
    exact max_sub_sub_right _ _ s
  -- the neighbourhood on which the sign conditions and the "third face is small" hold
  have ha : ∀ᶠ q in 𝓝 p,
      0 < Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ q) := by
    have hcont : Continuous (fun q : ℝ × ℝ =>
        Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ q)) :=
      (Work.Smooth.BoxGeneric.contDiff_faceLin c σ i ε).continuous.comp
        (Work.Smooth.Morse.param_continuous ψ)
    have hopen : IsOpen {q : ℝ × ℝ |
        0 < Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ q)} :=
      isOpen_lt continuous_const hcont
    refine hopen.mem_nhds ?_
    show 0 < Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ p)
    rw [hp, hacti.1]; exact hs
  have hb : ∀ᶠ q in 𝓝 p,
      0 < Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ q) := by
    have hcont : Continuous (fun q : ℝ × ℝ =>
        Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ q)) :=
      (Work.Smooth.BoxGeneric.contDiff_faceLin c σ j ε').continuous.comp
        (Work.Smooth.Morse.param_continuous ψ)
    have hopen : IsOpen {q : ℝ × ℝ |
        0 < Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ q)} :=
      isOpen_lt continuous_const hcont
    refine hopen.mem_nhds ?_
    show 0 < Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ p)
    rw [hp, hactj.1]; exact hs
  have hc : ∀ᶠ q in 𝓝 p,
      ∀ k : Fin 3, k ≠ i → k ≠ j → Work.Smooth.BoxGeneric.faceNorm c σ k (Work.Smooth.Morse.param ψ q) < s := by
    rw [eventually_all]
    intro k
    by_cases hk : k ≠ i ∧ k ≠ j
    · obtain ⟨hki, hkj⟩ := hk
      have hcont : Continuous (fun q : ℝ × ℝ =>
          Work.Smooth.BoxGeneric.faceNorm c σ k (Work.Smooth.Morse.param ψ q)) :=
        (Work.Smooth.BoxGeneric.continuous_faceNorm c σ k).comp
          (Work.Smooth.Morse.param_continuous ψ)
      have hopen : IsOpen {q : ℝ × ℝ |
          Work.Smooth.BoxGeneric.faceNorm c σ k (Work.Smooth.Morse.param ψ q) < s} :=
        isOpen_lt hcont continuous_const
      have hev : ∀ᶠ q in 𝓝 p,
          Work.Smooth.BoxGeneric.faceNorm c σ k (Work.Smooth.Morse.param ψ q) < s :=
        hopen.mem_nhds (by
          show Work.Smooth.BoxGeneric.faceNorm c σ k (Work.Smooth.Morse.param ψ p) < s
          rw [hp]; exact huniq k hki hkj)
      exact hev.mono (fun q hq _ _ => hq)
    · have hk' : k = i ∨ k = j := by
        rcases not_and_or.mp hk with h | h
        · exact Or.inl (not_not.mp h)
        · exact Or.inr (not_not.mp h)
      refine Eventually.of_forall (fun q h1 h2 => ?_)
      rcases hk' with hk | hk
      · exact absurd hk h1
      · exact absurd hk h2
  have hall : ∀ᶠ q in 𝓝 p,
      (0 < Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ q)) ∧
      (0 < Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ q)) ∧
      (∀ k : Fin 3, k ≠ i → k ≠ j → Work.Smooth.BoxGeneric.faceNorm c σ k (Work.Smooth.Morse.param ψ q) < s) :=
    ha.and (hb.and hc)
  obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ := Metric.mem_nhds_iff.mp hall
  have hbc : ∀ q : ℝ × ℝ, q ∈ Metric.ball p δ₂ →
      (0 < Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ q)) ∧
      (0 < Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ q)) ∧
      (∀ k : Fin 3, k ≠ i → k ≠ j → Work.Smooth.BoxGeneric.faceNorm c σ k (Work.Smooth.Morse.param ψ q) < s) :=
    fun q hq => hδ₂sub hq
  -- the two implications identifying the box level with the corner level
  have step_II : ∀ q : ℝ × ℝ, q ∈ Metric.ball p δ₂ → max (f q) (g q) = 0 →
      Submission.boxNorm c σ (Work.Smooth.Morse.param ψ q) = s := by
    intro q hq hmax
    obtain ⟨hai, haj, hoth⟩ := hbc q hq
    have hAi : Work.Smooth.BoxGeneric.faceNorm c σ i (Work.Smooth.Morse.param ψ q)
        = Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ q) :=
      faceNorm_eq_faceLin_of_nonneg hε (le_of_lt hai)
    have hBj : Work.Smooth.BoxGeneric.faceNorm c σ j (Work.Smooth.Morse.param ψ q)
        = Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ q) :=
      faceNorm_eq_faceLin_of_nonneg hε' (le_of_lt haj)
    have hAB : max (Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ q))
        (Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ q)) = s := by
      rw [hmaxf q] at hmax
      linarith
    have hAs : Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ q) ≤ s :=
      le_trans (le_max_left _ _) (le_of_eq hAB)
    have hBs : Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ q) ≤ s :=
      le_trans (le_max_right _ _) (le_of_eq hAB)
    have hle : Submission.boxNorm c σ (Work.Smooth.Morse.param ψ q) ≤ s := by
      rw [Work.Smooth.BoxGeneric.boxNorm_le_iff]
      intro k
      by_cases hki : k = i
      · rw [hki, hAi]; exact hAs
      · by_cases hkj : k = j
        · rw [hkj, hBj]; exact hBs
        · exact le_of_lt (hoth k hki hkj)
    have hge : s ≤ Submission.boxNorm c σ (Work.Smooth.Morse.param ψ q) := by
      rcases (max_eq_iff.mp hAB) with ⟨hA, -⟩ | ⟨hB, -⟩
      · rw [← hA, ← hAi]
        exact Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ i _
      · rw [← hB, ← hBj]
        exact Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ j _
    exact le_antisymm hle hge
  have step_I : ∀ q : ℝ × ℝ, q ∈ Metric.ball p δ₂ →
      Submission.boxNorm c σ (Work.Smooth.Morse.param ψ q) = s → max (f q) (g q) = 0 := by
    intro q hq hbox
    obtain ⟨hai, haj, hoth⟩ := hbc q hq
    have hAi : Work.Smooth.BoxGeneric.faceNorm c σ i (Work.Smooth.Morse.param ψ q)
        = Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ q) :=
      faceNorm_eq_faceLin_of_nonneg hε (le_of_lt hai)
    have hBj : Work.Smooth.BoxGeneric.faceNorm c σ j (Work.Smooth.Morse.param ψ q)
        = Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ q) :=
      faceNorm_eq_faceLin_of_nonneg hε' (le_of_lt haj)
    have hallf : ∀ k : Fin 3,
        Work.Smooth.BoxGeneric.faceNorm c σ k (Work.Smooth.Morse.param ψ q) ≤ s :=
      (Work.Smooth.BoxGeneric.boxNorm_le_iff c σ s (Work.Smooth.Morse.param ψ q)).mp (le_of_eq hbox)
    have hAs : Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ q) ≤ s := by
      rw [← hAi]; exact hallf i
    have hBs : Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ q) ≤ s := by
      rw [← hBj]; exact hallf j
    obtain ⟨k, hk⟩ :=
      Work.Smooth.BoxGeneric.exists_faceNorm_eq_boxNorm c σ (Work.Smooth.Morse.param ψ q)
    have hks : Work.Smooth.BoxGeneric.faceNorm c σ k (Work.Smooth.Morse.param ψ q) = s := by
      rw [hk, hbox]
    have hki_or : k = i ∨ k = j := by
      by_contra hcon
      rw [not_or] at hcon
      have hlt := hoth k hcon.1 hcon.2
      rw [hks] at hlt
      exact lt_irrefl s hlt
    have hAB : max (Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ q))
        (Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ q)) = s := by
      rcases hki_or with hkj | hkj
      · rw [hkj] at hks
        have hAs' : Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ q) = s := by
          rw [← hAi]; exact hks
        rw [hAs']; exact max_eq_left hBs
      · rw [hkj] at hks
        have hBs' : Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ q) = s := by
          rw [← hBj]; exact hks
        rw [hBs']; exact max_eq_right hAs
    rw [hmaxf q, hAB, sub_self]
  -- a ball on which the parametrisation is injective
  obtain ⟨εp, hεppos, hεpinj⟩ := Work.Smooth.Morse.Surface.param_local_injective ψ p
  let δ : ℝ := min ε₀ (min εp δ₂)
  have hδpos : 0 < δ := lt_min hε₀pos (lt_min hεppos hδ₂pos)
  have hδε₀ : δ ≤ ε₀ := min_le_left _ _
  have hδεp : δ ≤ εp := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδδ₂ : δ ≤ δ₂ := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨Work.Smooth.Morse.param ψ '' Metric.ball p δ,
    Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ
      (U := Metric.ball p δ) Metric.isOpen_ball,
    ⟨p, Metric.mem_ball_self hδpos, hp⟩,
    Set.Ioo (-1 : ℝ) 1 ∩ arc ⁻¹' Metric.ball p δ, 0,
    fun t => Work.Smooth.Morse.param ψ (arc t), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact harccont.isOpen_inter_preimage isOpen_Ioo Metric.isOpen_ball
  · refine ⟨by norm_num, ?_⟩
    show arc 0 ∈ Metric.ball p δ
    rw [harc0]; exact Metric.mem_ball_self hδpos
  · exact (Work.Smooth.Morse.param_continuous ψ).continuousOn.comp
      (harccont.mono inter_subset_left) (Set.mapsTo_univ _ _)
  · show Work.Smooth.Morse.param ψ (arc 0) = y
    rw [harc0, hp]
  · intro t1 ht1 t2 ht2 heq
    simp only [Set.mem_inter_iff, Set.mem_preimage] at ht1 ht2
    have h1 : arc t1 ∈ Metric.ball p εp := Metric.ball_subset_ball hδεp ht1.2
    have h2 : arc t2 ∈ Metric.ball p εp := Metric.ball_subset_ball hδεp ht2.2
    exact harcinj ht1.1 ht2.1 (hεpinj h1 h2 heq)
  · intro t ht
    simp only [Set.mem_inter_iff, Set.mem_preimage] at ht
    rw [Work.Smooth.Morse.mem_levelSet]
    exact ⟨Work.Smooth.Morse.param_mem ψ (arc t),
      step_II (arc t) (Metric.ball_subset_ball hδδ₂ ht.2) (harclev t ht.1)⟩
  · intro z hz hzU
    rw [Work.Smooth.Morse.mem_levelSet] at hz
    obtain ⟨-, hzbox⟩ := hz
    obtain ⟨q, hqB, hqy⟩ := hzU
    have hboxq : Submission.boxNorm c σ (Work.Smooth.Morse.param ψ q) = s := by
      rw [hqy]; exact hzbox
    have hmax : max (f q) (g q) = 0 := step_I q (Metric.ball_subset_ball hδδ₂ hqB) hboxq
    have hd : ‖q - p‖ < ε₀ := by
      have hqd : dist q p < δ := Metric.mem_ball.mp hqB
      rw [dist_eq_norm] at hqd
      exact lt_of_lt_of_le hqd hδε₀
    obtain ⟨t, htI, htq⟩ := harccov q hmax hd
    refine ⟨t, ?_, ?_⟩
    · simp only [Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨htI, by rw [htq]; exact hqB⟩
    · show Work.Smooth.Morse.param ψ (arc t) = z
      rw [htq, hqy]

end

end Work.Smooth.BoxGeneric.LocalSurface
