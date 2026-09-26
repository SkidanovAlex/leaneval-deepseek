import Mathlib
import Submission.Work.Drive.Final.cornerGates
import Submission.Work.Drive.Final.faceEventGates
import Submission.Work.Drive.Final.eventGates
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.Drive.Final.faceEventGatesLocal
import Submission.Work.Drive.Final.cornerEventGatesLocal

/-!
# The local gates of the tilted sweep, with the neighbourhood inside a prescribed ball

`Work.Drive.Final.gates_local`: at an event `p` of the tilted sweep (of any of the three types
`IsEvent`, `IsFaceEvent`, `IsCornerEvent`) and for every `ρ > 0` there is a set `E`, open in the
torus and containing a *carrier-neighbourhood* of `par ψ p`, contained in the ball of radius `ρ`
around `par ψ p`, such that the region of the sweep at the event's level meets `E` in the union of
two sets each of which is empty or path connected.

The point of the statement (compared with `eventGates`, `faceEventGates`, `cornerGates`) is the
**radius control**: the neighbourhood `E` may be taken inside an arbitrary prescribed ball.  That
does *not* follow from the three gate lemmas by intersecting their `E` with a ball (the intersections
of the path connected pieces with a ball need not stay path connected), so the three proofs are
re-run with the source neighbourhood of the chart chosen small enough that its image lies in the
ball of radius `ρ / 2`.  All the path connectedness inputs of the three proofs are stated for
*arbitrary* radii (`gateNoFace`, `halfSquare`, `cornerRegionChart_pathConnected`,
`cornerLevelPieceDown`), so they survive the shrinking.

The three cases:

* `Work.Drive.Final.eventGatesLocal` (here): `IsEvent`.  Strictly inside the slab by
  `GoodSweepData2`, so near the event the region is the superlevel set of the sweep height, which
  the Morse lemma normalises to a quadratic form; the two pieces are the convex sectors of
  `gateNoFace` (`eventGates`, interior case).
* `Work.Drive.Final.faceEventGatesLocal`: `IsFaceEvent` (`faceEventGates`).
* `Work.Drive.Final.cornerEventGatesLocal`: `IsCornerEvent` (`cornerGates`).
-/

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set
open Work.BoxShrink.Pinch

noncomputable section

/-- **The interior case of `gates_local`**: at an event which is a critical point of the sweep
height strictly inside the box and the slab, the gates can be localised to an arbitrary ball. -/
theorem eventGatesLocal {ψ : Submission.Diffeo} {K : Knot} {s R : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ}
    (hG : Work.Drive.Final.GoodSweepData3 ψ K s c σ u v h R ℓ exc lam0 lam1)
    {p : ℝ × ℝ} (hp : Work.Drive.Final.IsEvent ψ s c σ u v h ℓ p)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ E U₁ U₂ : Set R3,
      Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ) E ∧
      (∃ ε : ℝ, 0 < ε ∧ Metric.ball (par ψ p) ε ∩
          (Work.Drive.EpsSphere.torusOf ψ).carrier ⊆ E) ∧
      E ⊆ Metric.ball (par ψ p) ρ ∧
      (U₁ = ∅ ∨ IsPathConnected U₁) ∧ (U₂ = ∅ ∨ IsPathConnected U₂) ∧
      U₁ ⊆ E ∧ U₂ ⊆ E ∧
      Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
        (Work.Drive.Final.eventValue ψ ℓ p) ∩ E = U₁ ∪ U₂ := by
  classical
  have hDP2 : Work.Drive.Final.GoodSweepData2 ψ K s c σ u v h R ℓ exc lam0 lam1 := hG.1
  have hGSD : Work.Drive.Final.GoodSweepData ψ K s c σ u v h R ℓ exc lam0 lam1 := hG.1.1
  have hℓne : ℓ ≠ 0 := hG.1.1.1.2.2.1
  have hv1 : ‖v‖ = 1 := hG.1.1.1.2.1
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv1
    norm_num at hv1
  have hh : 0 < h := hG.1.1.1.2.2.2.2.2.1
  have hbox : par ψ p ∈ Submission.PBox s c σ := hp.1
  have hslabstrict : |Work.Drive.Final.slabFn c u v (par ψ p)| < h := hG.1.2.2.2.1 p hp
  have hcrit : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p = 0 := hp.2.2
  have hnondeg : Function.Injective
      (fderiv ℝ (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ)) p) :=
    (hG.1.1.1.1.2.2.1 p hp.1 hp.2.1 hp.2.2).1
  have hVp : inner ℝ v (par ψ p) - (inner ℝ v c + u) - h < 0 := by
    rw [Work.Drive.Final.slabFn_apply, abs_lt] at hslabstrict
    linarith [hslabstrict.2]
  have hVm : -(inner ℝ v (par ψ p) - (inner ℝ v c + u)) - h < 0 := by
    rw [Work.Drive.Final.slabFn_apply, abs_lt] at hslabstrict
    linarith [hslabstrict.1]
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.EpsForm.sweepHeight ψ ℓ) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : R3 => ℓ y) := ℓ.contDiff
    exact Work.Smooth.Morse.pullback_contDiff ψ h1
  obtain ⟨φ, s₁, s₂, hpsrc, hφ0, hφsm, hφsymm, hs₁, hs₂, hquad⟩ :=
    morseLemmaProd (Work.Drive.EpsForm.sweepHeight ψ ℓ) p hsm hcrit hnondeg
  set Φ : ℝ × ℝ → R3 := fun w => par ψ (φ.symm w) with hΦ
  have htarget : (0 : ℝ × ℝ) ∈ φ.target := by rw [← hφ0]; exact φ.map_source hpsrc
  have hsymm0 : φ.symm 0 = p := by rw [← hφ0]; exact φ.left_inv hpsrc
  have hΦ0 : Φ 0 = par ψ p := by rw [hΦ]; simp [hsymm0]
  have hsymm_smooth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ × ℝ => φ.symm w) 0 :=
    hφsymm.contDiffAt (φ.open_target.mem_nhds htarget)
  have hΦ_smooth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ 0 := by
    have hg := (Work.BoxShrink.Pinch.par_contDiff ψ).comp_contDiffAt 0 hsymm_smooth
    rw [hΦ]
    exact hg
  have hΦ_contOn : ContinuousOn Φ φ.target :=
    (par_continuous ψ).comp_continuousOn hφsymm.continuousOn
  have hev : ∀ᶠ ξ in nhds (0 : ℝ × ℝ), ξ ∈ φ.target ∧ Φ ξ ∈ Submission.PBox s c σ ∧
      (inner ℝ v (Φ ξ) - (inner ℝ v c + u) - h < 0) ∧
      (-(inner ℝ v (Φ ξ) - (inner ℝ v c + u)) - h < 0) := by
    have h1 : ∀ᶠ ξ in nhds (0 : ℝ × ℝ), ξ ∈ φ.target := φ.open_target.mem_nhds htarget
    have h2 : ∀ᶠ ξ in nhds (0 : ℝ × ℝ), Φ ξ ∈ Submission.PBox s c σ :=
      hΦ_smooth.continuousAt.preimage_mem_nhds
        ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds (by rw [hΦ0]; exact hbox))
    have h3 : ∀ᶠ ξ in nhds (0 : ℝ × ℝ), inner ℝ v (Φ ξ) - (inner ℝ v c + u) - h < 0 := by
      have hcont : Continuous (fun y : R3 => inner ℝ v y - (inner ℝ v c + u) - h) := by fun_prop
      exact hΦ_smooth.continuousAt.preimage_mem_nhds
        ((isOpen_lt hcont continuous_const).mem_nhds (by rw [hΦ0]; exact hVp))
    have h4 : ∀ᶠ ξ in nhds (0 : ℝ × ℝ),
        -(inner ℝ v (Φ ξ) - (inner ℝ v c + u)) - h < 0 := by
      have hcont : Continuous (fun y : R3 => -(inner ℝ v y - (inner ℝ v c + u)) - h) := by
        fun_prop
      exact hΦ_smooth.continuousAt.preimage_mem_nhds
        ((isOpen_lt hcont continuous_const).mem_nhds (by rw [hΦ0]; exact hVm))
    filter_upwards [h1, h2, h3, h4] with ξ h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := exists_sq_subset hev
  -- the new requirement: the source square is small enough that its image lies in the ball
  have hball_nhds : Φ ⁻¹' Metric.ball (par ψ p) (ρ / 2) ∈ nhds (0 : ℝ × ℝ) := by
    have hcont : ContinuousAt Φ 0 := hΦ_smooth.continuousAt
    refine hcont.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds ?_)
    rw [hΦ0]
    exact Metric.mem_ball_self (by linarith)
  obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ := exists_sq_subset hball_nhds
  set δ : ℝ := min δ₁ δ₂ with hδdef
  have hδpos : 0 < δ := lt_min hδ₁pos hδ₂pos
  have hδle₁ : δ ≤ δ₁ := min_le_left _ _
  have hδle₂ : δ ≤ δ₂ := min_le_right _ _
  have hsq₁ : sq δ ⊆ sq δ₁ := by
    intro ξ hξ
    rw [mem_sq] at hξ ⊢
    exact ⟨⟨by linarith [hξ.1.1, hδle₁], by linarith [hξ.1.2, hδle₁]⟩,
      ⟨by linarith [hξ.2.1, hδle₁], by linarith [hξ.2.2, hδle₁]⟩⟩
  have hsq₂ : sq δ ⊆ sq δ₂ := by
    intro ξ hξ
    rw [mem_sq] at hξ ⊢
    exact ⟨⟨by linarith [hξ.1.1, hδle₂], by linarith [hξ.1.2, hδle₂]⟩,
      ⟨by linarith [hξ.2.1, hδle₂], by linarith [hξ.2.2, hδle₂]⟩⟩
  have htargetδ : ∀ ξ ∈ sq δ, ξ ∈ φ.target := fun ξ hξ => (hδ₁sub (hsq₁ hξ)).1
  have hPBoxδ : ∀ ξ ∈ sq δ, Φ ξ ∈ Submission.PBox s c σ :=
    fun ξ hξ => (hδ₁sub (hsq₁ hξ)).2.1
  have hVpδ : ∀ ξ ∈ sq δ, inner ℝ v (Φ ξ) - (inner ℝ v c + u) - h < 0 :=
    fun ξ hξ => (hδ₁sub (hsq₁ hξ)).2.2.1
  have hVmδ : ∀ ξ ∈ sq δ, -(inner ℝ v (Φ ξ) - (inner ℝ v c + u)) - h < 0 :=
    fun ξ hξ => (hδ₁sub (hsq₁ hξ)).2.2.2
  have hballδ : ∀ ξ ∈ sq δ, Φ ξ ∈ Metric.ball (par ψ p) (ρ / 2) :=
    fun ξ hξ => hδ₂sub (hsq₂ hξ)
  have hheight : ∀ ξ ∈ sq δ, ℓ (Φ ξ) = eventValue ψ ℓ p + s₁ * ξ.1 ^ 2 + s₂ * ξ.2 ^ 2 := by
    intro ξ hξ
    have h2 : φ.symm ξ ∈ φ.source := φ.map_target (htargetδ ξ hξ)
    have h3 := hquad (φ.symm ξ) h2
    rw [φ.right_inv (htargetδ ξ hξ)] at h3
    have h4 : Work.Drive.EpsForm.sweepHeight ψ ℓ p = eventValue ψ ℓ p := rfl
    rw [h4] at h3
    have h5 : Work.Drive.EpsForm.sweepHeight ψ ℓ (φ.symm ξ) = ℓ (Φ ξ) := by rw [hΦ]; rfl
    rw [← h5]
    exact h3
  obtain ⟨S₁, S₂, hS₁, hS₂, hS⟩ := gateNoFace δ hδpos (ContinuousLinearMap.id ℝ (ℝ × ℝ))
    (fun _ _ h => h) s₁ s₂ hs₁ hs₂
  simp only [ContinuousLinearMap.id_apply] at hS
  have hS₁U : S₁ ⊆ sq δ := by
    intro x hx
    have hx' : x ∈ Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ ∩
        {ξ : ℝ × ℝ | 0 < s₁ * ξ.1 ^ 2 + s₂ * ξ.2 ^ 2} := by
      rw [← hS]; exact Or.inl hx
    exact hx'.1
  have hS₂U : S₂ ⊆ sq δ := by
    intro x hx
    have hx' : x ∈ Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ ∩
        {ξ : ℝ × ℝ | 0 < s₁ * ξ.1 ^ 2 + s₂ * ξ.2 ^ 2} := by
      rw [← hS]; exact Or.inr hx
    exact hx'.1
  have hΦ_contOn' : ContinuousOn Φ (Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ) :=
    hΦ_contOn.mono (fun ξ hξ => htargetδ ξ (by rw [mem_sq]; exact hξ))
  have hparam_open : IsOpen (φ.symm '' sq δ) :=
    φ.isOpen_image_symm_of_subset_target (isOpen_sq δ)
      (fun ξ hξ => htargetδ ξ (by rw [mem_sq]; exact hξ))
  have hopen : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
      (Φ '' sq δ) := by
    have h := Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hparam_open
    have himg : Φ '' sq δ = par ψ '' (φ.symm '' sq δ) := by
      rw [hΦ]
      show (par ψ ∘ ⇑φ.symm) '' sq δ = par ψ '' (⇑φ.symm '' sq δ)
      rw [Set.image_comp]
    have h' : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
        (par ψ '' (φ.symm '' sq δ)) := by
      simpa only [Work.Drive.EpsSphere.torusOf, Work.Smooth.Morse.torus,
        Work.BoxShrink.Pinch.par_def, Work.Smooth.Morse.param_def] using h
    rwa [himg]
  obtain ⟨E, hEopen, hEeq⟩ := (isOpen_induced_iff.mp hopen :
    ∃ W : Set R3, IsOpen W ∧ Subtype.val ⁻¹' W = Subtype.val ⁻¹' (Φ '' sq δ))
  have hEcarrier : ∀ y : R3, y ∈ (Work.Smooth.Morse.torus ψ).carrier →
      (y ∈ E ↔ y ∈ Φ '' sq δ) := by
    intro y hy
    have h1 : (⟨y, hy⟩ : (Work.Smooth.Morse.torus ψ).carrier) ∈ Subtype.val ⁻¹' E ↔
        (⟨y, hy⟩ : (Work.Smooth.Morse.torus ψ).carrier) ∈
          Subtype.val ⁻¹' (Φ '' sq δ) := by
      rw [hEeq]
    rwa [Set.mem_preimage, Set.mem_preimage] at h1
  have h0sq : (0 : ℝ × ℝ) ∈ sq δ := by
    simp only [mem_sq, Set.mem_Ioo, Prod.fst_zero, Prod.snd_zero]
    exact ⟨⟨by linarith, hδpos⟩, ⟨by linarith, hδpos⟩⟩
  have hparE : par ψ p ∈ E := (hEcarrier (par ψ p) (par_mem_carrier ψ p)).mpr ⟨0, h0sq, hΦ0⟩
  -- the pieces
  have hU₁ : Φ '' S₁ = ∅ ∨ IsPathConnected (Φ '' S₁) := by
    rcases hS₁ with h | h
    · exact Or.inl (by rw [h]; exact Set.image_empty _)
    · exact Or.inr (h.image' (hΦ_contOn'.mono hS₁U))
  have hU₂ : Φ '' S₂ = ∅ ∨ IsPathConnected (Φ '' S₂) := by
    rcases hS₂ with h | h
    · exact Or.inl (by rw [h]; exact Set.image_empty _)
    · exact Or.inr (h.image' (hΦ_contOn'.mono hS₂U))
  have hU₁W : Φ '' S₁ ⊆ E := by
    rintro y ⟨ξ, hξ, rfl⟩
    exact (hEcarrier (Φ ξ) (par_mem_carrier ψ _)).mpr ⟨ξ, hS₁U hξ, rfl⟩
  have hU₂W : Φ '' S₂ ⊆ E := by
    rintro y ⟨ξ, hξ, rfl⟩
    exact (hEcarrier (Φ ξ) (par_mem_carrier ψ _)).mpr ⟨ξ, hS₂U hξ, rfl⟩
  have hU₁ball : Φ '' S₁ ⊆ Metric.ball (par ψ p) (ρ / 2) := by
    rintro y ⟨ξ, hξ, rfl⟩
    exact hballδ ξ (hS₁U hξ)
  have hU₂ball : Φ '' S₂ ⊆ Metric.ball (par ψ p) (ρ / 2) := by
    rintro y ⟨ξ, hξ, rfl⟩
    exact hballδ ξ (hS₂U hξ)
  have hball_mono : Metric.ball (par ψ p) (ρ / 2) ⊆ Metric.ball (par ψ p) ρ :=
    Metric.ball_subset_ball (by linarith)
  have hUnionSub : Φ '' S₁ ∪ Φ '' S₂ ⊆ Metric.ball (par ψ p) ρ :=
    Set.union_subset (hU₁ball.trans hball_mono) (hU₂ball.trans hball_mono)
  -- the gate identity on the big carrier-neighbourhood `E`
  have hgal : Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
      s c σ u v h ℓ (Work.Drive.Final.eventValue ψ ℓ p) ∩ E = Φ '' S₁ ∪ Φ '' S₂ := by
    ext y
    constructor
    · rintro ⟨hyreg, hyE⟩
      rw [mem_openTiltedSweepRegion_iff] at hyreg
      obtain ⟨hyc, -, hcond⟩ := hyreg
      obtain ⟨ξ, hξU, hξeq⟩ := (hEcarrier y hyc).mp hyE
      rw [← hξeq] at hcond ⊢
      have hξS : ξ ∈ S₁ ∪ S₂ := by
        rw [hS]
        rcases hcond with h | h | h
        · exact absurd h (not_lt.mpr (le_of_lt (hVpδ ξ hξU)))
        · exact absurd h (not_lt.mpr (le_of_lt (hVmδ ξ hξU)))
        · refine ⟨hξU, ?_⟩
          show 0 < s₁ * ξ.1 ^ 2 + s₂ * ξ.2 ^ 2
          have hh2 := hheight ξ hξU
          linarith
      rcases hξS with h | h
      · exact Or.inl ⟨ξ, h, rfl⟩
      · exact Or.inr ⟨ξ, h, rfl⟩
    · rintro (⟨ξ, hξS, hξeq⟩ | ⟨ξ, hξS, hξeq⟩)
      · refine ⟨?_, ?_⟩
        · rw [← hξeq, mem_openTiltedSweepRegion_iff]
          refine ⟨par_mem_carrier ψ _, hPBoxδ ξ (hS₁U hξS), ?_⟩
          have h : ξ ∈ Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ ∩
              {ξ : ℝ × ℝ | 0 < s₁ * ξ.1 ^ 2 + s₂ * ξ.2 ^ 2} := by
            rw [← hS]; exact Or.inl hξS
          have h' : 0 < s₁ * ξ.1 ^ 2 + s₂ * ξ.2 ^ 2 := by simpa using h.2
          have hh2 := hheight ξ (hS₁U hξS)
          refine Or.inr (Or.inr ?_)
          linarith
        · rw [hEcarrier y (by rw [← hξeq]; exact par_mem_carrier ψ _)]
          exact ⟨ξ, hS₁U hξS, hξeq⟩
      · refine ⟨?_, ?_⟩
        · rw [← hξeq, mem_openTiltedSweepRegion_iff]
          refine ⟨par_mem_carrier ψ _, hPBoxδ ξ (hS₂U hξS), ?_⟩
          have h : ξ ∈ Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ ∩
              {ξ : ℝ × ℝ | 0 < s₁ * ξ.1 ^ 2 + s₂ * ξ.2 ^ 2} := by
            rw [← hS]; exact Or.inr hξS
          have h' : 0 < s₁ * ξ.1 ^ 2 + s₂ * ξ.2 ^ 2 := by simpa using h.2
          have hh2 := hheight ξ (hS₂U hξS)
          refine Or.inr (Or.inr ?_)
          linarith
        · rw [hEcarrier y (by rw [← hξeq]; exact par_mem_carrier ψ _)]
          exact ⟨ξ, hS₂U hξS, hξeq⟩
  -- the final packaging: intersect the neighbourhood with the prescribed ball
  have hEball : E ∩ Metric.ball (par ψ p) ρ ⊆ Metric.ball (par ψ p) ρ := Set.inter_subset_right
  have hEopen' : IsOpen (E ∩ Metric.ball (par ψ p) ρ) := hEopen.inter Metric.isOpen_ball
  have hUnionsub : Φ '' S₁ ∪ Φ '' S₂ ⊆ E ∩ Metric.ball (par ψ p) ρ :=
    Set.union_subset (fun y hy => ⟨hU₁W hy, hball_mono (hU₁ball hy)⟩)
      (fun y hy => ⟨hU₂W hy, hball_mono (hU₂ball hy)⟩)
  refine ⟨E ∩ Metric.ball (par ψ p) ρ, Φ '' S₁, Φ '' S₂,
    hEopen'.preimage continuous_subtype_val, ?_, hEball, hU₁, hU₂,
    fun y hy => hUnionsub (Or.inl hy), fun y hy => hUnionsub (Or.inr hy), ?_⟩
  · obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hEopen (par ψ p) hparE
    refine ⟨min ε (ρ / 2), lt_min hεpos (by linarith), ?_⟩
    intro y hy
    obtain ⟨hyball, hyc⟩ := hy
    refine ⟨hεsub ((Metric.ball_subset_ball (min_le_left _ _)) hyball), ?_⟩
    exact Metric.ball_subset_ball (by linarith [min_le_right ε (ρ / 2)]) hyball
  · rw [← Set.inter_assoc, hgal, Set.union_inter_distrib_right,
      Set.inter_eq_self_of_subset_left (hU₁ball.trans hball_mono),
      Set.inter_eq_self_of_subset_left (hU₂ball.trans hball_mono)]


theorem gates_local {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s R : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ}
    (hG : Work.Drive.Final.GoodSweepData3 ψ K s c σ u v h R ℓ exc lam0 lam1)
    {p : ℝ × ℝ} (hp : Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ E U₁ U₂ : Set LeanEval.KnotTheory.PardonDistortion.R3,
      Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ) E ∧
      (∃ ε : ℝ, 0 < ε ∧ Metric.ball (Work.BoxShrink.Pinch.par ψ p) ε ∩
          (Work.Drive.EpsSphere.torusOf ψ).carrier ⊆ E) ∧
      E ⊆ Metric.ball (Work.BoxShrink.Pinch.par ψ p) ρ ∧
      (U₁ = ∅ ∨ IsPathConnected U₁) ∧ (U₂ = ∅ ∨ IsPathConnected U₂) ∧
      U₁ ⊆ E ∧ U₂ ⊆ E ∧
      Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
        (Work.Drive.Final.eventValue ψ ℓ p) ∩ E = U₁ ∪ U₂ := by
  unfold Work.Drive.Final.IsAnyEvent at hp
  rcases hp with h | h | h
  · exact eventGatesLocal hG h hρ
  · exact faceEventGatesLocal hG h hρ
  · exact cornerEventGatesLocal hG h hρ

end

end Work.Drive.Final
