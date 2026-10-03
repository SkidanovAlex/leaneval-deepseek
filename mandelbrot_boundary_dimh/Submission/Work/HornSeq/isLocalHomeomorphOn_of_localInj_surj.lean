import Mathlib

namespace Work.HornSeq

/-!
# Local homeomorphisms from local injectivity + local surjectivity onto balls

Auxiliary lemmas and the main statement: if `q : ℂ → ℂ` maps a set `Z` into a set `W`,
is continuous on `Z`, and is, around every point `x ∈ Z`, injective on a ball around `x`
intersected with `Z` while its image covers a ball around `q x`, then the induced map
`↥Z → ↥W` is a local homeomorphism.
-/

/-- **Local hitting lemma.** Under the local structure hypothesis `h`, any point of `W` close
enough to `q z` is the image of a point of `Z` that is close to `z` and stays within a
prescribed ball around `x₀`. -/
lemma aux_close {Z W : Set ℂ} {q : ℂ → ℂ}
    (h : ∀ x ∈ Z, ∀ ε : ℝ, 0 < ε → ∃ ρ δ : ℝ,
      0 < ρ ∧ ρ < ε ∧ 0 < δ ∧ Set.InjOn q (Metric.ball x ρ ∩ Z) ∧
      Metric.ball (q x) δ ⊆ q '' (Metric.ball x ρ ∩ Z))
    {x₀ z : ℂ} {ρ₀ : ℝ} (hz : z ∈ Z) (hzρ : dist z x₀ < ρ₀) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ W, dist w (q z) < δ →
      ∃ y ∈ Z, dist y x₀ < ρ₀ ∧ dist y z < ε ∧ q y = w := by
  intro ε hε
  have hεpos : 0 < min ε (ρ₀ - dist z x₀) := lt_min hε (by linarith)
  obtain ⟨ρ, δ, hρ, hρ', hδ, -, hsub⟩ := h z hz _ hεpos
  refine ⟨δ, hδ, fun w _ hwd => ?_⟩
  obtain ⟨y, hy, hyq⟩ := hsub (by simpa [Metric.mem_ball] using hwd)
  have hyz : dist y z < ρ := by simpa [Metric.mem_ball] using hy.1
  refine ⟨y, hy.2, ?_, ?_, hyq⟩
  · calc dist y x₀ ≤ dist y z + dist z x₀ := dist_triangle y z x₀
      _ < ρ + dist z x₀ := by linarith
      _ ≤ ρ₀ := by have h2 := min_le_right ε (ρ₀ - dist z x₀); linarith
  · calc dist y z < ρ := hyz
      _ < min ε (ρ₀ - dist z x₀) := hρ'
      _ ≤ ε := min_le_left _ _

/-- Injectivity of `q` on `ball x₀ ρ₀ ∩ Z` descends to injectivity of the induced map
`↥Z → ↥W` on the corresponding basic neighbourhood of a point of `Z`. -/
lemma aux_injOn {Z W : Set ℂ} {q : ℂ → ℂ} (hqZ : ∀ z ∈ Z, q z ∈ W)
    {x₀ : ℂ} {ρ₀ : ℝ} (hinj : Set.InjOn q (Metric.ball x₀ ρ₀ ∩ Z)) :
    Set.InjOn (fun z : ↥Z => (⟨q z, hqZ z z.2⟩ : ↥W)) {z : ↥Z | dist (z : ℂ) x₀ < ρ₀} := by
  intro z hz z' hz' heq
  have h1 : (z : ℂ) ∈ Metric.ball x₀ ρ₀ ∩ Z := ⟨by simpa [Metric.mem_ball] using hz, z.2⟩
  have h2 : (z' : ℂ) ∈ Metric.ball x₀ ρ₀ ∩ Z := ⟨by simpa [Metric.mem_ball] using hz', z'.2⟩
  refine Subtype.ext (hinj h1 h2 ?_)
  simpa using congrArg Subtype.val heq

theorem isLocalHomeomorphOn_of_localInj_surj {Z W : Set ℂ} {q : ℂ → ℂ} (hW : IsOpen W)
    (hcont : ContinuousOn q Z) (hqZ : ∀ z ∈ Z, q z ∈ W)
    (h : ∀ x ∈ Z, ∀ ε : ℝ, 0 < ε → ∃ ρ δ : ℝ,
      0 < ρ ∧ ρ < ε ∧ 0 < δ ∧ Set.InjOn q (Metric.ball x ρ ∩ Z) ∧
      Metric.ball (q x) δ ⊆ q '' (Metric.ball x ρ ∩ Z)) :
    IsLocalHomeomorphOn (fun z : ↥Z => (⟨q z, hqZ z z.2⟩ : ↥W)) Set.univ := by
  classical
  intro x _
  let f : ↥Z → ↥W := fun z => ⟨q z, hqZ z z.2⟩
  show ∃ e : OpenPartialHomeomorph ↥Z ↥W, x ∈ e.source ∧ f = e
  obtain ⟨ρ₀, δ₀, hρ₀, -, hδ₀, hinj, hsurj⟩ := h (x : ℂ) x.2 (1 : ℝ) one_pos
  haveI : Nonempty ↥Z := ⟨x⟩
  let U : Set ↥Z := {z | dist (z : ℂ) (x : ℂ) < ρ₀}
  have hxU : x ∈ U := by simp [U, hρ₀]
  have hUopen : IsOpen U := by
    have hUeq : U = Subtype.val ⁻¹' Metric.ball (x : ℂ) ρ₀ := by
      ext z; simp [U, Metric.mem_ball, Subtype.dist_eq]
    rw [hUeq]
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  have hinjU : Set.InjOn f U := aux_injOn hqZ hinj
  have hcontf : ContinuousOn f U := by
    have hqcont : Continuous (fun z : ↥Z => q (z : ℂ)) :=
      hcont.comp_continuous continuous_subtype_val (fun z => z.2)
    exact (hqcont.subtype_mk (fun z => hqZ z z.2)).continuousOn
  have hopen : IsOpenMap (U.domRestrict f) := by
    intro s' hs'
    rw [Metric.isOpen_iff] at hs' ⊢
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨ε₁, hε₁, hε₁'⟩ := hs' z hz
    obtain ⟨δ, hδ, hδ'⟩ := aux_close h
      (show (((z : U) : ↥Z) : ℂ) ∈ Z from ((z : U) : ↥Z).2)
      (show dist (((z : U) : ↥Z) : ℂ) (x : ℂ) < ρ₀ from (z : U).2) ε₁ hε₁
    refine ⟨δ, hδ, ?_⟩
    intro w hw
    have hwd : dist (w : ℂ) (q ((z : U) : ℂ)) < δ := by
      have h1 := Metric.mem_ball.mp hw
      rw [Subtype.dist_eq] at h1
      simpa [Set.domRestrict_apply, f] using h1
    obtain ⟨y, hyZ, hyx, hyz, hyq⟩ := hδ' (w : ℂ) w.2 hwd
    have hyU : (⟨y, hyZ⟩ : ↥Z) ∈ U := hyx
    refine ⟨⟨⟨y, hyZ⟩, hyU⟩, ?_, ?_⟩
    · apply hε₁'
      rw [Metric.mem_ball]
      simpa [Subtype.dist_eq] using hyz
    · apply Subtype.ext
      simpa [Set.domRestrict_apply, f] using hyq
  let e : PartialEquiv ↥Z ↥W := hinjU.toPartialEquiv f U
  refine ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict e hcontf hopen hUopen, hxU, ?_⟩
  exact (OpenPartialHomeomorph.coe_ofContinuousOpenRestrict e hcontf hopen hUopen).symm

end Work.HornSeq
