import Mathlib
import Submission.Work.Drive.Generic.nclmPkg

/-!
# Reassembling the chart data from its clause packages

`Work.Drive.Generic.nclm_dataC_of_packages` turns the five clause packages (`nclmPkgScale`,
`nclmPkgProfile`, `nclmPkgEndpoints`, `nclmPkgChamfer`, `nclmPkgConcave`) into the full chart data
`nclmDataC`: the ε-level thresholds are minimised, the constants of the packages are merged by
`min`/`max` (every clause is monotone in its constants in the favourable direction), and the clauses
are re-emitted.  The only clause proved outright here is the differentiability of the profile
ordinate `nclmAH` (analyticity of the knot).
-/

noncomputable section
namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant

/-- The profile ordinate `nclmAH` is differentiable everywhere (the knot is smooth). -/
lemma nclmAH_differentiableAt {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) (lam δ₁ δ₂ ε σ : ℝ) (v : Space) (ξ : ℝ) :
    DifferentiableAt ℝ (nclmAH r D lam δ₁ δ₂ ε σ v) ξ := by
  have h1 : DifferentiableAt ℝ (fun x : ℝ =>
      r (Work.Drive.taR D σ + x * Work.Drive.sweepW' D σ)) ξ :=
    (hr.smooth.differentiable (by simp)).differentiableAt.comp ξ (by fun_prop)
  have h2 : DifferentiableAt ℝ (fun x : ℝ =>
      r (Work.Drive.taR D σ + x * Work.Drive.sweepW' D σ)
        - Work.Drive.chartC r D lam δ₁ δ₂ ε v) ξ :=
    h1.sub (differentiableAt_const _)
  have h3 : DifferentiableAt ℝ (fun x : ℝ => inner ℝ
      (r (Work.Drive.taR D σ + x * Work.Drive.sweepW' D σ)
        - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
      (Work.Drive.chartE r D lam δ₁ δ₂ ε v)) ξ :=
    DifferentiableAt.inner ℝ h2 (differentiableAt_const _)
  change DifferentiableAt ℝ (fun x : ℝ => inner ℝ
      (r (Work.Drive.taR D σ + x * Work.Drive.sweepW' D σ)
        - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
      (Work.Drive.chartE r D lam δ₁ δ₂ ε v)) ξ
  exact h3

/-- **The chart data from its clause packages.** -/
theorem nclm_dataC_of_packages {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d)
    (hScale : nclmPkgScale r D) (hProfile : nclmPkgProfile r D)
    (hEnd : nclmPkgEndpoints r D) (hCham : nclmPkgChamfer r D) (hConc : nclmPkgConcave r D) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ (cℓ Cℓ ch Ch cm cE cK Λ : ℝ),
        0 < cℓ ∧ 0 < Cℓ ∧ 0 < ch ∧ 0 < Ch ∧ 0 < cm ∧ 0 < cE ∧ 0 ≤ cK ∧ 0 < Λ ∧
        ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
          0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∀ (v : Space), ‖v‖ = 1 →
          Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε
            = ‖Work.Drive.chordEndB r D δ₂ ε - Work.Drive.chordEndA r D δ₂ ε‖ • v →
          nclmDataC r D lam δ₁ δ₂ ε v cℓ Cℓ ch Ch cm cE cK := by
  obtain ⟨ε₁, hε₁0, H₁⟩ := hScale
  obtain ⟨ε₂, hε₂0, H₂⟩ := hProfile
  obtain ⟨ε₃, hε₃0, H₃⟩ := hEnd
  obtain ⟨ε₄, hε₄0, H₄⟩ := hCham
  obtain ⟨ε₅, hε₅0, H₅⟩ := hConc
  refine ⟨min (min (min (min ε₁ ε₂) (min ε₃ ε₄)) ε₅) (1 / 2),
    lt_min (lt_min (lt_min (lt_min hε₁0 hε₂0) (lt_min hε₃0 hε₄0)) hε₅0) (by norm_num),
    fun ε hε hεε => ?_⟩
  have hεA : ε ≤ min (min (min ε₁ ε₂) (min ε₃ ε₄)) ε₅ := le_trans hεε (min_le_left _ _)
  have hε12 : ε ≤ 1 / 2 := le_trans hεε (min_le_right _ _)
  have hεB : ε ≤ min (min ε₁ ε₂) (min ε₃ ε₄) := le_trans hεA (min_le_left _ _)
  have hε5 : ε ≤ ε₅ := le_trans hεA (min_le_right _ _)
  have hεC : ε ≤ min ε₁ ε₂ := le_trans hεB (min_le_left _ _)
  have hεD : ε ≤ min ε₃ ε₄ := le_trans hεB (min_le_right _ _)
  have hε1 : ε ≤ ε₁ := le_trans hεC (min_le_left _ _)
  have hε2 : ε ≤ ε₂ := le_trans hεC (min_le_right _ _)
  have hε3 : ε ≤ ε₃ := le_trans hεD (min_le_left _ _)
  have hε4 : ε ≤ ε₄ := le_trans hεD (min_le_right _ _)
  obtain ⟨cℓ, Cℓ, ch₁, Ch, Λ₁, hcℓ, hCℓ, hch₁, hCh, hΛ₁, H₁'⟩ := H₁ ε hε hε1
  obtain ⟨cm, ch₂, Λ₂, hcm, hch₂, hΛ₂, H₂'⟩ := H₂ ε hε hε2
  obtain ⟨Λ₃, hΛ₃, H₃'⟩ := H₃ ε hε hε3
  obtain ⟨cE, cK, Λ₄, hcE, hcK, hΛ₄, H₄'⟩ := H₄ ε hε hε4
  obtain ⟨Λ₅, hΛ₅, H₅'⟩ := H₅ ε hε hε5
  have hWpos : 0 < Work.Drive.sweepW' D ε :=
    Work.Drive.wds_sweepW'_pos D hε (by linarith [hε12])
  refine ⟨cℓ, Cℓ, min ch₁ ch₂, Ch, cm, cE, cK, min (min (min (min Λ₁ Λ₂) Λ₃) Λ₄) Λ₅,
    hcℓ, hCℓ, lt_min hch₁ hch₂, hCh, hcm, hcE, hcK, ?_, ?_⟩
  · exact lt_min (lt_min (lt_min (lt_min hΛ₁ hΛ₂) hΛ₃) hΛ₄) hΛ₅
  intro lam δ₁ δ₂ hlam0 hlamΛ hlam2 hδ₁0 hδ₁Λ hδ₂0 hδ₂Λ hδ₂ε v hv hb
  have hΛAB : lam ≤ min (min (min Λ₁ Λ₂) Λ₃) Λ₄ := le_trans hlamΛ (min_le_left _ _)
  have hΛ₅' : lam ≤ Λ₅ := le_trans hlamΛ (min_le_right _ _)
  have hΛABC : lam ≤ min (min Λ₁ Λ₂) Λ₃ := le_trans hΛAB (min_le_left _ _)
  have hΛ₄' : lam ≤ Λ₄ := le_trans hΛAB (min_le_right _ _)
  have hΛA : lam ≤ min Λ₁ Λ₂ := le_trans hΛABC (min_le_left _ _)
  have hΛ₁' : lam ≤ Λ₁ := le_trans hΛA (min_le_left _ _)
  have hΛ₂' : lam ≤ Λ₂ := le_trans hΛA (min_le_right _ _)
  have hΛ₃' : lam ≤ Λ₃ := le_trans hΛABC (min_le_right _ _)
  have hδAB : δ₁ ≤ min (min (min Λ₁ Λ₂) Λ₃) Λ₄ := le_trans hδ₁Λ (min_le_left _ _)
  have hδ₅ : δ₁ ≤ Λ₅ := le_trans hδ₁Λ (min_le_right _ _)
  have hδABC : δ₁ ≤ min (min Λ₁ Λ₂) Λ₃ := le_trans hδAB (min_le_left _ _)
  have hδ₄ : δ₁ ≤ Λ₄ := le_trans hδAB (min_le_right _ _)
  have hδA : δ₁ ≤ min Λ₁ Λ₂ := le_trans hδABC (min_le_left _ _)
  have hδ₁₁ : δ₁ ≤ Λ₁ := le_trans hδA (min_le_left _ _)
  have hδ₁₂ : δ₁ ≤ Λ₂ := le_trans hδA (min_le_right _ _)
  have hδ₁₃ : δ₁ ≤ Λ₃ := le_trans hδABC (min_le_right _ _)
  have hΔAB : δ₂ ≤ min (min (min Λ₁ Λ₂) Λ₃) Λ₄ := le_trans hδ₂Λ (min_le_left _ _)
  have hΔ₅ : δ₂ ≤ Λ₅ := le_trans hδ₂Λ (min_le_right _ _)
  have hΔABC : δ₂ ≤ min (min Λ₁ Λ₂) Λ₃ := le_trans hΔAB (min_le_left _ _)
  have hΔ₄ : δ₂ ≤ Λ₄ := le_trans hΔAB (min_le_right _ _)
  have hΔA : δ₂ ≤ min Λ₁ Λ₂ := le_trans hΔABC (min_le_left _ _)
  have hδ₂₁ : δ₂ ≤ Λ₁ := le_trans hΔA (min_le_left _ _)
  have hδ₂₂ : δ₂ ≤ Λ₂ := le_trans hΔA (min_le_right _ _)
  have hδ₂₃ : δ₂ ≤ Λ₃ := le_trans hΔABC (min_le_right _ _)
  obtain ⟨hws, hℓpos, hℓlo, hℓhi, hE1, hEv, hhlo, hhhi⟩ :=
    H₁' lam δ₁ δ₂ hlam0 hΛ₁' hlam2 hδ₁0 hδ₁₁ hδ₂0 hδ₂₁ hδ₂ε v hv hb
  obtain ⟨htan, hmono, hxpos0, hxposb, hξ₀raw⟩ :=
    H₂' lam δ₁ δ₂ hlam0 hΛ₂' hlam2 hδ₁0 hδ₁₂ hδ₂0 hδ₂₂ hδ₂ε v hv hb
  obtain ⟨hHbd, hend⟩ := H₃' lam δ₁ δ₂ hlam0 hΛ₃' hlam2 hδ₁0 hδ₁₃ hδ₂0 hδ₂₃ hδ₂ε v hv hb
  obtain ⟨hacc, hdev, hbr⟩ := H₄' lam δ₁ δ₂ hlam0 hΛ₄' hlam2 hδ₁0 hδ₄ hδ₂0 hΔ₄ hδ₂ε v hv hb
  obtain hchord := H₅' lam δ₁ δ₂ hlam0 hΛ₅' hlam2 hδ₁0 hδ₅ hδ₂0 hΔ₅ hδ₂ε v hv hb
  have hWs : (0 : ℝ) ≤ Work.Drive.sweepW' D ε ^ 2 := sq_nonneg _
  have hchle : min ch₁ ch₂ ≤ ch₁ := min_le_left _ _
  have hchle₂ : min ch₁ ch₂ ≤ ch₂ := min_le_right _ _
  have hhlo' : min ch₁ ch₂ * Work.Drive.sweepW' D ε ^ 2
      ≤ ‖Work.Drive.chartUp r D lam δ₁ δ₂ ε v‖ / 2 :=
    le_trans (mul_le_mul_of_nonneg_right hchle hWs) hhlo
  have hξ₀ : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
      ∃ ξ₀ ∈ Set.Ioo lam (1 - lam),
        nclmAX r D lam δ₁ δ₂ ε σ v ξ₀ = 0
          ∧ min ch₁ ch₂ * Work.Drive.sweepW' D ε ^ 2
            ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ₀ := by
    intro σ h1 h2
    obtain ⟨ξ₀, hmem, hX0, hH0⟩ := hξ₀raw σ h1 h2
    exact ⟨ξ₀, hmem, hX0, le_trans (mul_le_mul_of_nonneg_right hchle₂ hWs) hH0⟩
  have hdiff : ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ → ∀ ξ ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (nclmAH r D lam δ₁ δ₂ ε σ v) ξ := by
    intro σ _ _ ξ _; exact nclmAH_differentiableAt hr D lam δ₁ δ₂ ε σ v ξ
  exact ⟨hWpos, hws, hℓpos, hℓlo, hℓhi, hE1, hEv, htan, hacc, hhlo', hhhi,
    hmono, hxpos0, hxposb, hdiff, hchord, hξ₀, hHbd, hend, hdev, hbr⟩

end Work.Drive.Generic
