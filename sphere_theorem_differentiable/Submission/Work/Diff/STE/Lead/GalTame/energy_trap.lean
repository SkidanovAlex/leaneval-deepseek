import Mathlib
import Submission.Work.Diff.STE.Lead.Gal.hasDerivAt_galE
import Submission.Work.Diff.STE.Lead.Gal.galE_apriori
import Submission.Work.Diff.STE.Lead.Gal.Prelude
import Submission.Work.Diff.STE.Lead.Gal.galVF2_lipschitz_on_pos

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

/-! `energy_trap`: the energy part of the trapping lemma — any solution of the span-form Galerkin ODE
on `[0,T]` starting at the origin, pinched at level `1/4` on `[0,T)`, keeps `galE ≤ B` on `[0,T]`,
provided the Grönwall constant satisfies `Cof (1/4) * τ₀ ≤ log (1 + B⁻¹)` and `T ≤ τ₀`.

PROOF (first-exit, mirroring `Work.Diff.STE.flat.galerkin_bootstrap`'s `trapping`): suppose the energy
first exceeds `B`; let `T₁ := sInf {s ∈ [0, min T τ₀] : B < galE (c s)}`.  On `[0,T₁)` the energy is
`≤ B` and the pinching holds, so `hapr` with `lam = 1/4` gives the Grönwall bound on `[0,T₁)`, and
passing to the limit (the energy is differentiable in `t` by
`Work.Diff.STE.Lead.Gal.hasDerivAt_galE` composed with the ODE) gives
`galE (c T₁) ≤ (galE (c 0) + 1) * exp (Cof (1/4) * T₁) - 1 ≤ B * (1 + B⁻¹) - 1 = B`; the inequality is
strict in the relevant cases, contradicting the minimality of `T₁` (note: no sign hypothesis on
`Cof (1/4)` is needed — if it is negative the exponential is `≤ 1` and the bound is even better). -/

theorem energy_trap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) (g₀.inner))
    (k₀ : ℕ) (B : ℝ) (ε₁ : ℝ) (Cof : ℝ → ℝ) (τ₀ : ℝ)
    (hapr : ∀ (lam : ℝ), 0 < lam → ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ ε₁ →
      ∀ (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)) (T : ℝ), 0 < T →
      (∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt c (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
        lam * g₀.inner x v v
          ≤ (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, Work.Diff.STE.Lead.galE D k₀ ε (c t) ≤ B) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        Work.Diff.STE.Lead.galE D k₀ ε (c t)
          ≤ (Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1) * Real.exp (Cof lam * t) - 1)
    (hτ : Cof (1 / 4) * τ₀ ≤ Real.log (1 + B⁻¹))
    (hB0 : 0 < B)
    (hE0 : ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ ε₁ →
      Work.Diff.STE.Lead.galE D k₀ ε
        (0 : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ≤ B - 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ ε₁) (T : ℝ)
    (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ))
    (hT0 : 0 ≤ T) (hTτ : T ≤ τ₀) (hc0 : c 0 = 0)
    (hode : ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivAt c (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t)
    (hpin : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
      (1 / 4 : ℝ) * g₀.inner x v v
        ≤ (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, Work.Diff.STE.Lead.galE D k₀ ε (c t) ≤ B := by
  -- ## Elementary facts about the initial energy
  have hy0 : Work.Diff.STE.Lead.galE D k₀ ε (c 0) ≤ B - 1 := by
    rw [hc0]; exact hE0 ε hε hε1
  have hy0nn : 0 ≤ Work.Diff.STE.Lead.galE D k₀ ε (c 0) :=
    Work.Diff.STE.Lead.Gal.galE_nonneg D k₀ ε (c 0)
  have hy0lt : Work.Diff.STE.Lead.galE D k₀ ε (c 0) < B := by linarith
  have hA : Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1 ≤ B := by linarith
  have hA1 : 0 ≤ Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1 := by linarith
  have hBinv : 0 < B⁻¹ := inv_pos.mpr hB0
  have hlogpos : 0 < Real.log (1 + B⁻¹) := Real.log_pos (by linarith)
  -- ## The energy is continuous along the solution
  have hcont : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ContinuousAt (fun s : ℝ => Work.Diff.STE.Lead.galE D k₀ ε (c s)) t :=
    fun t ht => (Work.Diff.STE.Lead.Gal.hasDerivAt_galE (I := I) (M := M) D k₀ ε hg
      (hode t ht)).continuousAt
  -- ## The strict-neighbourhood property of the sublevel set `{energy < B}`
  have hstrict : ∀ t₀ ∈ Set.Icc (0 : ℝ) T, Work.Diff.STE.Lead.galE D k₀ ε (c t₀) < B →
      ∃ δ > 0, ∀ s ∈ Set.Icc (0 : ℝ) T, |s - t₀| < δ →
        Work.Diff.STE.Lead.galE D k₀ ε (c s) < B := by
    intro t₀ ht₀ hlt
    have hmem : {x : ℝ | x < B} ∈ nhds (Work.Diff.STE.Lead.galE D k₀ ε (c t₀)) :=
      isOpen_Iio.mem_nhds hlt
    obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhds_iff.mp ((hcont t₀ ht₀).tendsto.eventually hmem)
    exact ⟨δ, hδ, fun s _ hsd => hδ' (by rw [Metric.mem_ball, Real.dist_eq]; exact hsd)⟩
  -- ## The Grönwall comparison function
  set Φ : ℝ → ℝ := fun s => (Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1)
    * Real.exp (Cof (1 / 4) * s) - 1 with hΦ
  -- ## First exit
  intro t ht
  by_contra hcon
  have htbad : B < Work.Diff.STE.Lead.galE D k₀ ε (c t) := not_le.mp hcon
  set S : Set ℝ := Set.Icc (0 : ℝ) T ∩
    {s : ℝ | B < Work.Diff.STE.Lead.galE D k₀ ε (c s)} with hS
  have hS₁ : ∀ s ∈ S, 0 ≤ s := fun s hs => by
    have h := hs; rw [hS] at h; exact h.1.1
  have hS₂ : ∀ s ∈ S, s ≤ T := fun s hs => by
    have h := hs; rw [hS] at h; exact h.1.2
  have hS₃ : ∀ s ∈ S, B < Work.Diff.STE.Lead.galE D k₀ ε (c s) := fun s hs => by
    have h := hs; rw [hS] at h; exact h.2
  have hSne : S.Nonempty := ⟨t, by rw [hS]; exact ⟨ht, htbad⟩⟩
  have hSbdd : BddBelow S := ⟨0, fun s hs => hS₁ s hs⟩
  set τ₂ : ℝ := sInf S with hτ₂def
  have hτ₂_le_T : τ₂ ≤ T := by
    obtain ⟨s₀, hs₀⟩ := hSne
    have h1 := csInf_le hSbdd hs₀
    rw [← hτ₂def] at h1
    linarith [hS₂ s₀ hs₀]
  have hτ₂ge : 0 ≤ τ₂ := by
    have h1 := le_csInf hSne (fun s hs => hS₁ s hs)
    rwa [← hτ₂def] at h1
  have hτ₂Icc : τ₂ ∈ Set.Icc (0 : ℝ) T := ⟨hτ₂ge, hτ₂_le_T⟩
  have hτ₂pos : 0 < τ₂ := by
    obtain ⟨δ, hδ, hδ'⟩ := hstrict 0 ⟨le_rfl, hT0⟩ hy0lt
    have hle : δ ≤ τ₂ := by
      refine le_csInf hSne (fun s hs => ?_)
      by_contra hlt
      have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hS₁ s hs, hS₂ s hs⟩
      have hmem := hδ' s hsIcc (by rw [sub_zero, abs_of_nonneg hsIcc.1]; exact not_le.mp hlt)
      linarith [hS₃ s hs, hmem]
    linarith
  -- ## The energy stays below `B` on `[0, τ₂)`
  have hbelow : ∀ s ∈ Set.Ico (0 : ℝ) τ₂, Work.Diff.STE.Lead.galE D k₀ ε (c s) ≤ B := by
    intro s hs
    by_contra hc
    have hsS : s ∈ S := by
      rw [hS]
      exact ⟨⟨hs.1, le_of_lt (lt_of_lt_of_le hs.2 hτ₂_le_T)⟩, not_le.mp hc⟩
    have h1 := csInf_le hSbdd hsS
    rw [← hτ₂def] at h1
    linarith [hs.2]
  -- ## The Grönwall bound of `hapr` on `[0, τ₂)`
  have hGrönwall : ∀ s ∈ Set.Ico (0 : ℝ) τ₂,
      Work.Diff.STE.Lead.galE D k₀ ε (c s) ≤ Φ s := by
    have h := hapr (1 / 4) (by norm_num) ε hε hε1 c τ₂ hτ₂pos
      (fun s hs => hode s ⟨hs.1, le_of_lt (lt_of_lt_of_le hs.2 hτ₂_le_T)⟩)
      (fun s hs x v hv => by
        have hp := hpin s ⟨hs.1, lt_of_lt_of_le hs.2 hτ₂_le_T⟩ x v
        have hgv := g₀.pos x v hv
        linarith)
      (fun s hs x v => hpin s ⟨hs.1, lt_of_lt_of_le hs.2 hτ₂_le_T⟩ x v)
      hbelow
    intro s hs
    rw [hΦ]
    exact h s hs
  -- ## Passing to the limit at `τ₂`
  have hlimbound : Work.Diff.STE.Lead.galE D k₀ ε (c τ₂) ≤ Φ τ₂ := by
    have hFcont : ContinuousAt Φ τ₂ := by
      rw [hΦ]
      exact ContinuousAt.sub (ContinuousAt.mul continuousAt_const
        (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul continuousAt_id)))
        continuousAt_const
    have hdiff : ContinuousAt
        (fun s : ℝ => Work.Diff.STE.Lead.galE D k₀ ε (c s) - Φ s) τ₂ :=
      (hcont τ₂ hτ₂Icc).sub hFcont
    have hmax : max 0 (τ₂ - 1) < τ₂ := max_lt hτ₂pos (by linarith)
    have hmono : ∀ᶠ s in nhdsWithin τ₂ (Set.Iio τ₂),
        Work.Diff.STE.Lead.galE D k₀ ε (c s) - Φ s ≤ 0 := by
      filter_upwards [Ioo_mem_nhdsLT hmax] with s hs
      have hs' : s ∈ Set.Ico (0 : ℝ) τ₂ :=
        ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hs.1), hs.2⟩
      linarith [hGrönwall s hs']
    have h0 := le_of_tendsto (hdiff.tendsto.mono_left nhdsWithin_le_nhds) hmono
    linarith
  rw [hΦ] at hlimbound
  -- ## The numerical bound at `τ₂`
  have hle_log : Cof (1 / 4) * τ₂ ≤ Real.log (1 + B⁻¹) := by
    rcases le_or_gt 0 (Cof (1 / 4)) with hc | hc
    · calc Cof (1 / 4) * τ₂ ≤ Cof (1 / 4) * τ₀ :=
          mul_le_mul_of_nonneg_left (le_trans hτ₂_le_T hTτ) hc
        _ ≤ Real.log (1 + B⁻¹) := hτ
    · have : Cof (1 / 4) * τ₂ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc.le hτ₂ge
      linarith
  have hexp_le : Real.exp (Cof (1 / 4) * τ₂) ≤ 1 + B⁻¹ := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < 1 + B⁻¹)]
    exact Real.exp_le_exp.mpr hle_log
  have hBone : B * (1 + B⁻¹) = B + 1 := by
    rw [mul_add, mul_one, mul_inv_cancel₀ (ne_of_gt hB0)]
  have hstep : (Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1)
      * Real.exp (Cof (1 / 4) * τ₂) - 1 ≤ B := by
    have h1 : (Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1)
          * Real.exp (Cof (1 / 4) * τ₂)
        ≤ B * Real.exp (Cof (1 / 4) * τ₂) :=
      mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
    have h2 : B * Real.exp (Cof (1 / 4) * τ₂) ≤ B * (1 + B⁻¹) :=
      mul_le_mul_of_nonneg_left hexp_le hB0.le
    linarith
  have hleB : Work.Diff.STE.Lead.galE D k₀ ε (c τ₂) ≤ B := by linarith
  -- ## Contradiction with the minimality of `τ₂`
  by_cases hcase : τ₂ < T
  · -- the strict case: the comparison bound is *strictly* below `B`
    have hlt_log : Cof (1 / 4) * τ₂ < Real.log (1 + B⁻¹) := by
      rcases lt_trichotomy (Cof (1 / 4)) 0 with hc | hc | hc
      · have : Cof (1 / 4) * τ₂ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc.le hτ₂ge
        linarith
      · rw [hc, zero_mul]; linarith
      · have : Cof (1 / 4) * τ₂ < Cof (1 / 4) * τ₀ :=
          mul_lt_mul_of_pos_left (lt_of_lt_of_le hcase hTτ) hc
        linarith
    have hexp_lt : Real.exp (Cof (1 / 4) * τ₂) < 1 + B⁻¹ := by
      rw [← Real.exp_log (by linarith : (0 : ℝ) < 1 + B⁻¹)]
      exact Real.exp_lt_exp.mpr hlt_log
    have hAG : (Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1)
        * Real.exp (Cof (1 / 4) * τ₂) < B + 1 := by
      have h2 : B * Real.exp (Cof (1 / 4) * τ₂) < B * (1 + B⁻¹) :=
        mul_lt_mul_of_pos_left hexp_lt hB0
      rcases lt_or_eq_of_le hA with hAlt | hAeq
      · have h1 : (Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1)
            * Real.exp (Cof (1 / 4) * τ₂)
          ≤ (Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1) * (1 + B⁻¹) :=
          mul_le_mul_of_nonneg_left hexp_lt.le hA1
        have h4 : (Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1) * (1 + B⁻¹)
            < B * (1 + B⁻¹) :=
          mul_lt_mul_of_pos_right hAlt (by linarith)
        linarith
      · rw [hAeq]; linarith
    have hyτ₂lt : Work.Diff.STE.Lead.galE D k₀ ε (c τ₂) < B := by linarith
    obtain ⟨δ, hδ0, hδ'⟩ := hstrict τ₂ hτ₂Icc hyτ₂lt
    obtain ⟨s, hsS, hslt⟩ : ∃ s ∈ S, s < τ₂ + δ := by
      by_contra hcon'
      push_neg at hcon'
      have h1 : τ₂ + δ ≤ τ₂ := by
        have h2 := le_csInf hSne (fun s hs => hcon' s hs)
        rw [← hτ₂def] at h2
        exact h2
      linarith
    have hsge : τ₂ ≤ s := by
      have h2 := csInf_le hSbdd hsS
      rw [← hτ₂def] at h2
      exact h2
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hS₁ s hsS, hS₂ s hsS⟩
    have hmem := hδ' s hsIcc (by rw [abs_of_nonneg (by linarith)]; linarith)
    linarith [hS₃ s hsS, hmem]
  · -- the endpoint case: `S = {T}`, but the bound at `T` is `≤ B`
    have hτ₂Teq : τ₂ = T := le_antisymm hτ₂_le_T (not_lt.mp hcase)
    obtain ⟨s₀, hs₀⟩ := hSne
    have hs₀T : s₀ = T := by
      have h1 := csInf_le hSbdd hs₀
      rw [← hτ₂def, hτ₂Teq] at h1
      exact le_antisymm (hS₂ s₀ hs₀) h1
    have hbad : B < Work.Diff.STE.Lead.galE D k₀ ε (c τ₂) := by
      have h1 := hS₃ s₀ hs₀
      rw [hs₀T, ← hτ₂Teq] at h1
      exact h1
    linarith

end Work.Diff.STE.Lead.GalTame
