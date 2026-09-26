import Mathlib
import Submission.Work.Asymptotics.FunnelAsm.psumData
import Submission.Work.Asymptotics.FunnelAsm.decomp
import Submission.Work.Asymptotics.E_seminorm
import Submission.Work.Asymptotics.tileLayerSeminormTS
import Submission.Work.Asymptotics.seminormK_cusp0_arc
import Submission.Work.Asymptotics.DomainD_cover_half
import Submission.Work.Asymptotics.punctured_iteratedDeriv
import Submission.Work.Asymptotics.highPart_seminorm_scaled
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.TSasm.layerSemi_Tregion
import Submission.Work.Asymptotics.TSasm.cuspOneLowHalfTile_TS

/-! # Assembly of the `r`-seminorm bound for `paperLayer` on `𝒟`

This module isolates the *purely combinatorial* part of
`Work.CKFinal.paperLayer_seminorm_DomainD`: assuming the four cusp-region bounds

* `hfun` on the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}` (for `paperLayer` itself),
* `hE` on the cusp-`0` region `KEpsilon = {τ ∈ 𝒟 : 2 ≤ Im (S • τ)}`,
* `hls` on the low strip `{τ ∈ 𝒟 : 1/2 ≤ Im τ ≤ 2}`,
* `hch` on the two cusp-`±1` half tiles `{τ ∈ 𝒟 : 1/2 ≤ Im (S • (τ ∓ 1))}`,

together with the cusp-`0` half tile `Tregion = {τ ∈ 𝒟 : 1/2 ≤ Im (S • τ) ≤ 2}` (proved in the
workspace as `Work.Asymptotics.layerSemi_Tregion`), it proves the second conjunct of the target.

The cover is `Work.Asymptotics.DomainD_cover_half`: every `τ ∈ 𝒟` has `Im τ ≥ 1/2`, or
`S • τ ∈ 𝒟` with `Im (S • τ) ≥ 1/2`, or the same for `τ ∓ 1`.

The passage from `layer` (the punctured layer, for which all region bounds are stated in the
workspace) to `paperLayer` is `paperLayer_transfer`. -/

namespace Work.CKFinal

open scoped ContDiff Topology
open UpperHalfPlane Filter

/-! ## Elementary `scale` monotonicity -/

private lemma mul_rpow_le_mul_rpow {s a n C N : ℝ} (hs : 1 ≤ s) (ha : 0 ≤ a) (hn : 0 ≤ n)
    (haC : a ≤ C) (hnN : n ≤ N) : a * s ^ n ≤ C * s ^ N := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have h1 : s ^ n ≤ s ^ N := Real.rpow_le_rpow_of_exponent_le hs hnN
  have h2 : a * s ^ n ≤ a * s ^ N := mul_le_mul_of_nonneg_left h1 ha
  have h3 : a * s ^ N ≤ C * s ^ N := mul_le_mul_of_nonneg_right haC (Real.rpow_nonneg hs0.le N)
  linarith

/-! ## The single puncture: `layer` versus `paperLayer` -/

/-- On a region `K ⊆ 𝒟` where the `layer` seminorms are bounded, the *unpunctured* `paperLayer`
seminorms are bounded too (with adjusted constants).  The two functions differ only at `r = 0`:
for `l ≥ 1` the iterated derivative at `0` is the same (`punctured_iteratedDeriv`, using the
evenness of `paperLayer` in `r`), and for `l = 0` the value `paperLayer τ 0 = highPart τ 0` is
controlled by the moderate growth of the coefficient functions. -/
private lemma paperLayer_transfer {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} (hd : d = 8 ∨ d = 24)
    (K : UpperHalfPlane → Prop) (hK : ∀ τ : UpperHalfPlane, K τ → τ ∈ Work.Asymptotics.DomainD)
    (hcd : ∀ τ : UpperHalfPlane, K τ → ContDiff ℝ ∞
      (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s))
    {k l : ℕ} {C N : ℝ} (hC : 0 ≤ C) (hN : 0 ≤ N)
    (h : ∀ τ : UpperHalfPlane, K τ → ∀ r : ℝ,
      |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
        ≤ C * (Work.Kernels.scale τ) ^ N) :
    ∃ C' N' : ℝ, 0 ≤ C' ∧ 0 ≤ N' ∧
      ∀ τ : UpperHalfPlane, K τ → ∀ r : ℝ,
        |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
          ≤ C' * (Work.Kernels.scale τ) ^ N' := by
  obtain ⟨c₀, N₀, hc₀, hhp⟩ :=
    Work.Asymptotics.highPart_seminorm_scaled (Work.Asymptotics.Gcusp ℓ d)
      (fun i j => Work.Asymptotics.GcuspInP ℓ d i j) 0 0
  set M₀ : ℝ := max N₀ 0 with hM₀def
  have hM₀0 : 0 ≤ M₀ := le_max_right _ _
  have hhpb : ∀ (τ : UpperHalfPlane), τ ∈ Work.Asymptotics.DomainD → ∀ r : ℝ,
      ‖Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r‖
        ≤ c₀ * (Work.Kernels.scale τ) ^ M₀ := by
    intro τ hτ r
    exact le_trans (by simpa using hhp τ r hτ)
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ) (le_max_left _ _)) hc₀)
  refine ⟨C + c₀, N + M₀, by linarith, by linarith, ?_⟩
  intro τ hτ r
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hfinal : ∀ {a n : ℝ}, 0 ≤ a → 0 ≤ n → a ≤ C + c₀ → n ≤ N + M₀ →
      a * (Work.Kernels.scale τ) ^ n ≤ (C + c₀) * (Work.Kernels.scale τ) ^ (N + M₀) :=
    fun ha hn haC hnN => mul_rpow_le_mul_rpow hs1 ha hn haC hnN
  rcases eq_or_ne r 0 with hr | hr
  · subst hr
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl
      have hpl : Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ 0
          = Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ 0 := by
        rw [Work.Asymptotics.paperLayer]
        simp [Work.Asymptotics.layerLow, Work.Asymptotics.layerTrunc, Work.Asymptotics.sinSq]
      have hb : ‖Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ 0‖
          ≤ c₀ * (Work.Kernels.scale τ) ^ M₀ := hhpb τ (hK τ hτ) 0
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simp only [iteratedDeriv_zero, Nat.cast_zero, pow_zero, abs_zero, one_mul]
        rw [hpl]
        exact le_trans hb (hfinal hc₀ hM₀0 (by linarith) (by linarith))
      · have hz : |(0 : ℝ)| ^ k = 0 := by rw [abs_zero, zero_pow hk.ne']
        rw [hz, zero_mul]
        exact mul_nonneg (by linarith) (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) _)
    · have heq : iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)
          = iteratedDeriv l (fun s : ℝ =>
            Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) := by
        have hlay : (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)
            = fun s : ℝ => if s = 0 then 0 else
                Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s := by
          funext s
          by_cases hs : s = 0 <;> simp [Work.Asymptotics.layer, hs]
        rw [hlay]
        exact Work.Asymptotics.punctured_iteratedDeriv
          (f := fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)
          (fun s => Work.Asymptotics.arcT_paperLayer_neg (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)
          ((hcd τ hτ).differentiable (by simp)) l hl
      have hval : ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) 0‖
          = ‖iteratedDeriv l (fun s : ℝ =>
            Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) 0‖ := by
        rw [← heq]
      rw [hval]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        exact le_trans (h τ hτ 0) (hfinal hC hN (by linarith) (by linarith))
      · have hz : |(0 : ℝ)| ^ k = 0 := by rw [abs_zero, zero_pow hk.ne']
        rw [hz, zero_mul]
        exact mul_nonneg (by linarith) (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) _)
  · have hev : (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)
        =ᶠ[𝓝 r] (fun s : ℝ =>
          Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) := by
      filter_upwards [isOpen_ne.mem_nhds hr] with s hs
      rw [Work.Asymptotics.layer]
      simp [hs]
    rw [← Work.Asymptotics.iteratedDeriv_congr_of_eventuallyEq hev l]
    exact le_trans (h τ hτ r) (hfinal hC hN (by linarith) (by linarith))



/-! ## The assembly -/

/-- **The seminorm part of the target**, from the four region bounds. -/
theorem paperLayer_seminorm_DomainD_assembly (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (hfun : ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → ∀ r : ℝ,
        |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
          ≤ C * (Work.Kernels.scale τ) ^ N)
    (hE : ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.KEpsilon → ∀ r : ℝ,
        |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
          ≤ C * (Work.Kernels.scale τ) ^ N)
    (hls : ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD → (1 : ℝ) / 2 ≤ τ.im → τ.im ≤ 2 →
        ∀ r : ℝ,
        |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
          ≤ C * (Work.Kernels.scale τ) ^ N)
    (hch : ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ((∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD →
          ModularGroup.S • ((-1 : ℝ) +ᵥ τ) ∈ Work.Asymptotics.DomainD →
          (1 : ℝ) / 2 ≤ (ModularGroup.S • ((-1 : ℝ) +ᵥ τ)).im → ∀ r : ℝ,
          |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
            Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
            ≤ C * (Work.Kernels.scale τ) ^ N) ∧
        (∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD →
          ModularGroup.S • ((1 : ℝ) +ᵥ τ) ∈ Work.Asymptotics.DomainD →
          (1 : ℝ) / 2 ≤ (ModularGroup.S • ((1 : ℝ) +ᵥ τ)).im → ∀ r : ℝ,
          |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
            Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
            ≤ C * (Work.Kernels.scale τ) ^ N))) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD → ∀ r : ℝ,
        |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
          ≤ C * (Work.Kernels.scale τ) ^ N := by
  have hcd : ∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD → ContDiff ℝ ∞
      (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) :=
    fun τ hτ => (Work.Asymptotics.ts_paperLayer_contDiff_at ℓ d hd τ hτ).of_le le_top
  intro k l
  obtain ⟨C1, N1, hC1, hN1, h1⟩ := hfun k l
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := hE k l
  obtain ⟨C3, N3, hC3, hN3, h3⟩ := hls k l
  obtain ⟨C4, N4, hC4, hN4, h4c⟩ := hch k l
  obtain ⟨h4a, h4b⟩ := h4c
  obtain ⟨P6, hP6, h6⟩ := Work.Asymptotics.layerSemi_Tregion ℓ d hd k l
  obtain ⟨P2, Q2, hP2, hQ2, hp2⟩ := paperLayer_transfer hd (fun τ => τ ∈ Work.Asymptotics.KEpsilon)
    (fun τ hτ => Work.Asymptotics.KEpsilon_subset_DomainD hτ)
    (fun τ hτ => hcd τ (Work.Asymptotics.KEpsilon_subset_DomainD hτ)) hC2 hN2 h2
  obtain ⟨P3, Q3, hP3, hQ3, hp3⟩ := paperLayer_transfer hd
    (fun τ => τ ∈ Work.Asymptotics.DomainD ∧ (1 : ℝ) / 2 ≤ τ.im ∧ τ.im ≤ 2)
    (fun τ hτ => hτ.1) (fun τ hτ => hcd τ hτ.1) hC3 hN3
    (fun τ hτ r => h3 τ hτ.1 hτ.2.1 hτ.2.2 r)
  obtain ⟨P4, Q4, hP4, hQ4, hp4⟩ := paperLayer_transfer hd
    (fun τ => τ ∈ Work.Asymptotics.DomainD ∧
      ModularGroup.S • ((-1 : ℝ) +ᵥ τ) ∈ Work.Asymptotics.DomainD ∧
      (1 : ℝ) / 2 ≤ (ModularGroup.S • ((-1 : ℝ) +ᵥ τ)).im)
    (fun τ hτ => hτ.1) (fun τ hτ => hcd τ hτ.1) hC4 hN4
    (fun τ hτ r => h4a τ hτ.1 hτ.2.1 hτ.2.2 r)
  obtain ⟨P5, Q5, hP5, hQ5, hp5⟩ := paperLayer_transfer hd
    (fun τ => τ ∈ Work.Asymptotics.DomainD ∧
      ModularGroup.S • ((1 : ℝ) +ᵥ τ) ∈ Work.Asymptotics.DomainD ∧
      (1 : ℝ) / 2 ≤ (ModularGroup.S • ((1 : ℝ) +ᵥ τ)).im)
    (fun τ hτ => hτ.1) (fun τ hτ => hcd τ hτ.1) hC4 hN4
    (fun τ hτ r => h4b τ hτ.1 hτ.2.1 hτ.2.2 r)
  obtain ⟨P7, Q7, hP7, hQ7, hp7⟩ := paperLayer_transfer hd (fun τ => τ ∈ Work.Asymptotics.Tregion)
    (fun τ hτ => Work.Asymptotics.Tregion_subset_DomainD hτ)
    (fun τ hτ => hcd τ (Work.Asymptotics.Tregion_subset_DomainD hτ))
    (C := P6) (N := 0) hP6 le_rfl
    (fun τ hτ r => by rw [Real.rpow_zero, mul_one]; exact h6 τ r hτ)
  set C : ℝ := C1 + P2 + P3 + P4 + P5 + P7 + 1 with hCdef
  set N : ℝ := N1 + Q2 + Q3 + Q4 + Q5 + Q7 + 1 with hNdef
  have hC0 : (0 : ℝ) ≤ C := by rw [hCdef]; linarith
  have hN0 : (0 : ℝ) ≤ N := by rw [hNdef]; linarith
  refine ⟨C, N, hC0, hN0, ?_⟩
  intro τ hτ r
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hC1' : C1 ≤ C := by rw [hCdef]; linarith
  have hN1' : N1 ≤ N := by rw [hNdef]; linarith
  have hP2' : P2 ≤ C := by rw [hCdef]; linarith
  have hQ2' : Q2 ≤ N := by rw [hNdef]; linarith
  have hP3' : P3 ≤ C := by rw [hCdef]; linarith
  have hQ3' : Q3 ≤ N := by rw [hNdef]; linarith
  have hP4' : P4 ≤ C := by rw [hCdef]; linarith
  have hQ4' : Q4 ≤ N := by rw [hNdef]; linarith
  have hP5' : P5 ≤ C := by rw [hCdef]; linarith
  have hQ5' : Q5 ≤ N := by rw [hNdef]; linarith
  have hP7' : P7 ≤ C := by rw [hCdef]; linarith
  have hQ7' : Q7 ≤ N := by rw [hNdef]; linarith
  rcases Work.Asymptotics.DomainD_cover_half τ hτ with hcase | hcase | hcase | hcase
  · by_cases h2 : 2 ≤ τ.im
    · exact le_trans (h1 τ hτ h2 r) (mul_rpow_le_mul_rpow hs1 hC1 hN1 hC1' hN1')
    · exact le_trans (hp3 τ ⟨hτ, hcase, le_of_lt (not_le.mp h2)⟩ r)
        (mul_rpow_le_mul_rpow hs1 hP3 hQ3 hP3' hQ3')
  · obtain ⟨hSD, hS1⟩ := hcase
    by_cases h2 : 2 ≤ (ModularGroup.S • τ).im
    · exact le_trans (hp2 τ ⟨hτ, h2⟩ r) (mul_rpow_le_mul_rpow hs1 hP2 hQ2 hP2' hQ2')
    · exact le_trans (hp7 τ ⟨hτ, hS1, le_of_lt (not_le.mp h2)⟩ r)
        (mul_rpow_le_mul_rpow hs1 hP7 hQ7 hP7' hQ7')
  · obtain ⟨hSD, hS1⟩ := hcase
    exact le_trans (hp4 τ ⟨hτ, hSD, hS1⟩ r) (mul_rpow_le_mul_rpow hs1 hP4 hQ4 hP4' hQ4')
  · obtain ⟨hSD, hS1⟩ := hcase
    exact le_trans (hp5 τ ⟨hτ, hSD, hS1⟩ r) (mul_rpow_le_mul_rpow hs1 hP5 hQ5 hP5' hQ5')

end Work.CKFinal
