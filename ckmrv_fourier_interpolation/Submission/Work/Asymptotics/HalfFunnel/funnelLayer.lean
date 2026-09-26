/-
# The funnel `r`-seminorm bound for the CKMRV layer `F₂`

This file proves `Work.Asymptotics.HalfFunnel.funnelLayer`: on the funnel
`{τ ∈ 𝒟 : 2 ≤ Im τ}` the `r`-seminorms of the CKMRV layer
`layer (Gcusp ℓ d) ℓ d τ · = low + trunc + high` grow at most moderately,

  `|r|^k ‖∂_r^l (layer τ ·) r‖ ≤ α (Im τ)^{-β} + γ ‖τ‖^δ`

with `α, β, γ, δ ≥ 0` depending only on `k, l` (and `ℓ, d`).

## The reduction

`layer = if r = 0 then 0 else paperLayer` and `paperLayer = layerLow + layerTrunc + highPart`
(`Work.Asymptotics.F2LayerDefs`).  Accordingly the bound is assembled from three pieces:

* `layerLow`: `sinSq r · ∫_0^1 K(τ,it) e^{-πr²t} dt`, bounded on the funnel by the flatness of the
  kernel at the cusp `0` (the hypothesis `hflat` of the statement, the conclusion of the sibling
  `Work.Asymptotics.HalfFunnel.funnelFlat`);
* `layerTrunc`: `sinSq r · ∫_1^∞ (K - 𝒢)(τ,it) e^{-πr²t} dt`, bounded with the funnel estimates
  `funnelKernelPre` (window), `funnelKernelSpike` (the two translate poles near `t = Im τ`),
  `funnelKernelTail` (the cusp-`i∞` expansion above the poles) and the smallness of the `i = 1`
  row of `Gcusp` (which is what makes `Aexp` polynomially bounded below the pole);
* `highPart`: the explicit closed form, bounded by `Work.Asymptotics.highPart_seminorm`.

Each of the three pieces is `C^ω` in `r` on the funnel, so `iteratedDeriv` distributes over the
sum; the single puncture of `layer` at `r = 0` is handled by
`Work.Asymptotics.punctured_iteratedDeriv` (the layer is even in `r` and
`paperLayer_neg` is unconditional), and the remaining cases at `r = 0` are trivial.

Finally the `scale τ`-form of the bound is converted to the requested
`α (Im τ)^{-β} + γ ‖τ‖^δ` form with `scale_rpow_le` (`scale τ = 1 + (Im τ)⁻¹ + ‖τ‖`).
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.layerLow_seminorm
import Submission.Work.Asymptotics.layerTrunc_seminorm_of_tailBound
import Submission.Work.Asymptotics.highPart_seminorm
import Submission.Work.Asymptotics.E_TailClosed
import Submission.Work.Asymptotics.HalfFunnel.layerLowFree
import Submission.Work.Asymptotics.HalfFunnel.funnelKernelWindow
import Submission.Work.Asymptotics.HalfFunnel.GcuspRow11Small
import Submission.Work.Asymptotics.HalfFunnel.funnelLayerTrunc
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.kernelTransform_seminorm_of_layer
import Submission.Work.Asymptotics.punctured_iteratedDeriv
import Submission.Work.Asymptotics.paperLayer_smooth

namespace Work.Asymptotics.HalfFunnel

open UpperHalfPlane
open scoped Topology ContDiff

noncomputable section

/-! ## Evenness of the layer in `r` (copied: the original lives in a module of the other
`KernelBoundAux` world, which cannot be imported together with the funnel-spike machinery) -/

lemma layerLow_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    Work.Asymptotics.layerLow ℓ d τ (-s) = Work.Asymptotics.layerLow ℓ d τ s := by
  have hsq : (((-s : ℝ)) : ℂ) ^ 2 = ((s : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [Work.Asymptotics.layerLow, Work.Asymptotics.sinSq, hsq]

lemma layerTrunc_neg (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (ℓ : Work.Kernels.LogLambdaData)
    (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    Work.Asymptotics.layerTrunc G ℓ d τ (-s) = Work.Asymptotics.layerTrunc G ℓ d τ s := by
  have hsq : (((-s : ℝ)) : ℂ) ^ 2 = ((s : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [Work.Asymptotics.layerTrunc, Work.Asymptotics.sinSq, hsq]

lemma highPart_neg (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (s : ℝ) :
    Work.Asymptotics.highPart G τ (-s) = Work.Asymptotics.highPart G τ s := by
  simp only [Work.Asymptotics.highPart, neg_sq]

lemma paperLayer_neg (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (ℓ : Work.Kernels.LogLambdaData)
    (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    Work.Asymptotics.paperLayer G ℓ d τ (-s) = Work.Asymptotics.paperLayer G ℓ d τ s := by
  simp only [Work.Asymptotics.paperLayer]
  rw [layerLow_neg, layerTrunc_neg, highPart_neg]


/-! ## The scale comparison -/

/-- `scale τ = 1 + (Im τ)⁻¹ + ‖τ‖` is dominated by `3(max ((Im τ)⁻¹) ‖τ‖)`, hence
`(scale τ)^M ≤ 3^M ((Im τ)^{-M} + ‖τ‖^M)` for `M ≥ 0`. -/
lemma scale_rpow_le (τ : UpperHalfPlane) {M : ℝ} (hM : 0 ≤ M) :
    (Work.Kernels.scale τ) ^ M
      ≤ 3 ^ M * ((τ.im) ^ (-M) + ‖(τ : ℂ)‖ ^ M) := by
  set u : ℝ := (τ.im)⁻¹ with hudef
  set v : ℝ := ‖(τ : ℂ)‖ with hvdef
  have hu0 : 0 ≤ u := by rw [hudef]; exact inv_nonneg.mpr τ.im_pos.le
  have hv0 : 0 ≤ v := by rw [hvdef]; exact norm_nonneg _
  have hmax1 : 1 ≤ max u v := by
    by_contra h
    rw [not_le, max_lt_iff] at h
    obtain ⟨h1, h2⟩ := h
    have him : 1 < τ.im := by
      rcases (inv_lt_one_iff₀.mp (by rw [← hudef]; exact h1)) with h3 | h3
      · exact absurd h3 (not_le.mpr τ.im_pos)
      · exact h3
    have hle : τ.im ≤ v := by rw [hvdef]; exact Work.Kernels.im_le_coe_norm τ
    linarith
  have hsc : Work.Kernels.scale τ ≤ 3 * max u v := by
    rw [Work.Kernels.scale, ← hudef, ← hvdef]
    linarith [le_max_left u v, le_max_right u v]
  have hstep1 : Work.Kernels.scale τ ^ M ≤ (3 * max u v) ^ M :=
    Real.rpow_le_rpow (Work.Kernels.scale_pos τ).le hsc hM
  have hstep2 : (3 * max u v) ^ M = 3 ^ M * (max u v) ^ M :=
    Real.mul_rpow (by norm_num) (le_trans hu0 (le_max_left u v))
  have hstep3 : (max u v) ^ M = max (u ^ M) (v ^ M) := Real.rpow_max hu0 hv0 hM
  have hstep4 : max (u ^ M) (v ^ M) ≤ u ^ M + v ^ M :=
    max_le (le_add_of_nonneg_right (Real.rpow_nonneg hv0 M))
      (le_add_of_nonneg_left (Real.rpow_nonneg hu0 M))
  have huM : u ^ M = (τ.im) ^ (-M) := by
    rw [hudef, Real.inv_rpow τ.im_pos.le, Real.rpow_neg τ.im_pos.le]
  have hvM : v ^ M = ‖(τ : ℂ)‖ ^ M := by rw [hvdef]
  calc Work.Kernels.scale τ ^ M ≤ (3 * max u v) ^ M := hstep1
    _ = 3 ^ M * (max u v) ^ M := hstep2
    _ = 3 ^ M * max (u ^ M) (v ^ M) := by rw [hstep3]
    _ ≤ 3 ^ M * (u ^ M + v ^ M) :=
        mul_le_mul_of_nonneg_left hstep4 (Real.rpow_nonneg (by norm_num) M)
    _ = 3 ^ M * ((τ.im) ^ (-M) + ‖(τ : ℂ)‖ ^ M) := by rw [huM, hvM]

/-! ## The assembly from the three pieces -/

/-- The `scale`-form seminorm bound for the three pieces of `paperLayer` (together with their
`C^ω`-smoothness in `r`) implies the target form of the `r`-seminorm bound on the funnel. -/
theorem funnelLayer_of_pieces (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hLow : ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧
      (∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        ContDiff ℝ ω (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s)) ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r‖
          ≤ c * (Work.Kernels.scale τ) ^ N)
    (hTrunc : ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧
      (∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        ContDiff ℝ ω (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)) ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        (|r| ^ k) * ‖iteratedDeriv l
            (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
          ≤ c * (Work.Kernels.scale τ) ^ N) :
    ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        (|r| ^ k) * ‖iteratedDeriv l
            (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
          ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ := by
  intro k l
  obtain ⟨cL, NL, hcL, hLcd, hLb⟩ := hLow k l
  obtain ⟨cT, NT, hcT, hTcd, hTb⟩ := hTrunc k l
  obtain ⟨cH, NH, hcH, hHb⟩ :=
    highPart_seminorm (Work.Asymptotics.Gcusp ℓ d) (fun i j => GcuspInP ℓ d i j) k l
  set N : ℝ := max (max (max NL NT) NH) 0 with hNdef
  have hN0 : 0 ≤ N := le_max_right _ _
  have hNL : NL ≤ N := le_trans (le_trans (le_max_left NL NT) (le_max_left (max NL NT) NH))
    (le_max_left _ _)
  have hNT : NT ≤ N := le_trans (le_trans (le_max_right NL NT) (le_max_left (max NL NT) NH))
    (le_max_left _ _)
  have hNH : NH ≤ N := le_trans (le_max_right (max NL NT) NH) (le_max_left _ _)
  set c : ℝ := cL + cT + cH with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; linarith
  refine ⟨c * 3 ^ N, N, c * 3 ^ N, N, by positivity, hN0, by positivity, hN0, ?_⟩
  intro τ r hτ hτ2
  have hτpos : (0 : ℝ) < τ.im := lt_of_lt_of_le (by norm_num) hτ2
  have hscale1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  -- the bound for `paperLayer`
  have hpaper : (|r| ^ k) * ‖iteratedDeriv l
        (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
      ≤ c * (Work.Kernels.scale τ) ^ N := by
    have hcdL := hLcd τ hτ hτ2
    have hcdT := hTcd τ hτ hτ2
    have hcdH := contDiff_omega_highPart (Work.Asymptotics.Gcusp ℓ d) τ
    have hsplit : iteratedDeriv l
          (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r
        = iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r
          + iteratedDeriv l
              (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ s) r := by
      have hfun : (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)
          = fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s
              + Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s
              + Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ s := by
        funext s; rw [Work.Asymptotics.paperLayer]
      have hE : (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s
              + Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s
              + Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ s)
          = (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s
              + Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)
            + (fun s : ℝ => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ s) := rfl
      rw [hfun, hE, iteratedDeriv_add
        (f := fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s
          + Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)
        (g := fun s : ℝ => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ s)
        (((hcdL.add hcdT).contDiffAt).of_le le_top) ((hcdH.contDiffAt).of_le le_top)]
      rw [show (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s
            + Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)
          = (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s)
            + (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) from rfl,
        iteratedDeriv_add (f := fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s)
          (g := fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)
          ((hcdL.contDiffAt).of_le le_top) ((hcdT.contDiffAt).of_le le_top)]
    rw [hsplit]
    have hL' : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r‖
        ≤ cL * (Work.Kernels.scale τ) ^ N := by
      refine le_trans (hLb τ r hτ hτ2) ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hscale1 hNL) hcL
    have hT' : (|r| ^ k) * ‖iteratedDeriv l
          (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
        ≤ cT * (Work.Kernels.scale τ) ^ N := by
      refine le_trans (hTb τ r hτ hτ2) ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hscale1 hNT) hcT
    have hH' : (|r| ^ k) * ‖iteratedDeriv l
          (fun s : ℝ => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ s) r‖
        ≤ cH * (Work.Kernels.scale τ) ^ N := by
      refine le_trans (hHb τ r hτ) ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hscale1 hNH) hcH
    have htri : ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r
            + iteratedDeriv l
                (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r
            + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ s) r‖
        ≤ ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r‖
            + ‖iteratedDeriv l
                (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
            + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ s) r‖ := by
      have h1 := norm_add_le
        (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r
          + iteratedDeriv l
              (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r)
        (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ s) r)
      have h2 := norm_add_le (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r)
        (iteratedDeriv l
          (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r)
      linarith
    calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r
            + iteratedDeriv l
                (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r
            + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ s) r‖
        ≤ (|r| ^ k) * (‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r‖
            + ‖iteratedDeriv l
                (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
            + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ s) r‖) :=
          mul_le_mul_of_nonneg_left htri (by positivity)
      _ = (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r‖
            + (|r| ^ k) * ‖iteratedDeriv l
                (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
            + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ s) r‖ := by ring
      _ ≤ cL * (Work.Kernels.scale τ) ^ N + cT * (Work.Kernels.scale τ) ^ N
            + cH * (Work.Kernels.scale τ) ^ N := add_le_add (add_le_add hL' hT') hH'
      _ = c * (Work.Kernels.scale τ) ^ N := by rw [hcdef]; ring
  -- the bound for `layer`
  have hlayer : (|r| ^ k) * ‖iteratedDeriv l
        (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
      ≤ c * (Work.Kernels.scale τ) ^ N := by
    rcases eq_or_ne r 0 with hr | hr
    · subst hr
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        rcases Nat.eq_zero_or_pos l with hl | hl
        · subst hl
          have hz : Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ 0 = 0 := by
            rw [Work.Asymptotics.layer]; simp
          simp only [iteratedDeriv_zero, hz, norm_zero, mul_zero]
          exact mul_nonneg hc0 (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le N)
        · have hcdL := hLcd τ hτ hτ2
          have hcdT := hTcd τ hτ hτ2
          have hcdH := contDiff_omega_highPart (Work.Asymptotics.Gcusp ℓ d) τ
          have hcdP : ContDiff ℝ ω
              (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) := by
            have hfun : (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)
                = fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s
                    + Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s
                    + Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ s := by
              funext s; rw [Work.Asymptotics.paperLayer]
            rw [hfun]
            exact (hcdL.add hcdT).add hcdH
          have hfun2 : (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)
              = fun s : ℝ => (if s = 0 then 0
                  else Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) := by
            funext s; rw [Work.Asymptotics.layer]
          rw [hfun2, punctured_iteratedDeriv (paperLayer_neg (Work.Asymptotics.Gcusp ℓ d) ℓ d τ)
            (hcdP.differentiable (by simp)) l hl]
          exact hpaper
      · have hz : (0 : ℝ) ^ k = 0 := zero_pow hk.ne'
        simp only [abs_zero, hz, zero_mul]
        exact mul_nonneg hc0 (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le N)
    · have heq : (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)
          =ᶠ[𝓝 r] (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) := by
        filter_upwards [isOpen_ne.mem_nhds hr] with s hs
        rw [Work.Asymptotics.layer, if_neg hs]
      rw [iteratedDeriv_congr_of_eventuallyEq heq l]
      exact hpaper
  -- convert to the requested form
  have hsc := scale_rpow_le τ hN0
  have hcN : 0 ≤ c * 3 ^ N := by positivity
  calc (|r| ^ k) * ‖iteratedDeriv l
        (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
      ≤ c * (Work.Kernels.scale τ) ^ N := hlayer
    _ ≤ c * (3 ^ N * ((τ.im) ^ (-N) + ‖(τ : ℂ)‖ ^ N)) :=
        mul_le_mul_of_nonneg_left hsc hc0
    _ = c * 3 ^ N * (τ.im) ^ (-N) + c * 3 ^ N * ‖(τ : ℂ)‖ ^ N := by ring

/-! ## The inputs on the funnel -/

/-- **The `low` piece of the layer on the funnel**, from the flatness hypothesis `hflat`
(the sibling `funnelFlat`); proved in `Work.Asymptotics.HalfFunnel.layerLowFree` (kept in the
`MiddleRange` world, which the funnel estimates belong to). -/
theorem funnelLayerLow_input (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hflat : ∃ C c m : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ m ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        t ≤ 1 → Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
          ≤ C * (1 + 1 / t) ^ m * Real.exp (-(c / t))) :
    ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧
      (∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        ContDiff ℝ ω (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s)) ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r‖
          ≤ c * (Work.Kernels.scale τ) ^ N :=
  funnelLayerLowF ℓ d hd hflat

/-- **The `trunc` piece of the layer on the funnel**, from the below-the-pole kernel bound
(`Work.Asymptotics.HalfFunnel.funnelKernelWindow`) and the exponential smallness of the `i = 1`
row of the cusp coefficients (`Work.Asymptotics.HalfFunnel.GcuspRow11Small`). -/
theorem funnelLayerTrunc_input (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧
      (∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        ContDiff ℝ ω
          (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)) ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        (|r| ^ k) * ‖iteratedDeriv l
            (fun s : ℝ => Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
          ≤ c * (Work.Kernels.scale τ) ^ N :=
  Work.Asymptotics.HalfFunnel.funnelLayerTrunc ℓ d hd
    (Work.Asymptotics.HalfFunnel.funnelKernelWindow ℓ d hd)
    (Work.Asymptotics.HalfFunnel.GcuspRow11Small ℓ d hd)

theorem funnelLayer (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (hflat : ∃ C c m : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ m ∧ ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → t ≤ 1 → Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) → ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C * (1 + 1 / t) ^ m * Real.exp (-(c / t))) : ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖ ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ :=
  funnelLayer_of_pieces ℓ d hd (funnelLayerLow_input ℓ d hd hflat) (funnelLayerTrunc_input ℓ d hd)

end

end Work.Asymptotics.HalfFunnel
