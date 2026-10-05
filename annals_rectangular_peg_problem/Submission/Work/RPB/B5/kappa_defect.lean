import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B2.chordSurf_lagrangian
import Submission.Work.RPV.levelPt_omega
import Submission.Work.RPB.B5.chartJets_chartLev_slice
import Submission.Work.RPB.B5.chartJets_oneSided
import Submission.Work.RPB.B5.chart_rho_lagrangian_kappa
import Submission.Work.RPB.B5.uproj_chart_contDiffAt_kappa
import Submission.Work.RPB.B5.noL_defect_jets_ha
import Submission.Work.RPB.B5.rho_range_kappa

/-!
# `Work.RPB.B5.kappa_defect`

Let `W` be the `ρ = r²`-chart of the chord annulus of a curve isotopy `CI` with chord phase `a`
(`W τ t (r ^ 2) = chordSurf CI.c a τ t r` for `0 < r ≤ π/2`, of class `C¹²` on
`[0,1] × ℝ × (-ρ₀, ρ₀)`), and let `ρh` be a level inversion of its level function on the level
interval `(-κ, κ)`:
`K₀ (W τ t (ρh τ t σ)) + 1 = -σ`, `ρh τ t σ ∈ (-ρ₀, ρ₀)`, `ρh τ t 0 = 0`.

The theorem produces a single `δ ∈ (0, κ]` such that, writing
`U τ t σ = uproj (W τ t (ρh τ t σ))` and `Q τ t σ = (W τ t (ρh τ t σ)).1.2`,

* the *flux defect* `ω_ℂ(∂_σ U, ∂_t U) - ∂_t Q` vanishes for `σ ∈ (-δ, 0)`, i.e. the surface
  `(σ, t) ↦ W τ t (ρh τ t σ)` is Lagrangian there; and
* the defect function is *flat to order 8* at `σ = 0`.

## The argument

Three independent facts are combined.

1. **Range of `ρh`** (`Work.RPB.B5.rho_range_kappa`, proved by a colleague): there is `ε ∈ (0, κ]`
   with `ρh τ t σ ∈ (0, π²/4)` for every `τ ∈ [0,1]`, every real `t` and every `σ ∈ (-ε, 0)`.
   On this range the chart value is the chord value at parameter `r = √(ρh τ t σ) < π/2`, hence
   the surface is a reparametrisation of the chord annulus.

2. **Lagrangian property** (`Work.RPB.B5.chart_rho_lagrangian_kappa`): for such `σ`,
   `symp (∂_σ (W τ t (ρh τ t ·))) (∂_t (W τ · (ρh τ · σ))) = 0`.  Since
   `levelPt (uproj x) σ (x.1.2) = x` for `K₀ x + 1 = -σ`, the level-curve identity
   `Work.RPV.levelPt_omega` turns this into the defect identity.  This is
   `Work.RPB.B5.defect_identity_kappa` below.

3. **Flatness of the jets** (`Work.RPB.B5.chartJets_oneSided`): the defect function is `C⁸` at
   `σ = 0` and vanishes on the one-sided neighbourhood `(-δ, 0)`, so all its iterated derivatives
   of order at most `8` at `0` vanish.  This is `Work.RPB.B5.defect_jets_kappa` below.
-/

open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## The pointwise defect identity -/

/-- **The flux defect vanishes on the negative side.**  Given the range bound
`ρh τ t σ ∈ (0, π²/4)` for `σ ∈ (-δ, 0)` (so that `W τ t (ρh τ t σ)` is a chord value at a
parameter in `(0, π/2)`, where the chord annulus is Lagrangian), the identity
`ω_ℂ(∂_σ U, ∂_t U) = ∂_t Q` holds for every `σ ∈ (-δ, 0)`.

This is `Work.RPB.B5.noL_defect_jets_ha`'s first conjunct, with the fixed radius `1` of `ρh`
replaced by the general `κ`. -/
theorem defect_identity_kappa (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    {κ : ℝ} (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    {δ : ℝ} (hδ : 0 < δ) (hδκ : δ ≤ κ)
    (hreg : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-δ) 0,
      ρh τ t σ ∈ Set.Ioo (0 : ℝ) (Real.pi ^ 2 / 4)) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ ∈ Set.Ioo (-δ) 0, ∀ t : ℝ,
      Work.RPV.ωC (deriv (fun s : ℝ => Work.RPV.uproj (W τ t (ρh τ t s))) σ)
          (deriv (fun s : ℝ => Work.RPV.uproj (W τ s (ρh τ s σ))) t)
        = deriv (fun s : ℝ => (W τ s (ρh τ s σ)).1.2) t := by
  have hlag := chart_rho_lagrangian_kappa CI a ha hρ₀ hW hWchord hκ hρh hρhv hδ hδκ hreg
  intro τ hτ σ hσ t
  have hσκ : σ ∈ Set.Ioo (-κ) κ :=
    ⟨by linarith [hσ.1, hδκ], by linarith [hσ.2, hκ]⟩
  obtain ⟨hΨcd, hΞcd⟩ := uproj_chart_contDiffAt_kappa (t := t) hW hκ hρh hρhv hτ hσκ
  -- slices with the `t`-coordinate fixed
  have hΓcd : ContDiffAt ℝ 12 (fun s : ℝ => Work.RPV.uproj (W τ t (ρh τ t s))) σ := by
    have hsec : ContDiffAt ℝ 12 (fun s : ℝ => (s, t)) σ := by fun_prop
    simpa only [Function.comp_def] using hΨcd.comp σ hsec
  have hAcd : ContDiffAt ℝ 12 (fun s : ℝ => (W τ t (ρh τ t s)).1.2) σ := by
    have hsec : ContDiffAt ℝ 12 (fun s : ℝ => (s, t)) σ := by fun_prop
    simpa only [Function.comp_def] using hΞcd.comp σ hsec
  -- slices with the `σ`-coordinate fixed
  have hΓt_cd : ContDiffAt ℝ 12 (fun s : ℝ => Work.RPV.uproj (W τ s (ρh τ s σ))) t := by
    have hsec : ContDiffAt ℝ 12 (fun s : ℝ => (σ, s)) t := by fun_prop
    simpa only [Function.comp_def] using hΨcd.comp t hsec
  have hAt_cd : ContDiffAt ℝ 12 (fun s : ℝ => (W τ s (ρh τ s σ)).1.2) t := by
    have hsec : ContDiffAt ℝ 12 (fun s : ℝ => (σ, s)) t := by fun_prop
    simpa only [Function.comp_def] using hΞcd.comp t hsec
  have hΓσ : HasDerivAt (fun s : ℝ => Work.RPV.uproj (W τ t (ρh τ t s)))
      (deriv (fun s : ℝ => Work.RPV.uproj (W τ t (ρh τ t s))) σ) σ :=
    (hΓcd.differentiableAt (by norm_num)).hasDerivAt
  have hΓt : HasDerivAt (fun s : ℝ => Work.RPV.uproj (W τ s (ρh τ s σ)))
      (deriv (fun s : ℝ => Work.RPV.uproj (W τ s (ρh τ s σ))) t) t :=
    (hΓt_cd.differentiableAt (by norm_num)).hasDerivAt
  have hAσ : HasDerivAt (fun s : ℝ => (W τ t (ρh τ t s)).1.2)
      (deriv (fun s : ℝ => (W τ t (ρh τ t s)).1.2) σ) σ :=
    (hAcd.differentiableAt (by norm_num)).hasDerivAt
  have hAt : HasDerivAt (fun s : ℝ => (W τ s (ρh τ s σ)).1.2)
      (deriv (fun s : ℝ => (W τ s (ρh τ s σ)).1.2) t) t :=
    (hAt_cd.differentiableAt (by norm_num)).hasDerivAt
  -- the level parametrisation supplies the symplectic pairing
  have homega := Work.RPV.levelPt_omega
    (fun σ t => Work.RPV.uproj (W τ t (ρh τ t σ)))
    (fun σ t => (W τ t (ρh τ t σ)).1.2) σ t
    (deriv (fun s : ℝ => Work.RPV.uproj (W τ t (ρh τ t s))) σ)
    (deriv (fun s : ℝ => Work.RPV.uproj (W τ s (ρh τ s σ))) t)
    (deriv (fun s : ℝ => (W τ t (ρh τ t s)).1.2) σ)
    (deriv (fun s : ℝ => (W τ s (ρh τ s σ)).1.2) t)
    hΓσ hΓt hAσ hAt
  -- rewrite the `levelPt`-parametrisation back to the chart `W ∘ ρh`
  have hpt1 : ∀ s ∈ Set.Ioo (-κ) κ,
      Work.RPV.levelPt (Work.RPV.uproj (W τ t (ρh τ t s))) s ((W τ t (ρh τ t s)).1.2)
        = W τ t (ρh τ t s) := fun s hs => levelPt_uproj_eq_self _ s (hρhl τ hτ t s hs)
  have hderiv1 : deriv (fun s => Work.RPV.levelPt (Work.RPV.uproj (W τ t (ρh τ t s))) s
        ((W τ t (ρh τ t s)).1.2)) σ = deriv (fun s => W τ t (ρh τ t s)) σ := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hσκ] with s hs
    exact hpt1 s hs
  have hderiv2 : deriv (fun s => Work.RPV.levelPt (Work.RPV.uproj (W τ s (ρh τ s σ))) σ
        ((W τ s (ρh τ s σ)).1.2)) t = deriv (fun s => W τ s (ρh τ s σ)) t := by
    congr 1
    funext s
    exact levelPt_uproj_eq_self _ σ (hρhl τ hτ s σ hσκ)
  rw [hderiv1, hderiv2, hlag τ hτ σ hσ t] at homega
  linarith [homega]

/-! ## Flatness of the defect jets at `σ = 0` -/

/-- **The defect function is flat to order `8` at `σ = 0`.**  The defect
`ω_ℂ(∂_σ U, ∂_t U) - ∂_t Q` is `C⁸` at `σ = 0` and vanishes on the one-sided neighbourhood
`(-δ, 0)` by `Work.RPB.B5.defect_identity_kappa`, so all its iterated derivatives of order at most
`8` at `0` vanish (`Work.RPB.B5.chartJets_oneSided`). -/
theorem defect_jets_kappa (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {W : ℝ → ℝ → ℝ → Work.RPV.PS} {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    {κ : ℝ} (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    {δ : ℝ} (hδ : 0 < δ) (hδκ : δ ≤ κ)
    (hreg : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-δ) 0,
      ρh τ t σ ∈ Set.Ioo (0 : ℝ) (Real.pi ^ 2 / 4)) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ j : ℕ, j ≤ 8 →
      iteratedDeriv j (fun σ : ℝ =>
        Work.RPV.ωC (deriv (fun s : ℝ => Work.RPV.uproj (W τ t (ρh τ t s))) σ)
            (deriv (fun s : ℝ => Work.RPV.uproj (W τ s (ρh τ s σ))) t)
          - deriv (fun s : ℝ => (W τ s (ρh τ s σ)).1.2) t) 0 = 0 := by
  have hfirst := defect_identity_kappa CI a ha hρ₀ hW hWchord hκ hρh hρhv hρhl hδ hδκ hreg
  intro τ hτ t j hj
  have hσ0 : (0 : ℝ) ∈ Set.Ioo (-κ) κ := ⟨by linarith, hκ⟩
  obtain ⟨hΨcd, hΞcd⟩ := uproj_chart_contDiffAt_kappa (t := t) hW hκ hρh hρhv hτ hσ0
  have hX1 : ContDiffAt ℝ 11
      (fun σ : ℝ => deriv (fun s => Work.RPV.uproj (W τ s (ρh τ s σ))) t) 0 := by
    simpa only [Nat.cast_ofNat] using
      (contDiffAt_deriv_slices (fun p : ℝ × ℝ => Work.RPV.uproj (W τ p.2 (ρh τ p.2 p.1)))
        (n := 11) hΨcd).1
  have hX2 : ContDiffAt ℝ 11
      (fun σ : ℝ => deriv (fun s => Work.RPV.uproj (W τ t (ρh τ t s))) σ) 0 := by
    simpa only [Nat.cast_ofNat] using
      (contDiffAt_deriv_slices (fun p : ℝ × ℝ => Work.RPV.uproj (W τ p.2 (ρh τ p.2 p.1)))
        (n := 11) hΨcd).2
  have hR : ContDiffAt ℝ 11
      (fun σ : ℝ => deriv (fun s => (W τ s (ρh τ s σ)).1.2) t) 0 := by
    simpa only [Nat.cast_ofNat] using
      (contDiffAt_deriv_slices (fun p : ℝ × ℝ => (W τ p.2 (ρh τ p.2 p.1)).1.2)
        (n := 11) hΞcd).1
  have hw : ContDiffAt ℝ 11
      (fun σ : ℝ => Work.RPV.ωC (deriv (fun s => Work.RPV.uproj (W τ t (ρh τ t s))) σ)
        (deriv (fun s => Work.RPV.uproj (W τ s (ρh τ s σ))) t)) 0 := by
    simpa only [Nat.cast_ofNat] using contDiffAt_omegaC hX2 hX1
  have hFcd : ContDiffAt ℝ 11 (fun σ : ℝ =>
      Work.RPV.ωC (deriv (fun s => Work.RPV.uproj (W τ t (ρh τ t s))) σ)
          (deriv (fun s => Work.RPV.uproj (W τ s (ρh τ s σ))) t)
        - deriv (fun s => (W τ s (ρh τ s σ)).1.2) t) 0 := by
    simpa only [Nat.cast_ofNat] using hw.sub hR
  have hF8 : ContDiffAt ℝ 8 (fun σ : ℝ =>
      Work.RPV.ωC (deriv (fun s => Work.RPV.uproj (W τ t (ρh τ t s))) σ)
          (deriv (fun s => Work.RPV.uproj (W τ s (ρh τ s σ))) t)
        - deriv (fun s => (W τ s (ρh τ s σ)).1.2) t) 0 :=
    hFcd.of_le (by norm_num)
  have hzero : ∀ x ∈ Set.Ioo ((0 : ℝ) - δ) 0,
      (fun σ : ℝ =>
        Work.RPV.ωC (deriv (fun s => Work.RPV.uproj (W τ t (ρh τ t s))) σ)
            (deriv (fun s => Work.RPV.uproj (W τ s (ρh τ s σ))) t)
          - deriv (fun s => (W τ s (ρh τ s σ)).1.2) t) x = (fun _ : ℝ => (0 : ℝ)) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (-δ) 0 := by simpa using hx
    have h1 := hfirst τ hτ x hx' t
    change Work.RPV.ωC (deriv (fun s => Work.RPV.uproj (W τ t (ρh τ t s))) x)
        (deriv (fun s => Work.RPV.uproj (W τ s (ρh τ s x))) t)
      - deriv (fun s => (W τ s (ρh τ s x)).1.2) t = 0
    rw [h1, sub_self]
  have hjet := chartJets_oneSided (E := ℝ) (n := 8) hδ hF8 contDiffAt_const hzero hj
  rw [hjet, iteratedDeriv_const]
  split <;> rfl

/-! ## The requested theorem -/

theorem kappa_defect (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (κ : ℝ) (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ κ ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ ∈ Set.Ioo (-δ) 0, ∀ t : ℝ,
        Work.RPV.ωC (deriv (fun s : ℝ => Work.RPV.uproj (W τ t (ρh τ t s))) σ)
            (deriv (fun s : ℝ => Work.RPV.uproj (W τ s (ρh τ s σ))) t)
          = deriv (fun s : ℝ => (W τ s (ρh τ s σ)).1.2) t) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ j : ℕ, j ≤ 8 →
        iteratedDeriv j (fun σ : ℝ =>
          Work.RPV.ωC (deriv (fun s : ℝ => Work.RPV.uproj (W τ t (ρh τ t s))) σ)
              (deriv (fun s : ℝ => Work.RPV.uproj (W τ s (ρh τ s σ))) t)
            - deriv (fun s : ℝ => (W τ s (ρh τ s σ)).1.2) t) 0 = 0) := by
  obtain ⟨ε, hεpos, hεκ, hreg⟩ :=
    rho_range_kappa CI a ha ρ₀ hρ₀ W ρh hκ hW hWchord hρh hρh0 hρhv hρhl
  exact ⟨ε, hεpos, hεκ,
    defect_identity_kappa CI a ha hρ₀ hW hWchord hκ hρh hρhv hρhl hεpos hεκ hreg,
    defect_jets_kappa CI a ha hρ₀ hW hWchord hκ hρh hρhv hρhl hεpos hεκ hreg⟩

end Work.RPB.B5
