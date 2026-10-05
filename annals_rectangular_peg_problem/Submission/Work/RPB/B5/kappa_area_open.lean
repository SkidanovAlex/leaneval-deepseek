import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B2.chordSurf_lagrangian
import Submission.Work.RPB.B5.chordLoop_area
import Submission.Work.RPB.B5.signedArea_parallelogram
import Submission.Work.RPB.B5.signedArea_comp_reparam
import Submission.Work.RPB.B5.area_normalised
import Submission.Work.RPB.B5.K0_chordSurf_level
import Submission.Work.RPV.VBasic

/-!
# B5: the area law on the chord side, on the open interval `(-δ, 0)`, `κ`-parametrised

This is the `κ`-parametrised version of the chord-side area law of `Work.RPB.B5.noL_near_area`
(the `(-1,1)` case).  The level inversion `ρh` is only available on an interval `(-κ, κ)`: the
level function `ρ ↦ K₀ (W τ t ρ) + 1 = ρ ‖halfChord‖²` of the chord chart need not be monotone on
the pinned region `(0, π²/4]`, so the inverse cannot in general be extended to a fixed interval
such as `(-1, 1)`.  Every consumer of `ρh` is therefore stated with a parameter `κ > 0`, and the
regular side is the interval `(-δ, 0)` with `0 < δ ≤ κ`.

The statement: given the `ρ = r²`-chart `W` of the chord annulus
(`W τ t (r ^ 2) = chordSurf CI.c a τ t r` for `0 < r ≤ π/2`), a level inversion `ρh`
(`K₀ (W τ t (ρh τ t σ)) + 1 = -σ` for `σ ∈ (-κ, κ)`, `ρh` `C⁸`, `2π`-periodic in `t`) which on the
regular interval `(-δ, 0)` takes values in `(0, π²/4)`, the level curve
`t ↦ uproj (W τ t (ρh τ t σ))` has signed area exactly `2π (1 + σ)`:

`signedArea (t ↦ uproj (W τ t (ρh τ t σ))) = 2π (1 + σ)`  for every `τ ∈ [0,1]`, `σ ∈ (-δ, 0)`.

## Proof

With `r = √(ρh τ t σ) ∈ (0, π/2)` the chord hypothesis `hchord` and `uproj_chordPS` give

`uproj (W τ t (ρh τ t σ)) = (c (t+r) + c (t-r)) / √2`

and the level condition (`hρhl` + `K0_chordPS`) gives `‖c (t+r) - c (t-r)‖² = -4σ`.

So the level curve is `N_σ = (P₊ + P₋)/√2`, where `P± = c (· ± r(·))` are `2π`-periodic
reparametrisations of the curve `c τ` (the reparametrisation parameter `t ± r t` is `C¹` with
`u (t + 2π) = u t + 2π` because `ρh` is `2π`-periodic in `t`), and `Δ = P₊ - P₋` is the chord loop
of constant length `2√(-σ)`, whose signed area is `-4πσ` (`chordLoop_area`, via the chord phase
monodromy).  The polarization (parallelogram) identity for the quadratic form `signedArea` gives

`signedArea (P₊ + P₋) + signedArea Δ = 2 signedArea P₊ + 2 signedArea P₋`,

so `signedArea (P₊ + P₋) = 4π + 4πσ`, and the real scaling law (`signedArea_const_mul`) with
`(√2)⁻¹` turns this into `signedArea N_σ = 2π (1 + σ)`.
-/

open scoped ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.RPB.B5

/-! ## The level curve of the `ρ`-chart -/

/-- `√(ρh τ t σ) ∈ (0, π/2]` whenever `ρh τ t σ ∈ (0, π²/4)`. -/
private lemma sqrt_rho_mem {ρh : ℝ → ℝ → ℝ → ℝ} {τ t σ : ℝ}
    (h : ρh τ t σ ∈ Set.Ioo (0 : ℝ) (Real.pi ^ 2 / 4)) :
    Real.sqrt (ρh τ t σ) ∈ Set.Ioc (0 : ℝ) (Real.pi / 2) := by
  refine ⟨Real.sqrt_pos.mpr h.1, ?_⟩
  have h2 : Real.sqrt (ρh τ t σ) < Real.pi / 2 :=
    (Real.sqrt_lt' (by positivity : (0 : ℝ) < Real.pi / 2)).mpr (by
      rw [show (Real.pi / 2) ^ 2 = Real.pi ^ 2 / 4 by ring]
      exact h.2)
  exact h2.le

/-- Slice smoothness of the level inversion in `t`, on the `κ`-interval. -/
private lemma rho_slice_contDiff {ρh : ℝ → ℝ → ℝ → ℝ} {κ : ℝ}
    (hρh : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ)) :
    ∀ τ' ∈ Set.Icc (0 : ℝ) 1, ∀ σ' ∈ Set.Ioo (-κ : ℝ) κ,
      ContDiff ℝ 8 (fun t : ℝ => ρh τ' t σ') := by
  intro τ' hτ' σ' hσ'
  have hmaps : Set.MapsTo (fun t : ℝ => ((τ' : ℝ), (t, σ'))) Set.univ
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ) := fun t _ => ⟨hτ', trivial, hσ'⟩
  have hcomp := hρh.comp
    ((by fun_prop : ContDiff ℝ 8 (fun t : ℝ => ((τ' : ℝ), (t, σ')))).contDiffOn) hmaps
  rwa [contDiffOn_univ] at hcomp

/-- Slice smoothness of `t ↦ √(ρh τ' t σ')` on the regular side `(-δ, 0)`.  The only use of
`δ ≤ κ` is that `(-δ, 0) ⊆ (-κ, κ)`, so that the slice smoothness of `ρh` is available. -/
private lemma rho_sqrt_slice_contDiff {ρh : ℝ → ℝ → ℝ → ℝ} {κ δ : ℝ}
    (hρh : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hκ : 0 < κ) (hδκ : δ ≤ κ)
    (hreg : ∀ τ' ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ' ∈ Set.Ioo (-δ) 0,
        ρh τ' t σ' ∈ Set.Ioo (0 : ℝ) (Real.pi ^ 2 / 4)) :
    ∀ τ' ∈ Set.Icc (0 : ℝ) 1, ∀ σ' ∈ Set.Ioo (-δ) 0,
      ContDiff ℝ 2 (fun t : ℝ => Real.sqrt (ρh τ' t σ')) := by
  intro τ' hτ' σ' hσ'
  have hσκ : σ' ∈ Set.Ioo (-κ : ℝ) κ :=
    ⟨by linarith [hδκ, hσ'.1], by linarith [hσ'.2]⟩
  rw [contDiff_iff_contDiffAt]
  intro t
  exact (Real.contDiffAt_sqrt (ne_of_gt (hreg τ' hτ' t σ' hσ').1)).comp t
    ((rho_slice_contDiff hρh τ' hτ' σ' hσκ).contDiffAt.of_le (by norm_num))

/-- The level curve of the chord chart in the `ρ = r²` variable is the midpoint (scaled by `√2`)
of the chord of half-length `√(ρh τ t σ)`. -/
private lemma uproj_W_level (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (W : ℝ → ℝ → ℝ → Work.RPV.PS) {ρh : ℝ → ℝ → ℝ → ℝ}
    (hchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    {τ t σ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (h : ρh τ t σ ∈ Set.Ioo (0 : ℝ) (Real.pi ^ 2 / 4)) :
    Work.RPV.uproj (W τ t (ρh τ t σ))
      = (CI.c τ (t + Real.sqrt (ρh τ t σ)) + CI.c τ (t - Real.sqrt (ρh τ t σ)))
          / (Real.sqrt 2 : ℂ) := by
  have hr := sqrt_rho_mem h
  have hsq : (Real.sqrt (ρh τ t σ)) ^ 2 = ρh τ t σ := Real.sq_sqrt h.1.le
  have hW : W τ t (ρh τ t σ) = Work.RPB.chordSurf CI.c a τ t (Real.sqrt (ρh τ t σ)) :=
    (congrArg (fun ρ => W τ t ρ) hsq.symm).trans (hchord τ hτ t _ hr)
  rw [hW, Work.RPB.chordSurf, Work.RPV.uproj_chordPS]

/-- The level condition: on the level `σ` the chord has squared length `-4σ`. -/
private lemma level_cond (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (W : ℝ → ℝ → ℝ → Work.RPV.PS) {ρh : ℝ → ℝ → ℝ → ℝ} {κ : ℝ}
    (hchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
        Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    {τ t σ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hσ : σ ∈ Set.Ioo (-κ : ℝ) κ)
    (h : ρh τ t σ ∈ Set.Ioo (0 : ℝ) (Real.pi ^ 2 / 4)) :
    ‖CI.c τ (t + Real.sqrt (ρh τ t σ)) - CI.c τ (t - Real.sqrt (ρh τ t σ))‖ ^ 2
      = -4 * σ := by
  have hr := sqrt_rho_mem h
  have hsq : (Real.sqrt (ρh τ t σ)) ^ 2 = ρh τ t σ := Real.sq_sqrt h.1.le
  have hW : W τ t (ρh τ t σ) = Work.RPB.chordSurf CI.c a τ t (Real.sqrt (ρh τ t σ)) :=
    (congrArg (fun ρ => W τ t ρ) hsq.symm).trans (hchord τ hτ t _ hr)
  have h1 := hρhl τ hτ t σ hσ
  rw [hW, Work.RPB.chordSurf, Work.RPV.K0_chordPS] at h1
  linarith

/-! ## The area law on the open interval -/

theorem kappa_area_open (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (W : ℝ → ℝ → ℝ → Work.RPV.PS) {ρh : ℝ → ℝ → ℝ → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ)
    (hρhp : ∀ τ t σ, ρh τ (t + 2 * Real.pi) σ = ρh τ t σ)
    (hρh : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    {δ : ℝ} (hδ : 0 < δ) (hδκ : δ ≤ κ)
    (hreg : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-δ) 0,
      ρh τ t σ ∈ Set.Ioo (0 : ℝ) (Real.pi ^ 2 / 4)) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ ∈ Set.Ioo (-δ) 0,
      Work.RPB.signedArea (fun t => Work.RPV.uproj (W τ t (ρh τ t σ)))
        = 2 * Real.pi * (1 + σ) := by
  intro τ hτ σ hσ
  have hσκ : σ ∈ Set.Ioo (-κ : ℝ) κ :=
    ⟨by linarith [hδκ, hσ.1], by linarith [hσ.2]⟩
  -- the half chord length as a function of `t`
  set r : ℝ → ℝ := fun t => Real.sqrt (ρh τ t σ) with hrdef
  have hrsm : ContDiff ℝ 2 r := by
    rw [hrdef]
    exact rho_sqrt_slice_contDiff hρh hκ hδκ hreg τ hτ σ hσ
  have hrper : ∀ t, r (t + 2 * Real.pi) = r t := by
    intro t
    simp only [hrdef]
    rw [hρhp τ t σ]
  have hpcd : ContDiff ℝ 1 (fun t : ℝ => CI.c τ (t + r t)) :=
    (CI.smooth.of_le (by norm_num)).comp
      (contDiff_const.prodMk (contDiff_id.add (hrsm.of_le (by norm_num))))
  have hmcd : ContDiff ℝ 1 (fun t : ℝ => CI.c τ (t - r t)) :=
    (CI.smooth.of_le (by norm_num)).comp
      (contDiff_const.prodMk (contDiff_id.sub (hrsm.of_le (by norm_num))))
  -- the reparametrisations preserve the signed area
  have hcr : ContDiff ℝ 1 (fun t : ℝ => CI.c τ t) :=
    (CI.smooth.of_le (by norm_num)).comp
      (by fun_prop : ContDiff ℝ 1 (fun t : ℝ => (τ, t)))
  have hp_area : Work.RPB.signedArea (fun t => CI.c τ (t + r t)) = Real.pi := by
    have hu : ContDiff ℝ 1 (fun t : ℝ => t + r t) :=
      contDiff_id.add (hrsm.of_le (by norm_num))
    have huper : ∀ t : ℝ, (t + 2 * Real.pi) + r (t + 2 * Real.pi) = (t + r t) + 2 * Real.pi :=
      fun t => by rw [hrper t]; ring
    rw [signedArea_comp_reparam (CI.c τ) (fun t : ℝ => t + r t) hcr (fun t => CI.per τ t) hu
      huper]
    simpa only [Work.RPB.signedArea] using CI.area τ hτ
  have hm_area : Work.RPB.signedArea (fun t => CI.c τ (t - r t)) = Real.pi := by
    have hu : ContDiff ℝ 1 (fun t : ℝ => t - r t) :=
      contDiff_id.sub (hrsm.of_le (by norm_num))
    have huper : ∀ t : ℝ, (t + 2 * Real.pi) - r (t + 2 * Real.pi) = (t - r t) + 2 * Real.pi :=
      fun t => by rw [hrper t]; ring
    rw [signedArea_comp_reparam (CI.c τ) (fun t : ℝ => t - r t) hcr (fun t => CI.per τ t) hu
      huper]
    simpa only [Work.RPB.signedArea] using CI.area τ hτ
  -- the difference loop has signed area `-4πσ`
  have hD : Work.RPB.signedArea (fun t => CI.c τ (t + r t) - CI.c τ (t - r t))
      = -4 * Real.pi * σ := by
    have hcall := chordLoop_area CI (fun τ' t' σ' => Real.sqrt (ρh τ' t' σ')) hδ
      (fun τ' hτ' t' σ' hσ' =>
        ⟨Real.sqrt_pos.mpr (hreg τ' hτ' t' σ' hσ').1,
          lt_of_le_of_lt (sqrt_rho_mem (hreg τ' hτ' t' σ' hσ')).2
            (show Real.pi / 2 < Real.pi by linarith [Real.pi_pos])⟩)
      (rho_sqrt_slice_contDiff hρh hκ hδκ hreg)
      (fun τ' t' σ' => by simp only [hρhp τ' t' σ'])
      (fun τ' hτ' t' σ' hσ' =>
        level_cond CI a W hchord hρhl hτ'
          ⟨by linarith [hδκ, hσ'.1], by linarith [hσ'.2]⟩ (hreg τ' hτ' t' σ' hσ'))
      τ hτ σ hσ
    simp only [hrdef]
    exact hcall
  -- the parallelogram identity
  have hpar : Work.RPB.signedArea (fun t => CI.c τ (t + r t) + CI.c τ (t - r t))
      + Work.RPB.signedArea (fun t => CI.c τ (t + r t) - CI.c τ (t - r t))
      = 2 * Work.RPB.signedArea (fun t => CI.c τ (t + r t))
        + 2 * Work.RPB.signedArea (fun t => CI.c τ (t - r t)) := by
    have h := signedArea_parallelogram (fun t => CI.c τ (t + r t)) (fun t => CI.c τ (t - r t))
      hpcd hmcd
    simpa only [] using h
  have hsum : Work.RPB.signedArea (fun t => CI.c τ (t + r t) + CI.c τ (t - r t))
      = 4 * Real.pi + 4 * Real.pi * σ := by
    linarith [hpar, hp_area, hm_area, hD]
  -- the level curve is `(P₊ + P₋)/√2`
  have hpoint : ∀ t : ℝ, Work.RPV.uproj (W τ t (ρh τ t σ))
      = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (CI.c τ (t + r t) + CI.c τ (t - r t)) := by
    intro t
    rw [uproj_W_level CI a W hchord hτ (hreg τ hτ t σ hσ)]
    simp only [hrdef]
    rw [div_eq_mul_inv, mul_comm]
    congr 1
    push_cast <;> rfl
  have hN : Work.RPB.signedArea (fun t => Work.RPV.uproj (W τ t (ρh τ t σ)))
      = Work.RPB.signedArea
          (fun t => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (CI.c τ (t + r t) + CI.c τ (t - r t))) := by
    congr 1
    funext t
    exact hpoint t
  have hscale : Work.RPB.signedArea
        (fun t => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (CI.c τ (t + r t) + CI.c τ (t - r t)))
      = (1 / 2) * Work.RPB.signedArea (fun t => CI.c τ (t + r t) + CI.c τ (t - r t)) := by
    have h := signedArea_const_mul (fun t => CI.c τ (t + r t) + CI.c τ (t - r t))
      ((Real.sqrt 2)⁻¹)
    have h' : Work.RPB.signedArea
          (fun t => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (CI.c τ (t + r t) + CI.c τ (t - r t)))
        = ((Real.sqrt 2)⁻¹) ^ 2
          * Work.RPB.signedArea (fun t => CI.c τ (t + r t) + CI.c τ (t - r t)) := by
      simpa only [] using h
    rw [h']
    congr 1
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hN, hscale, hsum]
  ring

end Work.RPB.B5
