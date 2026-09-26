import Mathlib
import Submission.Work.Drive.ofatTopEndDefs
import Submission.Work.Drive.ofatEndgameSOfTopEnd
import Submission.Work.Drive.blurSlicesScheduledFull
import Submission.Work.Drive.chamferLoopGen_slicesClause
import Submission.Work.Drive.sweepToNeedleEpsOfSlices_gen
import Submission.Work.Drive.sweepFamOf_chamferLoopGen_eq_sweepNeedle

/-!
# The top end of the `OFat` endgame from the wide-end estimate

This file discharges `Work.Drive.ofatTopEnd_of_wideEnd`: the producer of the last pin
`Work.Drive.NeedleTopEnd` of the `OFat` endgame, from

* the **wide-end estimate** `Work.Drive.WideEndUniform` (the C¹-closeness of a blurred *scheduled*
  slice near `σ = 1` to a rotation of the knot, with the trough slice `σ₀` produced before the
  layout), and
* the **scheduling slot** `Work.Drive.SchedSlot` (the injectivity of the raw scheduled loop and the
  junction non-degeneracy on the clamped window).

The proof is the assembly already used for `Work.Drive.needleTopEnd_of_schedSlot`: the wide-end
estimate gives `σ₀ ∈ (1/2,1)`, the slot at the window `(ε, σ₀)` gives the layout `(lay, ρ₀, cQ)` with
`C * lay ≤ ε₁/4`, the proved `Work.Drive.chamferLoopGen_slicesClause` turns the slot's injectivity and
junction data into the blurred-slices clause on `[ε, σ₀]` at *that* layout, and the three-phase glue
(rotation → interpolation to the wide-end slice → reparametrised sweep) produces the family.  The
trough identity `Work.Drive.sweepFamOf_chamferLoopGen_eq_sweepNeedle` moves the endpoint from the
blurred scheduled slice at `ε` to the standard needle `sweepNeedleFam`.
-/

noncomputable section
set_option maxHeartbeats 4000000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The transcription core of the top end at a prescribed layout.**  This is the body of
`Work.Drive.sweepToNeedleEpsOfSlices_genLw` from its step (d) on, with

* the loop `Γ = chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D)`,
* the slices clause `hsl` read at the *single* window `[ε, σ₀]` for this layout,
* the wide-end estimate `hsw` at the *single* slice `σ₀` for this layout.

(it is the same three-phase construction: phase A a rotation of the knot, phase B the interpolation to
the wide-end slice, phase C the sweep itself). -/
private theorem topEnd_of_data_wide {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {δ ε σ₀ lay ρ₀ cQ δs ε_uc ε₁ Ls Δ : ℝ}
    (hδs : 0 < δs) (hlay0 : 0 < lay) (hlay4 : lay ≤ 1 / 4) (hlayΔ : lay ≤ Δ)
    (hε0 : 0 < ε) (hεσ₀ : ε < σ₀)
    (hε₁0 : 0 < ε₁) (hε₁uc : ε₁ ≤ ε_uc) (hLs0 : 0 < Ls) (hΔ : 0 < Δ) (hδ : 0 < δ)
    (h_uc : ∀ W : ℝ → ℝ → Space, ContDiff ℝ 1 (fun p : ℝ × ℝ => W p.1 p.2) →
      (∀ s t : ℝ, W (t + period) s = W t s) →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ‖W t s‖ < ε_uc ∧
        ‖deriv (fun u : ℝ => W u s) t‖ < ε_uc) →
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        Function.Periodic (fun t : ℝ => r (t + s * period) + W t s) period ∧
          Set.InjOn (fun t : ℝ => r (t + s * period) + W t s) (Set.Ico 0 period) ∧
            ∀ t : ℝ, velocity (fun t : ℝ => r (t + s * period) + W t s) t ≠ 0)
    (hsl : ∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ Ls → 0 < δ₂ → δ₂ ≤ Ls →
        ∀ σ ∈ Set.Icc ε σ₀,
          Set.InjOn (fun t : ℝ => sweepFamOf
              (chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D)
                (schedBeta r lay ρ₀ δs cQ D)) δ₁ δ₂ σ t) (Set.Ico 0 period) ∧
          (∀ t : ℝ, velocity (fun t : ℝ => sweepFamOf
              (chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D)
                (schedBeta r lay ρ₀ δs cQ D)) δ₁ δ₂ σ t) t ≠ 0))
    (hsw : ∀ L : ℝ, 0 < L →
        ∃ (δ₁ δ₂ c : ℝ) (Θ : ℝ → ℝ), 0 < δ₁ ∧ δ₁ ≤ L ∧ 0 < δ₂ ∧ δ₂ ≤ L ∧
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
          (∀ t : ℝ, Θ (t + period) = Θ t + period) ∧ (∀ t : ℝ, 0 < deriv Θ t) ∧
          (∀ t : ℝ, ‖sweepFamOf (chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D)
                (schedBeta r lay ρ₀ δs cQ D)) δ₁ δ₂ σ₀ (Θ t) - r (t + c)‖ < ε₁) ∧
          (∀ t : ℝ, ‖deriv (fun u : ℝ => sweepFamOf (chamferLoopGen r D lay
                (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D))
                δ₁ δ₂ σ₀ (Θ u)) t - velocity r (t + c)‖ < ε₁)) :
    ∃ (δ₁ δ₂ : ℝ) (r0 : ℝ → Space) (H : ℝ → ℝ → Space),
      (0 < lay ∧ lay < 1 / 2 ∧ 0 < δ₁ ∧ 0 < δ₂ ∧ δ₂ ≤ ε / 2 ∧
        lay ≤ Δ ∧ δ₁ ≤ Δ ∧ δ₂ ≤ Δ) ∧
      IsSmoothKnot r0 ∧
      (∀ t : ℝ, ‖r0 t - r t‖ < δ ∧ ‖velocity r0 t - velocity r t‖ < δ) ∧
      ContDiff ℝ 1 (fun p : ℝ × ℝ => H p.1 p.2) ∧
      (∀ s t : ℝ, H (t + period) s = H t s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => H t s)) ∧
      (∀ t : ℝ, H t 0 = r0 t) ∧
      (∀ t : ℝ, H t 1 = sweepFamOf (chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D)
          (schedBeta r lay ρ₀ δs cQ D)) δ₁ δ₂ ε t) := by
  have hle : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  have hle0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- ## (d) the scheduled loop and the structural clauses of its blurred family
  let Γ : ℝ → ℝ → Space :=
    chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D)
  have hLI : MeasureTheory.LocallyIntegrable (fun p : ℝ × ℝ => Γ p.1 p.2) MeasureTheory.volume :=
    chamferLoopGen_locallyIntegrable (r := r) hr (D := D) (lay := lay) (ρ₀ := ρ₀) (δs := δs)
      (cQ := cQ) hlay0 hδs
  have hperΓ : ∀ s t : ℝ, Γ s (t + period) = Γ s t :=
    fun s t => chamferLoopGen_periodic_t D lay (schedAlpha lay ρ₀ δs D)
      (schedBeta r lay ρ₀ δs cQ D) s t
  obtain ⟨δ₁, δ₂, c, Θ, hδ₁0, hδ₁Lw, hδ₂0, hδ₂Lw, hΘsm, hΘsh, hΘpos, hcl1, hcl2⟩ :=
    hsw (min Ls (min Δ (min (ε / 4) (1 / 4)))) (by
      exact lt_min hLs0 (lt_min hΔ (lt_min (by linarith) (by norm_num))))
  have hδ₁Ls : δ₁ ≤ Ls := hδ₁Lw.trans (min_le_left _ _)
  have hδ₂Ls : δ₂ ≤ Ls := hδ₂Lw.trans (min_le_left _ _)
  have hδ₁Δ : δ₁ ≤ Δ := hδ₁Lw.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ₂Δ : δ₂ ≤ Δ := hδ₂Lw.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ₂ε : δ₂ ≤ ε / 2 := by
    have h : δ₂ ≤ ε / 4 :=
      hδ₂Lw.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have hδ₁ne : δ₁ ≠ 0 := ne_of_gt hδ₁0
  have hδ₂ne : δ₂ ≠ 0 := ne_of_gt hδ₂0
  obtain ⟨hsmjoint, hsmper, hsmslice⟩ :=
    sweepFamOf_contDiff_periodic_li Γ hLI hperΓ δ₁ δ₂ hδ₁ne hδ₂ne
  have hσcl : ∀ σ ∈ Set.Icc ε σ₀,
      Set.InjOn (fun t : ℝ => sweepFamOf Γ δ₁ δ₂ σ t) (Set.Ico 0 period) ∧
      (∀ t : ℝ, velocity (fun t : ℝ => sweepFamOf Γ δ₁ δ₂ σ t) t ≠ 0) :=
    fun σ hσ => hsl δ₁ δ₂ hδ₁0 hδ₁Ls hδ₂0 hδ₂Ls σ hσ
  -- ## (e) the shifted knot `K`, the wide-end slice `G`, and the correction `w`
  let K : ℝ → Space := fun t => r (t + c)
  let G : ℝ → Space := fun t => sweepFamOf Γ δ₁ δ₂ σ₀ (Θ t)
  let w : ℝ → Space := fun t => G t - K t
  have hKsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => r (t + c))
    exact (hr.smooth.of_le le_top).comp (by
      simpa using (contDiff_id.add contDiff_const :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => t + c)))
  have hGsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => sweepFamOf Γ δ₁ δ₂ σ₀ (Θ t))
    exact (hsmslice σ₀).comp hΘsm
  have hwsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G - K)
    exact hGsmooth.sub hKsmooth
  have hwper : Function.Periodic w period := by
    intro t
    change G (t + period) - K (t + period) = G t - K t
    have h1 : G (t + period) = G t := by
      change sweepFamOf Γ δ₁ δ₂ σ₀ (Θ (t + period)) = sweepFamOf Γ δ₁ δ₂ σ₀ (Θ t)
      rw [hΘsh t, hsmper]
    have h2 : K (t + period) = K t := by
      change r (t + period + c) = r (t + c)
      rw [show t + period + c = (t + c) + period from by ring]
      exact hr.periodic (t + c)
    rw [h1, h2]
  have hwbd : ∀ t : ℝ, ‖w t‖ < ε_uc := by
    intro t
    have h : ‖w t‖ < ε₁ := by
      change ‖sweepFamOf Γ δ₁ δ₂ σ₀ (Θ t) - r (t + c)‖ < ε₁
      exact hcl1 t
    exact lt_of_lt_of_le h hε₁uc
  have hwvel : ∀ t : ℝ, ‖velocity w t‖ < ε_uc := by
    intro t
    have h := hcl2 t
    have hderiv : velocity w t
        = deriv (fun u : ℝ => sweepFamOf Γ δ₁ δ₂ σ₀ (Θ u)) t - velocity r (t + c) := by
      change deriv (fun u : ℝ => G u - K u) t
        = deriv (fun u : ℝ => sweepFamOf Γ δ₁ δ₂ σ₀ (Θ u)) t - velocity r (t + c)
      rw [show (fun u : ℝ => G u - K u)
          = (fun u : ℝ => sweepFamOf Γ δ₁ δ₂ σ₀ (Θ u)) - fun u : ℝ => r (u + c) from rfl]
      rw [deriv_sub]
      · congr 1
        change deriv (fun u : ℝ => r (u + c)) t = deriv r (t + c)
        exact deriv_shift r ((hr.smooth.of_le le_top).differentiable hle0 (t + c))
      · exact (hGsmooth.differentiable hle0) t
      · exact DifferentiableAt.comp t
          ((hr.smooth.of_le le_top).differentiable hle0 (t + c)) (by fun_prop)
    rw [hderiv]
    exact lt_of_lt_of_le h hε₁uc
  -- ## (f) phase A: rotations of the knot
  let A : ℝ → ℝ → Space := fun t p => r (t + c * p)
  have hAjoint : ContDiff ℝ 1 (fun p : ℝ × ℝ => A p.1 p.2) := by
    change ContDiff ℝ 1 (fun p : ℝ × ℝ => r (p.1 + c * p.2))
    have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 + c * p.2) := by fun_prop
    exact (hr.smooth.of_le le_top).of_le hle |>.comp h1
  have hAper : ∀ s t : ℝ, A (t + period) s = A t s := by
    intro s t
    change r (t + period + c * s) = r (t + c * s)
    rw [show t + period + c * s = (t + c * s) + period from by ring]
    exact hr.periodic _
  have hAslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => A t s) := by
    intro s hs
    change IsCInfKnot (fun t : ℝ => r (t + c * s))
    simpa using isCInfKnot_shift (IsSmoothKnot.toCInf hr) (c * s)
  have hA1 : ∀ t : ℝ, A t 1 = K t := by
    intro t
    change r (t + c * 1) = r (t + c)
    ring_nf
  have hA0 : ∀ t : ℝ, A t 0 = r t := by
    intro t
    change r (t + c * 0) = r t
    simp
  -- ## (g) phase B: from the shifted knot to the wide-end slice
  let B : ℝ → ℝ → Space := fun t p => K t + p • w t
  have hBjoint : ContDiff ℝ 1 (fun p : ℝ × ℝ => B p.1 p.2) := by
    change ContDiff ℝ 1 (fun p : ℝ × ℝ => K p.1 + p.2 • w p.1)
    refine (hKsmooth.of_le hle).comp contDiff_fst |>.add ?_
    exact contDiff_snd.smul ((hwsmooth.of_le hle).comp contDiff_fst)
  have hBper : ∀ s t : ℝ, B (t + period) s = B t s := by
    intro s t
    change K (t + period) + s • w (t + period) = K t + s • w t
    rw [show K (t + period) = K t from by
      change r (t + period + c) = r (t + c)
      rw [show t + period + c = (t + c) + period from by ring]
      exact hr.periodic (t + c), hwper t]
  have hB0 : ∀ t : ℝ, B t 0 = K t := by
    intro t
    change K t + (0 : ℝ) • w t = K t
    simp
  have hB1 : ∀ t : ℝ, B t 1 = G t := by
    intro t
    change K t + (1 : ℝ) • (G t - K t) = G t
    rw [one_smul]
    abel
  have hBslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => B t s) := by
    intro s hs
    have hnorm1 : ∀ t : ℝ, ‖s • w t‖ < ε_uc := by
      intro t
      rw [norm_smul]
      have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
      calc |s| * ‖w t‖ ≤ 1 * ‖w t‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
        _ = ‖w t‖ := one_mul _
        _ < ε_uc := hwbd t
    have hnorm2 : ∀ t : ℝ, ‖deriv (fun u : ℝ => s • w u) t‖ < ε_uc := by
      intro t
      have hd : deriv (fun u : ℝ => s • w u) t = s • velocity w t := by
        show deriv (fun u : ℝ => s • w u) t = s • deriv w t
        exact (((hwsmooth.differentiable hle0) t).hasDerivAt.const_smul s).deriv
      rw [hd, norm_smul]
      have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
      calc |s| * ‖velocity w t‖ ≤ 1 * ‖velocity w t‖ :=
            mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
        _ = ‖velocity w t‖ := one_mul _
        _ < ε_uc := hwvel t
    have hWsm : ContDiff ℝ 1 (fun q : ℝ × ℝ => s • w q.1) :=
      ((hwsmooth.of_le hle).comp contDiff_fst).const_smul s
    have hWper : ∀ a t : ℝ, s • w (t + period) = s • w t := by
      intro a t; rw [hwper t]
    have hWsmall : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
        ‖s • w t‖ < ε_uc ∧ ‖deriv (fun u : ℝ => s • w u) t‖ < ε_uc :=
      fun a ha t => ⟨hnorm1 t, hnorm2 t⟩
    obtain ⟨hc1, hc2, hc3⟩ := h_uc (fun t a => s • w t) hWsm hWper hWsmall
      (sweepParam c) ⟨(sweepParam_mem c).1, (sweepParam_mem c).2.le⟩
    have hshift : (fun t : ℝ => r (t + sweepParam c * period) + s • w t)
        = fun t : ℝ => B t s := by
      funext t
      change r (t + sweepParam c * period) + s • w t = r (t + c) + s • w t
      congr 1
      exact (shift_eq_mod hr.periodic c t).symm
    rw [hshift] at hc1 hc2 hc3
    refine ⟨?_, hc1, hc2, hc3⟩
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => r (t + c) + s • w t)
    exact hKsmooth.add (hwsmooth.const_smul s)
  -- ## (h) phase C: the sweep itself, reparametrised
  have hΘ1 : ContDiff ℝ 1 Θ := hΘsm.of_le hle
  obtain ⟨hθjoint1, hθderiv, hθshift⟩ := interpTheta_facts hΘ1 hΘsh hΘpos
  have hθsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (1 - q.2) * Θ q.1 + q.2 * q.1) := interpTheta_smooth hΘsm
  let σfun : ℝ → ℝ := fun p => ε + (σ₀ - ε) * (1 - gluePsi p)
  let θfun : ℝ → ℝ → ℝ := fun p t => (1 - p) * Θ t + p * t
  let Cc : ℝ → ℝ → Space := fun t p => sweepFamOf Γ δ₁ δ₂ (σfun p) (θfun p t)
  have hσmem : ∀ p ∈ Set.Icc (0 : ℝ) 1, ε ≤ σfun p ∧ σfun p ≤ σ₀ := by
    intro p hp
    have hg : gluePsi p ∈ Set.Icc (0 : ℝ) 1 := gluePsi_facts.2.2.1 p hp
    have hsub : 0 ≤ σ₀ - ε := by linarith
    change ε ≤ ε + (σ₀ - ε) * (1 - gluePsi p) ∧ ε + (σ₀ - ε) * (1 - gluePsi p) ≤ σ₀
    have h1 : 0 ≤ (σ₀ - ε) * (1 - gluePsi p) := mul_nonneg hsub (by linarith [hg.2])
    have h2 : (σ₀ - ε) * (1 - gluePsi p) ≤ σ₀ - ε := by
      have h3 : (1 - gluePsi p) ≤ 1 := by linarith [hg.1]
      nlinarith [hsub, h3]
    exact ⟨by linarith, by linarith⟩
  have hσc1 : ContDiff ℝ 1 σfun := by
    change ContDiff ℝ 1 (fun p : ℝ => ε + (σ₀ - ε) * (1 - gluePsi p))
    have hg : ContDiff ℝ 1 gluePsi := gluePsi_facts.2.2.2.2
    exact contDiff_const.add (contDiff_const.mul (contDiff_const.sub hg))
  have hCcjoint : ContDiff ℝ 1 (fun p : ℝ × ℝ => Cc p.1 p.2) := by
    change ContDiff ℝ 1 (fun p : ℝ × ℝ => sweepFamOf Γ δ₁ δ₂ (σfun p.2) (θfun p.2 p.1))
    have hinner : ContDiff ℝ 1 (fun q : ℝ × ℝ => (σfun q.2, θfun q.2 q.1)) := by
      refine (hσc1.comp contDiff_snd).prodMk ?_
      change ContDiff ℝ 1 (fun q : ℝ × ℝ => (1 - q.2) * Θ q.1 + q.2 * q.1)
      exact hθjoint1
    have hcomp := hsmjoint.comp hinner
    simpa only [Function.comp_def] using hcomp
  have hCcper : ∀ s t : ℝ, Cc (t + period) s = Cc t s := by
    intro s t
    change sweepFamOf Γ δ₁ δ₂ (ε + (σ₀ - ε) * (1 - gluePsi s))
        ((1 - s) * Θ (t + period) + s * (t + period))
      = sweepFamOf Γ δ₁ δ₂ (ε + (σ₀ - ε) * (1 - gluePsi s)) ((1 - s) * Θ t + s * t)
    rw [show (1 - s) * Θ (t + period) + s * (t + period)
        = ((1 - s) * Θ t + s * t) + period from by rw [hΘsh t]; ring]
    exact hsmper _ _
  have hCcslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => Cc t s) := by
    intro s hs
    have hmem := hσmem s hs
    have hslic : IsCInfKnot (fun t : ℝ => sweepFamOf Γ δ₁ δ₂ (σfun s) t) :=
      ⟨hsmslice (σfun s), hsmper (σfun s), (hσcl (σfun s) ⟨hmem.1, hmem.2⟩).1,
        (hσcl (σfun s) ⟨hmem.1, hmem.2⟩).2⟩
    have hgsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => θfun s t) := by
      change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (1 - s) * Θ t + s * t)
      exact hθsmooth.comp (contDiff_id.prodMk contDiff_const)
    have hgshift : ∀ t : ℝ, θfun s (t + period) = θfun s t + period := by
      intro t
      change (1 - s) * Θ (t + period) + s * (t + period) = (1 - s) * Θ t + s * t + period
      rw [hΘsh t]; ring
    have hgderiv : ∀ t : ℝ, 0 < deriv (fun u : ℝ => θfun s u) t := by
      intro t
      have h := hθderiv s hs t
      rwa [show (fun u : ℝ => θfun s u) = fun u : ℝ => (1 - s) * Θ u + s * u from
        funext fun u => rfl] at h
    have hcomp := isCInfKnot_comp_reparam hgsmooth hgshift hgderiv hslic
    change IsCInfKnot (fun t : ℝ => sweepFamOf Γ δ₁ δ₂ (σfun s) (θfun s t))
    simpa only [Function.comp_def] using hcomp
  have hCc0 : ∀ t : ℝ, Cc t 0 = G t := by
    intro t
    change sweepFamOf Γ δ₁ δ₂ (ε + (σ₀ - ε) * (1 - gluePsi 0)) ((1 - 0) * Θ t + 0 * t) = G t
    have h1 : ε + (σ₀ - ε) * (1 - gluePsi 0) = σ₀ := by rw [gluePsi_facts.1]; ring
    have h2 : (1 - 0) * Θ t + 0 * t = Θ t := by ring
    rw [h1, h2]
  have hCc1 : ∀ t : ℝ, Cc t 1 = sweepFamOf Γ δ₁ δ₂ ε t := by
    intro t
    change sweepFamOf Γ δ₁ δ₂ (ε + (σ₀ - ε) * (1 - gluePsi 1)) ((1 - 1) * Θ t + 1 * t)
      = sweepFamOf Γ δ₁ δ₂ ε t
    have h1 : ε + (σ₀ - ε) * (1 - gluePsi 1) = ε := by rw [gluePsi_facts.2.1]; ring
    have h2 : (1 - 1) * Θ t + 1 * t = t := by ring
    rw [h1, h2]
  -- ## (i) gluing the three phases
  let AB : ℝ → ℝ → Space := fun t s => sweepGlue A B s t
  obtain ⟨hABjoint, hABper, hABslice, hAB0, hAB1⟩ :=
    sweepGlue_clauses hAjoint hBjoint (fun t => (hA1 t).trans (hB0 t).symm)
      hAslice hBslice hAper hBper
  have hAB0' : ∀ t : ℝ, AB t 0 = A t 0 := hAB0
  have hjun : ∀ t : ℝ, AB t 1 = Cc t 0 := by
    intro t
    change sweepGlue A B 1 t = Cc t 0
    rw [hAB1 t, hB1 t, hCc0 t]
  obtain ⟨hHjoint, hHper, hHslice, hH0, hH1⟩ :=
    sweepGlue_clauses hABjoint hCcjoint hjun hABslice hCcslice hABper hCcper
  refine ⟨δ₁, δ₂, r, fun t s => sweepGlue AB Cc s t,
    ⟨hlay0, by linarith, hδ₁0, hδ₂0, hδ₂ε, hlayΔ, hδ₁Δ, hδ₂Δ⟩, hr, ?_, hHjoint, hHper,
    hHslice, ?_, ?_⟩
  · intro t
    exact ⟨by rw [sub_self, norm_zero]; exact hδ, by rw [sub_self, norm_zero]; exact hδ⟩
  · intro t
    change sweepGlue AB Cc 0 t = r t
    rw [hH0, hAB0']
    exact hA0 t
  · intro t
    change sweepGlue AB Cc 1 t = sweepFamOf Γ δ₁ δ₂ ε t
    rw [hH1]
    exact hCc1 t

theorem ofatTopEnd_of_wideEnd {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {δs ε : ℝ} (hδs : 0 < δs) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (hwide : Work.Drive.WideEndUniform r D δs)
    (htrough : ∀ σ ∈ Set.Icc (ε / 2) (3 * ε / 2), 4 * Work.Drive.schedC D σ ≤ δs)
    (hslot : ∀ Lmax : ℝ, 0 < Lmax → ∀ ε' σ₀ : ℝ, 0 < ε' → ε' < σ₀ → σ₀ < 1 →
      Work.Drive.SchedSlot r D δs Lmax ε' σ₀) :
    Work.Drive.NeedleTopEnd r D ε := by

  intro δ hδ Δ hΔ
  -- ## (a) the uniform small-correction threshold, valid for every rotation of `r`
  have hle : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  have hrotjoint : ContDiff ℝ 1 (fun p : ℝ × ℝ => r (p.1 + p.2 * period)) := by
    have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 + p.2 * period) := by fun_prop
    exact (hr.smooth.of_le le_top).of_le hle |>.comp h1
  have hrotper : ∀ s t : ℝ, r ((t + period) + s * period) = r (t + s * period) := by
    intro s t
    have h : t + period + s * period = (t + s * period) + period := by ring
    rw [h, hr.periodic]
  have hrotsl : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => r (t + s * period)) := by
    intro s hs
    simpa using isCInfKnot_shift (IsSmoothKnot.toCInf hr) (s * period)
  obtain ⟨ε_uc, hε_uc_pos, h_uc⟩ := uniformCorrection_clauses hrotjoint hrotper hrotsl
  -- ## (b) the wide end, with the slice `σ₀` chosen *before* the layout
  have hwideUnif : WideEndUniform r D δs := hwide
  obtain ⟨Cmin, hCminpos, hCsw⟩ := hwideUnif
  set ε₁ : ℝ := min ε_uc (Cmin / 2) with hε₁def
  have hε₁pos : 0 < ε₁ := lt_min hε_uc_pos (by linarith)
  have hε₁uc : ε₁ ≤ ε_uc := min_le_left _ _
  have hε₁C : ε₁ ≤ Cmin := by
    have h : ε₁ ≤ Cmin / 2 := min_le_right _ _
    linarith
  obtain ⟨σ₀, hσ₀half, hσ₀lt, hgap, hsw⟩ := hCsw Cmin le_rfl ε₁ hε₁pos hε₁C
  have hεσ₀ : ε < σ₀ := lt_trans hε1 hσ₀half
  -- ## (c) the slot at the window `(ε, σ₀)`
  set Lmax : ℝ := min (min Δ (1 / 4)) (ε₁ / (4 * Cmin)) with hLmaxdef
  have hLmaxpos : 0 < Lmax := by
    rw [hLmaxdef]
    exact lt_min (lt_min hΔ (by norm_num)) (by positivity)
  obtain ⟨lay, ρ₀, cQ, hlay0, hlayL, hlay4, hρ₀0, hcQ0, hcQ1, hIJ⟩ :=
    hslot Lmax hLmaxpos ε σ₀ hε0 hεσ₀ hσ₀lt
  have hlayΔ : lay ≤ Δ := by
    have h : lay ≤ min Δ (1 / 4) := le_trans hlayL (min_le_left _ _)
    exact le_trans h (min_le_left _ _)
  have hClay : Cmin * lay ≤ ε₁ / 4 := by
    have h : lay ≤ ε₁ / (4 * Cmin) := le_trans hlayL (min_le_right _ _)
    have h4 : (0 : ℝ) < 4 * Cmin := by linarith
    have hm := mul_le_mul_of_nonneg_left h hCminpos.le
    have he : Cmin * (ε₁ / (4 * Cmin)) = ε₁ / 4 := by field_simp
    linarith [hm, he.le, he.ge]
  -- the slices clause on `[ε, σ₀]` at this layout
  obtain ⟨Ls, hLs0, hLs⟩ :=
    chamferLoopGen_slicesClause (ρ₀ := ρ₀) (δs := δs) (cQ := cQ) (lay := lay)
      hr D hδs hlay0 hlay4 hε0 hεσ₀ (hσ₀lt) (fun σ hσ => (hIJ σ hσ).2) (fun σ hσ => (hIJ σ hσ).1)
  -- the wide-end data at this layout
  have hsw' : ∀ L : ℝ, 0 < L →
      ∃ (δ₁ δ₂ c : ℝ) (Θ : ℝ → ℝ), 0 < δ₁ ∧ δ₁ ≤ L ∧ 0 < δ₂ ∧ δ₂ ≤ L ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
        (∀ t : ℝ, Θ (t + period) = Θ t + period) ∧ (∀ t : ℝ, 0 < deriv Θ t) ∧
        (∀ t : ℝ, ‖sweepFamOf (chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D)
              (schedBeta r lay ρ₀ δs cQ D)) δ₁ δ₂ σ₀ (Θ t) - r (t + c)‖ < ε₁) ∧
        (∀ t : ℝ, ‖deriv (fun u : ℝ => sweepFamOf (chamferLoopGen r D lay
              (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D))
              δ₁ δ₂ σ₀ (Θ u)) t - velocity r (t + c)‖ < ε₁) :=
    fun L hL => hsw lay hlay0 hlay4 hClay ρ₀ cQ hρ₀0 hcQ0 L hL
  obtain ⟨δ₁, δ₂, r0, H, hbox, hr0, hclose, hHj, hHper, hHslice, hH0, hH1⟩ :=
    topEnd_of_data_wide (r := r) hr (D := D) (ε := ε) (σ₀ := σ₀) (lay := lay) (ρ₀ := ρ₀)
      (cQ := cQ) (δs := δs) (ε_uc := ε_uc) (ε₁ := ε₁) (Ls := Ls) (Δ := Δ)
      hδs hlay0 hlay4 hlayΔ hε0 hεσ₀ hε₁pos hε₁uc hLs0 hΔ hδ h_uc hLs hsw'
  obtain ⟨hlay0', hlay12, hδ₁0', hδ₂0', hδ₂ε, hlayΔ', hδ₁Δ', hδ₂Δ'⟩ := hbox
  -- ## (d) the blurred scheduled slice at `σ = ε` is the needle
  have hwin : ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      schedAlpha lay ρ₀ δs D (ε - δ₂ * v) = lay ∧
      schedBeta r lay ρ₀ δs cQ D (ε - δ₂ * v) = lay := by
    intro v hv
    have hvabs : |v| ≤ 1 := abs_le.mpr hv
    have hσ_lo : ε / 2 ≤ ε - δ₂ * v := by
      have h1 : δ₂ * v ≤ δ₂ := by
        calc δ₂ * v ≤ δ₂ * 1 := mul_le_mul_of_nonneg_left hv.2 hδ₂0'.le
          _ = δ₂ := mul_one _
      linarith
    have hσ_hi : ε - δ₂ * v ≤ 3 * ε / 2 := by
      have h1 : -(δ₂ * v) ≤ δ₂ := by
        have h2 : -(δ₂ * v) ≤ δ₂ * 1 := by
          have h3 : -v ≤ 1 := by linarith [hv.1]
          nlinarith [hδ₂0'.le, h3]
        linarith [h2]
      linarith
    have hσ0' : 0 < ε - δ₂ * v := by linarith [hε0]
    have hσ1' : ε - δ₂ * v < 1 := by
      have : 3 * ε / 2 < 1 := by linarith
      linarith
    have hc : schedC D (ε - δ₂ * v) ≤ δs / 4 := by
      have h := htrough (ε - δ₂ * v) ⟨hσ_lo, hσ_hi⟩
      linarith
    have hW := sweepW'_pos_lt D hσ0' hσ1'
    exact ⟨schedAlpha_trough D hδs hlay0 (ne_of_gt hW.1) hW.1.le hc,
      schedBeta_trough D hδs hc⟩
  have hend := sweepFamOf_chamferLoopGen_eq_sweepNeedle (r := r) (D := D) (ρ₀ := ρ₀)
    (δs := δs) (cQ := cQ) (lay := lay) (δ₁ := δ₁) (δ₂ := δ₂) (ε := ε) hwin
  refine ⟨lay, δ₁, δ₂, r0, H,
    ⟨hlay0', hlay12, hδ₁0', hδ₂0', hδ₂ε, hlayΔ', hδ₁Δ', hδ₂Δ'⟩,
    hr0, hclose, hHj, hHper, hHslice, hH0, ?_⟩
  intro t
  rw [hH1 t, hend]


end Work.Drive
