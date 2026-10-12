import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.HeatSamplingMonoDefs
import Submission.Work.BoseBoxFock.firstMoment_heatForm
import Submission.Work.BoseBoxFock.kinRow_lattice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators Real Topology

/-! # `Work.BoseBoxFock.firstMoment_alias` — the `2R1 ≤ 3S1` row

**The target** (the statement at the bottom of this file, unchanged): for `ℓ > 0` and smooth `ψ`
supported in the box `boxL ℓ`,

    2·⟨g,√−Δ g⟩  ≤  3·Σ_n ℓ⁻³‖k_n‖‖ĝ(k_n)‖² ,   g := χ_Λ·(ψ − ℓ⁻³∫_{acube ℓ}ψ) ,  k_n = (2π/ℓ)n .

This file fixes the **vocabulary** in which the row is a single analytic crux, and proves
everything that is *not* the crux.

* `latMoment ℓ g` — the lattice first moment `S1 = Σ_n ℓ⁻³‖k_n‖‖ĝ(k_n)‖²`;
* `bsOneBody_sqrtKin_eq_kinFirst` — the target's left-hand side is literally `kinFirst g`
  (`kinFirst` is the corpus's name for `(2π)⁻³∫‖p‖‖ĝ(p)‖²`);
* `firstMomentSum_eq_latMoment` — the target's right-hand side is literally `3·latMoment ℓ g`;
* `three_latMoment_sub_two_kinFirst` + `kinFirst_le_of_heatSpec` — **the row follows from the
  pointwise heat row** `N + 2·contHeat(t) − 3·latHeat(t) ≥ 0` (`∀t>0`), via the PROVED
  subordinations (`lattice_heatSubordination`, `continuum_heatSubordination_v2`) and the mass
  identity (`frame_lattice_ball`).  This is exactly the conclusion of the corpus's
  `heatSampling_le`;
* `latMoment_deficit` — **the remaining analytic crux**, in the cleanest form: for every smooth
  `g` whose support lies in the *closed* ball of radius `ℓ/2` (the class of the admissible
  states `g = χ_Λ·h`), one has `2·kinFirst g ≤ 3·latMoment ℓ g`.

**Where the crux stands** (see `FINDING_firstMoment_alias_s11.md` in this directory).
With `𝒢 = Re(g⋆g̃)` (supported in `closedBall 0 ℓ`, `C^∞`, and *flat* on the sphere `‖u‖ = ℓ`),
the PROVED `aliasImageIdentity` writes the deficit as

    D := kinFirst g − latMoment ℓ g = π⁻² Σ_{m≠0} ∫_u 𝒢(u)‖u − ℓ•latVec m‖⁻⁴ du ,

so the crux is `D ≤ kinFirst g/3`; numerically `D/kinFirst ≤ 0.132` over every admissible state
tested (factor 2.5 of room), but every route based on a *scalar* summary of the state is dead:
the two-blob states `g = φ(·−p)+φ(·+p)` with `‖p‖ = ℓ/2−ρ` have `D ≈ π⁻²·2(2ρ)⁻⁴` while
`N/ℓ ≈ 2c_φ ρ⁻³`, so `D·ℓ/N → ∞`, and they are admissible (their `h = g/χ_Λ` is smooth, since
`g` is supported strictly inside the open ball).  The comparison must therefore be made between
the two *kernels* `K = Σ_{m≠0}‖·−ℓm‖⁻⁴` and `(𝒢(0)−𝒢)/𝒢`.

Through the reduction above the crux also follows from the corpus's `heatSampling_le`, whose
currently-open content is one half of the antitonicity of `t ↦ hsKT/hsKR` (the "means"
inequality; the corpus's PROVED `hsRatio_mono_of_lowMean` covers the case
`hsKR2 ≤ (2π/ℓ)²·hsKR`, the case `hsKR2 > (2π/ℓ)²·hsKR` is open). -/

noncomputable section

/-- **The lattice first moment `S1`** of a state `g`: `Σ_n ℓ⁻³·‖k_n‖·‖ĝ(k_n)‖²`, `k_n = kmomInt ℓ n`. -/
noncomputable def latMoment (ℓ : ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ *
    ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2

lemma latMoment_eq (ℓ : ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℂ) :
    latMoment ℓ g = ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ *
      ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := rfl

/-- **The target's left-hand side is the free `√−Δ` form of the windowed mean-free state:**
for `F = (fun r => r)` and `u = 0`, `bsOneBody` *is* `(2π)⁻³∫‖p‖‖kinFT (χ_Λ·Q_Λψ) p‖²`, i.e.
`kinFirst (winState ℓ ψ)` (definitional, via `winState_eq`). -/
theorem bsOneBody_sqrtKin_eq_kinFirst (ℓ : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BSKinetic.bsOneBody ℓ (fun r => r) 0 ψ = kinFirst (winState ℓ ψ) := by
  rw [Work.BSKinetic.bsOneBody, kinFirst, winState_eq]

/-- **The target's right-hand side is the lattice first moment of `winState ℓ ψ`**: the
`qVec`-coefficients are the values of `kinFT (winState ℓ ψ)` at the lattice momenta
(`qCoeff_eq_winState`, PROVED). -/
theorem firstMomentSum_eq_latMoment {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hψsupp : tsupport ψ ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    firstMomentSum ℓ ψ = latMoment ℓ (winState ℓ ψ) := by
  rw [firstMomentSum, latMoment]
  refine tsum_congr (fun n => ?_)
  rw [qCoeff_eq_winState hℓ hψ hψsupp n]
  ring

/-- **The heat form of the deficit, in the `latMoment` vocabulary** (the PROVED
`firstMoment_heatForm`). -/
theorem kinFirst_sub_latMoment {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2)) :
    kinFirst g - latMoment ℓ g
      = (2 * Real.sqrt Real.pi)⁻¹ *
        ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
          (latHeat ℓ t g - contHeat g t) := by
  simpa only [latMoment] using firstMoment_heatForm hℓ hg hgsupp

/-- **The algebraic form of the deficit**: `3·S1 − 2·R1` is the `t^{-3/2}`-integral of
`N + 2·contHeat − 3·latHeat` (times `(2√π)⁻¹`).  This is the step that turns the row into the
pointwise heat row. -/
theorem three_latMoment_sub_two_kinFirst {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2)) :
    3 * latMoment ℓ g - 2 * kinFirst g
      = (2 * Real.sqrt Real.pi)⁻¹ *
        ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
          (hsN ℓ g + 2 * contHeat g t - 3 * latHeat ℓ t g) := by
  have hgc : HasCompactSupport g := by
    rw [HasCompactSupport, Metric.isCompact_iff_isClosed_bounded]
    exact ⟨isClosed_tsupport g, Metric.isBounded_ball.subset hgsupp⟩
  have hbox : tsupport g ⊆ Work.BoseK15.corpusBox.boxL ℓ :=
    hgsupp.trans (ball_subset_corpusBox_boxL hℓ)
  have hM0 : hsN ℓ g
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
          ‖Submission.BoseGases.kinFT g p‖ ^ 2 :=
    frame_lattice_ball hℓ hg hgc hbox
  have hIlat := integrableOn_heatDeficit_lat hℓ hg hgc
  have hIcont := integrableOn_heatDeficit_cont hg hgc
  have hA : latMoment ℓ g = (2 * Real.sqrt Real.pi)⁻¹ *
      ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * (hsN ℓ g - latHeat ℓ t g) := by
    rw [latMoment_eq, lattice_heatSubordination hℓ hg hgsupp]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by
      simp only [hsN, latHeat]; ring)
  have hB : kinFirst g = (2 * Real.sqrt Real.pi)⁻¹ *
      ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * (hsN ℓ g - contHeat g t) := by
    rw [show kinFirst g = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
        ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2 from rfl,
      continuum_heatSubordination_v2 hℓ hg hgsupp, ← hM0]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by
      simp only [hsN, contHeat]; ring)
  have hIa : IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ)) *
      (hsN ℓ g - latHeat ℓ t g)) (Set.Ioi 0) volume := hIlat
  have hIb : IntegrableOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ)) *
      (hsN ℓ g - contHeat g t)) (Set.Ioi 0) volume := by
    rw [hM0]; exact hIcont
  rw [hA, hB,
    show (3 : ℝ) * ((2 * Real.sqrt Real.pi)⁻¹ * (∫ t in Set.Ioi (0 : ℝ),
          t ^ (-(3 / 2 : ℝ)) * (hsN ℓ g - latHeat ℓ t g)))
        - 2 * ((2 * Real.sqrt Real.pi)⁻¹ * (∫ t in Set.Ioi (0 : ℝ),
          t ^ (-(3 / 2 : ℝ)) * (hsN ℓ g - contHeat g t)))
      = (2 * Real.sqrt Real.pi)⁻¹ *
        (3 * (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * (hsN ℓ g - latHeat ℓ t g))
          - 2 * (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * (hsN ℓ g - contHeat g t)))
      from by ring]
  congr 1
  have h1 : (3 : ℝ) * (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
        (hsN ℓ g - latHeat ℓ t g))
      = ∫ t in Set.Ioi (0 : ℝ), 3 * (t ^ (-(3 / 2 : ℝ)) *
        (hsN ℓ g - latHeat ℓ t g)) := by
    rw [MeasureTheory.integral_const_mul]
  have h2 : (2 : ℝ) * (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
        (hsN ℓ g - contHeat g t))
      = ∫ t in Set.Ioi (0 : ℝ), 2 * (t ^ (-(3 / 2 : ℝ)) *
        (hsN ℓ g - contHeat g t)) := by
    rw [MeasureTheory.integral_const_mul]
  rw [h1, h2, ← MeasureTheory.integral_sub (hIa.const_mul 3) (hIb.const_mul 2)]
  exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring)

/-- **The free row follows from the pointwise heat row** (`N + 2·contHeat − 3·latHeat ≥ 0`),
i.e. from the corpus's `heatSampling_le`. -/
theorem kinFirst_le_of_heatSpec {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2))
    (hspec : ∀ t : ℝ, 0 < t →
      0 ≤ hsN ℓ g + 2 * contHeat g t - 3 * latHeat ℓ t g) :
    2 * kinFirst g ≤ 3 * latMoment ℓ g := by
  have hkey := three_latMoment_sub_two_kinFirst hℓ hg hgsupp
  have hnn : 0 ≤ ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) *
      (hsN ℓ g + 2 * contHeat g t - 3 * latHeat ℓ t g) := by
    refine MeasureTheory.setIntegral_nonneg_of_ae_restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (hspec t ht)
  have hfin := mul_nonneg (by positivity : (0 : ℝ) ≤ (2 * Real.sqrt Real.pi)⁻¹) hnn
  rw [← hkey] at hfin
  linarith

/-- **The remaining analytic crux**: for a smooth state `g` supported in the *closed* ball of
radius `ℓ/2` (the class of the admissible states `g = χ_Λ·h`, `h` smooth on a neighbourhood of
the closed ball),

    2·kinFirst g ≤ 3·latMoment ℓ g .

Equivalently (PROVED `aliasImageIdentity`) `π⁻²Σ_{m≠0}∫𝒢(u)‖u−ℓ•latVec m‖⁻⁴du ≤ kinFirst g/3`.
See `FINDING_firstMoment_alias_s11.md` for the state of the art. -/
theorem latMoment_deficit {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    2 * kinFirst g ≤ 3 * latMoment ℓ g := by
  sorry

/-- `χ_Λ` (the corpus window) vanishes outside the closed ball of radius `ℓ/2`. -/
theorem tsupport_chiLam_subset_closedBall {ℓ : ℝ} (hℓ : 0 < ℓ) :
    tsupport (Work.BoseK15.corpusBox.chiLam ℓ) ⊆ Metric.closedBall 0 (ℓ / 2) := by
  refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
  rw [Function.mem_support] at hx
  by_contra hc
  refine hx ?_
  have hmem : ¬ (x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (ℓ / 2)) := hc
  have hlt : ℓ / 2 < ‖x‖ := by
    by_contra h
    exact hmem (by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_not_gt h)
  have hnorm : (1 / 2 : ℝ) < ‖(ℓ⁻¹ : ℝ) • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le), inv_mul_eq_div,
      lt_div_iff₀ hℓ]
    linarith
  show Work.BoseK15.corpusBox.chiLam ℓ x = 0
  rw [Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi]
  exact Submission.BoseGases.chi_eq_zero_of_norm_gt _ hnorm

/-- `winState ℓ ψ` is supported in the closed ball of radius `ℓ/2`. -/
theorem tsupport_winState_subset {ℓ : ℝ} (hℓ : 0 < ℓ)
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    tsupport (winState ℓ ψ) ⊆ Metric.closedBall 0 (ℓ / 2) := by
  refine (closure_mono (fun z hz => ?_)).trans (tsupport_chiLam_subset_closedBall hℓ)
  rw [Function.mem_support] at hz
  intro h
  apply hz
  show winState ℓ ψ z = 0
  rw [winState]
  rw [show Work.BoseK15.corpusBox.chiLam ℓ z = 0 from h]
  simp

/-- `winState ℓ ψ` is smooth for smooth `ψ`. -/
theorem contDiff_winState {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) : ContDiff ℝ (⊤ : ENat) (winState ℓ ψ) := by
  have hchi : ContDiff ℝ (⊤ : ENat) (Work.BoseK15.corpusBox.chiLam ℓ) := by
    have heq : Work.BoseK15.corpusBox.chiLam ℓ
        = fun x : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chi ((ℓ⁻¹ : ℝ) • x) := by
      funext x
      rw [Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi]
    rw [heq]
    exact (Submission.BoseGases.chi_contDiff).comp (contDiff_const_smul (ℓ⁻¹))
  have h2 : ContDiff ℝ (⊤ : ENat) (fun z : EuclideanSpace ℝ (Fin 3) =>
      ((ψ z - (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.acube ℓ, ψ x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hψ.sub contDiff_const)
  exact (Complex.ofRealCLM.contDiff.comp hchi).mul h2

theorem firstMoment_alias {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hψsupp : tsupport ψ ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    (2 : ℝ) * Work.BSKinetic.bsOneBody ℓ (fun r => r) 0 ψ ≤ 3 * firstMomentSum ℓ ψ := by
  rw [bsOneBody_sqrtKin_eq_kinFirst ℓ ψ, firstMomentSum_eq_latMoment hℓ hψ hψsupp]
  exact latMoment_deficit hℓ (contDiff_winState hℓ hψ) (tsupport_winState_subset hℓ ψ)

end

end Work.BoseBoxFock
