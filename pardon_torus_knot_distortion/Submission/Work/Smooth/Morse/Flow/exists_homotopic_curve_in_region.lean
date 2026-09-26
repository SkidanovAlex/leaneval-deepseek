import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Flow.exists_descentRate_lower_bound_of_regularValue
import Submission.Work.Smooth.Morse.Flow.pullback_flow_descends_of_eta
import Submission.Work.Smooth.Morse.Flow.exists_localFlow_of_lipschitz
import Submission.Work.Smooth.Morse.Flow.flow_equivariant_of_periodic
import Submission.Work.Smooth.Morse.Flow.lipschitzWith_descentField
import Submission.Work.Smooth.Morse.Flow.norm_descentField_le_one
import Submission.Work.Smooth.Morse.Flow.flow_equivariant_of_periodic_on_ball
import Submission.Work.Smooth.Morse.Flow.pullback_flow_descends_of_eta_at
import Submission.Work.Smooth.Morse.Flow.exists_continuous_addCircle_lift
import Submission.Work.TorusCover.ParamTorus_exists_liftOf
import Submission.Work.CoreTopology.Disk

/-!
# Homotoping a curve of the surface into a lower sublevel region

`Work.Smooth.Morse.Flow.exists_homotopic_curve_in_region`: if `[a,b]` contains no critical value of
`g|_F` (`F = torus ψ`), then every closed curve `γ` of `F` lying in the sublevel region
`region ψ g b = F ∩ {g < b}` can be homotoped inside `F` to a closed curve `γ'` lying in the
smaller region `region ψ g a = F ∩ {g < a}`.

## The construction

The descent field `Work.Smooth.Morse.descentField ψ g` lowers the level of `pullback ψ g` at the
positive rate `descentRate ψ g` (`Work.Smooth.Morse.fderiv_pullback_descentField`), and on the
critical-free band `[a-η, b]` this rate is bounded below by a positive constant `δ` for a suitable
`η > 0` (`Work.Smooth.Morse.Flow.exists_descentRate_lower_bound_of_regularValue`).  The field is
Lipschitz, bounded by one and `2π`-biperiodic
(`Work.Smooth.Morse.Flow.lipschitzWith_descentField`), so it admits a local flow on every ball
(`Work.Smooth.Morse.Flow.exists_localFlow_of_lipschitz`).

* We lift `γ` to the parameter plane (`Work.TorusCover.ParamTorus_exists_liftOf`); the lift of
  `[0,2π]` is bounded, so it lies in a ball `closedBall 0 R`.
* On that ball we take the flow `Φ` of the descent field and the time
  `T = (b - a + η)/δ`; by `Work.Smooth.Morse.Flow.pullback_flow_descends_of_eta_at` every point
  whose level is below `b` is pushed below `a` in time `T`.
* The equivariance of the flow under the period lattice
  (`Work.Smooth.Morse.Flow.flow_equivariant_of_periodic_on_ball`, restricted to the ball) shows that
  the transport of the two parameters `L 0` and `L 2π` (which differ by the winding vector) gives
  the same point of `F`, so the transported family is `2π`-periodic in the curve parameter.
* `Work.Smooth.Morse.Flow.exists_continuous_addCircle_lift` then descends the transported family on
  `[0,2π] × [0,1]` to a continuous `2π`-periodic family `H : ℝ → ℝ → F`, i.e. to the required
  homotopy, whose time-one trace is `γ'`. -/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped NNReal

namespace Work.Smooth.Morse.Flow

/-- **A curve of the region `{g < b}` is homotopic to a curve of the region `{g < a}`** whenever
`[a,b]` contains no critical value of `g|_F`: run the normalised gradient flow of `g|_F` for
time `(b - a + η)/δ`, which lowers every level below `b` to a level below `a`. -/
theorem exists_homotopic_curve_in_region (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hg : ContDiff ℝ 2 g) {a b : ℝ} (hab : a ≤ b) (hreg : ∀ t ∈ Set.Icc a b, Work.Smooth.Morse.IsRegularValue ψ g t) (γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)) (hγ : ∀ t : ℝ, γ t ∈ Work.Smooth.Morse.region ψ g b) : ∃ γ' : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ), (∀ t : ℝ, γ' t ∈ Work.Smooth.Morse.region ψ g a) ∧ Work.CoreTopology.Homotopic (Work.Smooth.Morse.torus ψ) γ γ' := by
  have hinst2pi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  obtain ⟨δ, hδpos, η, hηpos, hrate⟩ :=
    exists_descentRate_lower_bound_of_regularValue ψ hg1 hab hreg
  obtain ⟨K, hK, hKbd, hKper⟩ := lipschitzWith_descentField ψ hg
  set T : ℝ := (b - a + η) / δ with hTdef
  have hTpos : 0 < T := by rw [hTdef]; positivity
  have hT0 : 0 ≤ T := hTpos.le
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf (Work.Smooth.Morse.torus ψ) γ
  have hcontL : Continuous fun t : ℝ => (L.Θ t, L.Φ t) := L.contΘ.prodMk L.contΦ
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
    hcontL.continuousOn
  set R : ℝ := max C 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hLmem : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), (L.Θ t, L.Φ t) ∈ Metric.closedBall (0 : ℝ × ℝ) R := by
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans (hC t ht) (le_max_left _ _)
  obtain ⟨Φ, hΦ0, hΦderiv, hΦcont⟩ :=
    exists_localFlow_of_lipschitz (Work.Smooth.Morse.descentField ψ g) hK hKbd (0 : ℝ × ℝ)
      (R := R) (T := T) hR0 hT0
  have h01 : (0:ℝ) ≤ 1 := zero_le_one
  let σ : ℝ → ℝ := fun s => T * (Set.projIcc 0 1 h01 s : ℝ)
  have hσmem : ∀ s : ℝ, σ s ∈ Set.Icc 0 T := by
    intro s
    refine ⟨mul_nonneg hT0 (Set.projIcc 0 1 h01 s).2.1, ?_⟩
    calc σ s = T * (Set.projIcc 0 1 h01 s : ℝ) := rfl
      _ ≤ T * 1 := by gcongr; exact (Set.projIcc 0 1 h01 s).2.2
      _ = T := mul_one T
  have hσ0 : σ 0 = 0 := by
    simp only [σ]
    rw [Set.projIcc_of_mem h01 (by norm_num : (0:ℝ) ∈ Set.Icc 0 1)]
    exact mul_zero T
  have hσ1 : σ 1 = T := by
    simp only [σ]
    rw [Set.projIcc_of_mem h01 (by norm_num : (1:ℝ) ∈ Set.Icc 0 1)]
    exact mul_one T
  let Lp : ℝ → ℝ × ℝ := fun u => (L.Θ u, L.Φ u)
  have hLpc : Continuous Lp := hcontL
  let F : ℝ → ℝ → LeanEval.KnotTheory.PardonDistortion.R3 :=
    fun s u => Work.Smooth.Morse.param ψ (Φ (σ s, Lp u))
  have hσc : Continuous σ := continuous_const.mul (continuous_subtype_val.comp continuous_projIcc)
  have hFcont : ContinuousOn (Function.uncurry F) (Set.univ ×ˢ Set.Icc 0 (2 * Real.pi)) := by
    have hinner : ContinuousOn (fun p : ℝ × ℝ => (σ p.1, Lp p.2))
        (Set.univ ×ˢ Set.Icc 0 (2 * Real.pi)) :=
      ((hσc.comp continuous_fst).prodMk (hLpc.comp continuous_snd)).continuousOn
    have hcomp : ContinuousOn (fun p : ℝ × ℝ => Φ (σ p.1, Lp p.2))
        (Set.univ ×ˢ Set.Icc 0 (2 * Real.pi)) :=
      hΦcont.comp hinner (fun p hp => ⟨hσmem p.1, hLmem p.2 hp.2⟩)
    have hpar : ContinuousOn (fun p : ℝ × ℝ => Work.Smooth.Morse.param ψ (Φ (σ p.1, Lp p.2)))
        (Set.univ ×ˢ Set.Icc 0 (2 * Real.pi)) :=
      (Work.Smooth.Morse.param_continuous ψ).continuousOn.comp hcomp
        (fun _ _ => Set.mem_univ _)
    apply hpar.congr
    intro p hp
    rfl
  have hperF : ∀ s : ℝ, F s (2 * Real.pi) = F s 0 := by
    intro s
    have hwspec := L.period_shift_winding 0
    have h1 : (Lp 0).1 + ((L.winding).1 : ℝ) * (2 * Real.pi) = (Lp (2 * Real.pi)).1 := by
      have h := hwspec.1
      simp only [zero_add] at h
      exact h.symm
    have h2 : (Lp 0).2 + ((L.winding).2 : ℝ) * (2 * Real.pi) = (Lp (2 * Real.pi)).2 := by
      have h := hwspec.2
      simp only [zero_add] at h
      exact h.symm
    have hq0 : Lp 0 ∈ Metric.closedBall (0 : ℝ × ℝ) R :=
      hLmem 0 ⟨le_rfl, by positivity⟩
    have hq2 : ((Lp 0).1 + ((L.winding).1 : ℝ) * (2 * Real.pi),
        (Lp 0).2 + ((L.winding).2 : ℝ) * (2 * Real.pi)) ∈ Metric.closedBall (0 : ℝ × ℝ) R := by
      rw [h1, h2]
      exact hLmem (2 * Real.pi) ⟨by positivity, le_rfl⟩
    have heq := flow_equivariant_of_periodic_on_ball (Work.Smooth.Morse.descentField ψ g) hK hKper Φ hΦ0 hΦderiv
      hq0 hq2 (u := σ s) (hσmem s)
    have hs : Φ (σ s, Lp (2 * Real.pi)) =
        ((Φ (σ s, Lp 0)).1 + ((L.winding).1 : ℝ) * (2 * Real.pi),
          (Φ (σ s, Lp 0)).2 + ((L.winding).2 : ℝ) * (2 * Real.pi)) := by
      simpa only [h1, h2] using heq
    show Work.Smooth.Morse.param ψ (Φ (σ s, Lp (2 * Real.pi))) =
      Work.Smooth.Morse.param ψ (Φ (σ s, Lp 0))
    rw [hs]
    exact ((Work.Smooth.Morse.torus ψ).psi_eq_iff _ _ _ _).mpr
      ⟨⟨(L.winding).1, by ring⟩, ⟨(L.winding).2, by ring⟩⟩
  obtain ⟨G, hGcont, hGapply⟩ := exists_continuous_addCircle_lift F hFcont hperF
  let H : ℝ → ℝ → LeanEval.KnotTheory.PardonDistortion.R3 :=
    fun s t => G (s, (t : AddCircle (2 * Real.pi)))
  have hHcont : Continuous (Function.uncurry H) := by
    have hcoe : Continuous fun t : ℝ => (t : AddCircle (2 * Real.pi)) := continuous_quotient_mk'
    have hc : Continuous (fun p : ℝ × ℝ => G (p.1, (p.2 : AddCircle (2 * Real.pi)))) :=
      hGcont.comp (continuous_fst.prodMk (hcoe.comp continuous_snd))
    apply hc.congr
    intro p
    rfl
  have hHper : ∀ s t : ℝ, H s (t + 2 * Real.pi) = H s t := by
    intro s t
    show G (s, ((t + 2 * Real.pi : ℝ) : AddCircle (2 * Real.pi))) = G (s, (t : AddCircle (2 * Real.pi)))
    rw [AddCircle.coe_add_period]
  let uI : ℝ → Set.Ico (0:ℝ) (0 + 2 * Real.pi) :=
    fun t => AddCircle.equivIco (2 * Real.pi) (0:ℝ) (t : AddCircle (2 * Real.pi))
  let ρ : ℝ → ℝ := fun t => (uI t : ℝ)
  have hρ_mem : ∀ t, ρ t ∈ Set.Ico (0:ℝ) (2 * Real.pi) := by
    intro t
    simpa only [ρ, zero_add] using (uI t).2
  have hρ_coe : ∀ t, ((ρ t : ℝ) : AddCircle (2 * Real.pi)) = (t : AddCircle (2 * Real.pi)) := by
    intro t
    exact AddCircle.coe_equivIco (p := 2 * Real.pi) (a := (0:ℝ))
      (y := (t : AddCircle (2 * Real.pi)))
  have hHapply : ∀ s t : ℝ, H s t = F s (ρ t) := by
    intro s t
    have hmem : ρ t ∈ Set.Icc (0:ℝ) (2 * Real.pi) := ⟨(hρ_mem t).1, (hρ_mem t).2.le⟩
    have h := hGapply s (ρ t) hmem
    show G (s, (t : AddCircle (2 * Real.pi))) = F s (ρ t)
    rw [← hρ_coe t]
    exact h
  have hρIcc : ∀ t, ρ t ∈ Set.Icc (0:ℝ) (2 * Real.pi) := fun t => ⟨(hρ_mem t).1, (hρ_mem t).2.le⟩
  have hLpmem : ∀ t, Lp (ρ t) ∈ Metric.closedBall (0 : ℝ × ℝ) R := fun t => hLmem (ρ t) (hρIcc t)
  have hlift : ∀ t, Work.Smooth.Morse.param ψ (Lp (ρ t)) = γ (ρ t) := by
    intro t
    show (Work.Smooth.Morse.torus ψ).psi (L.Θ (ρ t)) (L.Φ (ρ t)) = γ.γ (ρ t)
    exact L.lifts (ρ t)
  have hγu : ∀ t, γ (ρ t) = γ t := by
    intro t
    have hper : Function.Periodic γ.γ (2 * Real.pi) := γ.periodic
    rw [← hper.lift_coe (ρ t), ← hper.lift_coe t, hρ_coe t]
  have hH0 : ∀ t : ℝ, H 0 t = γ t := by
    intro t
    rw [hHapply 0 t]
    have hΦ0' := hΦ0 (Lp (ρ t)) (hLpmem t)
    show Work.Smooth.Morse.param ψ (Φ (σ 0, Lp (ρ t))) = γ t
    rw [hσ0, hΦ0', hlift t, hγu t]
  have hH1 : ∀ t : ℝ, H 1 t = Work.Smooth.Morse.param ψ (Φ (T, Lp (ρ t))) := by
    intro t
    rw [hHapply 1 t]
    show Work.Smooth.Morse.param ψ (Φ (σ 1, Lp (ρ t))) = Work.Smooth.Morse.param ψ (Φ (T, Lp (ρ t)))
    rw [hσ1]
  let γ' : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ) :=
    { γ := fun t => H 1 t
      cont := by
        have h := hHcont.comp
          ((continuous_const : Continuous fun _ : ℝ => (1:ℝ)).prodMk continuous_id)
        apply h.congr
        intro t
        rfl
      periodic := fun t => hHper 1 t
      mem := fun t => by
        rw [hH1 t]
        exact Work.Smooth.Morse.param_mem ψ _ }
  have hγ'a : ∀ t : ℝ, γ' t ∈ Work.Smooth.Morse.region ψ g a := by
    intro t
    have hdescent : Work.Smooth.Morse.pullback ψ g (Φ (T, Lp (ρ t))) < a := by
      have h0' : (fun u q => Φ (u, q)) 0 (Lp (ρ t)) = Lp (ρ t) := hΦ0 _ (hLpmem t)
      have hflow' : ∀ τ ∈ Set.Icc 0 T, HasDerivWithinAt (fun s : ℝ => Φ (s, Lp (ρ t)))
          (Work.Smooth.Morse.descentField ψ g (Φ (τ, Lp (ρ t)))) (Set.Icc 0 T) τ :=
        fun τ hτ => hΦderiv _ (hLpmem t) τ hτ
      have hrate' : ∀ τ ∈ Set.Icc 0 T,
          Work.Smooth.Morse.pullback ψ g (Φ (τ, Lp (ρ t))) ∈ Set.Icc (a - η) b →
            δ ≤ Work.Smooth.Morse.descentRate ψ g (Φ (τ, Lp (ρ t))) :=
        fun τ hτ hmem => hrate _ hmem
      have hq' : Work.Smooth.Morse.pullback ψ g (Lp (ρ t)) < b := by
        show g (Work.Smooth.Morse.param ψ (Lp (ρ t))) < b
        rw [hlift t, hγu t]
        exact (hγ t).2
      exact pullback_flow_descends_of_eta_at (Φ := fun u q => Φ (u, q)) (T := T) (a := a) (b := b) (δ := δ)
        (η := η) (q := Lp (ρ t)) ψ hg1 hδpos hηpos hT0 (le_of_eq hTdef.symm) h0' hflow' hrate' hq'
    show H 1 t ∈ Work.Smooth.Morse.region ψ g a
    refine ⟨?_, ?_⟩
    · rw [hH1 t]; exact Work.Smooth.Morse.param_mem ψ _
    · rw [hH1 t]; exact hdescent
  refine ⟨γ', hγ'a, ?_⟩
  exact ⟨H, hHcont, (fun s t => by rw [hHapply s t]; exact Work.Smooth.Morse.param_mem ψ _),
    hH0, (fun t => rfl), hHper⟩

end Work.Smooth.Morse.Flow
