/-
Work.MRMT.Found — a continuous solution of the Beltrami equation with `O(1/‖z‖)` decay
vanishes, stated for *weak* (distributional) Wirtinger derivatives.

`Work.MRMT.Found.eq_zero_of_beltrami_pd`: if `h : ℂ → ℂ` is continuous, has weak Wirtinger
derivatives `p = ∂h`, `q = ∂̄h` (in the sense of `Work.MRMT.IsDzDeriv` / `Work.MRMT.IsDbarDeriv`,
both locally square integrable), satisfies `q = μ p` a.e. with `‖μ‖ ≤ k < 1` a.e., and decays
like `C/‖z‖` at infinity, then `h = 0`.

This is the version of the Liouville theorem for quasiregular maps that is stated purely in
terms of the weak derivatives — no a priori identification of `p`, `q` with the pointwise
Fréchet derivatives `dz h`, `dzbar h` is needed (and none is available in this vocabulary).

The proof is the `L²`-energy argument, carried out in the same way as
`Work.MRMT.Found.DecayAux` (which proves the analogous statement from `HasW12LocOn h Set.univ`),
avoiding any dependence on the mutually incompatible modules
`Work.MRMT.QC.principal_unique` / `Work.MRMT.QC.eq_zero_of_beltrami_of_decay`:

* cut `h` off by the smooth family `ψₙ` (`1` on `B(0,Rₙ)`, `Rₙ = n+1`, supported in
  `B(0,2Rₙ)`); the weak Leibniz rule
  (`isDzDeriv_mul_and_isDbarDeriv_mul_of_contDiff_infty`) gives the weak derivatives
  `pC h p n = ψₙ p + h ∂ψₙ`, `qC h q n = ψₙ q + h ∂̄ψₙ` of the compactly supported `ψₙ h`;
* the compactly supported energy identity `∫‖∂u‖² = ∫‖∂̄u‖²`, together with `q = μ p`, gives the
  a priori estimate `∫‖pC‖² ≤ (∫ eC²)/(1-k)²` (`Work.MRMT.QC.l2_bound_of_energy`) with error
  term `eC = ‖h‖(‖∂̄ψₙ‖ + k‖∂ψₙ‖)`, whose `L²` norm is `O(1/Rₙ)`;
* hence `∫_{B(0,Rₙ)} ‖p‖² = 0` for every `n`, so `p = 0` a.e., then `q = μ p = 0` a.e.;
* Weyl's lemma makes `h` entire, and Liouville plus the decay at infinity give `h = 0`.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.QC.isDzDeriv_mul_and_isDbarDeriv_mul
import Submission.Work.MRMT.Found.principalData_aux
import Submission.Work.MRMT.Found.DecayAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal ContDiff

noncomputable section

/-- A continuous function on `ℂ` is locally square integrable. -/
theorem memL2Loc_of_continuous_pd {f : ℂ → ℂ} (hf : Continuous f) : Work.MRMT.MemL2Loc f := by
  intro Kc hKc
  rw [Set.inter_univ]
  exact (hf.norm.pow 2).continuousOn.integrableOn_compact hKc

/-- **A continuous solution of the Beltrami equation with `O(1/‖z‖)` decay vanishes.**

Stated for the weak (distributional) Wirtinger derivatives `p = ∂h`, `q = ∂̄h`. -/
theorem eq_zero_of_beltrami_pd {h p q μ : ℂ → ℂ} {k : ℝ}
    (hhc : Continuous h) (hp : Work.MRMT.IsDzDeriv h p) (hq : Work.MRMT.IsDbarDeriv h q)
    (hpL : Work.MRMT.MemL2Loc p) (hqL : Work.MRMT.MemL2Loc q) (hk : k < 1)
    (hμ : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k)
    (hrel : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), q z = μ z * p z)
    (hdec : ∃ C R : ℝ, 0 ≤ C ∧ ∀ z : ℂ, R ≤ ‖z‖ → ‖h z‖ ≤ C / ‖z‖) :
    h = fun _ => 0 := by
  obtain ⟨C, R, hC0, hdecC⟩ := hdec
  have hk0 : 0 ≤ k := by
    obtain ⟨z, hz⟩ := hμ.exists
    exact le_trans (norm_nonneg _) hz
  obtain ⟨M, hM⟩ := Work.MRMT.QC.chiC_fderiv_bound
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hAESMh : AEStronglyMeasurable h (volume : Measure ℂ) := hhc.aestronglyMeasurable
  have hAESMp : AEStronglyMeasurable p (volume : Measure ℂ) := hp.2.1.aestronglyMeasurable
  have hAESMq : AEStronglyMeasurable q (volume : Measure ℂ) := hq.2.1.aestronglyMeasurable
  have hl : Work.MRMT.MemL2Loc h := memL2Loc_of_continuous_pd hhc
  have hstep : ∀ n : ℕ, ∫ z in Metric.ball 0 (Work.MRMT.QC.Rn n), ‖p z‖^2 ≤
      (∫ z, (Work.MRMT.QC.eC h k n z)^2) / (1 - k)^2 := by
    intro n
    obtain ⟨hpz, hpb⟩ := Work.MRMT.QC.isDzDeriv_mul_and_isDbarDeriv_mul_of_contDiff_infty
      (Work.MRMT.QC.psiC_contDiff n) (Work.MRMT.QC.psiC_cs n) hp hq
    have hpn : MemLp (Work.MRMT.QC.pC h p n) 2 (volume : Measure ℂ) :=
      Work.MRMT.QC.memLp_pC hAESMh hAESMp hpL hl hM
    have hqn : MemLp (Work.MRMT.QC.qC h q n) 2 (volume : Measure ℂ) :=
      Work.MRMT.QC.memLp_qC hAESMh hAESMq hqL hl hM
    have hen : MemLp (Work.MRMT.QC.eC h k n) 2 (volume : Measure ℂ) :=
      Work.MRMT.QC.memLp_eC hk0 hM0 hM hAESMh hl
    have henn : ∀ᵐ z ∂(volume : Measure ℂ), 0 ≤ Work.MRMT.QC.eC h k n z :=
      Eventually.of_forall (fun z => by unfold Work.MRMT.QC.eC; positivity)
    have hpint : Integrable (fun z => ‖Work.MRMT.QC.pC h p n z‖^2) (volume : Measure ℂ) :=
      (MeasureTheory.memLp_two_iff_integrable_sq_norm
        (Work.MRMT.QC.aesm_pC hAESMh hAESMp)).mp hpn
    have hbd : ∀ᵐ z ∂(volume : Measure ℂ),
        ‖Work.MRMT.QC.qC h q n z‖ ≤ k * ‖Work.MRMT.QC.pC h p n z‖ +
          Work.MRMT.QC.eC h k n z := by
      filter_upwards [hrel, hμ] with z h1 h2
      have h3 : Work.MRMT.QC.qC h q n z = μ z * Work.MRMT.QC.pC h p n z +
          h z * (Work.MRMT.dzbar (Work.MRMT.QC.psiC n) z -
            μ z * Work.MRMT.dz (Work.MRMT.QC.psiC n) z) := by
        unfold Work.MRMT.QC.qC Work.MRMT.QC.pC
        rw [h1]
        ring
      rw [h3]
      have h4 : ‖Work.MRMT.dzbar (Work.MRMT.QC.psiC n) z -
            μ z * Work.MRMT.dz (Work.MRMT.QC.psiC n) z‖
          ≤ ‖Work.MRMT.dzbar (Work.MRMT.QC.psiC n) z‖ +
            k * ‖Work.MRMT.dz (Work.MRMT.QC.psiC n) z‖ := by
        calc ‖Work.MRMT.dzbar (Work.MRMT.QC.psiC n) z -
              μ z * Work.MRMT.dz (Work.MRMT.QC.psiC n) z‖
            ≤ ‖Work.MRMT.dzbar (Work.MRMT.QC.psiC n) z‖ +
              ‖μ z * Work.MRMT.dz (Work.MRMT.QC.psiC n) z‖ := norm_sub_le _ _
          _ = ‖Work.MRMT.dzbar (Work.MRMT.QC.psiC n) z‖ +
              ‖μ z‖ * ‖Work.MRMT.dz (Work.MRMT.QC.psiC n) z‖ := by rw [norm_mul]
          _ ≤ ‖Work.MRMT.dzbar (Work.MRMT.QC.psiC n) z‖ +
              k * ‖Work.MRMT.dz (Work.MRMT.QC.psiC n) z‖ :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
      calc ‖μ z * Work.MRMT.QC.pC h p n z +
              h z * (Work.MRMT.dzbar (Work.MRMT.QC.psiC n) z -
                μ z * Work.MRMT.dz (Work.MRMT.QC.psiC n) z)‖
          ≤ ‖μ z * Work.MRMT.QC.pC h p n z‖
              + ‖h z * (Work.MRMT.dzbar (Work.MRMT.QC.psiC n) z -
                μ z * Work.MRMT.dz (Work.MRMT.QC.psiC n) z)‖ :=
            norm_add_le _ _
        _ = ‖μ z‖ * ‖Work.MRMT.QC.pC h p n z‖
              + ‖h z‖ * ‖Work.MRMT.dzbar (Work.MRMT.QC.psiC n) z -
                μ z * Work.MRMT.dz (Work.MRMT.QC.psiC n) z‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ k * ‖Work.MRMT.QC.pC h p n z‖ + ‖h z‖ *
              (‖Work.MRMT.dzbar (Work.MRMT.QC.psiC n) z‖ +
                k * ‖Work.MRMT.dz (Work.MRMT.QC.psiC n) z‖) :=
            add_le_add (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
              (mul_le_mul_of_nonneg_left h4 (norm_nonneg _))
        _ = k * ‖Work.MRMT.QC.pC h p n z‖ + Work.MRMT.QC.eC h k n z := rfl
    have henergy : ∫ z, ‖Work.MRMT.QC.pC h p n z‖^2 =
        ∫ z, ‖Work.MRMT.QC.qC h q n z‖^2 :=
      Work.MRMT.QC.integral_norm_dz_eq_integral_norm_dzbar
        (hus := (Work.MRMT.QC.psiC_cs n).mul_right (f' := h)) hpz hpb hpn hqn
    have hbound := Work.MRMT.QC.l2_bound_of_energy hk0 hk hpn hqn hen henn henergy hbd
    calc ∫ z in Metric.ball 0 (Work.MRMT.QC.Rn n), ‖p z‖^2
        = ∫ z in Metric.ball 0 (Work.MRMT.QC.Rn n), ‖Work.MRMT.QC.pC h p n z‖^2 := by
          refine setIntegral_congr_fun measurableSet_ball (fun z hz => ?_)
          rw [Metric.mem_ball, dist_zero_right] at hz
          unfold Work.MRMT.QC.pC
          rw [Work.MRMT.QC.psiC_one n z (le_of_lt hz), Work.MRMT.QC.psiC_dz_zero n z hz]
          simp
      _ ≤ ∫ z, ‖Work.MRMT.QC.pC h p n z‖^2 :=
          setIntegral_le_integral hpint (Eventually.of_forall fun z => sq_nonneg _)
      _ ≤ (∫ z, (Work.MRMT.QC.eC h k n z)^2) / (1 - k)^2 := hbound
  have hest : Tendsto (fun n : ℕ => (∫ z, (Work.MRMT.QC.eC h k n z)^2)) atTop (𝓝 0) :=
    Work.MRMT.QC.tendsto_integral_eC_sq hhc hk0 hC0 hdecC
  have hlim : ∀ m : ℕ, ∫ z in Metric.ball 0 (Work.MRMT.QC.Rn m), ‖p z‖^2 ≤ 0 := by
    intro m
    have h1 : Tendsto (fun n : ℕ => (∫ z, (Work.MRMT.QC.eC h k n z)^2) / (1 - k)^2)
        atTop (𝓝 0) := by
      simpa using hest.div_const ((1 - k)^2)
    refine ge_of_tendsto h1 ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    calc ∫ z in Metric.ball 0 (Work.MRMT.QC.Rn m), ‖p z‖^2
        ≤ ∫ z in Metric.ball 0 (Work.MRMT.QC.Rn n), ‖p z‖^2 := by
          refine setIntegral_mono_set
            ((Work.MRMT.QC.memL2Loc_integrableOn hpL
              (isCompact_closedBall 0 (Work.MRMT.QC.Rn n))).mono_set
                Metric.ball_subset_closedBall)
            (Eventually.of_forall fun z => sq_nonneg _)
            (Eventually.of_forall fun z hz => ?_)
          simp only [Metric.mem_ball, dist_zero_right] at hz ⊢
          have h2 : Work.MRMT.QC.Rn m ≤ Work.MRMT.QC.Rn n := by
            have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
            unfold Work.MRMT.QC.Rn; linarith
          linarith
      _ ≤ (∫ z, (Work.MRMT.QC.eC h k n z)^2) / (1 - k)^2 := hstep n
  have hp_ae : p =ᵐ[(volume : Measure ℂ)] (fun _ => (0 : ℂ)) := by
    have hnull : ∀ m : ℕ,
        (volume : Measure ℂ) (Metric.ball 0 (Work.MRMT.QC.Rn m) ∩ {z : ℂ | p z ≠ 0}) = 0 := by
      intro m
      have h1 : ∫ z in Metric.ball 0 (Work.MRMT.QC.Rn m), ‖p z‖^2 = 0 :=
        le_antisymm (hlim m) (integral_nonneg fun z => sq_nonneg _)
      have h2 : IntegrableOn (fun z => ‖p z‖^2) (Metric.ball 0 (Work.MRMT.QC.Rn m))
          (volume : Measure ℂ) :=
        (Work.MRMT.QC.memL2Loc_integrableOn hpL
          (isCompact_closedBall 0 (Work.MRMT.QC.Rn m))).mono_set Metric.ball_subset_closedBall
      have h3 := (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall fun z => sq_nonneg _) h2).mp h1
      have h5 := (MeasureTheory.ae_iff
        (p := fun z => z ∈ Metric.ball 0 (Work.MRMT.QC.Rn m) → ‖p z‖^2 = 0)
        (μ := (volume : Measure ℂ))).mp
        ((MeasureTheory.ae_restrict_iff' measurableSet_ball).mp h3)
      have hset : Metric.ball 0 (Work.MRMT.QC.Rn m) ∩ {z : ℂ | p z ≠ 0}
          = {z : ℂ | ¬ (z ∈ Metric.ball 0 (Work.MRMT.QC.Rn m) → ‖p z‖^2 = 0)} := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, not_imp]
        constructor
        · rintro ⟨hz, hz'⟩
          exact ⟨hz, fun h0 => hz' (by simpa [pow_two, mul_self_eq_zero, norm_eq_zero] using h0)⟩
        · rintro ⟨hz, hz'⟩
          exact ⟨hz, fun h0 => hz' (by rw [h0]; simp)⟩
      rw [hset]; exact h5
    change ∀ᵐ z ∂(volume : Measure ℂ), p z = 0
    rw [MeasureTheory.ae_iff]
    have hcover : {z : ℂ | ¬ p z = 0}
        = ⋃ m, (Metric.ball 0 (Work.MRMT.QC.Rn m) ∩ {z : ℂ | p z ≠ 0}) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hz
        obtain ⟨m, hm⟩ := exists_nat_gt ‖z‖
        refine ⟨m, ?_, hz⟩
        rw [Metric.mem_ball, dist_zero_right]
        have h2 : (m : ℝ) ≤ Work.MRMT.QC.Rn m := by
          unfold Work.MRMT.QC.Rn; push_cast; linarith
        linarith
      · rintro ⟨m, _, hz⟩; exact hz
    rw [hcover]
    exact MeasureTheory.measure_iUnion_null hnull
  have hq_ae0 : q =ᵐ[(volume : Measure ℂ)] (fun _ => (0 : ℂ)) := by
    filter_upwards [hrel, hp_ae] with z h1 h2
    rw [h2] at h1
    simpa using h1
  have hdb0 : Work.MRMT.IsDbarDeriv h (fun _ => 0) := by
    refine ⟨hq.1, MeasureTheory.locallyIntegrable_zero, fun φ => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hq.2.2 φ
    refine ⟨h1, by simp, ?_⟩
    have h4 : ∫ z, q z * (φ : ℂ → ℂ) z = 0 := by
      have he : (fun z => q z * (φ : ℂ → ℂ) z)
          =ᵐ[(volume : Measure ℂ)] (fun _ => (0 : ℂ)) := by
        filter_upwards [hq_ae0] with z hz
        rw [hz]; simp
      rw [integral_congr_ae he]; simp
    rw [h3, h4]; simp
  have hdbOn : Work.MRMT.IsDbarDerivOn h (fun _ => 0) Set.univ := by
    obtain ⟨a, b, c⟩ := hdb0
    refine ⟨?_, ?_, fun φ _ => c φ⟩
    · exact (MeasureTheory.locallyIntegrableOn_univ).mpr a
    · exact MeasureTheory.locallyIntegrable_zero.locallyIntegrableOn Set.univ
  have hdiff : Differentiable ℂ h := by
    have := Work.MRMT.QC.differentiableOn_of_isDbarDerivOn_zero isOpen_univ
      hhc.continuousOn hdbOn
    rwa [differentiableOn_univ] at this
  have htend : Tendsto h (cocompact ℂ) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [Filter.hasBasis_cocompact.eventually_iff]
    refine ⟨Metric.closedBall 0 (max R (C / ε) + 1), isCompact_closedBall _ _, ?_⟩
    intro z hz
    have hz_gt : max R (C / ε) + 1 < ‖z‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    have hzpos : 0 < ‖z‖ := by
      linarith [hε, div_nonneg hC0 hε.le, le_max_right R (C / ε)]
    rw [dist_zero_right]
    calc ‖h z‖ ≤ C / ‖z‖ := hdecC z (by linarith [le_max_left R (C / ε)])
      _ < ε := by
          rw [div_lt_iff₀ hzpos]
          have := (div_lt_iff₀ hε).mp (by linarith [le_max_right R (C / ε)] :
            C / ε < ‖z‖)
          linarith
  exact funext fun z => hdiff.apply_eq_of_tendsto_cocompact z htend

end

end Work.MRMT.Found
