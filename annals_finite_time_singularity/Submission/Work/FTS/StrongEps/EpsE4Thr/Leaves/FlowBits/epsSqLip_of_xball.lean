/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FlowBits/epsSqLip_of_xball.lean` — the `EpsSq`-Lipschitz property of the fake-time curve

LEAF of the `FlowBits` node (the `X`-ball producer `EpsFlowP α ρ ε δ Φs E g`): for a regular
`P₀`-solution `g` (`IsEpsSolP` + `EpsRegP`) whose slices all lie in the fixed `X`-ball
`XBall α ρ ε R C₁` on the horizon `[0,δ]`, the fake-time curve `s ↦ slice g s` is Lipschitz in the
weighted `L²`-size `EpsSq`:

  `∃ Lw > 0, ∀ s t ∈ Icc 0 δ, EpsSq α (slice g s − slice g t) ≤ Lw (s − t)²`.

## Route

1. **The right-hand side is bounded in `X` on the ball.**  `ConjOneSq`
   (`EpsLocalPStar/EpsRHSPLipX_Sq.lean`) gives `L > 0` with
   `EpsMem α (Feps … u) ∧ EpsSq α (Feps … u) ≤ L` at every profile `u` of the ball
   `SmoothOpen u ∧ EpsMem α u ∧ EpsSq α u ≤ R ∧ ClassC α (Wp ρ ε u) ∧ Xn α (Wp ρ ε u) ≤ C₁ α²`
   (`Wp ρ ε u = Pz (J_ε u)`, so the `XBall` fields apply verbatim; `Feps u = epsRHPSlice … 0 u`
   is `Feps_eq_epsRHPSlice`).
2. **The single-solution Volterra identity** (`volterra_interval_of_regP`): for
   `s ≤ t` in `[0,δ]` and `(z,θ)` in the open quadrant,
   `g z θ t − g z θ s = ∫_s^t Feps (slice g σ) z θ dσ`.  The integrand is `epsRHSP … g σ`
   (`epsRHSP_eq_Feps_slice`) and it is continuous on `Icc 0 δ` by
   `IsEpsSolPQ.continuousOn_derivWithin_curve` (the joint `C¹`-clause of `EpsRegP` makes the
   fake-time derivative continuous on the *closed* horizon), after which the fundamental theorem
   of calculus (`integral_eq_sub_of_hasDerivAt_of_le`) applies.
3. **Minkowski for the interval integral** (`EpsEngine.EpsSq_intervalIntegral_le_gen`): the
   weighted difference curve is a.e. strongly measurable for `(vol↾uIoc a b) ⊗ DomM`
   (`aesm_of_continuousOn_box`: on the open box `Ioo a b × Quad` it agrees with the *jointly
   continuous* `(τ,z,θ) ↦ epsRHSP … g τ z θ · epsW α z θ`, `continuousOn_epsRHSP_joint_Ioo` +
   `continuousOn_epsW`, and that box carries the whole restricted product measure), while the
   a.e. bound `epsL2 α (Feps (slice g σ)) ≤ ofReal L` is step 1 (`epsL2_le_ofReal_of_mem`).
   Hence `EpsSq α (∫_s^t Feps (slice g ·)) ≤ (t−s)((t−s)L)`.
4. **Transport to the slices**: on the open quadrant the difference of the slices *is* minus the
   interval integral (step 2), and the open quadrant is conull for `DomM` (`ae_open_DomM`), so
   `EpsSq_congr_ae` + `EpsSq_sub_comm` (`EpsSq_neg2`) identify the two sizes, and
   `(t−s)((t−s)L) = L (s−t)²`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.StrongEps.EpsE4Thr.XStep
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPLipX_Sq
import Submission.Work.FTS.EpsEngine.EpsSq_intervalIntegral_le_gen
import Submission.Work.FTS.EpsEngine.IterContMeas
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.WeakRHS
import Submission.Work.FTS.StrongEps.RhsCont
import Submission.Work.FTS.StrongEps.IsEpsSolPQ.epsSolP_volterra
import Submission.Work.FTS.EpsEngine.aesm_weighted_prod_restricted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

/-! ## The open box carries the whole restricted product measure -/

/-- **Almost every point of `(vol↾uIoc a b) ⊗ DomM` lies in the open box
`Ioo a b × Quad`**: the time coordinate misses `{a,b}` (a null set for Lebesgue) and the profile
coordinate misses the boundary of the quadrant (`ae_open_DomM`). -/
private lemma ae_mem_box_uIoc {a b : ℝ} (hab : a ≤ b) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM),
      p.1 ∈ Set.Ioo a b ∧ p.2 ∈ Work.FTS.StrongEps.Quad := by
  have hIoc : Set.Ioc a b =ᵐ[(MeasureTheory.volume : Measure ℝ)] Set.Ioo a b :=
    (MeasureTheory.Ioc_ae_eq_Icc).trans (MeasureTheory.Ioo_ae_eq_Icc).symm
  have h1 : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.uIoc a b)), x ∈ Set.Ioo a b := by
    rw [Set.uIoc_of_le hab, MeasureTheory.Measure.restrict_congr_set hIoc]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have h2 : ∀ᵐ y ∂Work.FTS.StrongEps.EpsLocalPStar.DomM, y ∈ Work.FTS.StrongEps.Quad := by
    filter_upwards [Work.FTS.StrongEps.EpsLocalPStar.ae_open_DomM] with y hy
    exact hy
  rw [Measure.ae_prod_iff_ae_ae]
  · filter_upwards [h1] with x hx
    filter_upwards [h2] with y hy
    exact ⟨hx, hy⟩
  · exact (measurableSet_Ioo.preimage measurable_fst).inter
      ((isOpen_Ioi.prod isOpen_Ioo).measurableSet.preimage measurable_snd)

/-- **A function continuous on the open box `Ioo a b × Quad` is a.e. strongly measurable for the
restricted product measure `(vol↾uIoc a b) ⊗ DomM`.** -/
private lemma aesm_of_continuousOn_box {a b : ℝ} (hab : a ≤ b) {f : ℝ × ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo a b ×ˢ Work.FTS.StrongEps.Quad)) :
    MeasureTheory.AEStronglyMeasurable f
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM) := by
  have hU : MeasurableSet (Set.Ioo a b ×ˢ Work.FTS.StrongEps.Quad) :=
    (isOpen_Ioo.prod (isOpen_Ioi.prod isOpen_Ioo)).measurableSet
  have hμ : (((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
      Work.FTS.StrongEps.EpsLocalPStar.DomM).restrict (Set.Ioo a b ×ˢ Work.FTS.StrongEps.Quad))
      = ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM) :=
    Measure.restrict_eq_self_of_ae_mem (ae_mem_box_uIoc hab)
  rw [← hμ]
  exact hf.aestronglyMeasurable hU

/-! ## The single-solution Volterra identity on a subinterval -/

/-- **The fake-time fundamental theorem of calculus for a regular `P₀`-solution**, on a general
subinterval `[s,t] ⊆ [0,δ]` of the horizon: on the open quadrant the increment of the family is
the interval integral of the (τ-free) right-hand side `Feps` along the curve of slices. -/
private lemma volterra_interval_of_regP {α ε δ : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam}
    (hδ : 0 < δ) (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε δ Φs E g₀ g)
    (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε δ g) :
    ∀ z θ s t : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → s ∈ Set.Icc 0 δ → t ∈ Set.Icc 0 δ →
      s ≤ t → g z θ t - g z θ s
        = ∫ σ in s..t, Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ) z θ := by
  intro z θ s t hz hθ hs ht hst
  have hder : ∀ σ ∈ Set.Icc 0 δ,
      HasDerivWithinAt (fun s' : ℝ => g z θ s')
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ) z θ) (Set.Icc 0 δ) σ := by
    intro σ hσ
    have h := hsol.2 z θ σ hz hθ hσ
    rwa [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E] at h
  have hcontG : ContinuousOn (fun σ : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ) z θ)
      (Set.Icc 0 δ) :=
    Work.FTS.StrongEps.IsEpsSolPQ.continuousOn_derivWithin_curve
      (f := fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (v := fun σ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ) z θ) hδ hz hθ hreg.1 hder
  have hsub : Set.Icc s t ⊆ Set.Icc 0 δ := fun x hx => ⟨le_trans hs.1 hx.1, le_trans hx.2 ht.2⟩
  have hcontf : ContinuousOn (fun σ : ℝ => g z θ σ) (Set.Icc s t) := by
    have hcurve : ContinuousOn (fun σ : ℝ => (z, (θ, σ))) (Set.Icc s t) := by fun_prop
    have hmap : Set.MapsTo (fun σ : ℝ => (z, (θ, σ))) (Set.Icc s t)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ) :=
      fun σ hσ => ⟨hz, hθ, hsub hσ⟩
    exact (hreg.1.continuousOn.comp hcurve hmap).congr (fun σ _ => rfl)
  have hint : IntervalIntegrable
      (fun σ : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ) z θ) volume s t :=
    ContinuousOn.intervalIntegrable_of_Icc hst (hcontG.mono hsub)
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hcontf ?_ hint).symm
  intro x hx
  have hx0 : 0 < x := lt_of_le_of_lt hs.1 hx.1
  have hxδ : x < δ := lt_of_lt_of_le hx.2 ht.2
  exact (hder x ⟨hx0.le, hxδ.le⟩).hasDerivAt (Icc_mem_nhds hx0 hxδ)

/-! ## The target -/

theorem epsSqLip_of_xball {α C₁ Ce Cs R ε δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₁ Φs E)
    (hδ : 0 < δ) (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε δ Φs E h₀ g)
    (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε δ g)
    (hX : ∀ τ ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₁ (Work.FTS.Galerkin.slice g τ)) :
    ∃ Lw : ℝ, 0 < Lw ∧ ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ,
      Work.FTS.StrongEps.EpsSq α (fun z θ => Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g t z θ)
        ≤ Lw * (s - t) ^ 2 := by
  -- ## 1. the size bound of the scheme's right-hand side at the ball profiles
  obtain ⟨L, hLpos, hLsize⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.ConjOneSq (α := α) (C₀ := C₁) (Ce := Ce) (Cs := Cs) (R := R)
      (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml hR
  refine ⟨L, hLpos, ?_⟩
  -- ## 2. `EpsMem`/`EpsSq` of `Feps` at every slice of the curve
  have hG : ∀ σ ∈ Set.Icc 0 δ,
      Work.FTS.StrongEps.EpsMem α (Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ)) ∧
      Work.FTS.StrongEps.EpsSq α (Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ)) ≤ L := by
    intro σ hσ
    have hb := hX σ hσ
    obtain ⟨hm, hbd⟩ := hLsize (slice g σ) hb.smoothOpen hb.mem hb.sq_le hb.classC hb.ball
    rw [← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 (slice g σ)] at hm hbd
    exact ⟨hm, hbd⟩
  -- ## 3. joint a.e. strong measurability of the weighted curve on the horizon
  have hmeas : ∀ a b : ℝ, a ≤ b → a ∈ Set.Icc 0 δ → b ∈ Set.Icc 0 δ →
      MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ × ℝ =>
          Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g p.1) p.2.1 p.2.2
            * Work.FTS.StrongEps.epsW α p.2.1 p.2.2)
        ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
          Work.FTS.StrongEps.EpsLocalPStar.DomM) := by
    intro a b hab ha hb
    refine aesm_of_continuousOn_box hab ?_
    have hmem : Set.Ioo a b ×ˢ Work.FTS.StrongEps.Quad
        ⊆ Set.Ioo 0 δ ×ˢ Work.FTS.StrongEps.Quad :=
      fun p hp => ⟨⟨lt_of_le_of_lt ha.1 hp.1.1, lt_of_lt_of_le hp.1.2 hb.2⟩, hp.2⟩
    have hcont1 : ContinuousOn
        (fun p : ℝ × (ℝ × ℝ) =>
          Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g p.1 p.2.1 p.2.2)
        (Set.Ioo a b ×ˢ Work.FTS.StrongEps.Quad) :=
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.continuousOn_epsRHSP_joint_Ioo hreg hsol).mono hmem
    have hcont2 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => Work.FTS.StrongEps.epsW α p.2.1 p.2.2)
        (Set.Ioo a b ×ˢ Work.FTS.StrongEps.Quad) :=
      (Work.FTS.StrongEps.EpsSqTools.continuousOn_epsW α).comp (by fun_prop) (fun p hp => hp.2)
    refine (hcont1.mul hcont2).congr (fun p hp => ?_)
    show Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g p.1 p.2.1 p.2.2
        * Work.FTS.StrongEps.epsW α p.2.1 p.2.2
      = Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g p.1) p.2.1 p.2.2
        * Work.FTS.StrongEps.epsW α p.2.1 p.2.2
    rw [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E]
  -- ## 4. the bound on each orientation of the interval
  have hcase : ∀ a b : ℝ, a ≤ b → a ∈ Set.Icc 0 δ → b ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsSq α (fun z θ => slice g a z θ - slice g b z θ)
        ≤ L * (a - b) ^ 2 := by
    intro a b hab ha hb
    have hbd : ∀ᵐ σ ∂(MeasureTheory.volume.restrict (Set.uIoc a b)),
        Work.FTS.StrongEps.EpsLocalPStar.epsL2 α
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ)) ≤ ENNReal.ofReal L := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with σ hσ
      have hσ' : σ ∈ Set.Icc 0 δ := by
        rw [Set.uIoc_of_le hab] at hσ
        exact ⟨le_trans ha.1 hσ.1.le, le_trans hσ.2 hb.2⟩
      exact Work.FTS.StrongEps.EpsLocalPStar.epsL2_le_ofReal_of_mem (hG σ hσ').1 (hG σ hσ').2
    obtain ⟨-, hsq⟩ := Work.FTS.EpsEngine.EpsSq_intervalIntegral_le_gen (α := α) (a := a) (b := b)
      (B := L) hab hLpos.le (hmeas a b hab ha hb) hbd
    rw [Work.FTS.StrongEps.EpsLocalPStar.EpsSq_sub_comm]
    have haeeq : ∀ᵐ p ∂Work.FTS.StrongEps.EpsLocalPStar.DomM,
        (fun z θ => slice g b z θ - slice g a z θ) p.1 p.2
          = (fun z θ => ∫ σ in a..b,
              Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ) z θ) p.1 p.2 := by
      filter_upwards [Work.FTS.StrongEps.EpsLocalPStar.ae_open_DomM] with p hp
      have hvol := volterra_interval_of_regP hδ hsol hreg p.1 p.2 a b hp.1 ⟨hp.2.1, hp.2.2⟩ ha hb hab
      simp only [Work.FTS.Galerkin.slice_apply]
      exact hvol
    rw [Work.FTS.StrongEps.EpsLocalPStar.EpsSq_congr_ae
      (f := fun z θ => slice g b z θ - slice g a z θ)
      (g := fun z θ => ∫ σ in a..b, Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ) z θ) haeeq]
    calc Work.FTS.StrongEps.EpsSq α
          (fun z θ => ∫ σ in a..b, Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g σ) z θ)
        ≤ (b - a) * ((b - a) * L) := hsq
      _ = L * (a - b) ^ 2 := by ring
  -- ## 5. both orientations
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact hcase s t hst hs ht
  · have h := hcase t s hts ht hs
    rw [Work.FTS.StrongEps.EpsLocalPStar.EpsSq_sub_comm]
    calc Work.FTS.StrongEps.EpsSq α (fun z θ => slice g t z θ - slice g s z θ)
        ≤ L * (t - s) ^ 2 := h
      _ = L * (s - t) ^ 2 := by ring

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
