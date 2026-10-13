import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.E4R3.Flow5
import Submission.Work.FTS.StrongEps.EpsE4Thr.XStep
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.EpsEngine.HkMem_intervalIntegralPerz
import Submission.Work.FTS.EpsEngine.hmeas_slot_epsRHSP_fam_of_gate
import Submission.Work.FTS.EpsEngine.hjoint_HkIntegrand_epsRHSP_fam_of_gate
import Submission.Work.FTS.EpsEngine.RHSDataFepsSix.exists_RHSData_feps_six
import Submission.Work.FTS.EllipticEst.HkMem_sub_open
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.ZeroProfile
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.sup_mixed_diff
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.perz_HkIntegrand_diff
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.rem_eq_intervalIntegral
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.intervalIntegrable_slice_epsRHSP
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.aesm_diff_family

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-- **The interval integral of a `ℋ⁶`-family, with the sharp constant on the interval of
integration.**

`Work.FTS.EpsEngine.HkMem_intervalIntegralPerz` bounds the `ℋ⁶`-norm of `∫_a^b D` by
`B (b-a)` where `B` must dominate `HkNorm α 6 (D s)` on the *whole* horizon `[0,T]` (its
hypotheses are phrased over `Icc 0 T`, and the horizon must contain the endpoints `a`, `b`).
Here the relevant bound is only known on `[a,b]` — this is the point of the lemma: the family is
*clamped* to the interval,

  `K s = if s ∈ uIoc a b then D s else 0`,

which agrees with `D` on `uIoc a b` (so the integral is unchanged) and whose `ℋ⁶`-norm vanishes
off it, so that `B := η` is a legitimate global bound.  The clamped family is again `C^∞` on the
open quadrant, honest, jointly measurable, bounded in every slot on compacta and bounded per `z`
outside the interval (the zero-profile facts of `ZeroProfile.lean`), so the interval-integral
lemma applies verbatim. -/
theorem HkMem_intervalIntegral_clamp {α η a b δ : ℝ} {D : ℝ → ℝ → ℝ → ℝ}
    (hab : a ≤ b) (haI : a ∈ Set.Icc 0 δ) (hbI : b ∈ Set.Icc 0 δ) (hη : 0 ≤ η) (hδ0 : 0 ≤ δ)
    (hd : ∀ s ∈ Set.Icc a b, Work.Spaces.HkNorm α 6 (D s) ≤ η)
    (hsmD : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EllipticEst.SmoothOpen (D s))
    (hmemD : ∀ s ∈ Set.Icc 0 δ, Work.Spaces.HkMem α 6 (D s))
    (hslots : ∀ (j i : ℕ), j + i ≤ 6 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (D s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc 0 δ)))
    (hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α 6 (D p.1) p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))))
    (hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc 0 δ, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ 6 →
        |Work.Spaces.mixed j i (D s) q.1 q.2| ≤ C)
    (hperz : ∀ z ∈ Work.Spaces.Iz, ∃ Cz : ℝ, 0 ≤ Cz ∧ ∀ s ∈ Set.Icc 0 δ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (D s) z θ) ≤ Cz) :
    Work.Spaces.HkMem α 6 (fun z θ => ∫ s in a..b, D s z θ) ∧
      Work.Spaces.HkNorm α 6 (fun z θ => ∫ s in a..b, D s z θ) ≤ η * (b - a) := by
  classical
  -- the clamped family
  set K : ℝ → ℝ → ℝ → ℝ :=
    fun s => if s ∈ Set.uIoc a b then D s else (fun _ _ : ℝ => 0) with hK
  have hAo : Set.uIoc a b ⊆ Set.Icc (0 : ℝ) δ := by
    intro s hs
    rw [Set.uIoc_of_le hab] at hs
    exact ⟨le_trans haI.1 hs.1.le, le_trans hs.2 hbI.2⟩
  have hAb : Set.uIoc a b ⊆ Set.Icc a b := by
    intro s hs
    rw [Set.uIoc_of_le hab] at hs
    exact ⟨hs.1.le, hs.2⟩
  have hKAe : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc 0 δ)),
      s ∈ Set.Icc (0 : ℝ) δ := MeasureTheory.ae_restrict_mem measurableSet_Icc
  -- the clamped family evaluated on the interval, resp. off it
  have hKmem_eq : ∀ s ∈ Set.uIoc a b, K s = D s := by
    intro s hs
    rw [hK]
    exact if_pos hs
  have hKzero_eq : ∀ s ∉ Set.uIoc a b, K s = fun _ _ : ℝ => 0 := by
    intro s hs
    rw [hK]
    exact if_neg hs
  -- ## the seven hypotheses of the interval-integral lemma
  have hKsm : ∀ s ∈ Set.Icc (0 : ℝ) δ, Work.FTS.EllipticEst.SmoothOpen (K s) := by
    intro s hs
    by_cases h : s ∈ Set.uIoc a b
    · rw [hKmem_eq s h]; exact hsmD s (hAo h)
    · rw [hKzero_eq s h]; exact smoothOpen_zero_profile
  have hKmem : ∀ s ∈ Set.Icc (0 : ℝ) δ, Work.Spaces.HkMem α 6 (K s) := by
    intro s hs
    by_cases h : s ∈ Set.uIoc a b
    · rw [hKmem_eq s h]; exact hmemD s (hAo h)
    · rw [hKzero_eq s h]; exact HkMem_zero_profile α 6
  have hKbd : ∀ s ∈ Set.Icc (0 : ℝ) δ, Work.Spaces.HkNorm α 6 (K s) ≤ η := by
    intro s hs
    by_cases h : s ∈ Set.uIoc a b
    · rw [hKmem_eq s h]; exact hd s (hAb h)
    · rw [hKzero_eq s h, HkNorm_zero_profile]; exact hη
  have hKmeas : ∀ (j i : ℕ), j + i ≤ 6 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (K s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc 0 δ)) := by
    intro j i hji z θ hzθ
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => Work.Spaces.mixed j i (D s) z θ)
        (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
      (hslots j i hji z θ hzθ).mono_measure
        (MeasureTheory.Measure.restrict_mono hAo le_rfl)
    have h2 : MeasureTheory.AEStronglyMeasurable
        ((Set.uIoc a b).indicator (fun s : ℝ => Work.Spaces.mixed j i (D s) z θ))
        MeasureTheory.volume :=
      Work.FTS.EpsEngine.MeasAlt.aesm_indicator_of_aesm_restrict measurableSet_uIoc h1
    have h3 : MeasureTheory.AEStronglyMeasurable
        ((Set.uIoc a b).indicator (fun s : ℝ => Work.Spaces.mixed j i (D s) z θ))
        (MeasureTheory.volume.restrict (Set.Icc 0 δ)) :=
      h2.mono_measure MeasureTheory.Measure.restrict_le_self
    refine h3.congr ?_
    filter_upwards [hKAe] with s hs
    by_cases h : s ∈ Set.uIoc a b
    · rw [Set.indicator_of_mem h, hKmem_eq s h]
    · rw [Set.indicator_of_notMem h, hKzero_eq s h, mixed_zero_profile]
  have hKjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α 6 (K p.1) p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    have h2 := hjoint.indicator
      (s := Set.uIoc a b ×ˢ (Set.univ : Set (ℝ × ℝ)))
      (measurableSet_uIoc.prod MeasurableSet.univ)
    refine h2.congr ?_
    have hae : ∀ᵐ p ∂((MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))), p.1 ∈ Set.Icc (0 : ℝ) δ := by
      refine (MeasureTheory.Measure.ae_prod_iff_ae_ae
        (p := fun p : ℝ × (ℝ × ℝ) => p.1 ∈ Set.Icc (0 : ℝ) δ)
        (measurableSet_Icc.preimage measurable_fst)).mpr ?_
      filter_upwards [hKAe] with s hs
      exact Filter.Eventually.of_forall fun q => hs
    filter_upwards [hae] with p hp
    by_cases h : p.1 ∈ Set.uIoc a b
    · rw [Set.indicator_of_mem (show p ∈ Set.uIoc a b ×ˢ (Set.univ : Set (ℝ × ℝ)) from
        ⟨h, Set.mem_univ _⟩), hKmem_eq p.1 h]
    · rw [Set.indicator_of_notMem (show p ∉ Set.uIoc a b ×ˢ (Set.univ : Set (ℝ × ℝ)) from
        fun hmem => h hmem.1), hKzero_eq p.1 h, HkIntegrand_zero_profile]
  have hKsup : ∀ K' : Set (ℝ × ℝ), IsCompact K' → K' ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) δ, ∀ q ∈ K', ∀ (j i : ℕ), j + i ≤ 6 →
        |Work.Spaces.mixed j i (K s) q.1 q.2| ≤ C := by
    intro K' hK' hK'Q
    obtain ⟨C, hC0, hC⟩ := hsup K' hK' hK'Q
    refine ⟨C, hC0, fun s hs q hq j i hji => ?_⟩
    by_cases h : s ∈ Set.uIoc a b
    · rw [hKmem_eq s h]; exact hC s hs q hq j i hji
    · rw [hKzero_eq s h, mixed_zero_profile]
      simpa using hC0
  have hKperz : ∀ z ∈ Work.Spaces.Iz, ∃ Cz : ℝ, 0 ≤ Cz ∧ ∀ s ∈ Set.Icc (0 : ℝ) δ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 (K s) z θ) ≤ Cz := by
    intro z hz
    obtain ⟨Cz, hCz0, hCz⟩ := hperz z hz
    refine ⟨Cz, hCz0, fun s hs => ?_⟩
    by_cases h : s ∈ Set.uIoc a b
    · rw [hKmem_eq s h]; exact hCz s hs
    · rw [hKzero_eq s h, HkIntegrand_zero_profile]
      simpa using hCz0
  -- ## the interval-integral lemma
  obtain ⟨hmemK, hnormK⟩ :=
    Work.FTS.EpsEngine.HkMem_intervalIntegralPerz (α := α) (B := η) (k := 6)
      (T := δ) (a := a) (b := b) (H := K) hab hδ0 haI hbI
      hKsm hKmem hKbd hKmeas hKjoint hKsup
      (fun z hz => by obtain ⟨Cz, _, hCz⟩ := hKperz z hz; exact ⟨Cz, hCz⟩)
  -- ## the clamped family and `D` have the same integral
  have hfun : (fun z θ => ∫ s in a..b, K s z θ) = fun z θ => ∫ s in a..b, D s z θ := by
    funext z θ
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with s hs
    exact congrFun (congrFun (hKmem_eq s hs) z) θ
  rw [hfun] at hmemK hnormK
  exact ⟨hmemK, hnormK⟩

theorem hkDerivWithin_of_xball {α C₁ Ce Cs R ε δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₁ Φs E)
    (hδ : 0 < δ) (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε δ g)
    (hX : ∀ τ ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₁ (Work.FTS.Galerkin.slice g τ))
    (hvol : ∀ z θ τ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → τ ∈ Set.Icc 0 δ →
      g z θ τ = g z θ 0 + ∫ s in (0 : ℝ)..τ, Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ)
    {Lw : ℝ} (hLw : 0 ≤ Lw)
    (hEq : ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ,
      Work.FTS.StrongEps.EpsSq α (fun z θ => Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g t z θ)
        ≤ Lw * (s - t) ^ 2)
    (hcont : ∀ τ ∈ Set.Icc 0 δ, Work.FTS.StrongEps.EpsE4Thr.E4R5.HkContWithin α 6
      (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g) (Set.Icc 0 δ) τ) :
    ∀ τ ∈ Set.Icc 0 δ, Work.FTS.StrongEps.EpsE4Thr.E4R5.HkDerivWithin α 6
      (Work.FTS.Galerkin.slice g) (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) (Set.Icc 0 δ) τ := by
  -- ## the profile-level data of the right-hand side along the curve
  obtain ⟨Ce', hCe'pos, hFeps⟩ :=
    Work.FTS.EpsEngine.Feps_data_of_xball (α := α) (C₀ := C₁) (Ce := Ce) (Cs := Cs) (R := R)
      (ε := ε) (ρ := ρ) (Φs := Φs) (E := E) hρ hα hε hε1 hR hEll hstar hml
  have hVsm : ∀ σ ∈ Set.Icc 0 δ,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g σ)) :=
    fun σ hσ => (hFeps _ (hX σ hσ)).1
  have hVmem : ∀ σ ∈ Set.Icc 0 δ,
      Work.Spaces.HkMem α 6 (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g σ)) :=
    fun σ hσ => (hFeps _ (hX σ hσ)).2.1
  -- ## the gates of the right-hand side along the curve
  obtain ⟨hmeasV, -, hsupV⟩ :=
    Work.FTS.EpsEngine.RHSDataFepsSix.Feps_gates_six (α := α) (C₀ := C₁) (R := R) (Ce := Ce)
      (Cs := Cs) (Lw := Lw) (δ := δ) (ε := ε) (ρ := ρ) (Φs := Φs) (E := E) (g := g)
      hα hρ hε hε1 hEll hstar hml hR hLw hX hEq
  obtain ⟨Cz0, hCz0pos, hCz0⟩ :=
    Work.FTS.EpsEngine.RHSDataFepsSix.perz_Feps_six (α := α) (C₀ := C₁) (Ce := Ce) (Cs := Cs)
      (R := R) (ε := ε) (T := δ) (ρ := ρ) (Φs := Φs) (E := E)
      (F₀ := Work.FTS.Galerkin.slice g) hρ hα hε hε1 hR hδ.le hEll hstar hml hX
  -- the slot measurability of the curve, in the `Feps` form
  have hslotV : ∀ (j i : ℕ), j + i ≤ 6 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable
        (fun σ : ℝ => Work.Spaces.mixed j i
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g σ)) z θ)
        (MeasureTheory.volume.restrict (Set.Icc 0 δ)) := by
    intro j i hji z θ hzθ
    refine (hmeasV j i hji z θ hzθ).congr (Filter.Eventually.of_forall fun σ => ?_)
    simp only [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E g σ]
  -- the sup and per-`z` data of the curve, in the `Feps` form
  have hsupV' : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc 0 δ, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ 6 →
        |Work.Spaces.mixed j i
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g σ)) q.1 q.2| ≤ C := by
    intro K hK hKQ
    obtain ⟨C, hC0, hC⟩ := hsupV K hK hKQ
    refine ⟨C, hC0, fun σ hσ q hq j i hji => ?_⟩
    have := hC σ hσ q hq j i hji
    simpa only [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E g σ] using this
  have hperzV : ∀ z ∈ Work.Spaces.Iz, ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc 0 δ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g σ)) z θ) ≤ C :=
    fun z hz => ⟨Cz0 * (1 + (Work.Spaces.w z) ^ 2),
      mul_nonneg hCz0pos.le (by positivity), fun σ hσ => hCz0 z hz σ hσ⟩
  intro τ hτ η hη
  obtain ⟨d, hd, hdcont⟩ := hcont τ hτ η hη
  refine ⟨d, hd, fun s hs hsd => ?_⟩
  -- the interval-integrability of the curve at a point of the quadrant
  have hint : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      IntervalIntegrable (fun u : ℝ =>
        Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g u) z θ)
        MeasureTheory.volume 0 δ :=
    intervalIntegrable_slice_epsRHSP (α := α) (C₁ := C₁) (Ce := Ce) (Cs := Cs) (R := R)
      (ε := ε) (δ := δ) (Lw := Lw) hα hρ hε hε1 hR hEll hstar hml hδ.le hLw hX hEq
  -- ## the difference family and its data (independent of the order of `s`, `τ`)
  have hsmD : ∀ σ ∈ Set.Icc 0 δ, Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g σ) z θ
        - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ) :=
    fun σ hσ => Work.FTS.EllipticEst.smoothOpen_sub (hVsm σ hσ) (hVsm τ hτ)
  have hmemD : ∀ σ ∈ Set.Icc 0 δ, Work.Spaces.HkMem α 6
      (fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g σ) z θ
        - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ) :=
    fun σ hσ => Work.FTS.EllipticEst.HkMem_sub_open (hVsm σ hσ) (hVsm τ hτ)
      (hVmem σ hσ) (hVmem τ hτ)
  have hdiff := aesm_diff_family (α := α) (k := 6) (δ := δ)
    (V := fun σ => fun z θ =>
      Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g σ) z θ)
    (W := fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ)
    le_rfl hVsm (hVsm τ hτ) hslotV
  have hslotD := hdiff.1
  have hjointD := hdiff.2
  have hsupW : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ 6 →
        |Work.Spaces.mixed j i
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ)) q.1 q.2| ≤ C := by
    intro K hK hKQ
    obtain ⟨C, hC0, hC⟩ := hsupV' K hK hKQ
    exact ⟨C, hC0, fun q hq j i hji => hC τ hτ q hq j i hji⟩
  have hsupD := sup_mixed_diff (k := 6) (δ := δ)
    (V := fun σ => fun z θ =>
      Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g σ) z θ)
    (W := fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ)
    le_rfl hVsm (hVsm τ hτ) hsupV' hsupW
  have hperzW : ∀ z ∈ Work.Spaces.Iz, ∃ C : ℝ, 0 ≤ C ∧
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ)) z θ) ≤ C :=
    fun z hz => by obtain ⟨C, hC0, hC⟩ := hperzV z hz; exact ⟨C, hC0, hC τ hτ⟩
  have hperzD := perz_HkIntegrand_diff (α := α) (k := 6) (δ := δ)
    (V := fun σ => fun z θ =>
      Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g σ) z θ)
    (W := fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ)
    le_rfl hVsm (hVsm τ hτ) hVmem (hVmem τ hτ) hperzV hperzW
  -- ## the remainder is the integral of the difference, and it is `C^∞`
  have hremid : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.FTS.StrongEps.EpsE4Thr.E4R5.rem (Work.FTS.Galerkin.slice g)
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ)) s τ z θ
        = ∫ u in τ..s, (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g u) z θ
            - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ) :=
    fun z θ hzθ => rem_eq_intervalIntegral (α := α) (δ := δ) (ε := ε) hvol hint hs hτ hzθ
  have hremSm : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.EpsE4Thr.E4R5.rem (Work.FTS.Galerkin.slice g)
        (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ)) s τ) :=
    Work.FTS.EllipticEst.smoothOpen_sub
      (Work.FTS.EllipticEst.smoothOpen_sub (hX s hs).smoothOpen (hX τ hτ).smoothOpen)
      (Work.FTS.EllipticEst.SmoothOpen.const_mul' (s - τ) (hVsm τ hτ))
  -- the family of differences, abbreviated for the two applications below
  have hgoal : Work.FTS.VocabO.HQo α 6
        (Work.FTS.StrongEps.EpsE4Thr.E4R5.rem (Work.FTS.Galerkin.slice g)
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ)) s τ) ∧
      Work.Spaces.HkNorm α 6
        (Work.FTS.StrongEps.EpsE4Thr.E4R5.rem (Work.FTS.Galerkin.slice g)
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ)) s τ)
        ≤ η * |s - τ| := by
    rcases le_total τ s with hτs | hsτ
    · -- ## the case `τ ≤ s`: the remainder is `∫_τ^s`
      have hdA : ∀ σ ∈ Set.Icc τ s, Work.Spaces.HkNorm α 6
          (fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g σ) z θ
            - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ) ≤ η := by
        intro σ hσ
        have h3 : |σ - τ| < d := by
          rw [abs_of_nonneg (by linarith [hσ.1])]
          have h4 : |s - τ| < d := hsd
          rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s - τ)] at h4
          linarith [hσ.2]
        exact (hdcont σ ⟨hτ.1.trans hσ.1, hσ.2.trans hs.2⟩ h3).2
      obtain ⟨hmemG, hnormG⟩ := HkMem_intervalIntegral_clamp (α := α) (η := η) (a := τ) (b := s)
        (δ := δ) (D := fun σ => fun z θ =>
          Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g σ) z θ
            - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ)
        hτs hτ hs hη.le hδ.le hdA hsmD hmemD hslotD hjointD hsupD hperzD
      have hEqOn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          Work.FTS.StrongEps.EpsE4Thr.E4R5.rem (Work.FTS.Galerkin.slice g)
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ)) s τ z θ
            = (fun z θ => ∫ u in τ..s,
                (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g u) z θ
                  - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ)) z θ :=
        fun z θ hz hθ hθ2 => hremid z θ ⟨hz, hθ, hθ2⟩
      constructor
      · exact ⟨hremSm, Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 6 hmemG
          (fun z hz θ hθ => (hEqOn z θ hz hθ.1 hθ.2).symm)⟩
      · have hnorm_eq : Work.Spaces.HkNorm α 6
            (Work.FTS.StrongEps.EpsE4Thr.E4R5.rem (Work.FTS.Galerkin.slice g)
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ)) s τ)
            = Work.Spaces.HkNorm α 6 (fun z θ => ∫ u in τ..s,
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g u) z θ
                - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ)) := by
          rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm,
            Work.FTS.EllipticEst.HkSq_congr_open α 6 hEqOn]
        rw [hnorm_eq, abs_of_nonneg (sub_nonneg.mpr hτs)]
        exact hnormG
    · -- ## the case `s ≤ τ`: the remainder is `-∫_s^τ`
      have hdB : ∀ σ ∈ Set.Icc s τ, Work.Spaces.HkNorm α 6
          (fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g σ) z θ
            - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ) ≤ η := by
        intro σ hσ
        refine (hdcont σ ⟨hs.1.trans hσ.1, hσ.2.trans hτ.2⟩ (lt_of_le_of_lt ?_ hsd)).2
        rw [abs_of_nonpos (by linarith [hσ.2]), abs_of_nonpos (by linarith [hsτ])]
        linarith [hσ.1]
      obtain ⟨hmemG, hnormG⟩ := HkMem_intervalIntegral_clamp (α := α) (η := η) (a := s) (b := τ)
        (δ := δ) (D := fun σ => fun z θ =>
          Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g σ) z θ
            - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ)
        hsτ hs hτ hη.le hδ.le hdB hsmD hmemD hslotD hjointD hsupD hperzD
      have hsym : (fun z θ => ∫ u in τ..s,
            (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g u) z θ
              - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ))
          = fun z θ => -(∫ u in s..τ,
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g u) z θ
                - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ)) := by
        funext z θ
        rw [intervalIntegral.integral_symm]
      have hEqOn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          Work.FTS.StrongEps.EpsE4Thr.E4R5.rem (Work.FTS.Galerkin.slice g)
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ)) s τ z θ
            = (fun z θ => -(∫ u in s..τ,
                (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g u) z θ
                  - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ))) z θ := by
        intro z θ hz hθ hθ2
        rw [hremid z θ ⟨hz, hθ, hθ2⟩]
        exact congrFun (congrFun hsym z) θ
      constructor
      · exact ⟨hremSm, Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 6
          (Work.FTS.LocData.HkMem_neg α 6 hmemG)
          (fun z hz θ hθ => (hEqOn z θ hz hθ.1 hθ.2).symm)⟩
      · have hnorm_eq1 : Work.Spaces.HkNorm α 6
            (Work.FTS.StrongEps.EpsE4Thr.E4R5.rem (Work.FTS.Galerkin.slice g)
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ)) s τ)
            = Work.Spaces.HkNorm α 6 (fun z θ => -(∫ u in s..τ,
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g u) z θ
                - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ))) := by
          rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm,
            Work.FTS.EllipticEst.HkSq_congr_open α 6 hEqOn]
        have hnorm_eq2 : Work.Spaces.HkNorm α 6 (fun z θ => -(∫ u in s..τ,
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g u) z θ
                - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ)))
            = Work.Spaces.HkNorm α 6 (fun z θ => ∫ u in s..τ,
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g u) z θ
                - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ)) := by
          rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm,
            Work.FTS.LocData.HkSq_neg α 6 (fun z θ => ∫ u in s..τ,
              (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g u) z θ
                - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g τ) z θ))]
        rw [hnorm_eq1, hnorm_eq2,
          show |s - τ| = τ - s from by rw [abs_of_nonpos (by linarith [hsτ])]; ring]
        exact hnormG
  simpa only [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E g τ] using hgoal

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
