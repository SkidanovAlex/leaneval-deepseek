import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.EpsSlotAux
import Submission.Work.FTS.StrongEps.EpsSlotLipP
import Submission.Work.FTS.StrongEps.aemeasurable_mixed_family
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.StrongEps.E5G.aemeasurable_uncurry_HkIntegrand
import Submission.Work.FTS.StrongEps.E5G.HkIntegrand_intervalIntegral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

/-! ## Elementary helper lemmas -/

/-- For a nonnegative function, `ENNReal.ofReal` of its Bochner integral is at most the
`lintegral` of `ENNReal.ofReal ∘ f`.  (No measurability or integrability is needed: this is the
`enorm` form of the elementary `‖∫ f‖ ≤ ∫ ‖f‖`.) -/
theorem slice_lip_ofReal_integral_le_lintegral {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  have h1 : ENNReal.ofReal (∫ x, f x ∂μ) = ‖∫ x, f x ∂μ‖ₑ :=
    (Real.enorm_eq_ofReal (integral_nonneg hf)).symm
  rw [h1]
  refine (enorm_integral_le_lintegral_enorm f).trans ?_
  refine lintegral_mono fun x => ?_
  rw [Real.enorm_eq_ofReal (hf x)]

/-- `HkSq` is the square of `HkNorm`, so a bound on the norm bounds the square. -/
theorem slice_lip_HkSq_le_sq {α B : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkNorm α k f ≤ B) : Work.Spaces.HkSq α k f ≤ B ^ 2 := by
  have h2 : Work.Spaces.HkSq α k f = (Work.Spaces.HkNorm α k f) ^ 2 :=
    (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k f)).symm
  rw [h2]
  exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α k f) h 2

/-! ## The pointwise slot identity for the fake-time integral -/

/-- The mixed slots of the fake-time integral of the right-hand side:
`D_z^jD_θ^i (∫ s in σ'..σ, epsRHSP s) = ∫ s in σ'..σ, D_z^jD_θ^i (epsRHSP s)` at every point of
the open quadrant, for `j + i ≤ 4`. -/
theorem slice_lip_slot_eq {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ) (Set.Icc (0 : ℝ) T))
    (hsmR : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (hslotb : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (j i : ℕ), j + i ≤ 4 → ∀ p : ℝ × ℝ, p ∈ K →
        |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2| ≤ C)
    {σ σ' : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) T) (hσ' : σ' ∈ Set.Icc (0 : ℝ) T) (hle : σ' ≤ σ)
    {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) {j i : ℕ} (hji : j + i ≤ 4) :
    Work.Spaces.mixed j i
        (fun z θ => ∫ s in σ'..σ, Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ) p.1 p.2
      = ∫ s in σ'..σ, Work.Spaces.mixed j i
          (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2 := by
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  -- a closed box around `p` inside the open quadrant
  set z₁ : ℝ := p.1 / 2 with hz₁
  set z₂ : ℝ := p.1 + 1 with hz₂
  set θ₁ : ℝ := p.2 / 2 with hθ₁
  set θ₂ : ℝ := (p.2 + Real.pi / 2) / 2 with hθ₂
  have hz1lt : z₁ < p.1 := by rw [hz₁]; linarith
  have hz2gt : p.1 < z₂ := by rw [hz₂]; linarith
  have hθ1lt : θ₁ < p.2 := by rw [hθ₁]; linarith
  have hθ2gt : p.2 < θ₂ := by rw [hθ₂]; linarith
  have hz1pos : 0 < z₁ := by rw [hz₁]; linarith
  have hθ1pos : 0 < θ₁ := by rw [hθ₁]; linarith
  have hθ2lt : θ₂ < Real.pi / 2 := by rw [hθ₂]; linarith
  have hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro q ⟨hq1, hq2⟩
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le hz1pos hq1.1, lt_of_lt_of_le hθ1pos hq2.1, lt_of_le_of_lt hq2.2 hθ2lt⟩
  have hbox_compact : IsCompact (Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hslotb _ hbox_compact hboxQ
  have hbdd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ →
        |Work.Spaces.mixed k l (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) q.1 q.2| ≤ max C 0 :=
    fun s hs k l hkl q hq => le_trans (hC s hs k l hkl q hq) (le_max_left _ _)
  exact Work.FTS.StrongEps.mixed_intervalIntegral_eq (H := fun s z θ =>
      Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ) hσ' hσ hle (le_max_right _ _) hsmR
    (Work.FTS.StrongEps.aemeasurable_mixed_family hsmR hcont) hbdd hboxQ hji p.1 p.2
    ⟨⟨hz1lt, hz2gt⟩, ⟨hθ1lt, hθ2gt⟩⟩

/-! ## The slice difference is the fake-time integral on the open quadrant -/

/-- `slice g σ - slice g σ'` agrees with `∫ s in σ'..σ, epsRHSP s` on the open quadrant. -/
theorem slice_lip_diff_eq_integral {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ) (Set.Icc (0 : ℝ) T))
    {σ σ' : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) T) (hσ' : σ' ∈ Set.Icc (0 : ℝ) T) (hle : σ' ≤ σ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.FTS.Galerkin.slice g σ z θ - Work.FTS.Galerkin.slice g σ' z θ
        = ∫ s in σ'..σ, Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ := by
  intro z θ hzθ
  have h1 := Work.FTS.StrongEps.epsSol_eq_integralP hsol hcont z θ σ hzθ hσ
  have h2 := Work.FTS.StrongEps.epsSol_eq_integralP hsol hcont z θ σ' hzθ hσ'
  have hcontF : ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ)
      (Set.Icc (0 : ℝ) T) := hcont z θ hzθ
  have hi1 : IntervalIntegrable (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ)
      volume 0 σ' :=
    ContinuousOn.intervalIntegrable_of_Icc hσ'.1
      (hcontF.mono (Set.Icc_subset_Icc le_rfl hσ'.2))
  have hi2 : IntervalIntegrable (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ)
      volume σ' σ :=
    ContinuousOn.intervalIntegrable_of_Icc hle
      (hcontF.mono (Set.Icc_subset_Icc hσ'.1 hσ.2))
  have hadj := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  show g z θ σ - g z θ σ' = _
  rw [h1, h2]
  linarith

/-! ## The per-`s` Tonelli identity -/

/-- For a fixed slice `f` of class `HkMem α k` whose `HkIntegrand` is jointly measurable, the
`lintegral` of `ofReal ∘ HkIntegrand` over `Iz × Iθ` is `ofReal (HkSq α k f)`. -/
theorem slice_lip_ofReal_HkSq_eq_lintegral {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k f)
    (hmeas : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :
    (∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f p.1 p.2)
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      = ENNReal.ofReal (Work.Spaces.HkSq α k f) := by
  have hmeas' : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k f p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hmeas
  rw [Work.Spaces.HkSq,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2
      (Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)]
  have hlin : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
      = ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α k f p.1 p.2)
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    MeasureTheory.lintegral_lintegral
      (f := fun z θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ)) hmeas'
  rw [← hlin]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z hz)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)).symm


/-! ## Auxiliary lemmas for the main chain -/

/-- The interval `uIoc σ' σ` is contained in `Icc 0 T`. -/
lemma slice_lip_uIoc_subset {T σ σ' : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) T)
    (hσ' : σ' ∈ Set.Icc (0 : ℝ) T) (hle : σ' ≤ σ) : Set.uIoc σ' σ ⊆ Set.Icc (0 : ℝ) T := by
  intro s hs
  have h1 : s ∈ Set.Icc σ' σ := by
    have h2 := Set.uIoc_subset_uIcc hs
    rwa [Set.uIcc_of_le hle] at h2
  exact ⟨le_trans hσ'.1 h1.1, le_trans h1.2 hσ.2⟩

/-- The interval integral over `σ'..σ` is the set integral over `uIoc σ' σ`. -/
lemma slice_lip_intervalIntegral_eq_set {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ x in a..b, f x) = ∫ x in Set.uIoc a b, f x := by
  rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]

/-- **Tonelli swap for the fake-time integral of the `HkIntegrand`.**
For a family `H` of `SmoothOpen` profiles whose `HkIntegrand` is jointly measurable, the iterated
`lintegral` over `(z,θ)` of the fake-time `lintegral` over `s` equals the iterated `lintegral` over
`s` of the `(z,θ)`-one. -/
theorem slice_lip_tonelli {α : ℝ} {k : ℕ} {T σ σ' : ℝ} {H : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hσ : σ ∈ Set.Icc (0 : ℝ) T) (hσ' : σ' ∈ Set.Icc (0 : ℝ) T) (hle : σ' ≤ σ)
    (hmeas : AEMeasurable
      (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.HkIntegrand α k (H q.1) q.2.1 q.2.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ))
      = ∫⁻ s in Set.uIoc σ' σ, ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ) := by
  have hsub : Set.uIoc σ' σ ⊆ Set.Icc (0 : ℝ) T := slice_lip_uIoc_subset hσ hσ' hle
  have hle' : (volume.restrict (Set.uIoc σ' σ) : Measure ℝ) ≤ volume.restrict (Set.Icc (0 : ℝ) T) :=
    Measure.restrict_mono hsub le_rfl
  have hle'' : (volume.restrict (Set.uIoc σ' σ) : Measure ℝ).prod
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
      ≤ (volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Measure.prod_mono hle' le_rfl
  -- measurability of the `ofReal`-family with the `s`-measure restricted to the interval
  have hf : AEMeasurable
      (fun q : ℝ × (ℝ × ℝ) => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H q.1) q.2.1 q.2.2))
      ((volume.restrict (Set.uIoc σ' σ)).prod
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hmeas.mono_measure hle'')
  -- measurability of the partial `s`-integral over `(z,θ)`
  have hf'' : AEMeasurable
      (fun p : ℝ × ℝ => ∫⁻ s in Set.uIoc σ' σ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    AEMeasurable.lintegral_prod_left'
      (f := fun q : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H q.1) q.2.1 q.2.2)) hf
  -- single-slice measurability, from continuity on the open quadrant
  have hsingle : ∀ s ∈ Set.uIoc σ' σ, AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    intro s hs
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    exact (Work.Spaces.aesm_of_continuousOn_Qd _
      ((hsm s (hsub hs)).continuousOn_HkIntegrand α k)).aemeasurable
  have h1 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ))
      = ∫⁻ p, (∫⁻ s in Set.uIoc σ' σ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2))
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.lintegral_prod
      (f := fun p : ℝ × ℝ => ∫⁻ s in Set.uIoc σ' σ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2)) hf'').symm
  have h2 : (∫⁻ p, (∫⁻ s in Set.uIoc σ' σ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2))
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      = ∫⁻ s in Set.uIoc σ' σ, ∫⁻ p,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2)
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.lintegral_prod_symm
        (f := fun q : ℝ × (ℝ × ℝ) =>
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H q.1) q.2.1 q.2.2)) hf).symm.trans
      (MeasureTheory.lintegral_prod
        (f := fun q : ℝ × (ℝ × ℝ) =>
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H q.1) q.2.1 q.2.2)) hf)
  have h3 : (∫⁻ s in Set.uIoc σ' σ, ∫⁻ p,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2)
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      = ∫⁻ s in Set.uIoc σ' σ, ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    exact MeasureTheory.lintegral_prod
      (f := fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) p.1 p.2))
      (hsingle s hs)
  exact h1.trans (h2.trans h3)

