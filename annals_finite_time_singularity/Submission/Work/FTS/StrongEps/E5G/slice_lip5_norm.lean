import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.psiSeries_bslOp_of_cptQ
import Submission.Work.FTS.PhiStar.Honesty.psiSeries_smooth_of_cptQ
import Submission.Work.FTS.PhiStar.Honesty.smoothCptQ_hkMem
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.smoothOpen_slice_of_epsRHSP
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.H6Aux.RStep
import Submission.Work.FTS.StrongPersist.H6Rows.NZzero6
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimExtract.limExtract_bounds10_const
import Submission.Work.FTS_EllLimOK.tower_jet_identities
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.ellWeakPos_psiSeries_of_cptQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- **The elliptic node for a compactly supported `C^∞` source, at every level.** -/
theorem ellWeakPos_psiSeries_of_cptQ (K : ℕ) {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {G : ℝ → ℝ → ℝ} (hG : SmoothCptQ G)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar G z = 0) :
    Work.FTS.EllipticEst.TT.EllWeakPos α K G (Work.FTS.PhiStar.Series.psiSeries α G) ∧
      Work.Elliptic.IsBslSol α G (Work.FTS.PhiStar.Series.psiSeries α G) := by
  have hγ : Work.Spaces.gam α ≤ 3 / 2 := by
    simp only [Work.Spaces.gam]
    linarith
  obtain ⟨hσ, hV⟩ := slots_psiSeries_of_cptQ K hα hα4 hG hFs
  refine ⟨ellWeakPos_K_psiSeries_of_level0 K hα hα4 hγ (smoothCptQ_hkMem hG K)
    (psiSeries_smooth_of_cptQ hα hα4 hG)
    (fun z hz θ hθ hθ2 => psiSeries_bslOp_of_cptQ hα hα4 hG hFs z hz θ hθ hθ2)
    hFs (hcoef_psiSeries hα hα4 hG.smoothOpen (smoothCptQ_hkMem hG 0)) hσ hV, ?_⟩
  exact isBslSol_psiSeries_of_cptQ hα hα4 hG hFs

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux3.L12_slice_eq_zero_of_hkMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **`L₁₂(slice g τ)(0) = 0` along an ε-solution, from `ℋ⁴` data**. -/
theorem L12_slice_eq_zero_of_hkMem {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g₀ : Fn} {g : Fam} {B : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hT : 0 < T)
    (hsol : IsEpsSolP α ρ ε T Φs E g₀ g)
    (hc1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    (hsm : ∀ τ ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (slice g τ))
    (hmem : ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (slice g τ))
    (hRm : ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (epsRHSP α ρ ε Φs E g τ) ∧
      Work.Spaces.HkNorm α 4 (epsRHSP α ρ ε Φs E g τ) ≤ B)
    (hWm : ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (Jeps ρ ε (epsWP α ρ ε Φs E g τ)))
    (h0 : Work.Construction.L12 g₀ 0 = 0) :
    ∀ τ ∈ Set.Icc 0 T, Work.Construction.L12 (slice g τ) 0 = 0 :=
  Work.FTS.StrongEps.E5Aux3.L12_slice_eq_zero_of_hkMem_proof hα hρ hε hT hsol hc1 hsm hmem hRm
    hWm h0

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.slice_lip5_norm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

/-! ## The level-`5` chain

This file is the level-`5` analogue of `E5G.slice_lip_norm`.  Everything in the chain of
`slice_lip_ordered` that does not mention the order is reused verbatim
(`slice_lip_uIoc_subset`, `slice_lip_tonelli`, `slice_lip_ofReal_HkSq_eq_lintegral`,
`slice_lip_intervalIntegral_eq_set`, `slice_lip_ofReal_integral_le_lintegral`,
`slice_lip_HkSq_le_sq`, `slice_lip_diff_eq_integral`, `aemeasurable_uncurry_HkIntegrand`,
`HkSq_congr_open`, `HkNorm_neg`); the two order-`4`-hard-wired steps are replaced by their
general versions

* `Work.FTS.StrongEps.E5G5.mixed_intervalIntegral_eq_gen` (the slot exchange, here at `n = 5`),
* `Work.FTS.StrongEps.E5G5.HkIntegrand_intervalIntegral_le_gen` (the slotwise Cauchy–Schwarz,
  here at `k = 5`). -/

/-- The mixed slots of the fake-time integral of the right-hand side, for `j + i ≤ 5`. -/
theorem slice_lip5_slot_eq {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ) (Set.Icc (0 : ℝ) T))
    (hsmR : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (hslotb : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (j i : ℕ), j + i ≤ 5 → ∀ p : ℝ × ℝ, p ∈ K →
        |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2| ≤ C)
    {σ σ' : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) T) (hσ' : σ' ∈ Set.Icc (0 : ℝ) T) (hle : σ' ≤ σ)
    {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) {j i : ℕ} (hji : j + i ≤ 5) :
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
  have hbdd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ 5 → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ →
        |Work.Spaces.mixed k l (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) q.1 q.2| ≤ max C 0 :=
    fun s hs k l hkl q hq => le_trans (hC s hs k l hkl q hq) (le_max_left _ _)
  exact Work.FTS.StrongEps.E5G5.mixed_intervalIntegral_eq_gen (H := fun s z θ =>
      Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ) (n := 5) hσ' hσ hle (le_max_right _ _) hsmR
    (Work.FTS.StrongEps.aemeasurable_mixed_family hsmR hcont) hbdd hboxQ hji p.1 p.2
    ⟨⟨hz1lt, hz2gt⟩, ⟨hθ1lt, hθ2gt⟩⟩

/-- **The `ℋ⁵`-Lipschitz bound in the fake time, for the ordered pair `σ' ≤ σ`.** -/
theorem slice_lip5_ordered {α T ε B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ) (Set.Icc (0 : ℝ) T))
    (hsmR : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (h5 : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (hb5 : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) ≤ B)
    (hslotb : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (j i : ℕ), j + i ≤ 5 → ∀ p : ℝ × ℝ, p ∈ K →
        |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2| ≤ C)
    {σ σ' : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) T) (hσ' : σ' ∈ Set.Icc (0 : ℝ) T) (hle : σ' ≤ σ) :
    Work.Spaces.HkNorm α 5
        (fun z θ => Work.FTS.Galerkin.slice g σ z θ - Work.FTS.Galerkin.slice g σ' z θ)
      ≤ B * (σ - σ') := by
  have hB : 0 ≤ B := le_trans (Work.Spaces.HkNorm_nonneg α 5 _) (hb5 σ hσ)
  have hΔ : 0 ≤ σ - σ' := sub_nonneg.mpr hle
  have hsub : Set.uIoc σ' σ ⊆ Set.Icc (0 : ℝ) T := slice_lip_uIoc_subset hσ hσ' hle
  set R : ℝ → ℝ → ℝ → ℝ := fun s z θ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ with hR
  set W : ℝ → ℝ → ℝ := fun z θ => ∫ s in σ'..σ, R s z θ with hW
  have hmeasJ : AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.HkIntegrand α 5 (R q.1) q.2.1 q.2.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :=
    Work.FTS.StrongEps.E5G.aemeasurable_uncurry_HkIntegrand (α := α) (T := T) (k := 5) hsmR hcont
  -- the pointwise bound
  have hpoint : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkIntegrand α 5 W z θ
        ≤ (σ - σ') * ∫ s in σ'..σ, Work.Spaces.HkIntegrand α 5 (R s) z θ := by
    intro z θ hzθ
    obtain ⟨C, hC⟩ := hslotb {(z, θ)} isCompact_singleton (by rintro q rfl; exact hzθ)
    exact Work.FTS.StrongEps.E5G5.HkIntegrand_intervalIntegral_le_gen (H := R) (C := max C 0)
      (k := 5) hle (le_max_right _ _)
      hzθ.1 hzθ.2.1 hzθ.2.2
      (fun j i hji => (Work.FTS.StrongEps.aemeasurable_mixed_family hsmR hcont j i z θ hzθ).mono_measure
        (Measure.restrict_mono hsub le_rfl))
      (fun j i hji s hs =>
        le_trans (hC s (hsub hs) j i hji (z, θ) (Set.mem_singleton _)) (le_max_left _ _))
      (fun j i hji => slice_lip5_slot_eq hcont hsmR hslotb hσ hσ' hle hzθ hji)
  -- the a.e. statements
  have hae_Ioo : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    change ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (Real.pi / 2))), θ ∈ Set.Ioo 0 (Real.pi / 2)
    rw [ae_restrict_iff' measurableSet_Icc]
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (t := ({0} : Set ℝ) ∪ {Real.pi / 2}) ?_
      (measure_union_null (measure_singleton 0) (measure_singleton (Real.pi / 2)))
    intro θ hθ
    simp only [Set.mem_ofPred_eq, not_imp, Set.mem_Icc, Set.mem_Ioo, Set.mem_union,
      Set.mem_singleton_iff] at hθ ⊢
    obtain ⟨⟨h0, h1⟩, h2⟩ := hθ
    rcases eq_or_lt_of_le h0 with h | h
    · exact Or.inl h.symm
    · refine Or.inr (le_antisymm h1 ?_)
      by_contra hcon
      exact h2 ⟨h, lt_of_not_ge hcon⟩
  have hae_z : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 < z := by
    change ∀ᵐ z ∂(volume.restrict (Set.Ici (0 : ℝ))), 0 < z
    rw [ae_restrict_iff' measurableSet_Ici]
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (t := ({0} : Set ℝ)) ?_ (measure_singleton 0)
    intro z hz
    simp only [Set.mem_ofPred_eq, not_imp, Set.mem_Ici, Set.mem_singleton_iff] at hz ⊢
    exact le_antisymm (le_of_not_gt hz.2) hz.1
  have haeθ : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 W z θ)
          ≤ ENNReal.ofReal ((σ - σ') * ∫ s in σ'..σ,
              Work.Spaces.HkIntegrand α 5 (R s) z θ) := by
    filter_upwards [hae_z] with z hz
    filter_upwards [hae_Ioo] with θ hθ
    exact ENNReal.ofReal_le_ofReal (hpoint z θ ⟨hz, hθ.1, hθ.2⟩)
  -- the chain
  have step1 : ENNReal.ofReal (Work.Spaces.HkSq α 5 W)
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 W z θ) := by
    rw [Work.Spaces.HkSq]
    exact (slice_lip_ofReal_integral_le_lintegral (μ := volume.restrict Work.Spaces.Iz)
        (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 5 W z θ)
        (fun z => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 5 W z θ)).trans
      (lintegral_mono fun z => slice_lip_ofReal_integral_le_lintegral
        (μ := volume.restrict Work.Spaces.Iθ) (f := fun θ => Work.Spaces.HkIntegrand α 5 W z θ)
        (fun θ => Work.Spaces.HkIntegrand_nonneg α 5 W z θ))
  have step2 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 W z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((σ - σ') * ∫ s in σ'..σ, Work.Spaces.HkIntegrand α 5 (R s) z θ) := by
    refine lintegral_mono_ae ?_
    filter_upwards [haeθ] with z hz
    exact lintegral_mono_ae hz
  have step3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((σ - σ') * ∫ s in σ'..σ, Work.Spaces.HkIntegrand α 5 (R s) z θ))
      = ENNReal.ofReal (σ - σ') * ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (∫ s in σ'..σ, Work.Spaces.HkIntegrand α 5 (R s) z θ) := by
    have hinner : ∀ z : ℝ, (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((σ - σ') * ∫ s in σ'..σ, Work.Spaces.HkIntegrand α 5 (R s) z θ))
        = ENNReal.ofReal (σ - σ') * ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (∫ s in σ'..σ, Work.Spaces.HkIntegrand α 5 (R s) z θ) := by
      intro z
      simp only [ENNReal.ofReal_mul hΔ]
      rw [MeasureTheory.lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    simp only [hinner]
    rw [MeasureTheory.lintegral_const_mul']
    exact ENNReal.ofReal_ne_top
  have step4 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (∫ s in σ'..σ, Work.Spaces.HkIntegrand α 5 (R s) z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (R s) z θ) := by
    refine lintegral_mono fun z => lintegral_mono fun θ => ?_
    rw [slice_lip_intervalIntegral_eq_set hle (fun s => Work.Spaces.HkIntegrand α 5 (R s) z θ)]
    exact slice_lip_ofReal_integral_le_lintegral (μ := volume.restrict (Set.uIoc σ' σ))
      (f := fun s => Work.Spaces.HkIntegrand α 5 (R s) z θ)
      (fun s => Work.Spaces.HkIntegrand_nonneg α 5 (R s) z θ)
  have step5 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (R s) z θ))
      = ∫⁻ s in Set.uIoc σ' σ, ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (R s) z θ) :=
    slice_lip_tonelli hsmR hσ hσ' hle hmeasJ
  have step6 : (∫⁻ s in Set.uIoc σ' σ, ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (R s) z θ))
      = ∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (Work.Spaces.HkSq α 5 (R s)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    have hsingle : AEMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 5 (R s) p.1 p.2)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
      (Work.Spaces.aesm_of_continuousOn_Qd _
        ((hsmR s (hsub hs)).continuousOn_HkIntegrand α 5)).aemeasurable
    rw [(MeasureTheory.lintegral_prod (f := fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (R s) p.1 p.2))
      (ENNReal.measurable_ofReal.comp_aemeasurable hsingle)).symm]
    exact slice_lip_ofReal_HkSq_eq_lintegral (h5 s (hsub hs)) hsingle
  have step7 : (∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (Work.Spaces.HkSq α 5 (R s)))
      ≤ ∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (B * B) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    exact ENNReal.ofReal_le_ofReal
      (by simpa only [pow_two] using slice_lip_HkSq_le_sq (hb5 s (hsub hs)))
  have step8 : (∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (B * B))
      = ENNReal.ofReal (B * B) * ENNReal.ofReal (σ - σ') := by
    rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ, Real.volume_uIoc,
      abs_of_nonneg hΔ]
  have step9 : ENNReal.ofReal (σ - σ') * (ENNReal.ofReal (B * B) * ENNReal.ofReal (σ - σ'))
      = ENNReal.ofReal ((B * (σ - σ')) ^ 2) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hB hB), ← ENNReal.ofReal_mul hΔ]
    congr 1
    ring
  have hchain : ENNReal.ofReal (Work.Spaces.HkSq α 5 W) ≤ ENNReal.ofReal ((B * (σ - σ')) ^ 2) := by
    have h7 : (∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (Work.Spaces.HkSq α 5 (R s)))
        ≤ ENNReal.ofReal (B * B) * ENNReal.ofReal (σ - σ') := by
      rw [← step8]; exact step7
    have hmono : ENNReal.ofReal (σ - σ') * (∫⁻ s in Set.uIoc σ' σ,
          ENNReal.ofReal (Work.Spaces.HkSq α 5 (R s)))
        ≤ ENNReal.ofReal (σ - σ') * (ENNReal.ofReal (B * B) * ENNReal.ofReal (σ - σ')) := by
      gcongr
    calc ENNReal.ofReal (Work.Spaces.HkSq α 5 W)
        ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 W z θ) := step1
      _ ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((σ - σ') * ∫ s in σ'..σ,
              Work.Spaces.HkIntegrand α 5 (R s) z θ) := step2
      _ = ENNReal.ofReal (σ - σ') * ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (∫ s in σ'..σ, Work.Spaces.HkIntegrand α 5 (R s) z θ) := step3
      _ ≤ ENNReal.ofReal (σ - σ') * ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (R s) z θ) := by
          gcongr
      _ = ENNReal.ofReal (σ - σ') * ∫⁻ s in Set.uIoc σ' σ, ∫⁻ z in Work.Spaces.Iz,
            ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 5 (R s) z θ) := by
          rw [step5]
      _ = ENNReal.ofReal (σ - σ') * ∫⁻ s in Set.uIoc σ' σ,
            ENNReal.ofReal (Work.Spaces.HkSq α 5 (R s)) := by rw [step6]
      _ ≤ ENNReal.ofReal (σ - σ') * (ENNReal.ofReal (B * B) * ENNReal.ofReal (σ - σ')) := hmono
      _ = ENNReal.ofReal ((B * (σ - σ')) ^ 2) := step9
  -- conclusion
  have hsq : Work.Spaces.HkSq α 5 W ≤ (B * (σ - σ')) ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg (B * (σ - σ')))).mp hchain
  have hcongr : Work.Spaces.HkSq α 5
        (fun z θ => Work.FTS.Galerkin.slice g σ z θ - Work.FTS.Galerkin.slice g σ' z θ)
      = Work.Spaces.HkSq α 5 W :=
    Work.FTS.EllipticEst.HkSq_congr_open α 5 (f := fun z θ =>
        Work.FTS.Galerkin.slice g σ z θ - Work.FTS.Galerkin.slice g σ' z θ) (g := W)
      (fun z θ hz hθ0 hθ1 => slice_lip_diff_eq_integral hsol hcont hσ hσ' hle z θ ⟨hz, hθ0, hθ1⟩)
  have hnorm_eq : Work.Spaces.HkNorm α 5
        (fun z θ => Work.FTS.Galerkin.slice g σ z θ - Work.FTS.Galerkin.slice g σ' z θ)
      = Work.Spaces.HkNorm α 5 W := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hcongr]
  rw [hnorm_eq]
  calc Work.Spaces.HkNorm α 5 W
      = Real.sqrt (Work.Spaces.HkSq α 5 W) := rfl
    _ ≤ Real.sqrt ((B * (σ - σ')) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = B * (σ - σ') := Real.sqrt_sq (mul_nonneg hB hΔ)

theorem slice_lip5_norm {α T ε B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ) (Set.Icc (0 : ℝ) T))
    (hsmR : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (h5 : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (hb5 : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) ≤ B)
    (hslotb : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (j i : ℕ), j + i ≤ 5 → ∀ p : ℝ × ℝ, p ∈ K →
        |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2| ≤ C) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 5 (fun z θ => Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ)
        ≤ B * |τ - τ'| := by
  intro τ hτ τ' hτ'
  rcases le_total τ' τ with hle | hle
  · have h := slice_lip5_ordered hsol hcont hsmR h5 hb5 hslotb hτ hτ' hle
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact h
  · have h := slice_lip5_ordered hsol hcont hsmR h5 hb5 hslotb hτ' hτ hle
    have hneg : Work.Spaces.HkNorm α 5
          (fun z θ => Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ)
        = Work.Spaces.HkNorm α 5
          (fun z θ => Work.FTS.Galerkin.slice g τ' z θ - Work.FTS.Galerkin.slice g τ z θ) := by
      rw [show (fun z θ => Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ)
            = -(fun z θ => Work.FTS.Galerkin.slice g τ' z θ - Work.FTS.Galerkin.slice g τ z θ)
            from by funext z θ; simp only [Pi.neg_apply]; ring,
        Work.FTS.EllipticEst.HkNorm_neg]
    show Work.Spaces.HkNorm α 5
        (fun z θ => Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ)
        ≤ B * |τ - τ'|
    rw [hneg, abs_of_nonpos (sub_nonpos.mpr hle),
      show -(τ - τ') = τ' - τ from by ring]
    exact h

end Work.FTS.StrongEps.E5G
end
