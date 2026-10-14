import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartAux
import Submission.Work.FTS.StrongEps.epsWP_abs_le_on_compact
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS.StrongPersist.SupOpenH2
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.slice_lip_ordered =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

/-- The `HkIntegrand` family is jointly measurable (from the delegated lemma). -/
private theorem slice_lip_hmeasJ {α : ℝ} {T : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => H s z θ) (Set.Icc (0 : ℝ) T)) :
    AEMeasurable (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.HkIntegrand α k (H q.1) q.2.1 q.2.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :=
  Work.FTS.StrongEps.E5G.aemeasurable_uncurry_HkIntegrand (α := α) (T := T) (k := k) hsm hcont

/-- **The `ℋ⁴`-Lipschitz bound in the fake time, for the ordered pair `σ' ≤ σ`.** -/
theorem slice_lip_ordered {α T ε B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ) (Set.Icc (0 : ℝ) T))
    (hsmR : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (h4 : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (hb4 : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) ≤ B)
    (hslotb : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (j i : ℕ), j + i ≤ 4 → ∀ p : ℝ × ℝ, p ∈ K →
        |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2| ≤ C)
    {σ σ' : ℝ} (hσ : σ ∈ Set.Icc (0 : ℝ) T) (hσ' : σ' ∈ Set.Icc (0 : ℝ) T) (hle : σ' ≤ σ) :
    Work.Spaces.HkNorm α 4
        (fun z θ => Work.FTS.Galerkin.slice g σ z θ - Work.FTS.Galerkin.slice g σ' z θ)
      ≤ B * (σ - σ') := by
  have hB : 0 ≤ B := le_trans (Work.Spaces.HkNorm_nonneg α 4 _) (hb4 σ hσ)
  have hΔ : 0 ≤ σ - σ' := sub_nonneg.mpr hle
  have hsub : Set.uIoc σ' σ ⊆ Set.Icc (0 : ℝ) T := slice_lip_uIoc_subset hσ hσ' hle
  set R : ℝ → ℝ → ℝ → ℝ := fun s z θ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ with hR
  set W : ℝ → ℝ → ℝ := fun z θ => ∫ s in σ'..σ, R s z θ with hW
  have hmeasJ : AEMeasurable (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.HkIntegrand α 4 (R q.1) q.2.1 q.2.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :=
    slice_lip_hmeasJ hsmR hcont
  -- the pointwise bound
  have hpoint : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkIntegrand α 4 W z θ
        ≤ (σ - σ') * ∫ s in σ'..σ, Work.Spaces.HkIntegrand α 4 (R s) z θ := by
    intro z θ hzθ
    obtain ⟨C, hC⟩ := hslotb {(z, θ)} isCompact_singleton (by rintro q rfl; exact hzθ)
    exact HkIntegrand_intervalIntegral_le (H := R) (C := max C 0) hle (le_max_right _ _)
      hzθ.1 hzθ.2.1 hzθ.2.2
      (fun j i hji => (Work.FTS.StrongEps.aemeasurable_mixed_family hsmR hcont j i z θ hzθ).mono_measure
        (Measure.restrict_mono hsub le_rfl))
      (fun j i hji s hs =>
        le_trans (hC s (hsub hs) j i hji (z, θ) (Set.mem_singleton _)) (le_max_left _ _))
      (fun j i hji => slice_lip_slot_eq hcont hsmR hslotb hσ hσ' hle hzθ hji)
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
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 W z θ)
          ≤ ENNReal.ofReal ((σ - σ') * ∫ s in σ'..σ, Work.Spaces.HkIntegrand α 4 (R s) z θ) := by
    filter_upwards [hae_z] with z hz
    filter_upwards [hae_Ioo] with θ hθ
    exact ENNReal.ofReal_le_ofReal (hpoint z θ ⟨hz, hθ.1, hθ.2⟩)
  -- the chain
  have step1 : ENNReal.ofReal (Work.Spaces.HkSq α 4 W)
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 W z θ) := by
    rw [Work.Spaces.HkSq]
    exact (slice_lip_ofReal_integral_le_lintegral (μ := volume.restrict Work.Spaces.Iz)
        (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 W z θ)
        (fun z => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 W z θ)).trans
      (lintegral_mono fun z => slice_lip_ofReal_integral_le_lintegral
        (μ := volume.restrict Work.Spaces.Iθ) (f := fun θ => Work.Spaces.HkIntegrand α 4 W z θ)
        (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 W z θ))
  have step2 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 W z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((σ - σ') * ∫ s in σ'..σ, Work.Spaces.HkIntegrand α 4 (R s) z θ) := by
    refine lintegral_mono_ae ?_
    filter_upwards [haeθ] with z hz
    exact lintegral_mono_ae hz
  have step3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((σ - σ') * ∫ s in σ'..σ, Work.Spaces.HkIntegrand α 4 (R s) z θ))
      = ENNReal.ofReal (σ - σ') * ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (∫ s in σ'..σ, Work.Spaces.HkIntegrand α 4 (R s) z θ) := by
    have hinner : ∀ z : ℝ, (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((σ - σ') * ∫ s in σ'..σ, Work.Spaces.HkIntegrand α 4 (R s) z θ))
        = ENNReal.ofReal (σ - σ') * ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (∫ s in σ'..σ, Work.Spaces.HkIntegrand α 4 (R s) z θ) := by
      intro z
      simp only [ENNReal.ofReal_mul hΔ]
      rw [MeasureTheory.lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    simp only [hinner]
    rw [MeasureTheory.lintegral_const_mul']
    exact ENNReal.ofReal_ne_top
  have step4 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (∫ s in σ'..σ, Work.Spaces.HkIntegrand α 4 (R s) z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (R s) z θ) := by
    refine lintegral_mono fun z => lintegral_mono fun θ => ?_
    rw [slice_lip_intervalIntegral_eq_set hle (fun s => Work.Spaces.HkIntegrand α 4 (R s) z θ)]
    exact slice_lip_ofReal_integral_le_lintegral (μ := volume.restrict (Set.uIoc σ' σ))
      (f := fun s => Work.Spaces.HkIntegrand α 4 (R s) z θ)
      (fun s => Work.Spaces.HkIntegrand_nonneg α 4 (R s) z θ)
  have step5 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (R s) z θ))
      = ∫⁻ s in Set.uIoc σ' σ, ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (R s) z θ) :=
    slice_lip_tonelli hsmR hσ hσ' hle hmeasJ
  have step6 : (∫⁻ s in Set.uIoc σ' σ, ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (R s) z θ))
      = ∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (Work.Spaces.HkSq α 4 (R s)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    have hsingle : AEMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 (R s) p.1 p.2)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
      (Work.Spaces.aesm_of_continuousOn_Qd _
        ((hsmR s (hsub hs)).continuousOn_HkIntegrand α 4)).aemeasurable
    rw [(MeasureTheory.lintegral_prod (f := fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (R s) p.1 p.2))
      (ENNReal.measurable_ofReal.comp_aemeasurable hsingle)).symm]
    exact slice_lip_ofReal_HkSq_eq_lintegral (h4 s (hsub hs)) hsingle
  have step7 : (∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (Work.Spaces.HkSq α 4 (R s)))
      ≤ ∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (B * B) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    exact ENNReal.ofReal_le_ofReal
      (by simpa only [pow_two] using slice_lip_HkSq_le_sq (hb4 s (hsub hs)))
  have step8 : (∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (B * B))
      = ENNReal.ofReal (B * B) * ENNReal.ofReal (σ - σ') := by
    rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ, Real.volume_uIoc,
      abs_of_nonneg hΔ]
  have step9 : ENNReal.ofReal (σ - σ') * (ENNReal.ofReal (B * B) * ENNReal.ofReal (σ - σ'))
      = ENNReal.ofReal ((B * (σ - σ')) ^ 2) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hB hB), ← ENNReal.ofReal_mul hΔ]
    congr 1
    ring
  have hchain : ENNReal.ofReal (Work.Spaces.HkSq α 4 W) ≤ ENNReal.ofReal ((B * (σ - σ')) ^ 2) := by
    have h7 : (∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (Work.Spaces.HkSq α 4 (R s)))
        ≤ ENNReal.ofReal (B * B) * ENNReal.ofReal (σ - σ') := by
      rw [← step8]; exact step7
    have hmono : ENNReal.ofReal (σ - σ') * (∫⁻ s in Set.uIoc σ' σ,
          ENNReal.ofReal (Work.Spaces.HkSq α 4 (R s)))
        ≤ ENNReal.ofReal (σ - σ') * (ENNReal.ofReal (B * B) * ENNReal.ofReal (σ - σ')) := by
      gcongr
    calc ENNReal.ofReal (Work.Spaces.HkSq α 4 W)
        ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 W z θ) := step1
      _ ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((σ - σ') * ∫ s in σ'..σ,
              Work.Spaces.HkIntegrand α 4 (R s) z θ) := step2
      _ = ENNReal.ofReal (σ - σ') * ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (∫ s in σ'..σ, Work.Spaces.HkIntegrand α 4 (R s) z θ) := step3
      _ ≤ ENNReal.ofReal (σ - σ') * ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ∫⁻ s in Set.uIoc σ' σ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (R s) z θ) := by
          gcongr
      _ = ENNReal.ofReal (σ - σ') * ∫⁻ s in Set.uIoc σ' σ, ∫⁻ z in Work.Spaces.Iz,
            ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 (R s) z θ) := by
          rw [step5]
      _ = ENNReal.ofReal (σ - σ') * ∫⁻ s in Set.uIoc σ' σ,
            ENNReal.ofReal (Work.Spaces.HkSq α 4 (R s)) := by rw [step6]
      _ ≤ ENNReal.ofReal (σ - σ') * (ENNReal.ofReal (B * B) * ENNReal.ofReal (σ - σ')) := hmono
      _ = ENNReal.ofReal ((B * (σ - σ')) ^ 2) := step9
  -- conclusion
  have hsq : Work.Spaces.HkSq α 4 W ≤ (B * (σ - σ')) ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg (B * (σ - σ')))).mp hchain
  have hcongr : Work.Spaces.HkSq α 4
        (fun z θ => Work.FTS.Galerkin.slice g σ z θ - Work.FTS.Galerkin.slice g σ' z θ)
      = Work.Spaces.HkSq α 4 W :=
    Work.FTS.EllipticEst.HkSq_congr_open α 4 (f := fun z θ =>
        Work.FTS.Galerkin.slice g σ z θ - Work.FTS.Galerkin.slice g σ' z θ) (g := W)
      (fun z θ hz hθ0 hθ1 =>
        slice_lip_diff_eq_integral hsol hcont hσ hσ' hle z θ ⟨hz, hθ0, hθ1⟩)
  have hnorm_eq : Work.Spaces.HkNorm α 4
        (fun z θ => Work.FTS.Galerkin.slice g σ z θ - Work.FTS.Galerkin.slice g σ' z θ)
      = Work.Spaces.HkNorm α 4 W := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hcongr]
  rw [hnorm_eq]
  calc Work.Spaces.HkNorm α 4 W
      = Real.sqrt (Work.Spaces.HkSq α 4 W) := rfl
    _ ≤ Real.sqrt ((B * (σ - σ')) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = B * (σ - σ') := Real.sqrt_sq (mul_nonneg hB hΔ)


end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.DeltaSlotJeps =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000


end Work.FTS.StrongEps.EpsRLX
end
