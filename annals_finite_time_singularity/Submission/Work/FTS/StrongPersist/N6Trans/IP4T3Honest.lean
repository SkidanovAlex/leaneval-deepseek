import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.TraceAe
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T2Sup.srestBound
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.l12Slice_JfamP_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `l12Slice_JfamP_tendsto` — the pointwise convergence of the `L₁₂`-mode of the `JfamP`-slices

Along the `ε`-scheme (`ε n → 0`), the `L₁₂`-mode of the projected slices converges at every
`z ∈ Iz = [0,∞)`:

  `L₁₂ (slice (JfamP ρ (ε n) (G n)) s) z  ⟶  L₁₂ (slice g s) z`.

The two ingredients are

* the *pointwise* slot convergence `mixed_JfamP_tendsto` on the open quadrant, which via the
  dominated convergence theorem in `θ` (domination by `K θ · Maj σ / σ`, the pointwise bound
  `|f n σ θ| ≤ Maj σ` coming from the `EpsDecay` clause `SlotMaj 1 Maj …`) gives the a.e.
  convergence of the angular densities `s ↦ L12dens K (f n) s` on `(0,∞)`;
* the `L¹`-domination `‖L12dens K (f n) σ‖ ≤ Maj σ / σ` on `(0,∞)`, whose majorant is integrable
  by the `hMajint` clause of `EpsDecay`,

after which `L12_tendsto_of_dominated` (the dominated convergence theorem for the outer radial
integral `L₁₂ f z = ∫_{σ>z} L12dens K f σ dσ`) gives the conclusion.

Measurability of the densities is supplied by `Work.Spaces.aesm_of_continuousOn_Qd` (joint a.e.
strong measurability of a function continuous on the open quadrant) through
`AEStronglyMeasurable.integral_prod_right'`; the only regularity used is
`ClassC.reg : SmoothOpen (slice (JfamP …) s)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

/-! ## Two auxiliary lemmas -/

/-- **A.e. strong measurability of the angular density** from continuity of the datum on the
open quadrant: the joint integrand `(s,θ) ↦ K θ · Y s θ / s` is continuous on `Q0`, hence a.e.
strongly measurable for `(volume.restrict Iz).prod (volume.restrict Iθ)`
(`Work.Spaces.aesm_of_continuousOn_Qd`), and Fubini measurability of the partial integral
(`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`) gives the claim. -/
private lemma aesm_L12dens_of_continuousOn' {Y : ℝ → ℝ → ℝ}
    (hY : ContinuousOn (Function.uncurry Y) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.AEStronglyMeasurable (fun σ => Work.FM.L12dens Work.Spaces.K Y σ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Y p.1 p.2 / p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((continuous_K.comp continuous_snd).continuousOn.mul hY).div continuousOn_fst
      (fun p hp => ne_of_gt hp.1)
  have hjoint := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have h := hjoint.integral_prod_right' (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
  convert h using 1
  funext σ
  rfl

/-- **The `L¹`-domination of the density by a pointwise bound on the datum.**  If `|Y σ θ| ≤ C`
for every `θ` (in particular for `θ ∈ Iθ`) and `σ > 0`, then
`‖L12dens K Y σ‖ ≤ C / σ`: bound the set integral by the integral of the absolute value, use
`|K θ| = K θ` on `Iθ`, factor the constant out and `∫_{Iθ} K = 1` (`AngIntK`). -/
private lemma abs_L12dens_le_of_bound' {Y : ℝ → ℝ → ℝ} {C σ : ℝ} (hσ : 0 < σ)
    (hbd : ∀ θ : ℝ, |Y σ θ| ≤ C) :
    ‖Work.FM.L12dens Work.Spaces.K Y σ‖ ≤ C / σ := by
  have hKnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.Spaces.K θ := AngFacts.1
  have hInt : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * C / σ) Work.Spaces.Iθ :=
    (((continuous_K.mul continuous_const)).div_const σ).continuousOn.integrableOn_compact
      isCompact_Icc
  have hstep : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * Y σ θ / σ|)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * C / σ :=
    MeasureTheory.setIntegral_mono_of_nonneg (fun θ _ => abs_nonneg _)
      (fun θ hθ => by
        rw [abs_div, abs_mul, abs_of_nonneg (hKnn θ hθ), abs_of_pos hσ]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hbd θ) (hKnn θ hθ)) hσ.le)
      hInt
  have hfac : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * C / σ)
      = (C / σ) * ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
  calc ‖Work.FM.L12dens Work.Spaces.K Y σ‖
      = |Work.FM.L12dens Work.Spaces.K Y σ| := by rw [Real.norm_eq_abs]
    _ = |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Y σ θ / σ| := by
        simp only [Work.FM.L12dens, Work.Spaces.Iθ]
    _ ≤ ∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * Y σ θ / σ| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * C / σ := hstep
    _ = (C / σ) * ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ := hfac
    _ = C / σ := by rw [AngIntK, mul_one]

/-! ## The theorem -/

theorem l12Slice_JfamP_tendsto {α B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {s : ℝ} {Maj : ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice (G n) s)) Work.FTS.StrongEps.Quad)
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G n) s)
      (Work.FTS.Galerkin.slice g s))
    (hC : ∀ n : ℕ, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hMajint : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (hDec : ∀ n : ℕ, Work.FTS.StrongEps.EpsDecay α ρ Φs E (ε n) s (G n) Maj)
    (hl12 : Filter.Tendsto (fun n : ℕ => Work.Construction.L12
      (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) s)) 0)
      Filter.atTop (nhds 0)) :
    ∀ z ∈ Work.Spaces.Iz, Filter.Tendsto (fun n : ℕ => Work.Construction.L12
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z) Filter.atTop
      (nhds (Work.Construction.L12 (Work.FTS.Galerkin.slice g s) z)) := by
  intro z hz
  have hz0 : (0:ℝ) ≤ z := hz
  have hsub : Set.Ioi z ⊆ Work.Spaces.Iz := fun σ hσ => by
    simp only [Set.mem_Ioi] at hσ
    simp only [Work.Spaces.Iz, Set.mem_Ici]
    linarith
  have hKnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.Spaces.K θ := AngFacts.1
  -- **Measurability** of every density (a.e. strong measurability on `(0,∞)`, hence on `(z,∞)`).
  have hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun σ => Work.FM.L12dens Work.Spaces.K
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) σ)
      (MeasureTheory.volume.restrict (Set.Ioi z)) := by
    intro n
    exact (aesm_L12dens_of_continuousOn' ((hC n).reg.continuousOn)).mono_measure
      (MeasureTheory.Measure.restrict_mono hsub le_rfl)
  -- **Convergence of the densities** at every `σ > 0`, by dominated convergence in `θ`.
  have hconv_ae : ∀ᵐ σ ∂(MeasureTheory.volume.restrict (Set.Ioi z)),
      Filter.Tendsto (fun n : ℕ => Work.FM.L12dens Work.Spaces.K
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) σ)
        Filter.atTop (nhds (Work.FM.L12dens Work.Spaces.K (Work.FTS.Galerkin.slice g s) σ)) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun σ hσ => ?_)
    have hσ0 : (0:ℝ) < σ := by
      simp only [Set.mem_Ioi] at hσ
      linarith
    have hFmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => Work.Spaces.K θ *
          Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s σ θ / σ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      intro n
      have hslice : MeasureTheory.AEStronglyMeasurable
          (fun θ : ℝ => Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s σ θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        Work.Spaces.aesm_slice_of_continuousOn_Qd _ ((hC n).reg.continuousOn) hσ0
      have hKc : Continuous fun θ : ℝ => Work.Spaces.K θ / σ := continuous_K.div_const σ
      exact (hKc.aestronglyMeasurable.mul hslice).congr
        (Filter.Eventually.of_forall fun θ => by simp only [Pi.mul_apply]; ring)
    have hBint : MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.K θ * Maj σ / σ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (((continuous_K.mul continuous_const).div_const σ).continuousOn).integrableOn_compact
        isCompact_Icc
    have hBnd : ∀ n : ℕ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ‖Work.Spaces.K θ * Work.FTS.Galerkin.slice
            (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s σ θ / σ‖
          ≤ Work.Spaces.K θ * Maj σ / σ := by
      intro n
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      have hb : |Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s σ θ| ≤ Maj σ := by
        have h := (hDec n).2.2.2.1 σ hσ0 θ 0 0 (by norm_num)
        simpa using h
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (hKnn θ hθ), abs_of_pos hσ0]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (hKnn θ hθ)) hσ0.le
    have hLim : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Filter.Tendsto (fun n : ℕ => Work.Spaces.K θ *
            Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s σ θ / σ)
          Filter.atTop (nhds (Work.Spaces.K θ * Work.FTS.Galerkin.slice g s σ θ / σ)) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · -- `θ = 0`: both integrands vanish because `K 0 = 0`
        rw [← h0]
        have hK0 : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
        simp only [hK0, zero_mul, zero_div]
        exact tendsto_const_nhds
      · rcases eq_or_lt_of_le hθ.2 with h2 | h2
        · -- `θ = π/2`: both integrands vanish because `K (π/2) = 0`
          rw [h2]
          have hKp : Work.Spaces.K (Real.pi / 2) = 0 := by
            rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
          simp only [hKp, zero_mul, zero_div]
          exact tendsto_const_nhds
        · -- interior: the slot convergence of `mixed_JfamP_tendsto`, times `K θ / σ`
          have hp : (σ, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := ⟨hσ0, h0, h2⟩
          have h := Work.FTS.StrongEps.mixed_JfamP_tendsto hρ hsm hconv
            (fun n => (hε n).1) hε0 hl12 hp (j := 0) (i := 0) (by norm_num)
          simp only [Work.Spaces.mixed, Work.Spaces.DthIter_zero, Work.Spaces.DzIter_zero] at h
          exact (h.const_mul (Work.Spaces.K θ)).div_const σ
    have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (F := fun (n : ℕ) (θ : ℝ) => Work.Spaces.K θ *
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s σ θ / σ)
      (f := fun θ : ℝ => Work.Spaces.K θ * Work.FTS.Galerkin.slice g s σ θ / σ)
      (fun θ : ℝ => Work.Spaces.K θ * Maj σ / σ)
      hFmeas hBint hBnd hLim
    simpa only [Work.FM.L12dens, Work.Spaces.Iθ] using hdct
  -- **Domination** of every density by the integrable majorant `Maj σ / σ`.
  have hbdd : ∀ᵐ σ ∂(MeasureTheory.volume.restrict (Set.Ioi z)), ∀ n : ℕ,
      ‖Work.FM.L12dens Work.Spaces.K
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) σ‖
        ≤ Maj σ / σ := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun σ hσ => ?_)
    have hσ0 : (0:ℝ) < σ := by
      simp only [Set.mem_Ioi] at hσ
      linarith
    intro n
    exact abs_L12dens_le_of_bound' hσ0 (fun θ => by
      have h := (hDec n).2.2.2.1 σ hσ0 θ 0 0 (by norm_num)
      simpa using h)
  have hMint : MeasureTheory.Integrable (fun σ : ℝ => Maj σ / σ)
      (MeasureTheory.volume.restrict (Set.Ioi z)) :=
    hMajint.mono_set (fun σ hσ => by
      simp only [Set.mem_Ioi] at hσ ⊢
      linarith)
  exact Work.FTS.StrongEps.L12_tendsto_of_dominated (M := fun σ => Maj σ / σ) (ρ := z)
    hmeas hconv_ae hbdd hMint

end Work.FTS.StrongEps.E5Aux2
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.IP4T3Honest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false


end Work.FTS.StrongPersist.N6Trans
end
