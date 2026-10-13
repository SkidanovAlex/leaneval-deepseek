import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiaDefs
import Submission.Work.FTS.StrongPersist.EnergyStep
import Submission.Work.FTS.StrongEps.EpsE4Thr.cs_diag
import Submission.Work.FTS.StrongEps.EpsE4Thr.tendsto_slope_interval_integral
import Submission.Work.FTS.StrongEps.EpsE4Thr.aemeasurable_slice_continuousOn
import Submission.Work.FTS.StrongEps.EpsE4Thr.integrable_uncurry_of_bound
import Submission.Work.FTS.StrongEps.EpsE4Thr.ae_slice_lintegral_lt_top
import Submission.Work.FTS.StrongEps.EpsE4Thr.sq_integral_interval_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.aemeasurable_udot_slice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace Work.FTS.StrongEps.EpsE4Thr

/-! ## Auxiliary material for the `L²`-route derivative of the weighted square -/

/-! ### small generic helpers -/

/-- The AM–GM integrability: `G·H·ρ` is integrable as soon as `G²ρ` and `H²ρ` are and both
factors are a.e. measurable. -/
theorem integrable_amgm_mul {wt : ℝ → ℝ → ℝ} {G H : ℝ × ℝ → ℝ}
    (hρnn : ∀ᵐ p ∂diaM, 0 ≤ wt p.1 p.2)
    (hρmeas : AEMeasurable (fun p : ℝ × ℝ => wt p.1 p.2) diaM)
    (hG : MeasureTheory.Integrable (fun p => G p * G p * wt p.1 p.2) diaM)
    (hH : MeasureTheory.Integrable (fun p => H p * H p * wt p.1 p.2) diaM)
    (hGm : AEMeasurable G diaM) (hHm : AEMeasurable H diaM) :
    MeasureTheory.Integrable (fun p => G p * H p * wt p.1 p.2) diaM := by
  have hdom_eq : (fun p => ((G p * G p + H p * H p) / 2) * wt p.1 p.2)
      = fun p => ((G p * G p * wt p.1 p.2) + (H p * H p * wt p.1 p.2)) / 2 := by
    funext p; ring
  have hdom : MeasureTheory.Integrable
      (fun p => ((G p * G p + H p * H p) / 2) * wt p.1 p.2) diaM := by
    rw [hdom_eq]
    exact (hG.add hH).div_const 2
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun p => G p * H p * wt p.1 p.2) diaM :=
    ((hGm.mul hHm).mul hρmeas).aestronglyMeasurable
  refine hdom.mono' hmeas ?_
  filter_upwards [hρnn] with p hp
  have h1 : |G p * H p| ≤ (G p * G p + H p * H p) / 2 := by
    have h2 : 2 * |G p| * |H p| ≤ G p * G p + H p * H p := by
      nlinarith [sq_nonneg (|G p| - |H p|), sq_abs (G p), sq_abs (H p),
        abs_nonneg (G p), abs_nonneg (H p)]
    rw [abs_mul]
    linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
  exact mul_le_mul_of_nonneg_right h1 hp

/-- `(G - H)²ρ` is integrable when both `G²ρ` and `H²ρ` are. -/
theorem integrable_sub_sq {wt : ℝ → ℝ → ℝ} {G H : ℝ × ℝ → ℝ}
    (hρnn : ∀ᵐ p ∂diaM, 0 ≤ wt p.1 p.2)
    (hρmeas : AEMeasurable (fun p : ℝ × ℝ => wt p.1 p.2) diaM)
    (hG : MeasureTheory.Integrable (fun p => G p * G p * wt p.1 p.2) diaM)
    (hH : MeasureTheory.Integrable (fun p => H p * H p * wt p.1 p.2) diaM)
    (hGm : AEMeasurable G diaM) (hHm : AEMeasurable H diaM) :
    MeasureTheory.Integrable
      (fun p => (G p - H p) * (G p - H p) * wt p.1 p.2) diaM := by
  have hcross := integrable_amgm_mul hρnn hρmeas hG hH hGm hHm
  have heq : (fun p => (G p - H p) * (G p - H p) * wt p.1 p.2)
      = fun p => (G p * G p * wt p.1 p.2) - 2 * (G p * H p * wt p.1 p.2)
          + (H p * H p * wt p.1 p.2) := by
    funext p; ring
  rw [heq]
  exact (hG.sub (hcross.const_mul 2)).add hH

/-- The weighted Cauchy–Schwarz for the product measure. -/
theorem cs_diag_mup {wt : ℝ → ℝ → ℝ} {G H : ℝ × ℝ → ℝ}
    (hρnn : ∀ᵐ p ∂diaM, 0 ≤ wt p.1 p.2)
    (hG : MeasureTheory.Integrable (fun p => G p * G p * wt p.1 p.2) diaM)
    (hH : MeasureTheory.Integrable (fun p => H p * H p * wt p.1 p.2) diaM)
    (hGH : MeasureTheory.Integrable (fun p => G p * H p * wt p.1 p.2) diaM) :
    (∫ p, G p * H p * wt p.1 p.2 ∂diaM) ^ 2
      ≤ (∫ p, G p * G p * wt p.1 p.2 ∂diaM)
        * (∫ p, H p * H p * wt p.1 p.2 ∂diaM) :=
  cs_diag (μ := diaM) (ρ := fun p => wt p.1 p.2) (f := G) (g := H) hρnn hG hH hGH



/-- The AM–GM pointwise inequality `|a * b| ≤ (a * a + b * b) / 2`. -/
theorem abs_mul_le_half_sq (a b : ℝ) : |a * b| ≤ (a * a + b * b) / 2 := by
  have h2 : 2 * |a| * |b| ≤ a * a + b * b := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b]
  rw [abs_mul]
  linarith

/-! ## The `L²`-data bundle and the derived objects -/

/-- The diagonal of the profile family. -/
def diagPfun (ρ : ℝ → ℝ → ℝ) (u : ℝ → Work.FTS.Galerkin.Fn) : ℝ → ℝ :=
  fun s => ∫ p : ℝ × ℝ, u s p.1 p.2 * u s p.1 p.2 * ρ p.1 p.2 ∂diaM

/-- The square remainder of the Newton-Leibniz decomposition. -/
def diagArem (ρ : ℝ → ℝ → ℝ) (u : ℝ → Work.FTS.Galerkin.Fn) (τ : ℝ) : ℝ → ℝ :=
  fun s => (s - τ)⁻¹ * ∫ p : ℝ × ℝ,
    (u s p.1 p.2 - u τ p.1 p.2) * (u s p.1 p.2 - u τ p.1 p.2) * ρ p.1 p.2 ∂diaM

/-- The crossed remainder of the Newton-Leibniz decomposition. -/
def diagBrem (ρ : ℝ → ℝ → ℝ) (u : ℝ → Work.FTS.Galerkin.Fn) (τ : ℝ) : ℝ → ℝ :=
  fun s => (s - τ)⁻¹ * ∫ p : ℝ × ℝ,
    u τ p.1 p.2 * (u s p.1 p.2 - u τ p.1 p.2) * ρ p.1 p.2 ∂diaM

/-- The crossed pairing at the base time. -/
def diagQval (ρ : ℝ → ℝ → ℝ) (u udot : ℝ → Work.FTS.Galerkin.Fn) (τ : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM

/-- **The `L²`-data of a curve and of its derivative family.**  All the hypotheses of the
`L²`-route derivative of `s ↦ ∫ p, u s p ^ 2 ρ p`, repackaged together with the elementary
consequences used by the proof (the `*`-form of the diagonal integrabilities, the a.e.
measurability of the time slices, and a window `(τ - δ, τ + δ) ⊆ (0, T)` with `δ ≤ τ / 2`). -/
structure DiagData (ρ : ℝ → ℝ → ℝ) (u udot : ℝ → Work.FTS.Galerkin.Fn) (τ T : ℝ) where
  hτ : τ ∈ Set.Ioo 0 T
  hτ1 : 0 < τ
  hτ2 : τ < T
  K : ℝ
  K_nonneg : 0 ≤ K
  ρmeas : AEMeasurable (Function.uncurry ρ) diaM
  wmeas : AEMeasurable (fun p : ℝ × ℝ => ρ p.1 p.2) diaM
  ρnn : ∀ᵐ p ∂diaM, 0 ≤ ρ p.1 p.2
  diag : ∀ s ∈ Set.Icc (0 : ℝ) T,
    MeasureTheory.Integrable (fun p : ℝ × ℝ => u s p.1 p.2 * u s p.1 p.2 * ρ p.1 p.2) diaM
  diagd : ∀ s ∈ Set.Icc (0 : ℝ) T,
    MeasureTheory.Integrable (fun p : ℝ × ℝ => udot s p.1 p.2 * udot s p.1 p.2 * ρ p.1 p.2) diaM
  diagd_sq : ∀ s ∈ Set.Icc (0 : ℝ) T,
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (udot s p.1 p.2) ^ 2 * ρ p.1 p.2) diaM
  bdd : ∀ σ ∈ Set.Icc (0 : ℝ) T,
    ∫ p : ℝ × ℝ, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2 ∂diaM ≤ K
  bdd_sq : ∀ σ ∈ Set.Icc (0 : ℝ) T,
    ∫ p : ℝ × ℝ, (udot σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM ≤ K
  aesm : MeasureTheory.AEStronglyMeasurable
    (fun q : ℝ × (ℝ × ℝ) => u q.1 q.2.1 q.2.2)
    (MeasureTheory.volume.prod diaM)
  aesmd : MeasureTheory.AEStronglyMeasurable
    (fun q : ℝ × (ℝ × ℝ) => udot q.1 q.2.1 q.2.2)
    (MeasureTheory.volume.prod diaM)
  deriv : ∀ᵐ p ∂diaM, ∀ s ∈ Set.Ioo (0 : ℝ) T,
    HasDerivAt (fun t : ℝ => u t p.1 p.2) (udot s p.1 p.2) s
  cont : ∀ᵐ p ∂diaM, ContinuousOn (fun s : ℝ => u s p.1 p.2) (Set.Icc 0 T)
  contU : Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ,
    (udot σ p.1 p.2 - udot τ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM) (nhds τ) (nhds 0)
  umeas : ∀ σ ∈ Set.Ioo (0 : ℝ) T, AEMeasurable (fun p : ℝ × ℝ => u σ p.1 p.2) diaM
  dmeas : ∀ σ ∈ Set.Ioo (0 : ℝ) T, AEMeasurable (fun p : ℝ × ℝ => udot σ p.1 p.2) diaM
  δ : ℝ
  δ_pos : 0 < δ
  δ_half : δ ≤ τ / 2
  δ_T : τ + δ < T

theorem DiagData.hτIcc {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Work.FTS.Galerkin.Fn} {τ T : ℝ}
    (D : DiagData ρ u udot τ T) : τ ∈ Set.Icc (0 : ℝ) T :=
  ⟨le_of_lt D.hτ1, le_of_lt D.hτ2⟩

theorem DiagData.δ_ab {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Work.FTS.Galerkin.Fn} {τ T : ℝ}
    (D : DiagData ρ u udot τ T) : τ - D.δ ≤ τ + D.δ := by
  have := D.δ_pos; linarith

theorem DiagData.δ_pos' {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Work.FTS.Galerkin.Fn} {τ T : ℝ}
    (D : DiagData ρ u udot τ T) : 0 < τ - D.δ := by
  have h1 := D.δ_half; have h2 := D.hτ1; linarith

theorem DiagData.δ_mem {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Work.FTS.Galerkin.Fn} {τ T : ℝ}
    (D : DiagData ρ u udot τ T) :
    Set.Ioo (τ - D.δ) (τ + D.δ) ∈ nhds τ :=
  Ioo_mem_nhds (by have h := D.δ_pos; linarith) (by have h1 := D.δ_pos; have h2 := D.δ_T; linarith)

theorem DiagData.Ioc_mem {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Work.FTS.Galerkin.Fn} {τ T : ℝ}
    (D : DiagData ρ u udot τ T) :
    Set.Ioc (τ - D.δ) (τ + D.δ) ⊆ Set.Icc (0 : ℝ) T := by
  intro x hx
  rw [Set.mem_Ioc] at hx
  exact ⟨by linarith [hx.1, D.δ_pos'], by linarith [hx.2, D.δ_T]⟩

theorem DiagData.Ioo_mem {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Work.FTS.Galerkin.Fn} {τ T : ℝ}
    (D : DiagData ρ u udot τ T) :
    Set.Ioo (τ - D.δ) (τ + D.δ) ⊆ Set.Ioo (0 : ℝ) T := by
  intro x hx
  rw [Set.mem_Ioo] at hx
  exact ⟨by linarith [hx.1, D.δ_pos'], by linarith [hx.2, D.δ_T]⟩

/-- The data bundle built from the raw hypotheses of the `L²`-route derivative. -/
noncomputable def DiagData.of_raw {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Work.FTS.Galerkin.Fn}
    {τ T : ℝ}
    (hT : 0 ≤ T) (hτ : τ ∈ Set.Ioo 0 T)
    (hρmeas : AEMeasurable (Function.uncurry ρ) diaM)
    (hρnn : ∀ᵐ p ∂diaM, 0 ≤ ρ p.1 p.2)
    (hdiag : ∀ s ∈ Set.Icc (0 : ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (u s p.1 p.2) ^ 2 * ρ p.1 p.2) diaM)
    (hdiagd : ∀ s ∈ Set.Icc (0 : ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (udot s p.1 p.2) ^ 2 * ρ p.1 p.2) diaM)
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => u q.1 q.2.1 q.2.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod diaM))
    (hmeasd : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => udot q.1 q.2.1 q.2.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod diaM))
    (hderiv : ∀ᵐ p ∂diaM, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun t : ℝ => u t p.1 p.2) (udot s p.1 p.2) s)
    (hcont : ∀ᵐ p ∂diaM, ContinuousOn (fun s : ℝ => u s p.1 p.2) (Set.Icc 0 T))
    (hK : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T,
      ∫ p : ℝ × ℝ, (udot σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM ≤ K)
    (hcontU : Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ,
        (udot σ p.1 p.2 - udot τ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM) (nhds τ) (nhds 0)) :
    DiagData ρ u udot τ T := by
  set K : ℝ := hK.choose with hKdef
  have hK0 : 0 ≤ K := hK.choose_spec.1
  have hKbd : ∀ σ ∈ Set.Icc (0 : ℝ) T,
      ∫ p : ℝ × ℝ, (udot σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM ≤ K := hK.choose_spec.2
  have hτ1 : 0 < τ := hτ.1
  have hτ2 : τ < T := hτ.2
  have hdiag' : ∀ s ∈ Set.Icc (0 : ℝ) T,
      MeasureTheory.Integrable (fun p : ℝ × ℝ => u s p.1 p.2 * u s p.1 p.2 * ρ p.1 p.2) diaM := by
    intro s hs
    refine (hdiag s hs).congr (Eventually.of_forall fun p => ?_)
    simp only [pow_two]
  have hdiagd' : ∀ s ∈ Set.Icc (0 : ℝ) T,
      MeasureTheory.Integrable (fun p : ℝ × ℝ => udot s p.1 p.2 * udot s p.1 p.2 * ρ p.1 p.2) diaM := by
    intro s hs
    refine (hdiagd s hs).congr (Eventually.of_forall fun p => ?_)
    simp only [pow_two]
  have hKbd' : ∀ σ ∈ Set.Icc (0 : ℝ) T,
      ∫ p : ℝ × ℝ, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2 ∂diaM ≤ K := by
    intro σ hσ
    have h1 : (∫ p : ℝ × ℝ, udot σ p.1 p.2 * udot σ p.1 p.2 * ρ p.1 p.2 ∂diaM)
        = ∫ p : ℝ × ℝ, (udot σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM :=
      integral_congr_ae (Eventually.of_forall (fun p => by simp only [pow_two]))
    rw [h1]
    exact hKbd σ hσ
  have hu_meas : ∀ σ ∈ Set.Ioo (0 : ℝ) T, AEMeasurable (fun p : ℝ × ℝ => u σ p.1 p.2) diaM := by
    intro σ hσ
    refine aemeasurable_slice_continuousOn (F := fun t (p : ℝ × ℝ) => u t p.1 p.2)
      (a := σ / 2) (b := (σ + T) / 2) (τ := σ) ?_ ?_ ?_ ?_
    · linarith [hσ.1]
    · linarith [hσ.2]
    · exact hmeas.aemeasurable
    · filter_upwards [hcont] with p hp
      refine hp.mono ?_
      intro x hx
      rw [Set.mem_Icc] at hx
      exact ⟨by linarith [hx.1, hσ.1], by linarith [hx.2, hσ.2]⟩
  have hudot_meas : ∀ σ ∈ Set.Ioo (0 : ℝ) T,
      AEMeasurable (fun p : ℝ × ℝ => udot σ p.1 p.2) diaM :=
    fun σ hσ => aemeasurable_udot_slice hσ hu_meas hderiv
  refine ⟨hτ, hτ1, hτ2, K, hK0, hρmeas, hρmeas, hρnn, hdiag', hdiagd', hdiagd, hKbd', hKbd,
    hmeas, hmeasd, hderiv, hcont, hcontU, hu_meas, hudot_meas,
    min (τ / 2) ((T - τ) / 2), ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · exact min_le_left _ _
  · have h := min_le_right (τ / 2) ((T - τ) / 2); linarith

end Work.FTS.StrongEps.EpsE4Thr
