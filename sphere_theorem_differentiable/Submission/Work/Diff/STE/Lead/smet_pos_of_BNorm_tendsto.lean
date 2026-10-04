import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.Pointwise
import Submission.Work.Diff.STE.Lead.BNorm_tendsto_of_coeff_tendsto
import Submission.Work.Diff.STE.Lead.pointwise_le_sqrt_BNorm_uniform

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

open Filter

theorem smet_pos_of_BNorm_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (τ₀ lam : ℝ) (k : ℕ)
    (hk : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * k)
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hsmu : ∀ (m : ℕ) (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (u m t) a b))
    (hperu : ∀ (m : ℕ) (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.Periodic1 (D.Rper i (u m t) a b))
    (hsmU : ∀ (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (U t) a b))
    (hperU : ∀ (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.Periodic1 (D.Rper i (U t) a b))
    (hdens : ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z)
    (hpos : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ₀ → ∀ (x : M) (v : TangentSpace I x),
      lam * g₀.inner x v v ≤ (u m t) x v v)
    (hconv : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k' : ℕ,
      Filter.Tendsto (fun m : ℕ => D.BNorm k' (u m t - U t)) Filter.atTop (nhds 0)) :
    ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x),
      lam * g₀.inner x v v ≤ (U t) x v v := by
  intro t ht x v
  -- the uniform pointwise bound: a constant valid for *every* section whose periodised localised
  -- components are smooth and `1`-periodic.  (The constant of `B3Data.pointwise_bound` depends on
  -- the section and cannot be used in a limit argument.)
  obtain ⟨C, hC, hCb⟩ :=
    pointwise_le_sqrt_BNorm_uniform (I := I) (M := M) D k hk hdens
  -- the periodised components of the difference are smooth and periodic
  have hsm_sub : ∀ (m : ℕ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (u m t - U t) a b) := by
    intro m i a b
    rw [B3Data.Rper_sub D (u m t) (U t) i a b]
    exact (hsmu m t i a b).sub (hsmU t i a b)
  have hper_sub : ∀ (m : ℕ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.Periodic1 (D.Rper i (u m t - U t) a b) := by
    intro m i a b
    rw [B3Data.Rper_sub D (u m t) (U t) i a b]
    intro j z
    simp only [Pi.sub_apply]
    rw [hperu m t i a b j z, hperU t i a b j z]
  -- the pointwise difference is bounded by `C √(BNorm k (u m t - U t)) · g₀(v,v)`
  have hdiff : ∀ m : ℕ,
      |(u m t) x v v - (U t) x v v|
        ≤ C * Real.sqrt (D.BNorm k (u m t - U t)) * Real.sqrt (g₀.inner x v v)
          * Real.sqrt (g₀.inner x v v) := by
    intro m
    have h := hCb (u m t - U t) (hsm_sub m) (hper_sub m) x v v
    simpa only [Pi.sub_apply, ContinuousLinearMap.sub_apply] using h
  -- the right-hand side is continuous in the norm and the norm tends to `0`
  have hN : Tendsto (fun m : ℕ => D.BNorm k (u m t - U t)) atTop (nhds 0) := hconv t ht k
  have hg : Tendsto (fun m : ℕ => C * Real.sqrt (D.BNorm k (u m t - U t))
      * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) atTop (nhds 0) := by
    have hcont : Continuous (fun N : ℝ => C * Real.sqrt N
        * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := by
      continuity
    have h0 := (hcont.tendsto 0).comp hN
    have hfun : ((fun N : ℝ => C * Real.sqrt N * Real.sqrt (g₀.inner x v v)
          * Real.sqrt (g₀.inner x v v)) ∘ fun m : ℕ => D.BNorm k (u m t - U t))
        = (fun m : ℕ => C * Real.sqrt (D.BNorm k (u m t - U t))
          * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := by
      funext m; rfl
    simpa only [hfun, Real.sqrt_zero, mul_zero, zero_mul] using h0
  -- hence the difference tends to `0`
  have habs : Tendsto (fun m : ℕ => |(u m t) x v v - (U t) x v v|) atTop (nhds 0) :=
    squeeze_zero (fun m => abs_nonneg _) (fun m => hdiff m) hg
  have hzero : Tendsto (fun m : ℕ => (u m t) x v v - (U t) x v v) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have hval : Tendsto (fun m : ℕ => (u m t) x v v) atTop (nhds ((U t) x v v)) := by
    have h := hzero.add_const ((U t) x v v)
    simpa only [sub_add_cancel, zero_add] using h
  -- pass the positivity inequality to the limit
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hval (fun m => hpos m t ht x v)

end Work.Diff.STE.Lead
