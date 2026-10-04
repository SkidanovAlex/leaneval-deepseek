import Mathlib
import Submission.Work.Diff.STE.Lead.smet_pos_of_BNorm_tendsto
import Submission.Work.Diff.STE.Lead.BNorm_J_sub_le_rho0
import Submission.Work.Diff.STE.Lead.galState_J_props
import Submission.Work.Diff.STE.Lead.Rper_contDiff
import Submission.Work.Diff.STE.B3.dens_lower_bound
import Submission.Work.Diff.STE.B3.densGood

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer STE / Lead: the positivity of the metric survives the Galerkin limit

Along the Galerkin scheme one has a sequence of sections `u m t` which are positive definite only
*after* the Friedrichs mollification: `λ g₀ ≤ J ρ (ε m) (u m t)`.  The Galerkin solutions converge
in the composite norms `D.BNorm k` to a limit `U t`, and `ε m → 0`.  This file shows that
`λ g₀ ≤ U t` in the limit.

Route.  `J ρ ε h - h` is bounded in the composite norm by `C ε BNorm (k+1) h`
(`Work.Diff.STE.Lead.BNorm_J_sub_le_rho0`), and `u m t → U t`.  Both pieces are differences of
sections, so the *uniform* pointwise bound of `Work.Diff.STE.Lead.pointwise_le_sqrt_BNorm_uniform`
turns their composite norms into pointwise ones:

  `|(w m) x v v - (z m) x v v| ≤ C √(D.BNorm k (w m - z m)) √(g₀(v,v)) √(g₀(v,v))`,

which tends to `0` as soon as `D.BNorm k (w m - z m) → 0`.  Hence
`(J ρ (ε m) (u m t)) x v v → (U t) x v v`, and the positivity passes to the limit.

The only structural inputs are that `ChartData` of a section gives smooth, `1`-periodic periodised
components (`Work.Diff.STE.Lead.Rper_contDiff_and_periodic`) and that these are preserved by
`J ρ ε` (`Work.Diff.STE.Lead.chartData_J_props`).
-/

namespace Work.Diff.STE.Lead

open Filter

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

/-- **Smoothness and `1`-periodicity of the periodised components pass to differences.**
`D.Rper i (X - Y) a b = D.Rper i X a b - D.Rper i Y a b` (`Work.Diff.STE.B3Data.Rper_sub`), and both
smoothness and `1`-periodicity are preserved by subtraction. -/
lemma Rper_sub_contDiff_periodic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (X Y : Work.Diff.STE.Bil (I := I) (M := M))
    (hX : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i X a b) ∧ Work.Diff.STE.Periodic1 (D.Rper i X a b))
    (hY : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i Y a b) ∧ Work.Diff.STE.Periodic1 (D.Rper i Y a b)) :
    ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (X - Y) a b)
        ∧ Work.Diff.STE.Periodic1 (D.Rper i (X - Y) a b) := by
  intro i a b
  rw [Work.Diff.STE.B3Data.Rper_sub D X Y i a b]
  refine ⟨(hX i a b).1.sub (hY i a b).1, ?_⟩
  intro j z
  simp only [Pi.sub_apply]
  rw [(hX i a b).2 j z, (hY i a b).2 j z]

/-- **Pointwise evaluation is continuous along a sequence converging in the composite norm.**
If `D.BNorm k (w m - z m) → 0` and the periodised components of the differences are smooth and
`1`-periodic, then `(w m) x v v - (z m) x v v → 0`, by the uniform pointwise bound
`|h x v v| ≤ C √(D.BNorm k h) √(g₀(v,v)) √(g₀(v,v))` of
`Work.Diff.STE.Lead.pointwise_le_sqrt_BNorm_uniform`. -/
lemma tendsto_sub_eval_of_BNorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (hk : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * k)
    (hdens : ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z)
    (w z : ℕ → Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ (m : ℕ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (w m - z m) a b)
        ∧ Work.Diff.STE.Periodic1 (D.Rper i (w m - z m) a b))
    (hconv : Filter.Tendsto (fun m : ℕ => D.BNorm k (w m - z m)) Filter.atTop (nhds 0))
    (x : M) (v : TangentSpace I x) :
    Filter.Tendsto (fun m : ℕ => (w m) x v v - (z m) x v v) Filter.atTop (nhds 0) := by
  obtain ⟨C, _hCnn, hCb⟩ := pointwise_le_sqrt_BNorm_uniform (I := I) (M := M) D k hk hdens
  have hbound : ∀ m : ℕ, |(w m) x v v - (z m) x v v|
      ≤ C * Real.sqrt (D.BNorm k (w m - z m)) * Real.sqrt (g₀.inner x v v)
        * Real.sqrt (g₀.inner x v v) := by
    intro m
    have h := hCb (w m - z m) (fun i a b => (hsm m i a b).1)
      (fun i a b => (hsm m i a b).2) x v v
    simpa only [Pi.sub_apply, ContinuousLinearMap.sub_apply] using h
  have hg : Filter.Tendsto (fun m : ℕ => C * Real.sqrt (D.BNorm k (w m - z m))
      * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) Filter.atTop (nhds 0) := by
    have hcont : Continuous (fun N : ℝ => C * Real.sqrt N
        * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := by
      continuity
    have h0 := (hcont.tendsto 0).comp hconv
    have hfun : ((fun N : ℝ => C * Real.sqrt N * Real.sqrt (g₀.inner x v v)
          * Real.sqrt (g₀.inner x v v)) ∘ fun m : ℕ => D.BNorm k (w m - z m))
        = (fun m : ℕ => C * Real.sqrt (D.BNorm k (w m - z m))
          * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := rfl
    simpa only [hfun, Real.sqrt_zero, mul_zero, zero_mul] using h0
  have habs : Filter.Tendsto (fun m : ℕ => |(w m) x v v - (z m) x v v|) Filter.atTop (nhds 0) :=
    squeeze_zero (fun m => abs_nonneg _) hbound hg
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habs

theorem limit_positivity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ0 : ρ 0 = 1) (hρb : ∀ y : Fin (Module.finrank ℝ E) → ℝ, ‖ρ y‖ ≤ 1)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (τ₀ lam : ℝ) (hτ₀ : 0 < τ₀) (hlam : 0 < lam)
    (k : ℕ) (hk : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * k)
    (hdens : ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z)
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hCD : ∀ (m : ℕ) (t : ℝ), Work.Diff.STE.D.ChartData (I := I) (M := M) (u m t))
    (ε : ℕ → ℝ) (hε : ∀ m : ℕ, ε m ∈ Set.Ioc (0 : ℝ) 1)
    (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (B : ℕ → ℝ) (hB : ∀ k : ℕ, 0 ≤ B k)
    (hBnd : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ k : ℕ, D.BNorm k (u m t) ≤ B k)
    (hpos : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ (x : M) (v : TangentSpace I x),
      lam * g₀.inner x v v ≤ (D.J ρ (ε m) (u m t)) x v v)
    (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hCDU : ∀ t : ℝ, Work.Diff.STE.D.ChartData (I := I) (M := M) (U t))
    (hconv : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) τ₀ → ∀ k : ℕ,
      Filter.Tendsto (fun m : ℕ => D.BNorm k (u m t - U t)) Filter.atTop (nhds 0)) :
    ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x),
      lam * g₀.inner x v v ≤ (U t) x v v := by
  intro t ht x v
  -- the level of `BNorm_J_sub_le_rho0` is stated for `finrank`, the one of the target for `card`
  have hk' : Module.finrank ℝ E < 2 * k := by simpa [Fintype.card_fin] using hk
  -- the uniform bound `J ρ ε h - h = O(ε)` in the composite norm
  obtain ⟨Cj, hCjnn, hCjb⟩ :=
    BNorm_J_sub_le_rho0 (I := I) (M := M) D ρ hρ0 hρb hρs k hk'
  have htIcc : t ∈ Set.Icc (0 : ℝ) τ₀ := Set.Ico_subset_Icc_self ht
  -- `ChartData` gives smooth, `1`-periodic periodised components
  have hRper : ∀ (Z : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) Z →
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ (⊤ : ℕ∞) (D.Rper i Z a b) ∧ Work.Diff.STE.Periodic1 (D.Rper i Z a b) :=
    fun Z hZ i a b => Rper_contDiff_and_periodic (I := I) (M := M) D Z hZ i a b
  -- **step A**: the mollification defect `J ρ (ε m) (u m t) - u m t` vanishes pointwise
  have hstepA : Filter.Tendsto
      (fun m : ℕ => (D.J ρ (ε m) (u m t)) x v v - (u m t) x v v) Filter.atTop (nhds 0) := by
    refine tendsto_sub_eval_of_BNorm (I := I) (M := M) D k hk hdens
      (fun m : ℕ => D.J ρ (ε m) (u m t)) (fun m : ℕ => u m t) ?_ ?_ x v
    · intro m i a b
      exact Rper_sub_contDiff_periodic (I := I) (M := M) D _ _
        (hRper _ (chartData_J_props (I := I) (M := M) D ρ hρb (ε m) (u m t) (hCD m t)))
        (hRper _ (hCD m t)) i a b
    · -- `D.BNorm k (J ρ (ε m) (u m t) - u m t) ≤ Cj ε m B (k+1) → 0`
      have hεC : Filter.Tendsto (fun m : ℕ => Cj * ε m * B (k + 1)) Filter.atTop (nhds 0) := by
        have h := hε0.const_mul (Cj * B (k + 1))
        have h' : (fun m : ℕ => Cj * B (k + 1) * ε m) = fun m : ℕ => Cj * ε m * B (k + 1) := by
          funext m; ring
        rw [h', mul_zero] at h
        exact h
      refine squeeze_zero (fun m => ?_) (fun m => ?_) hεC
      · simp only [Work.Diff.STE.B3Data.BNorm]
        exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
          Finset.sum_nonneg fun b _ => Work.Diff.STE.CSq_nonneg k _
      · have hsmR : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
            ContDiff ℝ (⊤ : ℕ∞) (D.R i (u m t) a b) :=
          Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D (u m t) (hCD m t)
        refine (hCjb (ε m) (hε m) (u m t) hsmR).trans ?_
        exact mul_le_mul_of_nonneg_left (hBnd m t htIcc (k + 1))
          (mul_nonneg hCjnn (hε m).1.le)
  -- **step B**: `u m t - U t → 0` pointwise, from the hypothesis `hconv`
  have hstepB : Filter.Tendsto
      (fun m : ℕ => (u m t) x v v - (U t) x v v) Filter.atTop (nhds 0) := by
    refine tendsto_sub_eval_of_BNorm (I := I) (M := M) D k hk hdens
      (fun m : ℕ => u m t) (fun _ : ℕ => U t) ?_ ?_ x v
    · intro m i a b
      exact Rper_sub_contDiff_periodic (I := I) (M := M) D _ _
        (hRper _ (hCD m t)) (hRper _ (hCDU t)) i a b
    · exact hconv t ht k
  -- assemble: `(J ρ (ε m) (u m t)) x v v → (U t) x v v`
  have hlim : Filter.Tendsto (fun m : ℕ => (D.J ρ (ε m) (u m t)) x v v) Filter.atTop
      (nhds ((U t) x v v)) := by
    have h2 : Filter.Tendsto (fun m : ℕ => ((D.J ρ (ε m) (u m t)) x v v - (u m t) x v v)
        + ((u m t) x v v - (U t) x v v)) Filter.atTop (nhds 0) := by
      have h := hstepA.add hstepB
      simpa using h
    have h3 := h2.add_const ((U t) x v v)
    have hfun : (fun m : ℕ => ((D.J ρ (ε m) (u m t)) x v v - (u m t) x v v)
        + ((u m t) x v v - (U t) x v v) + (U t) x v v)
        = fun m : ℕ => (D.J ρ (ε m) (u m t)) x v v := by
      funext m
      ring
    rw [hfun] at h3
    simpa using h3
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim (fun m => hpos m t htIcc x v)

end Work.Diff.STE.Lead
