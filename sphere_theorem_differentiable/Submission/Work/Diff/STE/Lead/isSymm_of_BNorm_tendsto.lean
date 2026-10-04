import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.Lead.pointwise_le_sqrt_BNorm_uniform
import Submission.Work.Diff.STE.B3.dens_lower_bound
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.Lead.Rper_contDiff
import Submission.Work.Diff.STE.Lead.CoeffRepr

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

/-!
# Symmetry of the limit section of the Galerkin scheme

The Galerkin scheme of the short-time-existence proof produces a sequence `u m` of symmetric
sections whose subsequence `u (φ m)` converges to a limit section `U` in every composite norm
`D.BNorm k`, i.e.

  `D.BNorm k (u (φ m) - U) ⟶ 0`  for every `k`.

Since, for a Sobolev level `k` with `card (Fin (finrank ℝ E)) < 2 k`, the composite norm controls
the *pointwise* value of a section by

  `|h x p q| ≤ C √(D.BNorm k h) · √(g₀.inner x p p) · √(g₀.inner x q q)`

(`Work.Diff.STE.Lead.pointwise_le_sqrt_BNorm_uniform`, which needs the uniform positive lower bound
for the chart densities of `D` — supplied by `Work.Diff.STE.B3.densGood` and
`Work.Diff.STE.B3.dens_lower_bound`), the difference `u (φ m) - U` tends to `0` pointwise, so the
pointwise symmetry of the `u m` passes to `U`.
-/

theorem isSymm_of_BNorm_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (u : ℕ → Work.Diff.STE.Bil (I := I) (M := M))
    (U : Work.Diff.STE.Bil (I := I) (M := M)) (φ : ℕ → ℕ)
    (hsm : ∀ m : ℕ, Work.Diff.STE.D.ChartData (I := I) (M := M) (u m))
    (hsmU : Work.Diff.STE.D.ChartData (I := I) (M := M) U)
    (hsym : ∀ (m : ℕ) (x : M) (p q : TangentSpace I x), u m x p q = u m x q p)
    (hconv : ∀ k : ℕ, Filter.Tendsto (fun m : ℕ => D.BNorm k (u (φ m) - U))
      Filter.atTop (nhds 0)) :
    ∀ (x : M) (p q : TangentSpace I x), U x p q = U x q p := by
  intro x p q
  -- a Sobolev level `k` for which the composite norm dominates the pointwise value
  have hk : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * (Module.finrank ℝ E + 1) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨C, _hC, hCb⟩ :=
    pointwise_le_sqrt_BNorm_uniform (I := I) (M := M) D (Module.finrank ℝ E + 1) hk
      (Work.Diff.STE.B3.dens_lower_bound (I := I) (M := M) D
        (fun i => Work.Diff.STE.B3.densGood (I := I) (M := M) D i))
  -- the differences of a smooth pair are chart-smooth
  have hCD : ∀ m : ℕ, Work.Diff.STE.D.ChartData (I := I) (M := M) (u (φ m) - U) :=
    fun m => ChartData_sub (I := I) (M := M) (u (φ m)) U (hsm (φ m)) hsmU
  -- hence their localised periodised components are smooth and `1`-periodic
  have hsmp : ∀ m : ℕ, (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (u (φ m) - U) a b)) ∧
      (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        Work.Diff.STE.Periodic1 (D.Rper i (u (φ m) - U) a b)) :=
    fun m => ⟨fun i a b => (Rper_contDiff_and_periodic (I := I) (M := M) D _
        (hCD m) i a b).1,
      fun i a b => (Rper_contDiff_and_periodic (I := I) (M := M) D _ (hCD m) i a b).2⟩
  -- pointwise convergence of the differences to `0`
  have hdiff : ∀ (z : M) (r s : TangentSpace I z),
      Filter.Tendsto (fun m : ℕ => (u (φ m) - U) z r s) Filter.atTop (nhds 0) := by
    intro z r s
    have hbound : ∀ m : ℕ, |(u (φ m) - U) z r s| ≤
        C * Real.sqrt (D.BNorm (Module.finrank ℝ E + 1) (u (φ m) - U))
          * Real.sqrt (g₀.inner z r r) * Real.sqrt (g₀.inner z s s) :=
      fun m => hCb (u (φ m) - U) (hsmp m).1 (hsmp m).2 z r s
    have hsqrt : Filter.Tendsto (fun m : ℕ =>
        Real.sqrt (D.BNorm (Module.finrank ℝ E + 1) (u (φ m) - U)))
        Filter.atTop (nhds 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp (hconv (Module.finrank ℝ E + 1))
      simpa only [Function.comp_def, Real.sqrt_zero] using h
    have hRHS : Filter.Tendsto (fun m : ℕ =>
        C * Real.sqrt (D.BNorm (Module.finrank ℝ E + 1) (u (φ m) - U))
          * Real.sqrt (g₀.inner z r r) * Real.sqrt (g₀.inner z s s))
        Filter.atTop (nhds 0) := by
      have h := ((hsqrt.const_mul C).mul_const (Real.sqrt (g₀.inner z r r))).mul_const
        (Real.sqrt (g₀.inner z s s))
      simpa using h
    have h0 : Filter.Tendsto (fun m : ℕ => |(u (φ m) - U) z r s|) Filter.atTop (nhds 0) :=
      squeeze_zero (fun m => abs_nonneg _) hbound hRHS
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using h0
  -- the two limits of `u (φ m) x p q`
  have hlim1 : Filter.Tendsto (fun m : ℕ => u (φ m) x p q) Filter.atTop (nhds (U x p q)) := by
    have h := (hdiff x p q).add_const (U x p q)
    have heq : (fun m : ℕ => (u (φ m) - U) x p q + U x p q) = fun m : ℕ => u (φ m) x p q := by
      funext m
      simp
    rw [heq] at h
    simpa using h
  have hlim2 : Filter.Tendsto (fun m : ℕ => u (φ m) x p q) Filter.atTop (nhds (U x q p)) := by
    have h' : Filter.Tendsto (fun m : ℕ => u (φ m) x q p) Filter.atTop (nhds (U x q p)) := by
      have h := (hdiff x q p).add_const (U x q p)
      have heq : (fun m : ℕ => (u (φ m) - U) x q p + U x q p) = fun m : ℕ => u (φ m) x q p := by
        funext m
        simp
      rw [heq] at h
      simpa using h
    have hcongr : (fun m : ℕ => u (φ m) x q p) =ᶠ[Filter.atTop]
        (fun m : ℕ => u (φ m) x p q) :=
      Filter.Eventually.of_forall (fun m => hsym (φ m) x q p)
    exact (Filter.tendsto_congr' hcongr).mp h'
  exact tendsto_nhds_unique hlim1 hlim2

end Work.Diff.STE.Lead
