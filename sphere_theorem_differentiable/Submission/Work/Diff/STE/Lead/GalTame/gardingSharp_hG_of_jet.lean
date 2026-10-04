import Mathlib
import Submission.Work.Diff.STE.Lead.GalTame.Contracts
import Submission.Work.Diff.STE.Lead.mat_jet_uniform_bound
import Submission.Work.Diff.STE.Lead.deTurck_limit
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

/-- **Discharge the pointwise first-jet hypothesis of the sharp Gårding estimate.**

`Work.Diff.STE.Lead.GalTame.GardingSharpData D hLC k k₀` (verbatim the conclusion of
`GalTame/gardingSharp`) provides, for every section `h` that is `lam`-elliptic, `K`-bounded,
`smooth` **and** whose chart-matrix first jet is bounded by the same constant `K`
(`hjet : ∀ i c d r z, ‖z‖ ≤ 2 D.σ i → |pdR r (D.mat i h c d) z| ≤ K`), the differential Gårding
estimate `ENormB_pair k (P h) h ≤ -(lam'/2) ENormB (k+1) h + Cg (1 + ENormB k h)`.

The consumer `Work.Diff.STE.Lead.GalTame.galE_apriori_L2` only assumes `lam g₀ ≤ h ≤ K g₀` and the
level-`k₀` energy bound `D.ENormB k₀ h + D.ENormB 0 h ≤ B₀`; `hjet` is *not* part of its interface
and must be discharged here.  It follows from the energy bound alone:

* `Work.Diff.STE.Lead.BNorm_le_ENormB_uniform D k₀` gives `Cb ≥ 0` with
  `D.BNorm k₀ h ≤ Cb * (D.ENormB k₀ h + D.ENormB 0 h)` for every `h` whose periodised components
  are `C^{k₀}` (obtain them from `hsmooth : ChartData h` via
  `Work.Diff.STE.B3.R_contDiff_of_chartData` then
  `Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff`, plus `ContDiff.of_le le_top`);
* hence `D.BNorm k₀ h ≤ Cb * B₀`;
* `Work.Diff.STE.Lead.mat_jet_uniform_bound D k₀ hk₀ (Cb * B₀) (by positivity)` then gives a
  section-independent `Kjet > 0` with `|pdR r (D.mat i h c d) z| ≤ Kjet` for `‖z‖ ≤ 2 D.σ i`.

Now apply `GardingSharpData` at the *larger* constant `Kmax := max K Kjet`: the upper bound
`hub : h ≤ K g₀ ≤ Kmax g₀` survives (`0 ≤ g₀.inner x v v`), and `hjet` holds with `Kmax` because
`Kjet ≤ Kmax`.  The result is `Work.Diff.STE.Lead.GalTame.GardingData D hLC k k₀`, i.e. the datum
`hG` of `galE_apriori_L2`.  Constants are uniform in `h`, in `ε` and in the level-`k` energy. -/
theorem gardingSharp_hG_of_jet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k k₀ : ℕ)
    (hk : Module.finrank ℝ E + 4 ≤ k)
    (hk₀ : Module.finrank ℝ E + 4 < 2 * k₀)
    (hSharp : Work.Diff.STE.Lead.GalTame.GardingSharpData
      (I := I) (M := M) D hLC k k₀) :
    Work.Diff.STE.Lead.GalTame.GardingData (I := I) (M := M) D hLC k k₀ := by
  intro lam K B₀ hlam hK hB₀
  -- ## Step 1: `BNorm k₀` is bounded by the level-`k₀` energy, uniformly in the section
  obtain ⟨Cb, hCb0, hCbb⟩ :=
    Work.Diff.STE.Lead.BNorm_le_ENormB_uniform (I := I) (M := M) D k₀
  -- ## Step 2: a section-independent pointwise first-jet bound from a `BNorm` bound
  obtain ⟨Kjet, _hKjetpos, hKjetb⟩ :=
    Work.Diff.STE.Lead.mat_jet_uniform_bound (I := I) (M := M) D k₀ hk₀ (Cb * B₀)
      (mul_nonneg hCb0 hB₀)
  -- ## Step 3: apply the sharp datum at the larger constant `max K Kjet`
  set Kmax : ℝ := max K Kjet with hKmaxdef
  have hKmax : 0 < Kmax := by rw [hKmaxdef]; exact lt_of_lt_of_le hK (le_max_left K Kjet)
  obtain ⟨lam', Cg, hlam', hCg, hbound⟩ := hSharp lam Kmax B₀ hlam hKmax hB₀
  refine ⟨lam', Cg, hlam', hCg, ?_⟩
  intro h hsym hpos hsmooth hell hub hB
  -- the periodised components are smooth (`⊤`-smooth from `ChartData`, then weakened to level `k₀`)
  have hRsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b) :=
    Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hsmooth
  have hRper : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i h a b) ∧ Work.Diff.STE.Periodic1 (D.Rper i h a b) :=
    fun i a b =>
      Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i h a b
        (hRsm i a b)
  -- hence `BNorm k₀ h ≤ Cb * B₀`, and the pointwise first-jet bound holds with `Kjet`
  have hBN : D.BNorm k₀ h ≤ Cb * B₀ := by
    have h1 := hCbb h
      (fun i a b => (hRper i a b).1.of_le (WithTop.coe_le_coe.mpr le_top))
      (fun i a b => (hRper i a b).2)
    exact le_trans h1 (mul_le_mul_of_nonneg_left hB hCb0)
  have hjetK : ∀ (i : ι₀) (c d r : Fin (Module.finrank ℝ E))
      (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i →
      |Work.Diff.STE.pdR r (D.mat i h c d) z| ≤ Kmax := fun i c d r z hz =>
    le_trans (hKjetb h hsmooth hBN i c d r z hz) (by rw [hKmaxdef]; exact le_max_right K Kjet)
  -- the upper bound survives at the larger constant
  have hub' : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ Kmax * g₀.inner x v v := by
    intro x v
    have h0 : 0 ≤ g₀.inner x v v :=
      Work.Diff.STE.Lead.smet_inner_nonneg (I := I) (g₀ := g₀) v
    calc h x v v ≤ K * g₀.inner x v v := hub x v
      _ ≤ Kmax * g₀.inner x v v :=
          mul_le_mul_of_nonneg_right (by rw [hKmaxdef]; exact le_max_left K Kjet) h0
  exact hbound h hsym hpos hsmooth hell hub' hjetK hB

end Work.Diff.STE.Lead.GalTame
