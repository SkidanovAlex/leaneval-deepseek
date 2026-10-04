import Mathlib
import Submission.Work.Diff.STE.Lead.deTurck_bound
import Submission.Work.Diff.STE.Lead.coordBound
import Submission.Work.Diff.STE.Lead.BNorm_zero_le_of_pointwise
import Submission.Work.Diff.STE.B3.transport_Rres_contDiffOn
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.Lead.CoeffRepr

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The DeTurck sections of a `BNorm`-convergent family converge in `BNorm 0`

`Work.Diff.STE.Lead.deTurckSec_BNorm0_tendsto`: if the *jet-level* DeTurck operators `pPhiJetOf` of
a sequence of sections `hs m` converge to that of a limit section `U` **uniformly** on the region
`Ky i ∩ {ψ i ≥ c}` of every chart `i` (hypothesis `hA`), then the *composite* `H⁰` norm of the
difference of the DeTurck sections tends to `0`:

`D.BNorm 0 (P (hs m) - P U) → 0`.

## Route

`BNorm 0` is the `ℓ²`-type mass of the periodised localised components
`D.Rper i X a b = per(ψ i · √(dens i) · mat i X a b)`, so by the pointwise criterion
`Work.Diff.STE.Lead.BNorm_zero_le_of_pointwise` it suffices to bound the section
`X = P (hs m) - P U` pointwise in the `g₀`-norm by a constant times `ε m`, with `ε m → 0`.

* **The pointwise bound** (`deTurckSec_sub_pointwise_bound` below).  Fix `y ∈ M` and pick the chart
  `i` of maximal weight at `y` (`exists_max_chart`): then `ψ i (coord i y) ≥ (√(card ι₀))⁻¹ ≥ c`,
  `y` lies in the chart source, and the frame `e i` is `g₀`-orthonormal at `y`.  The chart expansion
  of the DeTurck operator (`deTurckOp_chart_expansion`) writes `P (hs m) y u v - P U y u v` as the
  double sum of the jet differences against the *coordinates* of `u`, `v` in the trivialisation at
  `x₀ i`; the coordinates are bounded by `B₀ √n √(g₀ u u)` (`coordCLM_bound`).  Since the point
  `coord i y` lies in `Ky i ∩ {ψ i ≥ c}`, the jet differences are bounded by `ε m`, whence
  `|X y u v| ≤ ε m · n² (B₀ √n)² √(g₀ u u) √(g₀ v v)`.
* **The convergence of `ε m`** is hypothesis `hA` (`TendstoUniformlyOn`, one chart and one matrix
  entry at a time, combined by `Filter.eventually_all` over finite index sets).
* The chart data of `X` is `ChartData_sub` of `chartData_deTurckSec`.
-/

namespace Work.Diff.STE.Lead

/-- **The absolute value of a double sum is bounded by `n²` times a uniform bound of the
summands.** -/
lemma abs_double_sum_le_of_bound {n : ℕ} (F : Fin n → Fin n → ℝ) (K : ℝ)
    (hF : ∀ k l, |F k l| ≤ K) :
    |∑ k : Fin n, ∑ l : Fin n, F k l| ≤ (n : ℝ) ^ 2 * K := by
  have h2 : ∀ k : Fin n, |∑ l : Fin n, F k l| ≤ (n : ℝ) * K := by
    intro k
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ l : Fin n, |F k l| ≤ ∑ _l : Fin n, K := Finset.sum_le_sum (fun l _ => hF k l)
      _ = (n : ℝ) * K := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc |∑ k : Fin n, ∑ l : Fin n, F k l|
      ≤ ∑ k : Fin n, |∑ l : Fin n, F k l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, (n : ℝ) * K := Finset.sum_le_sum (fun k _ => h2 k)
    _ = (n : ℝ) * ((n : ℝ) * K) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (n : ℝ) ^ 2 * K := by ring

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The pointwise bound for the difference of two DeTurck sections.**  If the jet-level DeTurck
operators of two sections `h`, `U` differ by at most `ε` on the region `Ky i ∩ {ψ i ≥ c}` of every
chart `i`, then the difference of the DeTurck sections is bounded pointwise by
`ε · n² (B₀ √n)²√(g₀ u u)√(g₀ v v)`. -/
lemma deTurckSec_sub_pointwise_bound
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (U : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hp : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (hUh : ∀ (x : M) (u v : TangentSpace I x), U x u v = U x v u)
    (hUp : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < U x v v)
    (hUm : Work.Diff.STE.D.ChartData (I := I) (M := M) U)
    (B₀ : ℝ) (hB₀nn : 0 ≤ B₀)
    (hB₀ : ∀ (i : ι₀) (a : Fin (Module.finrank ℝ E))
      (y : Fin (Module.finrank ℝ E) → ℝ),
      y ∈ Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i → ∀ j : Fin (Module.finrank ℝ E),
        |Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) (D.pt i y) j
          (D.e i a (D.pt i y))| ≤ B₀)
    (c : ℝ) (hc1 : c ≤ (Real.sqrt (Fintype.card ι₀))⁻¹)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hdiff : ∀ (i : ι₀) (k l : Fin (Module.finrank ℝ E))
      (z : Fin (Module.finrank ℝ E) → ℝ),
      z ∈ Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i → c ≤ D.psi i z →
      |Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ h (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) k l
        - Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ U (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) k l| ≤ ε)
    (y : M) (u v : TangentSpace I y) :
    |((Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hh hp hm
        - Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ U hUh hUp hUm) y u) v|
      ≤ ((Module.finrank ℝ E : ℝ) ^ 2 * (B₀ * Real.sqrt (Module.finrank ℝ E)) ^ 2 * ε)
        * Real.sqrt (g₀.inner y u u) * Real.sqrt (g₀.inner y v v) := by
  classical
  obtain ⟨i, hψmax, hψpos, hsrc, hσ, hON, hKy⟩ :=
    Work.Diff.STE.Lead.exists_max_chart (I := I) (M := M) D y
  have hc_le : c ≤ D.psi i (Work.Diff.STE.coord (I := I) (D.x₀ i) y) := le_trans hc1 hψmax
  have hhapp := Work.Diff.STE.D.deTurckSec_apply (I := I) (M := M) hLC g₀ h hh hp hm y u v
  have hUapp := Work.Diff.STE.D.deTurckSec_apply (I := I) (M := M) hLC g₀ U hUh hUp hUm y u v
  have hhexp := Work.Diff.STE.Lead.deTurckOp_chart_expansion (I := I) (M := M) hLC g₀ D h hh hp hm
    i hsrc u v
  have hUexp := Work.Diff.STE.Lead.deTurckOp_chart_expansion (I := I) (M := M) hLC g₀ D U hUh hUp hUm
    i hsrc u v
  have hkey : |((Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hh hp hm
        - Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ U hUh hUp hUm) y u) v|
      = |∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          (Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ h (D.x₀ i)
              ((extChartAt I (D.x₀ i)) y) k l
            - Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ U (D.x₀ i)
              ((extChartAt I (D.x₀ i)) y) k l)
          * ((Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) y k) u
              * (Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) y l) v)| := by
    rw [Pi.sub_apply, sub_apply, sub_apply, hhapp, hUapp, hhexp, hUexp]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [hkey]
  have hF : ∀ (k l : Fin (Module.finrank ℝ E)),
      |(Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ h (D.x₀ i)
            ((extChartAt I (D.x₀ i)) y) k l
          - Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ U (D.x₀ i)
            ((extChartAt I (D.x₀ i)) y) k l)
        * ((Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) y k) u
            * (Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) y l) v)|
      ≤ ε * (B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner y u u))
          * (B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner y v v)) := by
    intro k l
    have hd : |Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ h (D.x₀ i)
          ((extChartAt I (D.x₀ i)) y) k l
        - Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ U (D.x₀ i)
          ((extChartAt I (D.x₀ i)) y) k l| ≤ ε := by
      have h1 := hdiff i k l (Work.Diff.STE.coord (I := I) (D.x₀ i) y) hKy hc_le
      rwa [Work.Diff.STE.Lead.flatToE_coord (I := I) (M := M) D hsrc] at h1
    have hcu := Work.Diff.STE.Lead.coordCLM_bound (I := I) (M := M) D B₀ hB₀nn hB₀ i hsrc hON hKy
      u k
    have hcv := Work.Diff.STE.Lead.coordCLM_bound (I := I) (M := M) D B₀ hB₀nn hB₀ i hsrc hON hKy
      v l
    have hBu : 0 ≤ B₀ * Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner y u u) :=
      mul_nonneg (mul_nonneg hB₀nn (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    rw [abs_mul, abs_mul]
    refine le_trans (mul_le_mul hd (mul_le_mul hcu hcv (abs_nonneg _) hBu)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hε) (le_of_eq ?_)
    ring
  have hbound := abs_double_sum_le_of_bound
    (fun k l => (Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ h (D.x₀ i)
            ((extChartAt I (D.x₀ i)) y) k l
          - Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ U (D.x₀ i)
            ((extChartAt I (D.x₀ i)) y) k l)
        * ((Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) y k) u
            * (Work.Diff.STE.D.coordCLM (I := I) (M := M) (D.x₀ i) y l) v)) _ hF
  exact le_trans hbound (le_of_eq (by ring))

end Helpers

theorem deTurckSec_BNorm0_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (hs : ℕ → Work.Diff.STE.Bil (I := I) (M := M))
    (U : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (m : ℕ) (x : M) (u v : TangentSpace I x), (hs m) x u v = (hs m) x v u)
    (hpos : ∀ (m : ℕ) (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < (hs m) x v v)
    (hsm : ∀ m : ℕ, Work.Diff.STE.D.ChartData (I := I) (M := M) (hs m))
    (hsymU : ∀ (x : M) (u v : TangentSpace I x), U x u v = U x v u)
    (hposU : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < U x v v)
    (hsmU : Work.Diff.STE.D.ChartData (I := I) (M := M) U)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ (Real.sqrt (Fintype.card ι₀))⁻¹)
    (hA : ∀ (i : ι₀) (j l : Fin (Module.finrank ℝ E)),
      TendstoUniformlyOn
        (fun (m : ℕ) (z : Fin (Module.finrank ℝ E) → ℝ) =>
          Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ (hs m) (D.x₀ i)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) j l)
        (fun (z : Fin (Module.finrank ℝ E) → ℝ) =>
          Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ U (D.x₀ i)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) j l)
        Filter.atTop
        (Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i ∩
          {z : Fin (Module.finrank ℝ E) → ℝ | c ≤ D.psi i z})) :
    Filter.Tendsto (fun m : ℕ => D.BNorm 0
      (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (hs m) (hsym m) (hpos m) (hsm m)
        - Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ U hsymU hposU hsmU))
      Filter.atTop (nhds 0) := by
  classical
  -- the pointwise criterion and the uniform frame bound
  obtain ⟨C, hCnn, hC⟩ := Work.Diff.STE.Lead.BNorm_zero_le_of_pointwise (I := I) (M := M) D
  obtain ⟨B₀, hB₀nn, hB₀⟩ := Work.Diff.STE.Lead.coord_factor_uniform (I := I) (M := M) D
  set K : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * (B₀ * Real.sqrt (Module.finrank ℝ E)) ^ 2
    with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- the uniform convergence of the jet differences on `Ky i ∩ {ψ i ≥ c}`
  have hunif : ∀ η > 0, ∀ᶠ m : ℕ in Filter.atTop,
      ∀ (i : ι₀) (k l : Fin (Module.finrank ℝ E))
        (z : Fin (Module.finrank ℝ E) → ℝ),
        z ∈ Work.Diff.STE.D.psi.Ky (I := I) (M := M) D i → c ≤ D.psi i z →
        |Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ (hs m) (D.x₀ i)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) k l
          - Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ U (D.x₀ i)
            (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) k l| ≤ η := by
    intro η hη
    refine Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun k =>
      Filter.eventually_all.mpr (fun l => ?_)))
    have hh := (Metric.tendstoUniformlyOn_iff.mp (hA i k l)) η hη
    refine hh.mono (fun m hm z hz1 hz2 => ?_)
    have h2 := hm z ⟨hz1, hz2⟩
    rw [Real.dist_eq] at h2
    rw [abs_sub_comm]
    exact le_of_lt h2
  rw [Metric.tendsto_atTop]
  intro ε hε
  set Dc : ℝ := C * K ^ 2 with hDcdef
  have hDcnn : 0 ≤ Dc := by rw [hDcdef]; exact mul_nonneg hCnn (sq_nonneg K)
  have hDc2 : (0 : ℝ) < Dc + 2 := by linarith
  set η : ℝ := Real.sqrt (ε / (Dc + 2)) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]; exact Real.sqrt_pos.mpr (div_pos hε hDc2)
  have hη2 : η ^ 2 = ε / (Dc + 2) := by
    rw [hηdef]; exact Real.sq_sqrt (le_of_lt (div_pos hε hDc2))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hunif η hηpos)
  refine ⟨N, fun m hm => ?_⟩
  -- the pointwise bound and the chart smoothness of the difference
  have hpoint : ∀ (y : M) (u v : TangentSpace I y),
      |((Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (hs m) (hsym m) (hpos m) (hsm m)
        - Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ U hsymU hposU hsmU) y u) v|
      ≤ (K * η) * Real.sqrt (g₀.inner y u u) * Real.sqrt (g₀.inner y v v) := by
    intro y u v
    rw [hKdef]
    exact deTurckSec_sub_pointwise_bound (I := I) (M := M) D hLC (hs m) U (hsym m) (hpos m)
      (hsm m) hsymU hposU hsmU B₀ hB₀nn hB₀ c hc1 η hηpos.le (hN m hm) y u v
  have hchart : Work.Diff.STE.D.ChartData (I := I) (M := M)
      (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (hs m) (hsym m) (hpos m) (hsm m)
        - Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ U hsymU hposU hsmU) :=
    Work.Diff.STE.Lead.ChartData_sub _ _
      (Work.Diff.STE.B3.chartData_deTurckSec (I := I) (M := M) (g₀ := g₀) hLC (hs m) (hsym m)
        (hpos m) (hsm m))
      (Work.Diff.STE.B3.chartData_deTurckSec (I := I) (M := M) (g₀ := g₀) hLC U hsymU hposU hsmU)
  have hCbound := hC _ (K * η) (mul_nonneg hKnn hηpos.le) hpoint hchart
  have hBNnn : 0 ≤ D.BNorm 0
      (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (hs m) (hsym m) (hpos m) (hsm m)
        - Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ U hsymU hposU hsmU) := by
    simp only [Work.Diff.STE.B3Data.BNorm]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun a _ =>
      Finset.sum_nonneg (fun b _ => Work.Diff.STE.CSq_nonneg 0 _)))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hBNnn]
  refine lt_of_le_of_lt hCbound ?_
  calc C * (K * η) ^ 2 = Dc * η ^ 2 := by rw [hDcdef]; ring
    _ = Dc * (ε / (Dc + 2)) := by rw [hη2]
    _ < ε := by
        rw [← mul_div_assoc, div_lt_iff₀ hDc2]
        nlinarith [hε]

end Work.Diff.STE.Lead
