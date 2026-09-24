import Mathlib
import Submission.Work.Drive.EnergyCover
import Submission.Work.Analysis.RiemannSurface.chartBall_open

/-!
# A *satisfiable* chart-ball cover with a partition of unity (repairs `Work.Drive.EnergyCover`)

## Why this file exists

`Work.Drive.EnergyCover` asks for a finite chart-ball cover with a partition of unity whose sum is
`1` on the union of the balls.  That is unsatisfiable when `Ω ≠ X` (see
`Submission/Work/Kernel/NOTES_exists_energyCover_REFUTED.md`); the repair is to ask for the partition
identity only on a *prescribed compact set* `K`, which this structure does.

## Why the fields are stated with `Submission.chartBall`

`chartAt ℂ y` is a **total** function `X → ℂ`; its values off its source are junk and, crucially, a
junk value may perfectly well land *inside* a ball around `(chartAt ℂ y) y`.  Hence a containment
such as

`(chartAt ℂ (y i)) ⁻¹' Metric.ball ((chartAt ℂ (y i)) (y i)) (ρ i) ⊆ (chartAt ℂ (y i)).source ∩ Ω`

is **false** for such a chart, for *every* positive radius: the junk point itself lies in the
preimage of the ball, but not in the source.  A charted space with this defect satisfies all the
hypotheses of the existence theorem (`Scratch/kernel/greenCover_refute.lean` **machine-checks** that
in such a space no `GreenCover` with the bare-preimage fields exists at all, even for `Ω = univ`).

Every field therefore mentions the source explicitly — `Submission.chartBall c a ρ = c.source ∩
c ⁻¹' Metric.ball a ρ` and `Submission.chartClosedBall c a ρ = c.source ∩ c ⁻¹' Metric.closedBall a
ρ` — exactly as in the workspace's `Submission.chartBall` (and as in
`Submission/Work/Drive/energyGreenCover.lean`, whose corrected structure is proved to be inhabited).
With the source intersected in, `chartClosedBall c (c y) s` is *compact* (and hence closed) as soon as
`Metric.closedBall (c y) s ⊆ c.target` (`Submission.isCompact_chartClosedBall`), which is exactly what
makes the bumps `β` constructible.

## The data

`Ω` is the region, `K` the compact set on which the partition of unity must add up to one, `a`
(resp. `b`) the pole carried by the distinguished chart `ia` (resp. `ib`).

Three radii per chart: `ψ i` is supported in the `s i`-ball, the bump `β i` is `≡ 1` on the closed
`s i`-ball and supported in the `σ i`-ball, and the differentiated functions are read in the `ρ i`-ball,
which lies in `Ω`.
-/

open Set Metric
open scoped Manifold Topology

noncomputable section

namespace Work.Kernel

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Corrected cover data for the energy route.**  All the chart balls are `source ∩ preimage` of a
Euclidean ball (`Submission.chartBall`, `Submission.chartClosedBall`), so that the junk values of
`chartAt` off the chart source can never be met. -/
structure GreenCover (ι : Type*) [Fintype ι] (Ω K : Set X) (a b : X) where
  y : ι → X
  s : ι → ℝ
  σ : ι → ℝ
  ρ : ι → ℝ
  ψ : ι → X → ℝ
  β : ι → X → ℝ
  ia : ι
  ib : ι
  hspos : ∀ i, 0 < s i
  hsσ : ∀ i, s i < σ i
  hσρ : ∀ i, σ i < ρ i
  htgt : ∀ i, Metric.ball ((chartAt ℂ (y i)) (y i)) (ρ i) ⊆ (chartAt ℂ (y i)).target
  hballΩ : ∀ i, Submission.chartBall (chartAt ℂ (y i)) ((chartAt ℂ (y i)) (y i)) (ρ i) ⊆ Ω
  hψnonneg : ∀ i x, 0 ≤ ψ i x
  hψsupp : ∀ i, tsupport (ψ i) ⊆
    Submission.chartBall (chartAt ℂ (y i)) ((chartAt ℂ (y i)) (y i)) (s i)
  /-- The partition identity, **on the prescribed compact set `K`**. -/
  hsum : ∀ x ∈ K, ∑ i, ψ i x = 1
  hψdiff : ∀ k i, Work.Drive.ChartDiff (chartAt ℂ (y k)) (ψ i) Ω
  ha_mem : a ∈ Submission.chartBall (chartAt ℂ (y ia)) ((chartAt ℂ (y ia)) (y ia)) (s ia)
  ha_nmem : ∀ i, i ≠ ia → a ∉
    Submission.chartClosedBall (chartAt ℂ (y i)) ((chartAt ℂ (y i)) (y i)) (σ i)
  hb_mem : b ∈ Submission.chartBall (chartAt ℂ (y ib)) ((chartAt ℂ (y ib)) (y ib)) (s ib)
  hb_nmem : ∀ i, i ≠ ib → b ∉
    Submission.chartClosedBall (chartAt ℂ (y i)) ((chartAt ℂ (y i)) (y i)) (σ i)
  hβone : ∀ i, ∀ x ∈
    Submission.chartClosedBall (chartAt ℂ (y i)) ((chartAt ℂ (y i)) (y i)) (s i), β i x = 1
  hβsupp : ∀ i, tsupport (β i) ⊆
    Submission.chartBall (chartAt ℂ (y i)) ((chartAt ℂ (y i)) (y i)) (σ i)
  hβdiff : ∀ k i, Work.Drive.ChartDiff (chartAt ℂ (y k)) (β i) Ω

namespace GreenCover

variable {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X} (E : GreenCover ι Ω K a b)

/-- `ψ i` vanishes off the `s i`-ball of its chart. -/
theorem ψ_eq_zero_of_notMem (i : ι) {x : X}
    (hx : x ∉ Submission.chartBall (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i)) (E.s i)) :
    E.ψ i x = 0 :=
  image_eq_zero_of_notMem_tsupport fun hmem => hx (E.hψsupp i hmem)

/-- `β i` vanishes off the `σ i`-ball of its chart. -/
theorem β_eq_zero_of_notMem (i : ι) {x : X}
    (hx : x ∉ Submission.chartBall (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i)) :
    E.β i x = 0 :=
  image_eq_zero_of_notMem_tsupport fun hmem => hx (E.hβsupp i hmem)

/-- The support of `ψ i` lies in the closed `s i`-disc, hence in the closed `σ i`-disc. -/
theorem tsupport_ψ_subset_chartClosedBall (i : ι) :
    tsupport (E.ψ i) ⊆
      Submission.chartClosedBall (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i) :=
  fun x hmem => by
    obtain ⟨hsrc, hball⟩ := E.hψsupp i hmem
    exact ⟨hsrc, (Metric.closedBall_subset_closedBall (E.hsσ i).le)
      (Metric.ball_subset_closedBall hball)⟩

/-- The topological support of `ψ i` lies in the `σ i`-ball of its chart. -/
theorem tsupport_ψ_subset_chartBall (i : ι) :
    tsupport (E.ψ i) ⊆
      Submission.chartBall (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i) :=
  fun x hmem => by
    obtain ⟨hsrc, hball⟩ := E.hψsupp i hmem
    exact ⟨hsrc, Metric.ball_subset_ball (E.hsσ i).le hball⟩

/-- The support of `β i` lies in the closed `σ i`-disc. -/
theorem tsupport_β_subset_chartClosedBall (i : ι) :
    tsupport (E.β i) ⊆
      Submission.chartClosedBall (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i) :=
  fun _ hmem => Submission.chartBall_subset_chartClosedBall _ _ _ (E.hβsupp i hmem)

/-- For `i ≠ ia` the weight `ψ i` vanishes on a neighbourhood of `a`. -/
theorem ψ_eq_zero_nhds_a (i : ι) (hi : i ≠ E.ia) : E.ψ i =ᶠ[𝓝 a] 0 := by
  have hnot : a ∉ tsupport (E.ψ i) := fun hmem =>
    E.ha_nmem i hi (E.tsupport_ψ_subset_chartClosedBall i hmem)
  filter_upwards [(isClosed_tsupport (E.ψ i)).isOpen_compl.mem_nhds hnot] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- For `i ≠ ib` the weight `ψ i` vanishes on a neighbourhood of `b`. -/
theorem ψ_eq_zero_nhds_b (i : ι) (hi : i ≠ E.ib) : E.ψ i =ᶠ[𝓝 b] 0 := by
  have hnot : b ∉ tsupport (E.ψ i) := fun hmem =>
    E.hb_nmem i hi (E.tsupport_ψ_subset_chartClosedBall i hmem)
  filter_upwards [(isClosed_tsupport (E.ψ i)).isOpen_compl.mem_nhds hnot] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- For `i ≠ ia` the bump `β i` vanishes on a neighbourhood of `a`. -/
theorem β_eq_zero_nhds_a (i : ι) (hi : i ≠ E.ia) : E.β i =ᶠ[𝓝 a] 0 := by
  have hnot : a ∉ tsupport (E.β i) := fun hmem =>
    E.ha_nmem i hi (E.tsupport_β_subset_chartClosedBall i hmem)
  filter_upwards [(isClosed_tsupport (E.β i)).isOpen_compl.mem_nhds hnot] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- For `i ≠ ib` the bump `β i` vanishes on a neighbourhood of `b`. -/
theorem β_eq_zero_nhds_b (i : ι) (hi : i ≠ E.ib) : E.β i =ᶠ[𝓝 b] 0 := by
  have hnot : b ∉ tsupport (E.β i) := fun hmem =>
    E.hb_nmem i hi (E.tsupport_β_subset_chartClosedBall i hmem)
  filter_upwards [(isClosed_tsupport (E.β i)).isOpen_compl.mem_nhds hnot] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- The bump of the distinguished chart `ia` is identically `1` near the pole `a`. -/
theorem β_ia_eq_one_nhds : E.β E.ia =ᶠ[𝓝 a] 1 := by
  have hopen : ∀ᶠ x in 𝓝 a, x ∈
      Submission.chartBall (chartAt ℂ (E.y E.ia)) ((chartAt ℂ (E.y E.ia)) (E.y E.ia))
        (E.s E.ia) :=
    (Submission.chartBall_isOpen _ _ _).mem_nhds E.ha_mem
  filter_upwards [hopen] with x hx
  exact E.hβone E.ia x (Submission.chartBall_subset_chartClosedBall _ _ _ hx)

/-- The bump of the distinguished chart `ib` is identically `1` near the pole `b`. -/
theorem β_ib_eq_one_nhds : E.β E.ib =ᶠ[𝓝 b] 1 := by
  have hopen : ∀ᶠ x in 𝓝 b, x ∈
      Submission.chartBall (chartAt ℂ (E.y E.ib)) ((chartAt ℂ (E.y E.ib)) (E.y E.ib))
        (E.s E.ib) :=
    (Submission.chartBall_isOpen _ _ _).mem_nhds E.hb_mem
  filter_upwards [hopen] with x hx
  exact E.hβone E.ib x (Submission.chartBall_subset_chartClosedBall _ _ _ hx)

/-- The weight of the distinguished chart `ia` is identically `1` near the pole `a` (given the
partition identity, which lives on `K`). -/
theorem ψ_ia_eq_one_nhds (hK : K ∈ 𝓝 a) : E.ψ E.ia =ᶠ[𝓝 a] 1 := by
  classical
  have h1 : ∀ᶠ x in 𝓝 a, ∀ i : ι, i ≠ E.ia → E.ψ i x = 0 :=
    Filter.eventually_all.mpr fun i => by
      by_cases hi : i = E.ia
      · exact Filter.Eventually.of_forall fun x h => absurd hi h
      · exact (E.ψ_eq_zero_nhds_a i hi).mono fun x hx _ => hx
  have h2 : ∀ᶠ x in 𝓝 a, ∑ i, E.ψ i x = 1 :=
    Filter.eventually_of_mem hK fun x hx => E.hsum x hx
  filter_upwards [h1, h2] with x hx hsum
  rw [Finset.sum_eq_single E.ia (fun i _ hi => hx i hi) (by simp)] at hsum
  exact hsum

/-- The weight of the distinguished chart `ib` is identically `1` near the pole `b`. -/
theorem ψ_ib_eq_one_nhds (hK : K ∈ 𝓝 b) : E.ψ E.ib =ᶠ[𝓝 b] 1 := by
  classical
  have h1 : ∀ᶠ x in 𝓝 b, ∀ i : ι, i ≠ E.ib → E.ψ i x = 0 :=
    Filter.eventually_all.mpr fun i => by
      by_cases hi : i = E.ib
      · exact Filter.Eventually.of_forall fun x h => absurd hi h
      · exact (E.ψ_eq_zero_nhds_b i hi).mono fun x hx _ => hx
  have h2 : ∀ᶠ x in 𝓝 b, ∑ i, E.ψ i x = 1 :=
    Filter.eventually_of_mem hK fun x hx => E.hsum x hx
  filter_upwards [h1, h2] with x hx hsum
  rw [Finset.sum_eq_single E.ib (fun i _ hi => hx i hi) (by simp)] at hsum
  exact hsum

/-- The partition identity on `K` at the pole `a`. -/
theorem ψ_ia_eq_one (haK : a ∈ K) : E.ψ E.ia a = 1 := by
  classical
  have h := E.hsum a haK
  rw [Finset.sum_eq_single E.ia (fun i _ hi => by
    have h0 : E.ψ i =ᶠ[𝓝 a] 0 := E.ψ_eq_zero_nhds_a i hi
    exact h0.self_of_nhds) (by simp)] at h
  exact h

/-- The partition identity on `K` at the pole `b`. -/
theorem ψ_ib_eq_one (hbK : b ∈ K) : E.ψ E.ib b = 1 := by
  classical
  have h := E.hsum b hbK
  rw [Finset.sum_eq_single E.ib (fun i _ hi => by
    have h0 : E.ψ i =ᶠ[𝓝 b] 0 := E.ψ_eq_zero_nhds_b i hi
    exact h0.self_of_nhds) (by simp)] at h
  exact h

end GreenCover

end Work.Kernel

end
