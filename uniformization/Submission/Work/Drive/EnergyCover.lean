import Mathlib
import Submission.Work.Drive.greenEnergyPairing

/-!
# The cover data for the Dirichlet-energy route to the symmetry of the Green function

This module fixes the combinatorial/geometric input of the energy route
(`Submission/Work/Drive/NOTES_greenSymmetryRegion_route.md`, Appendix 6):

* `Work.Drive.ChartDiff c f Ω` — the chart representative of `f` in the chart `c` is differentiable
  at every point of `Ω ∩ c.source` (this is the "smoothness in a chart" that the transfer lemma
  `Work.Drive.pairTerm_transfer` asks for);
* `Work.Drive.EnergyCover ι Ω a b` — a finite chart-ball cover of `Ω`, with a partition of unity
  `ψ`, with *two distinguished charts* (`ia` around `a`, `ib` around `b`) and with a family of
  "bumps" `β k` that are `≡ 1` on the whole smaller ball of chart `k`.

The bumps are the device that makes `pairTerm_transfer` applicable to a weight supported in one
chart only: the product `ψ i * β k` is supported in the intersection of chart `i`'s and chart `k`'s
balls, which is exactly what the transfer lemma needs (see Appendix 6, §6.2 step 3).
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- `ChartDiff c f Ω`: the chart representative `w ↦ f (c.symm w)` of `f` is differentiable at the
image under `c` of every point of `Ω` that lies in the source of `c`. -/
def ChartDiff (c : OpenPartialHomeomorph X ℂ) (f : X → ℝ) (Ω : Set X) : Prop :=
  ∀ x ∈ Ω ∩ c.source, DifferentiableAt ℝ (fun w : ℂ => f (c.symm w)) (c x)

/-- **The cover data of the Dirichlet-energy route.**  With `c i := chartAt ℂ (y i)`:

* three radii `s i < σ i < ρ i`: `ψ i` is supported in the ball of radius `s i`, the bump `β i` is
  `≡ 1` on the *closed* ball of radius `s i` and supported in the ball of radius `σ i`, and the
  differentiated functions are read in the ball of radius `ρ i` (so that the clamped pullbacks are
  `C¹` with compact support);
* `ψ i` is a nonnegative smooth function with `∑ i, ψ i = 1` on `Ω`;
* `ia` (resp. `ib`) is the unique index whose `σ`-ball does not meet the *closed* `σ`-ball of any
  other index, and `a` (resp. `b`) lies in the smaller ball of `ia` (whence `ψ ia = 1` near `a`, and
  `ψ i = 0` near `a` for `i ≠ ia`). -/
structure EnergyCover (ι : Type*) [Fintype ι] (Ω : Set X) (a b : X) where
  y : ι → X
  s : ι → ℝ
  σ : ι → ℝ
  ρ : ι → ℝ
  ψ : ι → X → ℝ
  β : ι → X → ℝ
  ia : ι
  ib : ι
  hΩo : IsOpen Ω
  hspos : ∀ i, 0 < s i
  hsσ : ∀ i, s i < σ i
  hσρ : ∀ i, σ i < ρ i
  htgt : ∀ i, Metric.ball ((chartAt ℂ (y i)) (y i)) (ρ i) ⊆ (chartAt ℂ (y i)).target
  hballΩ : ∀ i, (chartAt ℂ (y i)) ⁻¹' Metric.ball ((chartAt ℂ (y i)) (y i)) (ρ i) ⊆ Ω
  hψnonneg : ∀ i x, 0 ≤ ψ i x
  hψsupp : ∀ i, tsupport (ψ i) ⊆
    (chartAt ℂ (y i)) ⁻¹' Metric.ball ((chartAt ℂ (y i)) (y i)) (s i)
  hsum : ∀ x ∈ ⋃ i, ((chartAt ℂ (y i)).source ∩
      (chartAt ℂ (y i)) ⁻¹' Metric.ball ((chartAt ℂ (y i)) (y i)) (s i)), ∑ i, ψ i x = 1
  hψdiff : ∀ k i, ChartDiff (chartAt ℂ (y k)) (ψ i) Ω
  ha_mem : a ∈ (chartAt ℂ (y ia)).source ∩
    (chartAt ℂ (y ia)) ⁻¹' Metric.ball ((chartAt ℂ (y ia)) (y ia)) (s ia)
  ha_nmem : ∀ i, i ≠ ia → a ∉ (chartAt ℂ (y i)) ⁻¹' Metric.closedBall ((chartAt ℂ (y i)) (y i)) (σ i)
  hb_mem : b ∈ (chartAt ℂ (y ib)).source ∩
    (chartAt ℂ (y ib)) ⁻¹' Metric.ball ((chartAt ℂ (y ib)) (y ib)) (s ib)
  hb_nmem : ∀ i, i ≠ ib → b ∉ (chartAt ℂ (y i)) ⁻¹' Metric.closedBall ((chartAt ℂ (y i)) (y i)) (σ i)
  hβone : ∀ i, ∀ x ∈ (chartAt ℂ (y i)) ⁻¹' Metric.closedBall ((chartAt ℂ (y i)) (y i)) (s i),
    β i x = 1
  hβsupp : ∀ i, tsupport (β i) ⊆
    (chartAt ℂ (y i)) ⁻¹' Metric.ball ((chartAt ℂ (y i)) (y i)) (σ i) ∩ (chartAt ℂ (y i)).source
  hβdiff : ∀ k i, ChartDiff (chartAt ℂ (y k)) (β i) Ω

namespace EnergyCover

variable {ι : Type*} [Fintype ι] {Ω : Set X} {a b : X} (E : EnergyCover ι Ω a b)

/-- `ψ i` vanishes identically off the `s`-ball of chart `i`. -/
theorem ψ_eq_zero_of_notMem (i : ι) {x : X}
    (hx : x ∉ (chartAt ℂ (E.y i)) ⁻¹' Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.s i)) :
    E.ψ i x = 0 :=
  image_eq_zero_of_notMem_tsupport fun hmem => hx (E.hψsupp i hmem)

/-- `β i` vanishes identically off the `σ`-ball of chart `i`. -/
theorem β_eq_zero_of_notMem (i : ι) {x : X}
    (hx : x ∉ (chartAt ℂ (E.y i)) ⁻¹' Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i)) :
    E.β i x = 0 :=
  image_eq_zero_of_notMem_tsupport fun hmem => hx (E.hβsupp i hmem).1

/-- For `i ≠ ia` the weight `ψ i` vanishes on a neighbourhood of `a`. -/
theorem ψ_eq_zero_nhds_a (i : ι) (hi : i ≠ E.ia) : E.ψ i =ᶠ[𝓝 a] 0 := by
  have hnot : a ∉ tsupport (E.ψ i) := fun hmem =>
    E.ha_nmem i hi (Set.mem_preimage.mpr (Metric.mem_closedBall.mpr
      (le_of_lt (lt_of_lt_of_le (Metric.mem_ball.mp (Set.mem_preimage.mp (E.hψsupp i hmem)))
        (E.hsσ i).le))))
  filter_upwards [(isClosed_tsupport (E.ψ i)).isOpen_compl.mem_nhds hnot] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- For `i ≠ ib` the weight `ψ i` vanishes on a neighbourhood of `b`. -/
theorem ψ_eq_zero_nhds_b (i : ι) (hi : i ≠ E.ib) : E.ψ i =ᶠ[𝓝 b] 0 := by
  have hnot : b ∉ tsupport (E.ψ i) := fun hmem =>
    E.hb_nmem i hi (Set.mem_preimage.mpr (Metric.mem_closedBall.mpr
      (le_of_lt (lt_of_lt_of_le (Metric.mem_ball.mp (Set.mem_preimage.mp (E.hψsupp i hmem)))
        (E.hsσ i).le))))
  filter_upwards [(isClosed_tsupport (E.ψ i)).isOpen_compl.mem_nhds hnot] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- For `i ≠ ia` the bump `β i` vanishes near `a`. -/
theorem β_eq_zero_nhds_a (i : ι) (hi : i ≠ E.ia) : E.β i =ᶠ[𝓝 a] 0 := by
  have hnot : a ∉ tsupport (E.β i) := fun hmem =>
    E.ha_nmem i hi (Metric.ball_subset_closedBall (Set.mem_preimage.mp (E.hβsupp i hmem).1))
  filter_upwards [(isClosed_tsupport (E.β i)).isOpen_compl.mem_nhds hnot] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- For `i ≠ ib` the bump `β i` vanishes near `b`. -/
theorem β_eq_zero_nhds_b (i : ι) (hi : i ≠ E.ib) : E.β i =ᶠ[𝓝 b] 0 := by
  have hnot : b ∉ tsupport (E.β i) := fun hmem =>
    E.hb_nmem i hi (Metric.ball_subset_closedBall (Set.mem_preimage.mp (E.hβsupp i hmem).1))
  filter_upwards [(isClosed_tsupport (E.β i)).isOpen_compl.mem_nhds hnot] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- The weight `ψ ia` is identically `1` near `a`. -/
theorem ψ_ia_eq_one_nhds : E.ψ E.ia =ᶠ[𝓝 a] 1 := by
  have haΩ : a ∈ Ω := E.hballΩ E.ia
    ((Metric.ball_subset_ball (le_of_lt (lt_trans (E.hsσ E.ia) (E.hσρ E.ia)))) E.ha_mem.2)
  have haW : a ∈ ⋃ i, ((chartAt ℂ (E.y i)).source ∩
      (chartAt ℂ (E.y i)) ⁻¹' Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.s i)) :=
    Set.mem_iUnion.mpr ⟨E.ia, E.ha_mem⟩
  have h1 : ∀ᶠ x in 𝓝 a, ∀ i : ι, i ≠ E.ia → E.ψ i x = 0 :=
    Filter.eventually_all.mpr fun i => by
      by_cases hi : i = E.ia
      · exact Filter.Eventually.of_forall fun x h => absurd hi h
      · filter_upwards [E.ψ_eq_zero_nhds_a i hi] with x hx _
        exact hx
  have h2 : ∀ᶠ x in 𝓝 a, ∑ i, E.ψ i x = 1 := by
    have hWopen : IsOpen (⋃ i, ((chartAt ℂ (E.y i)).source ∩
        (chartAt ℂ (E.y i)) ⁻¹' Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.s i))) :=
      isOpen_iUnion fun i => (chartAt ℂ (E.y i)).isOpen_inter_preimage Metric.isOpen_ball
    filter_upwards [hWopen.mem_nhds haW] with x hx
    exact E.hsum x hx
  filter_upwards [h1, h2] with x hx hsum
  rw [Finset.sum_eq_single E.ia (fun i _ hi => hx i hi) (by simp)] at hsum
  exact hsum

end EnergyCover

end Work.Drive
