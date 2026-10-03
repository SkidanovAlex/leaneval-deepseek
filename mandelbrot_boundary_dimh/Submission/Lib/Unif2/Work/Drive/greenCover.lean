import Mathlib
import Submission.Lib.Unif2.Work.Drive.energyGreenRung
import Submission.Lib.Unif2.Work.Drive.EnergyCover

/-!
# The chart partition-of-unity datum for the chart-wise energy route to `gA b = gB a`

This module fixes the geometric input of the chart-wise energy route to the symmetry of the Green
function (`NOTES_energyRoute_chartwise.md`):

* `Work.Drive.GreenCover ι Ω a b U` — a finite family of charts `chartAt ℂ (y i)`, three radii
  `s i < σ i < ρ i`, a smooth partition of unity `ψ i` subordinate to the chart balls of radius
  `s i`, and "bumps" `β i` which are `≡ 1` on `tsupport (ψ i)` and supported in the ball of radius
  `σ i`.  The partition of unity sums to `1` on the *open* set `U`, and all the chart balls of
  radius `ρ i` are contained in `Ω`.

The bumps `β` are what makes `Work.Drive.pairTerm_transfer` applicable to a weight supported in one
chart only: the product `ψ i * β k` is supported in the intersection of the two chart balls, hence
in the overlap of the two chart sources.

Special charts: `y ia = a` and `y ib = b` (the *preferred* charts at the poles), and
`a ∉ tsupport (ψ i)` for `i ≠ ia`, `b ∉ tsupport (ψ i)` for `i ≠ ib`.
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- **The chart partition-of-unity datum.** -/
structure GreenCover (ι : Type*) [Fintype ι] (Ω : Set X) (a b : X) (U : Set X) where
  y : ι → X
  s : ι → ℝ
  σ : ι → ℝ
  ρ : ι → ℝ
  ψ : ι → X → ℝ
  β : ι → X → ℝ
  ia : ι
  ib : ι
  hya : y ia = a
  hyb : y ib = b
  hΩo : IsOpen Ω
  hUo : IsOpen U
  hUΩ : U ⊆ Ω
  haU : a ∈ U
  hbU : b ∈ U
  hspos : ∀ i, 0 < s i
  hsσ : ∀ i, s i < σ i
  hσρ : ∀ i, σ i < ρ i
  htgt : ∀ i, Metric.ball ((chartAt ℂ (y i)) (y i)) (ρ i) ⊆ (chartAt ℂ (y i)).target
  hballΩ : ∀ i, (chartAt ℂ (y i)).source ∩
    (chartAt ℂ (y i)) ⁻¹' Metric.ball ((chartAt ℂ (y i)) (y i)) (ρ i) ⊆ Ω
  hballsrc : ∀ i, (chartAt ℂ (y i)).source ∩
    (chartAt ℂ (y i)) ⁻¹' Metric.ball ((chartAt ℂ (y i)) (y i)) (ρ i) ⊆
    (chartAt ℂ (y i)).source
  hψnonneg : ∀ i x, 0 ≤ ψ i x
  hψsupp : ∀ i, tsupport (ψ i) ⊆ (chartAt ℂ (y i)).source ∩
    (chartAt ℂ (y i)) ⁻¹' Metric.ball ((chartAt ℂ (y i)) (y i)) (s i)
  hψsrc : ∀ i, tsupport (ψ i) ⊆ (chartAt ℂ (y i)).source
  hψdiff : ∀ k i, ChartDiff (chartAt ℂ (y k)) (ψ i) Ω
  hψc1 : ∀ k i, ∀ x ∈ (chartAt ℂ (y k)).source,
    ContDiffAt ℝ 1 ((ψ i) ∘ (chartAt ℂ (y k)).symm) ((chartAt ℂ (y k)) x)
  hsum : ∀ x ∈ U, ∑ i, ψ i x = 1
  ha_nmem : ∀ i, i ≠ ia → a ∉ tsupport (ψ i)
  hb_nmem : ∀ i, i ≠ ib → b ∉ tsupport (ψ i)
  hβone : ∀ i, ∀ x ∈ tsupport (ψ i), β i x = 1
  hβsupp : ∀ i, tsupport (β i) ⊆ (chartAt ℂ (y i)).source ∩
    (chartAt ℂ (y i)) ⁻¹' Metric.ball ((chartAt ℂ (y i)) (y i)) (σ i)
  hβsrc : ∀ i, tsupport (β i) ⊆ (chartAt ℂ (y i)).source
  hβdiff : ∀ k i, ChartDiff (chartAt ℂ (y k)) (β i) Ω
  hβc1 : ∀ k i, ∀ x ∈ (chartAt ℂ (y k)).source,
    ContDiffAt ℝ 1 ((β i) ∘ (chartAt ℂ (y k)).symm) ((chartAt ℂ (y k)) x)
  hβ_a_nmem : ∀ i, i ≠ ia → a ∉ tsupport (β i)
  hβ_b_nmem : ∀ i, i ≠ ib → b ∉ tsupport (β i)

namespace GreenCover

variable {ι : Type*} [Fintype ι] {Ω : Set X} {a b : X} {U : Set X} (E : GreenCover ι Ω a b U)

/-- `ψ ia` is identically `1` near `a`. -/
theorem ψ_ia_eq_one_nhds : E.ψ E.ia =ᶠ[𝓝 a] 1 := by
  have h1 : ∀ᶠ x in 𝓝 a, ∀ i : ι, i ≠ E.ia → E.ψ i x = 0 :=
    Filter.eventually_all.mpr fun i => by
      by_cases hi : i = E.ia
      · exact Filter.Eventually.of_forall fun x h => absurd hi h
      · have hnot : a ∉ tsupport (E.ψ i) := E.ha_nmem i hi
        filter_upwards [(isClosed_tsupport (E.ψ i)).isOpen_compl.mem_nhds hnot] with x hx _
        exact image_eq_zero_of_notMem_tsupport hx
  have h2 : ∀ᶠ x in 𝓝 a, ∑ i, E.ψ i x = 1 :=
    Filter.eventually_of_mem (E.hUo.mem_nhds E.haU) fun x hx => E.hsum x hx
  filter_upwards [h1, h2] with x hx hsum
  rw [Finset.sum_eq_single E.ia (fun i _ hi => hx i hi) (by simp)] at hsum
  exact hsum

/-- `ψ ib` is identically `1` near `b`. -/
theorem ψ_ib_eq_one_nhds : E.ψ E.ib =ᶠ[𝓝 b] 1 := by
  have h1 : ∀ᶠ x in 𝓝 b, ∀ i : ι, i ≠ E.ib → E.ψ i x = 0 :=
    Filter.eventually_all.mpr fun i => by
      by_cases hi : i = E.ib
      · exact Filter.Eventually.of_forall fun x h => absurd hi h
      · have hnot : b ∉ tsupport (E.ψ i) := E.hb_nmem i hi
        filter_upwards [(isClosed_tsupport (E.ψ i)).isOpen_compl.mem_nhds hnot] with x hx _
        exact image_eq_zero_of_notMem_tsupport hx
  have h2 : ∀ᶠ x in 𝓝 b, ∑ i, E.ψ i x = 1 :=
    Filter.eventually_of_mem (E.hUo.mem_nhds E.hbU) fun x hx => E.hsum x hx
  filter_upwards [h1, h2] with x hx hsum
  rw [Finset.sum_eq_single E.ib (fun i _ hi => hx i hi) (by simp)] at hsum
  exact hsum

/-- For `i ≠ ia` the weight `ψ i` vanishes on a neighbourhood of `a`. -/
theorem ψ_eq_zero_nhds_a (i : ι) (hi : i ≠ E.ia) : E.ψ i =ᶠ[𝓝 a] 0 := by
  have hnot : a ∉ tsupport (E.ψ i) := E.ha_nmem i hi
  filter_upwards [(isClosed_tsupport (E.ψ i)).isOpen_compl.mem_nhds hnot] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- For `i ≠ ib` the weight `ψ i` vanishes on a neighbourhood of `b`. -/
theorem ψ_eq_zero_nhds_b (i : ι) (hi : i ≠ E.ib) : E.ψ i =ᶠ[𝓝 b] 0 := by
  have hnot : b ∉ tsupport (E.ψ i) := E.hb_nmem i hi
  filter_upwards [(isClosed_tsupport (E.ψ i)).isOpen_compl.mem_nhds hnot] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- `tsupport (ψ i)` is contained in the source of the chart `i`. -/
theorem tsupport_ψ_subset_source (i : ι) : tsupport (E.ψ i) ⊆ (chartAt ℂ (E.y i)).source :=
  E.hψsrc i

/-- `tsupport (β i)` is contained in the source of the chart `i`. -/
theorem tsupport_β_subset_source (i : ι) : tsupport (E.β i) ⊆ (chartAt ℂ (E.y i)).source :=
  E.hβsrc i

/-- The weight `ψ i * β k` is supported in the overlap of the two chart sources. -/
theorem tsupport_mul_subset_inter (i k : ι) :
    tsupport (E.ψ i * E.β k) ⊆ (chartAt ℂ (E.y i)).source ∩ (chartAt ℂ (E.y k)).source := by
  intro x hx
  exact ⟨E.tsupport_ψ_subset_source i (tsupport_mul_subset_left (f := E.ψ i) (g := E.β k) hx),
    E.tsupport_β_subset_source k (tsupport_mul_subset_right (f := E.ψ i) (g := E.β k) hx)⟩

/-- The sum of the weights is `1` near every point of `U`. -/
theorem sum_eq_one_nhds {x : X} (hx : x ∈ U) : ∀ᶠ z in 𝓝 x, ∑ i, E.ψ i z = 1 :=
  Filter.eventually_of_mem (E.hUo.mem_nhds hx) fun z hz => E.hsum z hz

end GreenCover

end Work.Drive
