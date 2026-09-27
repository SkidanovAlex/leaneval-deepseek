import Mathlib
import Submission.Work.EQ.meromorphic_order_nonneg_of_bounded

/-!
# Boundedness and analyticity of the normal form `toMeromorphicNFOn G {0}ᶜ` far from `0`

Let `G : ℂ → ℂ` be meromorphic at every `u ≠ 0` and bounded by `B` on the exterior disc
`R < ‖u‖`.  Then on the strictly larger exterior domain `max R 1 < ‖u‖` the normal form
`Ĝ = toMeromorphicNFOn G {0}ᶜ` is analytic and still bounded by `max B 0`.

Two independent facts are combined.

*On the punctured neighbourhood `0 < ‖·‖`.*  For `u ≠ 0`, the normal form `Ĝ` agrees with `G` on
the punctured neighbourhood of `u`, so it has there the same meromorphic order as `G`.  Since
`R < ‖u‖` is an *open* condition, `G` is bounded by `B` on a whole neighbourhood of `u`;
a meromorphic function bounded near a point has nonnegative order, and the normal form of
nonnegative order is analytic.  (This is the content of
`Submission.Work.EQ.meromorphic_order_nonneg_of_bounded`.)

*At the point `u` itself.*  Since `u ∈ {0}ᶜ`, `Ĝ u = toMeromorphicNFAt G u u`: the normal form at
`u` of `G`, which is the analytic regularisation of `G` at `u` — it may differ from `G u`.
Because it is analytic at `u`, it is continuous, and it agrees with `G` on the punctured
neighbourhood of `u`; passing to the limit in `‖G ·‖ ≤ B` therefore gives the same bound
`‖Ĝ u‖ ≤ B`, whence `‖Ĝ u‖ ≤ max B 0`.
-/

namespace Work.EQ

open Filter Topology

theorem toMeromorphicNFOn_far {G : ℂ → ℂ} {R B : ℝ}
    (hmero : ∀ u : ℂ, u ≠ 0 → MeromorphicAt G u)
    (hfar : ∀ u : ℂ, R < ‖u‖ → ‖G u‖ ≤ B) :
    ∀ u : ℂ, max R 1 < ‖u‖ →
      AnalyticAt ℂ (toMeromorphicNFOn G {0}ᶜ) u ∧ ‖toMeromorphicNFOn G {0}ᶜ u‖ ≤ max B 0 := by
  intro u hu
  have huR : R < ‖u‖ := lt_of_le_of_lt (le_max_left R 1) hu
  have hu1 : (1 : ℝ) < ‖u‖ := lt_of_le_of_lt (le_max_right R 1) hu
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hu1
    norm_num at hu1
  have hmem : u ∈ ({0}ᶜ : Set ℂ) := by simpa using hu0
  have hMerG : MeromorphicOn G {0}ᶜ := fun z hz => hmero z (by simpa using hz)
  have hMerAt : MeromorphicAt G u := hmero u hu0
  -- `G` is bounded by `B` on a full neighbourhood of `u`, hence on the punctured one
  have hbdd : ∀ᶠ z in 𝓝[≠] u, ‖G z‖ ≤ B := by
    have hU : {z : ℂ | R < ‖z‖} ∈ 𝓝 u :=
      IsOpen.mem_nhds (isOpen_lt continuous_const continuous_norm) huR
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    filter_upwards [hU] with z hz
    exact hfar z hz
  -- the order of `G` at `u` is nonnegative, so its normal form at `u` is analytic there
  have hordG : 0 ≤ meromorphicOrderAt G u := meromorphic_order_nonneg_of_bounded hMerAt hbdd
  have hNFAtu : AnalyticAt ℂ (toMeromorphicNFAt G u) u :=
    hMerAt.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp hordG
  have hAn : AnalyticAt ℂ (toMeromorphicNFOn G {0}ᶜ) u :=
    hNFAtu.congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hMerG hmem).symm
  refine ⟨hAn, ?_⟩
  have hval : toMeromorphicNFOn G {0}ᶜ u = toMeromorphicNFAt G u u :=
    toMeromorphicNFOn_eq_toMeromorphicNFAt hMerG hmem
  rw [hval]
  -- the regularised value is the limit of `G` along the punctured neighbourhood
  have hlim : Tendsto (fun z => ‖toMeromorphicNFAt G u z‖) (𝓝[≠] u)
      (𝓝 ‖toMeromorphicNFAt G u u‖) :=
    (hNFAtu.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).norm
  have hev : ∀ᶠ z in 𝓝[≠] u, ‖toMeromorphicNFAt G u z‖ ≤ B := by
    filter_upwards [hMerAt.eq_nhdsNE_toMeromorphicNFAt, hbdd] with z hz1 hz2
    rw [← hz1]
    exact hz2
  exact le_trans (le_of_tendsto hlim hev) (le_max_left B 0)

end Work.EQ
