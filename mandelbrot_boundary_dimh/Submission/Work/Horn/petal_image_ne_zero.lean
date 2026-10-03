import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# `Work.Horn.petal_image_ne_zero`

Let `D ⊆ ℂ` be open, `G : ℂ → ℂ` holomorphic on `D`, and let `V i` (`i : Fin q`) be connected
subsets of `D` accumulating at `0`.  Suppose that

* every point of `D` whose forward orbit stays in `D` until it reaches `⋃ i, V i` belongs to the
  parabolic basin `MandelDim.ParabolicBasin G D` (`hVreach`), and
* `0` itself is *not* in that basin (`h0out`).

Then no petal `V i` is mapped to `0` by `G`.

The proof: if `z ∈ V i` and `G z = 0`, then `z ∈ D` and, taking `n = 0` in `hVreach`, the point `z`
lies in the basin; the basin witness `U ∈ 𝓝 z` satisfies `G '' U ⊆ D`, so `0 = G z ∈ D`.

* If `G` is locally open at `z` (equivalently `deriv G z ≠ 0`), then `G '' U` is a neighbourhood
  of `0` which is mapped into `D` by every iterate and on which `G^[n] → 0` uniformly: hence
  `0` lies in the basin, contradicting `h0out`.

* Otherwise `G` is constant, equal to `G z = 0`, on a neighbourhood of `z`.  The petal `V i` is
  preconnected with `z ∈ V i`, so by the identity theorem `G ≡ 0` on `V i`; and since
  `0 ∈ closure (V i)` we may pick `w₀ ∈ V i` inside any disc `ball 0 δ ⊆ D`.  The union
  `V i ∪ ball 0 δ` (preconnected, as it is a union of two preconnected sets meeting in `w₀`) is
  mapped to `0` by `G`, so `G ≡ 0` on a neighbourhood of `0`; again `0` is in the basin.
-/

namespace Work.Horn

open Filter Function Metric Set Topology

theorem petal_image_ne_zero {G : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {V : Fin q → Set ℂ}
    (hD : IsOpen D) (hG : DifferentiableOn ℂ G D)
    (hVconn : ∀ i, IsConnected (V i)) (hVsub : ∀ i, V i ⊆ D)
    (hVcl : ∀ i, (0 : ℂ) ∈ closure (V i))
    (hVreach : ∀ z ∈ D, (∃ n : ℕ, (∀ k < n, G^[k] z ∈ D) ∧ G^[n] z ∈ ⋃ i, V i) →
      z ∈ MandelDim.ParabolicBasin G D)
    (h0out : (0 : ℂ) ∉ MandelDim.ParabolicBasin G D) :
    ∀ i, ∀ z ∈ V i, G z ≠ 0 := by
  intro i z hz hGz
  have hzD : z ∈ D := hVsub i hz
  -- `n = 0`: the point `z` of the petal reaches the petals immediately, so it is in the basin
  have hzbasin : z ∈ MandelDim.ParabolicBasin G D :=
    hVreach z hzD
      ⟨0, (by intro k hk; omega), by
        simpa [Function.iterate_zero] using Set.mem_iUnion.mpr ⟨i, hz⟩⟩
  obtain ⟨U, hU, hUmap, hUconv⟩ := hzbasin
  have hzU : z ∈ U := mem_of_mem_nhds hU
  -- the basin witness gives `0 = G z ∈ G '' U ⊆ D`
  have h0D : (0 : ℂ) ∈ D := by
    have h1 : G z ∈ D := by
      simpa [Function.iterate_one] using hUmap 1 hzU
    rwa [hGz] at h1
  rcases (hG.analyticAt (hD.mem_nhds hzD)).eventually_constant_or_nhds_le_map_nhds with
    hconst | hopen
  · -- ## `G` is constant, equal to `G z = 0`, near `z`
    have hconst0 : G =ᶠ[𝓝 z] 0 := by
      filter_upwards [hconst] with w hw
      simp [hw, hGz]
    -- a disc around `0` contained in `D`
    obtain ⟨δ, hδ, hδD⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds h0D)
    -- `V i` meets that disc, hence `V i ∪ ball 0 δ` is preconnected
    obtain ⟨w₀, hw₀V, hw₀d⟩ := Metric.mem_closure_iff.mp (hVcl i) δ hδ
    have hw₀ball : w₀ ∈ ball (0 : ℂ) δ := by
      simpa [Metric.mem_ball, dist_comm] using hw₀d
    have hpre : IsPreconnected (V i ∪ ball (0 : ℂ) δ) :=
      IsPreconnected.union w₀ hw₀V hw₀ball (hVconn i).isPreconnected isPreconnected_ball
    have hsub : V i ∪ ball (0 : ℂ) δ ⊆ D := by
      intro w hw
      rcases hw with hw | hw
      · exact hVsub i hw
      · exact hδD hw
    -- the identity theorem on the preconnected set `V i ∪ ball 0 δ`
    have hzero : ∀ w ∈ V i ∪ ball (0 : ℂ) δ, G w = 0 :=
      ((hG.analyticOnNhd hD).mono hsub).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        hpre (Or.inl hz) hconst0
    have hballzero : ∀ w ∈ ball (0 : ℂ) δ, G w = 0 := fun w hw => hzero w (Or.inr hw)
    have hG0 : G 0 = 0 := hballzero 0 (mem_ball_self hδ)
    have hiter0 : ∀ k : ℕ, (G^[k]) (0 : ℂ) = 0 := by
      intro k
      induction k with
      | zero => simp
      | succ j ih => rw [Function.iterate_succ_apply', ih, hG0]
    have hiterpos : ∀ n : ℕ, 1 ≤ n → ∀ y ∈ ball (0 : ℂ) δ, (G^[n]) y = 0 := by
      intro n
      induction n with
      | zero => intro h; omega
      | succ j ih =>
          intro _ y hy
          rw [Function.iterate_succ_apply']
          rcases Nat.eq_zero_or_pos j with hj | hj
          · subst hj
            simpa [Function.iterate_zero] using hballzero y hy
          · rw [ih hj y hy]
            exact hG0
    -- `ball 0 δ` is a neighbourhood of `0` mapped to `0` by `G`
    refine h0out ⟨ball (0 : ℂ) δ, Metric.mem_nhds_iff.mpr ⟨δ, hδ, subset_rfl⟩, ?_, ?_⟩
    · intro n y hy
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        simpa [Function.iterate_zero] using hδD hy
      · rw [hiterpos n hpos y hy]
        exact h0D
    · rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      refine Filter.eventually_atTop.mpr ⟨1, fun n hn y hy => ?_⟩
      rw [hiterpos n hn y hy]
      simpa using hε
  · -- ## `G` is locally open at `z`
    have hGUnhds : G '' U ∈ 𝓝 (G z) :=
      Filter.le_def.mp hopen (G '' U)
        (Filter.mem_map.mpr (Filter.mem_of_superset hU (fun u hu => ⟨u, hu, rfl⟩)))
    rw [hGz] at hGUnhds
    -- `G '' U` is a neighbourhood of `0`, and its iterates are the iterates of `U`
    refine h0out ⟨G '' U, hGUnhds, ?_, ?_⟩
    · intro n y hy
      obtain ⟨u, hu, rfl⟩ := hy
      have h : (G^[n]) (G u) = G^[n + 1] u := by rw [Function.iterate_succ_apply]
      rw [h]
      exact hUmap (n + 1) hu
    · rw [Metric.tendstoUniformlyOn_iff] at hUconv ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hUconv ε hε)
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn y hy => ?_⟩
      obtain ⟨u, hu, rfl⟩ := hy
      have h := hN (n + 1) (by omega) u hu
      simpa [Function.iterate_succ_apply, Function.iterate_succ_apply'] using h

end Work.Horn
