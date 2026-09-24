import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Normed.Module.Connected

namespace Commons.Analysis.Complex

open scoped Classical
open Filter
open scoped Topology

theorem exists_unique_zero_of_divisor_finsum_eq_one {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball (0:ℂ) R))
    (hsum : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor h (Metric.ball (0:ℂ) ρ)) u : ℤ)) = 1) :
    ∃ z ∈ Metric.ball (0:ℂ) ρ, h z = 0 ∧ ∀ y ∈ Metric.ball (0:ℂ) ρ, h y = 0 → y = z := by
  classical
  let U : Set ℂ := Metric.ball (0:ℂ) ρ
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUconn : IsPreconnected U := Metric.isPreconnected_ball
  have hhU : AnalyticOnNhd ℂ h U := hh.mono (Metric.ball_subset_ball hρR)
  let D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor h U
  have hsumD : (∑ᶠ u : ℂ, D u) = 1 := hsum
  have hDnonneg : ∀ u, 0 ≤ D u := by
    intro u
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hhU u
  have hnotzero : ¬ Set.EqOn h 0 U := by
    intro hz0
    have hzero_all : ∀ u, D u = 0 := by
      intro u
      by_cases hu : u ∈ U
      · have hev : ∀ᶠ z in 𝓝 u, h z = 0 := by
          filter_upwards [hUopen.mem_nhds hu] with z hz using hz0 hz
        have htop : meromorphicOrderAt h u = ⊤ :=
          meromorphicOrderAt_eq_top_iff.mpr (hev.filter_mono nhdsWithin_le_nhds)
        show D u = 0
        rw [MeromorphicOn.divisor_apply hhU.meromorphicOn hu, htop, WithTop.untop₀_top]
      · show D u = 0
        exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem D hu
    have hz : (∑ᶠ u : ℂ, D u) = 0 := by
      rw [finsum_congr hzero_all, finsum_zero]
    omega
  have hDpos : ∀ u ∈ U, h u = 0 → 1 ≤ D u := by
    intro u hu hu0
    have hAn : AnalyticAt ℂ h u := hhU u hu
    have hne0 : analyticOrderAt h u ≠ 0 := hAn.analyticOrderAt_ne_zero.mpr hu0
    have hnetop : analyticOrderAt h u ≠ ⊤ := by
      intro htop
      refine hnotzero
        (AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hhU hUconn hu ?_)
      exact analyticOrderAt_eq_top.mp htop
    obtain ⟨n, hn⟩ : ∃ n : ℕ, analyticOrderAt h u = ↑n := by
      cases hh2 : analyticOrderAt h u with
      | top => exact absurd hh2 hnetop
      | coe n => exact ⟨n, rfl⟩
    have hn0 : n ≠ 0 := by
      rw [hn] at hne0
      simpa using hne0
    show 1 ≤ D u
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hhU hu, hn,
      ENat.map_natCast, WithTop.untop₀_coe]
    omega
  have hex : ∃ u, D u ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_ne_iff] at hcon
    have hz : (∑ᶠ u : ℂ, D u) = 0 := by
      rw [finsum_congr hcon, finsum_zero]
    omega
  obtain ⟨z, hz_ne⟩ := hex
  have hzU : z ∈ U := by
    by_contra hz
    exact hz_ne (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem D hz)
  have hzh : h z = 0 := by
    by_contra hznz
    have h0 : analyticOrderAt h z = 0 := (hhU z hzU).analyticOrderAt_eq_zero.mpr hznz
    have hDz : D z = 0 := by
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hhU hzU, h0]
      simp
    exact hz_ne hDz
  refine ⟨z, hzU, hzh, ?_⟩
  intro y hy hyh
  by_contra hyz
  have hDynz : D y ≠ 0 := by
    have := hDpos y hy hyh
    omega
  have hfin : Function.HasFiniteSupport (fun u : ℂ => D u) :=
    hasFiniteSupport_of_finsum_eq_one hsumD
  have hsum_s : ∑ i ∈ hfin.toFinset, D i = 1 := by
    have h1 := finsum_eq_finsetSum_of_support_subset (fun u : ℂ => D u) (s := hfin.toFinset)
      (fun x hx => (Set.Finite.mem_toFinset hfin).mpr hx)
    rw [← h1]
    exact hsumD
  have hzs : z ∈ hfin.toFinset :=
    (Set.Finite.mem_toFinset hfin).mpr (Function.mem_support.mpr hz_ne)
  have hys : y ∈ hfin.toFinset :=
    (Set.Finite.mem_toFinset hfin).mpr (Function.mem_support.mpr hDynz)
  have hz1 : 1 ≤ D z := hDpos z hzU hzh
  have hy1 : 1 ≤ D y := hDpos y hy hyh
  have hpair : ∑ i ∈ ({z, y} : Finset ℂ), D i ≤ ∑ i ∈ hfin.toFinset, D i :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact hzs
        · exact hys)
      (fun i _ _ => hDnonneg i)
  have hpairval : ∑ i ∈ ({z, y} : Finset ℂ), D i = D z + D y :=
    Finset.sum_pair (Ne.symm hyz)
  omega

end Commons.Analysis.Complex