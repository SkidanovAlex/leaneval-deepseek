import Mathlib
import Submission.Work.EQ.EquiLocalDefs
import Submission.Work.EQ.H0_structure
import Submission.Work.EQ.root_near_of_limit_root

namespace Work.EQ

open Filter _root_.Topology
open scoped Topology

/-- **The set of `ζ` whose leg point lies on the other leg is open (local half of a dichotomy).**
Let `E`, `F` be chart data with the same centre `u₁` (`ψ₁(E ζ) = u₁ + κ ζ^k`,
`ψ₁(F η) = u₁ + κ' η^{k'}`), on the punctured unit disc, and let `ρ > 0` be small enough that
every root of `u₁ + κ ζ^k = u` and of `u₁ + κ' η^{k'} = u` with `dist u u₁ < ρ` has modulus `< 1`
(this is the hypothesis `hsmallE` / `hsmallF`).  If a point `E ζ` with `ζ ≠ 0`, `‖κ ζ^k‖ < ρ` also
lies on the `F`-leg over the same value (`E ζ ∈ F '' {η ≠ 0 | ‖κ' η^{k'}‖ < ρ}`), then the whole
leg still lies on the `F`-leg for all `ζ'` close to `ζ`:
`∃ ε > 0, ball ζ ε ⊆ {ζ' | ζ' ≠ 0 ∧ ‖κ ζ'^k‖ < ρ ∧ E ζ' ∈ F '' {η ≠ 0 | ‖κ' η^{k'}‖ < ρ}}`.

Route: `ψ₁` is locally injective on `H0` (`Work.EQ.H0_structure` clause 1 plus
`Work.EQ.localInj_of_localHomeomorph`), so there is a neighbourhood `U` of `E ζ = F η` in
`ChainData` where equal `ψ₁`-values force equal points (`E ζ ∈ H0` and `F η ∈ H0` by the chart
properties, using `hsmallE`/`hsmallF` to know the relevant parameters have modulus `< 1`).
By continuity of `E` at `ζ`, of `F` at `η`, and by `Work.EQ.root_near_of_limit_root` applied to
`κ'`, `k'` (the map `η ↦ u₁ + κ' η^{k'}` is a local homeomorphism at `η ≠ 0`, so its image of a
small ball around `η` is a neighbourhood of `u₁ + κ' η^{k'}`), every `ζ'` close to `ζ` has a
partner `η'` close to `η` with `u₁ + κ' η'^{k'} = u₁ + κ ζ'^k`; then `E ζ'` and `F η'` are both in
`U ∩ H0` with the same `ψ₁`-value, hence equal, so `E ζ' ∈ F '' {η ≠ 0 | ‖κ' η^{k'}‖ < ρ}`. -/
theorem chart_leg_meets_open {a : ℝ} {h : ℂ → ℂ} {r : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hh : IsStableGerm a h r) {u₁ : ℂ}
    {E F : ℂ → ChainData} {κ κ' : ℂ} {k k' : ℕ} (hE : IsChartData a h E u₁ κ k)
    (hF : IsChartData a h F u₁ κ' k') {ρ : ℝ} (hρ : 0 < ρ)
    (hsmallE : ∀ u ζ : ℂ, dist u u₁ < ρ → u₁ + κ * ζ ^ k = u → ‖ζ‖ < 1)
    (hsmallF : ∀ u ζ : ℂ, dist u u₁ < ρ → u₁ + κ' * ζ ^ k' = u → ‖ζ‖ < 1)
    {ζ : ℂ} (hζ : ζ ≠ 0) (hζρ : ‖κ * ζ ^ k‖ < ρ)
    (hmeet : E ζ ∈ F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ}) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball ζ ε ⊆
      {ζ' : ℂ | ζ' ≠ 0 ∧ ‖κ * ζ' ^ k‖ < ρ ∧
        E ζ' ∈ F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ}} := by
  obtain ⟨hk, hκ, hEprop, -, hEcont⟩ := hE
  obtain ⟨hk', hκ', hFprop, -, hFcont⟩ := hF
  have hlocInj : LocalInj a h := localInj_of_localHomeomorph (H0_structure ha0 ha1 hh).1
  -- `ζ` lies in the chart domain
  have hζ_lt_one : ‖ζ‖ < 1 := by
    refine hsmallE (u₁ + κ * ζ ^ k) ζ ?_ rfl
    rw [dist_eq_norm]
    have hz : u₁ + κ * ζ ^ k - u₁ = κ * ζ ^ k := by ring
    rw [hz]; exact hζρ
  have hζmem : ζ ∈ Metric.ball (0 : ℂ) 1 \ {0} :=
    ⟨by rw [Metric.mem_ball, dist_zero_right]; exact hζ_lt_one, hζ⟩
  have hEζH : E ζ ∈ H0 a h := (hEprop ζ hζmem).1
  have hEζψ : (E ζ).2.1 = u₁ + κ * ζ ^ k := (hEprop ζ hζmem).2
  -- the partner `η`
  obtain ⟨η, hηspec, hFη_eq⟩ := hmeet
  obtain ⟨hηne, hηρ⟩ := hηspec
  have hη_lt_one : ‖η‖ < 1 := by
    refine hsmallF (u₁ + κ' * η ^ k') η ?_ rfl
    rw [dist_eq_norm]
    have hz : u₁ + κ' * η ^ k' - u₁ = κ' * η ^ k' := by ring
    rw [hz]; exact hηρ
  have hηmem : η ∈ Metric.ball (0 : ℂ) 1 \ {0} :=
    ⟨by rw [Metric.mem_ball, dist_zero_right]; exact hη_lt_one, hηne⟩
  have hFηψ : (F η).2.1 = u₁ + κ' * η ^ k' := (hFprop η hηmem).2
  have hψeq : κ' * η ^ k' = κ * ζ ^ k := by
    have hsum : u₁ + κ' * η ^ k' = u₁ + κ * ζ ^ k := by
      rw [← hFηψ, hFη_eq, hEζψ]
    exact add_left_cancel hsum
  -- local injectivity neighbourhood of `E ζ = F η`
  obtain ⟨U, hUo, hEζU, hUinj⟩ := hlocInj (E ζ) hEζH
  have hFηU : F η ∈ U := by rw [hFη_eq]; exact hEζU
  -- continuity of the two charts at the centres
  have hsopen : IsOpen (Metric.ball (0 : ℂ) 1 \ {0}) :=
    Metric.isOpen_ball.sdiff isClosed_singleton
  have hE_at : ContinuousAt E ζ := hEcont.continuousAt (hsopen.mem_nhds hζmem)
  have hF_at : ContinuousAt F η := hFcont.continuousAt (hsopen.mem_nhds hηmem)
  have hE_near : ∀ᶠ ζ' in 𝓝 ζ, E ζ' ∈ U :=
    Filter.Tendsto.eventually hE_at (hUo.mem_nhds hEζU)
  have hF_near : ∀ᶠ η' in 𝓝 η, F η' ∈ U :=
    Filter.Tendsto.eventually hF_at (hUo.mem_nhds hFηU)
  obtain ⟨δF, hδFpos, hδFsub⟩ := Metric.mem_nhds_iff.mp hF_near
  -- the equation `u₁ + κ' η'^{k'} = u` is solvable for `u` near its value at the root `η`
  obtain ⟨ρ'', hρ''pos, hρ''prop⟩ :=
    root_near_of_limit_root (κ := κ') (u₀ := u₁) (u₁ := u₁ + κ' * η ^ k')
      (k := k') (ζ₀ := η) (ε := δF) hκ' hk' rfl hδFpos
  -- eventual conditions near `ζ`
  have hA1 : ∀ᶠ ζ' in 𝓝 ζ, ζ' ≠ 0 :=
    isClosed_singleton.isOpen_compl.mem_nhds hζ
  have hA2 : ∀ᶠ ζ' in 𝓝 ζ, ‖κ * ζ' ^ k‖ < ρ := by
    have hcont : ContinuousAt (fun ζ' : ℂ => ‖κ * ζ' ^ k‖) ζ := by
      simpa using (((continuousAt_id (x := ζ)).pow k).const_mul κ).norm
    exact Filter.Tendsto.eventually hcont (isOpen_Iio.mem_nhds hζρ)
  have hA4 : ∀ᶠ ζ' in 𝓝 ζ, ‖κ * ζ' ^ k - κ * ζ ^ k‖ < ρ'' := by
    have hcont : ContinuousAt (fun ζ' : ℂ => ‖κ * ζ' ^ k - κ * ζ ^ k‖) ζ := by
      simpa using ((((continuousAt_id (x := ζ)).pow k).const_mul κ).sub continuousAt_const).norm
    have hval : ‖κ * ζ ^ k - κ * ζ ^ k‖ < ρ'' := by simpa using hρ''pos
    exact Filter.Tendsto.eventually hcont (isOpen_Iio.mem_nhds hval)
  -- assembly
  refine Metric.mem_nhds_iff.mp ?_
  have hnear : ∀ᶠ ζ' in 𝓝 ζ,
      ζ' ≠ 0 ∧ (‖κ * ζ' ^ k‖ < ρ ∧ (E ζ' ∈ U ∧ ‖κ * ζ' ^ k - κ * ζ ^ k‖ < ρ'')) :=
    hA1.and (hA2.and (hE_near.and hA4))
  refine Filter.mem_of_superset hnear ?_
  rintro ζ' ⟨hζ'ne, hζ'ρ, hζ'U, hζ'close⟩
  refine ⟨hζ'ne, hζ'ρ, ?_⟩
  -- solve for the partner `η'`
  have hdist : dist (u₁ + κ * ζ' ^ k) (u₁ + κ' * η ^ k') < ρ'' := by
    rw [hψeq, dist_eq_norm]
    have hz : u₁ + κ * ζ' ^ k - (u₁ + κ * ζ ^ k) = κ * ζ' ^ k - κ * ζ ^ k := by ring
    rw [hz]; exact hζ'close
  obtain ⟨η', hη'eq, hη'dist⟩ := hρ''prop (u₁ + κ * ζ' ^ k) hdist
  have hψ' : κ' * η' ^ k' = κ * ζ' ^ k := add_left_cancel hη'eq
  have hη'ne : η' ≠ 0 := by
    intro h0
    have hL : ‖κ' * η' ^ k'‖ = 0 := by rw [h0, zero_pow hk'.ne', mul_zero, norm_zero]
    have hzero : ‖κ * ζ' ^ k‖ = 0 := by rw [← hψ', hL]
    have h2 : κ * ζ' ^ k = 0 := norm_eq_zero.mp hzero
    have h3 : ζ' ^ k = 0 := (mul_eq_zero.mp h2).resolve_left hκ
    exact hζ'ne ((pow_eq_zero_iff hk.ne').mp h3)
  have hη'ρ : ‖κ' * η' ^ k'‖ < ρ := by rw [hψ']; exact hζ'ρ
  have hη'lt1 : ‖η'‖ < 1 := by
    refine hsmallF (u₁ + κ' * η' ^ k') η' ?_ rfl
    rw [dist_eq_norm]
    have hz : u₁ + κ' * η' ^ k' - u₁ = κ' * η' ^ k' := by ring
    rw [hz]; exact hη'ρ
  have hη'mem : η' ∈ Metric.ball (0 : ℂ) 1 \ {0} :=
    ⟨by rw [Metric.mem_ball, dist_zero_right]; exact hη'lt1, hη'ne⟩
  have hFη'H : F η' ∈ H0 a h := (hFprop η' hη'mem).1
  have hFη'ψ : (F η').2.1 = u₁ + κ' * η' ^ k' := (hFprop η' hη'mem).2
  have hζ'lt1 : ‖ζ'‖ < 1 := by
    refine hsmallE (u₁ + κ * ζ' ^ k) ζ' ?_ rfl
    rw [dist_eq_norm]
    have hz : u₁ + κ * ζ' ^ k - u₁ = κ * ζ' ^ k := by ring
    rw [hz]; exact hζ'ρ
  have hζ'mem : ζ' ∈ Metric.ball (0 : ℂ) 1 \ {0} :=
    ⟨by rw [Metric.mem_ball, dist_zero_right]; exact hζ'lt1, hζ'ne⟩
  have hEζ'H : E ζ' ∈ H0 a h := (hEprop ζ' hζ'mem).1
  have hEζ'ψ : (E ζ').2.1 = u₁ + κ * ζ' ^ k := (hEprop ζ' hζ'mem).2
  have hη'U : F η' ∈ U := hδFsub (Metric.mem_ball.mpr hη'dist)
  have hsame : (E ζ').2.1 = (F η').2.1 := by rw [hEζ'ψ, hFη'ψ, hψ']
  exact ⟨η', ⟨hη'ne, hη'ρ⟩,
    (hUinj (E ζ') hζ'U hEζ'H (F η') hη'U hFη'H hsame).symm⟩

end Work.EQ
