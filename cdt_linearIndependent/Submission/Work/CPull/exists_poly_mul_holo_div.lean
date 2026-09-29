import Mathlib
import Submission.Work.CPull.defs

namespace Work.CPull

open Polynomial Metric Filter
open scoped Topology

/-- **Clearing the zeros of a holomorphic function by a polynomial.** If `g` is holomorphic on the
open unit disc with `g 0 ≠ 0`, and every zero of `g` in the disc lies in the finite set `S`, then
there are a polynomial `W` with `W.eval 0 ≠ 0` and a holomorphic `u` on the disc with
`u z * g z = W.eval z` everywhere on the disc; equivalently `1/g = u/W` on the disc.

*Construction.* `W := ∏ s ∈ S, (X - C s) ^ analyticOrderNatAt g s`, and `u := W/g`, which is
holomorphic off the finitely many zeros of `g`; at a zero `s` the order of `W` at `s` is at least
`analyticOrderNatAt g s`, so the singularity of `W/g` at `s` is removable (e.g. patch the values
with `Function.update` and finitely induct on `Complex.differentiableOn_update_limUnder_of_bddAbove`,
using `AnalyticAt.analyticOrderNatAt_eq_iff` for the local factorisation of `g`). -/
theorem exists_poly_mul_holo_div {g : ℂ → ℂ} (S : Finset ℂ)
    (hg : DifferentiableOn ℂ g (Metric.ball 0 1)) (hg0 : g 0 ≠ 0)
    (hS : ∀ z ∈ Metric.ball (0:ℂ) 1, g z = 0 → z ∈ S) :
    ∃ (W : Polynomial ℂ) (u : ℂ → ℂ), W.eval 0 ≠ 0 ∧ DifferentiableOn ℂ u (Metric.ball 0 1) ∧
      ∀ z ∈ Metric.ball (0:ℂ) 1, u z * g z = W.eval z := by
  classical
  let U : Set ℂ := Metric.ball (0:ℂ) 1
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUconn : IsConnected U := Metric.isConnected_ball zero_lt_one
  have h0U : (0:ℂ) ∈ U := by simp [U, Metric.mem_ball]
  have hgA : AnalyticOnNhd ℂ g U := hg.analyticOnNhd hUopen
  -- `g` is not locally zero anywhere on the disc, so all analytic orders are finite.
  have hfin : ∀ x ∈ U, analyticOrderAt g x ≠ ⊤ := by
    intro x hx
    have hwit : ∃ u : U, analyticOrderAt g (u:ℂ) ≠ ⊤ :=
      ⟨⟨0, h0U⟩, by rw [(hgA 0 h0U).analyticOrderAt_eq_zero.mpr hg0]; exact ENat.zero_ne_top⟩
    exact (hgA.exists_analyticOrderAt_ne_top_iff_forall hUconn).mp hwit ⟨x, hx⟩
  -- the clearing polynomial
  let W : Polynomial ℂ := ∏ s ∈ S, (Polynomial.X - Polynomial.C s) ^ (analyticOrderNatAt g s)
  have hWprod : W = ∏ s ∈ S, (Polynomial.X - Polynomial.C s) ^ (analyticOrderNatAt g s) := rfl
  -- `W 0 ≠ 0`
  have hW0 : W.eval 0 ≠ 0 := by
    rw [hWprod, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
    intro a ha
    rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rcases eq_or_ne a 0 with rfl | ha0
    · have hga : AnalyticAt ℂ g 0 := hgA 0 h0U
      have h0 : analyticOrderNatAt g 0 = 0 := by
        simp [analyticOrderNatAt, hga.analyticOrderAt_eq_zero.mpr hg0]
      rw [h0]; simp
    · exact pow_ne_zero _ (by simpa using sub_ne_zero.mpr (Ne.symm ha0))
  -- zeros of `g` in the disc are zeros of `W`
  have hWz : ∀ z ∈ U, g z = 0 → W.eval z = 0 := by
    intro z hz hgz
    have hzS : z ∈ S := hS z hz hgz
    have hk : analyticOrderNatAt g z ≠ 0 := by
      intro h
      rcases ENat.toNat_eq_zero.mp h with h0 | htop
      · rcases (analyticOrderAt_eq_zero.mp h0) with hna | hne
        · exact hna (hgA z hz)
        · exact hne hgz
      · have hev : g =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.mp htop
        have := hgA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconn.isPreconnected hz hev
        exact hg0 (this h0U)
    rw [hWprod]
    rw [← Finset.mul_prod_erase S (fun s => (Polynomial.X - Polynomial.C s) ^ (analyticOrderNatAt g s)) hzS]
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [show z - z = (0:ℂ) by ring, zero_pow hk, zero_mul]
  -- splitting off the factor at a point of `S`
  have hVfac : ∀ z ∈ S, ∃ V : Polynomial ℂ,
      W = (Polynomial.X - Polynomial.C z) ^ (analyticOrderNatAt g z) * V := by
    intro z hz
    exact ⟨_, hWprod.trans (Finset.mul_prod_erase S
      (fun s => (Polynomial.X - Polynomial.C s) ^ (analyticOrderNatAt g s)) hz).symm⟩
  -- the naive quotient
  let f : ℂ → ℂ := fun z => W.eval z / g z
  have hfW : ∀ y ∈ U, f y * g y = W.eval y := by
    intro y hy
    show W.eval y / g y * g y = W.eval y
    by_cases hgy : g y = 0
    · rw [hgy, div_zero, zero_mul]
      exact (hWz y hy hgy).symm
    · exact div_mul_cancel₀ _ hgy
  have hfM : MeromorphicOn f U := by
    have h1 : AnalyticOnNhd ℂ (fun z => W.eval z) U := fun z _ => W.differentiable.analyticAt z
    exact h1.meromorphicOn.div (hgA.meromorphicOn : MeromorphicOn g U)
  -- the quotient has non-negative meromorphic order everywhere on the disc
  have hfnn : ∀ x ∈ U, 0 ≤ meromorphicOrderAt f x := by
    intro x hx
    rw [(hfM x hx).meromorphicOrderAt_nonneg_iff]
    by_cases hgx : g x = 0
    · have hxS : x ∈ S := hS x hx hgx
      obtain ⟨V, hV⟩ := hVfac x hxS
      obtain ⟨hh, hha, hhne, hheq'⟩ := (AnalyticAt.analyticOrderNatAt_eq_iff (hgA x hx) (hfin x hx)).mp rfl
      have hheq : g =ᶠ[𝓝 x] fun w => (w - x) ^ (analyticOrderNatAt g x) * hh w := by
        filter_upwards [hheq'] with w hw
        rw [hw, smul_eq_mul]
      refine ⟨fun w => V.eval w / hh w, ?_, ?_⟩
      · exact (V.differentiable.analyticAt x).div hha hhne
      · have hWeval : ∀ w, W.eval w = (w - x) ^ (analyticOrderNatAt g x) * V.eval w := by
          intro w
          rw [hV, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C]
        show f =ᶠ[𝓝[≠] x] fun w => V.eval w / hh w
        show (fun w => W.eval w / g w) =ᶠ[𝓝[≠] x] fun w => V.eval w / hh w
        filter_upwards [hheq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hgw hwne
        rw [hWeval w, hgw]
        exact mul_div_mul_left (V.eval w) (hh w)
          (pow_ne_zero _ (sub_ne_zero.mpr (by simpa using hwne)))
    · refine ⟨f, ?_, Filter.EventuallyEq.refl _ _⟩
      show AnalyticAt ℂ (fun z => W.eval z / g z) x
      exact (W.differentiable.analyticAt x).div (hgA x hx) hgx
  -- the normal form of the quotient is holomorphic
  let u : ℂ → ℂ := toMeromorphicNFOn f U
  have huA : AnalyticOnNhd ℂ u U := by
    intro x hx
    have h1 : MeromorphicNFAt u x := (meromorphicNFOn_toMeromorphicNFOn f U) hx
    rw [← h1.meromorphicOrderAt_nonneg_iff_analyticAt]
    rw [show meromorphicOrderAt u x = meromorphicOrderAt f x from meromorphicOrderAt_toMeromorphicNFOn hfM hx]
    exact hfnn x hx
  refine ⟨W, u, hW0, huA.differentiableOn, ?_⟩
  -- the identity `u * g = W` holds modulo a discrete set, hence everywhere by continuity
  intro z hz
  have hzU : z ∈ U := hz
  have hψan : AnalyticAt ℂ (fun y => u y * g y - W.eval y) z :=
    ((huA z hzU).mul (hgA z hzU)).sub (W.differentiable.analyticAt z)
  have hzero : Tendsto (fun y => u y * g y - W.eval y) (𝓝[≠] z) (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hfM.toMeromorphicNFOn_eq_self_on_nhdsNE hzU,
      nhdsWithin_le_nhds (hUopen.mem_nhds hzU)] with y hy hyU
    have huy : u y = f y := hy
    rw [huy, hfW y hyU, sub_self]
  have hlim : Tendsto (fun y => u y * g y - W.eval y) (𝓝[≠] z) (𝓝 (u z * g z - W.eval z)) :=
    hψan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have := tendsto_nhds_unique hzero hlim
  exact sub_eq_zero.mp this.symm

end Work.CPull
