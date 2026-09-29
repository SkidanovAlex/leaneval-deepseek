import Mathlib
import Submission.Work.OdeCont.vecBound
import Submission.Work.OdeCont.localUniq

/-!
# Uniqueness for the linear system `Y' = A(z) · Y + b(z)` on a preconnected open set

If `X` and `Y` are two `ℂ`-differentiable solutions of the (inhomogeneous, linear, first order)
system
`Y'(z) = A(z) · Y(z) + b(z)` on an open preconnected set `U ⊆ ℂ`, and if `X` and `Y` agree at one
point of `U`, then they agree on all of `U`.

Proof.  The difference `Z = X - Y` solves the *homogeneous* system `Z' = A(z) · Z` and satisfies
`Z z₀ = 0`.

* `Work.OdeCont.vecBound` bounds the linear map `v ↦ A z · v` uniformly on a ball around `z₀`
  (the entries of `A` are continuous there, being differentiable on the open set `U`), and
* `Work.OdeCont.localUniq` (Grönwall along the segments from `z₀`, which stay inside the ball
  because balls are convex) shows that `Z` vanishes on that whole ball.

So `X = Y` in a whole neighbourhood of `z₀`; the identity theorem for analytic functions
(`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, applicable since `X` and `Y` are
holomorphic on the open set `U`) propagates this to all of `U`.
-/

namespace Work.OdeCont

open scoped BigOperators

theorem uniqueness {k : ℕ} {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ)
    (hA : ∀ i j : Fin k, DifferentiableOn ℂ (fun z : ℂ => A z i j) U)
    (hb : ∀ i : Fin k, DifferentiableOn ℂ (fun z : ℂ => b z i) U)
    (X Y : ℂ → Fin k → ℂ) (hX : DifferentiableOn ℂ X U) (hY : DifferentiableOn ℂ Y U)
    (hX' : ∀ z ∈ U, HasDerivAt X
      (fun i => (Finset.univ.sum (fun j => A z i j * X z j)) + b z i) z)
    (hY' : ∀ z ∈ U, HasDerivAt Y
      (fun i => (Finset.univ.sum (fun j => A z i j * Y z j)) + b z i) z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (h : X z₀ = Y z₀) : Set.EqOn X Y U := by
  -- Step 1: the difference `X - Y` solves the homogeneous system (the `b z` terms cancel).
  have hode : ∀ z ∈ U, HasDerivAt (X - Y)
      (fun i : Fin k => Finset.univ.sum (fun j => A z i j * (X z j - Y z j))) z := by
    intro z hz
    have hsub := (hX' z hz).sub (hY' z hz)
    have hkey : ((fun i : Fin k => (Finset.univ.sum (fun j => A z i j * X z j)) + b z i)
          - (fun i : Fin k => (Finset.univ.sum (fun j => A z i j * Y z j)) + b z i))
        = (fun i : Fin k => Finset.univ.sum (fun j => A z i j * (X z j - Y z j))) := by
      ext i
      simp only [Pi.sub_apply]
      rw [add_sub_add_comm, sub_self, add_zero, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    exact hsub.congr_deriv hkey
  -- Step 2: a ball around `z₀` contained in `U`.
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
  set R : ℝ := ε / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hballsub : Metric.ball z₀ R ⊆ U :=
    fun z hz => hεsub (Metric.ball_subset_ball (by rw [hRdef]; linarith) hz)
  have hclosedsub : Metric.closedBall z₀ R ⊆ U :=
    fun z hz => hεsub (Metric.closedBall_subset_ball (by rw [hRdef]; linarith) hz)
  have hAcont : ∀ i j : Fin k, ContinuousOn (fun z : ℂ => A z i j) (Metric.closedBall z₀ R) :=
    fun i j => (hA i j).continuousOn.mono hclosedsub
  -- Step 3: uniform bound for `v ↦ A z · v` on that ball, then Grönwall.
  obtain ⟨C, hC, hbound⟩ := vecBound (A := A) (w := z₀) (R := R) hAcont
  have hZode : ∀ z ∈ Metric.ball z₀ R,
      HasDerivAt (X - Y) (fun i : Fin k => ∑ j, A z i j * (X - Y) z j) z :=
    fun z hz => by simpa using hode z (hballsub hz)
  have hw0 : (X - Y) z₀ = 0 := by
    show X z₀ - Y z₀ = 0
    rw [h, sub_self]
  have hloc : ∀ z ∈ Metric.ball z₀ R, (X - Y) z = 0 :=
    localUniq (A := A) (Z := X - Y) (w := z₀) (R := R) (C := C) hC hbound hZode hw0
  -- Step 4: identity theorem for analytic functions on the preconnected open set `U`.
  have hev : X =ᶠ[nhds z₀] Y := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hRpos)] with z hz
    have hz0 : (X - Y) z = 0 := hloc z hz
    exact sub_eq_zero.mp hz0
  have hXan : AnalyticOnNhd ℂ X U := hX.analyticOnNhd hU
  have hYan : AnalyticOnNhd ℂ Y U := hY.analyticOnNhd hU
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hXan hYan hc hz₀ hev

end Work.OdeCont
