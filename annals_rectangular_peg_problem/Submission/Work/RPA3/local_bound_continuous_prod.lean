import Mathlib

/-!
# Local uniform boundedness of a jointly continuous two-variable function

If `f : X → ℝ → F` is jointly continuous, then the family `(u ↦ f x u)_{u ∈ uIcc a b}`
is locally uniformly bounded near any `x₀ : X` (here `uIcc a b` is a compact interval of `ℝ`).

This is the domination input needed when differentiating a parametric interval integral
`x ↦ ∫ u in a..b, f x u`: the derivative is locally bounded uniformly in the integration
variable, in finite *and* infinite dimensions.
-/

set_option autoImplicit false

open Set

namespace Work.RPA3

universe u

/-- A jointly continuous `f : X → ℝ → F` is bounded on `ball x₀ δ ×ˢ uIcc a b` for some
`δ > 0`. -/
theorem local_bound_continuous_prod {X F : Type u} [NormedAddCommGroup X] [NormedAddCommGroup F]
    {f : X → ℝ → F} (hf : Continuous (fun z : X × ℝ => f z.1 z.2)) (x₀ : X) (a b : ℝ) :
    ∃ δ > 0, ∃ C : ℝ, ∀ x : X, dist x x₀ < δ → ∀ u ∈ Set.uIcc a b, ‖f x u‖ ≤ C := by
  -- For each `u` the function `x ↦ ‖f x u‖` is locally bounded near `x₀`, uniformly for `v` close
  -- to `u`.
  have hpt : ∀ u : ℝ, ∃ d C : ℝ, 0 < d ∧ ∀ x : X, dist x x₀ < d →
      ∀ v : ℝ, dist v u < d → ‖f x v‖ ≤ C := by
    intro u
    have hcont : ContinuousAt (fun z : X × ℝ => ‖f z.1 z.2‖) (x₀, u) := hf.norm.continuousAt
    rcases Metric.continuousAt_iff.1 hcont 1 zero_lt_one with ⟨r, rpos, hr⟩
    refine ⟨r, ‖f x₀ u‖ + 1, rpos, fun x hx v hv => ?_⟩
    have hd : dist (x, v) (x₀, u) < r := by
      rw [Prod.dist_eq]; exact max_lt hx hv
    have := hr hd
    rw [Real.dist_eq] at this
    have := (abs_lt.mp this).2
    linarith
  choose d C hdpos hdC using hpt
  -- Compactness of `uIcc a b` turns the pointwise statement into a uniform one.
  have hcover : Set.uIcc a b ⊆ ⋃ u, Metric.ball u (d u) :=
    fun u _ => Set.mem_iUnion.mpr ⟨u, Metric.mem_ball_self (hdpos u)⟩
  obtain ⟨t, ht⟩ := isCompact_uIcc.elim_finite_subcover (fun u : ℝ => Metric.ball u (d u))
      (fun u => Metric.isOpen_ball) hcover
  have htne : t.Nonempty := by
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp (ht (left_mem_uIcc (a := a) (b := b)))
    obtain ⟨hv', -⟩ := Set.mem_iUnion.mp hv
    exact ⟨v, hv'⟩
  obtain ⟨δ, _, hδmin⟩ := t.exists_min_image d htne
  obtain ⟨c, _, hcmax⟩ := t.exists_max_image C htne
  refine ⟨d δ, hdpos δ, C c, fun x hx v hv => ?_⟩
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp (ht hv)
  obtain ⟨hwt, hwv⟩ := Set.mem_iUnion.mp hw
  exact (hdC w x (lt_of_lt_of_le hx (hδmin w hwt)) v (Metric.mem_ball.mp hwv)).trans
    (hcmax w hwt)

end Work.RPA3
