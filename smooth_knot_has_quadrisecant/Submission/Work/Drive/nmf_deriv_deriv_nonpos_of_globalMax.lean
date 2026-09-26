import Mathlib

namespace Work.Drive

/-- A real function with a global maximum at `a` has nonpositive second derivative there.
(Second-derivative test at a global maximiser; Mathlib has only the *converse* statements
`isLocalMin_of_deriv_deriv_pos` / `isLocalMax_of_deriv_deriv_neg`.) -/
lemma nmf_deriv_deriv_nonpos_of_globalMax {f : ℝ → ℝ} {a : ℝ} (h : ∀ x, f x ≤ f a)
    (hc : ContinuousAt f a) : deriv (deriv f) a ≤ 0 := by
  -- Suppose the second derivative at the global maximiser were positive.
  rw [← not_lt]
  intro hpos
  -- A global maximum is a local maximum, hence (Fermat) `deriv f a = 0`
  -- (`IsLocalMax.deriv_eq_zero` needs no differentiability hypothesis: `deriv` is `0` where `f`
  -- is not differentiable).
  have hmax : IsLocalMax f a := Filter.Eventually.of_forall h
  have hd : deriv f a = 0 := hmax.deriv_eq_zero
  -- The second-derivative test (Mathlib's `isLocalMin_of_deriv_deriv_pos`) makes `a` a local
  -- minimum: eventually `f a ≤ f x`.
  have hmin : IsLocalMin f a := isLocalMin_of_deriv_deriv_pos hpos hd hc
  -- Together with the global maximum (`f x ≤ f a` eventually, indeed everywhere) this forces `f`
  -- to be eventually constant at `a`.
  have hfe : f =ᶠ[nhds a] fun _ => f a := by
    filter_upwards [show ∀ᶠ x in nhds a, f x ≤ f a from hmax,
      show ∀ᶠ x in nhds a, f a ≤ f x from hmin] with x hx1 hx2
    exact le_antisymm hx1 hx2
  -- Hence `deriv f` is eventually the zero function ...
  have hde : deriv f =ᶠ[nhds a] fun _ => (0 : ℝ) := by
    filter_upwards [hfe.deriv] with x hx
    simpa using hx
  -- ... so `deriv (deriv f) a = deriv 0 a = 0`, contradicting `hpos`.
  have h2 : deriv (deriv f) a = 0 := by
    simpa using Filter.EventuallyEq.deriv_eq hde
  exact absurd h2 (ne_of_gt hpos)

end Work.Drive
