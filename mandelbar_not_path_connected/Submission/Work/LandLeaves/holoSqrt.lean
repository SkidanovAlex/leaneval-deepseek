import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A holomorphic square root on the unit disc

If `h : ℂ → ℂ` is holomorphic on the open unit ball, `h 0 = 1` and `h` has no zeros there,
then `h` has a holomorphic square root `u` on the ball with `u 0 = 1`.

The proof follows the classical route through the logarithmic derivative: on the disc (which is
open, convex, hence simply connected) the holomorphic function `deriv h / h` has a primitive `g`
vanishing at `0` (Morera's theorem for discs, `DifferentiableOn.isExactOn_ball`).  Then
`z ↦ h z * exp (-(g z))` has vanishing derivative on the ball, hence is constant, and evaluating
at `0` gives `h z = exp (g z)`.  Finally `u z = exp (g z / 2)` is holomorphic with `u 0 = 1` and
`u z ^ 2 = h z`.
-/

namespace Work.LandLeaves

theorem holoSqrt (h : ℂ → ℂ) (hd : DifferentiableOn ℂ h (Metric.ball 0 1)) (h0 : h 0 = 1)
    (hne : ∀ z ∈ Metric.ball 0 1, h z ≠ 0) :
    ∃ u : ℂ → ℂ, DifferentiableOn ℂ u (Metric.ball 0 1) ∧ u 0 = 1 ∧
      ∀ z ∈ Metric.ball 0 1, u z ^ 2 = h z := by
  let B : Set ℂ := Metric.ball 0 1
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hBconn : IsPreconnected B := Metric.isPreconnected_ball
  have h0B : (0 : ℂ) ∈ B := Metric.mem_ball_self one_pos
  -- The logarithmic derivative `deriv h / h` is holomorphic on the ball ...
  have hdh : DifferentiableOn ℂ (deriv h) B := hd.deriv Metric.isOpen_ball
  have hlog : DifferentiableOn ℂ (fun z => deriv h z / h z) B := hdh.div hd hne
  -- ... hence by Morera's theorem has a primitive `g`, which we normalize by `g 0 = 0`.
  obtain ⟨g, hg0, hg⟩ := (hlog.isExactOn_ball).with_val_at 0 0
  have hgd : DifferentiableOn ℂ g B :=
    fun z hz => (hg z hz).differentiableAt.differentiableWithinAt
  -- `h · exp (-g)` has vanishing derivative, so it is constant, equal to `1`.
  set φ : ℂ → ℂ := fun z => h z * Complex.exp (-(g z)) with hφdef
  have hφd : DifferentiableOn ℂ φ B := by
    rw [hφdef]
    fun_prop
  have hφd0 : ∀ z ∈ B, HasDerivAt φ 0 z := by
    intro z hz
    have hzh : h z ≠ 0 := hne z hz
    have hdhz : HasDerivAt h (deriv h z) z :=
      (hd.differentiableAt (hBopen.mem_nhds hz)).hasDerivAt
    have hgdz : HasDerivAt g (deriv h z / h z) z := hg z hz
    have hgd2 : HasDerivAt (fun w => -(g w)) (-(deriv h z / h z)) z := hgdz.neg
    have hexp2 : HasDerivAt (fun w => Complex.exp (-(g w)))
        (Complex.exp (-(g z)) * (-(deriv h z / h z))) z :=
      (Complex.hasDerivAt_exp (-(g z))).comp z hgd2
    have hmul : HasDerivAt (fun w => h w * Complex.exp (-(g w)))
        (deriv h z * Complex.exp (-(g z)) +
          h z * (Complex.exp (-(g z)) * (-(deriv h z / h z)))) z :=
      hdhz.mul hexp2
    rw [hφdef]
    convert hmul using 1
    field_simp
    ring
  have hφderiv : Set.EqOn (deriv φ) 0 B := fun z hz => (hφd0 z hz).deriv
  have hφ0 : φ 0 = 1 := by
    rw [hφdef]; simp [h0, hg0]
  have hconst : ∀ z ∈ B, φ z = φ 0 :=
    fun z hz => hBopen.is_const_of_deriv_eq_zero hBconn hφd hφderiv hz h0B
  -- Thus `h = exp ∘ g` on the ball.
  have hexp_eq : ∀ z ∈ B, h z = Complex.exp (g z) := by
    intro z hz
    have hz1 : h z * Complex.exp (-(g z)) = 1 := by
      have hc := hconst z hz
      rw [hφ0] at hc
      exact hc
    have he1 : Complex.exp (-(g z)) * Complex.exp (g z) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    calc h z = h z * 1 := by ring
      _ = h z * (Complex.exp (-(g z)) * Complex.exp (g z)) := by rw [he1]
      _ = (h z * Complex.exp (-(g z))) * Complex.exp (g z) := by ring
      _ = 1 * Complex.exp (g z) := by rw [hz1]
      _ = Complex.exp (g z) := by ring
  -- Half the logarithm is the required square root.
  refine ⟨fun z => Complex.exp (g z / 2), ?_, ?_, ?_⟩
  · have hg2 : DifferentiableOn ℂ (fun z => g z / 2) B := hgd.div_const (2 : ℂ)
    simpa [Function.comp_def] using
      (Complex.differentiable_exp.differentiableOn (s := Set.univ)).comp hg2
        (fun z _ => trivial)
  · simp [hg0, Complex.exp_zero]
  · intro z hz
    rw [hexp_eq z hz, ← Complex.exp_nat_mul]
    congr 1
    ring

end Work.LandLeaves
