import Mathlib
import Submission.Work.FatouDeg.Petal.DefsAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

/-- **The error of the Fatou coordinate has bounded derivative on the petal.**

`Dom m ρ` is the wide sector of radius `2ρ`, `Pet m ρ` its narrow sub-sector of radius `ρ`.  Every
point of `Pet m ρ` has the ball of radius `κ * ‖z‖` around it inside `Dom m ρ` (hypothesis
`hmargin`).  On `Dom m ρ` the coordinate `phifun m G` is holomorphic and differs from the explicit
`Afun m G` by at most `D * ‖z‖`.  Then the derivative of the error `phifun m G - Afun m G` is
bounded on `Pet m ρ` by a constant `D'`.

Proof: `E = phifun m G - Afun m G` is holomorphic on `Dom m ρ` (use `Complex.differentiableAt_log`
on `Re z > 0` for `Afun`), and on the disc of radius `κ ‖z‖ / 2` around `z ∈ Pet m ρ` (which lies
in `Dom m ρ` by `hmargin`) it satisfies `‖E w‖ ≤ D ‖w‖ ≤ D (‖z‖ + κ‖z‖)`, so the Cauchy estimate
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` gives
`‖deriv E z‖ ≤ D (1 + κ) / (κ/2)`, independent of `z`. -/
theorem coordDerivAux (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) {ρ κ D : ℝ} (hρ : 0 < ρ)
    (hκ : 0 < κ) (hD : 0 ≤ D)
    (hdiff : DifferentiableOn ℂ (phifun m G) (Dom m ρ))
    (hgrowth : ∀ z ∈ Dom m ρ, ‖phifun m G z - Afun m G z‖ ≤ D * ‖z‖)
    (hmargin : ∀ z ∈ Pet m ρ, ∀ w : ℂ, ‖w - z‖ ≤ κ * ‖z‖ → w ∈ Dom m ρ) :
    ∃ D' : ℝ, 0 ≤ D' ∧ ∀ z ∈ Pet m ρ, ‖deriv (phifun m G) z - deriv (Afun m G) z‖ ≤ D' := by
  -- `Afun` is holomorphic on the working domain: every point of `Dom` has `Re z > 0`
  have hA : DifferentiableOn ℂ (Afun m G) (Dom m ρ) := by
    intro z hz
    rw [mem_Dom] at hz
    obtain ⟨-, hzsec⟩ := hz
    have hre : 0 < z.re := lt_of_le_of_lt (mul_nonneg (by positivity) (abs_nonneg z.im)) hzsec
    have hz0 : z ≠ 0 := by intro h; rw [h] at hre; simp at hre
    have hpow : z ^ (m - 1) ≠ 0 := pow_ne_zero _ hz0
    have hp : DifferentiableAt ℂ (fun w : ℂ => w ^ (m - 1)) z := differentiableAt_pow (m - 1)
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (w ^ (m - 1))⁻¹ * (Ppoly m G).eval w) z :=
      (hp.inv hpow).mul (Polynomial.differentiableAt (Ppoly m G))
    have hl : DifferentiableAt ℂ Complex.log z :=
      Complex.differentiableAt_log (by rw [Complex.mem_slitPlane_iff]; exact Or.inl hre)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => betac m G * Complex.log w) z := hl.const_mul _
    exact (h1.add h2).differentiableWithinAt
  refine ⟨2 * D * (1 + κ) / κ, by positivity, ?_⟩
  intro z hzPet
  have hz' := hzPet
  rw [mem_Pet] at hz'
  obtain ⟨hzρ, hzsec⟩ := hz'
  have hre : 0 < z.re := lt_of_le_of_lt (mul_nonneg (by positivity) (abs_nonneg z.im)) hzsec
  have hznorm : 0 < ‖z‖ := lt_of_lt_of_le hre (Complex.re_le_norm z)
  have hzDom : z ∈ Dom m ρ := Pet_subset_Dom m (by omega) ρ hzPet
  -- the error `E = phifun - Afun` is holomorphic on the working domain
  have hE_dom : DifferentiableOn ℂ (fun w => phifun m G w - Afun m G w) (Dom m ρ) := hdiff.sub hA
  -- ... hence on the Cauchy disc of radius `κ ‖z‖` around `z`
  have hE_ball : DifferentiableOn ℂ (fun w => phifun m G w - Afun m G w)
      (Metric.ball z (κ * ‖z‖)) :=
    hE_dom.mono (fun w hw => by
      rw [Metric.mem_ball, dist_eq_norm] at hw
      exact hmargin z hzPet w (le_of_lt hw))
  set R : ℝ := κ * ‖z‖ / 2 with hRdef
  have hκz : 0 < κ * ‖z‖ := mul_pos hκ hznorm
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hRlt : R < κ * ‖z‖ := by rw [hRdef]; linarith
  have hE_closed : DifferentiableOn ℂ (fun w => phifun m G w - Afun m G w)
      (Metric.closedBall z R) :=
    hE_ball.mono (Metric.closedBall_subset_ball hRlt)
  have hcont : DiffContOnCl ℂ (fun w => phifun m G w - Afun m G w) (Metric.ball z R) := by
    refine DifferentiableOn.diffContOnCl ?_
    rwa [closure_ball z (ne_of_gt hRpos)]
  -- the bound `‖E w‖ ≤ D (1 + κ) ‖z‖` on the sphere of radius `R`
  have hsphere : ∀ w ∈ Metric.sphere z R, ‖phifun m G w - Afun m G w‖ ≤ D * (1 + κ) * ‖z‖ := by
    intro w hw
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    have hwdom : w ∈ Dom m ρ := hmargin z hzPet w (by rw [hw, hRdef]; linarith)
    have hwle : ‖w‖ ≤ ‖z‖ * (1 + κ) := by
      have h1 : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
        simpa [norm_sub_rev] using norm_le_norm_add_norm_sub z w
      rw [hw] at h1
      have h2 : R = κ * ‖z‖ / 2 := hRdef
      linarith
    calc ‖phifun m G w - Afun m G w‖ ≤ D * ‖w‖ := hgrowth w hwdom
      _ ≤ D * (‖z‖ * (1 + κ)) := mul_le_mul_of_nonneg_left hwle hD
      _ = D * (1 + κ) * ‖z‖ := by ring
  -- identify `deriv E z` with the difference of the two derivatives
  have hdz : DifferentiableAt ℂ (phifun m G) z :=
    hdiff.differentiableAt ((isOpen_Dom m ρ).mem_nhds hzDom)
  have hdAz : DifferentiableAt ℂ (Afun m G) z :=
    hA.differentiableAt ((isOpen_Dom m ρ).mem_nhds hzDom)
  have hderiv : deriv (fun w => phifun m G w - Afun m G w) z
      = deriv (phifun m G) z - deriv (Afun m G) z := by
    have h : (fun w => phifun m G w - Afun m G w) = (phifun m G - Afun m G) := rfl
    rw [h]
    exact deriv_sub hdz hdAz
  rw [← hderiv]
  -- Cauchy's estimate, then the elementary simplification of the quotient
  have hbound := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := fun w => phifun m G w - Afun m G w) hRpos hcont hsphere
  refine le_trans hbound ?_
  have key : D * (1 + κ) * ‖z‖ / R = 2 * D * (1 + κ) / κ := by
    rw [hRdef]
    have h1 : ‖z‖ ≠ 0 := ne_of_gt hznorm
    have h2 : κ ≠ 0 := ne_of_gt hκ
    field_simp
  rw [key]

end Work.FatouDeg.Petal
