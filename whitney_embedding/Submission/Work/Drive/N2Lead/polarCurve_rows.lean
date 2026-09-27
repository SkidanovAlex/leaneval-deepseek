import Mathlib
import Submission.Work.Drive.N2.saddleWindowBlock

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology in
/-- **The rows of the packet's polar curve** (§3.2 step 2 of `N2Lead/NOTES_LEAD_saddlePacket.md`).

Let `r : ℝ → ℝ` be a positive smooth `2π`-periodic *radial profile* (in the packet it is
`Work.Drive.N2Lead.mobius_lowerProfile`'s `r`), and let `Θ : ℝ → ℝ` be a smooth strictly increasing
angle function with `deriv Θ ≠ 0` and `Θ (t + 1) = Θ t + 2 π` (in the packet it is produced by
`circleArcExtension` composed with the arc lifts `Work.Drive.N2Lead.exists_arcLift`).  Then the
planar polar curve

  `C₀ t = cE3 (r (Θ t) * exp (i Θ t))`

satisfies exactly the four rows that `Work.Drive.N2Lead.exists_picture_of_curves` consumes:

* `C₀` is `C^∞`;
* `C₀ (t + 1) = C₀ t` (because `r` is `2π`-periodic and `Θ` jumps by `2π`);
* `C₀ s = C₀ t` forces `s = t + k` for some `k : ℤ` (polar coordinates with a *positive* radius are
  injective, and the strict monotonicity of `Θ` with `Θ (t+1) = Θ t + 2π` pins the period);
* `deriv C₀ t ≠ 0` (the velocity of `(r (Θ t), Θ t)` in polar coordinates is
  `(r' (Θ t) + i r (Θ t)) · Θ' t · exp (i Θ t)`, and `r > 0`, `Θ' ≠ 0`). -/
theorem polarCurve_rows {r Θ : ℝ → ℝ}
    (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r) (hrpos : ∀ φ : ℝ, 0 < r φ)
    (hrper : ∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ)
    (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ) (hΘmono : StrictMono Θ)
    (hΘderiv : ∀ t : ℝ, deriv Θ t ≠ 0)
    (hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => Work.Drive.N2.cE3 (r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))) ∧
      (∀ t : ℝ, r (Θ (t + 1)) * Complex.exp (((Θ (t + 1) : ℝ) : ℂ) * Complex.I)
        = r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)) ∧
      (∀ s t : ℝ, r (Θ s) * Complex.exp (((Θ s : ℝ) : ℂ) * Complex.I)
          = r (Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) → ∃ k : ℤ, s = t + k) ∧
      (∀ t : ℝ, deriv (fun u : ℝ =>
        Work.Drive.N2.cE3 (r (Θ u) * Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I))) t ≠ 0) := by
  -- ### the integer shift of `Θ`
  -- `g u = Θ u - 2πu` is `1`-periodic, so `Θ (t + k) = Θ t + 2πk` for every `k : ℤ`.
  have hshift : ∀ (k : ℤ) (t : ℝ), Θ (t + k) = Θ t + k * (2 * Real.pi) := by
    let g : ℝ → ℝ := fun u => Θ u - 2 * Real.pi * u
    have hgper : Function.Periodic g 1 := by
      intro x
      show g (x + 1) = g x
      simp only [g]
      rw [hΘper x]
      ring
    intro k t
    have h := (hgper.int_mul k) t
    simp only [mul_one] at h
    simp only [g] at h
    rw [mul_add] at h
    have h2 : Θ (t + ↑k) = Θ t + 2 * Real.pi * ↑k := by linarith
    rw [h2]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ### smoothness
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (r (Θ t) : ℂ)) :=
      ContDiff.comp Complex.ofRealCLM.contDiff (ContDiff.comp hr hΘ)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => ((Θ t : ℝ) : ℂ)) :=
      ContDiff.comp Complex.ofRealCLM.contDiff hΘ
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)) :=
      ContDiff.comp Complex.contDiff_exp (ContDiff.mul h2 contDiff_const)
    exact ContDiff.comp Work.Drive.N2.cE3.contDiff (ContDiff.mul h1 h3)
  · -- ### periodicity
    intro t
    have h1 : r (Θ (t + 1)) = r (Θ t) := by rw [hΘper t]; exact hrper (Θ t)
    have h2 : Complex.exp (((Θ (t + 1) : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) := by
      rw [hΘper t]
      have hcast : ((Θ t + 2 * Real.pi : ℝ) : ℂ) * Complex.I
          = ((Θ t : ℝ) : ℂ) * Complex.I + (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast; ring
      rw [hcast, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    rw [h1, h2]
  · -- ### injectivity modulo the period
    intro s t hEq
    have hval : r (Θ s) = r (Θ t) := by
      have h := congrArg (fun z : ℂ => ‖z‖) hEq
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] at h
      simpa [abs_of_pos (hrpos (Θ s)), abs_of_pos (hrpos (Θ t))] using h
    have hexp : Complex.exp (((Θ s : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) := by
      have h := hEq
      rw [← hval] at h
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (hrpos (Θ s)))) h
    rw [Complex.exp_eq_exp_iff_exists_int] at hexp
    obtain ⟨n, hn⟩ := hexp
    have h3 : ((Θ s : ℝ) : ℂ) = ((Θ t : ℝ) : ℂ) + ((n : ℝ) : ℂ) * (2 * (Real.pi : ℂ)) := by
      have hn' : ((Θ s : ℝ) : ℂ) * Complex.I
          = (((Θ t : ℝ) : ℂ) + ((n : ℝ) : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
        rw [hn]; push_cast; ring
      exact mul_right_cancel₀ Complex.I_ne_zero hn'
    have h5 : Θ s = Θ t + (n : ℝ) * (2 * Real.pi) := by
      have hh := congrArg Complex.re h3
      simpa using hh
    refine ⟨n, ?_⟩
    have hs : Θ s = Θ (t + (n : ℝ)) := by
      rw [hshift n t]; exact h5
    exact hΘmono.injective hs
  · -- ### nonvanishing velocity
    intro t
    have hΘd : HasDerivAt Θ (deriv Θ t) t :=
      ((hΘ.differentiable (by simp)).differentiableAt).hasDerivAt
    have hrd : HasDerivAt r (deriv r (Θ t)) (Θ t) :=
      ((hr.differentiable (by simp)).differentiableAt).hasDerivAt
    have h1 : HasDerivAt (fun u : ℝ => (r (Θ u) : ℂ))
        (((deriv r (Θ t) * deriv Θ t : ℝ)) : ℂ) t :=
      (hrd.comp t hΘd).ofReal_comp
    have h2a : HasDerivAt (fun u : ℝ => ((Θ u : ℝ) : ℂ)) ((deriv Θ t : ℝ) : ℂ) t :=
      hΘd.ofReal_comp
    have h2 : HasDerivAt (fun u : ℝ => Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I))
        (Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) * (((deriv Θ t : ℝ) : ℂ) * Complex.I)) t :=
      (h2a.mul_const Complex.I).cexp
    have hF := h1.mul h2
    set E : ℂ := Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) with hEdef
    have hne : (((deriv r (Θ t) * deriv Θ t : ℝ)) : ℂ) * E
        + ((r (Θ t) : ℝ) : ℂ) * (E * (((deriv Θ t : ℝ) : ℂ) * Complex.I)) ≠ 0 := by
      have hDne : (((deriv Θ t : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hΘderiv t
      have hBrne : (((deriv r (Θ t) : ℝ)) : ℂ) + ((r (Θ t) : ℝ) : ℂ) * Complex.I ≠ 0 := by
        intro h
        have hh := congrArg Complex.im h
        simp at hh
        linarith [hrpos (Θ t)]
      have hfac : (((deriv r (Θ t) * deriv Θ t : ℝ)) : ℂ) * E
          + ((r (Θ t) : ℝ) : ℂ) * (E * (((deriv Θ t : ℝ) : ℂ) * Complex.I))
          = E * ((((deriv Θ t : ℝ)) : ℂ)
              * ((((deriv r (Θ t) : ℝ)) : ℂ) + ((r (Θ t) : ℝ) : ℂ) * Complex.I)) := by
        push_cast; ring
      rw [hfac]
      exact mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero hDne hBrne)
    have hcE3 : HasDerivAt (fun u : ℝ => Work.Drive.N2.cE3
          ((r (Θ u) : ℂ) * Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I)))
        (Work.Drive.N2.cE3 ((((deriv r (Θ t) * deriv Θ t : ℝ)) : ℂ) * E
          + ((r (Θ t) : ℝ) : ℂ) * (E * (((deriv Θ t : ℝ) : ℂ) * Complex.I)))) t :=
      (ContinuousLinearMap.hasFDerivAt Work.Drive.N2.cE3).comp_hasDerivAt t hF
    rw [hcE3.deriv]
    intro hz
    exact hne (Work.Drive.N2.cE3_injective (by simpa using hz))

end Work.Drive.N2Lead
