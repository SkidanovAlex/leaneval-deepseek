import Mathlib
import Submission.Work.HornSC.JC.exists_injective_lift

namespace Work.HornSC.CellBoundaryJordan

/-- **Extraction of an `n`-th root of a closed curve.**  If `γ : Circle → ℂ` is injective and
`θ : ℝ → ℂ` is a continuous lift of `t ↦ γ (exp (2π i t))` through the exponential which gains
exactly `n · 2π i` when `t` is shifted by `1` (i.e. the curve winds `n` times around `0`), then
`γ` has an injective continuous `n`-th root `g`, given explicitly by
`g (exp (2π i t)) = exp (θ t / n)`. -/
theorem rootCircleMap {γ : C(Circle, ℂ)} (hγ : Function.Injective γ)
    {θ : ℝ → ℂ} (hθc : Continuous θ)
    (hθexp : ∀ t, Complex.exp (θ t) = γ (Circle.exp (2 * Real.pi * t)))
    {n : ℕ} (hn : 0 < n)
    (hθper : ∀ t, θ (t + 1) = θ t + (n : ℂ) * (2 * Real.pi * Complex.I)) :
    ∃ g : C(Circle, ℂ), Function.Injective g ∧
      (∀ z : Circle, (g z) ^ n = γ z) ∧
      (∀ t : ℝ, g (Circle.exp (2 * Real.pi * t)) = Complex.exp (θ t / (n : ℂ))) := by
  classical
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
  -- The `1`-periodic candidate on `ℝ`.
  set G : ℝ → ℂ := fun t => Complex.exp (θ t / (n : ℂ)) with hGdef
  have hGc : Continuous G := by
    simp only [hGdef]
    exact Complex.continuous_exp.comp (hθc.div_const (n : ℂ))
  have hGper : Function.Periodic G 1 := by
    intro t
    simp only [hGdef]
    rw [hθper t]
    have hsplit : (θ t + (n : ℂ) * (2 * Real.pi * Complex.I)) / (n : ℂ)
        = θ t / (n : ℂ) + 2 * Real.pi * Complex.I := by
      rw [add_div, mul_div_cancel_left₀ _ hnC]
    rw [hsplit, Complex.exp_add]
    have h2 : Complex.exp (2 * Real.pi * Complex.I) = 1 := by
      simpa using Complex.exp_two_pi_mul_I
    rw [h2, mul_one]
  -- Descend it to the circle using `arg`.
  set g₀ : Circle → ℂ := fun z => G (Complex.arg (z : ℂ) / (2 * Real.pi)) with hg₀def
  have hcomp : ∀ t : ℝ, g₀ (Circle.exp t) = G (t / (2 * Real.pi)) := by
    intro t
    simp only [hg₀def]
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp (Circle.exp_arg (Circle.exp t))
    rw [hm]
    have hdiv : (t + (m : ℝ) * (2 * Real.pi)) / (2 * Real.pi)
        = t / (2 * Real.pi) + (m : ℝ) := by
      field_simp
    rw [hdiv]
    simpa using (hGper.int_mul m (t / (2 * Real.pi)))
  have hq : Topology.IsQuotientMap (⇑Circle.exp) :=
    Circle.isCoveringMap_exp.isQuotientMap Circle.exp_surjective
  have hcont : Continuous g₀ := by
    rw [hq.continuous_iff]
    refine (hGc.comp (continuous_id.div_const (2 * Real.pi))).congr fun t => ?_
    exact (hcomp t).symm
  -- The power relation.
  have hpow : ∀ z : Circle, (g₀ z) ^ n = γ z := by
    intro z
    set w : ℝ := Complex.arg (z : ℂ) / (2 * Real.pi) with hwdef
    have hzw : Circle.exp (2 * Real.pi * w) = z := by
      have h2 : 2 * Real.pi * w = Complex.arg (z : ℂ) := by
        rw [hwdef]; field_simp
      rw [h2, Circle.exp_arg]
    have hgz : g₀ z = Complex.exp (θ w / (n : ℂ)) := by
      simp only [hg₀def, hGdef, hwdef]
    rw [hgz, ← Complex.exp_nat_mul, mul_comm (n : ℂ) (θ w / (n : ℂ)),
      div_mul_cancel₀ _ hnC, hθexp w, hzw]
  -- Injectivity.
  have hinj : Function.Injective g₀ := by
    intro z w hzw
    refine hγ ?_
    have h2 : (g₀ z) ^ n = (g₀ w) ^ n := by rw [hzw]
    rwa [hpow z, hpow w] at h2
  -- Value on the standard parametrisation.
  have hper : ∀ t : ℝ, g₀ (Circle.exp (2 * Real.pi * t)) = Complex.exp (θ t / (n : ℂ)) := by
    intro t
    have h := hcomp (2 * Real.pi * t)
    rw [show 2 * Real.pi * t / (2 * Real.pi) = t by field_simp] at h
    simpa only [hGdef] using h
  exact ⟨⟨g₀, hcont⟩, hinj, hpow, hper⟩

end Work.HornSC.CellBoundaryJordan
