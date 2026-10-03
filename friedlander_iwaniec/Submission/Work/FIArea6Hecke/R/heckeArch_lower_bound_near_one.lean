import Mathlib
import Submission.Work.FITop4.Bridge.area5_6_defs

/-!
# Lower bound for the archimedean factor `heckeArch d m` just right of `s = 1`

The archimedean factor of the completed Hecke `L`-function of `ℚ(i)` is

  `heckeArch d m s = X^s · Γ(s + |m|/2)`,     `X = 4d/π`   (`Work.FITop4.Bridge.heckeArch`),

a non-vanishing entire-ish function with no zeros on the closed half plane `Re s ≥ 0`
(`Gamma` has no zeros there; the base `X` is a positive real).  Consequently it is bounded
below by a positive constant on any compact subset of `Re s > 0`; here we need this in the
neighbourhood of `s = 1`, where every one of the contour-shift arguments of *FI* §16 lands.

The proof is uniform in `d ≥ 1` and in `m ∈ ℤ`:

* on the real axis, `X = 4d/π > 1`, so `‖X^σ‖ = X^σ ≥ 1`, and `Γ` of a positive real is a
  positive real, so `‖heckeArch d m σ‖ = X^σ · Γ(σ + |m|/2)` for real `σ > 0`;
* `σ ↦ X^σ · Γ(σ + |m|/2)` is continuous and positive on the compact interval `[1, 3/2]`,
  so it attains a positive minimum there, which serves as the constant `c` for `δ = 1/2`.

No explicit value of `c` is needed downstream; only the existence.
-/

namespace Work.FIArea6Hecke.R

/-- **Lower bound for the Hecke archimedean factor near `1`.** For every `d ≥ 1` and every
`m : ℤ` the archimedean factor `Work.FITop4.Bridge.heckeArch d m σ` is bounded below by a
positive constant on a right neighbourhood of `σ = 1`. -/
theorem heckeArch_lower_bound_near_one (d : ℕ) (m : ℤ) (hd : 1 ≤ d) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      c ≤ ‖Work.FITop4.Bridge.heckeArch d m (σ : ℂ)‖ := by
  set X : ℝ := 4 * (d : ℝ) / Real.pi with hXdef
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hX1 : 1 ≤ X := by
    rw [hXdef, le_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_four, hd1]
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  set a : ℝ := |(m : ℝ)| / 2 with hadef
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  -- the base of `heckeArch` is `↑X`
  have hbase : ((4 : ℂ) * ((d : ℝ) : ℂ) / ((Real.pi : ℝ) : ℂ)) = (X : ℂ) := by
    rw [hXdef]; push_cast; ring
  -- on the real axis the archimedean factor is the positive real `X^σ · Γ(σ + |m|/2)`
  have hval : ∀ σ : ℝ, 1 ≤ σ → σ ≤ 3/2 →
      ‖Work.FITop4.Bridge.heckeArch d m (σ : ℂ)‖ = X ^ σ * Real.Gamma (σ + a) := by
    intro σ h1 h2
    rw [Work.FITop4.Bridge.heckeArch, hbase, ← hadef, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
    have hg : ((σ : ℂ) + ((a : ℝ) : ℂ)) = ((σ + a : ℝ) : ℂ) := by push_cast; ring
    have hGa : 0 < Real.Gamma (σ + a) := Real.Gamma_pos_of_pos (by linarith)
    have hnorm : ‖(((Real.Gamma (σ + a)) : ℝ) : ℂ)‖ = Real.Gamma (σ + a) := by
      have h := RCLike.norm_ofReal (K := ℂ) (Real.Gamma (σ + a))
      rwa [abs_of_nonneg hGa.le] at h
    rw [hg, Complex.Gamma_ofReal, hnorm, Complex.ofReal_re]
  -- continuity of `σ ↦ X^σ · Γ(σ + |m|/2)` on `[1, 3/2]`
  have hgcont : ContinuousOn (fun σ : ℝ => X ^ σ * Real.Gamma (σ + a)) (Set.Icc 1 (3/2)) := by
    refine (Real.continuous_const_rpow hXpos.ne').continuousOn.mul ?_
    have h1 : ContinuousOn (fun σ : ℝ => (Complex.Gamma ((σ : ℂ) + (a : ℂ))).re)
        (Set.Icc 1 (3/2)) := by
      intro σ hσ
      have hσpos : (0 : ℝ) < σ + a := by linarith [hσ.1, ha0]
      have hne : ∀ k : ℕ, ((σ : ℂ) + (a : ℂ)) ≠ -↑k := by
        intro k hk
        have hre : (((σ : ℂ) + (a : ℂ))).re = -(k : ℝ) := by rw [hk]; simp
        have h2 : σ + a = -(k : ℝ) := by simpa using hre
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      have hlin : ContinuousAt (fun y : ℝ => ((y : ℂ) + (a : ℂ))) σ :=
        Complex.continuous_ofReal.continuousAt.add continuousAt_const
      have hΓ : ContinuousAt (fun y : ℝ => Complex.Gamma ((y : ℂ) + (a : ℂ))) σ :=
        ContinuousAt.comp (x := σ) (f := fun y : ℝ => ((y : ℂ) + (a : ℂ)))
          (Complex.continuousAt_Gamma ((σ : ℂ) + (a : ℂ)) hne) hlin
      exact (Complex.continuous_re.continuousAt.comp hΓ).continuousWithinAt
    refine h1.congr ?_
    intro σ hσ
    simp [Real.Gamma, Complex.ofReal_add]
  -- positivity of the same function on `[1, 3/2]`
  have hgpos : ∀ σ ∈ Set.Icc 1 (3/2), 0 < X ^ σ * Real.Gamma (σ + a) := by
    intro σ hσ
    exact mul_pos (Real.rpow_pos_of_pos hXpos σ)
      (Real.Gamma_pos_of_pos (by linarith [hσ.1, ha0]))
  -- the minimum of the continuous function on the compact interval `[1, 3/2]`
  obtain ⟨σ0, hσ0, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr (by norm_num)) hgcont
  refine ⟨X ^ σ0 * Real.Gamma (σ0 + a), 1/2, hgpos σ0 hσ0, by norm_num, ?_⟩
  intro σ hσ1 hσ2
  rw [hval σ (le_of_lt hσ1) (by linarith)]
  exact hmin ⟨by linarith, by linarith⟩

end Work.FIArea6Hecke.R
