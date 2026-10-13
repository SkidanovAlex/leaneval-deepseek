import Mathlib
import Submission.Work.WilC4aA.Defs

open Classical Topology Filter Set

namespace Work.WilC4aA

/-- **Puiseux change of variable along an analytic arc.**  If `t(s) = s^N u(s)` with `N ≥ 1`,
`u 0 > 0`, and `y` has one-sided integer asymptotics at `0⁺`, then `t > 0` near `0⁺` and the
`t`-parametrised value `y(s)` has asymptotics `b t^q` with `q : ℚ` rational (or `y` vanishes
near `0⁺`).

Indeed, writing `y(s) ~ b s^k` and `q = k/N`, on `s ∈ (0,δ)` one has
`y(s)/t(s)^q = (y(s)/s^k) · u(s)^{-q}`, whose limit `b · u(0)^{-q}` is nonzero. -/
theorem asym_div_rpow {t y u : ℝ → ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hu : AnalyticAt ℝ u 0) (hu0 : 0 < u 0)
    (ht : t =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun s => s ^ N * u s))
    (hy : Work.WilC4aA.HasAsymAt0 y) :
    (∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t s) ∧
      ((y =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] 0) ∨
        ∃ (q : ℚ) (b : ℝ), b ≠ 0 ∧
          Filter.Tendsto (fun s : ℝ => y s / t s ^ ((q : ℝ)))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds b)) := by
  -- `u` is continuous at `0` and positive there, hence positive near `0⁺`.
  have hulim : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 (u 0)) :=
    hu.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hupos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < u s :=
    hulim.eventually (Ioi_mem_nhds hu0)
  have hune : u 0 ≠ 0 := ne_of_gt hu0
  -- Positivity of `t` near `0⁺` is immediate from `t = s^N u(s)`.
  have htpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < t s := by
    filter_upwards [ht, hupos, self_mem_nhdsWithin] with s hts hus hs
    rw [hts]
    exact mul_pos (pow_pos (Set.mem_Ioi.mp hs) N) hus
  refine ⟨htpos, ?_⟩
  rcases hy with hy0 | ⟨k, b, hb, hT⟩
  · exact Or.inl hy0
  · -- The chosen exponent is `q = k / N`, so that `N q = k`.
    right
    refine ⟨(k : ℚ) / N, b * (u 0) ^ (-(((k : ℚ) / N : ℚ) : ℝ)), ?_, ?_⟩
    · exact mul_ne_zero hb (ne_of_gt (Real.rpow_pos_of_pos hu0 _))
    · have hNq : (N : ℝ) * (((k : ℚ) / N : ℚ) : ℝ) = (k : ℝ) := by
        have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hN)
        push_cast
        field_simp
      -- On `(0,δ)` the quotient `y s / t s^q` equals `(y s / s^k) · u(s)^{-q}`.
      have hev : (fun s : ℝ => y s / t s ^ ((((k : ℚ) / N : ℚ) : ℝ)))
          =ᶠ[𝓝[>] (0 : ℝ)]
            (fun s : ℝ =>
              (y s / s ^ ((k : ℤ) : ℝ)) * (u s) ^ (-(((k : ℚ) / N : ℚ) : ℝ))) := by
        filter_upwards [ht, hupos, self_mem_nhdsWithin] with s hts hus hs
        have hs' : 0 < s := Set.mem_Ioi.mp hs
        rw [hts, Real.mul_rpow (le_of_lt (pow_pos hs' N)) (le_of_lt hus),
          ← Real.rpow_natCast_mul (le_of_lt hs') N (((k : ℚ) / N : ℚ) : ℝ), hNq,
          Real.rpow_neg (le_of_lt hus), div_mul_eq_div_mul_one_div, inv_eq_one_div]
      have hU : Tendsto (fun s : ℝ => (u s) ^ (-(((k : ℚ) / N : ℚ) : ℝ))) (𝓝[>] (0 : ℝ))
          (𝓝 ((u 0) ^ (-(((k : ℚ) / N : ℚ) : ℝ)))) := hulim.rpow_const (Or.inl hune)
      exact (hT.mul hU).congr' hev.symm

end Work.WilC4aA
