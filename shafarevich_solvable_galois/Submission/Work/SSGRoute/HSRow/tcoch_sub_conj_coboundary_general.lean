import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.HSRow

/-- **The transgression difference is a coboundary (abstract group version).**

Over an abstract group `Γ` acting on an additive group `M` through `ρ : Γ →* G`, let `c : Γ → Γ → M`
be a `2`-cochain which is the coboundary of a `1`-cochain `b` on a subgroup `D`,
`c g h = ρ g • b h - b (g * h) + b g` for `g, h ∈ D`, and let `σ ∈ D` normalise `I ≤ D`
(`σ⁻¹ * n * σ ∈ I` for `n ∈ I`).

Then for `n ∈ I` the expression
`tprim σ c β n - β n - (ρ σ • (β - b)(σ⁻¹ n σ) - (β - b) n)`,
where `tprim σ c β n = ρ σ • β (σ⁻¹ n σ) - c σ (σ⁻¹ n σ) + ρ n • c σ σ⁻¹ - c (n σ) σ⁻¹ + c 1 1`,
equals the coboundary `ρ n • b σ - b σ` of the value `b σ`.  No hypothesis on `β` is needed: the
`β`-terms cancel. -/
theorem tcoch_sub_conj_coboundary_general {Γ G M : Type*} [Group Γ] [Group G]
    [AddCommGroup M] [DistribMulAction G M]
    (ρ : Γ →* G) (D I : Subgroup Γ) (σ : Γ) (hσ : σ ∈ D) (hI : I ≤ D)
    (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I)
    (c : Γ → Γ → M) (b β : Γ → M)
    (hbcob : ∀ g ∈ D, ∀ h ∈ D, c g h = ρ g • b h - b (g * h) + b g)
    (hc11 : c 1 1 = 0) :
    ∀ n ∈ I,
      (ρ σ • β (σ⁻¹ * n * σ) - c σ (σ⁻¹ * n * σ) + ρ n • c σ σ⁻¹
          - c (n * σ) σ⁻¹ + c 1 1 - β n)
        - (ρ σ • (β (σ⁻¹ * n * σ) - b (σ⁻¹ * n * σ)) - (β n - b n))
      = ρ n • b σ - b σ := by
  intro n hn
  -- membership facts
  have hDσinv : σ⁻¹ ∈ D := D.inv_mem hσ
  have hDn : n ∈ D := hI hn
  have hDA : σ⁻¹ * n * σ ∈ D := hI (hnorm2 n hn)
  have hDnσ : n * σ ∈ D := D.mul_mem hDn hσ
  -- `c 1 1 = b 1`, hence `b 1 = 0`
  have hb1 : b 1 = 0 := by
    have h := hbcob 1 D.one_mem 1 D.one_mem
    rw [hc11] at h
    simpa using h.symm
  -- the three coboundary expansions
  have hc1 : c σ (σ⁻¹ * n * σ) = ρ σ • b (σ⁻¹ * n * σ) - b (n * σ) + b σ := by
    rw [hbcob σ hσ (σ⁻¹ * n * σ) hDA,
        show σ * (σ⁻¹ * n * σ) = n * σ by group]
  have hc2 : c σ σ⁻¹ = ρ σ • b σ⁻¹ - b 1 + b σ := by
    rw [hbcob σ hσ σ⁻¹ hDσinv, show σ * σ⁻¹ = 1 by group]
  have hc3 : c (n * σ) σ⁻¹ = ρ (n * σ) • b σ⁻¹ - b n + b (n * σ) := by
    rw [hbcob (n * σ) hDnσ σ⁻¹ hDσinv, show (n * σ) * σ⁻¹ = n by group]
  -- assemble and simplify
  rw [hc1, hc2, hc3, hc11, hb1, map_mul]
  simp only [mul_smul, smul_sub, smul_add, sub_zero, add_zero]
  abel

end Work.SSGRoute.HSRow
