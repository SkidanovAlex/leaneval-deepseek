import Mathlib
import Submission.Work.Twist.away_chart_mvPolynomial
import Submission.Work.PointlessIndexFive.Model

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

/-- **The chart ring `A⁰_{X₀}` of `ℙⁿ` at `X₀` is a polynomial ring, compatibly with the
constants.**  `Work.Twist.away_chart_mvPolynomial` provides a ring isomorphism
`chartPsi : A⁰_{X₀} ≃+* 𝕜[y₁,…,yₙ]` (with `chartPsi (Away.mk _ _ N a ha) = chartDhom 𝕜 n a`).
The present statement records that this isomorphism identifies the structure map
`𝒜 0 →+* A⁰_{X₀}` coming from the grading with the map `c ↦ C (zeroComponentEquiv 𝕜 n c)`, i.e.
that a constant of `𝕜[X₀,…,Xₙ]` maps to the corresponding constant of `𝕜[y₁,…,yₙ]`.

Route: `ChartAway 𝕜 n = HomogeneousLocalization.Away (stdGrading 𝕜 n) (X 0)`; take
`e := RingEquiv.ofBijective (chartPsi 𝕜 n) ⟨chartPsi_injective 𝕜 n, chartPsi_surjective 𝕜 n⟩`.
For `c : ↥(stdGrading 𝕜 n 0)` the element `fromZeroRingHom 𝒜 (Submonoid.powers (X 0)) c` is the
fraction `c / X₀ ^ 0`, i.e. `Away.mk 𝒜 (X0_mem_stdGrading 𝕜 n) 0 c c.2`, so `chartPsi_awayMk`
gives `e _ = chartDhom 𝕜 n c.1`.  Finally `c.1 = C (zeroComponentEquiv 𝕜 n c)` by
`(Work.PointlessIndexFive.exists_zeroComponentRingEquiv 𝕜 (Fin (n+1))).choose_spec`, and
`chartDhom 𝕜 n (C r) = C r` because `chartDhom` is an `eval₂Hom` over `algebraMap 𝕜 _`. -/
theorem exists_chart_away_X_zero_compat (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    ∃ e : HomogeneousLocalization.Away (Work.Twist.stdGrading 𝕜 n) (MvPolynomial.X (0 : Fin (n+1))) ≃+*
        MvPolynomial (Fin n) 𝕜,
      ∀ c : ↥(Work.Twist.stdGrading 𝕜 n 0),
        e (HomogeneousLocalization.fromZeroRingHom (Work.Twist.stdGrading 𝕜 n)
            (Submonoid.powers (MvPolynomial.X (0 : Fin (n+1)))) c)
          = MvPolynomial.C (Work.PointlessIndexFive.zeroComponentEquiv 𝕜 n c) := by
  refine ⟨RingEquiv.ofBijective (Work.Twist.chartPsi 𝕜 n)
    ⟨Work.Twist.chartPsi_injective 𝕜 n, Work.Twist.chartPsi_surjective 𝕜 n⟩, ?_⟩
  intro c
  -- The degree-zero element `c / X₀ ^ 0` of the homogeneous localisation, written as `Away.mk`.
  have hx : c.1 ∈ Work.Twist.stdGrading 𝕜 n (0 • 1) := by rw [zero_smul]; exact c.2
  -- `fromZeroRingHom` is the fraction with numerator `c` and denominator `1 = X₀ ^ 0`.
  have hmk : HomogeneousLocalization.fromZeroRingHom (Work.Twist.stdGrading 𝕜 n)
        (Submonoid.powers (MvPolynomial.X (0 : Fin (n + 1)))) c
      = HomogeneousLocalization.Away.mk (Work.Twist.stdGrading 𝕜 n)
          (Work.Twist.X0_mem_stdGrading 𝕜 n) 0 c.1 hx := by
    have h1 : HomogeneousLocalization.fromZeroRingHom (Work.Twist.stdGrading 𝕜 n)
        (Submonoid.powers (MvPolynomial.X (0 : Fin (n + 1)))) c
          = HomogeneousLocalization.mk ⟨0, c, 1, one_mem _⟩ := rfl
    rw [h1]
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.Away.val_mk]
    simp
  rw [hmk]
  -- `RingEquiv.ofBijective (chartPsi 𝕜 n) _` acts as `chartPsi 𝕜 n`.
  change Work.Twist.chartPsi 𝕜 n (HomogeneousLocalization.Away.mk (Work.Twist.stdGrading 𝕜 n)
          (Work.Twist.X0_mem_stdGrading 𝕜 n) 0 c.1 hx) = _
  rw [Work.Twist.chartPsi_awayMk]
  -- `c` is a constant, so it is `C r` for `r = zeroComponentEquiv 𝕜 n c`.
  rw [← (Work.PointlessIndexFive.exists_zeroComponentRingEquiv 𝕜 (Fin (n + 1))).choose_spec c]
  -- `chartDhom` is an `eval₂Hom` over `algebraMap 𝕜 _`, hence fixes constants.
  rw [Work.Twist.chartDhom, MvPolynomial.eval₂Hom_C, MvPolynomial.algebraMap_eq]
  rfl

end Work.Twist
