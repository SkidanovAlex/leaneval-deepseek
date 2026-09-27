import Mathlib

/-!
# The `C¹`-closeness ball for the first-order remainder

Step (a) of the germ-extension recipe (`NOTES_hasFingerData_S33.md` §6, §10): for a globally `C^∞`
map `Φ : ℝ^N → ℝ^N` whose derivative at `0` is injective, the *first-order remainder*
`W z := Φ z - Φ 0 - Ae z` (where `Ae` is the linear part, i.e. the continuous linear equivalence
built from `fderiv ℝ Φ 0`) has derivative of arbitrarily small norm on a ball around `0`.  This is
just continuity of `fderiv ℝ Φ` at `0` together with `fderiv ℝ W 0 = 0`.

The statement is ε- and ρ-quantified as `∃ Ae ε ρ, 0 < ε ∧ 0 < ρ ∧ …` with `ε := 1`: consumers
that need a *prescribed* `ε` (the interpolated map of the germ lemma needs `‖fderiv ℝ W‖` small
compared with `‖Ae.symm‖⁻¹`) should instantiate the same construction with their own `ε` — the proof
below is uniform in `ε`.
-/

open scoped ContDiff Topology

namespace Work.Whitney.CutPush

theorem exists_fderiv_close_of_contDiff {N : ℕ}
    (Φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hd : Function.Injective (fderiv ℝ Φ 0)) :
    ∃ (Ae : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)) (ε ρ : ℝ),
      0 < ε ∧ 0 < ρ ∧
      (Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) = fderiv ℝ Φ 0 ∧
      (∀ y : EuclideanSpace ℝ (Fin N), ‖y‖ < ρ →
        ‖fderiv ℝ (fun z => Φ z - Φ 0 - Ae z) y‖ ≤ ε) := by
  classical
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hker : (fderiv ℝ Φ 0).ker = ⊥ := LinearMap.ker_eq_bot.mpr hd
  have hsurj : (fderiv ℝ Φ 0).range = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hd)
  let Ae : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N) :=
    ContinuousLinearEquiv.ofBijective (fderiv ℝ Φ 0) hker hsurj
  have hAe : (Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) = fderiv ℝ Φ 0 :=
    DFunLike.coe_injective
      (ContinuousLinearEquiv.coeFn_ofBijective (fderiv ℝ Φ 0) hker hsurj)
  -- continuity of the derivative at `0` gives the ball
  have hcont : ContinuousAt (fderiv ℝ Φ) (0 : EuclideanSpace ℝ (Fin N)) :=
    (hΦ.continuous_fderiv hne).continuousAt
  have hev : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℝ (Fin N)),
      ‖fderiv ℝ Φ y - fderiv ℝ Φ 0‖ ≤ 1 := by
    have h1 : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℝ (Fin N)),
        fderiv ℝ Φ y ∈ Metric.closedBall (fderiv ℝ Φ 0) 1 :=
      hcont.preimage_mem_nhds (Metric.closedBall_mem_nhds _ (by norm_num))
    refine h1.mono fun y hy => ?_
    rwa [Metric.mem_closedBall, dist_eq_norm] at hy
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨Ae, 1, ρ, one_pos, hρ, hAe, ?_⟩
  intro y hy
  have hy' : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin N)) ρ := by
    simpa [Metric.mem_ball, dist_zero_right] using hy
  have hyb : ‖fderiv ℝ Φ y - fderiv ℝ Φ 0‖ ≤ 1 := hsub hy'
  have hder : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin N) => Φ z - Φ 0 - Ae z) y
      = fderiv ℝ Φ y - (Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) := by
    have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin N) => Φ z - Φ 0 - Ae z)
        (fderiv ℝ Φ y - 0 - (Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))) y :=
      (((hΦ.contDiffAt (x := y)).differentiableAt hne).hasFDerivAt.sub
        (hasFDerivAt_const (c := Φ 0) (x := y))).sub
        (ContinuousLinearMap.hasFDerivAt
          (Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)))
    rw [h1.fderiv]
    simp
  rw [hder, hAe]
  exact hyb

/-- **The `C¹`-closeness ball with a prescribed bound.**  The construction of
`exists_fderiv_close_of_contDiff` is uniform in `ε`: this version hands the caller the bound `c` it
needs.  The assembly `(c)` of the germ recipe (`NOTES_hasFingerData_S33.md` §10–§12) needs this,
because the interpolated perturbation `V := Ae⁻¹ ∘ (χ • W)` has Lipschitz constant bounded by
`‖Ae.symm‖ (Lip χ · sup ‖W‖ + sup ‖fderiv ℝ W‖)`, and the cutoff `χ` of
`lipschitz_smooth_cutoff` has `Lip χ ~ 1/r` on a support of radius `3 r` while `sup ‖W‖ ≤ c · 3 r`:
the product term is `~ 3 c Lip(χ) r` and is *not* improved by shrinking `r` unless `c` is prescribed
small. -/
theorem exists_fderiv_close_of_contDiff' {N : ℕ}
    (Φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hd : Function.Injective (fderiv ℝ Φ 0)) (c : ℝ) (hc : 0 < c) :
    ∃ (Ae : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)) (ρ : ℝ),
      0 < ρ ∧ (Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) = fderiv ℝ Φ 0 ∧
      (∀ y : EuclideanSpace ℝ (Fin N), ‖y‖ < ρ →
        ‖fderiv ℝ (fun z => Φ z - Φ 0 - Ae z) y‖ ≤ c) := by
  classical
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hker : (fderiv ℝ Φ 0).ker = ⊥ := LinearMap.ker_eq_bot.mpr hd
  have hsurj : (fderiv ℝ Φ 0).range = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hd)
  let Ae : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N) :=
    ContinuousLinearEquiv.ofBijective (fderiv ℝ Φ 0) hker hsurj
  have hAe : (Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) = fderiv ℝ Φ 0 :=
    DFunLike.coe_injective
      (ContinuousLinearEquiv.coeFn_ofBijective (fderiv ℝ Φ 0) hker hsurj)
  have hcont : ContinuousAt (fderiv ℝ Φ) (0 : EuclideanSpace ℝ (Fin N)) :=
    (hΦ.continuous_fderiv hne).continuousAt
  have hev : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℝ (Fin N)),
      ‖fderiv ℝ Φ y - fderiv ℝ Φ 0‖ ≤ c := by
    have h1 : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℝ (Fin N)),
        fderiv ℝ Φ y ∈ Metric.closedBall (fderiv ℝ Φ 0) c :=
      hcont.preimage_mem_nhds (Metric.closedBall_mem_nhds _ hc)
    refine h1.mono fun y hy => ?_
    rwa [Metric.mem_closedBall, dist_eq_norm] at hy
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨Ae, ρ, hρ, hAe, ?_⟩
  intro y hy
  have hy' : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin N)) ρ := by
    simpa [Metric.mem_ball, dist_zero_right] using hy
  have hyb : ‖fderiv ℝ Φ y - fderiv ℝ Φ 0‖ ≤ c := hsub hy'
  have hder : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin N) => Φ z - Φ 0 - Ae z) y
      = fderiv ℝ Φ y - (Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) := by
    have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin N) => Φ z - Φ 0 - Ae z)
        (fderiv ℝ Φ y - 0 - (Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))) y :=
      (((hΦ.contDiffAt (x := y)).differentiableAt hne).hasFDerivAt.sub
        (hasFDerivAt_const (c := Φ 0) (x := y))).sub
        (ContinuousLinearMap.hasFDerivAt
          (Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)))
    rw [h1.fderiv]
    simp
  rw [hder, hAe]
  exact hyb

/-- **The `C¹`-closeness ball for a *given* linear part.**  Trap 13c of
`NOTES_hasFingerData_S33.md` §13: the two lemmas above *return* `Ae`, but the assembly `(c)` must
choose `c` from `‖Ae.symm‖` *before* asking for the ball (the constant is
`c < (2 ‖Ae.symm‖ (3 C₁ + 1))⁻¹`).  This variant takes the linear part as input, which removes the
circularity: the caller builds
`Ae := ContinuousLinearEquiv.ofBijective (fderiv ℝ Φ 0) _ _` by hand, picks `c`, and then obtains
the ball. -/
theorem exists_fderiv_close_of_contDiff'' {N : ℕ}
    (Φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (Ae : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N))
    (hAe : (Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) = fderiv ℝ Φ 0)
    (c : ℝ) (hc : 0 < c) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ y : EuclideanSpace ℝ (Fin N), ‖y‖ < ρ →
        ‖fderiv ℝ (fun z => Φ z - Φ 0 - Ae z) y‖ ≤ c) := by
  classical
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hcont : ContinuousAt (fderiv ℝ Φ) (0 : EuclideanSpace ℝ (Fin N)) :=
    (hΦ.continuous_fderiv hne).continuousAt
  have hev : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℝ (Fin N)),
      ‖fderiv ℝ Φ y - fderiv ℝ Φ 0‖ ≤ c := by
    have h1 : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℝ (Fin N)),
        fderiv ℝ Φ y ∈ Metric.closedBall (fderiv ℝ Φ 0) c :=
      hcont.preimage_mem_nhds (Metric.closedBall_mem_nhds _ hc)
    refine h1.mono fun y hy => ?_
    rwa [Metric.mem_closedBall, dist_eq_norm] at hy
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨ρ, hρ, fun y hy => ?_⟩
  have hy' : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin N)) ρ := by
    simpa [Metric.mem_ball, dist_zero_right] using hy
  have hyb : ‖fderiv ℝ Φ y - fderiv ℝ Φ 0‖ ≤ c := hsub hy'
  have hder : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin N) => Φ z - Φ 0 - Ae z) y
      = fderiv ℝ Φ y - (Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) := by
    have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin N) => Φ z - Φ 0 - Ae z)
        (fderiv ℝ Φ y - 0 - (Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))) y :=
      (((hΦ.contDiffAt (x := y)).differentiableAt hne).hasFDerivAt.sub
        (hasFDerivAt_const (c := Φ 0) (x := y))).sub
        (ContinuousLinearMap.hasFDerivAt
          (Ae : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)))
    rw [h1.fderiv]
    simp
  rw [hder, hAe]
  exact hyb

end Work.Whitney.CutPush
