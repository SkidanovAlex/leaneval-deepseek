import Mathlib

namespace Work.Drive.Push

open scoped ContDiff

/-- **The auxiliary projection family `Q t = P t - proj_{P t e}`**: for a globally projecting smooth
family `P` of constant rank `k` and a vector `e` with `P t e ≠ 0` for all `t`, the family
`Q t x := P t x - (⟪P t e, x⟫ / ‖P t e‖²) • P t e` is a globally defined jointly smooth family of
orthogonal projections of constant rank `k - 1` whose range is `range (P t) ∩ (P t e)ᗮ`. -/
theorem planeFamilyQ {N k : ℕ}
    (P : ℝ → EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (hPsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) => P p.1 p.2))
    (hidem : ∀ t, P t * P t = P t)
    (hsa : ∀ t (x y : EuclideanSpace ℝ (Fin N)), inner ℝ (P t x) y = inner ℝ x (P t y))
    (hrank : ∀ t, Module.finrank ℝ (LinearMap.range (P t).toLinearMap) = k)
    (e : EuclideanSpace ℝ (Fin N)) (he : e ≠ 0)
    (hPe : ∀ t, P t e ≠ 0) :
    ∃ Q : ℝ → EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => Q p.1 p.2) ∧
      (∀ t, Q t * Q t = Q t) ∧
      (∀ t, Module.finrank ℝ (LinearMap.range (Q t).toLinearMap) = k - 1) ∧
      (∀ t, Q t e = 0) ∧
      (∀ t (u : EuclideanSpace ℝ (Fin N)), inner ℝ u e = 0 → inner ℝ (Q t u) e = 0) ∧
      (∀ t (x : EuclideanSpace ℝ (Fin N)),
        Q t x = P t x - (inner ℝ (P t e) x / ‖P t e‖ ^ 2) • P t e) ∧
      (∀ t (v : EuclideanSpace ℝ (Fin N)), P t v = v → inner ℝ v (P t e) = 0 → Q t v = v) := by
  -- The candidate family: `Q t = P t - ‖P t e‖⁻² • (inner (P t e)) ⊗ (P t e)`.
  let Q : ℝ → EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    fun t => P t - ((‖P t e‖ ^ 2)⁻¹ • innerSL ℝ (P t e)).smulRight (P t e)
  have _he : e ≠ 0 := he
  have hne_norm : ∀ t, (‖P t e‖ ^ 2) ≠ 0 := fun t =>
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (hPe t))
  -- `P t` is idempotent, pointwise.
  have hPP : ∀ t x, P t (P t x) = P t x := by
    intro t x
    have h : (P t * P t) x = P t x := DFunLike.congr_fun (hidem t) x
    rwa [mul_apply_eq_comp] at h
  -- The defining formula for `Q`.
  have hQform : ∀ t x, Q t x = P t x - (inner ℝ (P t e) x / ‖P t e‖ ^ 2) • P t e := by
    intro t x
    simp only [Q, sub_apply, ContinuousLinearMap.smulRight_apply, smul_apply, innerSL_apply_apply,
      div_eq_mul_inv, smul_eq_mul, mul_comm]
  -- `⟪P t e, e⟫ = ‖P t e‖²` (the residual `e - P t e` is orthogonal to `range (P t)`).
  have hse : ∀ t, inner ℝ (P t e) e = ‖P t e‖ ^ 2 := by
    intro t
    have h := hsa t (P t e) e
    rw [hPP t e] at h
    exact h.trans (real_inner_self_eq_norm_sq (P t e))
  -- `Q t` is idempotent, pointwise.
  have hQidem_pt : ∀ t x, Q t (Q t x) = Q t x := by
    intro t x
    have h3 : inner ℝ (P t e) (P t x) = inner ℝ (P t e) x := by
      have h := (hsa t (P t e) x).symm
      rwa [hPP t e] at h
    have h1 : P t (Q t x) = Q t x := by
      rw [hQform t x]
      simp only [map_sub, map_smul, hPP t x, hPP t e]
    have h2 : inner ℝ (P t e) (Q t x) = 0 := by
      rw [hQform t x, inner_sub_right, real_inner_smul_right, h3, real_inner_self_eq_norm_sq,
        div_mul_cancel₀ _ (hne_norm t), sub_self]
    rw [hQform t (Q t x), h1, h2, zero_div, zero_smul, sub_zero]
  have hQe : ∀ t, Q t e = 0 := by
    intro t
    rw [hQform t e, hse t, div_self (hne_norm t), one_smul, sub_self]
  -- `Q t` kills `e` as well, so it preserves `eᗮ` (indeed `Q t u ⊥ e` for *every* `u`).
  have hpres : ∀ t (u : EuclideanSpace ℝ (Fin N)), inner ℝ u e = 0 → inner ℝ (Q t u) e = 0 := by
    intro t u _
    have h1 : inner ℝ (P t u) e = inner ℝ (P t e) u :=
      (hsa t u e).trans (real_inner_comm _ _)
    rw [hQform t u, inner_sub_left, real_inner_smul_left, h1, hse t,
      div_mul_cancel₀ _ (hne_norm t), sub_self]
  refine ⟨Q, ?_, ?_, ?_, ?_, hpres, hQform, ?_⟩
  · -- Joint smoothness: unfold `Q` into its explicit formula.
    have hWe : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => P p.1 e) := by fun_prop
    have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => ‖P p.1 e‖ ^ 2) := by
      have h := ContDiff.inner ℝ hWe hWe
      simpa only [real_inner_self_eq_norm_sq] using h
    have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => inner ℝ (P p.1 e) p.2) := by
      have h := ContDiff.inner ℝ hWe contDiff_snd
      simpa only [Prod.fst, Prod.snd] using h
    have hne : ∀ p : ℝ × EuclideanSpace ℝ (Fin N), ‖P p.1 e‖ ^ 2 ≠ 0 := fun p =>
      pow_ne_zero 2 (norm_ne_zero_iff.mpr (hPe p.1))
    have hfun : (fun p : ℝ × EuclideanSpace ℝ (Fin N) => Q p.1 p.2) =
        fun p : ℝ × EuclideanSpace ℝ (Fin N) =>
          P p.1 p.2 - (inner ℝ (P p.1 e) p.2 / ‖P p.1 e‖ ^ 2) • P p.1 e := by
      funext p; exact hQform p.1 p.2
    rw [hfun]
    exact hPsm.sub ((hA.div hN hne).smul hWe)
  · -- Idempotence.
    intro t
    apply ContinuousLinearMap.ext
    intro x
    show Q t (Q t x) = Q t x
    exact hQidem_pt t x
  · -- The rank drops by exactly one: `range (P t) = range (Q t) ⊔ span {P t e}`.
    intro t
    have hVmem : ∀ v, v ∈ LinearMap.range (P t).toLinearMap → P t v = v := by
      rintro v ⟨u, rfl⟩
      exact hPP t u
    have hUfix : ∀ z, z ∈ LinearMap.range (Q t).toLinearMap → Q t z = z := by
      rintro z ⟨y, rfl⟩
      exact hQidem_pt t y
    have hPeV : P t e ∈ LinearMap.range (P t).toLinearMap := ⟨P t e, hPP t e⟩
    have hUV : LinearMap.range (Q t).toLinearMap ≤ LinearMap.range (P t).toLinearMap := by
      rintro z ⟨y, rfl⟩
      change Q t y ∈ LinearMap.range (P t).toLinearMap
      rw [hQform t y]
      exact Submodule.sub_mem _ (LinearMap.mem_range_self (P t).toLinearMap y)
        (Submodule.smul_mem _ _ hPeV)
    have hVU : LinearMap.range (P t).toLinearMap ≤
        LinearMap.range (Q t).toLinearMap ⊔ Submodule.span ℝ {P t e} := by
      intro v hv
      have hpv : P t v = v := hVmem v hv
      have hdec : v = Q t v + (inner ℝ (P t e) v / ‖P t e‖ ^ 2) • P t e := by
        rw [hQform t v, hpv]
        abel
      rw [hdec]
      exact Submodule.add_mem_sup (LinearMap.mem_range_self (Q t).toLinearMap v)
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)))
    have hspanV : Submodule.span ℝ {P t e} ≤ LinearMap.range (P t).toLinearMap := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact hPeV
    have hVe : LinearMap.range (P t).toLinearMap =
        LinearMap.range (Q t).toLinearMap ⊔ Submodule.span ℝ {P t e} :=
      le_antisymm hVU (sup_le hUV hspanV)
    have hnotmem : P t e ∉ LinearMap.range (Q t).toLinearMap := by
      intro hmem
      have hfix : Q t (P t e) = P t e := hUfix _ hmem
      have hzero : Q t (P t e) = 0 := by
        rw [hQform t (P t e), hPP t e, real_inner_self_eq_norm_sq, div_self (hne_norm t),
          one_smul, sub_self]
      exact hPe t (hfix.symm.trans hzero)
    have hfr : k = Module.finrank ℝ ↥(LinearMap.range (Q t).toLinearMap) + 1 := by
      have h := Submodule.finrank_sup_span_singleton (K := ℝ)
        (V := EuclideanSpace ℝ (Fin N)) (p := LinearMap.range (Q t).toLinearMap)
        (v := P t e) hnotmem
      rw [← hVe] at h
      rw [hrank t] at h
      exact h
    omega
  · intro t
    exact hQe t
  · -- Elements of `range (P t)` orthogonal to `P t e` are fixed.
    intro t v hv hperp
    have h1 : inner ℝ (P t e) v = 0 := (real_inner_comm v (P t e)).trans hperp
    rw [hQform t v, hv, h1, zero_div, zero_smul, sub_zero]

end Work.Drive.Push
