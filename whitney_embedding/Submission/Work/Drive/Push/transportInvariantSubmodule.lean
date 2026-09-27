import Mathlib
import Submission.Work.Whitney.CutPush.transport_of_plane_family

namespace Work.Drive.Push

open scoped ContDiff
open Work.Whitney.CutPush
open Set

set_option maxHeartbeats 8000000

/-- **Transport of a smooth plane family to a fixed plane, with an invariant submodule clause.**
This is `Work.Whitney.CutPush.exists_transport_of_plane_family_joint` with one extra input: a
submodule `K` preserved by every `pr t`.  The conclusion carries two extra clauses, that `Λ t` and
`Λinv t` map `K` into itself.  The construction is the same "marching product" of the small steps
`1 - pr (ℓ (k+1) τ) + pr (ℓ k τ)`; each factor preserves `K`, so every partial product does.  The
clause for `Λinv` follows because `Λ t` is injective, so the image of the finite-dimensional `K` has
the same dimension as `K`. -/
theorem transportInvariantSubmodule {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {k : ℕ}
    (pr : ℝ → E →L[ℝ] E)
    (hpr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => pr p.1 p.2))
    (hidem : ∀ t, pr t * pr t = pr t)
    (hrank : ∀ t : ℝ, Module.finrank ℝ (LinearMap.range (pr t : E →ₗ[ℝ] E)) = k)
    (K : Submodule ℝ E) (hK : ∀ t : ℝ, ∀ y : E, y ∈ K → pr t y ∈ K) :
    ∃ (Λ Λinv : ℝ → E →L[ℝ] E),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => Λ p.1 p.2) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => Λinv p.1 p.2) ∧
      (∀ t y, Λinv t (Λ t y) = y) ∧ (∀ t y, Λ t (Λinv t y) = y) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        LinearMap.range ((Λ t).toLinearMap.comp (pr t).toLinearMap)
          = LinearMap.range (pr 0).toLinearMap) ∧
      (∀ t : ℝ, ∀ y : E, y ∈ K → Λ t y ∈ K) ∧
      (∀ t : ℝ, ∀ y : E, y ∈ K → Λinv t y ∈ K) := by
  classical
  -- ## step 1: a uniform scale on which `pr` moves by less than `1`
  obtain ⟨δ1, hδ1pos, hδ1⟩ :=
    exists_close_of_close_param pr hpr.continuous (by norm_num : (0 : ℝ) < 1)
  -- ## step 2: a number of steps
  obtain ⟨N, hNpos, hN⟩ : ∃ N : ℕ, (0 : ℝ) < (N : ℝ) ∧ 2 / (N : ℝ) < δ1 := by
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / δ1)
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 / δ1) hn.le
    refine ⟨n, hn0, ?_⟩
    rw [div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hδ1pos] at hn
    linarith
  -- ## step 3: the bounded smooth reparametrisation
  obtain ⟨ψ, hψsm, hψid, hψbd⟩ : ∃ ψ : ℝ → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ (∀ τ : ℝ, |τ| ≤ 1 → ψ τ = τ) ∧
      (∀ τ : ℝ, |ψ τ| ≤ 2) := by
    refine ⟨fun τ => τ * Real.smoothTransition (2 - τ ^ 2), ?_, ?_, ?_⟩
    · fun_prop
    · intro τ hτ
      have hτ2 : τ ^ 2 ≤ 1 := by
        have h := abs_le.mp hτ
        nlinarith [h.1, h.2, sq_nonneg τ, sq_abs τ]
      have h : 1 ≤ 2 - τ ^ 2 := by linarith
      show τ * Real.smoothTransition (2 - τ ^ 2) = τ
      rw [Real.smoothTransition.one_of_one_le h, mul_one]
    · intro τ
      rw [abs_mul]
      by_cases h : |τ| ≤ 2
      · have h2 : |Real.smoothTransition (2 - τ ^ 2)| ≤ 1 := by
          rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
          exact Real.smoothTransition.le_one _
        calc |τ| * |Real.smoothTransition (2 - τ ^ 2)| ≤ 2 * 1 :=
              mul_le_mul h h2 (abs_nonneg _) (by norm_num)
          _ = 2 := by norm_num
      · have h0 : Real.smoothTransition (2 - τ ^ 2) = 0 := by
          apply Real.smoothTransition.zero_of_nonpos
          have h2 : τ ^ 2 > 4 := by nlinarith [sq_abs τ]
          linarith
        rw [h0, abs_zero, mul_zero]
        norm_num
  -- ## step 4: the levels
  let ℓ : ℕ → ℝ → ℝ := fun j τ => ψ τ * (j : ℝ) / (N : ℝ)
  have hℓ_succ : ∀ j τ, ℓ (j + 1) τ = ψ τ * ((j + 1 : ℕ) : ℝ) / (N : ℝ) := fun j τ => rfl
  -- ## step 5: the step-size bound, the levels lie in `[-2,2]`, and small steps
  have hfac_step : ∀ j : ℕ, ∀ τ : ℝ, |ℓ (j + 1) τ - ℓ j τ| ≤ 2 / (N : ℝ) := by
    intro j τ
    have h1 : ψ τ * ((j + 1 : ℕ) : ℝ) / (N : ℝ) - ψ τ * (j : ℝ) / (N : ℝ)
        = ψ τ / (N : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]; ring
    change |ψ τ * ((j + 1 : ℕ) : ℝ) / (N : ℝ) - ψ τ * (j : ℝ) / (N : ℝ)| ≤ 2 / (N : ℝ)
    rw [h1, abs_div, abs_of_pos hNpos, div_le_div_iff_of_pos_right hNpos]
    exact hψbd τ
  have hlev_abs : ∀ j : ℕ, j ≤ N → ∀ τ : ℝ, |ℓ j τ| ≤ 2 := by
    intro j hj τ
    have hjN0 : (0 : ℝ) ≤ (j : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg j) hNpos.le
    have hjN : (j : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_one hNpos]
      exact_mod_cast hj
    have habs : |ℓ j τ| = |ψ τ| * ((j : ℝ) / (N : ℝ)) := by
      change |ψ τ * (j : ℝ) / (N : ℝ)| = |ψ τ| * ((j : ℝ) / (N : ℝ))
      rw [abs_div, abs_mul, abs_of_pos hNpos,
        show |(j : ℝ)| = (j : ℝ) from abs_of_nonneg (Nat.cast_nonneg j)]
      ring
    rw [habs]
    calc |ψ τ| * ((j : ℝ) / (N : ℝ)) ≤ 2 * 1 :=
          mul_le_mul (hψbd τ) hjN hjN0 (by norm_num)
      _ = 2 := by norm_num
  have hlev_mem : ∀ j : ℕ, j ≤ N → ∀ τ : ℝ, ℓ j τ ∈ Icc (-2 : ℝ) 2 := by
    intro j hj τ
    exact ⟨by nlinarith [hlev_abs j hj τ, neg_abs_le (ℓ j τ)],
      by nlinarith [hlev_abs j hj τ, le_abs_self (ℓ j τ)]⟩
  have hsmall : ∀ (a b : ℝ), a ∈ Icc (-2 : ℝ) 2 → b ∈ Icc (-2 : ℝ) 2 → |a - b| < δ1 →
      ‖pr a - pr b‖ < 1 := fun a b ha hb h => hδ1 a ha b hb h
  have hstep_close : ∀ k : ℕ, k < N → ∀ τ : ℝ,
      ‖pr (ℓ (k + 1) τ) - pr (ℓ k τ)‖ < 1 := by
    intro k hk τ
    have hk1 : k + 1 ≤ N := by omega
    refine hsmall (ℓ (k + 1) τ) (ℓ k τ)
      (hlev_mem (k + 1) hk1 τ) (hlev_mem k (by omega) τ) ?_
    have h1 : ℓ (k + 1) τ - ℓ k τ = ψ τ / (N : ℝ) := by
      change ψ τ * ((k + 1 : ℕ) : ℝ) / (N : ℝ) - ψ τ * (k : ℝ) / (N : ℝ) = ψ τ / (N : ℝ)
      rw [Nat.cast_add, Nat.cast_one]
      ring
    rw [h1, abs_div, abs_of_pos hNpos]
    have h2 : |ψ τ| / (N : ℝ) ≤ 2 / (N : ℝ) := by
      rw [div_le_div_iff_of_pos_right hNpos]
      exact hψbd τ
    linarith
  have hfac_inj : ∀ k : ℕ, k < N → ∀ τ : ℝ,
      Function.Injective ((1 - pr (ℓ (k + 1) τ) + pr (ℓ k τ) : E →L[ℝ] E)) := by
    intro k hk τ
    have h := hstep_close k hk τ
    have h' : ‖pr (ℓ k τ) - pr (ℓ (k + 1) τ)‖ < 1 := by rw [norm_sub_rev]; exact h
    exact small_step_injective h'
  have hfac_range : ∀ k : ℕ, k < N → ∀ τ : ℝ, ∀ y : E,
      y ∈ LinearMap.range (pr (ℓ (k + 1) τ) : E →ₗ[ℝ] E) →
      ((1 - pr (ℓ (k + 1) τ) + pr (ℓ k τ) : E →L[ℝ] E)) y
        ∈ LinearMap.range (pr (ℓ k τ) : E →ₗ[ℝ] E) := by
    intro k hk τ y hy
    exact small_step_mem_range (hidem (ℓ (k + 1) τ)) hy
  -- ## step 7: the range induction
  have hF : ∀ (τ : ℝ) (j : ℕ), j < N → ∀ y : E,
      y ∈ LinearMap.range (pr (ℓ (N - j) τ) : E →ₗ[ℝ] E) →
      ((1 - pr (ℓ (N - 1 - j + 1) τ) + pr (ℓ (N - 1 - j) τ) : E →L[ℝ] E)) y
        ∈ LinearMap.range (pr (ℓ (N - (j + 1)) τ) : E →ₗ[ℝ] E) := by
    intro τ j hj y hy
    have hy' : y ∈ LinearMap.range (pr (ℓ ((N - 1 - j) + 1) τ) : E →ₗ[ℝ] E) := by
      rw [show (N - 1 - j) + 1 = N - j from by omega]
      exact hy
    have := hfac_range (N - 1 - j) (by omega) τ y hy'
    simpa [show N - 1 - j = N - (j + 1) from by omega] using this
  have hstep_mem : ∀ (τ : ℝ) (j : ℕ), j ≤ N → ∀ (x : E),
      (marchFac (fun k => (1 - pr (ℓ (N - 1 - k + 1) τ) + pr (ℓ (N - 1 - k) τ)
        : E →L[ℝ] E)) j) ((pr (ℓ N τ)) x) ∈
        LinearMap.range (pr (ℓ (N - j) τ) : E →ₗ[ℝ] E) := by
    intro τ j hj x
    exact marchFac_mem (P := fun k => LinearMap.range (pr (ℓ k τ) : E →ₗ[ℝ] E))
      (fun k hk y hy => hF τ k hk y hy) j hj _ ⟨x, rfl⟩
  have hΛapp : ∀ (τ : ℝ) (x : E),
      (marchFac (fun k => (1 - pr (ℓ (N - 1 - k + 1) τ) + pr (ℓ (N - 1 - k) τ)
        : E →L[ℝ] E)) N) ((pr (ℓ N τ)) x) ∈
        LinearMap.range (pr (ℓ 0 τ) : E →ₗ[ℝ] E) := by
    intro τ x
    simpa using hstep_mem τ N le_rfl x
  -- ## step 8: the two families
  let Fac : ℝ → ℕ → E →L[ℝ] E := fun τ k => 1 - pr (ℓ (N - 1 - k + 1) τ) + pr (ℓ (N - 1 - k) τ)
  let Λ : ℝ → E →L[ℝ] E := fun τ => marchFac (Fac τ) N
  have hFac_sm : ∀ k : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun τ : ℝ => Fac τ k) := by
    intro k
    have h1 : ∀ c : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun τ : ℝ => pr (ψ τ * c / (N : ℝ))) := by
      intro c
      rw [contDiff_clm_apply_iff]
      intro y
      have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun τ : ℝ => (ψ τ * c / (N : ℝ), y)) :=
        (((hψsm.mul contDiff_const).div_const _).prodMk contDiff_const)
      exact hpr.comp h2
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun τ : ℝ => pr (ℓ (N - 1 - k + 1) τ)) :=
      h1 ((N - 1 - k + 1 : ℕ) : ℝ)
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun τ : ℝ => pr (ℓ (N - 1 - k) τ)) :=
      h1 ((N - 1 - k : ℕ) : ℝ)
    exact ((contDiff_const.sub h2).add h3)
  have hΛ_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Λ := by
    have h : ∀ j : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun τ : ℝ => marchFac (Fac τ) j) := by
      intro j
      induction j with
      | zero => simpa using contDiff_const
      | succ i ih =>
          have h1 : (fun τ : ℝ => marchFac (Fac τ) (i + 1))
              = fun τ : ℝ => Fac τ i * marchFac (Fac τ) i := by
            funext τ; rw [marchFac_succ]
          rw [h1]
          exact (hFac_sm i).clm_comp ih
    exact h N
  have hΛ_inj : ∀ τ : ℝ, Function.Injective (Λ τ) := by
    intro τ
    have h : ∀ j : ℕ, j ≤ N → Function.Injective (marchFac (Fac τ) j) := by
      intro j hj
      induction j with
      | zero => simpa using Function.injective_id
      | succ i ih =>
          have hi : i < N := by omega
          have h1 : (marchFac (Fac τ) (i + 1)) = Fac τ i * marchFac (Fac τ) i := marchFac_succ _ _
          rw [h1]
          exact (hfac_inj (N - 1 - i) (by omega) τ).comp (ih (by omega))
    exact h N le_rfl
  have hinv : ∀ τ : ℝ, (Λ τ).IsInvertible := by
    intro τ
    have hbij : Function.Bijective (Λ τ) :=
      ⟨hΛ_inj τ, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (rfl : Module.finrank ℝ E = Module.finrank ℝ E)).mp (hΛ_inj τ)⟩
    refine ⟨(LinearEquiv.ofBijective (Λ τ : E →ₗ[ℝ] E) hbij).toContinuousLinearEquiv, ?_⟩
    ext x
    rfl
  have hΛinv_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun τ : ℝ => ContinuousLinearMap.inverse (Λ τ)) := by
    rw [contDiff_iff_contDiffAt]
    intro τ
    exact (hinv τ).contDiffAt_map_inverse.comp τ hΛ_sm.contDiffAt
  -- ## step 9: `Λ` preserves `K`
  have hKfac : ∀ (τ : ℝ) (k : ℕ), ∀ y : E, y ∈ K → Fac τ k y ∈ K := by
    intro τ k y hy
    show (1 - pr (ℓ (N - 1 - k + 1) τ) + pr (ℓ (N - 1 - k) τ) : E →L[ℝ] E) y ∈ K
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply]
    exact K.add_mem (K.sub_mem hy (hK _ y hy)) (hK _ y hy)
  have hKmarch : ∀ (τ : ℝ) (j : ℕ), ∀ y : E, y ∈ K → (marchFac (Fac τ) j) y ∈ K := by
    intro τ j
    induction j with
    | zero => intro y hy; simpa using hy
    | succ i ih =>
        intro y hy
        rw [marchFac_succ, ContinuousLinearMap.mul_apply]
        exact hKfac τ i _ (ih y hy)
  have hΛK : ∀ (τ : ℝ) (y : E), y ∈ K → Λ τ y ∈ K := by
    intro τ y hy
    exact hKmarch τ N y hy
  -- ## step 10: `Λinv` preserves `K`
  have hKmap_le : ∀ τ : ℝ, Submodule.map (Λ τ).toLinearMap K ≤ K := by
    intro τ y hy
    rw [Submodule.mem_map] at hy
    obtain ⟨x, hxK, rfl⟩ := hy
    exact hΛK τ x hxK
  have hKmap_eq : ∀ τ : ℝ, Submodule.map (Λ τ).toLinearMap K = K := by
    intro τ
    refine Submodule.eq_of_le_of_finrank_eq (hKmap_le τ) ?_
    exact (LinearEquiv.finrank_eq
      (K.equivMapOfInjective (Λ τ).toLinearMap (hΛ_inj τ))).symm
  have hΛinvK : ∀ (τ : ℝ) (y : E), y ∈ K → ContinuousLinearMap.inverse (Λ τ) y ∈ K := by
    intro τ y hy
    have hy' : y ∈ Submodule.map (Λ τ).toLinearMap K := by rw [hKmap_eq τ]; exact hy
    rw [Submodule.mem_map] at hy'
    obtain ⟨x, hxK, hxy⟩ := hy'
    have hinvx : ContinuousLinearMap.inverse (Λ τ) ((Λ τ) x) = x := by
      have h := congrArg (fun g : E →L[ℝ] E => g x) ((hinv τ).inverse_comp_self)
      simpa using h
    rw [← hxy]
    change ContinuousLinearMap.inverse (Λ τ) ((Λ τ) x) ∈ K
    rw [hinvx]
    exact hxK
  let Λinv : ℝ → E →L[ℝ] E := fun τ => ContinuousLinearMap.inverse (Λ τ)
  have hΛinv_sm' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => Λinv p.1 p.2) :=
    (hΛinv_sm.comp contDiff_fst).clm_apply contDiff_snd
  refine ⟨Λ, Λinv, (hΛ_sm.comp contDiff_fst).clm_apply contDiff_snd, hΛinv_sm', ?_, ?_, ?_, ?_, ?_⟩
  · intro τ y
    have h := congrArg (fun g : E →L[ℝ] E => g y) ((hinv τ).inverse_comp_self)
    simpa [Λinv] using h
  · intro τ y
    have h := congrArg (fun g : E →L[ℝ] E => g y) ((hinv τ).self_comp_inverse)
    simpa [Λinv] using h
  · intro τ hτ
    have hτψ : ψ τ = τ := hψid τ (by rw [abs_of_nonneg hτ.1]; exact hτ.2)
    have hℓ0 : ℓ 0 τ = 0 := by
      show ψ τ * ((0 : ℕ) : ℝ) / (N : ℝ) = 0
      simp
    have hℓN : ℓ N τ = τ := by
      show ψ τ * ((N : ℕ) : ℝ) / (N : ℝ) = τ
      rw [mul_div_assoc, div_self (ne_of_gt hNpos), mul_one]
      exact hτψ
    have hincl : LinearMap.range ((Λ τ).toLinearMap.comp (pr τ).toLinearMap)
        ≤ LinearMap.range (pr 0 : E →ₗ[ℝ] E) := by
      rintro y ⟨x, rfl⟩
      have h := hΛapp τ x
      rw [hℓN, hℓ0] at h
      simpa using h
    have hfr : Module.finrank ℝ ↥(LinearMap.range ((Λ τ).toLinearMap.comp (pr τ).toLinearMap))
        = Module.finrank ℝ ↥(LinearMap.range (pr τ : E →ₗ[ℝ] E)) := by
      have h1 : LinearMap.range ((Λ τ).toLinearMap.comp (pr τ).toLinearMap)
          = Submodule.map (Λ τ).toLinearMap (LinearMap.range (pr τ : E →ₗ[ℝ] E)) :=
        LinearMap.range_comp _ _
      rw [h1]
      exact (LinearEquiv.finrank_eq ((LinearMap.range (pr τ : E →ₗ[ℝ] E)).equivMapOfInjective
        (Λ τ).toLinearMap (hΛ_inj τ))).symm
    refine Submodule.eq_of_le_of_finrank_eq hincl ?_
    rw [hfr, hrank τ, ← hrank 0]
  · intro τ y hy
    exact hΛK τ y hy
  · intro τ y hy
    exact hΛinvK τ y hy

end Work.Drive.Push
