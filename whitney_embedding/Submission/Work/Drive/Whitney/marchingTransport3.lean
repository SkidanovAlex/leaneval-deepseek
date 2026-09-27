import Mathlib
import Submission.Work.Whitney.CutPush.transport_of_plane_family

/-!
# Marching transport of a three-parameter family of projections

`Work.Drive.Whitney.marchingTransport3`: let `E` be a finite-dimensional real normed space and
`pr : ℝ → ℝ → ℝ → E →L[ℝ] E` a family of idempotent ("projection") operators of constant rank `k`,
smooth jointly in `(t, a, b, y)`, and *uniformly in `(a, b)`* close for small differences of the
parameter `t` on the window `[-2,2]`:

`∃ δ > 0, ∀ s t ∈ [-2,2], ∀ a b, |s - t| < δ → ‖pr s a b - pr t a b‖ < 1`.

Then there are jointly smooth families `Λ`, `Λinv` of linear isomorphisms of `E`, inverse to each
other pointwise, with `range ((Λ t a b) ∘ (pr t a b)) = range (pr 0 a b)` for `t ∈ [0,1]`.

The proof is the marching argument of `Work.Whitney.CutPush.exists_transport_of_plane_family`
(and of the two-parameter `Work.Drive.Whitney.marchingTransportParam`), with the parameter space
`ℝ` of the latter replaced by an arbitrary normed space `Z`; the target is the instance
`Z = ℝ × ℝ` (`a`,`b` paired), where the only extra ingredient is the smoothness of the
reassociation `((t,a),b) ↦ (t,(a,b))` of the coordinates.

* **small steps** (`Work.Whitney.CutPush.small_step_mem_range`, `…small_step_injective`): two
  projections at distance `< 1` are bridged by the isomorphism `1 - pr' + pr`, which carries
  `range pr'` onto `range pr`;
* **marching** (`Work.Whitney.CutPush.marchFac`, `…marchFac_mem`): with `N` so large that
  `2/N < δ` and a smooth, globally `2`-bounded `ψ` with `ψ = id` on `[-1,1]`, the levels
  `ℓ j t = ψ t * j / N` give factors `1 - pr (ℓ (k+1) t) z + pr (ℓ k t) z` whose consecutive
  projections differ by less than `1`, *simultaneously for all* parameters `z`;
* the result is a smooth family of isomorphisms; the inverse family is Mathlib's
  `ContinuousLinearMap.inverse` of it, smooth by
  `ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse`.
-/

open scoped ContDiff
open Set

namespace Work.Drive.Whitney

set_option maxHeartbeats 8000000

/-- A smooth function `ψ : ℝ → ℝ` with `ψ = id` on `[-1,1]` and `|ψ| ≤ 2` everywhere. -/
theorem exists_smooth_id_bounded :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
      (∀ τ : ℝ, |τ| ≤ 1 → ψ τ = τ) ∧ (∀ τ : ℝ, |ψ τ| ≤ 2) := by
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

/-- Marching transport of a family of projections with an arbitrary normed parameter space `Z`:
the two-parameter statement `Work.Drive.Whitney.marchingTransportParam` with `ℝ` replaced by an
arbitrary normed space.  The proof only uses that the parameter dependence is jointly smooth and
that the closeness hypothesis is uniform in the parameter. -/
theorem marchingTransport_gen {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {k : ℕ}
    (pr : ℝ → Z → E →L[ℝ] E)
    (hpr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : (ℝ × Z) × E => pr p.1.1 p.1.2 p.2))
    (hidem : ∀ t z, pr t z * pr t z = pr t z)
    (hrank : ∀ t z, Module.finrank ℝ (LinearMap.range (pr t z : E →ₗ[ℝ] E)) = k)
    (hclose : ∃ δ > 0, ∀ s ∈ Set.Icc (-2 : ℝ) 2, ∀ t ∈ Set.Icc (-2 : ℝ) 2, ∀ z : Z,
      |s - t| < δ → ‖pr s z - pr t z‖ < 1) :
    ∃ (Λ Λinv : ℝ → Z → E →L[ℝ] E),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : (ℝ × Z) × E => Λ p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : (ℝ × Z) × E => Λinv p.1.1 p.1.2 p.2) ∧
      (∀ t z y, Λinv t z (Λ t z y) = y) ∧ (∀ t z y, Λ t z (Λinv t z y) = y) ∧
      (∀ z : Z, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        LinearMap.range ((Λ t z).toLinearMap.comp (pr t z).toLinearMap)
          = LinearMap.range (pr 0 z : E →ₗ[ℝ] E)) := by
  classical
  obtain ⟨δ1, hδ1pos, hδ1⟩ := hclose
  -- ## step 1: the number of steps
  obtain ⟨N, hNpos, hN⟩ : ∃ N : ℕ, (0 : ℝ) < (N : ℝ) ∧ 2 / (N : ℝ) < δ1 := by
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / δ1)
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 / δ1) hn.le
    refine ⟨n, hn0, ?_⟩
    rw [div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hδ1pos] at hn
    linarith
  -- ## step 2: a smooth, globally `2`-bounded function which is the identity on `[-1,1]`
  obtain ⟨ψ, hψsm, hψid, hψbd⟩ := exists_smooth_id_bounded
  -- ## step 3: the levels
  let ℓ : ℕ → ℝ → ℝ := fun j τ => ψ τ * (j : ℝ) / (N : ℝ)
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
  -- ## step 4: the factors and the marching product
  let Fac : ℝ → Z → ℕ → E →L[ℝ] E :=
    fun τ z k => 1 - pr (ℓ (N - 1 - k + 1) τ) z + pr (ℓ (N - 1 - k) τ) z
  let Λ : ℝ → Z → E →L[ℝ] E := fun τ z => Work.Whitney.CutPush.marchFac (Fac τ z) N
  -- ## step 5: consecutive projections differ by less than `1`
  have hstep_close : ∀ k : ℕ, k < N → ∀ τ : ℝ, ∀ z : Z,
      ‖pr (ℓ (k + 1) τ) z - pr (ℓ k τ) z‖ < 1 := by
    intro k hk τ z
    have hk1 : k + 1 ≤ N := by omega
    refine hδ1 (ℓ (k + 1) τ) (hlev_mem (k + 1) hk1 τ) (ℓ k τ) (hlev_mem k (by omega) τ) z ?_
    have h1 : ℓ (k + 1) τ - ℓ k τ = ψ τ / (N : ℝ) := by
      change ψ τ * ((k + 1 : ℕ) : ℝ) / (N : ℝ) - ψ τ * (k : ℝ) / (N : ℝ) = ψ τ / (N : ℝ)
      rw [Nat.cast_add, Nat.cast_one]
      ring
    rw [h1, abs_div, abs_of_pos hNpos]
    have h2 : |ψ τ| / (N : ℝ) ≤ 2 / (N : ℝ) := by
      rw [div_le_div_iff_of_pos_right hNpos]
      exact hψbd τ
    linarith
  have hfac_inj : ∀ k : ℕ, k < N → ∀ τ : ℝ, ∀ z : Z,
      Function.Injective ((1 - pr (ℓ (k + 1) τ) z + pr (ℓ k τ) z : E →L[ℝ] E)) := by
    intro k hk τ z
    have h' : ‖pr (ℓ k τ) z - pr (ℓ (k + 1) τ) z‖ < 1 := by
      rw [norm_sub_rev]; exact hstep_close k hk τ z
    exact Work.Whitney.CutPush.small_step_injective h'
  have hfac_range : ∀ k : ℕ, k < N → ∀ τ : ℝ, ∀ z : Z, ∀ y : E,
      y ∈ LinearMap.range (pr (ℓ (k + 1) τ) z : E →ₗ[ℝ] E) →
      ((1 - pr (ℓ (k + 1) τ) z + pr (ℓ k τ) z : E →L[ℝ] E)) y
        ∈ LinearMap.range (pr (ℓ k τ) z : E →ₗ[ℝ] E) := by
    intro k hk τ z y hy
    exact Work.Whitney.CutPush.small_step_mem_range (hidem (ℓ (k + 1) τ) z) hy
  -- ## step 6: the range induction
  have hF : ∀ (τ : ℝ) (z : Z) (j : ℕ), j < N → ∀ y : E,
      y ∈ LinearMap.range (pr (ℓ (N - j) τ) z : E →ₗ[ℝ] E) →
      ((1 - pr (ℓ (N - 1 - j + 1) τ) z + pr (ℓ (N - 1 - j) τ) z : E →L[ℝ] E)) y
        ∈ LinearMap.range (pr (ℓ (N - (j + 1)) τ) z : E →ₗ[ℝ] E) := by
    intro τ z j hj y hy
    have hy' : y ∈ LinearMap.range (pr (ℓ ((N - 1 - j) + 1) τ) z : E →ₗ[ℝ] E) := by
      rw [show (N - 1 - j) + 1 = N - j from by omega]
      exact hy
    have h := hfac_range (N - 1 - j) (by omega) τ z y hy'
    simpa [show N - 1 - j = N - (j + 1) from by omega] using h
  have hstep_mem : ∀ (τ : ℝ) (z : Z) (j : ℕ), j ≤ N → ∀ (x : E),
      (Work.Whitney.CutPush.marchFac
        (fun k => (1 - pr (ℓ (N - 1 - k + 1) τ) z + pr (ℓ (N - 1 - k) τ) z : E →L[ℝ] E)) j)
          ((pr (ℓ N τ) z) x) ∈ LinearMap.range (pr (ℓ (N - j) τ) z : E →ₗ[ℝ] E) := by
    intro τ z j hj x
    exact Work.Whitney.CutPush.marchFac_mem
      (P := fun k => LinearMap.range (pr (ℓ k τ) z : E →ₗ[ℝ] E))
      (fun k hk y hy => hF τ z k hk y hy) j hj _ ⟨x, rfl⟩
  have hΛapp : ∀ (τ : ℝ) (z : Z) (x : E),
      (Λ τ z) ((pr (ℓ N τ) z) x) ∈ LinearMap.range (pr (ℓ 0 τ) z : E →ₗ[ℝ] E) := by
    intro τ z x
    simpa using hstep_mem τ z N le_rfl x
  -- ## step 7: smoothness of the factors
  have hFac_sm : ∀ k : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × Z => Fac q.1 q.2 k) := by
    intro k
    have h1 : ∀ c : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × Z => pr (ψ q.1 * c / (N : ℝ)) q.2) := by
      intro c
      rw [contDiff_clm_apply_iff]
      intro y
      have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : ℝ × Z => ((ψ q.1 * c / (N : ℝ), q.2), y)) :=
        ((((hψsm.mul contDiff_const).div_const _).comp
          (contDiff_fst : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × Z => q.1))).prodMk
            contDiff_snd).prodMk contDiff_const
      exact hpr.comp h2
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × Z => pr (ℓ (N - 1 - k + 1) q.1) q.2) :=
      h1 ((N - 1 - k + 1 : ℕ) : ℝ)
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × Z => pr (ℓ (N - 1 - k) q.1) q.2) :=
      h1 ((N - 1 - k : ℕ) : ℝ)
    exact ((contDiff_const.sub h2).add h3)
  have hΛ_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × Z => Λ q.1 q.2) := by
    have h : ∀ j : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × Z => Work.Whitney.CutPush.marchFac (Fac q.1 q.2) j) := by
      intro j
      induction j with
      | zero => simpa using contDiff_const
      | succ i ih =>
          have h1 : (fun q : ℝ × Z => Work.Whitney.CutPush.marchFac (Fac q.1 q.2) (i + 1))
              = fun q : ℝ × Z =>
                  Fac q.1 q.2 i * Work.Whitney.CutPush.marchFac (Fac q.1 q.2) i := by
            funext q; rw [Work.Whitney.CutPush.marchFac_succ]
          rw [h1]
          exact (hFac_sm i).clm_comp ih
    exact h N
  -- ## step 8: the marching product is an isomorphism
  have hΛ_inj : ∀ τ : ℝ, ∀ z : Z, Function.Injective (Λ τ z) := by
    intro τ z
    have h : ∀ j : ℕ, j ≤ N → Function.Injective (Work.Whitney.CutPush.marchFac (Fac τ z) j) := by
      intro j hj
      induction j with
      | zero => simpa using Function.injective_id
      | succ i ih =>
          have hi : i < N := by omega
          have h1 : (Work.Whitney.CutPush.marchFac (Fac τ z) (i + 1))
              = Fac τ z i * Work.Whitney.CutPush.marchFac (Fac τ z) i :=
            Work.Whitney.CutPush.marchFac_succ _ _
          rw [h1]
          exact (hfac_inj (N - 1 - i) (by omega) τ z).comp (ih (by omega))
    exact h N le_rfl
  have hinv : ∀ τ : ℝ, ∀ z : Z, (Λ τ z).IsInvertible := by
    intro τ z
    have hbij : Function.Bijective (Λ τ z) :=
      ⟨hΛ_inj τ z, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (rfl : Module.finrank ℝ E = Module.finrank ℝ E)).mp (hΛ_inj τ z)⟩
    refine ⟨(LinearEquiv.ofBijective (Λ τ z : E →ₗ[ℝ] E) hbij).toContinuousLinearEquiv, ?_⟩
    ext x
    rfl
  have hΛinv_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × Z => ContinuousLinearMap.inverse (Λ q.1 q.2)) := by
    rw [contDiff_iff_contDiffAt]
    intro q
    exact (hinv q.1 q.2).contDiffAt_map_inverse.comp q hΛ_sm.contDiffAt
  -- ## step 9: the five clauses
  refine ⟨Λ, fun τ z => ContinuousLinearMap.inverse (Λ τ z), ?_, ?_, ?_, ?_, ?_⟩
  · exact (hΛ_sm.comp contDiff_fst).clm_apply contDiff_snd
  · exact (hΛinv_sm.comp contDiff_fst).clm_apply contDiff_snd
  · intro t z y
    have h := congrArg (fun g : E →L[ℝ] E => g y) ((hinv t z).inverse_comp_self)
    simpa using h
  · intro t z y
    have h := congrArg (fun g : E →L[ℝ] E => g y) ((hinv t z).self_comp_inverse)
    simpa using h
  · intro z t ht
    have htψ : ψ t = t := hψid t (by rw [abs_of_nonneg ht.1]; exact ht.2)
    have hℓ0 : ℓ 0 t = 0 := by
      show ψ t * ((0 : ℕ) : ℝ) / (N : ℝ) = 0
      simp
    have hℓN : ℓ N t = t := by
      show ψ t * ((N : ℕ) : ℝ) / (N : ℝ) = t
      rw [mul_div_assoc, div_self (ne_of_gt hNpos), mul_one]
      exact htψ
    have hincl : LinearMap.range ((Λ t z).toLinearMap.comp (pr t z).toLinearMap)
        ≤ LinearMap.range (pr 0 z : E →ₗ[ℝ] E) := by
      rintro y ⟨x, rfl⟩
      have h := hΛapp t z x
      rw [hℓN, hℓ0] at h
      simpa using h
    have hfr : Module.finrank ℝ ↥(LinearMap.range ((Λ t z).toLinearMap.comp (pr t z).toLinearMap))
        = Module.finrank ℝ ↥(LinearMap.range (pr t z : E →ₗ[ℝ] E)) := by
      have h1 : LinearMap.range ((Λ t z).toLinearMap.comp (pr t z).toLinearMap)
          = Submodule.map (Λ t z).toLinearMap (LinearMap.range (pr t z : E →ₗ[ℝ] E)) :=
        LinearMap.range_comp _ _
      rw [h1]
      exact (LinearEquiv.finrank_eq ((LinearMap.range (pr t z : E →ₗ[ℝ] E)).equivMapOfInjective
        (Λ t z).toLinearMap (hΛ_inj t z))).symm
    refine Submodule.eq_of_le_of_finrank_eq hincl ?_
    rw [hfr, hrank t z, ← hrank 0 z]

/-- Reassociation of the coordinates `((t,a),b) ↦ (t,(a,b))`, smoothly. -/
theorem contDiff_reassoc_three {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ((ℝ × ℝ) × ℝ) × E => ((p.1.1.1, (p.1.1.2, p.1.2)), p.2)) := by
  exact (((contDiff_fst.fst.fst).prodMk
    ((contDiff_fst.fst.snd).prodMk contDiff_fst.snd)).prodMk contDiff_snd)

/-- Reassociation of the coordinates in the other direction. -/
theorem contDiff_reassoc_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × (ℝ × ℝ)) × E => (((p.1.1, p.1.2.1), p.1.2.2), p.2)) := by
  exact ((((contDiff_fst.fst).prodMk (contDiff_fst.snd.fst)).prodMk
    (contDiff_fst.snd.snd)).prodMk contDiff_snd)

theorem marchingTransport3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {k : ℕ}
    (pr : ℝ → ℝ → ℝ → E →L[ℝ] E)
    (hpr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ((ℝ × ℝ) × ℝ) × E => pr p.1.1.1 p.1.1.2 p.1.2 p.2))
    (hidem : ∀ t a b, pr t a b * pr t a b = pr t a b)
    (hrank : ∀ t a b, Module.finrank ℝ (LinearMap.range (pr t a b : E →ₗ[ℝ] E)) = k)
    (hclose : ∃ δ > 0, ∀ s ∈ Set.Icc (-2 : ℝ) 2, ∀ t ∈ Set.Icc (-2 : ℝ) 2, ∀ a b : ℝ,
      |s - t| < δ → ‖pr s a b - pr t a b‖ < 1) :
    ∃ (Λ Λinv : ℝ → ℝ → ℝ → E →L[ℝ] E),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ((ℝ × ℝ) × ℝ) × E => Λ p.1.1.1 p.1.1.2 p.1.2 p.2) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ((ℝ × ℝ) × ℝ) × E => Λinv p.1.1.1 p.1.1.2 p.1.2 p.2) ∧
      (∀ t a b y, Λinv t a b (Λ t a b y) = y) ∧ (∀ t a b y, Λ t a b (Λinv t a b y) = y) ∧
      (∀ a b : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        LinearMap.range ((Λ t a b).toLinearMap.comp (pr t a b).toLinearMap)
          = LinearMap.range (pr 0 a b : E →ₗ[ℝ] E)) := by
  classical
  obtain ⟨δ, hδpos, hδ⟩ := hclose
  have hprZ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × (ℝ × ℝ)) × E => pr p.1.1 p.1.2.1 p.1.2.2 p.2) :=
    hpr.comp contDiff_reassoc_pair
  obtain ⟨ΛZ, ΛinvZ, hΛZ_sm, hΛinvZ_sm, hcompZ, hcompZ', hrangeZ⟩ :=
    marchingTransport_gen (Z := ℝ × ℝ) (E := E) (k := k)
      (fun t z => pr t z.1 z.2) hprZ
      (fun t z => hidem t z.1 z.2) (fun t z => hrank t z.1 z.2)
      ⟨δ, hδpos, fun s hs t ht z hst => hδ s hs t ht z.1 z.2 hst⟩
  refine ⟨fun t a b => ΛZ t (a, b), fun t a b => ΛinvZ t (a, b), ?_, ?_, ?_, ?_, ?_⟩
  · exact hΛZ_sm.comp contDiff_reassoc_three
  · exact hΛinvZ_sm.comp contDiff_reassoc_three
  · intro t a b y
    exact hcompZ t (a, b) y
  · intro t a b y
    exact hcompZ' t (a, b) y
  · intro a b t ht
    exact hrangeZ (a, b) t ht

end Work.Drive.Whitney
