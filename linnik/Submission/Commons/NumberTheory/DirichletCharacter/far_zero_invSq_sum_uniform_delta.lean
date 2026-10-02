import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_rightHalf_avg_core
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.Linnik.completedL_ballZeroCount
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity

open Complex DirichletCharacter Metric MeromorphicOn Function
open scoped Real BigOperators

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Commons.NumberTheory.DirichletCharacter

/-- Elementary arithmetic: if `0 < δ ≤ 1` and `x ≥ 0` with `δ²/2 < x`, then
`1 + x ≤ (3/δ²) x`. -/
private lemma one_add_le_three_div_sq_mul {δ x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hx0 : 0 ≤ x) (hx : δ ^ 2 / 2 < x) : 1 + x ≤ (3 / δ ^ 2) * x := by
  have hδ2pos : 0 < δ ^ 2 := pow_pos hδ 2
  have hδ2le : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hlt : (1 : ℝ) < 2 * x / δ ^ 2 := by
    rw [lt_div_iff₀ hδ2pos]
    linarith only [hx]
  have hle : x ≤ x / δ ^ 2 := by
    rw [le_div_iff₀ hδ2pos]
    nlinarith only [hx0, hδ2le]
  have h1 : 1 + x < 2 * x / δ ^ 2 + x / δ ^ 2 := by linarith only [hlt, hle]
  have h2 : 2 * x / δ ^ 2 + x / δ ^ 2 = 3 * x / δ ^ 2 := by ring
  have heq : (3 / δ ^ 2) * x = 3 * x / δ ^ 2 := by ring
  linarith only [hlt, hle, h2, heq]

/-- **Uniform-in-`δ` far-zero inverse-square sum bound.**

For a non-trivial primitive Dirichlet character `χ mod N` and every `s` with `Re s ≥ 1`,
the divisor-weighted zero sum of `Λ = completedLFunction χ`,
`Σ_u (divisor Λ univ u) · 1/‖s-u‖²`, restricted to zeros `u` at distance `> δ` from the
point `1 + i·Im s`, is summable and bounded by `(c/δ²)·(log N + log(2+‖s‖) + 2)`, with an
absolute constant `c`, uniformly in `χ`, `N`, `s` and `δ ∈ (0,1]`. -/
theorem far_zero_invSq_sum_uniform_delta :
    ∃ c : ℝ, 0 < c ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hχprim : χ.IsPrimitive), ∀ ⦃s : ℂ⦄, 1 ≤ s.re → ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
      Summable (fun u : ℂ =>
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℝ) *
          (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ > δ then (1 / ‖s - u‖ ^ 2) else 0)) ∧
      (∑' u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℝ) *
          (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ > δ then (1 / ‖s - u‖ ^ 2) else 0))
        ≤ (c / δ ^ 2) * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := by
  refine ⟨30, by norm_num, ?_⟩
  intro N _inst χ hχ hχprim s hs δ hδ hδ1
  classical
  set Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ with hΛdef
  set T : ℝ := s.im with hTdef
  set P : ℂ := (1 : ℂ) + (s.im : ℂ) * Complex.I with hPdef
  have hΛdiff : Differentiable ℂ Λ := by
    have h := DirichletCharacter.differentiable_completedLFunction hχ
    simpa [hΛdef] using h
  have hΛan : ∀ U : Set ℂ, AnalyticOnNhd ℂ Λ U := fun U z _ => hΛdiff.analyticAt z
  have huniv : ∀ u : ℂ, MeromorphicOn.divisor Λ Set.univ u = (analyticOrderNatAt Λ u : ℤ) :=
    fun u => Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (hΛan Set.univ) (Set.mem_univ u)
  have hball : ∀ (R : ℝ) (u : ℂ), u ∈ Metric.closedBall (0 : ℂ) R →
      MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u = (analyticOrderNatAt Λ u : ℤ) :=
    fun R u hu => Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (hΛan _) hu
  have hΛzero : ∀ (R : ℝ) (u : ℂ),
      MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u ≠ 0 → Λ u = 0 := by
    intro R u hd
    have huB : u ∈ Metric.closedBall (0 : ℂ) R := by
      by_contra h
      have h0 : MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) R) u = 0 := by
        rw [MeromorphicOn.divisor_def, if_neg]
        exact fun hc => h hc.2
      exact hd h0
    have hcast : (analyticOrderNatAt Λ u : ℤ) ≠ 0 := by rw [← hball R u huB]; exact hd
    have haux : analyticOrderNatAt Λ u ≠ 0 := fun h0 => hcast (by simp [h0])
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero haux
  have hstrip : ∀ (R : ℝ) (u : ℂ),
      MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u ≠ 0 → 0 < u.re ∧ u.re < 1 :=
    fun R u hd => Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hχprim (by simpa [hΛdef] using hΛzero R u hd)
  have hDnn_univ : ∀ x : ℂ, (0 : ℝ) ≤ ((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ) := by
    intro x
    rw [huniv x]; positivity
  have hDnn : ∀ (ρ : ℝ) (x : ℂ),
      (0 : ℝ) ≤ ((MeromorphicOn.divisor Λ (Metric.closedBall 0 ρ) x : ℤ) : ℝ) := by
    intro ρ x
    by_cases hx : x ∈ Metric.closedBall (0 : ℂ) ρ
    · exact_mod_cast (AnalyticOnNhd.divisor_nonneg (hΛan (Metric.closedBall (0:ℂ) ρ))) x
    · have h0 : MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) ρ) x = 0 := by
        rw [MeromorphicOn.divisor_def, if_neg]
        exact fun hc => hx hc.2
      rw [h0]; simp
  set K : ℂ → ℝ := fun u => (2 - u.re) / ((2 - u.re) ^ 2 + (T - u.im) ^ 2)
      + (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2) with hKdef
  have hsqn : ∀ u : ℂ, ‖s - u‖ ^ 2 = (s.re - u.re) ^ 2 + (s.im - u.im) ^ 2 := by
    intro u
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre : (s - u).re = s.re - u.re := by simp
    have him : (s - u).im = s.im - u.im := by simp
    rw [hre, him]; ring
  have hsqn' : ∀ u : ℂ, ‖P - u‖ ^ 2 = (1 - u.re) ^ 2 + (s.im - u.im) ^ 2 := by
    intro u
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre : (P - u).re = 1 - u.re := by simp [hPdef]
    have him : (P - u).im = s.im - u.im := by simp [hPdef]
    rw [hre, him]; ring
  have hKge : ∀ u : ℂ, 0 < u.re → u.re < 1 → 1 / (1 + (T - u.im) ^ 2) ≤ K u := by
    intro u h1 h2
    have ha : (1 : ℝ) < 2 - u.re := by linarith only [h2]
    have ha2 : (2 : ℝ) - u.re < 2 := by linarith only [h1]
    have hb : (1 : ℝ) < 1 + u.re := by linarith only [h1]
    have hb2 : (1 : ℝ) + u.re < 2 := by linarith only [h2]
    have h1' : (1 / 2) / (1 + (T - u.im) ^ 2) ≤ (2 - u.re) / ((2 - u.re) ^ 2 + (T - u.im) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [sq_nonneg (T - u.im), ha, ha2, h1, h2]
    have h2' : (1 / 2) / (1 + (T - u.im) ^ 2) ≤ (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [sq_nonneg (T - u.im), hb, hb2, h2, h1]
    have hsum : (1 / 2) / (1 + (T - u.im) ^ 2) + (1 / 2) / (1 + (T - u.im) ^ 2)
        = 1 / (1 + (T - u.im) ^ 2) := by field_simp; ring
    rw [hKdef]
    linarith only [h1', h2', hsum.le, hsum.ge, hsum]
  have hKnn : ∀ u : ℂ, 0 < u.re → u.re < 1 → 0 ≤ K u := by
    intro u h1 h2
    have h := hKge u h1 h2
    have h2' : 0 < 1 / (1 + (T - u.im) ^ 2) := by positivity
    linarith only [h, h2']
  have hwcmp : ∀ u : ℂ, 0 < u.re → u.re < 1 →
      (if ‖P - u‖ > δ then (1 / ‖s - u‖ ^ 2) else 0) ≤ (3 / δ ^ 2) * K u := by
    intro u h1 h2
    have hδ2pos : 0 < δ ^ 2 := pow_pos hδ 2
    by_cases hc : ‖P - u‖ > δ
    · rw [if_pos hc]
      set M : ℝ := max ((1 - u.re) ^ 2) ((T - u.im) ^ 2) with hMdef
      have hMpos : 0 < M := lt_of_lt_of_le (pow_pos (by linarith only [h2] : (0:ℝ) < 1 - u.re) 2)
        (le_max_left _ _)
      have hP2 : ‖P - u‖ ^ 2 = (1 - u.re) ^ 2 + (T - u.im) ^ 2 := by
        rw [hsqn' u, ← hTdef]
      have hsum_gt : δ ^ 2 < (1 - u.re) ^ 2 + (T - u.im) ^ 2 := by
        rw [← hP2]; nlinarith only [hc, hδ]
      have h2M : δ ^ 2 / 2 < M := by
        have hle : (1 - u.re) ^ 2 + (T - u.im) ^ 2 ≤ 2 * M := by
          rw [hMdef]
          have ha := le_max_left ((1 - u.re) ^ 2) ((T - u.im) ^ 2)
          have hb := le_max_right ((1 - u.re) ^ 2) ((T - u.im) ^ 2)
          linarith only [ha, hb]
        linarith only [hsum_gt, hle]
      have hkey := one_add_le_three_div_sq_mul hδ hδ1 hMpos.le h2M
      have hy2le : (T - u.im) ^ 2 ≤ M := le_max_right _ _
      have hkey2 : 1 + (T - u.im) ^ 2 ≤ (3 / δ ^ 2) * M := by linarith only [hkey, hy2le]
      have hy2pos : 0 < 1 + (T - u.im) ^ 2 := by positivity
      have h2' : 1 / M ≤ (3 / δ ^ 2) / (1 + (T - u.im) ^ 2) := by
        rw [div_le_div_iff₀ hMpos hy2pos]
        simpa using hkey2
      have hsqle : M ≤ ‖s - u‖ ^ 2 := by
        rw [hMdef]
        rw [hsqn u]
        apply max_le
        · have h1u : (0:ℝ) ≤ 1 - u.re := by linarith only [h2]
          have hd : (0:ℝ) ≤ (s.re - u.re) - (1 - u.re) := by linarith only [hs]
          nlinarith only [sq_nonneg ((s.re - u.re) - (1 - u.re)), sq_nonneg (s.im - u.im), h1u, hd, hs, h2]
        · rw [← hTdef]
          linarith only [sq_nonneg (s.re - u.re)]
      have h3 : 1 / ‖s - u‖ ^ 2 ≤ 1 / M := one_div_le_one_div_of_le hMpos hsqle
      have h4 : (3 / δ ^ 2) / (1 + (T - u.im) ^ 2) ≤ (3 / δ ^ 2) * K u := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hKge u h1 h2) (by positivity)
      linarith only [h2', h3, h4]
    · rw [if_neg hc]
      exact mul_nonneg (by positivity) (hKnn u h1 h2)
  have hfinsum : ∀ z : Finset ℂ,
      ∑ x ∈ z, ((((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ)) *
          (if ‖P - x‖ > δ then (1 / ‖s - x‖ ^ 2) else 0))
        ≤ (30 / δ ^ 2) * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := by
    intro z
    have hfac : (0 : ℝ) ≤ 3 / δ ^ 2 := by positivity
    set z' : Finset ℂ := z.filter (fun x => MeromorphicOn.divisor Λ Set.univ x ≠ 0) with hz'def
    have hsum_eq : ∑ x ∈ z, ((((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ)) *
          (if ‖P - x‖ > δ then (1 / ‖s - x‖ ^ 2) else 0))
        = ∑ x ∈ z', ((((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ)) *
          (if ‖P - x‖ > δ then (1 / ‖s - x‖ ^ 2) else 0)) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro x hx hxn
      have h0 : MeromorphicOn.divisor Λ Set.univ x = 0 := by
        by_contra hne; exact hxn (Finset.mem_filter.mpr ⟨hx, hne⟩)
      rw [h0]; simp
    rw [hsum_eq]
    by_cases hz'empty : z'.Nonempty
    · set R : ℝ := 2 + ∑ u ∈ z', ‖u‖ with hRdef
      have hdn : ∀ u ∈ z',
          MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u = MeromorphicOn.divisor Λ Set.univ u := by
        intro u hu
        have huR : ‖u‖ ≤ R := by
          simp only [hRdef]
          have h1 : ‖u‖ ≤ ∑ v ∈ z', ‖v‖ :=
            Finset.single_le_sum (fun v _ => norm_nonneg v) hu
          linarith only [h1]
        have huB : u ∈ Metric.closedBall (0 : ℂ) R := by
          rw [Metric.mem_closedBall, dist_zero_right]; exact huR
        rw [huniv u, hball R u huB]
      have hstripz : ∀ u ∈ z', 0 < u.re ∧ u.re < 1 := by
        intro u hu
        have hne : MeromorphicOn.divisor Λ Set.univ u ≠ 0 := (Finset.mem_filter.mp hu).2
        refine hstrip R u ?_
        rw [hdn u hu]; exact hne
      have hposD : ∀ u ∈ z', 0 < ((MeromorphicOn.divisor Λ Set.univ u : ℤ) : ℝ) := by
        intro u hu
        have hne : ((MeromorphicOn.divisor Λ Set.univ u : ℤ) : ℝ) ≠ 0 := by
          intro h0
          have hz : MeromorphicOn.divisor Λ Set.univ u = 0 := by
            have : ((MeromorphicOn.divisor Λ Set.univ u : ℤ) : ℝ) = ((0 : ℤ) : ℝ) := by simpa using h0
            exact_mod_cast this
          exact (Finset.mem_filter.mp hu).2 hz
        rcases lt_or_eq_of_le (hDnn_univ u) with h | h
        · exact h
        · exact absurd h.symm hne
      have hpt : ∀ x ∈ z',
          ((((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ)) *
              (if ‖P - x‖ > δ then (1 / ‖s - x‖ ^ 2) else 0))
            ≤ (3 / δ ^ 2) * ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) x : ℤ) : ℝ)) * K x) := by
        intro x hx
        have hst := hstripz x hx
        have hw := hwcmp x hst.1 hst.2
        have hDx := hposD x hx
        rw [hdn x hx]
        nlinarith only [hw, hDx]
      have hsum_le : ∑ x ∈ z', ((((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ)) *
              (if ‖P - x‖ > δ then (1 / ‖s - x‖ ^ 2) else 0))
          ≤ (3 / δ ^ 2) * ∑ x ∈ z', ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) x : ℤ) : ℝ)) * K x) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hpt
      have hSfin : (Function.support (fun u : ℂ =>
          (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ)))).Finite := by
        rw [hΛdef]
        exact Commons.NumberTheory.Linnik.divisor_real_finiteSupport (N := N) χ hχ (0 : ℂ) R
      have hSmem : ∀ u : ℂ, u ∈ hSfin.toFinset ↔
          (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ)) ≠ 0 := by
        intro u
        simp [Set.Finite.mem_toFinset, Function.mem_support]
      have hKnn' : ∀ u : ℂ, 0 ≤ ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ)) * K u) := by
        intro u
        by_cases hd : ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ))) = 0
        · rw [hd]; simp
        · have hd' : MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u ≠ 0 := by
            intro h0; exact hd (by simp [h0])
          have hst := hstrip R u hd'
          exact mul_nonneg (hDnn R u) (hKnn u hst.1 hst.2)
      have hz'sub : z' ⊆ hSfin.toFinset := by
        intro u hu
        rw [hSmem u, hdn u hu]
        exact ne_of_gt (hposD u hu)
      have hfsum : (∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ)) * K u))
          = ∑ u ∈ hSfin.toFinset, ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ)) * K u) := by
        refine finsum_eq_sum_of_support_subset _ ?_
        intro u hu
        rw [Finset.mem_coe, hSmem u]
        rw [Function.mem_support] at hu
        exact fun h0 => hu (by simp [h0])
      have hstep : ∑ x ∈ z', ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) x : ℤ) : ℝ)) * K x)
          ≤ ∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ)) * K u) := by
        rw [hfsum]
        exact Finset.sum_le_sum_of_subset_of_nonneg hz'sub (fun x _ _ => hKnn' x)
      have hbase : (∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ)) * K u))
          ≤ Real.log (N : ℝ) + Real.log (2 + |T|) + 10 := by
        have h := Commons.NumberTheory.DirichletCharacter.finsum_divisor_re_sub_inv_le χ hχ hχprim T R
        simpa [hKdef, hΛdef] using h
      have hlogT : Real.log (2 + |T|) ≤ Real.log (2 + ‖s‖) := by
        apply Real.log_le_log (by positivity)
        have := Complex.abs_im_le_norm s
        simp only [hTdef]
        linarith only [this]
      have hlogN0 : 0 ≤ Real.log (N : ℝ) := by
        apply Real.log_nonneg
        exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
      have hlog2 : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith only [norm_nonneg s])
      have hfinal : (3 / δ ^ 2) * (Real.log (N : ℝ) + Real.log (2 + |T|) + 10)
          ≤ (30 / δ ^ 2) * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := by
        have h10 : Real.log (N : ℝ) + Real.log (2 + |T|) + 10
            ≤ 10 * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := by
          linarith only [hlogT, hlogN0, hlog2]
        calc (3 / δ ^ 2) * (Real.log (N : ℝ) + Real.log (2 + |T|) + 10)
            ≤ (3 / δ ^ 2) * (10 * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2)) :=
              mul_le_mul_of_nonneg_left h10 hfac
          _ = (30 / δ ^ 2) * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := by ring
      calc ∑ x ∈ z', ((((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ)) *
              (if ‖P - x‖ > δ then (1 / ‖s - x‖ ^ 2) else 0))
          ≤ (3 / δ ^ 2) * ∑ x ∈ z', ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) x : ℤ) : ℝ)) * K x) := hsum_le
        _ ≤ (3 / δ ^ 2) * ∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ)) * K u) := by
              exact mul_le_mul_of_nonneg_left hstep hfac
        _ ≤ (3 / δ ^ 2) * (Real.log (N : ℝ) + Real.log (2 + |T|) + 10) := by
              exact mul_le_mul_of_nonneg_left hbase hfac
        _ ≤ (30 / δ ^ 2) * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := hfinal
    · have hz0 : z' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hz'empty
      rw [hz0]
      simp only [Finset.sum_empty]
      have hpos : 0 < (30 / δ ^ 2) * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := by
        have h1 : 0 ≤ Real.log (N : ℝ) := by
          apply Real.log_nonneg
          exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
        have h2 : 0 < Real.log (2 + ‖s‖) := Real.log_pos (by linarith only [norm_nonneg s])
        have h3 : (0 : ℝ) < 30 / δ ^ 2 := div_pos (by norm_num) (pow_pos hδ 2)
        exact mul_pos h3 (by linarith only [h1, h2])
      exact hpos.le
  have hnn : ∀ x : ℂ, 0 ≤ ((((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ)) *
      (if ‖P - x‖ > δ then (1 / ‖s - x‖ ^ 2) else 0)) :=
    fun x => mul_nonneg (hDnn_univ x) (by split <;> positivity)
  exact ⟨summable_of_sum_le hnn hfinsum, Real.tsum_le_of_sum_le hnn hfinsum⟩

end Commons.NumberTheory.DirichletCharacter
