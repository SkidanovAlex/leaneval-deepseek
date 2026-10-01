import Mathlib
import Submission.Commons.NumberTheory.Linnik.explicitFormula_chi_gen
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_rightHalf_avg
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.Linnik.completedL_ballZeroCount
import Submission.Commons.Analysis.Complex.lapX_sub_inv_bound
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity

open Complex DirichletCharacter Metric MeromorphicOn Function
open scoped Real BigOperators

set_option maxHeartbeats 8000000

namespace Commons.NumberTheory.Linnik

/-- Uniform-in-`χ` far-zero inverse-square sum bound. -/
theorem far_zero_invSq_sum_uniform :
    ∃ c : ℝ, 0 < c ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hχprim : χ.IsPrimitive), ∀ ⦃s : ℂ⦄, 1 ≤ s.re →
      Summable (fun u : ℂ =>
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℝ) *
          (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ > 1/2 then (1 / ‖s - u‖ ^ 2) else 0)) ∧
      (∑' u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℝ) *
          (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ > 1/2 then (1 / ‖s - u‖ ^ 2) else 0))
        ≤ c * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := by
  refine ⟨50, by norm_num, ?_⟩
  intro N _inst χ hχ hχprim s hs
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
    fun R u hd => completedL_zero_strip χ hχ hχprim (by simpa [hΛdef] using hΛzero R u hd)
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
    have ha : (1 : ℝ) < 2 - u.re := by linarith
    have ha2 : (2 : ℝ) - u.re < 2 := by linarith
    have hb : (1 : ℝ) < 1 + u.re := by linarith
    have hb2 : (1 : ℝ) + u.re < 2 := by linarith
    have h1' : (1 / 2) / (1 + (T - u.im) ^ 2) ≤ (2 - u.re) / ((2 - u.re) ^ 2 + (T - u.im) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (T - u.im), ha, ha2]
    have h2' : (1 / 2) / (1 + (T - u.im) ^ 2) ≤ (1 + u.re) / ((1 + u.re) ^ 2 + (T - u.im) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (T - u.im), hb, hb2]
    have hsum : (1 / 2) / (1 + (T - u.im) ^ 2) + (1 / 2) / (1 + (T - u.im) ^ 2)
        = 1 / (1 + (T - u.im) ^ 2) := by field_simp; ring
    rw [hKdef]
    linarith [h1', h2', hsum.le, hsum.ge]
  have hKnn : ∀ u : ℂ, 0 < u.re → u.re < 1 → 0 ≤ K u := by
    intro u h1 h2
    have h := hKge u h1 h2
    have h2' : 0 < 1 / (1 + (T - u.im) ^ 2) := by positivity
    linarith
  have hwcmp : ∀ u : ℂ, 0 < u.re → u.re < 1 →
      (if ‖P - u‖ > 1/2 then (1 / ‖s - u‖ ^ 2) else 0) ≤ 5 * K u := by
    intro u h1 h2
    have hsq : ‖P - u‖ ^ 2 ≤ ‖s - u‖ ^ 2 := by
      rw [hsqn u, hsqn' u]
      have hprod : 0 ≤ (s.re - u.re - (1 - u.re)) * (s.re - u.re + (1 - u.re)) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [hprod]
    have hsq2 : (T - u.im) ^ 2 ≤ ‖s - u‖ ^ 2 := by
      rw [hsqn u]
      have hTe : s.im - u.im = T - u.im := by simp [hTdef]
      nlinarith [sq_nonneg (s.re - u.re)]
    by_cases hc : ‖P - u‖ > 1/2
    · rw [if_pos hc]
      have h4 : (1 / 4 : ℝ) < ‖P - u‖ ^ 2 := by
        have hp := mul_pos (by linarith : (0 : ℝ) < ‖P - u‖ - 1/2)
          (by linarith : (0 : ℝ) < ‖P - u‖ + 1/2)
        nlinarith [hp]
      have hmaxle : max (1/4) ((T - u.im) ^ 2) ≤ ‖s - u‖ ^ 2 := max_le (by linarith) hsq2
      have hmaxpos : 0 < max (1/4) ((T - u.im) ^ 2) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      have hle1 : (1 : ℝ) / ‖s - u‖ ^ 2 ≤ 1 / max (1/4) ((T - u.im) ^ 2) :=
        one_div_le_one_div_of_le hmaxpos hmaxle
      have hle2 : (1 : ℝ) / max (1/4) ((T - u.im) ^ 2) ≤ 5 / (1 + (T - u.im) ^ 2) := by
        rcases le_total ((T - u.im) ^ 2) (1/4) with hcase | hcase
        · rw [max_eq_left hcase]
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          nlinarith [sq_nonneg (T - u.im)]
        · rw [max_eq_right hcase]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      have hle3 : 5 / (1 + (T - u.im) ^ 2) ≤ 5 * K u := by
        have h := hKge u h1 h2
        have hx : 5 / (1 + (T - u.im) ^ 2) = 5 * (1 / (1 + (T - u.im) ^ 2)) := by ring
        rw [hx]
        exact mul_le_mul_of_nonneg_left h (by norm_num)
      linarith
    · rw [if_neg hc]
      have h := hKnn u h1 h2
      linarith
  have hfinsum : ∀ z : Finset ℂ,
      ∑ x ∈ z, ((((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ)) *
          (if ‖P - x‖ > 1/2 then (1 / ‖s - x‖ ^ 2) else 0))
        ≤ 50 * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := by
    intro z
    set z' : Finset ℂ := z.filter (fun x => MeromorphicOn.divisor Λ Set.univ x ≠ 0) with hz'def
    have hsum_eq : ∑ x ∈ z, ((((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ)) *
          (if ‖P - x‖ > 1/2 then (1 / ‖s - x‖ ^ 2) else 0))
        = ∑ x ∈ z', ((((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ)) *
          (if ‖P - x‖ > 1/2 then (1 / ‖s - x‖ ^ 2) else 0)) := by
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
          linarith
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
              (if ‖P - x‖ > 1/2 then (1 / ‖s - x‖ ^ 2) else 0))
            ≤ 5 * ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) x : ℤ) : ℝ)) * K x) := by
        intro x hx
        have hst := hstripz x hx
        have hw := hwcmp x hst.1 hst.2
        have hDx := hposD x hx
        rw [hdn x hx]
        nlinarith [hw, hDx]
      have hsum_le : ∑ x ∈ z', ((((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ)) *
              (if ‖P - x‖ > 1/2 then (1 / ‖s - x‖ ^ 2) else 0))
          ≤ 5 * ∑ x ∈ z', ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) x : ℤ) : ℝ)) * K x) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hpt
      have hSfin : (Function.support (fun u : ℂ =>
          (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ)))).Finite := by
        rw [hΛdef]
        exact divisor_real_finiteSupport (N := N) χ hχ (0 : ℂ) R
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
        linarith
      have hlogN0 : 0 ≤ Real.log (N : ℝ) := by
        apply Real.log_nonneg
        exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
      have hlog2 : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
      have hfinal : 5 * (Real.log (N : ℝ) + Real.log (2 + |T|) + 10)
          ≤ 50 * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := by
        nlinarith [hlogT, hlogN0, hlog2]
      calc ∑ x ∈ z', ((((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ)) *
              (if ‖P - x‖ > 1/2 then (1 / ‖s - x‖ ^ 2) else 0))
          ≤ 5 * ∑ x ∈ z', ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) x : ℤ) : ℝ)) * K x) := hsum_le
        _ ≤ 5 * ∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ)) * K u) := by
              exact mul_le_mul_of_nonneg_left hstep (by norm_num)
        _ ≤ 5 * (Real.log (N : ℝ) + Real.log (2 + |T|) + 10) := by
              exact mul_le_mul_of_nonneg_left hbase (by norm_num)
        _ ≤ 50 * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := hfinal
    · have hz0 : z' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hz'empty
      rw [hz0]
      simp only [Finset.sum_empty]
      have hpos : 0 < 50 * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := by
        have h1 : 0 ≤ Real.log (N : ℝ) := by
          apply Real.log_nonneg
          exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
        have h2 : 0 < Real.log (2 + ‖s‖) := Real.log_pos (by linarith [norm_nonneg s])
        positivity
      exact hpos.le
  have hnn : ∀ x : ℂ, 0 ≤ ((((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ)) *
      (if ‖P - x‖ > 1/2 then (1 / ‖s - x‖ ^ 2) else 0)) :=
    fun x => mul_nonneg (hDnn_univ x) (by split <;> positivity)
  exact ⟨summable_of_sum_le hnn hfinsum, Real.tsum_le_of_sum_le hnn hfinsum⟩

/-- A Dirichlet character different from the principal character forces the modulus to be at least 3. -/
lemma three_le_modulus_of_char_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (h : χ ≠ 1) : 3 ≤ q := by
  by_contra hq
  have hq1 : 1 ≤ q := NeZero.one_le
  have hq' : q = 1 ∨ q = 2 := by omega
  rcases hq' with rfl | rfl
  · exact h (Subsingleton.elim χ 1)
  · exact h (by rw [← DirichletCharacter.toUnitHom_inj]; exact Subsingleton.elim _ _)

/-- Pointwise bound for the `f(0)`-regularised exponential kernel. -/
lemma norm_rdcKernel_le {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    {L : ℝ} (hL : 0 < L) {s u : ℂ} (hu : u.re < s.re) :
    ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L:ℂ)) * (t:ℂ))) * ((f t : ℝ) : ℂ))
      - ((f 0 : ℝ) : ℂ) / ((s - u) * (L:ℂ))‖
      ≤ (3 * B * x₀ + 2 * |f 0| / x₀) / (L ^ 2 * ‖s - u‖ ^ 2) := by
  set F : ℝ → ℂ := fun t => ((f t : ℝ) : ℂ) with hF
  have hcontF : ContinuousOn F (Set.Icc 0 x₀) :=
    Complex.continuous_ofReal.comp_continuousOn (hcont.mono Set.Icc_subset_Ici_self)
  have hf2F : ContDiffOn ℝ 2 F (Set.Ioo 0 x₀) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hf2
  have hBndF : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 F t‖ ≤ B := by
    intro t ht
    exact norm_ofReal_iteratedDeriv_two_le hf2 ht (hBnd t ht)
  have hvanF : ∀ t : ℝ, x₀ ≤ t → F t = 0 := by intro t ht; simp [hF, hsupp t ht]
  have hzre : 0 < ((s - u) * (L:ℂ)).re := by
    rw [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_pos (by linarith) hL
  have h := Commons.Analysis.Complex.lapX_sub_inv_bound (x₀ := x₀) (B := B) (f := F)
    hx₀ hB hcontF hf2F hBndF hvanF hzre
  have hnorm : ‖((s - u) * (L:ℂ))‖ ^ 2 = L ^ 2 * ‖s - u‖ ^ 2 := by
    rw [norm_mul, Complex.norm_of_nonneg hL.le]; ring
  have hF0 : ‖F 0‖ = |f 0| := by simp [hF, Complex.normSq_ofReal, Real.norm_eq_abs]
  rw [hnorm, hF0] at h
  simpa [hF] using h

/-- Real part of a von Mangoldt weighted kernel term. -/
lemma re_vonMangoldt_mul (n : ℕ) (z : ℂ) (y : ℝ) :
    (((ArithmeticFunction.vonMangoldt n : ℂ) * z * ((y : ℝ) : ℂ)).re)
      = (ArithmeticFunction.vonMangoldt n : ℝ) * z.re * y := by
  rw [Complex.mul_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- The `univ`-divisor of the completed L-function agrees with the divisor on a ball inside. -/
lemma divisor_univ_eq_closedBall {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {a : ℂ} {R : ℝ} {u : ℂ} (hu : u ∈ Metric.closedBall a R) :
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ u
      = MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall a R) u := by
  have hdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction hχ
  have hanU : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
    fun z _ => hdiff.analyticAt z
  have hanB : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall a R) :=
    fun z _ => hdiff.analyticAt z
  rw [MeromorphicOn.divisor_apply hanU.meromorphicOn (Set.mem_univ u),
    MeromorphicOn.divisor_apply hanB.meromorphicOn hu]


/-- Linnik/Heath-Brown Lemma 5.2, `σ ≥ 1` case. -/
theorem lemma5_2_sigma_ge_one (x₀ B : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 ≤ f 0)
      {ε : ℝ} (hε : 0 < ε),
      ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive),
        (∀ s : ℂ, 1 ≤ s.re → s.re ≤ 1 + Real.sqrt (Real.log (Real.log q)) / Real.log q → |s.im| ≤ Real.log q →
          (-logDeriv (DirichletCharacter.LFunction χ) s).re
            + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
                (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0))
            ≤ ((1/6 : ℝ) + ε) * Real.log (q : ℝ)) →
        ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 1 + Real.sqrt (Real.log (Real.log q)) / Real.log q → |s.im| ≤ Real.log q →
          (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / Real.log q))
            ≤ -(Real.log q) * (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
                (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (Real.log q)) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) else 0))
            + f 0 * ((1/6 : ℝ) + ε) * Real.log (q : ℝ)
            + C * (B * x₀ + |f 0| / x₀ + 1) * Real.log (2 + ‖s‖) := by
  intro f hcont hsupp hf2 hBnd hf0 ε hε
  obtain ⟨CEF, hCEFpos, hEF⟩ := Commons.NumberTheory.Linnik.explicitFormula_chi_gen x₀ B hx₀ hB
  obtain ⟨cF, hcFpos, hcF⟩ := far_zero_invSq_sum_uniform
  refine ⟨CEF * 11 + (10000 / Real.log 2) * cF + 1, by positivity, 1/2, by norm_num, by norm_num, ?_⟩
  intro q _inst χ hχ hχprim H s hs1 hs2 hsim
  classical
  have hq3 : 3 ≤ q := three_le_modulus_of_char_ne_one χ hχ
  have hq1 : 1 < q := by omega
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hLgt1 : 1 < L := by
    rw [hLdef]
    have h3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    have h1 : (1 : ℝ) < Real.log 3 := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    exact lt_of_lt_of_le h1 (Real.log_le_log (by norm_num) h3)
  have hLpos : 0 < L := by linarith
  have hsre : |s.re - 1| ≤ Real.sqrt (Real.log L) / L := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h0 : 0 ≤ Real.sqrt (Real.log L) / L := by positivity
      linarith
    · linarith [hs2]
  have hsim' : |s.im| ≤ L := hsim
  have hLne : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs1
  set Φ : ℂ → ℂ := fun u => (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L:ℂ)) * (t:ℂ))) * ((f t : ℝ) : ℂ))
      - ((f 0 : ℝ) : ℂ) / ((s - u) * (L:ℂ)) with hΦdef
  set Q : ℝ := B * x₀ + |f 0| / x₀ + 1 with hQdef
  set A : ℝ := 3 * B * x₀ + 2 * |f 0| / x₀ with hAdef
  have hQnn : 0 ≤ Q := by rw [hQdef]; positivity
  have hAnn : 0 ≤ A := by rw [hAdef]; positivity
  have hAle : A ≤ 3 * Q := by
    rw [hAdef, hQdef]
    have h1 : (0:ℝ) ≤ |f 0| / x₀ := by positivity
    have h2 : 2 * (|f 0| / x₀) ≤ 3 * (|f 0| / x₀) + 3 := by linarith
    calc 3 * B * x₀ + 2 * |f 0| / x₀ = 3 * B * x₀ + 2 * (|f 0| / x₀) := by ring
      _ ≤ 3 * B * x₀ + (3 * (|f 0| / x₀) + 3) := by linarith
      _ = 3 * (B * x₀ + |f 0| / x₀ + 1) := by ring
  have hEFb : ‖(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ) / (n : ℂ) ^ s
        * ((f (Real.log n / L) : ℝ) : ℂ))
      + (L : ℂ) * (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ u : ℤ) : ℂ) * Φ u)
      + ((f 0 : ℝ) : ℂ) * logDeriv (DirichletCharacter.LFunction χ) s‖
      ≤ CEF * Q * (Real.log L) ^ (-(1/2 : ℝ)) * Real.log (2 + ‖s‖) := by
    have h := hEF (N := q) χ hχ hχprim hcont hsupp hf2 hBnd hLgt1 s hsre hsim' hLne
    simpa [hQdef, hΦdef] using h
  -- the natural-number sum: finite support, and real part is the target sum
  have hsupp_n : ∀ n : ℕ, ⌈Real.exp (x₀ * L)⌉₊ ≤ n →
      (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ) / (n : ℂ) ^ s
        * ((f (Real.log n / L) : ℝ) : ℂ) = 0 := by
    intro n hn
    have hn' : Real.exp (x₀ * L) ≤ (n : ℝ) := by
      have h1 : Real.exp (x₀ * L) ≤ (⌈Real.exp (x₀ * L)⌉₊ : ℝ) := Nat.le_ceil _
      exact h1.trans (by exact_mod_cast hn)
    have hlog : x₀ ≤ Real.log (n : ℝ) / L := by
      rw [le_div_iff₀ hLpos]
      calc x₀ * L = Real.log (Real.exp (x₀ * L)) := (Real.log_exp _).symm
        _ ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos _) hn'
    rw [hsupp (Real.log (n : ℝ) / L) hlog]
    simp
  have hsumm_n : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ) / (n : ℂ) ^ s
        * ((f (Real.log n / L) : ℝ) : ℂ)) :=
    summable_of_ne_finset_zero (s := Finset.range (⌈Real.exp (x₀ * L)⌉₊ + 1))
      (fun n hn => by
        rw [Finset.mem_range] at hn
        exact hsupp_n n (by omega))
  have hAre : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ) / (n : ℂ) ^ s
        * ((f (Real.log n / L) : ℝ) : ℂ)).re
      = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / L) := by
    rw [Complex.re_tsum hsumm_n]
    refine tsum_congr (fun n => ?_)
    rw [mul_div_assoc]
    exact re_vonMangoldt_mul n ((χ (n : ZMod q) : ℂ) / (n : ℂ) ^ s) (f (Real.log n / L))
  -- ===== divisor data and the pointwise kernel bound =====
  set du : ℂ → ℤ := fun u => MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ u with hdudef
  set Near : ℂ → Prop := fun u => ‖(1:ℂ) + (s.im:ℂ) * Complex.I - u‖ ≤ 1/2 with hNeardef
  have huniv : ∀ u : ℂ, du u = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℤ) := by
    intro u
    rw [hdudef]
    exact Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast
      (fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z) (Set.mem_univ u)
  have hdu_nn : ∀ u : ℂ, (0:ℝ) ≤ (du u : ℝ) := by
    intro u; rw [huniv u]; positivity
  have hduzero : ∀ u : ℂ, du u ≠ 0 → DirichletCharacter.completedLFunction χ u = 0 := by
    intro u hu
    have hcast : (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℤ) ≠ 0 := by
      rw [← huniv u]; exact hu
    have haux : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u ≠ 0 :=
      fun h0 => hcast (by simp [h0])
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero haux
  have hdustrip : ∀ u : ℂ, du u ≠ 0 → 0 < u.re ∧ u.re < 1 :=
    fun u hu => completedL_zero_strip χ hχ hχprim (hduzero u hu)
  have hΦbound : ∀ u : ℂ, du u ≠ 0 → ‖Φ u‖ ≤ A / (L ^ 2 * ‖s - u‖ ^ 2) := by
    intro u hu
    have hst := hdustrip u hu
    have h := norm_rdcKernel_le hx₀ hB hcont hsupp hf2 hBnd hLpos (u := u) (s := s)
      (by linarith [hst.2, hs1])
    rw [hΦdef]
    exact h
  -- ===== the far weight =====
  set farwt : ℂ → ℝ := fun u => ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ u : ℤ) : ℝ) *
      (if ‖(1:ℂ) + (s.im:ℂ) * Complex.I - u‖ > 1/2 then (1 / ‖s - u‖ ^ 2) else 0) with hfarwtdef
  have hfarwt := hcF χ hχ hχprim (s := s) hs1
  have hfarwt_summ : Summable farwt := hfarwt.1
  have hfarwt_bound : (∑' u : ℂ, farwt u) ≤ cF * (L + Real.log (2 + ‖s‖) + 2) := by
    simpa [hLdef, hfarwtdef] using hfarwt.2
  have hfarwt_eq : ∀ u : ℂ, farwt u = (du u : ℝ) * (if Near u then 0 else (1 / ‖s - u‖ ^ 2)) := by
    intro u
    have hdueq : (du u : ℝ) = ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ u : ℤ) : ℝ) := by
      rw [hdudef]
    have h1 : farwt u = ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ u : ℤ) : ℝ) *
        (if ‖(1:ℂ) + (s.im:ℂ) * Complex.I - u‖ > 1/2 then (1 / ‖s - u‖ ^ 2) else 0) := by
      rw [hfarwtdef]
    rw [h1, hdueq]
    by_cases h : Near u
    · have h2 : ¬ (‖(1:ℂ) + (s.im:ℂ) * Complex.I - u‖ > 1/2) := by
        intro hc; have hh := h; rw [hNeardef] at hh; linarith
      rw [if_pos h, if_neg h2]
    · have h2 : ‖(1:ℂ) + (s.im:ℂ) * Complex.I - u‖ > 1/2 := by
        by_contra hc
        exact h (by rw [hNeardef]; linarith [not_lt.mp hc])
      rw [if_neg h, if_pos h2]
  have hPnorm_le : ‖(1:ℂ) + (s.im:ℂ) * Complex.I‖ ≤ 1 + |s.im| := by
    have h1 : ‖(1:ℂ) + (s.im:ℂ) * Complex.I‖ ^ 2 = 1 + s.im ^ 2 := by
      have h2 := Complex.normSq_add_mul_I 1 s.im
      rw [Complex.ofReal_one, one_pow] at h2
      rw [Complex.sq_norm]
      exact h2
    calc ‖(1:ℂ) + (s.im:ℂ) * Complex.I‖ = Real.sqrt (‖(1:ℂ) + (s.im:ℂ) * Complex.I‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (1 + s.im ^ 2) := by rw [h1]
      _ ≤ Real.sqrt ((1 + |s.im|) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_abs s.im, abs_nonneg s.im])
      _ = 1 + |s.im| := Real.sqrt_sq (by positivity)
  have hNear_iff : ∀ u : ℂ, Near u ↔ ‖(1:ℂ) + (s.im:ℂ) * Complex.I - u‖ ≤ (1/2:ℝ) := by
    intro u; simp [hNeardef]
  have hmem_ball : ∀ u : ℂ, Near u → u ∈ Metric.closedBall (0:ℂ) (|s.im| + 2) := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖u‖ ≤ ‖(1:ℂ) + (s.im:ℂ) * Complex.I‖ + ‖u - ((1:ℂ) + (s.im:ℂ) * Complex.I)‖ := by
      have := norm_add_le ((1:ℂ) + (s.im:ℂ) * Complex.I) (u - ((1:ℂ) + (s.im:ℂ) * Complex.I))
      simpa using this
    have h2 := (hNear_iff u).mp hu
    have h3 : ‖u - ((1:ℂ) + (s.im:ℂ) * Complex.I)‖ = ‖(1:ℂ) + (s.im:ℂ) * Complex.I - u‖ := by
      rw [norm_sub_rev]
    rw [h3] at h1
    linarith [hPnorm_le, h2]
  have hdiv_eq_near : ∀ u : ℂ, Near u →
      du u = MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 (|s.im| + 2)) u := by
    intro u hu
    rw [hdudef]
    exact divisor_univ_eq_closedBall χ hχ (hmem_ball u hu)
  -- ===== finite support of the near part =====
  have hSfin : (Function.support (fun u : ℂ => (du u : ℝ) * (if Near u then (1:ℝ) else 0))).Finite := by
    refine Set.Finite.subset
      (s := Function.support (fun u : ℂ =>
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall ((1:ℂ) + (s.im:ℂ) * Complex.I) (1/2))) u : ℤ))) ?_ ?_
    · exact divisor_finiteSupport χ hχ _ _
    · intro u hu
      rw [Function.mem_support] at hu ⊢
      have hdu_ne : du u ≠ 0 := by intro h0; exact hu (by rw [h0]; simp)
      have hnear : Near u := by by_contra h; exact hu (by rw [if_neg h]; simp)
      have hball : u ∈ Metric.closedBall ((1:ℂ) + (s.im:ℂ) * Complex.I) (1/2) := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        rw [hNeardef] at hnear
        simpa [norm_sub_rev] using hnear
      rw [← divisor_univ_eq_closedBall χ hχ hball]
      exact hdu_ne
  -- ===== summability =====
  have hNsumm : Summable (fun u : ℂ => (du u : ℝ) * (if Near u then (Φ u).re else 0)) := by
    refine summable_of_ne_finset_zero (s := hSfin.toFinset) (fun u hu => ?_)
    by_cases h : Near u
    · have hmem := hu
      rw [Set.Finite.mem_toFinset, Function.mem_support] at hmem
      have hdu0 : (du u : ℝ) = 0 := by simpa [h] using not_not.mp hmem
      rw [if_pos h, hdu0]; ring
    · rw [if_neg h]; ring
  have hFsumm : Summable (fun u : ℂ => (du u : ℝ) * (if Near u then 0 else (Φ u).re)) := by
    have hg : Summable (fun u : ℂ => (A / L ^ 2) * farwt u) := hfarwt_summ.mul_left _
    refine Summable.of_norm_bounded hg (fun u => ?_)
    rw [Real.norm_eq_abs]
    have h1 : |(if Near u then (0:ℝ) else (Φ u).re)| ≤ (if Near u then 0 else 1) * ‖Φ u‖ := by
      by_cases h : Near u
      · rw [if_pos h, if_pos h]; simp
      · rw [if_neg h, if_neg h, one_mul]; exact Complex.abs_re_le_norm (Φ u)
    calc |(du u : ℝ) * (if Near u then 0 else (Φ u).re)|
        = (du u : ℝ) * |(if Near u then (0:ℝ) else (Φ u).re)| := by
          rw [abs_mul, abs_of_nonneg (hdu_nn u)]
      _ ≤ (du u : ℝ) * ((if Near u then 0 else 1) * ‖Φ u‖) :=
          mul_le_mul_of_nonneg_left h1 (hdu_nn u)
      _ = ((du u : ℝ) * (if Near u then 0 else 1)) * ‖Φ u‖ := by ring
      _ ≤ ((du u : ℝ) * (if Near u then 0 else 1)) * (A / (L ^ 2 * ‖s - u‖ ^ 2)) := by
          by_cases hu : du u = 0
          · rw [hu]; simp
          · exact mul_le_mul_of_nonneg_left (hΦbound u hu)
              (by by_cases h : Near u <;> simp [h, hdu_nn])
      _ = (A / L ^ 2) * farwt u := by
          rw [hfarwt_eq u]
          by_cases h : Near u
          · rw [if_pos h, if_pos h]; ring
          · rw [if_neg h, if_neg h]; field_simp; try ring
  have hsummFam : Summable (fun u : ℂ => ((du u : ℤ) : ℂ) * Φ u) := by
    have hid : (fun u : ℂ => ((du u : ℤ) : ℂ) * Φ u)
        = fun u : ℂ => (((du u : ℤ) : ℂ) * Φ u) * (if Near u then (1:ℂ) else 0)
            + (((du u : ℤ) : ℂ) * Φ u) * (if Near u then (0:ℂ) else 1) := by
      funext u; by_cases h : Near u <;> simp [h]
    rw [hid]
    refine Summable.add ?_ ?_
    · -- near part has finite support
      have hfinC : (Function.support (fun u : ℂ =>
            (((du u : ℤ) : ℂ) * Φ u) * (if Near u then (1:ℂ) else 0))).Finite := by
        refine Set.Finite.subset hSfin ?_
        intro u hu
        rw [Function.mem_support] at hu ⊢
        by_cases h : Near u
        · simp only [h, if_true, mul_one]
          intro h0
          exact (mul_ne_zero_iff.mp hu).1 (by rw [← Complex.ofReal_intCast, h0]; simp)
        · exfalso
          exact hu (by rw [if_neg h]; ring)
      exact summable_of_ne_finset_zero (s := hfinC.toFinset)
        (fun u hu => by
          by_cases h : Near u
          · have hmem := hu
            rw [Set.Finite.mem_toFinset, Function.mem_support] at hmem
            exact not_not.mp hmem
          · rw [if_neg h]; ring)
    · refine Summable.of_norm_bounded (g := fun u : ℂ => (A / L ^ 2) * farwt u)
        (hfarwt_summ.mul_left _) (fun u => ?_)
      rw [show (((du u : ℤ) : ℂ) * Φ u) * (if Near u then (0:ℂ) else 1)
          = (((du u : ℤ) : ℂ) * Φ u) * (if Near u then (0:ℂ) else 1) from rfl]
      rw [hfarwt_eq u]
      by_cases h : Near u
      · simp [h]
      · simp only [h, if_false, norm_one, mul_one, norm_mul]
        rw [Complex.norm_intCast, abs_of_nonneg (hdu_nn u)]
        by_cases hu : du u = 0
        · simp [hu]
        · calc (du u : ℝ) * ‖Φ u‖ ≤ (du u : ℝ) * (A / (L ^ 2 * ‖s - u‖ ^ 2)) :=
                mul_le_mul_of_nonneg_left (hΦbound u hu) (hdu_nn u)
            _ = (A / L ^ 2) * ((du u : ℝ) * (1 / ‖s - u‖ ^ 2)) := by field_simp; try ring
  -- ===== real part of the divisor sum =====
  have hTre : (∑' u : ℂ, ((du u : ℤ) : ℂ) * Φ u).re
      = ∑' u : ℂ, (du u : ℝ) * (Φ u).re := by
    rw [Complex.re_tsum hsummFam]
    refine tsum_congr (fun u => ?_)
    rw [← Complex.ofReal_intCast, Complex.re_ofReal_mul]
  have hTre2 : (∑' u : ℂ, (du u : ℝ) * (Φ u).re)
      = (∑' u : ℂ, (du u : ℝ) * (if Near u then (Φ u).re else 0))
        + (∑' u : ℂ, (du u : ℝ) * (if Near u then 0 else (Φ u).re)) := by
    rw [← Summable.tsum_add hNsumm hFsumm]
    refine tsum_congr (fun u => ?_)
    by_cases h : Near u <;> simp [h]
  have hnearfinsum : (∑' u : ℂ, (du u : ℝ) * (if Near u then (Φ u).re else 0))
      = ∑ᶠ u : ℂ, (du u : ℝ) * (if Near u then (Φ u).re else 0) := by
    refine tsum_eq_finsum ?_
    refine hSfin.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    have hdu_ne : (du u : ℝ) ≠ 0 := (mul_ne_zero_iff.mp hu).1
    have hnear : Near u := by
      by_contra h
      exact (mul_ne_zero_iff.mp hu).2 (by rw [if_neg h])
    rw [if_pos hnear, mul_one]
    exact hdu_ne
  -- ===== the real part of the exponential kernel =====
  have hPhire : ∀ u : ℂ, (Φ u).re
      = (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L:ℂ)) * (t:ℂ))) * ((f t : ℝ) : ℂ)).re
        - (f 0 / L) * ((1/(s - u)).re) := by
    intro u
    by_cases hsu : (s - u) * (L:ℂ) = 0
    · have hsue : s = u := by
        rcases mul_eq_zero.mp hsu with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h (Complex.ofReal_ne_zero.mpr hLpos.ne')
      rw [hΦdef, hsue]
      simp
    · have hsu' : s - u ≠ 0 := fun h => hsu (by rw [h, zero_mul])
      have hL' : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLpos.ne'
      have h2 : (((f 0 : ℝ) : ℂ) / ((s - u) * (L:ℂ))).re
          = (f 0 / L) * ((1/(s-u)).re) := by
        have h3 : ((f 0 : ℝ) : ℂ) / ((s - u) * (L:ℂ)) = (((f 0 / L : ℝ)) : ℂ) * ((s-u)⁻¹) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, Complex.ofReal_mul, Complex.ofReal_inv]
          ring
        rw [h3, Complex.re_ofReal_mul, one_div]
      have h1 : Φ u = (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L:ℂ)) * (t:ℂ))) * ((f t : ℝ) : ℂ))
          - ((f 0 : ℝ) : ℂ) / ((s - u) * (L:ℂ)) := by rw [hΦdef]
      rw [h1, Complex.sub_re, h2]
  -- ===== the near finsum splits =====
  have support_indicator : ∀ (F : ℂ → ℝ), Function.support
      (fun u : ℂ => (du u : ℝ) * (if Near u then F u else 0)) ⊆ (↑hSfin.toFinset : Set ℂ) := by
    intro F u hu
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    rw [Function.mem_support] at hu ⊢
    have hnear : Near u := by
      by_contra h
      exact hu (by simp [h])
    have hdu0 : (du u : ℝ) ≠ 0 := by
      intro h0
      exact hu (by simp [hnear, h0])
    simp [hnear, hdu0]
  have hsplit : (∑ᶠ u : ℂ, (du u : ℝ) * (if Near u then (Φ u).re else 0))
      = (∑ᶠ u : ℂ, (du u : ℝ) * (if Near u then
            (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L:ℂ)) * (t:ℂ))) * ((f t : ℝ) : ℂ)).re else 0))
        - (f 0 / L) * (∑ᶠ u : ℂ, (du u : ℝ) * (if Near u then ((1/(s - u)).re) else 0)) := by
    set FF : ℂ → ℝ := fun u => (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s - u) * (L:ℂ)) * (t:ℂ))) * ((f t : ℝ) : ℂ)).re with hFF
    set GG : ℂ → ℝ := fun u => (1 / (s - u)).re with hGG
    have hG : (∑ᶠ u : ℂ, (du u : ℝ) * (if Near u then (Φ u).re else 0))
        = ∑ᶠ u : ℂ, (du u : ℝ) * (if Near u then (FF u - (f 0 / L) * GG u) else 0) := by
      refine finsum_congr (fun u => ?_)
      rw [hPhire u, hFF, hGG]
    have hsum : (∑ᶠ u : ℂ, (du u : ℝ) * (if Near u then (FF u - (f 0 / L) * GG u) else 0))
        = ∑ u ∈ hSfin.toFinset, (du u : ℝ) * (if Near u then (FF u - (f 0 / L) * GG u) else 0) :=
      finsum_eq_sum_of_support_subset _ (support_indicator _)
    have hfacsum : (∑ u ∈ hSfin.toFinset, (du u : ℝ) * (if Near u then (FF u - (f 0 / L) * GG u) else 0))
        = ∑ u ∈ hSfin.toFinset, ((du u : ℝ) * (if Near u then FF u else 0)
            - (f 0 / L) * ((du u : ℝ) * (if Near u then GG u else 0))) := by
      refine Finset.sum_congr rfl (fun u _ => ?_)
      by_cases h : Near u <;> simp [h] <;> try ring
    have hA : (∑ u ∈ hSfin.toFinset, (du u : ℝ) * (if Near u then FF u else 0))
        = ∑ᶠ u : ℂ, (du u : ℝ) * (if Near u then FF u else 0) :=
      (finsum_eq_sum_of_support_subset _ (support_indicator _)).symm
    have hB : (∑ u ∈ hSfin.toFinset, (du u : ℝ) * (if Near u then GG u else 0))
        = ∑ᶠ u : ℂ, (du u : ℝ) * (if Near u then GG u else 0) :=
      (finsum_eq_sum_of_support_subset _ (support_indicator _)).symm
    rw [hG, hsum, hfacsum, Finset.sum_sub_distrib, ← Finset.mul_sum, hA, hB, hFF, hGG]
  -- ===== the far part bound =====
  have hFnorm : ∀ u : ℂ, ‖(du u : ℝ) * (if Near u then 0 else (Φ u).re)‖ ≤ (A / L ^ 2) * farwt u := by
    intro u
    rw [Real.norm_eq_abs]
    have h1 : |(if Near u then (0:ℝ) else (Φ u).re)| ≤ (if Near u then 0 else 1) * ‖Φ u‖ := by
      by_cases h : Near u
      · rw [if_pos h, if_pos h]; simp
      · rw [if_neg h, if_neg h, one_mul]; exact Complex.abs_re_le_norm (Φ u)
    calc |(du u : ℝ) * (if Near u then 0 else (Φ u).re)|
        = (du u : ℝ) * |(if Near u then (0:ℝ) else (Φ u).re)| := by
          rw [abs_mul, abs_of_nonneg (hdu_nn u)]
      _ ≤ (du u : ℝ) * ((if Near u then 0 else 1) * ‖Φ u‖) :=
          mul_le_mul_of_nonneg_left h1 (hdu_nn u)
      _ = ((du u : ℝ) * (if Near u then 0 else 1)) * ‖Φ u‖ := by ring
      _ ≤ ((du u : ℝ) * (if Near u then 0 else 1)) * (A / (L ^ 2 * ‖s - u‖ ^ 2)) := by
          by_cases hu : du u = 0
          · rw [hu]; simp
          · exact mul_le_mul_of_nonneg_left (hΦbound u hu)
              (by by_cases h : Near u <;> simp [h, hdu_nn])
      _ = (A / L ^ 2) * farwt u := by
          rw [hfarwt_eq u]
          by_cases h : Near u
          · simp [h]
          · simp only [h, if_false, mul_one]
            field_simp
            try ring
  have hFlower : -( (A / L ^ 2) * (cF * (L + Real.log (2 + ‖s‖) + 2)) )
      ≤ (∑' u : ℂ, (du u : ℝ) * (if Near u then 0 else (Φ u).re)) := by
    have hAbsSumm : Summable (fun u : ℂ => ‖(du u : ℝ) * (if Near u then 0 else (Φ u).re)‖) := by
      have hg : Summable (fun u : ℂ => (A / L ^ 2) * farwt u) := hfarwt_summ.mul_left _
      exact Summable.of_nonneg_of_le (fun u => norm_nonneg _) (fun u => by
        simpa [Real.norm_eq_abs] using hFnorm u) hg
    have h1 : (∑' u : ℂ, -(‖(du u : ℝ) * (if Near u then 0 else (Φ u).re)‖))
        ≤ ∑' u : ℂ, (du u : ℝ) * (if Near u then 0 else (Φ u).re) := by
      refine Summable.tsum_le_tsum (fun u => ?_) (hAbsSumm.neg) hFsumm
      rw [Real.norm_eq_abs]
      exact neg_abs_le _
    rw [tsum_neg] at h1
    have h2 : (∑' u : ℂ, ‖(du u : ℝ) * (if Near u then 0 else (Φ u).re)‖)
        ≤ (A / L ^ 2) * (cF * (L + Real.log (2 + ‖s‖) + 2)) := by
      have hg : Summable (fun u : ℂ => (A / L ^ 2) * farwt u) := hfarwt_summ.mul_left _
      have h3 := Summable.tsum_le_tsum (fun u => by simpa [Real.norm_eq_abs] using hFnorm u)
        hAbsSumm hg
      have h4 : (∑' u : ℂ, (A / L ^ 2) * farwt u) = (A / L ^ 2) * (∑' u : ℂ, farwt u) :=
        tsum_mul_left
      rw [h4] at h3
      exact h3.trans (by
        have h5 : (0:ℝ) ≤ A / L ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left hfarwt_bound h5)
    linarith
  -- ===== abbreviations for the assembly =====
  set TL : ℝ := ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
      ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / L) with hTL
  set TN : ℝ := ∑' u : ℂ, (du u : ℝ) * (if Near u then (Φ u).re else 0) with hTN
  set TF : ℝ := ∑' u : ℂ, (du u : ℝ) * (if Near u then 0 else (Φ u).re) with hTF
  set TNf : ℝ := ∑ᶠ u : ℂ, (du u : ℝ) * (if Near u then (Φ u).re else 0) with hTNf
  set TK : ℝ := ∑ᶠ u : ℂ, (du u : ℝ) * (if Near u then ((1/(s - u)).re) else 0) with hTK
  set TI : ℝ := ∑ᶠ u : ℂ, (du u : ℝ) * (if Near u then
      (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L:ℂ)) * (t:ℂ))) * ((f t : ℝ) : ℂ)).re else 0)
    with hTI
  set Hsum : ℝ := ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ (1/2:ℝ) then ((1/(s-u)).re) else 0) with hHsum
  set Tdiv : ℝ := ∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ (1/2:ℝ) then
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L:ℂ)) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      else 0) with hTdiv
  have hTNf_eq : TN = TNf := by
    rw [hTN, hTNf]
    refine tsum_eq_finsum ?_
    refine hSfin.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    have hdu_ne : (du u : ℝ) ≠ 0 := (mul_ne_zero_iff.mp hu).1
    have hnear : Near u := by
      by_contra h
      exact (mul_ne_zero_iff.mp hu).2 (by rw [if_neg h])
    rw [if_pos hnear, mul_one]
    exact hdu_ne
  have hTN_split : TN = TI - (f 0 / L) * TK := by
    rw [hTNf_eq, hsplit]
  have hTK_Hsum : TK = Hsum := by
    rw [hTK, hHsum]
    refine finsum_congr (fun u => ?_)
    by_cases h : Near u
    · have h2 : ‖(1:ℂ) + (s.im:ℂ) * Complex.I - u‖ ≤ (1/2:ℝ) := (hNear_iff u).mp h
      simp only [h, h2, if_true]
      rw [hdiv_eq_near u h]
    · have h2 : ¬ (‖(1:ℂ) + (s.im:ℂ) * Complex.I - u‖ ≤ (1/2:ℝ)) :=
        fun hc => h ((hNear_iff u).mpr hc)
      simp only [h, h2, if_false, mul_zero]
  have hTI_Tdiv : TI = Tdiv := by
    rw [hTI, hTdiv]
    refine finsum_congr (fun u => ?_)
    by_cases h : Near u
    · have h2 : ‖(1:ℂ) + (s.im:ℂ) * Complex.I - u‖ ≤ (1/2:ℝ) := (hNear_iff u).mp h
      simp only [h, h2, if_true]
      rw [hdiv_eq_near u h]
    · have h2 : ¬ (‖(1:ℂ) + (s.im:ℂ) * Complex.I - u‖ ≤ (1/2:ℝ)) :=
        fun hc => h ((hNear_iff u).mpr hc)
      simp only [h, h2, if_false, mul_zero]
  have hHideal : Hsum - (logDeriv (DirichletCharacter.LFunction χ) s).re ≤ ((1/6 : ℝ) + ε) * L := by
    have h := H s hs1 hs2 hsim
    have h2 : (-logDeriv (DirichletCharacter.LFunction χ) s).re + Hsum ≤ ((1/6 : ℝ) + ε) * L := by
      have h3 := h
      simp only [Complex.neg_re] at h3
      exact h3
    simp only [Complex.neg_re] at h2
    linarith
  -- ===== real part of the explicit formula =====
  have hReEF : TL + L * (TN + TF) + f 0 * (logDeriv (DirichletCharacter.LFunction χ) s).re
      ≤ CEF * Q * (Real.log L) ^ (-(1/2 : ℝ)) * Real.log (2 + ‖s‖) := by
    have h1 := Complex.re_le_norm
      ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ) / (n : ℂ) ^ s
          * ((f (Real.log n / L) : ℝ) : ℂ))
        + (L : ℂ) * (∑' u : ℂ, ((du u : ℤ) : ℂ) * Φ u)
        + ((f 0 : ℝ) : ℂ) * logDeriv (DirichletCharacter.LFunction χ) s)
    have h2 : ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ) / (n : ℂ) ^ s
          * ((f (Real.log n / L) : ℝ) : ℂ))
        + (L : ℂ) * (∑' u : ℂ, ((du u : ℤ) : ℂ) * Φ u)
        + ((f 0 : ℝ) : ℂ) * logDeriv (DirichletCharacter.LFunction χ) s).re
        = (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ) / (n : ℂ) ^ s
            * ((f (Real.log n / L) : ℝ) : ℂ)).re
          + L * (∑' u : ℂ, (du u : ℝ) * (Φ u).re)
          + f 0 * (logDeriv (DirichletCharacter.LFunction χ) s).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      rw [hTre]
      ring
    rw [h2, hTre2] at h1
    have h3 : (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) : ℂ) / (n : ℂ) ^ s
          * ((f (Real.log n / L) : ℝ) : ℂ)).re = TL := by
      rw [hTL]
      exact hAre
    rw [h3] at h1
    exact le_trans h1 hEFb
  -- ===== final arithmetic =====
  have hlogLbound : (Real.log L) ^ (-(1/2 : ℝ)) ≤ 11 := by
    have hL3 : Real.log 3 ≤ L := by
      rw [hLdef]
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hq3)
    have hlogL_ge : (1/121 : ℝ) ≤ Real.log L := by
      have h1 : (121/120 : ℝ) ≤ L := by
        have h := Real.log_three_gt_d9
        linarith
      have h2 : 0 < L := by linarith
      have h3 : (L - 1) / L ≤ Real.log L := by
        have h := Real.log_le_sub_one_of_pos (x := L⁻¹) (inv_pos.mpr h2)
        rw [Real.log_inv] at h
        have h4 : (L - 1) / L = 1 - L⁻¹ := by field_simp; try ring
        rw [h4]; linarith
      have h5 : (121/120 - 1)/(121/120) ≤ (L - 1) / L := by
        rw [div_le_div_iff₀ (by norm_num) h2]
        nlinarith [h1]
      have h6 : (121/120 - 1)/(121/120) = (1/121 : ℝ) := by norm_num
      linarith [h3, h5]
    have hpos : 0 < Real.log L := Real.log_pos hLgt1
    have hsqrt : (1/11 : ℝ) ≤ Real.sqrt (Real.log L) := by
      rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/11)]
      exact Real.sqrt_le_sqrt (by nlinarith [hlogL_ge])
    have heq : (Real.log L) ^ (-(1/2 : ℝ)) = 1 / Real.sqrt (Real.log L) := by
      rw [Real.rpow_neg hpos.le, Real.sqrt_eq_rpow]
      exact (one_div _).symm
    rw [heq, div_le_iff₀ (Real.sqrt_pos.mpr hpos)]
    linarith
  have hQlog : (0:ℝ) < Real.log (2 + ‖s‖) :=
    Real.log_pos (by have := norm_nonneg s; linarith)
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hEbound : CEF * Q * (Real.log L) ^ (-(1/2 : ℝ)) * Real.log (2 + ‖s‖)
      ≤ CEF * 11 * Q * Real.log (2 + ‖s‖) := by
    have h1 : CEF * Q * (Real.log L) ^ (-(1/2 : ℝ)) ≤ CEF * 11 * Q :=
      (mul_le_mul_of_nonneg_left hlogLbound (by positivity)).trans_eq (by ring)
    exact mul_le_mul_of_nonneg_right h1 hQlog.le
  have hXbound : (A / L) * (cF * (L + Real.log (2 + ‖s‖) + 2))
      ≤ (10000 / Real.log 2) * cF * Q * Real.log (2 + ‖s‖) := by
    have hL1 : (1:ℝ) ≤ L := by linarith
    have hnorm_s : ‖s‖ ≤ 3 * L := by
      have h1 : s.re ≤ 1 + Real.sqrt (Real.log L) / L := hs2
      have h2 : Real.sqrt (Real.log L) / L ≤ 1 := by
        rw [div_le_one hLpos]
        have h3 : Real.log L ≤ L ^ 2 := by nlinarith [hL1, Real.log_le_sub_one_of_pos hLpos]
        rw [Real.sqrt_le_iff]
        exact ⟨by positivity, h3⟩
      have h3 : s.re ≤ 2 := by linarith
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ = s.re + |s.im| := by rw [abs_of_pos (by linarith : (0:ℝ) < s.re)]
        _ ≤ 2 + L := by linarith [hsim]
        _ ≤ 3 * L := by linarith
    have hlogbound : Real.log (2 + ‖s‖) ≤ 5 * L := by
      have h1 : (2:ℝ) + ‖s‖ ≤ 2 + 3 * L := by linarith
      have h2 : Real.log (2 + ‖s‖) ≤ Real.log (2 + 3 * L) :=
        Real.log_le_log (by positivity) h1
      have h3 : Real.log (2 + 3 * L) ≤ 2 + 3 * L := Real.log_le_self (by positivity)
      linarith
    have hres : (A / L) * (cF * (L + Real.log (2 + ‖s‖) + 2))
        = (A * cF) * ((L + Real.log (2 + ‖s‖) + 2) / L) := by field_simp; try ring
    rw [hres]
    have hratio : (L + Real.log (2 + ‖s‖) + 2) / L ≤ 8 := by
      rw [div_le_iff₀ hLpos]
      nlinarith [hlogbound, hL1]
    have hmain : A * cF * ((L + Real.log (2+‖s‖) + 2)/L) ≤ A * cF * 8 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    have hlast : A * cF * 8 ≤ (10000 / Real.log 2) * cF * Q * Real.log (2 + ‖s‖) := by
      have h1 : A * cF * 8 ≤ 24 * Q * cF := by nlinarith [hAle, hcFpos.le, hAnn]
      have h2 : 24 * Q * cF ≤ (10000 / Real.log 2) * cF * Q * Real.log (2 + ‖s‖) := by
        have h4 : Real.log 2 ≤ Real.log (2 + ‖s‖) :=
          Real.log_le_log (by norm_num) (by have := norm_nonneg s; linarith)
        have h3 : (24:ℝ) ≤ (10000 / Real.log 2) * Real.log (2 + ‖s‖) := by
          calc (24:ℝ) ≤ 10000 := by norm_num
            _ = (10000 / Real.log 2) * Real.log 2 := by field_simp
            _ ≤ (10000 / Real.log 2) * Real.log (2 + ‖s‖) :=
                mul_le_mul_of_nonneg_left h4 (by positivity)
        nlinarith [h3, hQnn, hcFpos.le, mul_nonneg hQnn hcFpos.le]
      linarith
    linarith
  -- ===== assemble =====
  have hTF' : -(L * TF) ≤ (A / L) * (cF * (L + Real.log (2 + ‖s‖) + 2)) := by
    have h3 : L * (-((A / L ^ 2) * (cF * (L + Real.log (2 + ‖s‖) + 2)))) ≤ L * TF :=
      mul_le_mul_of_nonneg_left hFlower hLpos.le
    have h4 : -(L * (-((A / L ^ 2) * (cF * (L + Real.log (2 + ‖s‖) + 2)))))
        = (A / L) * (cF * (L + Real.log (2 + ‖s‖) + 2)) := by field_simp; try ring
    linarith [h3, h4.le, h4.ge]
  have hfin : TL ≤ -(L * Tdiv) + f 0 * ((1/6 : ℝ) + ε) * L
      + (CEF * 11 + (10000 / Real.log 2) * cF + 1) * Q * Real.log (2 + ‖s‖) := by
    have h1 := hReEF
    rw [hTN_split, hTI_Tdiv, hTK_Hsum] at h1
    have heq : L * ((Tdiv - (f 0 / L) * Hsum) + TF) = L * Tdiv - f 0 * Hsum + L * TF := by
      field_simp; try ring
    rw [heq] at h1
    have h2f : f 0 * (Hsum - (logDeriv (DirichletCharacter.LFunction χ) s).re)
        ≤ f 0 * ((1/6 : ℝ) + ε) * L := by
      have h2 := mul_le_mul_of_nonneg_left hHideal hf0
      linarith
    have hCL : CEF * 11 * Q * Real.log (2 + ‖s‖) + (10000 / Real.log 2) * cF * Q * Real.log (2 + ‖s‖)
        ≤ (CEF * 11 + (10000 / Real.log 2) * cF + 1) * Q * Real.log (2 + ‖s‖) := by
      nlinarith [mul_nonneg hQnn hQlog.le]
    have stepA : TL ≤ CEF * Q * (Real.log L) ^ (-(1/2 : ℝ)) * Real.log (2 + ‖s‖) - L * Tdiv
        + f 0 * (Hsum - (logDeriv (DirichletCharacter.LFunction χ) s).re) + -(L * TF) := by
      linarith [h1]
    have stepB : TL ≤ CEF * 11 * Q * Real.log (2 + ‖s‖) - L * Tdiv
        + f 0 * ((1/6 : ℝ) + ε) * L + (A / L) * (cF * (L + Real.log (2 + ‖s‖) + 2)) := by
      linarith [stepA, h2f, hTF', hEbound]
    have stepC : TL ≤ CEF * 11 * Q * Real.log (2 + ‖s‖) - L * Tdiv
        + f 0 * ((1/6 : ℝ) + ε) * L + (10000 / Real.log 2) * cF * Q * Real.log (2 + ‖s‖) := by
      linarith [stepB, hXbound]
    linarith [stepC, hCL]
  simpa only [hLdef, hTL, hTdiv, hQdef, neg_mul] using hfin
end Commons.NumberTheory.Linnik
