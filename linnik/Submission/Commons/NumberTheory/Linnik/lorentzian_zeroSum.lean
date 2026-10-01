import Mathlib
import Submission.Commons.NumberTheory.Linnik.zeroSum_invSq_bound
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity

/-!
# The Lorentzian zero sum of a completed Dirichlet L-function

For a non-trivial primitive Dirichlet character `χ mod N` we bound the divisor-weighted
Lorentzian (Poisson) kernel sum over the zeros of the completed L-function
`Λ = completedLFunction χ`:

`Σ_u (divisor Λ univ u) · 1/(1 + (t - Im u)²) ≤ c · (log N + log (2 + |t|) + 2)`,

uniformly in `t`.  The sum is moreover summable.

**Proof route.**  Since `χ` is non-trivial, `Λ` is entire, so its divisor on `univ` is
non-negative and supported on the zeros of `Λ`, all of which lie in the critical strip
`0 < Re < 1` (`completedL_zero_strip`).  For such a point `u` the Lorentzian weight is
dominated by the inverse-square kernel centred at `s = 2 + i t`:

`1/(1 + (t - Im u)²) ≤ 8 / (1 + ‖s - u‖²)`

(the real part of `u` being between `0` and `1` keeps `|2 - Re u| ∈ [1,2]`).  The
inverse-square sum over any ball is bounded, uniformly in the radius, by
`zeroSum_invSq_bound`.  This gives the bound for the divisor on `closedBall 0 R`, for
every `R`, with a constant independent of `R`.

To pass from `closedBall 0 R` to `univ` we compare, for any finite set `z` of points,
`Σ_{u ∈ z} (divisor Λ univ u) w(u) ≤ Σᶠ_u (divisor Λ (closedBall 0 R) u) w(u)` where
`R` is chosen larger than all `‖u‖`, `u ∈ z`: on the ball the two divisors agree
(`divisor_eq_analyticOrderNatAt_cast`), and outside the support of the univ-divisor the
summands vanish.  Boundedness of all finite partial sums of a non-negative function gives
summability, and the `tsum` bound, via `summable_of_sum_le` / `Real.tsum_le_of_sum_le`.
-/

open Complex DirichletCharacter Metric MeromorphicOn Function
open scoped Real BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Commons.NumberTheory.Linnik

theorem lorentzian_zeroSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ,
      Summable (fun u : ℂ =>
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℝ) *
          (1 / (1 + (t - u.im) ^ 2))) ∧
      (∑' u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℝ) *
          (1 / (1 + (t - u.im) ^ 2)))
        ≤ c * (Real.log (N : ℝ) + Real.log (2 + |t|) + 2) := by
  classical
  obtain ⟨C, hCpos, hC⟩ := zeroSum_invSq_bound χ hχ hχprim
  refine ⟨16 * C, by positivity, ?_⟩
  intro t
  set Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ with hΛdef
  set s : ℂ := (2 : ℂ) + (t : ℂ) * Complex.I with hsdef
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
  have hstrip : ∀ (R : ℝ) (u : ℂ), MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u ≠ 0 →
      0 < u.re ∧ u.re < 1 := by
    intro R u hd
    exact completedL_zero_strip χ hχ hχprim (by simpa [hΛdef] using hΛzero R u hd)
  have hDnn : ∀ (ρ : ℝ) (x : ℂ), (0 : ℝ) ≤ ((MeromorphicOn.divisor Λ (Metric.closedBall 0 ρ) x : ℤ) : ℝ) := by
    intro ρ x
    by_cases hx : x ∈ Metric.closedBall (0 : ℂ) ρ
    · exact divisor_real_nonneg_of_analyticOnNhd (hΛan _) hx
    · have h0 : MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) ρ) x = 0 := by
        rw [MeromorphicOn.divisor_def, if_neg]
        exact fun hc => hx hc.2
      rw [h0]; simp
  have hWpos : ∀ x : ℂ, (0 : ℝ) < 1 / (1 + (t - x.im) ^ 2) := fun x => by positivity
  have hweight : ∀ u : ℂ, 0 ≤ u.re → u.re ≤ 1 →
      (1 : ℝ) / (1 + (t - u.im) ^ 2) ≤ 8 / (1 + ‖s - u‖ ^ 2) := by
    intro u h1 h2
    have hnorm : ‖s - u‖ ^ 2 = (2 - u.re) ^ 2 + (t - u.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have hre : (s - u).re = 2 - u.re := by simp [s]
      have him : (s - u).im = t - u.im := by simp [s]
      rw [hre, him]; ring
    rw [hnorm]
    have hy : (0 : ℝ) < 1 + (t - u.im) ^ 2 := by positivity
    have hd : (0 : ℝ) < 1 + ((2 - u.re) ^ 2 + (t - u.im) ^ 2) := by positivity
    rw [div_le_div_iff₀ hy hd]
    nlinarith [sq_nonneg (t - u.im), sq_nonneg (2 - u.re), h1, h2]
  have hsnorm : ‖s‖ ≤ 2 + |t| := by
    have hns : ‖s‖ ^ 2 = 4 + t ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have hre : s.re = 2 := by simp [s]
      have him : s.im = t := by simp [s]
      rw [hre, him]; ring
    have hle : ‖s‖ ^ 2 ≤ (2 + |t|) ^ 2 := by
      rw [hns]; nlinarith [abs_nonneg t, sq_abs t]
    calc ‖s‖ = Real.sqrt (‖s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg s)).symm
      _ ≤ Real.sqrt ((2 + |t|) ^ 2) := Real.sqrt_le_sqrt hle
      _ = 2 + |t| := Real.sqrt_sq (by positivity)
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogt : Real.log 2 ≤ Real.log (2 + |t|) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hlogs : Real.log (2 + ‖s‖) ≤ Real.log 2 + Real.log (2 + |t|) := by
    have h1 : 2 + ‖s‖ ≤ 2 * (2 + |t|) := by linarith [hsnorm, abs_nonneg t]
    calc Real.log (2 + ‖s‖) ≤ Real.log (2 * (2 + |t|)) :=
          Real.log_le_log (by positivity) h1
      _ = Real.log 2 + Real.log (2 + |t|) := Real.log_mul (by norm_num) (by positivity)
  have hballbound : ∀ R : ℝ,
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ) *
          (1 / (1 + (t - u.im) ^ 2)))
        ≤ 16 * C * (Real.log (N : ℝ) + Real.log (2 + |t|) + 2) := by
    intro R
    have hSfin : (Function.support
        (fun u : ℂ => MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u)).Finite :=
      MeromorphicOn.divisor_support_finite_of_subset (f := Λ) (U := Metric.closedBall (0 : ℂ) R)
        (V := Metric.closedBall (0 : ℂ) R) (hΛan _).meromorphicOn
        (isCompact_closedBall (0 : ℂ) R) (Set.Subset.refl _)
    set S : Finset ℂ := hSfin.toFinset with hSdef
    have hS : ∀ u : ℂ, u ∈ S ↔ MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u ≠ 0 :=
      fun u => hSfin.mem_toFinset
    have he1 : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ) *
          (1 / (1 + (t - u.im) ^ 2)))
        = ∑ u ∈ S, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ) *
          (1 / (1 + (t - u.im) ^ 2)) := by
      refine finsum_eq_sum_of_support_subset _ ?_
      intro u hu
      rw [Function.mem_support] at hu
      exact (hS u).mpr (by intro h0; exact hu (by simp [h0]))
    have he2 : (∑ᶠ u : ℂ, |((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ)| *
          (1 / (1 + ‖s - u‖ ^ 2)))
        = ∑ u ∈ S, |((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ)| *
          (1 / (1 + ‖s - u‖ ^ 2)) := by
      refine finsum_eq_sum_of_support_subset _ ?_
      intro u hu
      rw [Function.mem_support] at hu
      have hne : ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ) ≠ 0 := by
        intro h0
        exact hu (by simp [h0])
      exact (hS u).mpr (by intro h0; exact hne (by simp [h0]))
    rw [he1]
    calc ∑ u ∈ S, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ) *
            (1 / (1 + (t - u.im) ^ 2))
        ≤ ∑ u ∈ S, |((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ)| *
            (8 / (1 + ‖s - u‖ ^ 2)) := by
          apply Finset.sum_le_sum
          intro u hu
          have hdu := (hS u).mp hu
          have hst := hstrip R u hdu
          have hw := hweight u (le_of_lt hst.1) (le_of_lt hst.2)
          have hnn := hDnn R u
          rw [abs_of_nonneg hnn]
          exact mul_le_mul_of_nonneg_left hw hnn
      _ = 8 * ∑ u ∈ S, |((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ)| *
            (1 / (1 + ‖s - u‖ ^ 2)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u hu; ring
      _ ≤ 8 * (C * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc ∑ u ∈ S, |((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ)| *
                (1 / (1 + ‖s - u‖ ^ 2))
              = ∑ᶠ u : ℂ, |((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ)| *
                (1 / (1 + ‖s - u‖ ^ 2)) := he2.symm
            _ ≤ C * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := hC s R
      _ ≤ 16 * C * (Real.log (N : ℝ) + Real.log (2 + |t|) + 2) := by
          nlinarith [hlogs, hlogN, hlogt, hlog2pos.le, hCpos.le]
  have hmain : ∀ z : Finset ℂ,
      ∑ x ∈ z, (((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ) *
          (1 / (1 + (t - x.im) ^ 2)))
        ≤ 16 * C * (Real.log (N : ℝ) + Real.log (2 + |t|) + 2) := by
    intro z
    set z' : Finset ℂ := z.filter (fun u => MeromorphicOn.divisor Λ Set.univ u ≠ 0) with hz'def
    have hz'sub : z' ⊆ z := Finset.filter_subset _ _
    have hsum_eq : ∑ x ∈ z, (((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ) *
          (1 / (1 + (t - x.im) ^ 2)))
        = ∑ x ∈ z', (((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ) *
          (1 / (1 + (t - x.im) ^ 2))) := by
      refine (Finset.sum_subset hz'sub ?_).symm
      intro x hx hxn
      have h0 : MeromorphicOn.divisor Λ Set.univ x = 0 := by
        by_contra hne
        exact hxn (Finset.mem_filter.mpr ⟨hx, hne⟩)
      rw [h0]; simp
    rw [hsum_eq]
    by_cases hz'empty : z'.Nonempty
    · set R : ℝ := 2 + ∑ u ∈ z', ‖u‖ with hRdef
      have hdn : ∀ u ∈ z', MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u
          = MeromorphicOn.divisor Λ Set.univ u := by
        intro u hu
        have huR : ‖u‖ ≤ R := by
          simp only [hRdef]
          have h1 : ‖u‖ ≤ ∑ v ∈ z', ‖v‖ :=
            Finset.single_le_sum (fun v (_ : v ∈ z') => norm_nonneg v) hu
          linarith
        have huB : u ∈ Metric.closedBall (0 : ℂ) R := by
          rw [Metric.mem_closedBall, dist_zero_right]; exact huR
        rw [huniv u, hball R u huB]
      have hz'bound : ∑ x ∈ z', (((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ) *
            (1 / (1 + (t - x.im) ^ 2)))
          ≤ ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ) *
            (1 / (1 + (t - u.im) ^ 2))) := by
        have hrew : ∀ x ∈ z', (((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ) *
              (1 / (1 + (t - x.im) ^ 2)))
            = (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) x : ℤ) : ℝ) *
              (1 / (1 + (t - x.im) ^ 2))) := by
          intro x hx; rw [hdn x hx]
        rw [Finset.sum_congr rfl hrew]
        have hSRfin : (Function.support
            (fun u : ℂ => MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u)).Finite :=
          MeromorphicOn.divisor_support_finite_of_subset (f := Λ) (U := Metric.closedBall (0 : ℂ) R)
            (V := Metric.closedBall (0 : ℂ) R) (hΛan _).meromorphicOn
            (isCompact_closedBall (0 : ℂ) R) (Set.Subset.refl _)
        set SR : Finset ℂ := hSRfin.toFinset with hSRdef
        have hSR : ∀ u : ℂ, u ∈ SR ↔ MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u ≠ 0 :=
          fun u => hSRfin.mem_toFinset
        have hsub : z' ⊆ SR := by
          intro u hu
          exact (hSR u).mpr (by rw [hdn u hu]; exact (Finset.mem_filter.mp hu).2)
        have hfinsum : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ) *
            (1 / (1 + (t - u.im) ^ 2)))
            = ∑ u ∈ SR, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ) *
            (1 / (1 + (t - u.im) ^ 2))) := by
          refine finsum_eq_sum_of_support_subset _ ?_
          intro u hu
          rw [Function.mem_support] at hu
          exact (hSR u).mpr (by intro h0; exact hu (by simp [h0]))
        rw [hfinsum]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun x _ _ => mul_nonneg (hDnn R x) (le_of_lt (hWpos x)))
      calc ∑ x ∈ z', (((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ) * (1 / (1 + (t - x.im) ^ 2)))
          ≤ ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R) u : ℤ) : ℝ) * (1 / (1 + (t - u.im) ^ 2))) := hz'bound
        _ ≤ 16 * C * (Real.log (N : ℝ) + Real.log (2 + |t|) + 2) := hballbound R
    · have hz0 : z' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hz'empty
      rw [hz0]
      simp only [Finset.sum_empty]
      have : (0:ℝ) < 16 * C * (Real.log (N : ℝ) + Real.log (2 + |t|) + 2) := by
        have h1 : (0:ℝ) < Real.log (2 + |t|) := by linarith [hlogt, hlog2pos]
        positivity
      exact le_of_lt this
  have hnn : ∀ x : ℂ, (0 : ℝ) ≤ (((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ) *
      (1 / (1 + (t - x.im) ^ 2))) := by
    intro x
    have h1 : (0:ℝ) ≤ ((MeromorphicOn.divisor Λ Set.univ x : ℤ) : ℝ) := by
      rw [huniv x]
      exact_mod_cast Nat.cast_nonneg (analyticOrderNatAt Λ x)
    exact mul_nonneg h1 (le_of_lt (hWpos x))
  exact ⟨summable_of_sum_le hnn hmain, Real.tsum_le_of_sum_le hnn hmain⟩

end Commons.NumberTheory.Linnik
