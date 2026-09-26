import Mathlib

/-!
# `x ↦ g ‖x‖` is analytic when `g : ℝ → ℂ` is even and analytic

`(⊤ : ℕ∞ω)` is `ω`, the class of *analytic* functions.  The point of the target
lemma `Work.RadialSpace.contDiff_comp_norm_omega` is therefore the following:
if `g : ℝ → ℂ` is **analytic** and even, then `x ↦ g ‖x‖` is analytic on `ℝⁿ`.

The Euclidean norm is analytic away from the origin (`contDiffAt_norm`), so the
only point at issue is `x = 0`.  There the evenness of `g` saves the day: the
power series of `g` at `0` has only even terms, so on a ball
`g (‖x‖) = ∑ j, c₂ⱼ (‖x‖²)ʲ = q.sum (‖x‖²)` for a one-variable power series `q`
of positive radius.  Composing the analytic function `q.sum` with the analytic
(polynomial) function `x ↦ ‖x‖²` gives analyticity at the origin.

Everything is proved from scratch below: parity of the iterated derivatives of an
even function, uniqueness of the coefficients of a convergent power series via
`HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum`, the construction of the
"decimated" scalar series and the positivity of its radius of convergence.
-/

noncomputable section

open Filter Topology
open scoped Topology ContDiff NNReal

namespace Work.RadialSpace

/-! ### Parity of the iterated derivatives of an even function -/

/-- An odd function `ℝ → ℂ` vanishes at `0`. -/
lemma Function.Odd.eq_zero {f : ℝ → ℂ} (hf : Function.Odd f) : f 0 = 0 := by
  have h : f 0 = -f 0 := by simpa using hf 0
  have h2 : (2 : ℂ) * f 0 = 0 := by
    rw [two_mul]
    nth_rewrite 1 [h]
    rw [neg_add_cancel]
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- The derivative of an even function `ℝ → ℂ` is odd. -/
lemma Function.Even.deriv_odd {f : ℝ → ℂ} (hf : Function.Even f) :
    Function.Odd (deriv f) := by
  intro x
  have h1 : deriv f x = -deriv f (-x) := by
    have := deriv_comp_neg f x
    rwa [show (fun y : ℝ => f (-y)) = f from funext fun y => hf y] at this
  simpa using (congrArg Neg.neg h1).symm

/-- The derivative of an odd function `ℝ → ℂ` is even. -/
lemma Function.Odd.deriv_even {f : ℝ → ℂ} (hf : Function.Odd f) :
    Function.Even (deriv f) := by
  intro x
  have h2 : deriv (fun y : ℝ => f (-y)) x = -deriv f (-x) := deriv_comp_neg f x
  rw [show (fun y : ℝ => f (-y)) = fun y => -f y from funext fun y => hf y] at h2
  have h1 : deriv (fun y : ℝ => -f y) x = -deriv f x := by
    simpa using deriv_fun_const_smul_field (c := (-1 : ℝ)) (f := f) (x := x)
  rw [h1] at h2
  simpa using (congrArg Neg.neg h2).symm

/-- For an even function, the `m`-th iterated derivative is even for even `m` and
odd for odd `m`. -/
lemma Function.Even.iteratedDeriv_parity {f : ℝ → ℂ} (hf : Function.Even f) (m : ℕ) :
    (Even m → Function.Even (iteratedDeriv m f)) ∧
      (Odd m → Function.Odd (iteratedDeriv m f)) := by
  induction m with
  | zero =>
    refine ⟨fun _ => ?_, fun h => absurd h ?_⟩
    · simpa [iteratedDeriv_zero] using hf
    · exact (by decide : ¬ Odd (0 : ℕ))
  | succ m ih =>
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · rw [iteratedDeriv_succ]
      exact Function.Odd.deriv_even (ih.2 (Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hm)))
    · rw [iteratedDeriv_succ]
      exact Function.Even.deriv_odd (ih.1 (Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hm)))

/-- All iterated derivatives of odd order of an even function vanish at `0`. -/
lemma Function.Even.iteratedDeriv_odd_eq_zero {f : ℝ → ℂ} (hf : Function.Even f)
    {m : ℕ} (hm : Odd m) : iteratedDeriv m f 0 = 0 :=
  Function.Odd.eq_zero ((Function.Even.iteratedDeriv_parity hf m).2 hm)

/-! ### Reindexing a series with vanishing odd terms -/

/-- If a series converges and all its odd terms vanish, then the sum of its even
terms is the same. -/
lemma hasSum_even_of_odd_eq_zero {f : ℕ → ℂ} {a : ℂ} (h : HasSum f a)
    (hodd : ∀ k, f (2 * k + 1) = 0) : HasSum (fun k => f (2 * k)) a := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k) :=
    mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)
  have hinj' : Function.Injective (fun k : ℕ => 2 * k + 1) :=
    (add_left_injective 1).comp hinj
  have h1 : Summable (fun k => f (2 * k)) := h.summable.comp_injective hinj
  have h2 : Summable (fun k => f (2 * k + 1)) := h.summable.comp_injective hinj'
  have key := tsum_even_add_odd h1 h2
  have hzero : (∑' k, f (2 * k + 1)) = 0 := by
    rw [show (fun k => f (2 * k + 1)) = (fun _ => (0 : ℂ)) from funext hodd, tsum_zero]
  rw [hzero, add_zero] at key
  have hval : (∑' k, f (2 * k)) = a := by rw [key, h.tsum_eq]
  simpa [hval] using h1.hasSum

/-! ### The decimated scalar series -/

/-- The scalar power series `∑ j, cⱼ sʲ` attached to the even subsequence of the
coefficients `c` of a one-variable power series on `ℝ` with values in `ℂ`. -/
def evenRadialSeries (p : FormalMultilinearSeries ℝ ℝ ℂ) :
    FormalMultilinearSeries ℝ ℝ ℂ :=
  fun j => p.coeff (2 * j) •
    ((ContinuousMultilinearMap.mkPiAlgebraFin ℝ j ℂ).compContinuousLinearMap
      (fun _ : Fin j => Complex.ofRealCLM))

lemma evenRadialSeries_apply (p : FormalMultilinearSeries ℝ ℝ ℂ) (j : ℕ)
    (v : Fin j → ℝ) :
    evenRadialSeries p j v = p.coeff (2 * j) * ∏ i, (v i : ℂ) := by
  simp [evenRadialSeries, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    List.prod_ofFn]

lemma evenRadialSeries_apply_const (p : FormalMultilinearSeries ℝ ℝ ℂ) (j : ℕ) (s : ℝ) :
    evenRadialSeries p j (fun _ : Fin j => s) = p.coeff (2 * j) * (s : ℂ) ^ j := by
  rw [evenRadialSeries_apply]
  congr 1
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma evenRadialSeries_norm_le (p : FormalMultilinearSeries ℝ ℝ ℂ) (j : ℕ) :
    ‖evenRadialSeries p j‖ ≤ ‖p.coeff (2 * j)‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun v => ?_
  rw [evenRadialSeries_apply, norm_mul]
  have hprod : ‖∏ i : Fin j, ((v i : ℝ) : ℂ)‖ = ∏ i : Fin j, ‖v i‖ := by
    rw [norm_prod]
    exact Finset.prod_congr rfl fun i _ => by simp
  rw [hprod]

/-! ### The main argument -/

/-- **Analyticity of `x ↦ g ‖x‖` at the origin.**  If `g : ℝ → ℂ` is analytic at every
point of `ℝ` and even, then `x ↦ g ‖x‖` is analytic at `0 ∈ ℝᴺ`. -/
lemma analyticAt_comp_norm_zero {N : ℕ} {g : ℝ → ℂ}
    (hg : ContDiff ℝ ⊤ g) (he : Function.Even g) :
    AnalyticAt ℝ (fun x : EuclideanSpace ℝ (Fin N) => g ‖x‖) 0 := by
  have han : AnalyticOnNhd ℝ g Set.univ := hg.analyticOnNhd
  have hanOn : AnalyticOn ℝ g Set.univ := han.analyticOn
  obtain ⟨p, hp⟩ : ∃ p : FormalMultilinearSeries ℝ ℝ ℂ, HasFPowerSeriesAt g p 0 :=
    han 0 trivial
  have hiff : ∀ᶠ z : ℝ in 𝓝 (0 : ℝ),
      HasSum (fun m => z ^ m • p.coeff m) (g (0 + z)) := hasFPowerSeriesAt_iff.mp hp
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hiff
  have hconv : ∀ z : ℝ, |z| < ε → HasSum (fun m => z ^ m • p.coeff m) (g z) := by
    intro z hz
    have hmem : z ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      exact hz
    simpa using hε hmem
  -- all odd coefficients of the power series of an even function vanish
  have hcoeff_odd : ∀ m : ℕ, Odd m → p.coeff m = 0 := by
    intro m hm
    obtain ⟨r, hr⟩ := hp
    have hsum := hr.iteratedFDeriv_eq_sum hanOn (v := fun _ : Fin m => (1 : ℝ))
    rw [← iteratedDeriv_eq_iteratedFDeriv,
      Function.Even.iteratedDeriv_odd_eq_zero he hm] at hsum
    have hcard : (∑ σ : Equiv.Perm (Fin m), p m (fun _ => (1 : ℝ))) =
        (m.factorial : ℂ) • p.coeff m := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        nsmul_eq_mul, smul_eq_mul]
      rfl
    rw [hcard] at hsum
    have h2 : (m.factorial : ℂ) * p.coeff m = 0 := by
      rw [smul_eq_mul] at hsum
      exact hsum.symm
    exact (mul_eq_zero.mp h2).resolve_left (by exact_mod_cast Nat.factorial_ne_zero m)
  -- a small radius where the original series converges absolutely
  set t : ℝ := ε / 2 with ht
  have htpos : 0 < t := by rw [ht]; linarith
  have htabs : |t| < ε := by rw [abs_of_pos htpos, ht]; linarith
  have hsumm : Summable (fun m => ‖p.coeff m‖ * ‖t‖ ^ m) := by
    have h1 : Summable (fun m => ‖t ^ m • p.coeff m‖) := (hconv t htabs).summable.norm
    refine h1.congr fun m => ?_
    rw [norm_smul, norm_pow, mul_comm]
  have hsub : Summable (fun j => ‖p.coeff (2 * j)‖ * (t ^ 2) ^ j) := by
    have h1 : Summable (fun j => ‖p.coeff (2 * j)‖ * ‖t‖ ^ (2 * j)) :=
      hsumm.comp_injective (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0))
    refine h1.congr fun j => ?_
    rw [show ‖t‖ ^ (2 * j) = (t ^ 2) ^ j by
      rw [Real.norm_of_nonneg htpos.le, pow_mul]]
  have hq_radius : 0 < (evenRadialSeries p).radius := by
    have hle : NNReal.mk (t ^ 2) (sq_nonneg t) ≤ (evenRadialSeries p).radius := by
      refine FormalMultilinearSeries.le_radius_of_summable_norm _
        (r := NNReal.mk (t ^ 2) (sq_nonneg t)) ?_
      refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hsub
      · positivity
      · rw [NNReal.coe_mk]
        gcongr
        exact evenRadialSeries_norm_le p j
    have h0 : (0 : ℝ≥0) < NNReal.mk (t ^ 2) (sq_nonneg t) := by
      have h2 : (0 : ℝ) < t ^ 2 := by positivity
      exact_mod_cast h2
    exact lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr h0) hle
  have hq_an : AnalyticAt ℝ (fun s : ℝ => (evenRadialSeries p).sum s) 0 :=
    (FormalMultilinearSeries.hasFPowerSeriesOnBall (evenRadialSeries p) hq_radius).analyticAt
  have hG : AnalyticAt ℝ
      (fun x : EuclideanSpace ℝ (Fin N) => (evenRadialSeries p).sum (‖x‖ ^ 2)) 0 :=
    AnalyticAt.comp (g := fun s : ℝ => (evenRadialSeries p).sum s)
      (f := fun x : EuclideanSpace ℝ (Fin N) => ‖x‖ ^ 2) (x := 0)
      (by rw [show ‖(0 : EuclideanSpace ℝ (Fin N))‖ ^ 2 = 0 by simp]; exact hq_an)
      ((contDiff_norm_sq ℝ (n := ⊤)).contDiffAt.analyticAt)
  refine AnalyticAt.congr hG ?_
  filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin N)) hεpos] with x hx
  have hxn : ‖x‖ < ε := by
    have h := Metric.mem_ball.mp hx
    rwa [dist_eq_norm, sub_zero] at h
  have hsum := hconv ‖x‖ (by rwa [abs_of_nonneg (norm_nonneg x)])
  have heven := hasSum_even_of_odd_eq_zero hsum (fun k => by
    rw [hcoeff_odd (2 * k + 1) ⟨k, rfl⟩, smul_zero])
  have hterm : ∀ j : ℕ, (fun m => ‖x‖ ^ m • p.coeff m) (2 * j) =
      (evenRadialSeries p) j (fun _ : Fin j => ‖x‖ ^ 2) := by
    intro j
    change ‖x‖ ^ (2 * j) • p.coeff (2 * j) =
      (evenRadialSeries p) j (fun _ : Fin j => ‖x‖ ^ 2)
    rw [evenRadialSeries_apply_const, Complex.ofReal_pow, ← pow_mul]
    simp [mul_comm, Complex.ofReal_pow]
  show (evenRadialSeries p).sum (‖x‖ ^ 2) = g ‖x‖
  rw [show (evenRadialSeries p).sum (‖x‖ ^ 2) =
      ∑' j, (evenRadialSeries p) j (fun _ : Fin j => ‖x‖ ^ 2) from rfl]
  rw [show (∑' j, (evenRadialSeries p) j (fun _ : Fin j => ‖x‖ ^ 2)) =
      ∑' j, ‖x‖ ^ (2 * j) • p.coeff (2 * j) from
    tsum_congr (fun j => (hterm j).symm)]
  simpa using heven.tsum_eq

/-! ### The target lemma -/

theorem contDiff_comp_norm_omega {n : ℕ} [NeZero n] {g : ℝ → ℂ}
    (hg : ContDiff ℝ ⊤ g) (he : Function.Even g) :
    ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin n) => g ‖x‖) := by
  rw [contDiff_omega_iff_analyticOnNhd]
  intro x _
  rcases eq_or_ne x 0 with rfl | hx
  · exact analyticAt_comp_norm_zero hg he
  · have h1 : AnalyticAt ℝ g ‖x‖ := (hg.contDiffAt).analyticAt
    have h2 : AnalyticAt ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) x :=
      (contDiffAt_norm ℝ hx).analyticAt
    simpa [Function.comp_def] using h1.comp h2

end Work.RadialSpace
