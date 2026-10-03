/-
# The periodised-window facts for the modified `g`-side bump `φ̃_{N,k,j}(t)` (the `1 ≤ N` form)

Statement: `Work.KMTPlan.A6.VarphitildeNtjPeriodizeAux`.

The modified `g`-side bump of §6/§8 (KMT (tpntj)) is

  `φ̃_{N,k,j}(t)(ξ) = (2^{-dk} N^d ξ)^j φ̃_{N,k}(t)(ξ)`,  `d = P.natDegree`,

the product of the (modulated) bump with a power of the frequency variable.  The three facts about
its periodisation `Φ = periodize (φ̃_{N,k,j}(t))` proved here are

* the pointwise bound `‖Φ θ‖ ≤ M` with the explicit witness
  `M = (Finset.Icc (-(⌊R⌋+2)) (⌊R⌋+1)).card * 2^{2d+1}`, `R = 2^{d(k - Log N)}`
  (the `card` being the number of integers `m` with `|x_θ + m| ≤ R`);
* `MemLp Φ ⊤ circleMeasure`;
* the arc: `Φ θ ≠ 0 → θ ∈ arcSet 0 R`.

## The proof

All three conjuncts come from **three** sorry-free facts:

* `Work.KMTPlan.A6.varphitildeNtj_support_lt` — the narrow support of `φ̃` (radius `R` exactly,
  with *no* hypothesis on `P.natDegree`, `N` or `k`);
* `Work.KMTPlan.A6.varphitildeNtj_norm_le_global` (below) — the uniform pointwise bound
  `‖φ̃_{N,k,j}(t)‖ ≤ 2^{2d+1}` for `j ∈ {-1,0,1}` and `(k,j) ≠ (0,-1)`, in *all* degenerate
  ranges (`d = 0`, `N = 0`, `j = -1`); it is built from `varphitildeNtj_pointwise`
  (the generic case `1 ≤ N`, `1 ≤ d`), `varphitildeNt_norm_le_one`, and
  `varphitildeNtj_eq_zero_of_abs_le` (the vanishing near the origin, which supplies the *lower*
  bound on `|ξ|` needed for the singular twist `j = -1`);
* `Work.Analysis.IonescuWainger.memLp_periodize`, whose hypotheses are only *measurable*,
  *supported in `[-R,R]`* and *bounded by `C`* — no smoothness, no integrability, and in
  particular **no `t ∈ [1/2,1]` restriction** (`varphitildeNtj_bounds`/`periodizeMemLpTop` are
  not needed: the `t`-dependence never has to be touched, since the modulation has modulus one).

The counting is the content: `periodize φ θ = ∑'_m φ (x_θ + m)` and every integer `m` outside
`Finset.Icc (-(⌊R⌋+2)) (⌊R⌋+1)` has a vanishing term, because `x_θ ∈ [0,1)` forces
`|x_θ + m| > R` (`Int.floor_le`, `Int.lt_floor_add_one`); `tsum_eq_sum` turns the `tsum` into that
finite sum, and `norm_sum_le` plus the `2^{2d+1}`-bound give `card · 2^{2d+1}`.  The arc conjunct is
the contrapositive: if every term of the collapsed sum vanished then the periodisation would be
`0`; otherwise `|x_θ + m| < R` and `θ = ((x_θ + m : ℝ) : Circle)` is the `arcSet 0 R` witness.

## Why the hypothesis `1 ≤ N`

Every consumer has `N = ⌊a n⌋ ≥ 1`.  The proof below is the `1 ≤ N` form of the frozen statement
`Work.KMTPlan.A6.VarphitildeNtjPeriodize`; the hypothesis is not used, because the estimate is
proved in the full generality of that statement (including `N = 0`, where the weight
`2^{-dk}N^dξ` vanishes for `d ≥ 1`).  The `N = 0` case is kept so that the argument is uniform in
`N` and no case analysis on the degenerate factor `N^d` is needed.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.VarphiNtjPeriodizeAux
import Submission.Work.KMTPlan.A6.periodizeVarphitildeNtjBound
import Submission.Work.KMTPlan.A6.lowModRandL2Gh
import Submission.Work.KMTPlan.A6.MdlPktG_fareyPart

namespace Work.KMTPlan.A6

set_option linter.unusedVariables false

open MeasureTheory

/-! ## Auxiliary facts for the periodised modified `g`-side bump `φ̃_{N,k,j}(t)` -/

/-- The set `{-1, 0, 1}` of twists, as a disjunction. -/
private lemma three_way (j : ℤ) (hj : j ∈ ({-1, 0, 1} : Finset ℤ)) :
    j = -1 ∨ j = 0 ∨ j = 1 := by
  simpa [Finset.mem_insert, Finset.mem_singleton] using hj

/-- **A uniform pointwise bound for the modified `g`-side bump `φ̃_{N,k,j}(t)` in the full
generality needed here** (no hypothesis on `N` or on `P.natDegree` beyond the non-degeneracy
`k = 0 → j ≠ -1`).

* for `j = 0` the bump is `φ̃_{N,t}`, of modulus `≤ 1`;
* for `j = 1` and `d = P.natDegree ≥ 1` the weight is bounded by `2^d` on the support of `φ̃_N`
  (`varphitildeNtj_norm_le`), and for `d = 0` the support has radius `1`;
* for `j = -1` (so `k ≠ 0`) and `d ≥ 1` one uses `varphitildeNtj_pointwise`; the two remaining
  degenerate ranges are `d = 0` (where the vanishing near the origin gives `|ξ| > 1/2`) and
  `N = 0` (where the coefficient `2^{-dk}N^dξ` vanishes). -/
private lemma varphitildeNtj_norm_le_global (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t : ℝ)
    (hj : j ∈ ({-1, 0, 1} : Finset ℤ)) (hk : k = 0 → j ≠ -1) :
    ∀ ξ : ℝ, ‖varphitildeNtj P N k j t ξ‖ ≤ (2 : ℝ) ^ (2 * P.natDegree + 1) := by
  have hmem : j = -1 ∨ j = 0 ∨ j = 1 := three_way j hj
  intro ξ
  by_cases hd0 : P.natDegree = 0
  · rcases hmem with h1 | h2 | h3
    · subst h1
      have hk0 : k ≠ 0 := fun h => hk h rfl
      have hcoef : ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree
          * ξ : ℝ) = ξ := by
        rw [hd0]; simp
      by_cases hφ : varphitildeNtj P N k (-1) t ξ = 0
      · rw [hφ, norm_zero]; positivity
      · rw [varphitildeNtj, hcoef, zpow_neg_one]
        have hδ : (2 : ℝ) ^ (-((P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))
            + ((P.natDegree : ℝ) + 1))) = 1 / 2 := by
          rw [hd0]; norm_num
        have hgt : (1 / 2 : ℝ) < |ξ| := by
          by_contra hle
          refine hφ (varphitildeNtj_eq_zero_of_abs_le P N k hk0 (-1) t ?_)
          rw [hδ]
          exact le_of_not_gt hle
        have hV : ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ‖ ≤ 1 :=
          varphitildeNt_norm_le_one P P.natDegree N k t ξ
        have hξpos : 0 < |ξ| := by linarith
        calc ‖((ξ : ℝ) : ℂ)⁻¹ * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ‖
            ≤ ‖((ξ : ℝ) : ℂ)⁻¹‖ * ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ‖ :=
              norm_mul_le _ _
          _ = |ξ|⁻¹ * ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ‖ := by
              rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ |ξ|⁻¹ * 1 := mul_le_mul_of_nonneg_left hV (by positivity)
          _ = |ξ|⁻¹ := mul_one _
          _ ≤ 2 := le_of_lt (by
              rw [inv_lt_comm₀ hξpos (by norm_num : (0 : ℝ) < 2),
                show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
              exact hgt)
          _ ≤ (2 : ℝ) ^ (2 * P.natDegree + 1) := by rw [hd0]; norm_num
    · subst h2
      rw [varphitildeNtj_zero]
      exact le_trans (varphitildeNt_norm_le_one P P.natDegree N k t ξ) (one_le_pow₀ (by norm_num))
    · subst h3
      have hcoef : ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree
          * ξ : ℝ) = ξ := by
        rw [hd0]; simp
      by_cases hφ : varphitildeNtj P N k 1 t ξ = 0
      · rw [hφ, norm_zero]; positivity
      · have hE : (2 : ℝ) ^ ((P.natDegree : ℝ) *
            ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) = 1 := by
          rw [hd0]; simp
        have hlt : |ξ| < 1 := by
          have h := varphitildeNtj_support_lt P N k 1 t ξ hφ
          rwa [hE] at h
        rw [varphitildeNtj, hcoef, zpow_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc |ξ| * ‖Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ‖
            ≤ 1 * 1 := mul_le_mul hlt.le (varphitildeNt_norm_le_one P P.natDegree N k t ξ)
                (norm_nonneg _) (by norm_num)
          _ ≤ (2 : ℝ) ^ (2 * P.natDegree + 1) := by rw [hd0]; norm_num
  · have hdne : P.natDegree ≠ 0 := hd0
    by_cases hN0 : N = 0
    · subst hN0
      have hcoef : ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * (((0 : ℕ) : ℝ)) ^ P.natDegree
          * ξ : ℝ) = 0 := by
        rw [Nat.cast_zero, zero_pow hdne, mul_zero, zero_mul]
      rcases hmem with h1 | h2 | h3
      · subst h1
        rw [varphitildeNtj, hcoef, Complex.ofReal_zero, zero_zpow (-1) (by norm_num), zero_mul,
          norm_zero]
        positivity
      · subst h2
        rw [varphitildeNtj, hcoef, Complex.ofReal_zero, zpow_zero, one_mul]
        exact le_trans (varphitildeNt_norm_le_one P P.natDegree 0 k t ξ) (one_le_pow₀ (by norm_num))
      · subst h3
        rw [varphitildeNtj, hcoef, Complex.ofReal_zero, zero_zpow 1 (by norm_num), zero_mul,
          norm_zero]
        positivity
    · have hN1 : 1 ≤ N := by omega
      have hkj : k ≠ 0 ∨ 0 ≤ j := by
        by_cases hk0 : k = 0
        · right
          rcases hmem with h1 | h2 | h3
          · exact absurd h1 (hk hk0)
          · subst h2; norm_num
          · subst h3; norm_num
        · exact Or.inl hk0
      exact varphitildeNtj_pointwise P (by omega) N k j t ξ hN1 hj hkj

theorem VarphitildeNtjPeriodizeAux (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t : ℝ)
    (hj : j ∈ ({-1, 0, 1} : Finset ℤ)) (hk : k = 0 → j ≠ -1) (hN : 1 ≤ N) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ θ : Work.Analysis.IonescuWainger.Circle,
        ‖Work.Analysis.IonescuWainger.periodize (Work.KMTPlan.A6.varphitildeNtj P N k j t) θ‖ ≤ M) ∧
      MeasureTheory.MemLp
        (Work.Analysis.IonescuWainger.periodize (Work.KMTPlan.A6.varphitildeNtj P N k j t))
        ⊤ Work.Analysis.IonescuWainger.circleMeasure ∧
      (∀ θ : Work.Analysis.IonescuWainger.Circle,
        Work.Analysis.IonescuWainger.periodize (Work.KMTPlan.A6.varphitildeNtj P N k j t) θ ≠ 0 →
        θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0
          ((2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))))) := by
  set R : ℝ := (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
    with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  -- the support radius of `φ̃_{N,k,j}(t)` is exactly `R`
  have hsupp : ∀ ξ : ℝ, varphitildeNtj P N k j t ξ ≠ 0 → |ξ| < R := by
    intro ξ hξ
    have h := varphitildeNtj_support_lt P N k j t ξ hξ
    rwa [← hR] at h
  have hvan : ∀ x : ℝ, R < |x| → varphitildeNtj P N k j t x = 0 := by
    intro x hx
    by_contra h
    exact absurd (hsupp x h) (not_lt.mpr hx.le)
  have hmem : j = -1 ∨ j = 0 ∨ j = 1 := three_way j hj
  have hkj : k ≠ 0 ∨ 0 ≤ j := by
    by_cases hk0 : k = 0
    · right
      rcases hmem with h1 | h2 | h3
      · exact absurd h1 (hk hk0)
      · subst h2; norm_num
      · subst h3; norm_num
    · exact Or.inl hk0
  have hmeas : Measurable (varphitildeNtj P N k j t) :=
    (contDiff_varphitildeNtj_all P N k j t hkj).continuous.measurable
  have hC : ∀ ξ : ℝ, ‖varphitildeNtj P N k j t ξ‖ ≤ (2 : ℝ) ^ (2 * P.natDegree + 1) :=
    varphitildeNtj_norm_le_global P N k j t hj hk
  -- only the shifts in this window contribute to the periodisation
  have hzero : ∀ (θ : Work.Analysis.IonescuWainger.Circle) (m : ℤ),
      m ∉ Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1) →
      varphitildeNtj P N k j t (circleRep θ + (m : ℝ)) = 0 := by
    intro θ m hm
    by_contra hne
    have hlt := hsupp (circleRep θ + (m : ℝ)) hne
    have hx1 := circleRep_nonneg θ
    have hx2 := circleRep_lt_one θ
    have hle := abs_le.mp (le_of_lt hlt)
    have hm1 : m ≤ ⌊R⌋ + 1 := by
      have h1 : (m : ℝ) ≤ R := by linarith [hle.2, hx1]
      have h2 := Int.le_floor.mpr h1
      linarith
    have hm2 : -(⌊R⌋ + 2) ≤ m := by
      have h1 : ((-m - 2 : ℤ) : ℝ) ≤ R := by push_cast; linarith [hle.1, hx2]
      have h2 := Int.le_floor.mpr h1
      linarith
    exact hm (Finset.mem_Icc.mpr ⟨hm2, hm1⟩)
  have hcollapse : ∀ θ : Work.Analysis.IonescuWainger.Circle,
      Work.Analysis.IonescuWainger.periodize (varphitildeNtj P N k j t) θ =
        ∑ m ∈ Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1),
          varphitildeNtj P N k j t (circleRep θ + (m : ℝ)) := by
    intro θ
    rw [Work.Analysis.IonescuWainger.periodize]
    exact tsum_eq_sum (fun m hm => hzero θ m hm)
  refine ⟨((Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1)).card : ℝ) * (2 : ℝ) ^ (2 * P.natDegree + 1),
    ?_, ?_, ?_, ?_⟩
  · positivity
  · intro θ
    rw [hcollapse θ]
    calc ‖∑ m ∈ Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1),
            varphitildeNtj P N k j t (circleRep θ + (m : ℝ))‖
        ≤ ∑ m ∈ Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1),
            ‖varphitildeNtj P N k j t (circleRep θ + (m : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1), (2 : ℝ) ^ (2 * P.natDegree + 1) :=
          Finset.sum_le_sum (fun m _ => hC _)
      _ = ((Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1)).card : ℝ) * (2 : ℝ) ^ (2 * P.natDegree + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  · exact Work.Analysis.IonescuWainger.memLp_periodize hmeas hR0 hvan hC
  · intro θ hθ
    have hex : ∃ m : ℤ, m ∈ Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1) ∧
        varphitildeNtj P N k j t (circleRep θ + (m : ℝ)) ≠ 0 := by
      by_contra hcon
      have hcon' : ∀ m : ℤ, m ∈ Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1) →
          varphitildeNtj P N k j t (circleRep θ + (m : ℝ)) = 0 := by
        intro m hm
        by_contra h
        exact hcon ⟨m, hm, h⟩
      exact hθ (by rw [hcollapse θ]; exact Finset.sum_eq_zero (fun m hm => hcon' m hm))
    obtain ⟨m, _, hmne⟩ := hex
    have hlt := hsupp _ hmne
    refine ⟨circleRep θ + (m : ℝ), le_of_lt hlt, ?_⟩
    rw [zero_add]
    have hInt : (((m : ℝ)) : Work.Analysis.IonescuWainger.Circle) = 0 := by
      rw [show (m : ℝ) = m • (1 : ℝ) by rw [zsmul_eq_mul, mul_one]]
      rw [AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
    rw [AddCircle.coe_add, hInt, add_zero]
    exact (coe_circleRep θ).symm


end Work.KMTPlan.A6
