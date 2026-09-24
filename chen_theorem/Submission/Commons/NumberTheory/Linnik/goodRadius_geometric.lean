import Mathlib
import Submission.Commons.NumberTheory.Linnik.completedL_zeroCount
import Submission.Commons.NumberTheory.Linnik.goodRadius_pair

open Complex DirichletCharacter Metric Set MeasureTheory
open scoped Real BigOperators ENNReal NNReal Topology

noncomputable section

namespace Commons.NumberTheory.Linnik

/-! # A good radius in a geometric window: `goodRadius_geometric`

For a primitive non-trivial character `χ mod N` and every sufficiently large `A`,
there is a radius `T ∈ [A, 2A]` whose circle `|z| = T` stays at distance at least
`1/ℓ(A)` (`ℓ(A) := log (A+2) + log N + 2`, in the sense
`ℓ(A)² · |‖u‖ − T| ≥ 1`) from every zero `u` of the completed L-function.

## Proof

Elementary interval-covering.  For a fixed `A`, put `δ := 1/ℓ(A)²` and
`B := 2A + δ`.  A radius `T ∈ [A, 2A]` is *bad* if some zero `u` has
`|‖u‖ − T| < δ`; such a zero necessarily satisfies `‖u‖ ≤ B`.  The zeros of `Λ`
inside `closedBall 0 B` form a finite set (divisor support), whose cardinality is
bounded by the divisor sum on that ball, i.e. by `c·B·(log(B+2)+log N+2)` with the
constant `c` of `completedL_zeroCount`.  Hence the total length of the forbidden
intervals `(‖u‖−δ, ‖u‖+δ)` is at most `c·B·(log(B+2)+logN+2)·2δ ≤ 12·c·A/ℓ(A) < A`
once `ℓ(A) > 12c`, i.e. for `A ≥ A₀`.  A short measure argument (a finite family of
open intervals of total width `< A` cannot cover an interval of length `A`) then yields
a point `T ∈ [A,2A]` avoiding all forbidden intervals. -/

/-- A point outside the open interval `(z−h, z+h)` is at distance `≥ h` from `z`. -/
lemma grg_not_mem_Ioo_abs_ge {x z h : ℝ} (hh : 0 < h) (hx : x ∉ Set.Ioo (z - h) (z + h)) :
    h ≤ |x - z| := by
  by_contra hlt
  have hlt' : |x - z| < h := lt_of_not_ge hlt
  have h1 : x < z + h := by
    have := (abs_sub_lt_iff.mp hlt').1
    linarith
  have h2 : z - h < x := by
    have := (abs_sub_lt_iff.mp hlt').2
    linarith
  exact hx ⟨h2, h1⟩

/-- A measure-theoretic covering lemma on the real line: an interval of length `ℓ` cannot
be covered by `m` open intervals of total width `m·w` when `m·w < ℓ`; consequently some
point of the interval stays at distance `≥ w/2` from every centre.  (Here each interval
has full width `w`, i.e. half-width `w/2`.) -/
lemma grg_exists_good_point_of_small_measure {a b : ℝ} (hab : a ≤ b) {w : ℝ} (hw : 0 < w)
    (centres : Finset ℝ) (hcard : (centres.card : ℝ) * w < b - a) :
    ∃ x : ℝ, a ≤ x ∧ x ≤ b ∧ ∀ z ∈ centres, w / 2 ≤ |x - z| := by
  classical
  by_contra h
  -- every point of [a,b] lies in some open interval (z−w/2, z+w/2)
  have hcover : Set.Icc a b ⊆ ⋃ z ∈ (centres : Set ℝ), Set.Ioo (z - w / 2) (z + w / 2) := by
    intro x hx
    by_contra hxmem
    have hnotmem : ∀ z ∈ centres, x ∉ Set.Ioo (z - w / 2) (z + w / 2) := by
      intro z hz hzmem
      apply hxmem
      exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, hzmem⟩⟩
    have hgood : ∀ z ∈ centres, w / 2 ≤ |x - z| := by
      intro z hz
      exact grg_not_mem_Ioo_abs_ge (x := x) (z := z) (h := w / 2) (by positivity : 0 < w / 2)
        (hnotmem z hz)
    exact h ⟨x, hx.1, hx.2, hgood⟩
  have hvol_le : volume (Set.Icc a b) ≤
      volume (⋃ z ∈ (centres : Set ℝ), Set.Ioo (z - w / 2) (z + w / 2)) := by
    exact measure_mono hcover
  have hvol_union : volume (⋃ z ∈ (centres : Set ℝ), Set.Ioo (z - w / 2) (z + w / 2)) ≤
      ∑ z ∈ centres, volume (Set.Ioo (z - w / 2) (z + w / 2)) := by
    exact measure_biUnion_finset_le centres (fun z : ℝ => Set.Ioo (z - w / 2) (z + w / 2))
  have hvol_each (z : ℝ) : volume (Set.Ioo (z - w / 2) (z + w / 2)) = ENNReal.ofReal w := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  have hvol_sum : (∑ z ∈ centres, volume (Set.Ioo (z - w / 2) (z + w / 2))) =
      ENNReal.ofReal ((centres.card : ℝ) * w) := by
    calc
      (∑ z ∈ centres, volume (Set.Ioo (z - w / 2) (z + w / 2)))
          = ∑ _z ∈ centres, ENNReal.ofReal w := by
              refine Finset.sum_congr rfl ?_
              intro z hz
              exact hvol_each z
      _ = ENNReal.ofReal ((centres.card : ℝ) * w) := by
        rw [Finset.sum_const]
        rw [nsmul_eq_mul]
        rw [show ((centres.card : ℕ) : ℝ≥0∞) = ENNReal.ofReal (centres.card : ℝ) by simp]
        exact (ENNReal.ofReal_mul (p := (centres.card : ℝ)) (q := w) (by positivity)).symm
  have hvol_big : volume (Set.Icc a b) = ENNReal.ofReal (b - a) := Real.volume_Icc
  have hle' : ENNReal.ofReal (b - a) ≤ ENNReal.ofReal ((centres.card : ℝ) * w) := by
    calc
      ENNReal.ofReal (b - a) = volume (Set.Icc a b) := by rw [hvol_big]
      _ ≤ volume (⋃ z ∈ (centres : Set ℝ), Set.Ioo (z - w / 2) (z + w / 2)) := hvol_le
      _ ≤ ∑ z ∈ centres, volume (Set.Ioo (z - w / 2) (z + w / 2)) := hvol_union
      _ = ENNReal.ofReal ((centres.card : ℝ) * w) := hvol_sum
  have hba_nonneg : 0 ≤ b - a := by linarith
  have hprod_nonneg : 0 ≤ (centres.card : ℝ) * w := by positivity
  have hle_real : b - a ≤ (centres.card : ℝ) * w := by
    have ht := ENNReal.toReal_le_toReal (a := ENNReal.ofReal (b - a))
      (b := ENNReal.ofReal ((centres.card : ℝ) * w))
      (ENNReal.ofReal_ne_top (r := b - a)) (ENNReal.ofReal_ne_top (r := (centres.card : ℝ) * w))
    have ht' : (ENNReal.ofReal (b - a)).toReal ≤ (ENNReal.ofReal ((centres.card : ℝ) * w)).toReal :=
      ht.mpr hle'
    have h1 : (ENNReal.ofReal (b - a)).toReal = b - a := ENNReal.toReal_ofReal hba_nonneg
    have h2 : (ENNReal.ofReal ((centres.card : ℝ) * w)).toReal = (centres.card : ℝ) * w :=
      ENNReal.toReal_ofReal hprod_nonneg
    rw [h1, h2] at ht'
    exact ht'
  linarith

/-! ## Zeros of the completed L-function inside a closed ball

`Λ := completedLFunction χ` is entire and not identically zero (for `χ ≠ 1`), so its
divisor on a closed ball has finite support containing all zeros inside the ball, with
coefficient `≥ 1` at each zero. -/

/-- The divisor coefficient of `Λ` at a zero inside the closed ball is at least `1`. -/
lemma grg_zeroCoeff_ge_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {B : ℝ} {z : ℂ} (hzB : ‖z‖ ≤ B)
    (hz0 : DirichletCharacter.completedLFunction χ z = 0) :
    (1 : ℤ) ≤ (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) B)) z := by
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hΛdiff : Differentiable ℂ Λ := by simpa [Λ] using (DirichletCharacter.differentiable_completedLFunction hχ)
  have hΛne : Λ ≠ 0 := by
    intro hz
    have h0 : Λ 0 ≠ 0 := by simpa [Λ] using (Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim)
    exact h0 (congrFun hz 0)
  have hΛan : AnalyticOnNhd ℂ Λ (closedBall (0 : ℂ) B) := by
    intro u _
    exact hΛdiff.analyticAt u
  have hzK : z ∈ closedBall (0 : ℂ) B := by simpa [Metric.mem_closedBall, dist_eq_norm] using hzB
  have hnz : MeromorphicOn.divisor Λ (closedBall (0 : ℂ) B) z ≠ 0 :=
    Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero hΛdiff hΛne hzK (by simpa [Λ] using hz0)
  have hnn : (0 : ℤ) ≤ MeromorphicOn.divisor Λ (closedBall (0 : ℂ) B) z := by
    exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (f := Λ) (U := closedBall (0 : ℂ) B) hΛan) z
  have hle : (1 : ℤ) ≤ MeromorphicOn.divisor Λ (closedBall (0 : ℂ) B) z := by omega
  simpa [Λ] using hle

/-- The set of zeros of `Λ` inside `closedBall 0 B` is contained in the support of the
divisor of `Λ` on that ball. -/
lemma grg_zeroSet_subset_divisorSupport {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {B : ℝ} :
    ({u : ℂ | DirichletCharacter.completedLFunction χ u = 0 ∧ ‖u‖ ≤ B} : Set ℂ) ⊆
      Function.support (fun u : ℂ =>
        MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) B) u) := by
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  intro z hz
  rw [Function.mem_support]
  have hΛdiff : Differentiable ℂ Λ := by simpa [Λ] using (DirichletCharacter.differentiable_completedLFunction hχ)
  have hΛne : Λ ≠ 0 := by
    intro h
    have h0 : Λ 0 ≠ 0 := by simpa [Λ] using (Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim)
    exact h0 (congrFun h 0)
  have hzK : z ∈ closedBall (0 : ℂ) B := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz.2
  exact Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero hΛdiff hΛne hzK (by simpa [Λ] using hz.1)

/-- The zero set of `Λ` in a closed ball is finite. -/
lemma grg_zeroSet_finite {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {B : ℝ} (hB : 0 ≤ B) :
    ({u : ℂ | DirichletCharacter.completedLFunction χ u = 0 ∧ ‖u‖ ≤ B} : Set ℂ).Finite := by
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hdif : Differentiable ℂ Λ := by simpa [Λ] using (DirichletCharacter.differentiable_completedLFunction hχ)
  have hΛan : AnalyticOnNhd ℂ Λ (closedBall (0 : ℂ) B) := by
    intro u _
    exact hdif.analyticAt u
  have hsup : (Function.support fun u : ℂ => MeromorphicOn.divisor Λ (closedBall (0 : ℂ) B) u).Finite := by
    simpa using (MeromorphicOn.divisor_support_finite_of_subset (f := Λ) (U := closedBall (0 : ℂ) B)
      (V := closedBall (0 : ℂ) B) hΛan.meromorphicOn (isCompact_closedBall (0 : ℂ) B)
        (by intro z hz; exact hz))
  exact hsup.subset (by simpa [Λ] using (grg_zeroSet_subset_divisorSupport χ hχ hχprim (B := B)))

/-- The cardinality of the finite zero set of `Λ` inside `closedBall 0 B` is at most the
(sum over all `u` of the) divisor coefficients of `Λ` on that ball. -/
lemma grg_zeroCard_le_divisorFinsum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {B : ℝ} (hB : 0 ≤ B) :
    let Z : Set ℂ := {u : ℂ | DirichletCharacter.completedLFunction χ u = 0 ∧ ‖u‖ ≤ B}
    ∀ hZ : Z.Finite,
      ((hZ.toFinset.card : ℝ) ≤
        ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) B)) u : ℤ) : ℝ)) := by
  intro Z hZ
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hdif : Differentiable ℂ Λ := by simpa [Λ] using (DirichletCharacter.differentiable_completedLFunction hχ)
  have hΛan : AnalyticOnNhd ℂ Λ (closedBall (0 : ℂ) B) := by
    intro u _
    exact hdif.analyticAt u
  let coeff : ℂ → ℤ := fun u => MeromorphicOn.divisor Λ (closedBall (0 : ℂ) B) u
  have hcoeff_nonneg (u : ℂ) : (0 : ℤ) ≤ coeff u := by
    exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (f := Λ) (U := closedBall (0 : ℂ) B) hΛan) u
  have hsupFin : (Function.support coeff).Finite := by
    simpa [coeff, Λ] using (MeromorphicOn.divisor_support_finite_of_subset (f := Λ)
      (U := closedBall (0 : ℂ) B) (V := closedBall (0 : ℂ) B) hΛan.meromorphicOn
        (isCompact_closedBall (0 : ℂ) B) (by intro z hz; exact hz))
  let Zfin : Finset ℂ := hZ.toFinset
  let supp : Finset ℂ := hsupFin.toFinset
  have hmem_Zfin (z : ℂ) : z ∈ Zfin ↔ z ∈ Z := by
    dsimp [Zfin]
    exact hZ.mem_toFinset
  have hmem_supp (z : ℂ) : z ∈ supp ↔ z ∈ Function.support coeff := by
    dsimp [supp]
    exact hsupFin.mem_toFinset
  have hZsub_supp : Zfin ⊆ supp := by
    intro z hz
    rw [hmem_supp]
    have hzZ : z ∈ Z := (hmem_Zfin z).1 hz
    have hmem : z ∈ Function.support coeff := by
      rw [Function.mem_support]
      dsimp [coeff]
      have hge : (1 : ℤ) ≤ (MeromorphicOn.divisor Λ (closedBall (0 : ℂ) B)) z :=
        grg_zeroCoeff_ge_one χ hχ hχprim (z := z) hzZ.2 hzZ.1
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) hge)
    exact hmem
  -- Σ over Zfin of coeff ≥ card Zfin
  have hsum_Zfin : (Zfin.card : ℝ) ≤ ∑ z ∈ Zfin, ((coeff z : ℤ) : ℝ) := by
    calc
      (Zfin.card : ℝ) = ∑ z ∈ Zfin, (1 : ℝ) := by
        exact_mod_cast (Finset.card_eq_sum_ones Zfin)
      _ ≤ ∑ z ∈ Zfin, ((coeff z : ℤ) : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro z hz
        have hge : (1 : ℤ) ≤ coeff z := by
          have hzZ : z ∈ Z := (hmem_Zfin z).1 hz
          exact grg_zeroCoeff_ge_one χ hχ hχprim (z := z) hzZ.2 hzZ.1
        exact_mod_cast hge
  have hsum_le_supp : (∑ z ∈ Zfin, ((coeff z : ℤ) : ℝ)) ≤ ∑ z ∈ supp, ((coeff z : ℤ) : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hZsub_supp ?_
    intro z hz _hznot
    exact_mod_cast hcoeff_nonneg z
  have hsupp_eq_finsum : (∑ z ∈ supp, ((coeff z : ℤ) : ℝ)) =
      ∑ᶠ u : ℂ, (((coeff u : ℤ) : ℝ)) := by
    refine (finsum_eq_finsetSum_of_support_subset (f := fun u : ℂ => ((coeff u : ℤ) : ℝ))
      (s := supp) ?_).symm
    intro u hu
    have huS : u ∈ Function.support coeff := by
      rw [Function.mem_support] at hu ⊢
      dsimp at hu
      exact_mod_cast hu
    exact (hmem_supp u).2 huS
  calc
    ((hZ.toFinset.card : ℝ)) = (Zfin.card : ℝ) := rfl
    _ ≤ ∑ z ∈ Zfin, ((coeff z : ℤ) : ℝ) := hsum_Zfin
    _ ≤ ∑ z ∈ supp, ((coeff z : ℤ) : ℝ) := hsum_le_supp
    _ = ∑ᶠ u : ℂ, (((coeff u : ℤ) : ℝ)) := hsupp_eq_finsum
    _ = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) B)) u : ℤ) : ℝ) := by simp [coeff, Λ]


/-! ## Elementary real inequalities -/

/-- `log 2 ≤ 1`. -/
lemma grg_log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_two_lt_d9
  norm_num at h
  linarith

/-- `0 ≤ log N` for `N ≠ 0`. -/
lemma grg_logN_nonneg {N : ℕ} [NeZero N] : 0 ≤ Real.log (N : ℝ) := by
  have hN : 1 ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
  exact Real.log_nonneg hN

/-- `12·c·A·L < A·L²` provided `L ≥ 12c + 1`, `c ≥ 0`, `A > 0`. -/
lemma grg_poly_lt {c A L : ℝ} (hc0 : 0 ≤ c) (hA0 : 0 < A) (hLbig : 12 * c + 1 ≤ L) :
    12 * c * A * L < A * L ^ 2 := by
  have hLpos : 0 < L := by nlinarith
  have h1 : (12 * c + 1) * L ≤ L ^ 2 := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_right hLbig (le_of_lt hLpos))
  have hALpos : 0 < A * L := mul_pos hA0 hLpos
  have h2 : 12 * c * A * L < (12 * c + 1) * A * L := by nlinarith
  have h3 : (12 * c + 1) * A * L ≤ A * L ^ 2 := by
    have hA0le : 0 ≤ A := le_of_lt hA0
    have hm := mul_le_mul_of_nonneg_left h1 hA0le
    simpa [mul_assoc, mul_left_comm, mul_comm] using hm
  nlinarith

/-- `1/L² ≤ 1` for `L ≥ 1`. -/
lemma grg_one_div_sq_le_one {L : ℝ} (hL1 : 1 ≤ L) : (1 : ℝ) / L ^ 2 ≤ 1 := by
  have h1 : (1 : ℝ) ≤ L ^ 2 := by nlinarith
  exact div_le_one_of_le₀ h1 (sq_nonneg L)

/-- `log(2A + 4) ≤ log(A + 2) + 1` for `0 < A + 2`. -/
lemma grg_log_two_mul_add_four {A : ℝ} (hA : 0 < A) :
    Real.log (2 * A + 4) ≤ Real.log (A + 2) + 1 := by
  have hAp2 : 0 < A + 2 := by linarith
  have h2 : 0 < (2 : ℝ) := by norm_num
  calc
    Real.log (2 * A + 4) = Real.log (2 * (A + 2)) := by congr 1; ring
    _ ≤ Real.log (A + 2) + 1 := by
      rw [Real.log_mul h2.ne' hAp2.ne']
      nlinarith [grg_log_two_le_one]

/-- **`goodRadius_geometric`.**  For every sufficiently large `A` there is a radius
`T ∈ [A, 2A]` such that every zero `u` of the completed L-function satisfies
`(log (A+2) + log N + 2)² · |‖u‖ − T| ≥ 1`. -/
theorem goodRadius_geometric {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      ∃ T : ℝ, A ≤ T ∧ T ≤ 2 * A ∧
        ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 →
          (Real.log (A + 2) + Real.log (N : ℝ) + 2) ^ 2 * |‖u‖ - T| ≥ 1 := by
  classical
  rcases Commons.NumberTheory.Linnik.completedL_zeroCount χ hχ hχprim with ⟨c0, hc0⟩
  let c : ℝ := max c0 1
  have hc0le : c0 ≤ c := le_max_left c0 1
  have hcge1 : (1 : ℝ) ≤ c := le_max_right c0 1
  have hcge0 : 0 ≤ c := by linarith
  have hc_bound : ∀ R : ℝ, 2 ≤ R →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ)) ≤
        c * R * (Real.log (R + 2) + Real.log (N : ℝ) + 2) := by
    intro R hR
    have hR0 : 0 ≤ R := by linarith
    have hℓR0 : 0 ≤ Real.log (R + 2) + Real.log (N : ℝ) + 2 := by
      have h1 : 0 ≤ Real.log (R + 2) := by
        refine Real.log_nonneg ?_
        linarith
      have h2 : 0 ≤ Real.log (N : ℝ) := grg_logN_nonneg
      linarith
    exact le_trans (hc0 R hR) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc0le hR0) hℓR0)
  refine ⟨max 2 (Real.exp (12 * c + 10)), ?_, ?_⟩
  · have hpos2 : 0 < (2 : ℝ) := by norm_num
    exact lt_of_lt_of_le hpos2 (le_max_left _ _)
  · intro A hA₀le
    let L : ℝ := Real.log (A + 2) + Real.log (N : ℝ) + 2
    let B : ℝ := 2 * A + 2
    have hA2 : 2 ≤ A := by
      have : (2 : ℝ) ≤ max 2 (Real.exp (12 * c + 10)) := le_max_left _ _
      exact le_trans this hA₀le
    have hApos : 0 < A := by linarith
    have hLbig : 12 * c + 1 ≤ L := by
      dsimp [L]
      have h1 : Real.log (Real.exp (12 * c + 10)) ≤ Real.log (A + 2) := by
        refine Real.log_le_log ?_ ?_
        · positivity
        · calc
            Real.exp (12 * c + 10) ≤ max 2 (Real.exp (12 * c + 10)) := le_max_right _ _
            _ ≤ A := hA₀le
            _ ≤ A + 2 := by linarith
      rw [Real.log_exp] at h1
      have h2 : 0 ≤ Real.log (N : ℝ) := grg_logN_nonneg
      nlinarith
    have hLpos : 0 < L := by nlinarith
    have hL1 : 1 ≤ L := by nlinarith
    have hL2pos : 0 < L ^ 2 := sq_pos_of_pos hLpos
    have hB2 : 2 ≤ B := by dsimp [B]; nlinarith
    have hB0 : 0 ≤ B := by dsimp [B]; nlinarith
    have hB3 : B ≤ 3 * A := by dsimp [B]; nlinarith
    let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
    let Z : Set ℂ := {u : ℂ | Λ u = 0 ∧ ‖u‖ ≤ B}
    have hZfin : Z.Finite := by
      simpa [Z, Λ] using (grg_zeroSet_finite χ hχ hχprim (B := B) hB0)
    let Zfin : Finset ℂ := hZfin.toFinset
    let centres : Finset ℝ := Zfin.image (fun u : ℂ => ‖u‖)
    have hcentres_le : (centres.card : ℝ) ≤ (Zfin.card : ℝ) := by
      dsimp [centres]
      exact_mod_cast (Finset.card_image_le : (Zfin.image (fun u : ℂ => ‖u‖)).card ≤ Zfin.card)
    have hcardZ : (Zfin.card : ℝ) ≤
        ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) B)) u : ℤ) : ℝ) := by
      simpa [Zfin, Z, Λ] using (grg_zeroCard_le_divisorFinsum χ hχ hχprim (B := B) hB0 hZfin)
    let ℓB : ℝ := Real.log (B + 2) + Real.log (N : ℝ) + 2
    have hℓB0 : 0 ≤ ℓB := by
      dsimp [ℓB]
      have h1 : 0 ≤ Real.log (B + 2) := by
        refine Real.log_nonneg ?_
        dsimp [B]
        linarith
      have h2 : 0 ≤ Real.log (N : ℝ) := grg_logN_nonneg
      linarith
    have hℓB2 : ℓB ≤ 2 * L := by
      dsimp [ℓB, L]
      have hlogB : Real.log (B + 2) ≤ Real.log (A + 2) + 1 := by
        have hEq : B + 2 = 2 * A + 4 := by dsimp [B]; ring
        rw [hEq]
        exact grg_log_two_mul_add_four hApos
      have hlogAp2 : 0 ≤ Real.log (A + 2) := by
        refine Real.log_nonneg ?_
        linarith
      have hlogN0 : 0 ≤ Real.log (N : ℝ) := grg_logN_nonneg
      nlinarith
    have hmainAux : (centres.card : ℝ) * 2 < A * L ^ 2 := by
      have h1 : (centres.card : ℝ) ≤ c * B * ℓB := by
        calc
          (centres.card : ℝ) ≤ (Zfin.card : ℝ) := hcentres_le
          _ ≤ ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall (0 : ℂ) B)) u : ℤ) : ℝ) := hcardZ
          _ ≤ c * B * ℓB := by
            simpa [ℓB] using hc_bound B hB2
      calc
        (centres.card : ℝ) * 2 ≤ c * B * ℓB * 2 := by
          exact mul_le_mul_of_nonneg_right h1 (by norm_num)
        _ ≤ c * (3 * A) * (2 * L) * 2 := by
          gcongr
        _ = 12 * c * A * L := by ring
        _ < A * L ^ 2 := by
          exact grg_poly_lt hcge0 hApos hLbig
    have hcard' : (centres.card : ℝ) * (2 / L ^ 2) < A := by
      rw [← mul_div_assoc]
      rw [div_lt_iff₀ hL2pos]
      simpa [mul_assoc] using hmainAux
    have hcard'' : (centres.card : ℝ) * (2 / L ^ 2) < 2 * A - A := by
      nlinarith [hcard']
    have hw : 0 < 2 / L ^ 2 := by
      exact div_pos (by norm_num) hL2pos
    have hab : A ≤ 2 * A := by linarith
    rcases grg_exists_good_point_of_small_measure hab hw centres hcard'' with
      ⟨T, hT1, hT2, hgood⟩
    have hw2 : (2 / L ^ 2) / 2 = (1 : ℝ) / L ^ 2 := by
      have hLne : L ≠ 0 := ne_of_gt hLpos
      field_simp [hLne]
    have hgood' : ∀ z ∈ centres, (1 : ℝ) / L ^ 2 ≤ |T - z| := by
      intro z hz
      rw [← hw2]
      exact hgood z hz
    refine ⟨T, hT1, hT2, ?_⟩
    intro u hu0
    have hdist : (1 : ℝ) / L ^ 2 ≤ |‖u‖ - T| := by
      by_cases huB : ‖u‖ ≤ B
      · have hmem : ‖u‖ ∈ centres := by
          dsimp [centres]
          refine Finset.mem_image.mpr ?_
          refine ⟨u, ?_, rfl⟩
          dsimp [Zfin]
          exact (hZfin.mem_toFinset).2 ⟨by simpa [Λ] using hu0, huB⟩
        have hd := hgood' (‖u‖) hmem
        simpa [abs_sub_comm] using hd
      · have hBlt : B < ‖u‖ := lt_of_not_ge huB
        have hbig : (2 : ℝ) ≤ ‖u‖ - T := by
          have hBT : (2 : ℝ) ≤ B - T := by
            dsimp [B]
            nlinarith [hT2]
          have h1 : B - T < ‖u‖ - T := sub_lt_sub_right hBlt T
          linarith
        have hd2 : (1 : ℝ) / L ^ 2 ≤ 2 := by
          have hle1 : (1 : ℝ) / L ^ 2 ≤ 1 := grg_one_div_sq_le_one hL1
          linarith
        have hle : (1 : ℝ) / L ^ 2 ≤ ‖u‖ - T := le_trans hd2 hbig
        have hnn : 0 ≤ ‖u‖ - T := by linarith
        simpa [abs_of_nonneg hnn] using hle
    have hfin : L ^ 2 * |‖u‖ - T| ≥ 1 := by
      have h2 : 1 ≤ |‖u‖ - T| * L ^ 2 := (div_le_iff₀ hL2pos).mp hdist
      have h3 : (1 : ℝ) ≤ L ^ 2 * |‖u‖ - T| := by
        simpa [mul_comm] using h2
      linarith
    dsimp [L] at hfin ⊢
    exact hfin

end Commons.NumberTheory.Linnik
