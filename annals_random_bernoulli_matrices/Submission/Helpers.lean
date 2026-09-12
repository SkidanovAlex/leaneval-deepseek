/-
Copyright (c) 2025. Released under Apache 2.0 license.
Helper lemmas for `RandomBernoulliMatrices` (Tikhomirov, Annals of Math 191 (2) 2020).

This module contains only fully proved, elementary facts.  They connect the
three `sorry`-free statements of the challenge:  (1) the linear-algebra fact
that a singular square real matrix has smallest singular value zero (which is
the bridge from `corollary_1`/`corollary_2` to `theorem_A`), (2) measure
monotonicity used to pass from pointwise matrix facts to probabilities, and
(3) the elementary squeeze used to turn the uniform-in-`t` bound of
`theorem_A` into an equality of the form `(1 - p + o(1))^n`.
-/
import Mathlib
import ChallengeDeps

set_option autoImplicit false

namespace Submission.Helpers

noncomputable section

open Matrix MeasureTheory
open scoped Matrix

/-! ## Elementary squeeze

If `a ≤ b + C * t` for every `t > 0` and `C > 0`, then `a ≤ b`.
This is the analytic step that lets one pass from the `+ C * t` term of
`theorem_A` to the pure exponential bound at `t → 0`. -/

theorem le_of_forall_pos_le_mul_add {a b C : ℝ} (hC : 0 < C)
    (h : ∀ t : ℝ, 0 < t → a ≤ b + C * t) : a ≤ b := by
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have ht : 0 < ε / C := div_pos hε hC
  have h' := h (ε / C) ht
  -- a ≤ b + C * (ε / C) = b + ε
  calc
    a ≤ b + C * (ε / C) := h'
    _ = b + ε := by field_simp [hC.ne']

/-! ## Singular matrices have zero smallest singular value

For a square real matrix `M`, `M.det = 0` iff the linear map
`M.toEuclideanLin` has a nonzero kernel vector; normalising such a vector
gives a unit vector in the kernel, so the infimum defining `σ_min M` is at
most `0`, while norms are non-negative, so it is `0`. -/

/-- A singular square real matrix has a unit vector in its kernel. -/
theorem exists_unit_vector_mulVec_eq_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (h : M.det = 0) :
    ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 ∧ M.toEuclideanLin v = 0 := by
  have h1 : ∃ w : Fin n → ℝ, w ≠ 0 ∧ M *ᵥ w = 0 :=
    (Matrix.exists_mulVec_eq_zero_iff).mpr h
  rcases h1 with ⟨w, hw, hMw⟩
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 w
  have hv0 : v ≠ 0 := by
    intro hv
    apply hw
    have hEq : (WithLp.equiv 2 (Fin n → ℝ)) v = w := by simp [v]
    have hzero : (WithLp.equiv 2 (Fin n → ℝ)) (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
      simp
    simpa [hzero, hv] using hEq.symm
  have hMv : M.toEuclideanLin v = 0 := by
    dsimp [v]
    simpa [hMw] using (Matrix.toEuclideanLin_apply_piLp_toLp M w)
  refine ⟨(‖v‖)⁻¹ • v, ?_, ?_⟩
  · calc
      ‖(‖v‖)⁻¹ • v‖ = ‖(‖v‖)⁻¹‖ * ‖v‖ := by rw [norm_smul]
      _ = (‖v‖)⁻¹ * ‖v‖ := by
            congr 1
            exact Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v))
      _ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)
  · rw [map_smul]
    simp [hMv]

/-- A singular square real matrix has smallest singular value equal to zero. -/
theorem sigma_min_eq_zero_of_det_eq_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (h : M.det = 0) : RandomBernoulliMatrices.σ_min M = 0 := by
  rcases exists_unit_vector_mulVec_eq_zero M h with ⟨v, hvnorm, hMv⟩
  unfold RandomBernoulliMatrices.σ_min
  let f : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1} → ℝ :=
    fun x => ‖M.toEuclideanLin x.1‖
  have hvmem : f ⟨v, hvnorm⟩ = 0 := by simp [f, hMv]
  have hbdd : BddBelow (Set.range f) := by
    refine ⟨0, ?_⟩
    rintro y ⟨x, rfl⟩
    exact norm_nonneg _
  apply le_antisymm
  · -- σ_min ≤ 0
    calc
      (⨅ x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}, ‖M.toEuclideanLin x.1‖)
          ≤ f ⟨v, hvnorm⟩ := ciInf_le hbdd ⟨v, hvnorm⟩
      _ = 0 := hvmem
  · -- 0 ≤ σ_min
    haveI : Nonempty {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1} := ⟨⟨v, hvnorm⟩⟩
    exact le_ciInf (fun x => norm_nonneg (M.toEuclideanLin x.1))

/-- If a matrix is singular then its smallest singular value is at most any
non-negative number `u`. -/
theorem sigma_min_le_of_det_eq_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    {u : ℝ} (hu : 0 ≤ u) (h : M.det = 0) : RandomBernoulliMatrices.σ_min M ≤ u := by
  simpa [sigma_min_eq_zero_of_det_eq_zero M h] using hu

/-! ## Measure bridge

If a pointwise matrix event implies a `σ_min` small-ball event, the same
inequality holds for the real parts of any finite measure. -/

theorem measureReal_le_of_subset {α : Type*} [MeasurableSpace α] {P : Measure α}
    {s t : Set α} (h : s ⊆ t) (ht : P t ≠ ⊤) : P.real s ≤ P.real t :=
  MeasureTheory.measureReal_mono h ht

/-- `P(ω | (B ω).det = 0) ≤ P(ω | σ_min (B ω) ≤ u)` for `0 ≤ u`, for any
finite measure `P`. -/
theorem singular_prob_le_smallBall {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {n : ℕ} (B : Ω → Matrix (Fin n) (Fin n) ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hP : P Set.univ ≠ ⊤) :
    P.real {ω : Ω | (B ω).det = 0} ≤
      P.real {ω : Ω | RandomBernoulliMatrices.σ_min (B ω) ≤ u} := by
  refine measureReal_le_of_subset ?_ ?_
  · intro ω hω
    exact sigma_min_le_of_det_eq_zero (B ω) hu hω
  · -- outer measure of the big set is finite since P univ is finite
    exact lt_top_iff_ne_top.mp (lt_of_le_of_lt (MeasureTheory.measure_mono (Set.subset_univ _))
      (lt_top_iff_ne_top.mpr hP))

end


/-! ## Counting: binomial partial sums

The first analytic estimate of Tikhomirov's Preliminaries (2020): the sum of
the binomial coefficients `∑_{ℓ ≤ r} C(m,ℓ)` is at most `(e·m/r)^r`.  It is the
counting engine of the tensorization lemma (Lemma 2.2) and of the ε-net
cardinality bounds used for compressible vectors. -/

theorem sum_choose_le_exp {m r : ℕ} (hr : 0 < r) (hrm : r ≤ m) :
    (∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ)) ≤
      (Real.exp 1 * (m : ℝ) / (r : ℝ)) ^ r := by
  let q : ℝ := (r : ℝ) / (m : ℝ)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le hr hrm)
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hrpos
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (le_of_lt hrpos) (le_of_lt hmpos)
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact div_le_one_of_le₀ (by exact_mod_cast hrm) (le_of_lt hmpos)
  have hqpos : 0 < q := by
    dsimp [q]
    exact div_pos hrpos hmpos
  have hA1 : ∀ ℓ ∈ Finset.range (r + 1),
      (m.choose ℓ : ℝ) * q ^ r ≤ (m.choose ℓ : ℝ) * q ^ ℓ := by
    intro ℓ hℓ
    have hℓr : ℓ ≤ r := by simpa using (Finset.mem_range.mp hℓ)
    have hpow : q ^ (r - ℓ) ≤ 1 := pow_le_one₀ hq0 hq1
    have hc0 : 0 ≤ (m.choose ℓ : ℝ) := by exact_mod_cast (Nat.zero_le _)
    calc
      (m.choose ℓ : ℝ) * q ^ r = (m.choose ℓ : ℝ) * (q ^ (r - ℓ) * q ^ ℓ) := by
        congr 1
        rw [← pow_add, Nat.sub_add_cancel hℓr]
      _ ≤ (m.choose ℓ : ℝ) * (1 * q ^ ℓ) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow (pow_nonneg hq0 ℓ)) hc0
      _ = (m.choose ℓ : ℝ) * q ^ ℓ := by ring
  have hS_le : (∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ)) * q ^ r ≤ (1 + q) ^ m := by
    calc
      (∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ)) * q ^ r
          = ∑ ℓ ∈ Finset.range (r + 1), ((m.choose ℓ : ℝ) * q ^ r) := by
            rw [Finset.sum_mul]
      _ ≤ ∑ ℓ ∈ Finset.range (r + 1), ((m.choose ℓ : ℝ) * q ^ ℓ) := by
            exact Finset.sum_le_sum hA1
      _ ≤ ∑ ℓ ∈ Finset.range (m + 1), ((m.choose ℓ : ℝ) * q ^ ℓ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?subset ?nonneg
            · intro x hx
              exact Finset.mem_range.mpr (lt_of_le_of_lt (by simpa using (Finset.mem_range.mp hx)) (by omega))
            · intro x hx hnot
              exact mul_nonneg (by exact_mod_cast (Nat.zero_le _)) (pow_nonneg hq0 _)
      _ = (1 + q) ^ m := by
            have hbin : (q + 1) ^ m =
                ∑ ℓ ∈ Finset.range (m + 1), ((m.choose ℓ : ℝ) * q ^ ℓ) := by
              rw [add_pow q (1 : ℝ) m]
              simp [mul_comm]
            rw [← hbin]
            congr 1
            rw [add_comm]
  have h_one : (1 + q) ^ m ≤ Real.exp (r : ℝ) := by
    have hle1 : 1 + (r : ℝ) / (m : ℝ) ≤ Real.exp ((r : ℝ) / (m : ℝ)) := by
      simpa [add_comm] using (Real.add_one_le_exp ((r : ℝ) / (m : ℝ)))
    have hp := pow_le_pow_left₀ (by positivity) hle1 m
    calc
      (1 + (r : ℝ) / (m : ℝ)) ^ m ≤ Real.exp ((r : ℝ) / (m : ℝ)) ^ m := hp
      _ = Real.exp ((m : ℝ) * ((r : ℝ) / (m : ℝ))) := by
            rw [Real.exp_nat_mul]
      _ = Real.exp (r : ℝ) := by
            field_simp [hm0]
  have hS : (∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ)) * q ^ r ≤ Real.exp (r : ℝ) :=
    le_trans hS_le h_one
  have hqpow_mul : q ^ r * ((m : ℝ) / (r : ℝ)) ^ r = 1 := by
    rw [← mul_pow]
    dsimp [q]
    field_simp [hm0, hr0]
    simp
  have hmr0 : 0 ≤ ((m : ℝ) / (r : ℝ)) ^ r := by
    exact pow_nonneg (div_nonneg (by exact_mod_cast (Nat.zero_le m)) (le_of_lt hrpos)) r
  have hS2 : (∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ)) ≤
      Real.exp (r : ℝ) * ((m : ℝ) / (r : ℝ)) ^ r := by
    have htmp := mul_le_mul_of_nonneg_right hS hmr0
    have htmp' : (∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ)) *
        (q ^ r * ((m : ℝ) / (r : ℝ)) ^ r) ≤
        Real.exp (r : ℝ) * ((m : ℝ) / (r : ℝ)) ^ r := by
      simpa [mul_assoc] using htmp
    rwa [hqpow_mul, mul_one] at htmp'
  calc
    (∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ))
        ≤ Real.exp (r : ℝ) * ((m : ℝ) / (r : ℝ)) ^ r := hS2
    _ = (Real.exp 1 * (m : ℝ) / (r : ℝ)) ^ r := by
      have hexp : Real.exp (r : ℝ) = (Real.exp 1) ^ r := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
      rw [hexp, ← mul_pow]
      congr 1
      ring

/-! ## Ball inclusion: few large coordinates

The elementary counting step of the tensorization lemma (Tikhomirov 2020,
Lemma 2.2(2)): a vector whose `ℓ₂` norm is at most `η·√r` has at most `r`
coordinates of absolute value larger than `η`.  Equivalent statement: if the
sum of squares is at most `η²·r` then at most `r` coordinates exceed `η`. -/

theorem card_big_le_of_sum_sq_le {m r : ℕ} (v : Fin m → ℝ) {η : ℝ} (hη0 : 0 ≤ η)
    (h : (∑ i : Fin m, (v i) ^ 2) ≤ η ^ 2 * (r : ℝ)) :
    ((Finset.univ : Finset (Fin m)).filter (fun i : Fin m => η < |v i|)).card ≤ r := by
  classical
  let B : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => η < |v i|)
  by_cases hz : η = 0
  · have hle0 : (∑ i : Fin m, (v i) ^ 2) ≤ 0 := by simpa [hz] using h
    have hge0 : 0 ≤ ∑ i : Fin m, (v i) ^ 2 := Finset.sum_nonneg (fun i hi => sq_nonneg (v i))
    have hsum0 : (∑ i : Fin m, (v i) ^ 2) = 0 := le_antisymm hle0 hge0
    have hv : ∀ i : Fin m, v i = 0 := by
      intro i
      have hterm : (v i) ^ 2 ≤ ∑ j : Fin m, (v j) ^ 2 :=
        Finset.single_le_sum (fun j hj => sq_nonneg (v j)) (Finset.mem_univ i)
      have hle : (v i) ^ 2 ≤ 0 := le_trans hterm (le_of_eq hsum0)
      have hsq : (v i) ^ 2 = 0 := le_antisymm hle (sq_nonneg (v i))
      exact sq_eq_zero_iff.mp hsq
    have hB : B = ∅ := by
      ext i
      simp [B, hz, hv i]
    change B.card ≤ r
    rw [hB]
    simp
  · have hηpos : 0 < η := lt_of_le_of_ne hη0 (Ne.symm hz)
    have hη2pos : 0 < η ^ 2 := sq_pos_of_pos hηpos
    by_contra hnot
    have hrlt : r < B.card := Nat.lt_of_not_ge hnot
    have hsub : (∑ i ∈ B, (v i) ^ 2) ≤ η ^ 2 * (r : ℝ) := by
      refine le_trans ?_ h
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
        (fun i hi hiu => sq_nonneg (v i))
    have hterm : ∀ i : Fin m, i ∈ B → η ^ 2 ≤ (v i) ^ 2 := by
      intro i hi
      have hiη : η < |v i| := by simpa [B] using (Finset.mem_filter.mp hi).2
      have hlt : η ^ 2 < (v i) ^ 2 := by
        rw [← sq_abs (v i)]
        exact sq_lt_sq.mpr (by simpa [abs_of_nonneg hη0] using hiη)
      exact le_of_lt hlt
    have hlow : (∑ i ∈ B, η ^ 2) ≤ ∑ i ∈ B, (v i) ^ 2 := Finset.sum_le_sum hterm
    have hlowR : (B.card : ℝ) * η ^ 2 ≤ ∑ i ∈ B, (v i) ^ 2 := by
      calc
        (B.card : ℝ) * η ^ 2 = ∑ i ∈ B, η ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ i ∈ B, (v i) ^ 2 := hlow
    have hBbig : (B.card : ℝ) * η ^ 2 ≤ η ^ 2 * (r : ℝ) := le_trans hlowR hsub
    have hcardR : (r : ℝ) < (B.card : ℝ) := by exact_mod_cast hrlt
    have hdiff_le : η ^ 2 * ((B.card : ℝ) - (r : ℝ)) ≤ 0 := by nlinarith [hBbig]
    have hdiff_pos : 0 < η ^ 2 * ((B.card : ℝ) - (r : ℝ)) := by
      exact mul_pos hη2pos (by nlinarith [hcardR])
    nlinarith

/-- Euclidean-space version of `card_big_le_of_sum_sq_le`: if `‖v‖² ≤ η²·r`
(`η ≥ 0`), then at most `r` coordinates of `v` exceed `η` in absolute value. -/
theorem card_big_le_of_norm_sq_le {m r : ℕ} (v : EuclideanSpace ℝ (Fin m)) {η : ℝ}
    (hη0 : 0 ≤ η) (h : ‖v‖ ^ 2 ≤ η ^ 2 * (r : ℝ)) :
    ((Finset.univ : Finset (Fin m)).filter (fun i : Fin m => η < |v i|)).card ≤ r := by
  have hv : (∑ i : Fin m, (v i) ^ 2) ≤ η ^ 2 * (r : ℝ) := by
    simpa [EuclideanSpace.real_norm_sq_eq v] using h
  exact card_big_le_of_sum_sq_le (fun i : Fin m => v i) hη0 hv

/-! ## Lévy concentration function and compressible vectors

Definitions from the Preliminaries of Tikhomirov (2020).  The Lévy concentration
function `cf(ξ,t) = sup_λ P{|ξ−λ| ≤ t}` is needed for the Littlewood–Offord
estimates; the sets of compressible/incompressible unit vectors give the
standard decomposition of the unit sphere used in the proof of Theorem A. -/

open scoped ENNReal

/-- The Lévy concentration function of a real random variable `ξ` (with respect
to a measure `P`) at scale `t`:  `cf(ξ,t) = sup_{l ∈ ℝ} P{|ξ−l| ≤ t}`. -/
noncomputable def levyConcentration {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (ξ : Ω → ℝ) (t : ℝ) : ℝ≥0∞ :=
  sSup {a : ℝ≥0∞ | ∃ l : ℝ, a = P {x | |ξ x - l| ≤ t}}

/-- For every `l`, the interval mass is a lower bound for the supremum. -/
theorem le_levyConcentration {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (ξ : Ω → ℝ) (t l : ℝ) :
    P {x | |ξ x - l| ≤ t} ≤ levyConcentration P ξ t := by
  unfold levyConcentration
  exact le_sSup ⟨l, rfl⟩

/-- The concentration function is monotone in the scale `t`. -/
theorem levyConcentration_mono {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (ξ : Ω → ℝ) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    levyConcentration P ξ t₁ ≤ levyConcentration P ξ t₂ := by
  unfold levyConcentration
  rw [sSup_le_iff]
  rintro b ⟨l, rfl⟩
  have hsub : {x | |ξ x - l| ≤ t₁} ⊆ {x | |ξ x - l| ≤ t₂} := by
    intro x hx
    exact le_trans hx ht
  exact le_trans (MeasureTheory.measure_mono hsub) (le_levyConcentration P ξ t₂ l)

/-- If `P` is a probability measure, the concentration function never exceeds `1`. -/
theorem levyConcentration_le_one {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (ξ : Ω → ℝ) (t : ℝ) [MeasureTheory.IsProbabilityMeasure P] :
    levyConcentration P ξ t ≤ 1 := by
  unfold levyConcentration
  rw [sSup_le_iff]
  rintro b ⟨l, rfl⟩
  have hsub : {x | |ξ x - l| ≤ t} ⊆ Set.univ := Set.subset_univ _
  have huniv : P Set.univ = 1 := MeasureTheory.measure_univ
  exact le_trans (MeasureTheory.measure_mono hsub) (le_of_eq huniv)

/-- The number of nonzero coordinates of a vector in `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def supportCard {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℕ :=
  by classical exact ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => x i ≠ 0)).card

/-- A unit vector is `(δ,ν)`-compressible if it lies within Euclidean distance
`ν` of a vector supported on at most `δ·n` coordinates. -/
noncomputable def compressible {n : ℕ} (δ ν : ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ‖x‖ = 1 ∧ ∃ y : EuclideanSpace ℝ (Fin n),
    ‖x - y‖ ≤ ν ∧ (supportCard y : ℝ) ≤ δ * (n : ℝ)

/-- A unit vector is `(δ,ν)`-incompressible if it is not `(δ,ν)`-compressible. -/
noncomputable def incompressible {n : ℕ} (δ ν : ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ‖x‖ = 1 ∧ ¬ compressible δ ν x

/-! ## The tensorization event inclusion

The small-ball event `{x | Σᵢ (ξᵢ x)² ≤ η²·r}` is contained in the union over all index
subsets `B` with `|B| ≤ r` of the events `{x | ∀ i ∉ B, |ξᵢ x| ≤ η}`:  indeed for a point in
the small ball, the set of "big" coordinates (those with `|ξᵢ| > η`) has size at most `r`
(by `card_big_le_of_sum_sq_le`), and outside that set all coordinates are small.  This is the
set-level heart of the union bound in the tensorization lemma. -/

/-- The set of indices where `|ξᵢ x| > η`. -/
noncomputable def bigCoords {m : ℕ} {Ω : Type*} (ξ : Fin m → Ω → ℝ) (η : ℝ) (x : Ω) :
    Finset (Fin m) :=
  (Finset.univ.filter (fun i : Fin m => η < |ξ i x|))

/-- Small-ball implies "few big coordinates", hence membership in one of the union events. -/
theorem smallBall_subset_union_bigCoords {m r : ℕ} {Ω : Type*} (ξ : Fin m → Ω → ℝ)
    {η : ℝ} (hη0 : 0 ≤ η) :
    {x : Ω | (∑ i : Fin m, (ξ i x) ^ 2) ≤ η ^ 2 * (r : ℝ)}
      ⊆ ⋃ B : {B : Finset (Fin m) // B.card ≤ r},
          {x : Ω | ∀ i : Fin m, i ∉ (B : Finset (Fin m)) → |ξ i x| ≤ η} := by
  intro x hx
  let B : Finset (Fin m) := bigCoords ξ η x
  have hcard : B.card ≤ r := card_big_le_of_sum_sq_le (fun i : Fin m => ξ i x) hη0 hx
  refine Set.mem_iUnion.mpr ⟨⟨B, hcard⟩, ?_⟩
  intro i hiB
  have hnot : ¬ η < |ξ i x| := by
    intro hbig
    have hmemB : i ∈ B := by simp [B, bigCoords, hbig]
    have hnotB : ¬ i ∈ B := by simpa using hiB
    exact hnotB hmemB
  exact le_of_not_gt hnot

/-! ## HasLaw bridge

If a random variable `X : Ω → ℝ` has law `μ` under `P` (`HasLaw X μ P`), then
`P.real {x | X x ∈ s} = μ.real s` for measurable sets `s`.  This is the tool that
converts hypotheses about the joint law of the entries of a Bernoulli matrix into
numerical probability statements about single entries. -/

open MeasureTheory ProbabilityTheory

/-- `P.real` mass of the preimage of a measurable set equals the law's real mass. -/
theorem hasLaw_measureReal_preimage {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}
    {μ : Measure ℝ} (P : Measure Ω) (h : HasLaw X μ P) (hmeas : Measurable X)
    {s : Set ℝ} (hs : MeasurableSet s) : P.real {x : Ω | X x ∈ s} = μ.real s := by
  rw [Measure.real_def, Measure.real_def]
  congr 1
  have hset : {x : Ω | X x ∈ s} = X ⁻¹' s := by rfl
  calc
    P {x : Ω | X x ∈ s} = P (X ⁻¹' s) := by rw [hset]
    _ = (Measure.map X P) s := by rw [Measure.map_apply hmeas hs]
    _ = μ s := by rw [h.map_eq]

/-- The interval `{x | |x − a| ≤ t}` is measurable, for the Bernoulli bridges below. -/
theorem measurableSet_abs_le (a t : ℝ) : MeasurableSet {x : ℝ | |x - a| ≤ t} := by
  have h : {x : ℝ | |x - a| ≤ t} = Set.Icc (a - t) (a + t) := by
    ext x
    constructor <;> intro hx
    · rw [Set.mem_Icc]
      change |x - a| ≤ t at hx
      rw [abs_le] at hx
      constructor <;> nlinarith
    · rw [Set.mem_Icc] at hx
      change |x - a| ≤ t
      rw [abs_le]
      constructor <;> nlinarith
  rw [h]
  exact measurableSet_Icc

end Submission.Helpers