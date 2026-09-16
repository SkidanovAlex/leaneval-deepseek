import Mathlib
import Submission.Lemma41

open scoped BigOperators Topology FourierTransform SchwartzMap
open Filter MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# The `k`-fold factorization of the divisor sum

P8 (36) for `k` coordinates factorizes over the coordinates, because the
coprimality condition `([d_j,d′_j], WN) = 1` is imposed pair by pair.  This
module records the two structural lemmas:

* `tsum_prod_pi` — `Σ'_{d : Fin k → ι} ∏_j f_j(d_j) = ∏_j Σ'_{x} f_j x` for
  absolutely summable `f_j`;
* `summable_norm_prod_pi` — the corresponding absolute summability.

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The equivalence `(Fin (k+1) → ι) ≃ ι × (Fin k → ι)` (head and tail). -/
def piFinSuccEquiv (k : ℕ) (ι : Type*) : (Fin (k+1) → ι) ≃ ι × (Fin k → ι) where
  toFun d := (d 0, fun j => d j.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv d := by
    funext j
    refine Fin.cases ?_ ?_ j
    · simp [Fin.cons_zero]
    · intro i; simp [Fin.cons_succ]
  right_inv p := by
    ext j
    · simp [Fin.cons_zero]
    · simp [Fin.cons_succ]

/-- The product family over `Fin k → ι` is absolutely summable when each factor
family is. -/
theorem summable_norm_prod_pi {ι : Type*} :
    ∀ (k : ℕ) (f : Fin k → ι → ℂ), (∀ j, Summable fun x => ‖f j x‖) →
      Summable fun d : Fin k → ι => ‖∏ j, f j (d j)‖
  | 0, f, _ => by
      have h : (fun d : Fin 0 → ι => ‖∏ j, f j (d j)‖) = fun _ => (1 : ℝ) := by
        funext d; rw [Fin.prod_univ_zero]; norm_num
      rw [h]
      exact Summable.of_finite
  | k+1, f, hf => by
      have hrec : Summable (fun e : Fin k → ι => ‖∏ j : Fin k, f j.succ (e j)‖) :=
        summable_norm_prod_pi k (fun j : Fin k => f j.succ) (fun j : Fin k => hf j.succ)
      have h1 : Summable (fun p : ι × (Fin k → ι) =>
          ‖f 0 p.1 * ∏ j : Fin k, f j.succ (p.2 j)‖) :=
        Summable.mul_norm (f := fun x : ι => f 0 x)
          (g := fun e : Fin k → ι => ∏ j : Fin k, f j.succ (e j)) (hf 0) hrec
      have h3 : (fun d : Fin (k+1) → ι => ‖∏ j, f j (d j)‖) =
          fun d => ‖f 0 (d 0) * ∏ j : Fin k, f j.succ (d j.succ)‖ := by
        funext d; rw [Fin.prod_univ_succ]
      have h4 : (fun d : Fin (k+1) → ι => ‖f 0 (d 0) * ∏ j : Fin k, f j.succ (d j.succ)‖) =
          (fun p : ι × (Fin k → ι) => ‖f 0 p.1 * ∏ j : Fin k, f j.succ (p.2 j)‖) ∘
            (piFinSuccEquiv k ι) := by
        funext d; simp [piFinSuccEquiv, Function.comp]
      rw [h3, h4]
      exact (Equiv.summable_iff (piFinSuccEquiv k ι)
        (f := fun p : ι × (Fin k → ι) => ‖f 0 p.1 * ∏ j : Fin k, f j.succ (p.2 j)‖)).2 h1

/-- **Factorization of a `tsum` over a function type.** -/
theorem tsum_prod_pi {ι : Type*} :
    ∀ (k : ℕ) (f : Fin k → ι → ℂ), (∀ j, Summable fun x => ‖f j x‖) →
      (∑' d : Fin k → ι, ∏ j, f j (d j)) = ∏ j, ∑' x, f j x
  | 0, f, _ => by
      rw [Fin.prod_univ_zero]
      rw [show (fun d : Fin 0 → ι => ∏ j, f j (d j)) = fun _ => (1 : ℂ) from by
        funext d; rw [Fin.prod_univ_zero]]
      haveI : Unique (Fin 0 → ι) :=
        ⟨⟨fun i => Fin.elim0 i⟩, fun a => by funext i; exact Fin.elim0 i⟩
      simp
  | k+1, f, hf => by
      have hrec : Summable (fun e : Fin k → ι => ‖∏ j : Fin k, f j.succ (e j)‖) :=
        summable_norm_prod_pi k (fun j : Fin k => f j.succ) (fun j : Fin k => hf j.succ)
      have hstep : (∑' d : Fin (k+1) → ι, ∏ j, f j (d j)) =
          ∑' p : ι × (Fin k → ι), f 0 p.1 * ∏ j : Fin k, f j.succ (p.2 j) := by
        rw [show (∑' d : Fin (k+1) → ι, ∏ j, f j (d j)) =
            ∑' d : Fin (k+1) → ι, f 0 (d 0) * ∏ j : Fin k, f j.succ (d j.succ) from
          tsum_congr (fun d => by rw [Fin.prod_univ_succ])]
        exact Equiv.tsum_eq (piFinSuccEquiv k ι)
          (fun p : ι × (Fin k → ι) => f 0 p.1 * ∏ j : Fin k, f j.succ (p.2 j))
      rw [hstep, ← tsum_mul_tsum_of_summable_norm (hf 0) hrec]
      rw [tsum_prod_pi k (fun j : Fin k => f j.succ) (fun j : Fin k => hf j.succ)]
      rw [Fin.prod_univ_succ]


/-! ## Summability of the raw divisor weights of one coordinate -/

/-- A continuous compactly supported real function is bounded. -/
lemma exists_abs_bound_of_hasCompactSupport (F : ℝ → ℝ) (hcs : HasCompactSupport F)
    (hcont : Continuous F) : ∃ C, 0 ≤ C ∧ ∀ t, |F t| ≤ C := by
  have hcomp : IsCompact (tsupport F) := hcs
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ tsupport F
  · have h := hC t ht
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport ht]
    simp

/-- `l1Cut` is nonnegative. -/
lemma l1Cut_nonneg (F : ℝ → ℝ) : 0 ≤ l1Cut F := integral_nonneg (fun _ => norm_nonneg _)

/-- The majorant is nonnegative. -/
lemma kernelMajorant_nonneg (q R : ℕ) (d : ℕ × ℕ) : 0 ≤ kernelMajorant q R d := by
  rw [kernelMajorant]
  positivity

/-- The divisor phase at the value `0` is `1`. -/
lemma divisorPhase_zero (R : ℕ) (ξ : ℝ) : divisorPhase R 0 ξ = 1 := by
  unfold divisorPhase logR
  simp

/-- The absolute value of one coordinate's Fourier expansion is bounded by the
`cpow` majorant times `l1Cut`. -/
lemma norm_coordForm_le (R : ℕ) (hR : 1 < R) {d : ℕ} (hd : d ≠ 0) (F : ℝ → ℝ)
    (hcs : HasCompactSupport F) (hsm : ContDiff ℝ (↑(⊤ : ℕ∞)) F) :
    ‖(F (logR d R) : ℂ)‖ ≤ (d : ℝ) ^ (-(1 / Real.log (R : ℝ))) * l1Cut F := by
  rw [divisorForm_fourierCut F hcs hsm R d]
  calc ‖∫ ξ : ℝ, divisorPhase R d ξ * fourierCut F ξ‖
      ≤ ∫ ξ : ℝ, ‖divisorPhase R d ξ * fourierCut F ξ‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ ξ : ℝ, (d : ℝ) ^ (-(1 / Real.log (R : ℝ))) * ‖fourierCut F ξ‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
        show ‖divisorPhase R d ξ * fourierCut F ξ‖ =
          (d : ℝ) ^ (-(1 / Real.log (R : ℝ))) * ‖fourierCut F ξ‖
        rw [norm_mul, norm_divisorPhase hR hd ξ]
    _ = (d : ℝ) ^ (-(1 / Real.log (R : ℝ))) * l1Cut F := by
        rw [integral_const_mul]
        rfl

/-- The absolute value of one divisor weight factor is bounded by the majorant. -/
lemma norm_coordWeight_le (q R : ℕ) (hR : 1 < R) (F G : ℝ → ℝ)
    (hcsF : HasCompactSupport F) (hsmF : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (hcsG : HasCompactSupport G) (hsmG : ContDiff ℝ (↑(⊤ : ℕ∞)) G) (d : ℕ × ℕ) :
    ‖mobiusLcmWeight q d.1 d.2 * (F (logR d.1 R) : ℂ) * (G (logR d.2 R) : ℂ)‖ ≤
      kernelMajorant q R d * (l1Cut F * l1Cut G) := by
  by_cases h1 : d.1 = 0
  · rw [h1, mobiusLcmWeight_zero_fst]
    simp only [zero_mul, norm_zero]
    exact mul_nonneg (kernelMajorant_nonneg q R _) (mul_nonneg (l1Cut_nonneg F) (l1Cut_nonneg G))
  · by_cases h2 : d.2 = 0
    · rw [h2, mobiusLcmWeight_zero_snd]
      simp only [zero_mul, norm_zero]
      exact mul_nonneg (kernelMajorant_nonneg q R _) (mul_nonneg (l1Cut_nonneg F) (l1Cut_nonneg G))
    · rw [norm_mul, norm_mul, kernelMajorant]
      have hFbd := norm_coordForm_le R hR h1 F hcsF hsmF
      have hGbd := norm_coordForm_le R hR h2 G hcsG hsmG
      have hw0 : (0 : ℝ) ≤ ‖mobiusLcmWeight q d.1 d.2‖ := norm_nonneg _
      have hstep1 : ‖mobiusLcmWeight q d.1 d.2‖ * ‖(F (logR d.1 R) : ℂ)‖ ≤
          ‖mobiusLcmWeight q d.1 d.2‖ *
            ((d.1 : ℝ) ^ (-(1 / Real.log (R : ℝ))) * l1Cut F) :=
        mul_le_mul_of_nonneg_left hFbd hw0
      have hstep2 : ‖mobiusLcmWeight q d.1 d.2‖ * ‖(F (logR d.1 R) : ℂ)‖ *
            ‖(G (logR d.2 R) : ℂ)‖ ≤
          ‖mobiusLcmWeight q d.1 d.2‖ *
            ((d.1 : ℝ) ^ (-(1 / Real.log (R : ℝ))) * l1Cut F) *
            ((d.2 : ℝ) ^ (-(1 / Real.log (R : ℝ))) * l1Cut G) :=
        mul_le_mul hstep1 hGbd (norm_nonneg _)
          (mul_nonneg hw0 (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (l1Cut_nonneg F)))
      refine hstep2.trans (le_of_eq ?_)
      ring

/-- The raw divisor-weight family of one coordinate is absolutely summable. -/
lemma summable_norm_coordWeight (q R : ℕ) (hq : q ≠ 0) (hR : 1 < R) (F G : ℝ → ℝ)
    (hcsF : HasCompactSupport F) (hsmF : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (hcsG : HasCompactSupport G) (hsmG : ContDiff ℝ (↑(⊤ : ℕ∞)) G) :
    Summable (fun d : ℕ × ℕ =>
      ‖mobiusLcmWeight q d.1 d.2 * (F (logR d.1 R) : ℂ) * (G (logR d.2 R) : ℂ)‖) := by
  have hL1F : 0 ≤ l1Cut F := l1Cut_nonneg F
  have hL1G : 0 ≤ l1Cut G := l1Cut_nonneg G
  refine Summable.of_nonneg_of_le (fun d => norm_nonneg _) (fun d => ?_)
    ((summable_kernelMajorant q R hq hR).mul_right (l1Cut F * l1Cut G))
  exact norm_coordWeight_le q R hR F G hcsF hsmF hcsG hsmG d


/-! ## The telescoping product bound -/

/-- Bound for the norm of a finite product. -/
lemma norm_finset_prod_le_pow {ι : Type*} (t : Finset ι) (b : ι → ℂ) (A : ℝ)
    (hb : ∀ j ∈ t, ‖b j‖ ≤ A) : ‖∏ j ∈ t, b j‖ ≤ A ^ t.card := by
  rw [norm_prod]
  calc ∏ j ∈ t, ‖b j‖ ≤ ∏ _j ∈ t, A :=
        Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j hj => hb j hj)
    _ = A ^ t.card := Finset.prod_const _

/-- **Telescoping bound for products**: `‖∏ a_j − ∏ b_j‖` is at most the sum
of the deviations multiplied by `A^{|s|−1}`, provided both families are bounded
by `A`. -/
lemma norm_prod_sub_prod_finset {ι : Type*} (s : Finset ι) (a b : ι → ℂ) (A : ℝ)
    (ha : ∀ j ∈ s, ‖a j‖ ≤ A) (hb : ∀ j ∈ s, ‖b j‖ ≤ A) :
    ‖∏ j ∈ s, a j - ∏ j ∈ s, b j‖ ≤ (∑ j ∈ s, ‖a j - b j‖) * A ^ (s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
      have hat : ∀ j ∈ t, ‖a j‖ ≤ A := fun j hj => ha j (Finset.mem_insert_of_mem hj)
      have hbt : ∀ j ∈ t, ‖b j‖ ≤ A := fun j hj => hb j (Finset.mem_insert_of_mem hj)
      have hai : ‖a i‖ ≤ A := ha i (Finset.mem_insert_self i t)
      have hih := ih hat hbt
      have hprodb := norm_finset_prod_le_pow t b A hbt
      -- decompose the difference
      have hdecomp : a i * ∏ j ∈ t, a j - b i * ∏ j ∈ t, b j =
          a i * (∏ j ∈ t, a j - ∏ j ∈ t, b j) + (a i - b i) * ∏ j ∈ t, b j := by ring
      rw [hdecomp]
      have hsum0 : (0 : ℝ) ≤ ∑ j ∈ t, ‖a j - b j‖ :=
        Finset.sum_nonneg (fun j _ => norm_nonneg _)
      have hA0 : 0 ≤ A := le_trans (norm_nonneg _) hai
      -- first piece
      have hb1 : ‖a i * (∏ j ∈ t, a j - ∏ j ∈ t, b j)‖ ≤
          A * ((∑ j ∈ t, ‖a j - b j‖) * A ^ (t.card - 1)) := by
        rw [norm_mul]
        exact mul_le_mul hai hih (norm_nonneg _) hA0
      -- second piece
      have hb2 : ‖(a i - b i) * ∏ j ∈ t, b j‖ ≤ ‖a i - b i‖ * A ^ t.card := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hprodb (norm_nonneg _)
      have hstep : A * ((∑ j ∈ t, ‖a j - b j‖) * A ^ (t.card - 1)) ≤
          (∑ j ∈ t, ‖a j - b j‖) * A ^ t.card := by
        rcases Nat.eq_zero_or_pos t.card with h0 | hpos
        · have ht : t = ∅ := Finset.card_eq_zero.mp h0
          subst ht; simp
        · have hpow : A * A ^ (t.card - 1) = A ^ t.card := by
            obtain ⟨m, hm⟩ : ∃ m, t.card = m + 1 := ⟨t.card - 1, by omega⟩
            rw [hm, Nat.add_sub_cancel, pow_succ']
          rw [show A * ((∑ j ∈ t, ‖a j - b j‖) * A ^ (t.card - 1)) =
              (∑ j ∈ t, ‖a j - b j‖) * (A * A ^ (t.card - 1)) from by ring, hpow]
      have hcard : (insert i t).card - 1 = t.card := by
        rw [Finset.card_insert_of_notMem hi]; omega
      rw [hcard]
      calc ‖a i * (∏ j ∈ t, a j - ∏ j ∈ t, b j) + (a i - b i) * ∏ j ∈ t, b j‖
          ≤ ‖a i * (∏ j ∈ t, a j - ∏ j ∈ t, b j)‖ + ‖(a i - b i) * ∏ j ∈ t, b j‖ :=
            norm_add_le _ _
        _ ≤ A * ((∑ j ∈ t, ‖a j - b j‖) * A ^ (t.card - 1)) + ‖a i - b i‖ * A ^ t.card :=
            add_le_add hb1 hb2
        _ ≤ (∑ j ∈ t, ‖a j - b j‖) * A ^ t.card + ‖a i - b i‖ * A ^ t.card :=
            add_le_add hstep le_rfl
        _ = (‖a i - b i‖ + ∑ j ∈ t, ‖a j - b j‖) * A ^ t.card := by ring

/-- The `Fin k` form of the telescoping product bound. -/
lemma norm_prod_sub_prod_le {k : ℕ} (a b : Fin k → ℂ) (A : ℝ)
    (ha : ∀ j, ‖a j‖ ≤ A) (hb : ∀ j, ‖b j‖ ≤ A) :
    ‖∏ j, a j - ∏ j, b j‖ ≤ (∑ j, ‖a j - b j‖) * A ^ (k - 1) := by
  simpa using norm_prod_sub_prod_finset (Finset.univ : Finset (Fin k)) a b A
    (fun j _ => ha j) (fun j _ => hb j)


/-! ## Lemma 4.1 for `k` coordinates -/

/-- **P8 Lemma 4.1, general `k`.**  For `k ≥ 1` and smooth compactly supported
cutoffs `F j, G j`, the `k`-fold divisor sum factorizes over the coordinates and
each factor is evaluated by `lemma41`, giving

    Σ_{d,d′} ∏_j μ(d_j)μ(d′_j)/[d_j,d′_j]·F_j(log_x d_j)·G_j(log_x d′_j)
      = (1 + o(1))·prefactor^k·∏_j ∫₀^∞ F_j′(t)G_j′(t) dt . -/
theorem lemma41_k (k : ℕ) (hk : 1 ≤ k)
    (F G : Fin k → (ℝ → ℝ)) (hcsF : ∀ j, HasCompactSupport (F j))
    (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j)) (hcsG : ∀ j, HasCompactSupport (G j))
    (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    (hcop : ∀ x, (W x).Coprime (N x))
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x * N x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log (((W x) * (N x) : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x →
        ‖(∑' d : Fin k → (ℕ × ℕ), ∏ j, (mobiusLcmWeight (W x * N x) (d j).1 (d j).2 *
              (F j (logR (d j).1 x) : ℂ) * (G j (logR (d j).2 x) : ℂ))) -
            (prefactor W N x : ℂ) ^ k * ∏ j, (∫ t : ℝ in Set.Ioi 0,
              ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ))‖ ≤
          ε x * prefactor W N x ^ k := by
  classical
  choose x₀j εj hrest using fun j : Fin k =>
    lemma41 (F j) (G j) (hcsF j) (hsmF j) (hcsG j) (hsmG j) W N hW hN hcop w hw hsmall hlq
  have hεj : ∀ j, Tendsto (εj j) atTop (𝓝 0) := fun j => (hrest j).1
  have hbound : ∀ j (x : ℕ), x₀j j ≤ x →
      ‖(∑' d : ℕ × ℕ, mobiusLcmWeight (W x * N x) d.1 d.2 *
          (F j (logR d.1 x) : ℂ) * (G j (logR d.2 x) : ℂ)) -
        (prefactor W N x : ℂ) * (∫ t : ℝ in Set.Ioi 0,
          ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ))‖ ≤
      εj j x * prefactor W N x := fun j x hx => (hrest j).2 x hx
  have hεev : ∀ᶠ x : ℕ in atTop, ∀ j : Fin k, |εj j x| ≤ 1 := by
    rw [Filter.eventually_all]
    intro j
    have h := (hεj j).abs
    rw [abs_zero] at h
    filter_upwards [h.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with x hx
    exact le_of_lt hx
  obtain ⟨X₂, hX₂⟩ := Filter.eventually_atTop.mp hεev
  refine ⟨max (Finset.univ.sup x₀j) (max X₂ 2),
    fun x => (∑ j, |εj j x|) * ((∑ j, ‖(∫ t : ℝ in Set.Ioi 0,
      ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ))‖) + 1) ^ (k - 1), ?_, ?_⟩
  · -- the error tends to zero
    have hsum : Tendsto (fun x : ℕ => ∑ j, |εj j x|) atTop (𝓝 0) := by
      have := tendsto_finset_sum Finset.univ (fun j _ => (hεj j).abs)
      simpa using this
    simpa using hsum.mul_const _
  · intro x hx
    have hxX₂ : X₂ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
    have hx2 : 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    have hx1 : 1 < x := by omega
    have hxj : ∀ j : Fin k, x₀j j ≤ x := fun j =>
      le_trans (Finset.le_sup (Finset.mem_univ j))
        (le_trans (le_max_left _ _) hx)
    have hεx : ∀ j : Fin k, |εj j x| ≤ 1 := fun j => hX₂ x hxX₂ j
    have hq : W x * N x ≠ 0 := mul_ne_zero (hW x) (hN x)
    -- the factorization
    have hfact : (∑' d : Fin k → (ℕ × ℕ), ∏ j, (mobiusLcmWeight (W x * N x) (d j).1 (d j).2 *
          (F j (logR (d j).1 x) : ℂ) * (G j (logR (d j).2 x) : ℂ))) =
        ∏ j, (∑' d : ℕ × ℕ, mobiusLcmWeight (W x * N x) d.1 d.2 *
          (F j (logR d.1 x) : ℂ) * (G j (logR d.2 x) : ℂ)) :=
      tsum_prod_pi k (fun j (d : ℕ × ℕ) => mobiusLcmWeight (W x * N x) d.1 d.2 *
          (F j (logR d.1 x) : ℂ) * (G j (logR d.2 x) : ℂ))
        (fun j => summable_norm_coordWeight (W x * N x) x hq hx1 (F j) (G j)
          (hcsF j) (hsmF j) (hcsG j) (hsmG j))
    rw [hfact]
    set P : ℝ := prefactor W N x with hP
    have hP0 : 0 ≤ P := by
      rw [hP, prefactor]
      have hφN : (0 : ℝ) < (N x).totient := by
        exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hN x))
      have hφW : (0 : ℝ) < (W x).totient := by
        exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (hW x))
      positivity
    have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
    set cc : Fin k → ℂ := fun j => ∫ t : ℝ in Set.Ioi 0,
      ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ) with hcc
    set Cc : ℝ := ∑ j, ‖cc j‖ with hCc
    have hCc0 : 0 ≤ Cc := by
      rw [hCc]; exact Finset.sum_nonneg (fun j _ => norm_nonneg _)
    have hCcj : ∀ j, ‖cc j‖ ≤ Cc := fun j => Finset.single_le_sum (fun i _ => norm_nonneg _)
      (Finset.mem_univ j)
    set A : ℝ := P * (Cc + 1) with hA
    have hA0 : 0 ≤ A := mul_nonneg hP0 (by linarith)
    -- bounds on the two families
    have ha : ∀ j, ‖(∑' d : ℕ × ℕ, mobiusLcmWeight (W x * N x) d.1 d.2 *
          (F j (logR d.1 x) : ℂ) * (G j (logR d.2 x) : ℂ))‖ ≤ A := by
      intro j
      have hb := hbound j x (hxj j)
      have h1 : ‖(∑' d : ℕ × ℕ, mobiusLcmWeight (W x * N x) d.1 d.2 *
            (F j (logR d.1 x) : ℂ) * (G j (logR d.2 x) : ℂ)) -
          (P : ℂ) * cc j‖ ≤ |εj j x| * P := by
        rw [hP, hcc]
        exact hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hP0)
      have h2 : ‖(P : ℂ) * cc j‖ ≤ P * Cc := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hP0, hP]
        exact mul_le_mul_of_nonneg_left (hCcj j) hP0
      calc ‖(∑' d : ℕ × ℕ, mobiusLcmWeight (W x * N x) d.1 d.2 *
            (F j (logR d.1 x) : ℂ) * (G j (logR d.2 x) : ℂ))‖
          ≤ ‖(∑' d : ℕ × ℕ, mobiusLcmWeight (W x * N x) d.1 d.2 *
              (F j (logR d.1 x) : ℂ) * (G j (logR d.2 x) : ℂ)) - (P : ℂ) * cc j‖ +
            ‖(P : ℂ) * cc j‖ := norm_le_norm_sub_add _ _
        _ ≤ |εj j x| * P + P * Cc := add_le_add h1 h2
        _ ≤ A := by
            rw [hA]
            nlinarith [hP0, hCc0, hεx j]
    have hb : ∀ j, ‖(P : ℂ) * cc j‖ ≤ A := by
      intro j
      have h2 : ‖(P : ℂ) * cc j‖ ≤ P * Cc := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hP0, hP]
        exact mul_le_mul_of_nonneg_left (hCcj j) hP0
      refine h2.trans ?_
      rw [hA]
      nlinarith [hP0, hCc0]
    -- the product bound
    have htel := norm_prod_sub_prod_le (fun j => (∑' d : ℕ × ℕ, mobiusLcmWeight (W x * N x) d.1 d.2 *
        (F j (logR d.1 x) : ℂ) * (G j (logR d.2 x) : ℂ))) (fun j => (P : ℂ) * cc j) A ha hb
    have hdev : ∀ j, ‖(∑' d : ℕ × ℕ, mobiusLcmWeight (W x * N x) d.1 d.2 *
          (F j (logR d.1 x) : ℂ) * (G j (logR d.2 x) : ℂ)) - (P : ℂ) * cc j‖ ≤ |εj j x| * P := by
      intro j
      have hb' := hbound j x (hxj j)
      rw [hP, hcc]
      exact hb'.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hP0)
    have hprod : ∏ j, ((P : ℂ) * cc j) = (P : ℂ) ^ k * ∏ j, cc j := by
      rw [Finset.prod_mul_distrib]
      congr 1
      simp [Finset.prod_const, Fintype.card_fin]
    rw [hprod] at htel
    -- the exponent arithmetic
    have hPk : P * P ^ (k - 1) = P ^ k := by
      obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel, pow_succ']
    have hAexp : A ^ (k - 1) = P ^ (k - 1) * (Cc + 1) ^ (k - 1) := by
      rw [hA, mul_pow]
    have hmain : (∑ j, ‖(∑' d : ℕ × ℕ, mobiusLcmWeight (W x * N x) d.1 d.2 *
          (F j (logR d.1 x) : ℂ) * (G j (logR d.2 x) : ℂ)) - (P : ℂ) * cc j‖) * A ^ (k - 1) ≤
        ((∑ j, |εj j x|) * (Cc + 1) ^ (k - 1)) * P ^ k := by
      have h1 : (∑ j, ‖(∑' d : ℕ × ℕ, mobiusLcmWeight (W x * N x) d.1 d.2 *
            (F j (logR d.1 x) : ℂ) * (G j (logR d.2 x) : ℂ)) - (P : ℂ) * cc j‖) ≤
          (∑ j, |εj j x|) * P := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum (fun j _ => hdev j)
      have hsum0 : 0 ≤ ∑ j, ‖(∑' d : ℕ × ℕ, mobiusLcmWeight (W x * N x) d.1 d.2 *
            (F j (logR d.1 x) : ℂ) * (G j (logR d.2 x) : ℂ)) - (P : ℂ) * cc j‖ :=
        Finset.sum_nonneg (fun j _ => norm_nonneg _)
      calc (∑ j, ‖(∑' d : ℕ × ℕ, mobiusLcmWeight (W x * N x) d.1 d.2 *
              (F j (logR d.1 x) : ℂ) * (G j (logR d.2 x) : ℂ)) - (P : ℂ) * cc j‖) * A ^ (k - 1)
          ≤ ((∑ j, |εj j x|) * P) * A ^ (k - 1) :=
            mul_le_mul_of_nonneg_right h1 (pow_nonneg hA0 _)
        _ = ((∑ j, |εj j x|) * (Cc + 1) ^ (k - 1)) * P ^ k := by
            rw [hAexp]
            have : (∑ j, |εj j x|) * P * (P ^ (k - 1) * (Cc + 1) ^ (k - 1)) =
                (∑ j, |εj j x|) * (Cc + 1) ^ (k - 1) * (P * P ^ (k - 1)) := by ring
            rw [this, hPk]
    -- assemble
    rw [hP] at htel hmain ⊢
    refine htel.trans hmain

end Commons.NumberTheory.MaynardSieve
