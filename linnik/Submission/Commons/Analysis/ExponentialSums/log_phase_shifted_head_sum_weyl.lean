import Mathlib
import Submission.Commons.Analysis.ExponentialSums.third_derivative_test

open Complex Filter
open scoped Real BigOperators Topology Filter ComplexConjugate
set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace Commons.Analysis.ExponentialSums

noncomputable section

/-! ### Inlined support (finite Abel, index shifts, conjugation) -/

namespace TdtAbel

private lemma sum_nat_Icc_eq_sum_int {a b : ℕ} (hab : a ≤ b) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc a b, f n) =
      ∑ z ∈ Finset.Icc (a : ℤ) (b : ℤ), f (Int.toNat z) := by
  classical
  refine Finset.sum_bij (fun n hn => (n : ℤ)) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact_mod_cast hn
  · intro a1 ha1 a2 ha2 h
    exact_mod_cast h
  · intro z hz
    have hz0 : (0 : ℤ) ≤ z := le_trans (by exact_mod_cast (Nat.zero_le a) : (0 : ℤ) ≤ (a : ℤ))
        (Finset.mem_Icc.mp hz).1
    have hzn : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
    refine ⟨Int.toNat z, ?_, hzn⟩
    have hza : (a : ℤ) ≤ z := (Finset.mem_Icc.mp hz).1
    have hzb : z ≤ (b : ℤ) := (Finset.mem_Icc.mp hz).2
    rw [← hzn] at hza hzb
    simp only [Finset.mem_Icc]
    exact ⟨by exact_mod_cast hza, by exact_mod_cast hzb⟩
  · intro n hn
    simp [Int.toNat_natCast]

/-- A sum of phase terms over a natural interval equals the same sum over the
embedded integer interval. -/

private lemma sum_Icc_union {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc a c, f n) =
      (∑ n ∈ Finset.Icc a b, f n) + (∑ n ∈ Finset.Icc (b + 1) c, f n) := by
  have hIcc : Finset.Icc a c = Finset.Icc a b ∪ Finset.Icc (b + 1) c := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    constructor
    · intro hn
      rcases hn with ⟨h1, h2⟩
      by_cases hnle : n ≤ b
      · exact Or.inl ⟨h1, hnle⟩
      · exact Or.inr ⟨by omega, h2⟩
    · intro hn
      rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1, le_trans h2 hbc⟩
      · exact ⟨le_trans hab (by omega), h2⟩
  rw [hIcc]
  rw [Finset.sum_union]
  · apply Finset.disjoint_left.mpr
    intro n hn hn2
    have hn1 : n ≤ b := (Finset.mem_Icc.mp hn).2
    have hn2' : b + 1 ≤ n := (Finset.mem_Icc.mp hn2).1
    omega


/-! ### rpow algebra helpers (positive bases; `p` plays the role of `8π`) -/

/-- `(x³)^(1/6) = x^(1/2)` for `0 ≤ x`. -/

private lemma abel_decomposition (a b : ℕ → ℂ) {N M : ℕ} (hNM : N ≤ M) (hN : 1 ≤ N) :
    (∑ k ∈ Finset.Icc N M, a k * b k) =
      (∑ n ∈ Finset.Icc N M, a n) * b M +
        ∑ k ∈ Finset.Icc N (M - 1), (∑ n ∈ Finset.Icc N k, a n) * (b k - b (k + 1)) := by
  let S : ℕ → ℂ := fun j => ∑ n ∈ Finset.Icc N j, a n
  let P : (n : ℕ) → N ≤ n → Prop := fun m _ =>
    (∑ k ∈ Finset.Icc N m, a k * b k) =
      S m * b m + ∑ k ∈ Finset.Icc N (m - 1), S k * (b k - b (k + 1))
  have hbase : P N (le_rfl) := by
    dsimp [P, S]
    have hIcc1 : Finset.Icc N N = {N} := by simp
    have hIcc2 : Finset.Icc N (N - 1) = ∅ := by
      exact Finset.Icc_eq_empty (by omega)
    rw [hIcc1, hIcc2]
    simp
  have hstep : ∀ (m : ℕ) (hm : N ≤ m), P m hm → P (m + 1) (by omega) := by
    intro m hm ih
    dsimp [P] at ih ⊢
    have hNm1 : N ≤ m + 1 := by omega
    have hmm1 : (m - 1) + 1 = m := by omega
    have hsplitL : (∑ k ∈ Finset.Icc N (m + 1), a k * b k)
        = (∑ k ∈ Finset.Icc N m, a k * b k) + a (m + 1) * b (m + 1) := by
        simpa using (Finset.sum_Icc_succ_top (a := N) (b := m) hNm1 (fun k => a k * b k))
    have hSM : S (m + 1) = S m + a (m + 1) := by
        dsimp [S]
        simpa using (Finset.sum_Icc_succ_top (a := N) (b := m) hNm1 a)
    have hsplit2 : (∑ k ∈ Finset.Icc N m, S k * (b k - b (k + 1)))
        = (∑ k ∈ Finset.Icc N (m - 1), S k * (b k - b (k + 1))) + S m * (b m - b (m + 1)) := by
        have htmp := Finset.sum_Icc_succ_top (a := N) (b := m - 1) (by omega)
          (fun k => S k * (b k - b (k + 1)))
        rw [hmm1] at htmp
        simpa [hmm1] using htmp
    calc
      (∑ k ∈ Finset.Icc N (m + 1), a k * b k)
          = a (m + 1) * b (m + 1) + (S m * b m + ∑ k ∈ Finset.Icc N (m - 1), S k * (b k - b (k + 1))) := by
            rw [hsplitL, ih]
            ring
      _ = S (m + 1) * b (m + 1) + ∑ k ∈ Finset.Icc N m, S k * (b k - b (k + 1)) := by
            rw [hSM, hsplit2]
            ring
  exact Nat.le_induction hbase hstep M hNM

/-- Norm bound from summation by parts (no positivity assumptions). -/

private lemma abel_norm_bound (a b : ℕ → ℂ) {N M : ℕ} (hNM : N ≤ M) (hN : 1 ≤ N) :
    ‖∑ k ∈ Finset.Icc N M, a k * b k‖ ≤
      ‖∑ n ∈ Finset.Icc N M, a n‖ * ‖b M‖ +
        ∑ k ∈ Finset.Icc N (M - 1), ‖∑ n ∈ Finset.Icc N k, a n‖ * ‖b k - b (k + 1)‖ := by
  have hdec := abel_decomposition a b hNM hN
  calc
    ‖∑ k ∈ Finset.Icc N M, a k * b k‖
        = ‖(∑ n ∈ Finset.Icc N M, a n) * b M +
            ∑ k ∈ Finset.Icc N (M - 1), (∑ n ∈ Finset.Icc N k, a n) * (b k - b (k + 1))‖ := by
          rw [hdec]
    _ ≤ ‖(∑ n ∈ Finset.Icc N M, a n) * b M‖ +
          ‖∑ k ∈ Finset.Icc N (M - 1), (∑ n ∈ Finset.Icc N k, a n) * (b k - b (k + 1))‖ := by
          exact norm_add_le _ _
    _ ≤ ‖∑ n ∈ Finset.Icc N M, a n‖ * ‖b M‖ +
          ‖∑ k ∈ Finset.Icc N (M - 1), (∑ n ∈ Finset.Icc N k, a n) * (b k - b (k + 1))‖ := by
          exact add_le_add (norm_mul_le _ _) le_rfl
    _ ≤ ‖∑ n ∈ Finset.Icc N M, a n‖ * ‖b M‖ +
          (∑ k ∈ Finset.Icc N (M - 1),
            ‖(∑ n ∈ Finset.Icc N k, a n) * (b k - b (k + 1))‖) := by
          exact add_le_add le_rfl (norm_sum_le _ _)
    _ ≤ ‖∑ n ∈ Finset.Icc N M, a n‖ * ‖b M‖ +
          (∑ k ∈ Finset.Icc N (M - 1), ‖∑ n ∈ Finset.Icc N k, a n‖ * ‖b k - b (k + 1)‖) := by
          exact add_le_add le_rfl (Finset.sum_le_sum (fun k hk => norm_mul_le _ _))

/-- Norm of a real cast into `ℂ`. -/

private lemma norm_real_cast (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  simpa using (Complex.norm_real x)

/-- Abel summation with a nonneg decreasing real weight. -/

private lemma abel_weighted_bound {X : ℕ} (hX : 1 ≤ X) (a : ℕ → ℂ) (w : ℕ → ℝ)
    (hw0 : ∀ k, 1 ≤ k → k ≤ X → 0 ≤ w k)
    (hwdec : ∀ k, 1 ≤ k → k < X → w (k + 1) ≤ w k) :
    ‖∑ n ∈ Finset.Icc 1 X, a n * (w n : ℂ)‖ ≤
      ‖∑ n ∈ Finset.Icc 1 X, a n‖ * w X +
        ∑ k ∈ Finset.Icc 1 (X - 1), ‖∑ n ∈ Finset.Icc 1 k, a n‖ * (w k - w (k + 1)) := by
  have hbM : ‖(w X : ℂ)‖ = w X := by
    rw [norm_real_cast, abs_of_nonneg (hw0 X hX le_rfl)]
  have hb : ∀ k ∈ Finset.Icc 1 (X - 1), ‖(w k : ℂ) - (w (k + 1) : ℂ)‖ = w k - w (k + 1) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkX : k ≤ X - 1 := (Finset.mem_Icc.mp hk).2
    have hkX' : k < X := by omega
    rw [← Complex.ofReal_sub]
    rw [norm_real_cast]
    rw [abs_of_nonneg]
    linarith [hwdec k hk1 hkX']
  have h := abel_norm_bound a (fun n => (w n : ℂ)) (by omega : 1 ≤ X) (by norm_num : 1 ≤ (1 : ℕ))
  -- h : ‖Σ (a·↑w)‖ ≤ ‖Σ a‖·‖↑wX‖ + Σ ‖Σ a‖·‖↑wk − ↑w(k+1)‖
  calc
    ‖∑ n ∈ Finset.Icc 1 X, a n * (w n : ℂ)‖
        ≤ ‖∑ n ∈ Finset.Icc 1 X, a n‖ * ‖(w X : ℂ)‖ +
            (∑ k ∈ Finset.Icc 1 (X - 1), ‖∑ n ∈ Finset.Icc 1 k, a n‖ * ‖(w k : ℂ) - (w (k + 1) : ℂ)‖) := by
            simpa using h
    _ = ‖∑ n ∈ Finset.Icc 1 X, a n‖ * w X +
            (∑ k ∈ Finset.Icc 1 (X - 1), ‖∑ n ∈ Finset.Icc 1 k, a n‖ * (w k - w (k + 1))) := by
            have hsum : (∑ k ∈ Finset.Icc 1 (X - 1),
                  ‖∑ n ∈ Finset.Icc 1 k, a n‖ * ‖(w k : ℂ) - (w (k + 1) : ℂ)‖) =
                (∑ k ∈ Finset.Icc 1 (X - 1),
                  ‖∑ n ∈ Finset.Icc 1 k, a n‖ * (w k - w (k + 1))) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [hb k hk]
            rw [hbM, hsum]


end TdtAbel

namespace TdtFejer

private lemma exp_conj_mul_I (r : ℝ) : conj (cexp ((((r : ℝ) : ℂ) * I))) = cexp (-(((r : ℝ) : ℂ) * I)) := by
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring


end TdtFejer

namespace TdtLogBound

private lemma norm_exp_neg_eq {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ‖∑ i ∈ s, cexp ((((x i : ℝ) : ℂ) * I))‖ =
      ‖∑ i ∈ s, cexp ((((-(x i) : ℝ) : ℂ) * I))‖ := by
  classical
  have hconj : (∑ i ∈ s, cexp ((((-(x i) : ℝ) : ℂ) * I))) =
      (starRingEnd ℂ) (∑ i ∈ s, cexp ((((x i : ℝ) : ℂ) * I))) := by
    rw [map_sum (starRingEnd ℂ)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [TdtFejer.exp_conj_mul_I (x i)]
    congr 1
    apply Complex.ext <;> simp
  calc
    ‖∑ i ∈ s, cexp ((((x i : ℝ) : ℂ) * I))‖
        = ‖(starRingEnd ℂ) (∑ i ∈ s, cexp ((((x i : ℝ) : ℂ) * I)))‖ :=
          (Complex.norm_conj _).symm
    _ = ‖∑ i ∈ s, cexp ((((-(x i) : ℝ) : ℂ) * I))‖ := by
          rw [← hconj]


end TdtLogBound

namespace TdtAbelRhs

private lemma sum_Icc_one_shift {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    (∑ k ∈ Finset.Icc 1 m, f k) = ∑ i ∈ Finset.range m, f (i + 1) := by
  classical
  induction m with
  | zero =>
      simp
  | succ m ih =>
      calc
        (∑ k ∈ Finset.Icc 1 (m + 1), f k)
            = (∑ k ∈ Finset.Icc 1 m, f k) + f (m + 1) := by
                simpa using (Finset.sum_Icc_succ_top (a := 1) (b := m) (by omega : (1 : ℕ) ≤ m + 1) f)
        _ = (∑ i ∈ Finset.range m, f (i + 1)) + f (m + 1) := by rw [ih]
        _ = ∑ i ∈ Finset.range (m + 1), f (i + 1) := by
                rw [Finset.sum_range_succ]


end TdtAbelRhs

namespace TdtShiftHead

/-! ### shifted phase and summand -/

/-- shifted phase factor `(c+x)^{-it} = cexp(2πi·(−(t/2π)·log(c+x)))`. -/
private def sPhase (c t : ℝ) (x : ℝ) : ℂ :=
  cexp ((((2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log (c + x))) : ℝ) : ℂ) * I)

/-- full shifted weighted summand `(c+x)^{-1/2-it}`. -/
private def sSummand (c t : ℝ) (x : ℝ) : ℂ := sPhase c t x / Real.sqrt (c + x)

/-- amplitude `(c+x)^{-1/2}` (real). -/
private def amp (c : ℝ) (x : ℝ) : ℝ := (Real.sqrt (c + x))⁻¹

private lemma norm_sPhase {c t x : ℝ} : ‖sPhase c t x‖ = 1 := by
  dsimp [sPhase]
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log (c + x)))

private lemma norm_sPhase_le_one {c t : ℝ} (x : ℝ) : ‖sPhase c t x‖ ≤ 1 := by
  rw [norm_sPhase]

private lemma sSummand_eq_mul (c t : ℝ) (x : ℝ) :
    sSummand c t x = sPhase c t x * ((amp c x : ℝ) : ℂ) := by
  dsimp [sSummand, amp]
  rw [div_eq_mul_inv]
  rw [Complex.ofReal_inv]

/-- norm of the amplitude cast. -/
private lemma norm_amp_cast (c x : ℝ) : ‖((amp c x : ℝ) : ℂ)‖ = |amp c x| := by
  simpa using (Complex.norm_real (amp c x))

/-- `star(cexp((w:ℂ)·I)) = cexp((−w)·I)` for real `w`. -/
private lemma conj_exp_ofReal_mul_I (w : ℝ) :
    starRingEnd ℂ (cexp (((w : ℝ) : ℂ) * I)) = cexp (((-w : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  simp

/-- `sPhase` equals the conjugate of `cexp(2πi·(t/(2π))·log(c+x))`. -/
private lemma sPhase_conj {c t x : ℝ} :
    starRingEnd ℂ (sPhase c t x) =
      cexp ((((2 * Real.pi * ((t / (2 * Real.pi)) * Real.log (c + x))) : ℝ) : ℂ) * I) := by
  rw [sPhase, conj_exp_ofReal_mul_I]
  congr 2
  field_simp [Real.pi_ne_zero]

/-- `sPhase`-analogue of `TdtAbel.phase_sum_nat_eq_phase_sum_int`. -/
private lemma sPhase_sum_nat_eq_int {a b : ℕ} (hab : a ≤ b) {c t : ℝ} :
    (∑ n ∈ Finset.Icc a b, sPhase c t (n : ℝ)) =
      ∑ z ∈ Finset.Icc (a : ℤ) (b : ℤ), sPhase c t (z : ℝ) := by
  have h1 := TdtAbel.sum_nat_Icc_eq_sum_int (a := a) (b := b) hab
    (fun n : ℕ => sPhase c t (n : ℝ))
  rw [h1]
  apply Finset.sum_congr rfl
  intro z hz
  have hz0 : (0 : ℤ) ≤ z := le_trans (by exact_mod_cast (Nat.zero_le a) : (0 : ℤ) ≤ (a : ℤ))
    (Finset.mem_Icc.mp hz).1
  have hzn : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
  have hzr : ((Int.toNat z : ℕ) : ℝ) = (z : ℝ) := by exact_mod_cast hzn
  exact congrArg (fun w : ℝ => sPhase c t w) hzr

/-! ### shifted derivative machinery -/

/-- neighbourhood of points where `c + z ≠ 0`. -/
private lemma hset_affine {c x : ℝ} (hx : c + x ≠ 0) : {z : ℝ | c + z ≠ 0} ∈ 𝓝 x := by
  have hx' : x ≠ -c := by
    intro h
    apply hx
    linarith
  have hmem : x ∈ {y : ℝ | y ≠ -c} := by simpa using hx'
  have hnh : {y : ℝ | y ≠ -c} ∈ 𝓝 x := (isOpen_ne (x := (-c : ℝ))).mem_nhds hmem
  convert hnh using 1
  ext z
  constructor
  · intro hz hzc
    apply hz
    linarith
  · intro hne hz
    exact hne (by linarith)

/-- `deriv (fun y ↦ log(c+y)) x = (c+x)⁻¹` for `c+x ≠ 0`. -/
private lemma deriv_shift_log {c x : ℝ} (hx : c + x ≠ 0) :
    deriv (fun z : ℝ => Real.log (c + z)) x = (c + x)⁻¹ := by
  have hlin : HasDerivAt (fun z : ℝ => c + z) (1 : ℝ) x := by
    simpa using (HasDerivAt.const_add c (hasDerivAt_id x))
  have hc : HasDerivAt (fun z : ℝ => Real.log (c + z)) ((c + x)⁻¹) x := by
    simpa [Function.comp_def] using (Real.hasDerivAt_log hx).comp x hlin
  exact hc.deriv

/-- `deriv (fun y ↦ (c+y)⁻¹) x = -(c+x)⁻²` for `c+x ≠ 0`. -/
private lemma deriv_shift_inv {c x : ℝ} (hx : c + x ≠ 0) :
    deriv (fun z : ℝ => (c + z)⁻¹) x = -((c + x) ^ 2)⁻¹ := by
  have hlin : HasDerivAt (fun z : ℝ => c + z) (1 : ℝ) x := by
    simpa using (HasDerivAt.const_add c (hasDerivAt_id x))
  have hd : HasDerivAt (fun z : ℝ => (c + z)⁻¹) (-((c + x) ^ 2)⁻¹) x := by
    have hinv := hasDerivAt_inv (𝕜 := ℝ) hx
    simpa [Function.comp_def] using hinv.comp x hlin
  exact hd.deriv

/-- `deriv (fun y ↦ (c+y)⁻²) x = -2·(c+x)⁻³` for `c+x ≠ 0`. -/
private lemma deriv_shift_inv_sq {c x : ℝ} (hx : c + x ≠ 0) :
    deriv (fun z : ℝ => ((c + z) ^ 2)⁻¹) x = -2 * ((c + x) ^ 3)⁻¹ := by
  have hlin : HasDerivAt (fun z : ℝ => c + z) (1 : ℝ) x := by
    simpa using (HasDerivAt.const_add c (hasDerivAt_id x))
  have hpow : HasDerivAt (fun z : ℝ => (c + z) ^ 2) (2 * (c + x)) x := by
    have hp := hasDerivAt_pow 2 (c + x)
    simpa [Function.comp_def] using hp.comp x hlin
  have hinv : HasDerivAt (fun z : ℝ => ((c + z) ^ 2)⁻¹) (-(2 * (c + x)) / ((c + x) ^ 2) ^ 2) x :=
    hpow.inv (pow_ne_zero 2 hx)
  rw [HasDerivAt.deriv hinv]
  field_simp [hx, pow_succ]

/-- `deriv (fun y ↦ k·log(c₀+y)) x = k·(c₀+x)⁻¹` for `c₀+x ≠ 0`. -/
private lemma deriv_const_shift_log {c0 k x : ℝ} (hx : c0 + x ≠ 0) :
    deriv (fun z : ℝ => k * Real.log (c0 + z)) x = k * (c0 + x)⁻¹ := by
  have hd : DifferentiableAt ℝ (fun z : ℝ => Real.log (c0 + z)) x := by
    have hc : DifferentiableAt ℝ (fun z : ℝ => c0 + z) x :=
      DifferentiableAt.const_add c0 differentiableAt_id
    exact (Real.differentiableAt_log hx).comp x hc
  rw [deriv_const_mul (c := k) hd]
  rw [deriv_shift_log hx]

/-- `deriv (deriv (fun y ↦ k·log(c₀+y))) x = k·(−((c₀+x)²)⁻¹)` for `c₀+x ≠ 0`. -/
private lemma deriv_deriv_const_shift_log {c0 k x : ℝ} (hx : c0 + x ≠ 0) :
    deriv (deriv (fun z : ℝ => k * Real.log (c0 + z))) x = k * (-(((c0 + x) ^ 2)⁻¹)) := by
  have hdf : (fun z : ℝ => k * (c0 + z)⁻¹) =ᶠ[𝓝 x]
      deriv (fun z : ℝ => k * Real.log (c0 + z)) := by
    filter_upwards [hset_affine (x := x) hx]
    intro z hz
    exact (deriv_const_shift_log (c0 := c0) (k := k) (x := z) hz).symm
  calc
    deriv (deriv (fun z : ℝ => k * Real.log (c0 + z))) x
        = deriv (fun z : ℝ => k * (c0 + z)⁻¹) x := (Filter.EventuallyEq.deriv_eq hdf).symm
    _ = k * (-(((c0 + x) ^ 2)⁻¹)) := by
          have hd : DifferentiableAt ℝ (fun z : ℝ => (c0 + z)⁻¹) x := by
            have hc : DifferentiableAt ℝ (fun z : ℝ => c0 + z) x :=
              DifferentiableAt.const_add c0 differentiableAt_id
            exact (differentiableAt_inv hx).comp x hc
          rw [deriv_const_mul (c := k) hd]
          rw [deriv_shift_inv hx]

/-- third derivative value of the shifted log phase. -/
private lemma third_deriv_shift_value {c t x : ℝ} (hx : c + x ≠ 0) :
    deriv (deriv (deriv (fun y : ℝ => (t / (2 * Real.pi)) * Real.log (c + y)))) x =
      (t / Real.pi) * ((c + x) ^ 3)⁻¹ := by
  have hddf : (fun z : ℝ => (t / (2 * Real.pi)) * (-(((c + z) ^ 2)⁻¹))) =ᶠ[𝓝 x]
      deriv (deriv (fun z : ℝ => (t / (2 * Real.pi)) * Real.log (c + z))) := by
    filter_upwards [hset_affine (x := x) hx]
    intro z hz
    exact (deriv_deriv_const_shift_log (c0 := c) (k := t / (2 * Real.pi)) (x := z) hz).symm
  calc
    deriv (deriv (deriv (fun y : ℝ => (t / (2 * Real.pi)) * Real.log (c + y)))) x
        = deriv (fun z : ℝ => (t / (2 * Real.pi)) * (-(((c + z) ^ 2)⁻¹))) x :=
          (Filter.EventuallyEq.deriv_eq hddf).symm
    _ = (t / Real.pi) * ((c + x) ^ 3)⁻¹ := by
          have hlin : HasDerivAt (fun z : ℝ => c + z) (1 : ℝ) x := by
            simpa using (HasDerivAt.const_add c (hasDerivAt_id x))
          have hpow : HasDerivAt (fun z : ℝ => (c + z) ^ 2) (2 * (c + x)) x := by
            have hp := hasDerivAt_pow 2 (c + x)
            simpa [Function.comp_def] using hp.comp x hlin
          have hinv : HasDerivAt (fun z : ℝ => ((c + z) ^ 2)⁻¹)
              (-(2 * (c + x)) / ((c + x) ^ 2) ^ 2) x :=
            hpow.inv (pow_ne_zero 2 hx)
          have hval : -(-(2 * (c + x)) / ((c + x) ^ 2) ^ 2) =
              2 * (c + x) * (((c + x) ^ 2) ^ 2)⁻¹ := by
            field_simp [hx]
          have hneg0 : HasDerivAt (fun z : ℝ => -(((c + z) ^ 2)⁻¹))
              (2 * (c + x) * (((c + x) ^ 2) ^ 2)⁻¹) x := by
            change HasDerivAt (-(fun z : ℝ => ((c + z) ^ 2)⁻¹))
              (2 * (c + x) * (((c + x) ^ 2) ^ 2)⁻¹) x
            simpa [hval] using hinv.neg
          have hveq : 2 * (c + x) * (((c + x) ^ 2) ^ 2)⁻¹ = 2 * ((c + x) ^ 3)⁻¹ := by
            field_simp [hx]
          have hneg : HasDerivAt (fun z : ℝ => -(((c + z) ^ 2)⁻¹)) (2 * ((c + x) ^ 3)⁻¹) x := by
            simpa [hveq] using hneg0
          have hmain : HasDerivAt
              (fun z : ℝ => (t / (2 * Real.pi)) * (-(((c + z) ^ 2)⁻¹)))
              ((t / (2 * Real.pi)) * (2 * ((c + x) ^ 3)⁻¹)) x := by
            simpa using (HasDerivAt.const_mul (t / (2 * Real.pi)) hneg)
          rw [HasDerivAt.deriv hmain]
          field_simp [Real.pi_ne_zero]

/-- The shifted log phase `x ↦ (t/(2π))·log(c+x)` is `C³` on any set where
`c + x > 0`. -/
private lemma contDiffOn_shiftedLog3 {c t : ℝ} {s : Set ℝ} (hs : ∀ x ∈ s, 0 < c + x) :
    ContDiffOn ℝ 3 (fun x : ℝ => (t / (2 * Real.pi)) * Real.log (c + x)) s := by
  have hlog : ContDiffOn ℝ 3 (fun x : ℝ => Real.log (c + x)) s := by
    have hlin : ContDiffOn ℝ 3 (fun x : ℝ => c + x) s := by
      simpa using ((contDiffOn_const : ContDiffOn ℝ 3 (fun _ : ℝ => c) s).add
        (contDiffOn_id : ContDiffOn ℝ 3 (fun x : ℝ => x) s))
    refine ContDiffOn.comp (Real.contDiffOn_log) hlin ?_
    intro x hx
    have hpos : 0 < c + x := hs x hx
    exact ne_of_gt hpos
  have hconst : ContDiffOn ℝ 3 (fun _ : ℝ => (t / (2 * Real.pi) : ℝ)) s :=
    contDiffOn_const
  exact ContDiffOn.mul hconst hlog

/-- **Two-sided third-derivative control of the shifted log phase on a partial
block.**  For `1 ≤ L ≤ P`, `c ≥ 0`, `t ≥ 1`, with
`λ := t/(π·(c+P+L)³)`, on `P < x < P+L`:

    λ ≤ deriv³(f) x ≤ 8·λ . -/
private lemma log_third_deriv_shift_two_sided {P L : ℕ} (hP : 1 ≤ P) (hLP : L ≤ P)
    {c : ℝ} (hc : 0 ≤ c) {t : ℝ} (ht : 1 ≤ t) :
    ∀ x : ℝ, x ∈ Set.Ioo (P : ℝ) ((P : ℝ) + (L : ℝ)) →
      (t / (Real.pi * (c + ((P + L : ℕ) : ℝ)) ^ 3)) ≤
          deriv (deriv (deriv (fun y : ℝ => (t / (2 * Real.pi)) * Real.log (c + y)))) x ∧
        deriv (deriv (deriv (fun y : ℝ => (t / (2 * Real.pi)) * Real.log (c + y)))) x ≤
          8 * (t / (Real.pi * (c + ((P + L : ℕ) : ℝ)) ^ 3)) := by
  intro x hx
  let u : ℝ := c + ((P + L : ℕ) : ℝ)
  have hPt0 : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hxP : (P : ℝ) < x := (Set.mem_Ioo.mp hx).1
  have hcast : (P : ℝ) + (L : ℝ) = ((P + L : ℕ) : ℝ) := by
    exact_mod_cast (by omega : P + L = P + L)
  have hxu : x < u := by
    dsimp [u]
    have hlt : x < (P : ℝ) + (L : ℝ) := (Set.mem_Ioo.mp hx).2
    rw [hcast] at hlt
    linarith
  have hcxp : 0 < c + x := by
    have h2 : 0 < x := lt_of_lt_of_le hPt0 (le_of_lt hxP)
    linarith
  have hcx0 : c + x ≠ 0 := ne_of_gt hcxp
  have hu : 0 < u := by
    have hpl : 0 < ((P + L : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < P + L)
    dsimp [u]
    linarith
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hval := third_deriv_shift_value (c := c) (t := t) (x := x) hcx0
  have hu3 : 0 < u ^ 3 := pow_pos hu 3
  have hcx3 : 0 < (c + x) ^ 3 := pow_pos hcxp 3
  have hx3le_u3 : (c + x) ^ 3 ≤ u ^ 3 := by
    have hle1 : c + x ≤ u := by
      have hx2 : x < ((P + L : ℕ) : ℝ) := by
        have hlt : x < (P : ℝ) + (L : ℝ) := (Set.mem_Ioo.mp hx).2
        rw [hcast] at hlt
        exact hlt
      dsimp [u]
      linarith
    exact pow_le_pow_left₀ (le_of_lt hcxp) hle1 3
  have hu3_le_8x3 : u ^ 3 ≤ 8 * (c + x) ^ 3 := by
    have hu_le_2cx : u ≤ 2 * (c + x) := by
      have hLPc : (L : ℝ) ≤ (P : ℝ) + c := by
        have hLP' : (L : ℝ) ≤ (P : ℝ) := by exact_mod_cast hLP
        linarith
      dsimp [u]
      rw [← hcast]
      nlinarith [hLPc, hxP, hc]
    calc
      u ^ 3 ≤ (2 * (c + x)) ^ 3 := pow_le_pow_left₀ hu.le hu_le_2cx 3
      _ = 8 * (c + x) ^ 3 := by ring
  have ht0 : 0 ≤ t := by
    have : 0 < t := lt_of_lt_of_le (by norm_num) ht
    linarith
  have hleft : (t / (Real.pi * u ^ 3)) ≤ (t / Real.pi) * ((c + x) ^ 3)⁻¹ := by
    have hinv : (u ^ 3)⁻¹ ≤ ((c + x) ^ 3)⁻¹ := by
      exact (inv_le_inv₀ hu3 hcx3).mpr hx3le_u3
    calc
      (t / (Real.pi * u ^ 3)) = (t / Real.pi) * (u ^ 3)⁻¹ := by
        field_simp [Real.pi_ne_zero, hu0, pow_ne_zero 3 hu0]
      _ ≤ (t / Real.pi) * ((c + x) ^ 3)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ t / Real.pi)
  have hright : (t / Real.pi) * ((c + x) ^ 3)⁻¹ ≤ 8 * (t / (Real.pi * u ^ 3)) := by
    have hinv : ((c + x) ^ 3)⁻¹ ≤ 8 * (u ^ 3)⁻¹ := by
      have hpos8 : 0 < 8 * (c + x) ^ 3 := by positivity
      have h1 : (8 * (c + x) ^ 3)⁻¹ ≤ (u ^ 3)⁻¹ := by
        exact (inv_le_inv₀ hpos8 hu3).mpr hu3_le_8x3
      calc
        ((c + x) ^ 3)⁻¹ = (8 * (c + x) ^ 3)⁻¹ * 8 := by
          field_simp [pow_ne_zero 3 hcx0]
        _ ≤ (u ^ 3)⁻¹ * 8 := by
          exact mul_le_mul_of_nonneg_right h1 (by norm_num : 0 ≤ (8 : ℝ))
        _ = 8 * (u ^ 3)⁻¹ := by ring
    calc
      (t / Real.pi) * ((c + x) ^ 3)⁻¹ ≤ (t / Real.pi) * (8 * (u ^ 3)⁻¹) := by
        exact mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ t / Real.pi)
      _ = 8 * (t / (Real.pi * u ^ 3)) := by
        field_simp [Real.pi_ne_zero, hu0, pow_ne_zero 3 hu0]
  constructor
  · rw [hval]
    simpa [u] using hleft
  · rw [hval]
    simpa [u] using hright

/-! ### conjugation norm bridge -/

/-- Norms of `Σ e(+2πi·(t/2π)log(c+m))` and `Σ sPhase` agree (conjugation). -/
private lemma phase_eq_norm_positive {c t : ℝ} (s : Finset ℕ) :
    ‖∑ m ∈ s, cexp ((((2 * Real.pi * ((t / (2 * Real.pi)) * Real.log (c + (m : ℝ)))) : ℝ) : ℂ) * I)‖ =
      ‖∑ m ∈ s, sPhase c t (m : ℝ)‖ := by
  classical
  have hconj : (∑ m ∈ s, cexp ((((2 * Real.pi * ((t / (2 * Real.pi)) * Real.log (c + (m : ℝ)))) : ℝ) : ℂ) * I)) =
      (starRingEnd ℂ) (∑ m ∈ s, sPhase c t (m : ℝ)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    exact (sPhase_conj (c := c) (t := t) (x := (m : ℝ))).symm
  calc
    ‖∑ m ∈ s, cexp ((((2 * Real.pi * ((t / (2 * Real.pi)) * Real.log (c + (m : ℝ)))) : ℝ) : ℂ) * I)‖
        = ‖(starRingEnd ℂ) (∑ m ∈ s, sPhase c t (m : ℝ))‖ := by rw [hconj]
    _ = ‖∑ m ∈ s, sPhase c t (m : ℝ)‖ := (Complex.norm_conj _)

/-! ### π-power bounds (crude) -/

/-- `π^{1/6} ≤ 2`. -/
private lemma pi_sixth_le_two : (Real.pi) ^ (1 / 6 : ℝ) ≤ 2 := by
  have hle : Real.pi ≤ 64 := by nlinarith [Real.pi_lt_four]
  have hmono : Real.pi ^ (1 / 6 : ℝ) ≤ (64 : ℝ) ^ (1 / 6 : ℝ) :=
    Real.rpow_le_rpow (le_of_lt Real.pi_pos) hle (by norm_num : 0 ≤ (1 / 6 : ℝ))
  exact le_trans hmono (by norm_num)

/-- `π^{−1/6} ≤ 1`. -/
private lemma pi_neg_sixth_le_one : (Real.pi) ^ (-(1 / 6 : ℝ)) ≤ 1 := by
  have h1 : 1 ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  calc
    (Real.pi) ^ (-(1 / 6 : ℝ)) ≤ (Real.pi) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1 (by norm_num : -(1 / 6 : ℝ) ≤ 0)
    _ = 1 := by rw [Real.rpow_zero]

/-! ### rpow algebra helpers for the shifted block bound -/

/-- `(x³)^(1/6) = x^(1/2)` for `0 ≤ x`. -/
private lemma pow3_rpow_sixth {x : ℝ} (hx : 0 ≤ x) :
    (x ^ 3) ^ (1 / 6 : ℝ) = x ^ (1 / 2 : ℝ) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx]
  congr 1
  norm_num

/-- `(x³)^(−1/6) = x^(−1/2)` for `0 ≤ x`. -/
private lemma pow3_rpow_neg_sixth {x : ℝ} (hx : 0 ≤ x) :
    (x ^ 3) ^ (-(1 / 6 : ℝ)) = x ^ (-(1 / 2 : ℝ)) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx]
  congr 1
  norm_num

/-- `λ^{1/6}` with `λ = t/(π·u³)` is `t^{1/6}·(π·u³)^{−1/6}` (`u > 0`). -/
private lemma lambda_sixth {t p u : ℝ} (ht : 0 ≤ t) (hu : 0 < p * u ^ 3) :
    (t / (p * u ^ 3)) ^ (1 / 6 : ℝ) = t ^ (1 / 6 : ℝ) * (p * u ^ 3) ^ (-(1 / 6 : ℝ)) := by
  calc
    (t / (p * u ^ 3)) ^ (1 / 6 : ℝ) = t ^ (1 / 6 : ℝ) / (p * u ^ 3) ^ (1 / 6 : ℝ) :=
      Real.div_rpow ht hu.le (1 / 6 : ℝ)
    _ = t ^ (1 / 6 : ℝ) * ((p * u ^ 3) ^ (1 / 6 : ℝ))⁻¹ := by
      rw [div_eq_mul_inv]
    _ = t ^ (1 / 6 : ℝ) * (p * u ^ 3) ^ (-(1 / 6 : ℝ)) := by
      rw [← Real.rpow_neg hu.le (1 / 6 : ℝ)]

/-- `λ^{−1/6}` with `λ = t/(π·u³)` is `t^{−1/6}·(π·u³)^{1/6}` (`t > 0`). -/
private lemma lambda_neg_sixth {t p u : ℝ} (ht : 0 < t) (hu : 0 < p * u ^ 3) :
    (t / (p * u ^ 3)) ^ (-(1 / 6 : ℝ)) = t ^ (-(1 / 6 : ℝ)) * (p * u ^ 3) ^ (1 / 6 : ℝ) := by
  have ht0 : 0 ≤ t := le_of_lt ht
  calc
    (t / (p * u ^ 3)) ^ (-(1 / 6 : ℝ))
        = ((t / (p * u ^ 3))⁻¹) ^ (1 / 6 : ℝ) := by
            rw [Real.rpow_neg_eq_inv_rpow]
    _ = ((p * u ^ 3) / t) ^ (1 / 6 : ℝ) := by
            congr 1
            rw [inv_div]
    _ = (p * u ^ 3) ^ (1 / 6 : ℝ) / t ^ (1 / 6 : ℝ) := by
            rw [Real.div_rpow hu.le ht0]
    _ = (p * u ^ 3) ^ (1 / 6 : ℝ) * t ^ (-(1 / 6 : ℝ)) := by
            rw [div_eq_mul_inv]
            rw [← Real.rpow_neg ht0 (1 / 6 : ℝ)]
    _ = t ^ (-(1 / 6 : ℝ)) * (p * u ^ 3) ^ (1 / 6 : ℝ) := by ring

/-- `(π·u³)^{1/6} = π^{1/6}·√u` for `0 ≤ π`, `0 < u`. -/
private lemma mul_rpow_sixth_sqrt {p u : ℝ} (hp : 0 ≤ p) (hu : 0 < u) :
    (p * u ^ 3) ^ (1 / 6 : ℝ) = p ^ (1 / 6 : ℝ) * Real.sqrt u := by
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [Real.mul_rpow hp (by positivity : 0 ≤ u ^ 3)]
  rw [pow3_rpow_sixth hu0]
  rw [Real.sqrt_eq_rpow]

/-- `(π·u³)^{−1/6} = π^{−1/6}·(√u)⁻¹` for `0 ≤ π`, `0 < u`. -/
private lemma mul_rpow_neg_sixth_invsqrt {p u : ℝ} (hp : 0 ≤ p) (hu : 0 < u) :
    (p * u ^ 3) ^ (-(1 / 6 : ℝ)) = p ^ (-(1 / 6 : ℝ)) * (Real.sqrt u)⁻¹ := by
  have hu0 : 0 ≤ u := le_of_lt hu
  rw [Real.mul_rpow hp (by positivity : 0 ≤ u ^ 3)]
  rw [pow3_rpow_neg_sixth hu0]
  rw [Real.sqrt_eq_rpow]
  rw [Real.rpow_neg hu0 (1 / 2 : ℝ)]

/-- `(√v)⁻¹ ≤ (√u)⁻¹` for `0 < u ≤ v`. -/
private lemma inv_sqrt_le_inv_sqrt {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (Real.sqrt v)⁻¹ ≤ (Real.sqrt u)⁻¹ := by
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (lt_of_lt_of_le hu huv)
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  exact (inv_le_inv₀ hsv hsu).mpr (Real.sqrt_le_sqrt huv)

/-! ### block phase-sum bound (ℤ-window via the third-derivative test) -/

/-- **Shifted phase partial-block bound** (natural-`m` form).  For
`1 ≤ L ≤ P`, `c > 0`, `t ≥ 1`, with `λ := t/(π·(c+P+L)³)`:

    |Σ_{P<m≤P+L} (c+m)^{−it}| ≤ C·( L·λ^{1/6} + √L·λ^{−1/6} ) . -/
private theorem shifted_phase_block_nat :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P L : ℕ) (hP : 1 ≤ P) (hL : 1 ≤ L) (hLP : L ≤ P)
        {c : ℝ} (hc : 0 < c) (t : ℝ) (ht : 1 ≤ t),
        let lam : ℝ := t / (Real.pi * (c + ((P + L : ℕ) : ℝ)) ^ 3)
        ‖∑ m ∈ Finset.Icc (P + 1) (P + L), sPhase c t (m : ℝ)‖ ≤
          C * ((L : ℝ) * lam ^ (1 / 6 : ℝ) + Real.sqrt (L : ℝ) * lam ^ (-(1 / 6 : ℝ))) := by
  classical
  obtain ⟨C8, hC8pos, hT⟩ := third_derivative_test (α := 8)
    (by norm_num : (1 : ℝ) ≤ 8)
  refine ⟨C8, hC8pos, ?_⟩
  intro P L hP hL hLP c hc t ht
  dsimp
  let f : ℝ → ℝ := fun x => (t / (2 * Real.pi)) * Real.log (c + x)
  let lam : ℝ := t / (Real.pi * (c + ((P + L : ℕ) : ℝ)) ^ 3)
  have hPt0 : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hLt0 : 0 < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hc0 : 0 ≤ c := le_of_lt hc
  have hfpos : ∀ x : ℝ, x ∈ Set.Icc (P : ℝ) ((P : ℝ) + (L : ℝ)) → 0 < c + x := by
    intro x hx
    have hxP : (P : ℝ) ≤ x := (Set.mem_Icc.mp hx).1
    linarith
  have hfC : ContDiffOn ℝ 3 f (Set.Icc (P : ℝ) ((P : ℝ) + (L : ℝ))) := by
    exact contDiffOn_shiftedLog3 (c := c) (t := t) (s := Set.Icc (P : ℝ) ((P : ℝ) + (L : ℝ))) hfpos
  have hl : 0 < lam := by
    dsimp [lam]
    positivity
  have hppp : ∀ x : ℝ, x ∈ Set.Ioo (P : ℝ) ((P : ℝ) + (L : ℝ)) →
      lam ≤ deriv (deriv (deriv f)) x ∧ deriv (deriv (deriv f)) x ≤ 8 * lam := by
    intro x hx
    have hb := log_third_deriv_shift_two_sided (P := P) (L := L) hP hLP (c := c) hc0 (t := t) ht x hx
    dsimp [lam, f] at hb ⊢
    exact hb
  have hs := hT (a := (P : ℤ)) (M := L) hL f (l := lam) hl hfC hppp
  -- hs bounds the +log phase; convert to sPhase and to ℕ indices
  have hconv : ‖∑ n ∈ Finset.Icc ((P : ℤ) + 1) ((P : ℤ) + (L : ℤ)),
        cexp ((((2 * Real.pi * f (n : ℝ)) : ℝ) : ℂ) * I)‖ =
      ‖∑ n ∈ Finset.Icc ((P : ℤ) + 1) ((P : ℤ) + (L : ℤ)), sPhase c t (n : ℝ)‖ := by
    have hne := TdtLogBound.norm_exp_neg_eq (s := Finset.Icc ((P : ℤ) + 1) ((P : ℤ) + (L : ℤ)))
      (x := fun n : ℤ => 2 * Real.pi * f (n : ℝ))
    calc
      ‖∑ n ∈ Finset.Icc ((P : ℤ) + 1) ((P : ℤ) + (L : ℤ)),
          cexp ((((2 * Real.pi * f (n : ℝ)) : ℝ) : ℂ) * I)‖
          = ‖∑ n ∈ Finset.Icc ((P : ℤ) + 1) ((P : ℤ) + (L : ℤ)),
              cexp ((((-(2 * Real.pi * f (n : ℝ)) : ℝ) : ℂ) * I))‖ := hne
      _ = ‖∑ n ∈ Finset.Icc ((P : ℤ) + 1) ((P : ℤ) + (L : ℤ)), sPhase c t (n : ℝ)‖ := by
            congr 1
            apply Finset.sum_congr rfl
            intro n hn
            dsimp [sPhase, f]
            congr 2
            field_simp [Real.pi_ne_zero]
  have hnat : (∑ m ∈ Finset.Icc (P + 1) (P + L), sPhase c t (m : ℝ)) =
      ∑ n ∈ Finset.Icc ((P : ℤ) + 1) ((P : ℤ) + (L : ℤ)), sPhase c t (n : ℝ) := by
    have hIccZ : Finset.Icc (((P + 1 : ℕ) : ℤ)) (((P + L : ℕ) : ℤ)) =
        Finset.Icc ((P : ℤ) + 1) ((P : ℤ) + (L : ℤ)) := by
      ext z; simp
    have hz := sPhase_sum_nat_eq_int (a := P + 1) (b := P + L) (by omega : P + 1 ≤ P + L)
      (c := c) (t := t)
    simpa [hIccZ] using hz
  have hmain : ‖∑ m ∈ Finset.Icc (P + 1) (P + L), sPhase c t (m : ℝ)‖ ≤
      C8 * ((L : ℝ) * lam ^ (1 / 6 : ℝ) + Real.sqrt (L : ℝ) * lam ^ (-(1 / 6 : ℝ))) := by
    calc
      ‖∑ m ∈ Finset.Icc (P + 1) (P + L), sPhase c t (m : ℝ)‖
          = ‖∑ n ∈ Finset.Icc ((P : ℤ) + 1) ((P : ℤ) + (L : ℤ)), sPhase c t (n : ℝ)‖ := by
            rw [hnat]
      _ = ‖∑ n ∈ Finset.Icc ((P : ℤ) + 1) ((P : ℤ) + (L : ℤ)),
            cexp ((((2 * Real.pi * f (n : ℝ)) : ℝ) : ℂ) * I)‖ := hconv.symm
      _ ≤ C8 * ((L : ℝ) * lam ^ (1 / 6 : ℝ) + Real.sqrt (L : ℝ) * lam ^ (-(1 / 6 : ℝ))) := hs
  exact hmain

/-- per-sub-block phase bound with explicit `A₀,B₀` (used by the block Abel). -/
private lemma subphase_block_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P L : ℕ) (hP : 1 ≤ P) (hL : 1 ≤ L) (hLP : L ≤ P)
        {c : ℝ} (hc : 0 < c) (t : ℝ) (ht : 1 ≤ t),
        ∀ k : ℕ, 1 ≤ k → k ≤ L →
          let A₀ : ℝ := t ^ (1 / 6 : ℝ) * (Real.sqrt (c + (P : ℝ)))⁻¹
          let B₀ : ℝ := t ^ (-(1 / 6 : ℝ)) * Real.sqrt (c + ((P + L : ℕ) : ℝ))
          ‖∑ m ∈ Finset.Icc (P + 1) (P + k), sPhase c t (m : ℝ)‖ ≤
            C * ((k : ℝ) * A₀ + Real.sqrt (k : ℝ) * B₀) := by
  classical
  obtain ⟨Cph, hCph, hph⟩ := shifted_phase_block_nat
  refine ⟨2 * Cph, by positivity, ?_⟩
  intro P L hP hL hLP c hc t ht k hk1 hkL
  have hkP : k ≤ P := le_trans hkL hLP
  dsimp
  let A₀ : ℝ := t ^ (1 / 6 : ℝ) * (Real.sqrt (c + (P : ℝ)))⁻¹
  let B₀ : ℝ := t ^ (-(1 / 6 : ℝ)) * Real.sqrt (c + ((P + L : ℕ) : ℝ))
  let u : ℝ := c + ((P + k : ℕ) : ℝ)
  let lam : ℝ := t / (Real.pi * u ^ 3)
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hcP : 0 < c + (P : ℝ) := by nlinarith [hc, show 0 < (P : ℝ) by exact_mod_cast (by omega : 0 < P)]
  have hcPL : 0 < c + ((P + L : ℕ) : ℝ) := by
    have : 0 ≤ ((P + L : ℕ) : ℝ) := by positivity
    nlinarith [hc]
  have hu : 0 < u := by
    dsimp [u]
    have : 0 ≤ ((P + k : ℕ) : ℝ) := by positivity
    nlinarith [hc]
  have hden : 0 < Real.pi * u ^ 3 := by positivity
  have hlam1 : lam ^ (1 / 6 : ℝ) = t ^ (1 / 6 : ℝ) * (Real.pi * u ^ 3) ^ (-(1 / 6 : ℝ)) := by
    dsimp [lam]
    exact lambda_sixth (by linarith : 0 ≤ t) hden
  have hlam2 : lam ^ (-(1 / 6 : ℝ)) = t ^ (-(1 / 6 : ℝ)) * (Real.pi * u ^ 3) ^ (1 / 6 : ℝ) := by
    dsimp [lam]
    exact lambda_neg_sixth ht0 hden
  have hphk := hph (P := P) (L := k) hP hk1 hkP (c := c) hc t ht
  have hphk' : ‖∑ m ∈ Finset.Icc (P + 1) (P + k), sPhase c t (m : ℝ)‖ ≤
      Cph * ((k : ℝ) * lam ^ (1 / 6 : ℝ) + Real.sqrt (k : ℝ) * lam ^ (-(1 / 6 : ℝ))) := by
    simpa [lam, u] using hphk
  -- term bounds
  have hu_le_w : u ≤ c + ((P + L : ℕ) : ℝ) := by
    have hkLc : (k : ℝ) ≤ (L : ℝ) := by exact_mod_cast hkL
    dsimp [u]
    norm_num
    nlinarith
  have htermA : lam ^ (1 / 6 : ℝ) ≤ A₀ := by
    calc
      lam ^ (1 / 6 : ℝ) = t ^ (1 / 6 : ℝ) * (Real.pi * u ^ 3) ^ (-(1 / 6 : ℝ)) := hlam1
      _ = t ^ (1 / 6 : ℝ) * (Real.pi ^ (-(1 / 6 : ℝ)) * (Real.sqrt u)⁻¹) := by
          rw [mul_rpow_neg_sixth_invsqrt (by positivity : 0 ≤ Real.pi) hu]
      _ = t ^ (1 / 6 : ℝ) * Real.pi ^ (-(1 / 6 : ℝ)) * (Real.sqrt u)⁻¹ := by ring
      _ ≤ t ^ (1 / 6 : ℝ) * (Real.sqrt u)⁻¹ := by
          have hle : Real.pi ^ (-(1 / 6 : ℝ)) ≤ 1 := pi_neg_sixth_le_one
          have hx : 0 ≤ (Real.sqrt u)⁻¹ := by positivity
          have ht1 : 0 ≤ t ^ (1 / 6 : ℝ) := by positivity
          calc
            t ^ (1 / 6 : ℝ) * Real.pi ^ (-(1 / 6 : ℝ)) * (Real.sqrt u)⁻¹
                = t ^ (1 / 6 : ℝ) * (Real.pi ^ (-(1 / 6 : ℝ)) * (Real.sqrt u)⁻¹) := by ring
            _ ≤ t ^ (1 / 6 : ℝ) * (1 * (Real.sqrt u)⁻¹) := by
                exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle hx) ht1
            _ = t ^ (1 / 6 : ℝ) * (Real.sqrt u)⁻¹ := by ring
      _ ≤ t ^ (1 / 6 : ℝ) * (Real.sqrt (c + (P : ℝ)))⁻¹ := by
          have hcP_le_u : c + (P : ℝ) ≤ u := by
            dsimp [u]
            have hcPk : (P : ℝ) ≤ ((P + k : ℕ) : ℝ) := by
              exact_mod_cast (by omega : P ≤ P + k)
            nlinarith
          exact mul_le_mul_of_nonneg_left (inv_sqrt_le_inv_sqrt hcP hcP_le_u) (by positivity : 0 ≤ t ^ (1 / 6 : ℝ))
      _ = A₀ := by rfl
  have htermB : lam ^ (-(1 / 6 : ℝ)) ≤ 2 * B₀ := by
    calc
      lam ^ (-(1 / 6 : ℝ)) = t ^ (-(1 / 6 : ℝ)) * (Real.pi * u ^ 3) ^ (1 / 6 : ℝ) := hlam2
      _ = t ^ (-(1 / 6 : ℝ)) * (Real.pi ^ (1 / 6 : ℝ) * Real.sqrt u) := by
          rw [mul_rpow_sixth_sqrt (by positivity : 0 ≤ Real.pi) hu]
      _ ≤ t ^ (-(1 / 6 : ℝ)) * (2 * Real.sqrt (c + ((P + L : ℕ) : ℝ))) := by
          have hle : Real.pi ^ (1 / 6 : ℝ) * Real.sqrt u ≤ 2 * Real.sqrt (c + ((P + L : ℕ) : ℝ)) := by
            calc
              Real.pi ^ (1 / 6 : ℝ) * Real.sqrt u
                  ≤ 2 * Real.sqrt u := mul_le_mul_of_nonneg_right pi_sixth_le_two (Real.sqrt_nonneg u)
              _ ≤ 2 * Real.sqrt (c + ((P + L : ℕ) : ℝ)) :=
                  mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hu_le_w) (by norm_num)
          exact mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ t ^ (-(1 / 6 : ℝ)))
      _ = 2 * (t ^ (-(1 / 6 : ℝ)) * Real.sqrt (c + ((P + L : ℕ) : ℝ))) := by ring
      _ = 2 * B₀ := by rfl
  have hkA0 : (k : ℝ) * lam ^ (1 / 6 : ℝ) ≤ (k : ℝ) * A₀ := by
    exact mul_le_mul_of_nonneg_left htermA (by positivity : 0 ≤ (k : ℝ))
  have hkB0 : Real.sqrt (k : ℝ) * lam ^ (-(1 / 6 : ℝ)) ≤ 2 * (Real.sqrt (k : ℝ) * B₀) := by
    calc
      Real.sqrt (k : ℝ) * lam ^ (-(1 / 6 : ℝ))
          ≤ Real.sqrt (k : ℝ) * (2 * B₀) := mul_le_mul_of_nonneg_left htermB (Real.sqrt_nonneg (k : ℝ))
      _ = 2 * (Real.sqrt (k : ℝ) * B₀) := by ring
  have hsum : (k : ℝ) * lam ^ (1 / 6 : ℝ) + Real.sqrt (k : ℝ) * lam ^ (-(1 / 6 : ℝ)) ≤
      (k : ℝ) * A₀ + 2 * (Real.sqrt (k : ℝ) * B₀) := by
    exact add_le_add hkA0 hkB0
  have hposA : 0 ≤ (k : ℝ) * A₀ := by
    dsimp [A₀]
    positivity
  have hfin : Cph * ((k : ℝ) * lam ^ (1 / 6 : ℝ) + Real.sqrt (k : ℝ) * lam ^ (-(1 / 6 : ℝ))) ≤
      2 * Cph * ((k : ℝ) * A₀ + Real.sqrt (k : ℝ) * B₀) := by
    have h1 : Cph * ((k : ℝ) * lam ^ (1 / 6 : ℝ) + Real.sqrt (k : ℝ) * lam ^ (-(1 / 6 : ℝ))) ≤
        Cph * ((k : ℝ) * A₀ + 2 * (Real.sqrt (k : ℝ) * B₀)) := by
      exact mul_le_mul_of_nonneg_left hsum (le_of_lt hCph)
    have h2 : Cph * ((k : ℝ) * A₀ + 2 * (Real.sqrt (k : ℝ) * B₀)) ≤
        2 * Cph * ((k : ℝ) * A₀ + Real.sqrt (k : ℝ) * B₀) := by
      have h2a : 0 ≤ Cph * ((k : ℝ) * A₀) := mul_nonneg (le_of_lt hCph) hposA
      have h2b : 0 ≤ Cph * (2 * (Real.sqrt (k : ℝ) * B₀)) := by positivity
      nlinarith
    exact le_trans h1 h2
  calc
    ‖∑ m ∈ Finset.Icc (P + 1) (P + k), sPhase c t (m : ℝ)‖
        ≤ Cph * ((k : ℝ) * lam ^ (1 / 6 : ℝ) + Real.sqrt (k : ℝ) * lam ^ (-(1 / 6 : ℝ))) := hphk'
    _ ≤ 2 * Cph * ((k : ℝ) * A₀ + Real.sqrt (k : ℝ) * B₀) := hfin

/-! ### discrete Abel / telescoping over the block weight -/

/-- reindex: a sum over the block `(P, P+L]` equals the sum over `1..L` with `m ↦ P + m`. -/
private lemma sum_block_reindex {P L : ℕ} (hP : 1 ≤ P) (hL : 1 ≤ L) (f : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc (P + 1) (P + L), f m) = ∑ n ∈ Finset.Icc 1 L, f (P + n) := by
  classical
  refine Finset.sum_bij (fun m hm => m - P) ?_ ?_ ?_ ?_
  · intro m hm
    have hm1 : P + 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm2 : m ≤ P + L := (Finset.mem_Icc.mp hm).2
    simp only [Finset.mem_Icc]
    constructor <;> omega
  · intro a1 ha1 a2 ha2 h
    have ha11 : P + 1 ≤ a1 := (Finset.mem_Icc.mp ha1).1
    have ha21 : P + 1 ≤ a2 := (Finset.mem_Icc.mp ha2).1
    omega
  · intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn2 : n ≤ L := (Finset.mem_Icc.mp hn).2
    refine ⟨n + P, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      constructor <;> omega
    · omega
  · intro m hm
    congr 1
    have hm1 : P + 1 ≤ m := (Finset.mem_Icc.mp hm).1
    omega

/-- `k ≤ L − 1` with `1 ≤ L` implies `k < L`. -/
private lemma lt_of_le_sub_one {k L : ℕ} (hL : 1 ≤ L) (hk : k ≤ L - 1) : k < L := by
  exact Nat.lt_of_succ_le (by simpa [Nat.sub_add_cancel hL] using Nat.succ_le_succ hk)

/-- telescoping `Σ_{k=1}^{L−1}(w k − w(k+1)) = w 1 − w L`. -/
private lemma sum_wdiff_telescope {L : ℕ} (hL : 1 ≤ L) (w : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 (L - 1), (w k - w (k + 1))) = w 1 - w L := by
  have hconv : (∑ k ∈ Finset.Icc 1 (L - 1), (w k - w (k + 1))) =
      ∑ i ∈ Finset.range (L - 1), (w (i + 1) - w (i + 2)) := by
    simpa [Nat.add_assoc] using
      (TdtAbelRhs.sum_Icc_one_shift (fun k : ℕ => w k - w (k + 1)) (L - 1))
  have ht := Finset.sum_range_sub' (fun j : ℕ => w (j + 1)) (L - 1)
  have hcast : (L - 1) + 1 = L := by omega
  calc
    (∑ k ∈ Finset.Icc 1 (L - 1), (w k - w (k + 1)))
        = ∑ i ∈ Finset.range (L - 1), (w (i + 1) - w (i + 2)) := hconv
    _ = w 1 - w ((L - 1) + 1) := by simpa using ht
    _ = w 1 - w L := by rw [hcast]

/-- `(L·w_L + Σ k·(w_k − w_{k+1})) ≤ L·w_1` for a decreasing weight. -/
private lemma block_sum_bound_nat {L : ℕ} (hL : 1 ≤ L) (w : ℕ → ℝ)
    (hwdec : ∀ k, 1 ≤ k → k < L → w (k + 1) ≤ w k) :
    (∑ k ∈ Finset.Icc 1 (L - 1), (k : ℝ) * (w k - w (k + 1))) + (L : ℝ) * w L ≤
      (L : ℝ) * w 1 := by
  have htel := sum_wdiff_telescope hL w
  have hsub : (∑ k ∈ Finset.Icc 1 (L - 1), (k : ℝ) * (w k - w (k + 1))) ≤
      (L : ℝ) * (∑ k ∈ Finset.Icc 1 (L - 1), (w k - w (k + 1))) := by
    calc
      (∑ k ∈ Finset.Icc 1 (L - 1), (k : ℝ) * (w k - w (k + 1)))
          ≤ ∑ k ∈ Finset.Icc 1 (L - 1), (L : ℝ) * (w k - w (k + 1)) := by
              apply Finset.sum_le_sum
              intro k hk
              have hk1b : 1 ≤ k := (Finset.mem_Icc.mp hk).1
              have hkLb : k ≤ L - 1 := (Finset.mem_Icc.mp hk).2
              have hkL : (k : ℝ) ≤ (L : ℝ) := by
                exact_mod_cast (le_of_lt (lt_of_le_sub_one hL hkLb))
              have hpos : 0 ≤ w k - w (k + 1) := by
                linarith [hwdec k hk1b (lt_of_le_sub_one hL hkLb)]
              exact mul_le_mul_of_nonneg_right hkL hpos
      _ = (L : ℝ) * (∑ k ∈ Finset.Icc 1 (L - 1), (w k - w (k + 1))) := by
          rw [Finset.mul_sum]
  calc
    (∑ k ∈ Finset.Icc 1 (L - 1), (k : ℝ) * (w k - w (k + 1))) + (L : ℝ) * w L
        ≤ (L : ℝ) * (∑ k ∈ Finset.Icc 1 (L - 1), (w k - w (k + 1))) + (L : ℝ) * w L := by
            nlinarith [hsub]
    _ = (L : ℝ) * (w 1 - w L) + (L : ℝ) * w L := by rw [htel]
    _ = (L : ℝ) * w 1 := by ring

/-- `(√L·w_L + Σ √k·(w_k − w_{k+1})) ≤ √L·w_1` for a decreasing weight. -/
private lemma block_sum_bound_sqrt {L : ℕ} (hL : 1 ≤ L) (w : ℕ → ℝ)
    (hwdec : ∀ k, 1 ≤ k → k < L → w (k + 1) ≤ w k) :
    (∑ k ∈ Finset.Icc 1 (L - 1), Real.sqrt (k : ℝ) * (w k - w (k + 1))) +
        Real.sqrt (L : ℝ) * w L ≤ Real.sqrt (L : ℝ) * w 1 := by
  have htel := sum_wdiff_telescope hL w
  have hsub : (∑ k ∈ Finset.Icc 1 (L - 1), Real.sqrt (k : ℝ) * (w k - w (k + 1))) ≤
      Real.sqrt (L : ℝ) * (∑ k ∈ Finset.Icc 1 (L - 1), (w k - w (k + 1))) := by
    calc
      (∑ k ∈ Finset.Icc 1 (L - 1), Real.sqrt (k : ℝ) * (w k - w (k + 1)))
          ≤ ∑ k ∈ Finset.Icc 1 (L - 1), Real.sqrt (L : ℝ) * (w k - w (k + 1)) := by
              apply Finset.sum_le_sum
              intro k hk
              have hk1b : 1 ≤ k := (Finset.mem_Icc.mp hk).1
              have hkLb : k ≤ L - 1 := (Finset.mem_Icc.mp hk).2
              have hkL : Real.sqrt (k : ℝ) ≤ Real.sqrt (L : ℝ) := by
                exact Real.sqrt_le_sqrt (by exact_mod_cast (le_of_lt (lt_of_le_sub_one hL hkLb)))
              have hpos : 0 ≤ w k - w (k + 1) := by
                linarith [hwdec k hk1b (lt_of_le_sub_one hL hkLb)]
              exact mul_le_mul_of_nonneg_right hkL hpos
      _ = Real.sqrt (L : ℝ) * (∑ k ∈ Finset.Icc 1 (L - 1), (w k - w (k + 1))) := by
          rw [Finset.mul_sum]
  calc
    (∑ k ∈ Finset.Icc 1 (L - 1), Real.sqrt (k : ℝ) * (w k - w (k + 1))) +
        Real.sqrt (L : ℝ) * w L
        ≤ Real.sqrt (L : ℝ) * (∑ k ∈ Finset.Icc 1 (L - 1), (w k - w (k + 1))) +
            Real.sqrt (L : ℝ) * w L := by
            nlinarith [hsub]
    _ = Real.sqrt (L : ℝ) * (w 1 - w L) + Real.sqrt (L : ℝ) * w L := by rw [htel]
    _ = Real.sqrt (L : ℝ) * w 1 := by ring

/-- `Σ_{i=1}^{L} w_i ≤ L·w_1` for a nonincreasing nonneg weight. -/
private lemma sum_weight_le {L : ℕ} (hL : 1 ≤ L) {w : ℕ → ℝ}
    (hw : ∀ i, 1 ≤ i → i ≤ L → w i ≤ w 1) (hw1 : 0 ≤ w 1) :
    (∑ i ∈ Finset.Icc 1 L, w i) ≤ (L : ℝ) * w 1 := by
  calc
    (∑ i ∈ Finset.Icc 1 L, w i) ≤ ∑ i ∈ Finset.Icc 1 L, w 1 := by
      apply Finset.sum_le_sum
      intro i hi
      exact hw i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
    _ = (L : ℝ) * w 1 := by
      have hsh := TdtAbelRhs.sum_Icc_one_shift (fun i : ℕ => w 1) L
      rw [hsh]
      simp

/-- `Σ_{i=1}^{L} (√i−√(i−1))·w_i ≤ √L·w_1` for a nonincreasing nonneg weight. -/
private lemma sum_sqrt_diff_weight_le {L : ℕ} (hL : 1 ≤ L) {w : ℕ → ℝ}
    (hw : ∀ i, 1 ≤ i → i ≤ L → w i ≤ w 1) (hw1 : 0 ≤ w 1) :
    (∑ i ∈ Finset.Icc 1 L, (Real.sqrt (i : ℝ) - Real.sqrt ((i - 1 : ℕ) : ℝ)) * w i) ≤
      Real.sqrt (L : ℝ) * w 1 := by
  have htel : (∑ i ∈ Finset.Icc 1 L, (Real.sqrt (i : ℝ) - Real.sqrt ((i - 1 : ℕ) : ℝ))) =
      Real.sqrt (L : ℝ) := by
    have hsh := TdtAbelRhs.sum_Icc_one_shift
      (fun i : ℕ => Real.sqrt (i : ℝ) - Real.sqrt ((i - 1 : ℕ) : ℝ)) L
    have ht := Finset.sum_range_sub (fun j : ℕ => Real.sqrt (j : ℝ)) L
    calc
      (∑ i ∈ Finset.Icc 1 L, (Real.sqrt (i : ℝ) - Real.sqrt ((i - 1 : ℕ) : ℝ)))
          = ∑ j ∈ Finset.range L, (Real.sqrt ((j + 1 : ℕ) : ℝ) -
              Real.sqrt ((((j + 1) : ℕ) - 1 : ℕ) : ℝ)) := hsh
      _ = ∑ j ∈ Finset.range L, (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hcast : ((j + 1 : ℕ) - 1 : ℕ) = j := by omega
          rw [hcast]
      _ = Real.sqrt (L : ℝ) - Real.sqrt (0 : ℝ) := by simpa using ht
      _ = Real.sqrt (L : ℝ) := by simp
  calc
    (∑ i ∈ Finset.Icc 1 L, (Real.sqrt (i : ℝ) - Real.sqrt ((i - 1 : ℕ) : ℝ)) * w i)
        ≤ ∑ i ∈ Finset.Icc 1 L, (Real.sqrt (i : ℝ) - Real.sqrt ((i - 1 : ℕ) : ℝ)) * w 1 := by
            apply Finset.sum_le_sum
            intro i hi
            have hcoef : 0 ≤ Real.sqrt (i : ℝ) - Real.sqrt ((i - 1 : ℕ) : ℝ) := by
              have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
              have hle : Real.sqrt ((i - 1 : ℕ) : ℝ) ≤ Real.sqrt (i : ℝ) := by
                exact Real.sqrt_le_sqrt (by
                  have hcast : ((i - 1 : ℕ) : ℝ) ≤ (i : ℝ) := by
                    have hi1' : 1 ≤ i := (Finset.mem_Icc.mp hi).1
                    rw [Nat.cast_sub hi1']
                    linarith
                  exact hcast)
              linarith
            exact mul_le_mul_of_nonneg_left (hw i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2) hcoef
    _ = (∑ i ∈ Finset.Icc 1 L, (Real.sqrt (i : ℝ) - Real.sqrt ((i - 1 : ℕ) : ℝ))) * w 1 := by
            rw [Finset.sum_mul]
    _ = Real.sqrt (L : ℝ) * w 1 := by rw [htel]

/-! ### the weighted partial-block bound (uniform in `c`) -/

/-- **Weighted (amplitude-included) partial-block bound, uniform in `c`.**  For
`1 ≤ L ≤ P`, `c > 0`, `t ≥ 1`:

    |Σ_{P<m≤P+L} (c+m)^{−1/2−it}| ≤ C·( t^{1/6} + t^{−1/6}·√(P+L) ) . -/
private theorem weighted_block_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P L : ℕ) (hP : 1 ≤ P) (hL : 1 ≤ L) (hLP : L ≤ P)
        {c : ℝ} (hc : 0 < c) (t : ℝ) (ht : 1 ≤ t),
        ‖∑ m ∈ Finset.Icc (P + 1) (P + L), sSummand c t (m : ℝ)‖ ≤
          C * (t ^ (1 / 6 : ℝ) + t ^ (-(1 / 6 : ℝ)) * Real.sqrt ((P + L : ℕ) : ℝ)) := by
  classical
  obtain ⟨Csub, hCsub, hsub⟩ := subphase_block_bound
  refine ⟨2 * Csub, by positivity, ?_⟩
  intro P L hP hL hLP c hc t ht
  let a : ℕ → ℂ := fun n => sPhase c t (((P + n : ℕ) : ℝ))
  let w : ℕ → ℝ := fun n => (Real.sqrt (c + (((P + n : ℕ) : ℝ))))⁻¹
  let A₀ : ℝ := t ^ (1 / 6 : ℝ) * (Real.sqrt (c + (P : ℝ)))⁻¹
  let B₀ : ℝ := t ^ (-(1 / 6 : ℝ)) * Real.sqrt (c + ((P + L : ℕ) : ℝ))
  have hP0 : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hc0 : 0 ≤ c := le_of_lt hc
  have hcP : 0 < c + (P : ℝ) := by nlinarith
  have hcPL : 0 < c + ((P + L : ℕ) : ℝ) := by
    have h1 : 0 ≤ ((P + L : ℕ) : ℝ) := by positivity
    nlinarith [hc]
  have hA0 : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hB0 : 0 ≤ B₀ := by dsimp [B₀]; positivity
  -- the weight is nonnegative and decreasing
  have hw0 : ∀ k, 1 ≤ k → k ≤ L → 0 ≤ w k := by
    intro k hk1 hkL
    dsimp [w]
    positivity
  have hwdec : ∀ k, 1 ≤ k → k < L → w (k + 1) ≤ w k := by
    intro k hk1 hkL
    dsimp [w]
    have h1 : 0 < c + (((P + (k + 1) : ℕ)) : ℝ) := by positivity
    have h2 : 0 < c + (((P + k : ℕ)) : ℝ) := by positivity
    have hle : c + (((P + k : ℕ)) : ℝ) ≤ c + (((P + (k + 1) : ℕ)) : ℝ) := by
      have hcast : (P + k : ℕ) ≤ P + (k + 1) := by omega
      have hc2 : ((P + k : ℕ) : ℝ) ≤ ((P + (k + 1) : ℕ) : ℝ) := by exact_mod_cast hcast
      linarith
    have hsq : Real.sqrt (c + (((P + k : ℕ)) : ℝ)) ≤ Real.sqrt (c + (((P + (k + 1) : ℕ)) : ℝ)) :=
      Real.sqrt_le_sqrt hle
    exact (inv_le_inv₀ (Real.sqrt_pos.mpr h1) (Real.sqrt_pos.mpr h2)).mpr hsq
  -- block sum = Abel-weighted sum
  have hrewrite : (∑ m ∈ Finset.Icc (P + 1) (P + L), sSummand c t (m : ℝ)) =
      ∑ n ∈ Finset.Icc 1 L, a n * (w n : ℂ) := by
    have hr := sum_block_reindex hP hL (fun m : ℕ => sSummand c t (m : ℝ))
    rw [hr]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [a, w]
    rw [sSummand_eq_mul]
    simp [amp]
  have hab := TdtAbel.abel_weighted_bound hL a w hw0 hwdec
  -- per-subblock phase sums (Csub-bounded, in A₀/B₀ form)
  have hsubk : ∀ k : ℕ, 1 ≤ k → k ≤ L →
      ‖∑ n ∈ Finset.Icc 1 k, a n‖ ≤ Csub * ((k : ℝ) * A₀ + Real.sqrt (k : ℝ) * B₀) := by
    intro k hk1 hkL
    have hkP : k ≤ P := le_trans hkL hLP
    have hz := hsub P L hP hL hLP hc t ht k hk1 hkL
    have hnrm : ‖∑ n ∈ Finset.Icc 1 k, a n‖ =
        ‖∑ m ∈ Finset.Icc (P + 1) (P + k), sPhase c t (m : ℝ)‖ := by
      have hr := sum_block_reindex hP (by omega : 1 ≤ k) (fun m : ℕ => sPhase c t (m : ℝ))
      rw [← hr]
    dsimp [A₀, B₀] at hz ⊢
    rwa [hnrm]
  -- block-sum coefficient bounds
  have hbndA : (∑ k ∈ Finset.Icc 1 (L - 1), (k : ℝ) * (w k - w (k + 1))) + (L : ℝ) * w L ≤
      (L : ℝ) * w 1 := by
    simpa [add_comm] using (block_sum_bound_nat hL w hwdec)
  have hbndB : (∑ k ∈ Finset.Icc 1 (L - 1), Real.sqrt (k : ℝ) * (w k - w (k + 1))) +
      Real.sqrt (L : ℝ) * w L ≤ Real.sqrt (L : ℝ) * w 1 := by
    simpa [add_comm] using (block_sum_bound_sqrt hL w hwdec)
  -- the Abel bound with sub-block bounds substituted
  have hAbel : ‖∑ n ∈ Finset.Icc 1 L, a n * (w n : ℂ)‖ ≤
      Csub * (A₀ * ((L : ℝ) * w 1) + B₀ * (Real.sqrt (L : ℝ) * w 1)) := by
    -- intermediate: Csub·(A0·L·wL + B0·√L·wL) + Csub·(A0·S1 + B0·S2)
    have htermX : ‖∑ n ∈ Finset.Icc 1 L, a n‖ * w L ≤
        Csub * ((L : ℝ) * A₀ * w L + Real.sqrt (L : ℝ) * B₀ * w L) := by
      have hb := hsubk L hL le_rfl
      have hc : Csub * ((L : ℝ) * A₀ + Real.sqrt (L : ℝ) * B₀) * w L ≤
          Csub * ((L : ℝ) * A₀ * w L + Real.sqrt (L : ℝ) * B₀ * w L) := by
        nlinarith [hCsub.le, hA0, hB0, hw0 L hL le_rfl]
      exact le_trans (mul_le_mul_of_nonneg_right hb (hw0 L hL le_rfl)) hc
    have htermY : (∑ k ∈ Finset.Icc 1 (L - 1), ‖∑ n ∈ Finset.Icc 1 k, a n‖ * (w k - w (k + 1))) ≤
        Csub * (A₀ * (∑ k ∈ Finset.Icc 1 (L - 1), (k : ℝ) * (w k - w (k + 1))) +
          B₀ * (∑ k ∈ Finset.Icc 1 (L - 1), Real.sqrt (k : ℝ) * (w k - w (k + 1)))) := by
      have hstep : (∑ k ∈ Finset.Icc 1 (L - 1), Csub * ((k : ℝ) * A₀ + Real.sqrt (k : ℝ) * B₀) * (w k - w (k + 1)))
          = Csub * (A₀ * (∑ k ∈ Finset.Icc 1 (L - 1), (k : ℝ) * (w k - w (k + 1))) +
            B₀ * (∑ k ∈ Finset.Icc 1 (L - 1), Real.sqrt (k : ℝ) * (w k - w (k + 1)))) := by
          calc
            (∑ k ∈ Finset.Icc 1 (L - 1), Csub * ((k : ℝ) * A₀ + Real.sqrt (k : ℝ) * B₀) * (w k - w (k + 1)))
                = (∑ k ∈ Finset.Icc 1 (L - 1), Csub * (((k : ℝ) * A₀ + Real.sqrt (k : ℝ) * B₀) * (w k - w (k + 1)))) := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    ring
            _ = Csub * (∑ k ∈ Finset.Icc 1 (L - 1), (((k : ℝ) * A₀ + Real.sqrt (k : ℝ) * B₀) * (w k - w (k + 1)))) := by
                    rw [← Finset.mul_sum]
            _ = Csub * (∑ k ∈ Finset.Icc 1 (L - 1), (((k : ℝ) * A₀) * (w k - w (k + 1)) +
                ((Real.sqrt (k : ℝ) * B₀) * (w k - w (k + 1))))) := by
                    apply congrArg (fun x : ℝ => Csub * x)
                    apply Finset.sum_congr rfl
                    intro k hk
                    ring
            _ = Csub * ((∑ k ∈ Finset.Icc 1 (L - 1), ((k : ℝ) * A₀) * (w k - w (k + 1))) +
                (∑ k ∈ Finset.Icc 1 (L - 1), (Real.sqrt (k : ℝ) * B₀) * (w k - w (k + 1)))) := by
                    apply congrArg (fun x : ℝ => Csub * x)
                    rw [Finset.sum_add_distrib]
            _ = Csub * (A₀ * (∑ k ∈ Finset.Icc 1 (L - 1), (k : ℝ) * (w k - w (k + 1))) +
                B₀ * (∑ k ∈ Finset.Icc 1 (L - 1), Real.sqrt (k : ℝ) * (w k - w (k + 1)))) := by
                    apply congrArg (fun x : ℝ => Csub * x)
                    congr 1
                    · rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro k hk
                      ring
                    · rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro k hk
                      ring
      calc
        (∑ k ∈ Finset.Icc 1 (L - 1), ‖∑ n ∈ Finset.Icc 1 k, a n‖ * (w k - w (k + 1)))
            ≤ ∑ k ∈ Finset.Icc 1 (L - 1), Csub * ((k : ℝ) * A₀ + Real.sqrt (k : ℝ) * B₀) * (w k - w (k + 1)) := by
                apply Finset.sum_le_sum
                intro k hk
                have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
                have hkL' : k < L := lt_of_le_sub_one hL (Finset.mem_Icc.mp hk).2
                have hkL : k ≤ L := le_of_lt hkL'
                have hdiff : 0 ≤ w k - w (k + 1) := by
                  linarith [hwdec k hk1 hkL']
                exact mul_le_mul_of_nonneg_right (hsubk k hk1 hkL) hdiff
        _ = Csub * (A₀ * (∑ k ∈ Finset.Icc 1 (L - 1), (k : ℝ) * (w k - w (k + 1))) +
            B₀ * (∑ k ∈ Finset.Icc 1 (L - 1), Real.sqrt (k : ℝ) * (w k - w (k + 1)))) := hstep
    have hAcomb : A₀ * (∑ k ∈ Finset.Icc 1 (L - 1), (k : ℝ) * (w k - w (k + 1))) +
        (L : ℝ) * A₀ * w L ≤ A₀ * ((L : ℝ) * w 1) := by
      have hA1 : A₀ * ((∑ k ∈ Finset.Icc 1 (L - 1), (k : ℝ) * (w k - w (k + 1))) + (L : ℝ) * w L) ≤
          A₀ * ((L : ℝ) * w 1) := mul_le_mul_of_nonneg_left hbndA hA0
      nlinarith
    have hBcomb : B₀ * (∑ k ∈ Finset.Icc 1 (L - 1), Real.sqrt (k : ℝ) * (w k - w (k + 1))) +
        Real.sqrt (L : ℝ) * B₀ * w L ≤ B₀ * (Real.sqrt (L : ℝ) * w 1) := by
      have hB1 : B₀ * ((∑ k ∈ Finset.Icc 1 (L - 1), Real.sqrt (k : ℝ) * (w k - w (k + 1))) + Real.sqrt (L : ℝ) * w L) ≤
          B₀ * (Real.sqrt (L : ℝ) * w 1) := mul_le_mul_of_nonneg_left hbndB hB0
      nlinarith
    calc
      ‖∑ n ∈ Finset.Icc 1 L, a n * (w n : ℂ)‖
          ≤ ‖∑ n ∈ Finset.Icc 1 L, a n‖ * w L +
              (∑ k ∈ Finset.Icc 1 (L - 1), ‖∑ n ∈ Finset.Icc 1 k, a n‖ * (w k - w (k + 1))) := hab
      _ ≤ Csub * ((L : ℝ) * A₀ * w L + Real.sqrt (L : ℝ) * B₀ * w L) +
              Csub * (A₀ * (∑ k ∈ Finset.Icc 1 (L - 1), (k : ℝ) * (w k - w (k + 1))) +
                B₀ * (∑ k ∈ Finset.Icc 1 (L - 1), Real.sqrt (k : ℝ) * (w k - w (k + 1)))) := by
              exact add_le_add htermX htermY
      _ = Csub * (A₀ * ((∑ k ∈ Finset.Icc 1 (L - 1), (k : ℝ) * (w k - w (k + 1))) + (L : ℝ) * w L) +
              B₀ * ((∑ k ∈ Finset.Icc 1 (L - 1), Real.sqrt (k : ℝ) * (w k - w (k + 1))) + Real.sqrt (L : ℝ) * w L)) := by
              ring
      _ ≤ Csub * (A₀ * ((L : ℝ) * w 1) + B₀ * (Real.sqrt (L : ℝ) * w 1)) := by
              have hc : A₀ * ((∑ k ∈ Finset.Icc 1 (L - 1), (k : ℝ) * (w k - w (k + 1))) + (L : ℝ) * w L) +
                  B₀ * ((∑ k ∈ Finset.Icc 1 (L - 1), Real.sqrt (k : ℝ) * (w k - w (k + 1))) + Real.sqrt (L : ℝ) * w L) ≤
                  A₀ * ((L : ℝ) * w 1) + B₀ * (Real.sqrt (L : ℝ) * w 1) := by
                  nlinarith [hAcomb, hBcomb]
              exact mul_le_mul_of_nonneg_left hc (le_of_lt hCsub)
  -- bound (L·w₁,A₀) and (√L·w₁,B₀) pieces
  have hw1le : w 1 ≤ (Real.sqrt (c + (P : ℝ)))⁻¹ := by
    dsimp [w]
    have hc1 : 0 < c + ((P + 1 : ℕ) : ℝ) := by positivity
    have hle : c + (P : ℝ) ≤ c + ((P + 1 : ℕ) : ℝ) := by
      have hcast : (P : ℝ) ≤ ((P + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : P ≤ P + 1)
      linarith
    have hsq : Real.sqrt (c + (P : ℝ)) ≤ Real.sqrt (c + ((P + 1 : ℕ) : ℝ)) :=
      Real.sqrt_le_sqrt hle
    exact (inv_le_inv₀ (Real.sqrt_pos.mpr hc1) (Real.sqrt_pos.mpr hcP)).mpr hsq
  have hLle_cP : (L : ℝ) ≤ c + (P : ℝ) := by
    have hLP' : (L : ℝ) ≤ (P : ℝ) := by exact_mod_cast hLP
    nlinarith
  have hL0r : 0 ≤ (L : ℝ) := by positivity
  have hsqrtL_le : Real.sqrt (L : ℝ) ≤ Real.sqrt ((P + L : ℕ) : ℝ) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : L ≤ P + L))
  have hsqr2 : Real.sqrt (c + ((P + L : ℕ) : ℝ)) ≤ Real.sqrt 2 * Real.sqrt (c + (P : ℝ)) := by
    have hinner : c + ((P + L : ℕ) : ℝ) ≤ 2 * (c + (P : ℝ)) := by
      have hcast : ((P + L : ℕ) : ℝ) = (P : ℝ) + (L : ℝ) := by exact_mod_cast (by omega : P + L = P + L)
      rw [hcast]
      nlinarith [hLle_cP]
    calc
      Real.sqrt (c + ((P + L : ℕ) : ℝ)) ≤ Real.sqrt (2 * (c + (P : ℝ))) := Real.sqrt_le_sqrt hinner
      _ = Real.sqrt 2 * Real.sqrt (c + (P : ℝ)) := by
          rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)) (c + (P : ℝ))]
  have hfinA : (L : ℝ) * A₀ * w 1 ≤ t ^ (1 / 6 : ℝ) := by
    dsimp [A₀]
    have h1 : (L : ℝ) * (t ^ (1 / 6 : ℝ) * (Real.sqrt (c + (P : ℝ)))⁻¹) * w 1 ≤
        (L : ℝ) * (t ^ (1 / 6 : ℝ) * (Real.sqrt (c + (P : ℝ)))⁻¹) * (Real.sqrt (c + (P : ℝ)))⁻¹ := by
      exact mul_le_mul_of_nonneg_left hw1le (by positivity)
    have h2 : (L : ℝ) * (t ^ (1 / 6 : ℝ) * (Real.sqrt (c + (P : ℝ)))⁻¹) * (Real.sqrt (c + (P : ℝ)))⁻¹ ≤
        t ^ (1 / 6 : ℝ) := by
      have hmult : (Real.sqrt (c + (P : ℝ)))⁻¹ * (Real.sqrt (c + (P : ℝ)))⁻¹ = (c + (P : ℝ))⁻¹ := by
        calc
          (Real.sqrt (c + (P : ℝ)))⁻¹ * (Real.sqrt (c + (P : ℝ)))⁻¹
              = (Real.sqrt (c + (P : ℝ)) * Real.sqrt (c + (P : ℝ)))⁻¹ := by
                  field_simp [ne_of_gt (Real.sqrt_pos.mpr hcP)]
          _ = (c + (P : ℝ))⁻¹ := by rw [Real.mul_self_sqrt (le_of_lt hcP)]
      have hfrac : (L : ℝ) / (c + (P : ℝ)) ≤ 1 := by
        exact (div_le_one hcP).mpr hLle_cP
      calc
        (L : ℝ) * (t ^ (1 / 6 : ℝ) * (Real.sqrt (c + (P : ℝ)))⁻¹) * (Real.sqrt (c + (P : ℝ)))⁻¹
            = t ^ (1 / 6 : ℝ) * ((L : ℝ) * ((Real.sqrt (c + (P : ℝ)))⁻¹ * (Real.sqrt (c + (P : ℝ)))⁻¹)) := by ring
        _ = t ^ (1 / 6 : ℝ) * ((L : ℝ) * (c + (P : ℝ))⁻¹) := by rw [hmult]
        _ = t ^ (1 / 6 : ℝ) * ((L : ℝ) / (c + (P : ℝ))) := by
            rw [div_eq_mul_inv]
            ring
        _ ≤ t ^ (1 / 6 : ℝ) * 1 := by
            exact mul_le_mul_of_nonneg_left hfrac (by positivity : 0 ≤ t ^ (1 / 6 : ℝ))
        _ = t ^ (1 / 6 : ℝ) := by ring
    exact le_trans h1 h2
  have hfinB : Real.sqrt (L : ℝ) * B₀ * w 1 ≤
      Real.sqrt 2 * (t ^ (-(1 / 6 : ℝ)) * Real.sqrt ((P + L : ℕ) : ℝ)) := by
    dsimp [B₀]
    have h1 : Real.sqrt (L : ℝ) * (t ^ (-(1 / 6 : ℝ)) * Real.sqrt (c + ((P + L : ℕ) : ℝ))) * w 1 ≤
        Real.sqrt (L : ℝ) * (t ^ (-(1 / 6 : ℝ)) * Real.sqrt (c + ((P + L : ℕ) : ℝ))) * (Real.sqrt (c + (P : ℝ)))⁻¹ := by
      exact mul_le_mul_of_nonneg_left hw1le (by positivity)
    have h2 : Real.sqrt (L : ℝ) * (t ^ (-(1 / 6 : ℝ)) * Real.sqrt (c + ((P + L : ℕ) : ℝ))) * (Real.sqrt (c + (P : ℝ)))⁻¹ ≤
        Real.sqrt 2 * (t ^ (-(1 / 6 : ℝ)) * Real.sqrt ((P + L : ℕ) : ℝ)) := by
      have hcore : Real.sqrt (c + ((P + L : ℕ) : ℝ)) * (Real.sqrt (c + (P : ℝ)))⁻¹ ≤ Real.sqrt 2 := by
        have hpp : 0 < Real.sqrt (c + (P : ℝ)) := Real.sqrt_pos.mpr hcP
        calc
          Real.sqrt (c + ((P + L : ℕ) : ℝ)) * (Real.sqrt (c + (P : ℝ)))⁻¹
              ≤ (Real.sqrt 2 * Real.sqrt (c + (P : ℝ))) * (Real.sqrt (c + (P : ℝ)))⁻¹ := by
                  exact mul_le_mul_of_nonneg_right hsqr2 (by positivity : 0 ≤ (Real.sqrt (c + (P : ℝ)))⁻¹)
          _ = Real.sqrt 2 * (Real.sqrt (c + (P : ℝ)) * (Real.sqrt (c + (P : ℝ)))⁻¹) := by ring
          _ = Real.sqrt 2 := by
              field_simp [ne_of_gt hpp]
      have h2a : Real.sqrt (L : ℝ) ≤ Real.sqrt ((P + L : ℕ) : ℝ) := hsqrtL_le
      have h2b : 0 ≤ t ^ (-(1 / 6 : ℝ)) * Real.sqrt ((P + L : ℕ) : ℝ) := by positivity
      calc
        Real.sqrt (L : ℝ) * (t ^ (-(1 / 6 : ℝ)) * Real.sqrt (c + ((P + L : ℕ) : ℝ))) * (Real.sqrt (c + (P : ℝ)))⁻¹
            = (t ^ (-(1 / 6 : ℝ)) * Real.sqrt (L : ℝ)) * (Real.sqrt (c + ((P + L : ℕ) : ℝ)) * (Real.sqrt (c + (P : ℝ)))⁻¹) := by ring
        _ ≤ (t ^ (-(1 / 6 : ℝ)) * Real.sqrt (L : ℝ)) * Real.sqrt 2 := by
            exact mul_le_mul_of_nonneg_left hcore (by positivity : 0 ≤ t ^ (-(1 / 6 : ℝ)) * Real.sqrt (L : ℝ))
        _ = Real.sqrt 2 * (t ^ (-(1 / 6 : ℝ)) * Real.sqrt (L : ℝ)) := by ring
        _ ≤ Real.sqrt 2 * (t ^ (-(1 / 6 : ℝ)) * Real.sqrt ((P + L : ℕ) : ℝ)) := by
            have hm : t ^ (-(1 / 6 : ℝ)) * Real.sqrt (L : ℝ) ≤
                t ^ (-(1 / 6 : ℝ)) * Real.sqrt ((P + L : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left h2a (by positivity : 0 ≤ t ^ (-(1 / 6 : ℝ)))
            exact mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ Real.sqrt 2)
    exact le_trans h1 h2
  have hw1pos : 0 ≤ w 1 := hw0 1 (by norm_num) (by omega)
  have hsummain : A₀ * ((L : ℝ) * w 1) + B₀ * (Real.sqrt (L : ℝ) * w 1) ≤
      t ^ (1 / 6 : ℝ) + Real.sqrt 2 * (t ^ (-(1 / 6 : ℝ)) * Real.sqrt ((P + L : ℕ) : ℝ)) := by
    have hAw1 : A₀ * ((L : ℝ) * w 1) ≤ t ^ (1 / 6 : ℝ) := by
      have hx : A₀ * ((L : ℝ) * w 1) = (L : ℝ) * A₀ * w 1 := by ring
      rw [hx]
      exact hfinA
    have hBw1 : B₀ * (Real.sqrt (L : ℝ) * w 1) ≤ Real.sqrt 2 * (t ^ (-(1 / 6 : ℝ)) * Real.sqrt ((P + L : ℕ) : ℝ)) := by
      have hx : B₀ * (Real.sqrt (L : ℝ) * w 1) = Real.sqrt (L : ℝ) * B₀ * w 1 := by ring
      rw [hx]
      exact hfinB
    exact add_le_add hAw1 hBw1
  calc
    ‖∑ m ∈ Finset.Icc (P + 1) (P + L), sSummand c t (m : ℝ)‖
        = ‖∑ n ∈ Finset.Icc 1 L, a n * (w n : ℂ)‖ := by rw [hrewrite]
    _ ≤ Csub * (A₀ * ((L : ℝ) * w 1) + B₀ * (Real.sqrt (L : ℝ) * w 1)) := hAbel
    _ ≤ Csub * (t ^ (1 / 6 : ℝ) + Real.sqrt 2 * (t ^ (-(1 / 6 : ℝ)) * Real.sqrt ((P + L : ℕ) : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hsummain (le_of_lt hCsub)
    _ = Csub * t ^ (1 / 6 : ℝ) + Csub * (Real.sqrt 2 * (t ^ (-(1 / 6 : ℝ)) * Real.sqrt ((P + L : ℕ) : ℝ))) := by ring
    _ ≤ (2 * Csub) * (t ^ (1 / 6 : ℝ) + t ^ (-(1 / 6 : ℝ)) * Real.sqrt ((P + L : ℕ) : ℝ)) := by
        have hpos1 : 0 ≤ Csub * t ^ (1 / 6 : ℝ) := by positivity
        have hpos2 : 0 ≤ Csub * (t ^ (-(1 / 6 : ℝ)) * Real.sqrt ((P + L : ℕ) : ℝ)) := by positivity
        have hsqrt2 : Real.sqrt 2 ≤ 2 := by
          have hsq4 : Real.sqrt (4 : ℝ) = 2 := by norm_num
          calc
            Real.sqrt 2 ≤ Real.sqrt (4 : ℝ) := Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 4)
            _ = 2 := hsq4
        nlinarith


/-! ### dyadic geometry -/

/-- `√(2^k) = (√2)^k` for every natural power `k`. -/
private lemma sqrt_two_pow (k : ℕ) : Real.sqrt ((2 : ℝ) ^ k) = (Real.sqrt 2) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ) ^ k) 2, ih]
      rw [pow_succ]

/-- Cast identity: `(2^k : ℕ) : ℝ = (2 : ℝ)^k`. -/
private lemma cast_two_pow (k : ℕ) : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by norm_num

/-- Geometric partial sum: `Σ_{k=0}^{K} (√2)^k ≤ 4·(√2)^K`. -/
private lemma geom_sqrt_two_le (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1), (Real.sqrt 2) ^ k) ≤ 4 * (Real.sqrt 2) ^ K := by
  let r : ℝ := Real.sqrt 2
  have hr1 : 1 < r := by
    dsimp [r]
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2)
  have hrm1 : 0 < r - 1 := sub_pos.mpr hr1
  have hgeom : (∑ k ∈ Finset.range (K + 1), (r ^ k)) * (r - 1) = r ^ (K + 1) - 1 :=
    geom_sum_mul r (K + 1)
  have hprod : (∑ k ∈ Finset.range (K + 1), (r ^ k)) * (r - 1) ≤ (4 * r ^ K) * (r - 1) := by
    calc
      (∑ k ∈ Finset.range (K + 1), (r ^ k)) * (r - 1) = r ^ (K + 1) - 1 := hgeom
      _ ≤ r ^ (K + 1) := by linarith
      _ = r * r ^ K := by rw [pow_succ']
      _ ≤ (4 * r ^ K) * (r - 1) := by
        have h43 : (4 / 3 : ℝ) ≤ r := by
          dsimp [r]
          exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
        have hrat : r ≤ 4 * (r - 1) := by nlinarith
        have hrK : 0 ≤ r ^ K := pow_nonneg (by dsimp [r]; exact Real.sqrt_nonneg 2) K
        calc
          r * r ^ K ≤ (4 * (r - 1)) * r ^ K := mul_le_mul_of_nonneg_right hrat hrK
          _ = (4 * r ^ K) * (r - 1) := by ring
  exact le_of_mul_le_mul_right hprod hrm1

/-- `Σ_{j=0}^{K} √(2^j : ℕ : ℝ) ≤ 4·√((2^K : ℕ) : ℝ)`. -/
private lemma sqrt_pow_nat_geom_le (K : ℕ) :
    (∑ j ∈ Finset.range (K + 1), Real.sqrt (((2 ^ j : ℕ) : ℝ))) ≤
      4 * Real.sqrt (((2 ^ K : ℕ) : ℝ)) := by
  calc
    (∑ j ∈ Finset.range (K + 1), Real.sqrt (((2 ^ j : ℕ) : ℝ)))
        = ∑ j ∈ Finset.range (K + 1), (Real.sqrt 2) ^ j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [cast_two_pow, sqrt_two_pow]
    _ ≤ 4 * (Real.sqrt 2) ^ K := geom_sqrt_two_le K
    _ = 4 * Real.sqrt (((2 ^ K : ℕ) : ℝ)) := by
          rw [cast_two_pow, sqrt_two_pow]

/-- power-of-two head-sum decomposition:
`Σ_{1≤n≤2^K} f = f 1 + Σ_{j<K} Σ_{2^j<n≤2^{j+1}} f`. -/
private lemma pow2_head_sum_decomp (K : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 (2 ^ K), f n) =
      f 1 + ∑ j ∈ Finset.range K, (∑ n ∈ Finset.Icc (2 ^ j + 1 : ℕ) (2 ^ (j + 1) : ℕ), f n) := by
  induction K with
  | zero =>
      have h1 : Finset.Icc 1 (2 ^ 0) = {1} := by
        ext n; simp [Finset.mem_Icc]
      simp [h1]
  | succ K ih =>
      have h1le : 1 ≤ 2 ^ K := by
        have h := pow_pos (show 0 < (2 : ℕ) by norm_num) K
        omega
      have hlt : 2 ^ K < 2 ^ (K + 1) := by
        exact pow_lt_pow_right₀ (by norm_num : (1 : ℕ) < (2 : ℕ)) (by omega : K < K + 1)
      have hsplit := TdtAbel.sum_Icc_union (a := 1) (b := 2 ^ K) (c := 2 ^ (K + 1)) h1le (le_of_lt hlt) f
      calc
        (∑ n ∈ Finset.Icc 1 (2 ^ (K + 1)), f n)
            = (∑ n ∈ Finset.Icc 1 (2 ^ K), f n) +
                (∑ n ∈ Finset.Icc (2 ^ K + 1) (2 ^ (K + 1)), f n) := hsplit
        _ = (f 1 + ∑ j ∈ Finset.range K,
              (∑ n ∈ Finset.Icc (2 ^ j + 1 : ℕ) (2 ^ (j + 1) : ℕ), f n)) +
              (∑ n ∈ Finset.Icc (2 ^ K + 1) (2 ^ (K + 1)), f n) := by rw [ih]
        _ = f 1 + ∑ j ∈ Finset.range (K + 1),
              (∑ n ∈ Finset.Icc (2 ^ j + 1 : ℕ) (2 ^ (j + 1) : ℕ), f n) := by
              rw [Finset.sum_range_succ]
              ring

/-- `Nat.log`-bound: for `Y ≥ 1`, `K := Nat.log 2 Y` satisfies
`(K:ℝ) + 1 ≤ 2·(1 + log(2Y))`. -/
private lemma logK_le {Y : ℕ} (hY : 1 ≤ Y) :
    ((Nat.log 2 Y : ℕ) : ℝ) + 1 ≤ 2 * (1 + Real.log (2 * (Y : ℝ))) := by
  let K : ℕ := Nat.log 2 Y
  have hY0 : Y ≠ 0 := by omega
  have hKle : (2 ^ K : ℕ) ≤ Y := by
    dsimp [K]
    exact Nat.pow_log_le_self 2 hY0
  have hc : ((2 ^ K : ℕ) : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hKle
  have h2Kpos : 0 < ((2 ^ K : ℕ) : ℝ) := by
    exact_mod_cast (pow_pos (show 0 < (2 : ℕ) by norm_num) K)
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast (by omega : 0 < Y)
  have hlogc : Real.log (((2 ^ K : ℕ) : ℝ)) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log h2Kpos hc
  have hpowident : Real.log (((2 ^ K : ℕ) : ℝ)) = (K : ℝ) * Real.log 2 := by
    rw [cast_two_pow]
    exact Real.log_pow (2 : ℝ) K
  have hKL : (K : ℝ) * Real.log 2 ≤ Real.log (Y : ℝ) := by
    rwa [hpowident] at hlogc
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hlt := Real.log_two_gt_d9
    exact le_of_lt (lt_trans (by norm_num : (1 / 2 : ℝ) < 0.6931471803) hlt)
  have hlogY2pos : 0 ≤ Real.log (2 * (Y : ℝ)) := by
    have htwoY : 1 < 2 * (Y : ℝ) := by
      have hYc : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
      nlinarith
    exact le_of_lt (Real.log_pos htwoY)
  have hKle2 : (K : ℝ) ≤ 2 * Real.log (2 * (Y : ℝ)) := by
    have h1 : (K : ℝ) ≤ 2 * ((K : ℝ) * Real.log 2) := by
      have hK0 : 0 ≤ (K : ℝ) := by positivity
      nlinarith [hlog2]
    have h2 : 2 * ((K : ℝ) * Real.log 2) ≤ 2 * Real.log (Y : ℝ) := by
      have h2mul : 0 ≤ (2 : ℝ) := by norm_num
      exact mul_le_mul_of_nonneg_left hKL h2mul
    have h3 : Real.log (Y : ℝ) ≤ Real.log (2 * (Y : ℝ)) := by
      have hle1 : (Y : ℝ) ≤ 2 * (Y : ℝ) := by nlinarith [hYpos]
      exact Real.log_le_log hYpos hle1
    have h4 : 2 * Real.log (Y : ℝ) ≤ 2 * Real.log (2 * (Y : ℝ)) := by
      exact mul_le_mul_of_nonneg_left h3 (by norm_num : 0 ≤ (2 : ℝ))
    nlinarith
  have htwoY : 0 ≤ Real.log (2 * (Y : ℝ)) := hlogY2pos
  have hlgpos : (K : ℝ) ≥ 0 := by positivity
  nlinarith

/-- `Σ_{j<K} √(2^{j+1}) ≤ 4·√2·√(2^K)`. -/
private lemma block_sqrt_sum_le (K : ℕ) :
    (∑ j ∈ Finset.range K, Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ))) ≤
      4 * Real.sqrt 2 * Real.sqrt (((2 ^ K : ℕ) : ℝ)) := by
  have hterm : ∀ j : ℕ, Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ)) =
      Real.sqrt 2 * Real.sqrt (((2 ^ j : ℕ) : ℝ)) := by
    intro j
    calc
      Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ))
          = Real.sqrt ((2 : ℝ) ^ (j + 1)) := by rw [cast_two_pow (j + 1)]
      _ = Real.sqrt ((2 : ℝ) ^ j * 2) := by rw [pow_succ]
      _ = Real.sqrt ((2 : ℝ) ^ j) * Real.sqrt 2 := by
          rw [Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ) ^ j) 2]
      _ = Real.sqrt 2 * Real.sqrt ((2 : ℝ) ^ j) := by ring
      _ = Real.sqrt 2 * Real.sqrt (((2 ^ j : ℕ) : ℝ)) := by rw [cast_two_pow j]
  calc
    (∑ j ∈ Finset.range K, Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ)))
        = ∑ j ∈ Finset.range K, Real.sqrt 2 * Real.sqrt (((2 ^ j : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hterm j
    _ = Real.sqrt 2 * (∑ j ∈ Finset.range K, Real.sqrt (((2 ^ j : ℕ) : ℝ))) := by
            rw [← Finset.mul_sum]
    _ ≤ Real.sqrt 2 * (4 * Real.sqrt (((2 ^ K : ℕ) : ℝ))) := by
            have hsub : (∑ j ∈ Finset.range K, Real.sqrt (((2 ^ j : ℕ) : ℝ))) ≤
                (∑ j ∈ Finset.range (K + 1), Real.sqrt (((2 ^ j : ℕ) : ℝ))) := by
              exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) (by
                intro j hj _
                exact Real.sqrt_nonneg _)
            calc
              Real.sqrt 2 * (∑ j ∈ Finset.range K, Real.sqrt (((2 ^ j : ℕ) : ℝ)))
                  ≤ Real.sqrt 2 * (∑ j ∈ Finset.range (K + 1), Real.sqrt (((2 ^ j : ℕ) : ℝ))) :=
                      mul_le_mul_of_nonneg_left hsub (by positivity : 0 ≤ Real.sqrt 2)
              _ ≤ Real.sqrt 2 * (4 * Real.sqrt (((2 ^ K : ℕ) : ℝ))) :=
                      mul_le_mul_of_nonneg_left (sqrt_pow_nat_geom_le K) (by positivity : 0 ≤ Real.sqrt 2)
    _ = 4 * Real.sqrt 2 * Real.sqrt (((2 ^ K : ℕ) : ℝ)) := by ring

/-- main assembly: weighted head-sum over `1..Y`. -/
private theorem shifted_head_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Y : ℕ) (hY : 1 ≤ Y) {c : ℝ} (hc : 0 < c) (t : ℝ) (ht : 1 ≤ t),
        ‖∑ m ∈ Finset.Icc 1 Y, sSummand c t (m : ℝ)‖ ≤
          C * (t ^ (1 / 6 : ℝ) * (1 + Real.log (2 * (Y : ℝ))) +
              t ^ (-(1 / 6 : ℝ)) * Real.sqrt (Y : ℝ)) := by
  classical
  obtain ⟨Cb, hCb, hb⟩ := weighted_block_bound
  refine ⟨1 + Cb * (3 + 4 * Real.sqrt 2), by positivity, ?_⟩
  intro Y hY c hc t ht
  let K : ℕ := Nat.log 2 Y
  let P : ℕ := 2 ^ K
  let B : ℝ := t ^ (1 / 6 : ℝ)
  let D : ℝ := t ^ (-(1 / 6 : ℝ))
  have hYne : Y ≠ 0 := by omega
  have hPK : P ≤ Y := by
    dsimp [P, K]
    exact Nat.pow_log_le_self 2 hYne
  have hPge1 : 1 ≤ P := by
    dsimp [P]
    have h := pow_pos (show 0 < (2 : ℕ) by norm_num) K
    omega
  have hYlt2P : Y < 2 * P := by
    dsimp [P, K]
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) Y
    have hsucc : (Nat.log 2 Y).succ = Nat.log 2 Y + 1 := rfl
    rw [hsucc] at h
    have hpow : 2 ^ (Nat.log 2 Y + 1) = 2 * 2 ^ Nat.log 2 Y := by
      rw [pow_succ]
      ring
    rwa [hpow] at h
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hB : 1 ≤ B := by
    dsimp [B]
    exact Real.one_le_rpow ht (by norm_num : 0 ≤ (1 / 6 : ℝ))
  have hB0 : 0 ≤ B := le_of_lt (by
    dsimp [B]
    exact Real.rpow_pos_of_pos ht0 (1 / 6 : ℝ))
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact le_of_lt (Real.rpow_pos_of_pos ht0 (-(1 / 6 : ℝ)))
  have hC0 : 0 ≤ Cb := le_of_lt hCb
  have hlogY : 0 ≤ Real.log (2 * (Y : ℝ)) := by
    have htwo : 1 < 2 * (Y : ℝ) := by
      have hYc : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
      nlinarith
    exact le_of_lt (Real.log_pos htwo)
  have hPKc : ((2 ^ K : ℕ) : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hPK
  -- per-block bound
  have hblock : ∀ j ∈ Finset.range K,
      ‖∑ m ∈ Finset.Icc (2 ^ j + 1 : ℕ) (2 ^ (j + 1) : ℕ), sSummand c t (m : ℝ)‖ ≤
        Cb * (B + D * Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ))) := by
    intro j hj
    have hPj : 1 ≤ 2 ^ j := by
      have h := pow_pos (show 0 < (2 : ℕ) by norm_num) j
      omega
    have hz := hb (2 ^ j) (2 ^ j) hPj hPj le_rfl hc t ht
    have hm : 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by
      rw [pow_succ]
      ring
    have hz' : ‖∑ m ∈ Finset.Icc (2 ^ j + 1 : ℕ) (2 ^ (j + 1) : ℕ), sSummand c t (m : ℝ)‖ ≤
        Cb * (B + D * Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ))) := by
      have hI : Finset.Icc (2 ^ j + 1 : ℕ) (2 ^ j + 2 ^ j : ℕ) =
          Finset.Icc (2 ^ j + 1 : ℕ) (2 ^ (j + 1) : ℕ) := by
        rw [hm]
      have hsq : Real.sqrt (((2 ^ j + 2 ^ j : ℕ) : ℝ)) = Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ)) := by
        rw [hm]
      have hz0 := hz
      dsimp [B, D] at hz0 ⊢
      rw [hI] at hz0
      rwa [hsq] at hz0
    exact hz'
  -- prefix decomposition
  have hdec : (∑ m ∈ Finset.Icc 1 P, sSummand c t (m : ℝ)) =
      sSummand c t (1 : ℝ) + ∑ j ∈ Finset.range K,
        (∑ m ∈ Finset.Icc (2 ^ j + 1 : ℕ) (2 ^ (j + 1) : ℕ), sSummand c t (m : ℝ)) := by
    simpa [P] using (pow2_head_sum_decomp K (fun m : ℕ => sSummand c t (m : ℝ)))
  have hterm1 : ‖sSummand c t (1 : ℝ)‖ ≤ 1 := by
    calc
      ‖sSummand c t (1 : ℝ)‖ = ‖sPhase c t (1 : ℝ) * ((amp c (1 : ℝ) : ℝ) : ℂ)‖ := by
          rw [sSummand_eq_mul]
      _ ≤ ‖sPhase c t (1 : ℝ)‖ * ‖((amp c (1 : ℝ) : ℝ) : ℂ)‖ := norm_mul_le _ _
      _ = |amp c (1 : ℝ)| := by
          rw [norm_sPhase, norm_amp_cast]
          simp
      _ ≤ 1 := by
          dsimp [amp]
          have h1c : 1 ≤ c + 1 := by linarith
          have hsqle : 1 ≤ Real.sqrt (c + 1) := by
            calc
              1 = Real.sqrt 1 := by rw [Real.sqrt_one]
              _ ≤ Real.sqrt (c + 1) := Real.sqrt_le_sqrt h1c
          rw [abs_of_nonneg]
          · exact inv_le_one_of_one_le₀ hsqle
          · exact inv_nonneg.mpr (Real.sqrt_nonneg (c + 1))
  have hpre : ‖∑ m ∈ Finset.Icc 1 P, sSummand c t (m : ℝ)‖ ≤
      1 + Cb * ((K : ℝ) * B + D * (4 * Real.sqrt 2 * Real.sqrt (((2 ^ K : ℕ) : ℝ)))) := by
    have h1 : ‖sSummand c t (1 : ℝ)‖ +
          (∑ j ∈ Finset.range K,
            ‖∑ m ∈ Finset.Icc (2 ^ j + 1 : ℕ) (2 ^ (j + 1) : ℕ), sSummand c t (m : ℝ)‖) ≤
        1 + (∑ j ∈ Finset.range K,
          Cb * (B + D * Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ)))) := by
      exact add_le_add hterm1 (Finset.sum_le_sum hblock)
    have h2 : (∑ j ∈ Finset.range K, Cb * (B + D * Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ)))) =
        Cb * ((K : ℝ) * B + D * (∑ j ∈ Finset.range K, Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ)))) := by
      calc
        (∑ j ∈ Finset.range K, Cb * (B + D * Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ))))
            = Cb * (∑ j ∈ Finset.range K, (B + D * Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ)))) := by
                rw [← Finset.mul_sum]
        _ = Cb * ((K : ℝ) * B + D * (∑ j ∈ Finset.range K, Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ)))) := by
                congr 1
                calc
                  (∑ j ∈ Finset.range K, (B + D * Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ))))
                      = (∑ j ∈ Finset.range K, B) +
                          ∑ j ∈ Finset.range K, D * Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ)) := by
                          rw [Finset.sum_add_distrib]
                  _ = (K : ℝ) * B + D * (∑ j ∈ Finset.range K, Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ))) := by
                          have hBsum : (∑ j ∈ Finset.range K, B) = (K : ℝ) * B := by
                            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
                          have hDsum : (∑ j ∈ Finset.range K, D * Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ))) =
                              D * (∑ j ∈ Finset.range K, Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ))) := by
                              rw [← Finset.mul_sum]
                          rw [hBsum, hDsum]
    have h3 : D * (∑ j ∈ Finset.range K, Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ))) ≤
        D * (4 * Real.sqrt 2 * Real.sqrt (((2 ^ K : ℕ) : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (block_sqrt_sum_le K) hD0
    have h4 : Cb * ((K : ℝ) * B + D * (∑ j ∈ Finset.range K, Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ)))) ≤
        Cb * ((K : ℝ) * B + D * (4 * Real.sqrt 2 * Real.sqrt (((2 ^ K : ℕ) : ℝ)))) := by
      have hinner : (K : ℝ) * B + D * (∑ j ∈ Finset.range K, Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ))) ≤
          (K : ℝ) * B + D * (4 * Real.sqrt 2 * Real.sqrt (((2 ^ K : ℕ) : ℝ))) := by
        nlinarith [h3]
      nlinarith [hinner, hC0]
    calc
      ‖∑ m ∈ Finset.Icc 1 P, sSummand c t (m : ℝ)‖
          = ‖sSummand c t (1 : ℝ) + ∑ j ∈ Finset.range K,
              (∑ m ∈ Finset.Icc (2 ^ j + 1 : ℕ) (2 ^ (j + 1) : ℕ), sSummand c t (m : ℝ))‖ := by rw [hdec]
      _ ≤ ‖sSummand c t (1 : ℝ)‖ +
            ‖∑ j ∈ Finset.range K, (∑ m ∈ Finset.Icc (2 ^ j + 1 : ℕ) (2 ^ (j + 1) : ℕ), sSummand c t (m : ℝ))‖ := by
            exact norm_add_le _ _
      _ ≤ ‖sSummand c t (1 : ℝ)‖ +
            (∑ j ∈ Finset.range K,
              ‖∑ m ∈ Finset.Icc (2 ^ j + 1 : ℕ) (2 ^ (j + 1) : ℕ), sSummand c t (m : ℝ)‖) := by
            exact add_le_add le_rfl (norm_sum_le _ _)
      _ ≤ 1 + (∑ j ∈ Finset.range K,
            Cb * (B + D * Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ)))) := h1
      _ = 1 + Cb * ((K : ℝ) * B + D * (∑ j ∈ Finset.range K, Real.sqrt (((2 ^ (j + 1) : ℕ) : ℝ)))) := by
            rw [h2]
      _ ≤ 1 + Cb * ((K : ℝ) * B + D * (4 * Real.sqrt 2 * Real.sqrt (((2 ^ K : ℕ) : ℝ)))) := by
            nlinarith [h4]
  -- top block
  have htop : ‖∑ m ∈ Finset.Icc (P + 1) Y, sSummand c t (m : ℝ)‖ ≤
      Cb * (B + D * Real.sqrt (Y : ℝ)) := by
    by_cases hyP : Y = P
    · have hE : Finset.Icc (P + 1) P = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hyP, hE]
      simp
      positivity
    · have hPne : P ≠ Y := by omega
      have hPly : P < Y := lt_of_le_of_ne hPK hPne
      let L : ℕ := Y - P
      have hLge1 : 1 ≤ L := by
        dsimp [L]
        have hP1 : P + 1 ≤ Y := Nat.succ_le_of_lt hPly
        have h1P : 1 + P ≤ Y := by simpa [Nat.add_comm] using hP1
        exact Nat.le_sub_of_add_le h1P
      have hLP : L ≤ P := by
        dsimp [L]
        have hY2 := Nat.le_of_lt hYlt2P
        exact (Nat.sub_le_iff_le_add).mpr (by
          have h0 : Y ≤ P + P := by
            convert hY2 using 1
            ring
          exact h0)
      have hPplusL : P + L = Y := by
        dsimp [L]
        simpa [Nat.add_comm] using (Nat.sub_add_cancel hPK)
      have hbI := hb P L hPge1 hLge1 hLP hc t ht
      have hIcc2 : Finset.Icc (P + 1) (P + L) = Finset.Icc (P + 1) Y := by rw [hPplusL]
      have hbI' : ‖∑ m ∈ Finset.Icc (P + 1) (P + L), sSummand c t (m : ℝ)‖ ≤
          Cb * (B + D * Real.sqrt ((P + L : ℕ) : ℝ)) := by
        dsimp [B, D] at hbI ⊢
        exact hbI
      calc
        ‖∑ m ∈ Finset.Icc (P + 1) Y, sSummand c t (m : ℝ)‖
            = ‖∑ m ∈ Finset.Icc (P + 1) (P + L), sSummand c t (m : ℝ)‖ := by rw [← hIcc2]
        _ ≤ Cb * (B + D * Real.sqrt ((P + L : ℕ) : ℝ)) := hbI'
        _ = Cb * (B + D * Real.sqrt (Y : ℝ)) := by rw [hPplusL]
  -- combine prefix and top over the split
  have hsplitY := TdtAbel.sum_Icc_union (a := 1) (b := P) (c := Y) hPge1 hPK
    (fun m => sSummand c t (m : ℝ))
  have htotal0 : ‖∑ m ∈ Finset.Icc 1 Y, sSummand c t (m : ℝ)‖ ≤
      (‖∑ m ∈ Finset.Icc 1 P, sSummand c t (m : ℝ)‖ +
        ‖∑ m ∈ Finset.Icc (P + 1) Y, sSummand c t (m : ℝ)‖) := by
    rw [hsplitY]
    exact norm_add_le _ _
  have htop0 : 0 ≤ ‖∑ m ∈ Finset.Icc (P + 1) Y, sSummand c t (m : ℝ)‖ := by positivity
  have htotal1 : ‖∑ m ∈ Finset.Icc 1 P, sSummand c t (m : ℝ)‖ +
        ‖∑ m ∈ Finset.Icc (P + 1) Y, sSummand c t (m : ℝ)‖ ≤
      1 + Cb * ((K : ℝ) * B + D * (4 * Real.sqrt 2 * Real.sqrt (Y : ℝ))) +
        Cb * (B + D * Real.sqrt (Y : ℝ)) := by
    have hKleY : Real.sqrt (((2 ^ K : ℕ) : ℝ)) ≤ Real.sqrt (Y : ℝ) := Real.sqrt_le_sqrt hPKc
    have hx : D * (4 * Real.sqrt 2 * Real.sqrt (((2 ^ K : ℕ) : ℝ))) ≤
        D * (4 * Real.sqrt 2 * Real.sqrt (Y : ℝ)) := by
      have hf : 4 * Real.sqrt 2 * Real.sqrt (((2 ^ K : ℕ) : ℝ)) ≤
          4 * Real.sqrt 2 * Real.sqrt (Y : ℝ) := by
        exact mul_le_mul_of_nonneg_left hKleY (by positivity : 0 ≤ 4 * Real.sqrt 2)
      exact mul_le_mul_of_nonneg_left hf hD0
    have hpre' : ‖∑ m ∈ Finset.Icc 1 P, sSummand c t (m : ℝ)‖ ≤
        1 + Cb * ((K : ℝ) * B + D * (4 * Real.sqrt 2 * Real.sqrt (Y : ℝ))) := by
      have hz : Cb * ((K : ℝ) * B + D * (4 * Real.sqrt 2 * Real.sqrt (((2 ^ K : ℕ) : ℝ)))) ≤
          Cb * ((K : ℝ) * B + D * (4 * Real.sqrt 2 * Real.sqrt (Y : ℝ))) := by
        have hinner : (K : ℝ) * B + D * (4 * Real.sqrt 2 * Real.sqrt (((2 ^ K : ℕ) : ℝ))) ≤
            (K : ℝ) * B + D * (4 * Real.sqrt 2 * Real.sqrt (Y : ℝ)) := by nlinarith [hx]
        nlinarith [hinner, hC0]
      calc
        ‖∑ m ∈ Finset.Icc 1 P, sSummand c t (m : ℝ)‖
            ≤ 1 + Cb * ((K : ℝ) * B + D * (4 * Real.sqrt 2 * Real.sqrt (((2 ^ K : ℕ) : ℝ)))) := hpre
        _ ≤ 1 + Cb * ((K : ℝ) * B + D * (4 * Real.sqrt 2 * Real.sqrt (Y : ℝ))) := by
            nlinarith [hz]
    exact add_le_add hpre' htop
  let X : ℝ := B * (1 + Real.log (2 * (Y : ℝ)))
  let Ys : ℝ := D * Real.sqrt (Y : ℝ)
  have hX1 : 1 ≤ X := by
    dsimp [X]
    have hlg1 : 1 ≤ 1 + Real.log (2 * (Y : ℝ)) := by linarith
    calc
      1 ≤ B * 1 := by simpa using hB
      _ ≤ B * (1 + Real.log (2 * (Y : ℝ))) := mul_le_mul_of_nonneg_left hlg1 hB0
  have hYsn : 0 ≤ Ys := by dsimp [Ys]; positivity
  have hXpos : 0 ≤ X := by dsimp [X]; positivity
  have hKl : (K : ℝ) + 1 ≤ 2 * (1 + Real.log (2 * (Y : ℝ))) := by
    exact logK_le hY
  have hbig : 1 + Cb * ((K : ℝ) * B + D * (4 * Real.sqrt 2 * Real.sqrt (Y : ℝ))) +
        Cb * (B + D * Real.sqrt (Y : ℝ)) ≤
      (1 + Cb * (3 + 4 * Real.sqrt 2)) * (X + Ys) := by
    have htermA : (K : ℝ) * B + B ≤ 2 * X := by
      have h1 : ((K : ℝ) + 1) * B ≤ 2 * X := by
        have h2 : (K : ℝ) + 1 ≤ 2 * (1 + Real.log (2 * (Y : ℝ))) := hKl
        have h3 : 0 ≤ B := hB0
        calc
          ((K : ℝ) + 1) * B ≤ (2 * (1 + Real.log (2 * (Y : ℝ)))) * B := by
              exact mul_le_mul_of_nonneg_right h2 h3
          _ = 2 * (B * (1 + Real.log (2 * (Y : ℝ)))) := by ring
          _ = 2 * X := by rfl
      nlinarith
    have htermB : D * (4 * Real.sqrt 2 * Real.sqrt (Y : ℝ)) + D * Real.sqrt (Y : ℝ) ≤
        (4 * Real.sqrt 2 + 1) * Ys := by
      dsimp [Ys]
      have hE : D * (4 * Real.sqrt 2 * Real.sqrt (Y : ℝ)) + D * Real.sqrt (Y : ℝ) =
          (4 * Real.sqrt 2 + 1) * (D * Real.sqrt (Y : ℝ)) := by ring
      rw [hE]
    have hfinA : Cb * ((K : ℝ) * B + D * (4 * Real.sqrt 2 * Real.sqrt (Y : ℝ))) +
        Cb * (B + D * Real.sqrt (Y : ℝ)) ≤ 2 * Cb * X + Cb * (4 * Real.sqrt 2 + 1) * Ys := by
      have h1 : Cb * ((K : ℝ) * B + D * (4 * Real.sqrt 2 * Real.sqrt (Y : ℝ))) +
          Cb * (B + D * Real.sqrt (Y : ℝ))
          = Cb * (((K : ℝ) * B + B) + (D * (4 * Real.sqrt 2 * Real.sqrt (Y : ℝ)) + D * Real.sqrt (Y : ℝ))) := by ring
      have h2 : ((K : ℝ) * B + B) + (D * (4 * Real.sqrt 2 * Real.sqrt (Y : ℝ)) + D * Real.sqrt (Y : ℝ)) ≤
          2 * X + (4 * Real.sqrt 2 + 1) * Ys := by nlinarith [htermA, htermB]
      calc
        Cb * ((K : ℝ) * B + D * (4 * Real.sqrt 2 * Real.sqrt (Y : ℝ))) +
            Cb * (B + D * Real.sqrt (Y : ℝ))
            = Cb * (((K : ℝ) * B + B) + (D * (4 * Real.sqrt 2 * Real.sqrt (Y : ℝ)) + D * Real.sqrt (Y : ℝ))) := h1
        _ ≤ Cb * (2 * X + (4 * Real.sqrt 2 + 1) * Ys) := by
            exact mul_le_mul_of_nonneg_left h2 hC0
        _ = 2 * Cb * X + Cb * (4 * Real.sqrt 2 + 1) * Ys := by ring
    have hfin2 : 1 + 2 * Cb * X + Cb * (4 * Real.sqrt 2 + 1) * Ys ≤
        (1 + Cb * (3 + 4 * Real.sqrt 2)) * (X + Ys) := by
      have hcA : 2 * Cb ≤ Cb * (3 + 4 * Real.sqrt 2) := by
        have h2 : (2 : ℝ) ≤ 3 + 4 * Real.sqrt 2 := by nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
        nlinarith [hC0]
      have hcB : Cb * (4 * Real.sqrt 2 + 1) ≤ Cb * (3 + 4 * Real.sqrt 2) := by
        have h1 : (4 * Real.sqrt 2 + 1 : ℝ) ≤ 3 + 4 * Real.sqrt 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left h1 hC0
      have h12 : 1 ≤ X + Ys := by nlinarith [hX1, hYsn]
      have hbig1 : 1 + 2 * Cb * X + Cb * (4 * Real.sqrt 2 + 1) * Ys ≤
          (X + Ys) + Cb * (3 + 4 * Real.sqrt 2) * X + Cb * (3 + 4 * Real.sqrt 2) * Ys := by
        nlinarith [h12, hcA, hcB, hXpos, hYsn]
      nlinarith
    nlinarith [hfinA, hfin2]
  calc
    ‖∑ m ∈ Finset.Icc 1 Y, sSummand c t (m : ℝ)‖
        ≤ ‖∑ m ∈ Finset.Icc 1 P, sSummand c t (m : ℝ)‖ +
            ‖∑ m ∈ Finset.Icc (P + 1) Y, sSummand c t (m : ℝ)‖ := htotal0
    _ ≤ 1 + Cb * ((K : ℝ) * B + D * (4 * Real.sqrt 2 * Real.sqrt (Y : ℝ))) +
            Cb * (B + D * Real.sqrt (Y : ℝ)) := htotal1
    _ ≤ (1 + Cb * (3 + 4 * Real.sqrt 2)) * (X + Ys) := hbig
    _ = (1 + Cb * (3 + 4 * Real.sqrt 2)) * (t ^ (1 / 6 : ℝ) * (1 + Real.log (2 * (Y : ℝ))) +
        t ^ (-(1 / 6 : ℝ)) * Real.sqrt (Y : ℝ)) := by rfl

/-- **Shifted (arithmetic-progression) head-sum bound.**  For `0 < c`, `1 ≤ Y`
with `(Y : ℝ)² ≤ t`, `1 ≤ t`:

    |Σ_{1≤m≤Y} (c+m)^{−1/2−it}| ≤ C·( t^{1/6}·(1 + log(2Y)) + t^{−1/6}·√Y )

with an absolute constant `C` (uniform in `c > 0`).  Here the summand is
`cexp(((2π·(−(t/2π)·log(c+m)) : ℝ) : ℂ)·I)/√(c+m) = (c+m)^{−1/2−it}`. -/
private theorem head_weyl_bound_shifted :
    ∃ C : ℝ, 0 < C ∧
      ∀ (c : ℝ) (hc : 0 < c) (Y : ℕ) (hY : 1 ≤ Y) (t : ℝ) (ht : 1 ≤ t)
        (hYt : (Y : ℝ) ^ 2 ≤ t),
        ‖∑ m ∈ Finset.Icc 1 Y,
            cexp ((((2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log (c + (m : ℝ)))) : ℝ) : ℂ) * I) /
              Real.sqrt (c + (m : ℝ))‖
          ≤ C * (t ^ (1 / 6 : ℝ) * (1 + Real.log (2 * (Y : ℝ))) +
              t ^ (-(1 / 6 : ℝ)) * Real.sqrt (Y : ℝ)) := by
  classical
  obtain ⟨C, hC, h⟩ := shifted_head_bound
  refine ⟨C, hC, ?_⟩
  intro c hc Y hY t ht hYt
  simpa [sSummand, sPhase] using (h Y hY hc t ht)

end TdtShiftHead

/-! ### Phase-argument bridge (target phrasing ↔ corpus phrasing) -/

/-- `−t·log(c+m) = 2π·(−(t/2π)·log(c+m))` (real identity used to match the
statement's phase to the corpus phase `sPhase`). -/
private lemma log_phase_shift_arg_eq (c t : ℝ) (m : ℕ) :
    (-(t * Real.log (c + (m : ℝ)))) =
      2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log (c + (m : ℝ))) := by
  field_simp [Real.pi_ne_zero]

/-- The target sum (phase `−(t·log(c+m))`) equals the corpus sum (phase
`2π·(−(t/2π)·log(c+m))`) termwise. -/
private lemma shifted_head_sum_eq (c : ℝ) (Y : ℕ) (t : ℝ) :
    (∑ m ∈ Finset.Icc 1 Y,
        cexp ((((-(t * Real.log (c + (m : ℝ)))) : ℝ) : ℂ) * I) /
          (Real.sqrt (c + (m : ℝ)) : ℂ)) =
      (∑ m ∈ Finset.Icc 1 Y,
        cexp ((((2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log (c + (m : ℝ)))) : ℝ) : ℂ) * I) /
          Real.sqrt (c + (m : ℝ))) := by
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  rw [log_phase_shift_arg_eq c t m]

/-- Shifted arithmetic-progression head-sum Weyl bound, uniform in the shift
`c > 0`: for `0 < c`, `1 ≤ Y` with `Y² ≤ t` and `1 ≤ t`,

    |Σ_{1≤m≤Y} (c+m)^{−1/2−it}| ≤ C·( t^{1/6}·(1 + log(2Y)) + t^{−1/6}·√Y )

with an absolute constant `C`.  (The summand is
`cexp(((−(t·log(c+m)) : ℝ) : ℂ)·I)/√(c+m) = (c+m)^{−1/2−it}`.) -/
theorem log_phase_shifted_head_sum_weyl :
    ∃ C : ℝ, 0 < C ∧
      ∀ (c : ℝ) (_hc : 0 < c) (Y : ℕ) (_hY : 1 ≤ Y) (t : ℝ) (_ht : 1 ≤ t)
        (_hYt : (Y : ℝ) ^ 2 ≤ t),
        ‖∑ m ∈ Finset.Icc 1 Y,
            cexp ((((-(t * Real.log (c + (m : ℝ)))) : ℝ) : ℂ) * I) /
              (Real.sqrt (c + (m : ℝ)) : ℂ)‖
          ≤ C * (t ^ (1 / 6 : ℝ) * (1 + Real.log (2 * (Y : ℝ))) +
              t ^ (-(1 / 6 : ℝ)) * Real.sqrt (Y : ℝ)) := by
  classical
  obtain ⟨C, hC, h⟩ := TdtShiftHead.head_weyl_bound_shifted
  refine ⟨C, hC, ?_⟩
  intro c hc Y hY t ht hYt
  rw [shifted_head_sum_eq c Y t]
  exact h c hc Y hY t ht hYt

end
end Commons.Analysis.ExponentialSums