import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.seriesFunM_eq_sum
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.flat.fourierCoeff_seriesFun
import Submission.Work.Diff.STE.CSq_comp_vecarg_le
import Submission.Work.Diff.STE.CSq_conv_le
import Submission.Work.Diff.STE.norm_seriesFun_le
import Submission.Work.Diff.STE.l1_le_sqrt_CSq
import Submission.Work.Diff.STE.CSq_le_ENormSq
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.CSq_le_ENormSq_seriesFun
import Submission.Work.Diff.STE.pd_seriesFun
import Submission.Work.Diff.STE.contDiff_seriesFun
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.flat.nonlin_bound_short

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

open MeasureTheory BigOperators

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat

noncomputable section

/-! ## STEP 1: from the level-`k` energy bound to the level-`j` coefficient bounds -/

/-- The hypothesis `card (Fin n) + 4 < 2 k` implies `sob n + 2 ≤ k`, i.e. the level `k` energy
controls the spatial derivatives of order `≤ 2` (which is what the jet needs). -/
lemma sob_add_two_le {n k : ℕ} (hk : Fintype.card (Fin n) + 4 < 2 * k) :
    Work.Diff.STE.flat.sob n + 2 ≤ k := by
  have hc : Fintype.card (Fin n) = n := Fintype.card_fin n
  rw [hc] at hk
  unfold Work.Diff.STE.flat.sob
  omega

/-- **All lower coefficient energies are dominated by the level-`k` energy.**  For a box-supported
coefficient family, `CSqM j c ≤ C · ENormSqFull k (seriesFunM c)` for every `j ≤ k`. -/
theorem csqM_le_of_energy {n k : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k', k' ∉ box n N → c k' = 0) → ∀ j ≤ k,
      CSqM j c ≤ C * ENormSqFull k (seriesFunM c) := by
  obtain ⟨C1, hC1nn, hC1⟩ := Work.Diff.STE.CSq_le_ENormSq_seriesFun (ι := Fin n) k
  refine ⟨(Fintype.card (Fin n) : ℝ) * (Fintype.card (Fin n) : ℝ) * max C1 1,
    by positivity, ?_⟩
  intro N c hc j hj
  have hkey : ∀ i j' : Fin n,
      CSq j (fun m => c m i j') ≤ max C1 1 * ENormSqFull k (seriesFunM c) := by
    intro i j'
    have hmom : ∀ M : ℕ, Summable (fun m : Fin n → ℤ => (wt m) ^ M * ‖c m i j'‖) :=
      fun M => summable_moment_box c hc i j' M
    have h1 : CSq k (fun m => c m i j') ≤ C1 *
        (ENormSq k (seriesFun (fun m => c m i j')) +
          ENormSq 0 (seriesFun (fun m => c m i j'))) := hC1 _ hmom
    have h2 : ENormSq k (seriesFun (fun m => c m i j')) ≤ ENormSqM k (seriesFunM c) := by
      have h := ENormSq_le_ENormSqM (j := k) (seriesFunM c) i j'
      simpa [seriesFunM_apply] using h
    have h3 : ENormSq 0 (seriesFun (fun m => c m i j')) ≤ ENormSqM 0 (seriesFunM c) := by
      have h := ENormSq_le_ENormSqM (j := 0) (seriesFunM c) i j'
      simpa [seriesFunM_apply] using h
    have hmono : CSq j (fun m => c m i j') ≤ CSq k (fun m => c m i j') := by
      rw [CSq, CSq]
      refine Summable.tsum_le_tsum (fun m => ?_)
        (summable_wt_pow_mul_norm_sq _ hmom j) (summable_wt_pow_mul_norm_sq _ hmom k)
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (wt_one_le m) hj) (sq_nonneg _)
    calc CSq j (fun m => c m i j') ≤ CSq k (fun m => c m i j') := hmono
      _ ≤ C1 * (ENormSq k (seriesFun (fun m => c m i j')) +
            ENormSq 0 (seriesFun (fun m => c m i j'))) := h1
      _ ≤ C1 * ENormSqFull k (seriesFunM c) := by
          rw [ENormSqFull]
          exact mul_le_mul_of_nonneg_left (by linarith) hC1nn
      _ ≤ max C1 1 * ENormSqFull k (seriesFunM c) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (ENormSqFull_nonneg k _)
  rw [CSqM]
  calc ∑ i : Fin n, ∑ j' : Fin n, CSq j (fun m => c m i j')
      ≤ ∑ i : Fin n, ∑ j' : Fin n, max C1 1 * ENormSqFull k (seriesFunM c) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j' _ => hkey i j'
    _ = (Fintype.card (Fin n) : ℝ) * (Fintype.card (Fin n) : ℝ) * max C1 1 *
          ENormSqFull k (seriesFunM c) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Uniform sup bounds for the derivatives of `seriesFunM c`** (the quantifier order of
`jet_sup_le` is not uniform in `c`; this version is). -/
theorem jet_sup_le_uniform {n k m : ℕ} (hm : m + sob n ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k', k' ∉ box n N → c k' = 0) → ∀ (l : Fin m → Fin n) (i j : Fin n) (x : Fin n → ℝ),
      ‖pdVec m l (fun y => seriesFunM c y i j) x‖
        ≤ C * (1 + Real.sqrt (ENormSqFull k (seriesFunM c))) := by
  obtain ⟨C0, hC0, h0⟩ := norm_seriesFun_le (ι := Fin n) (sob n) (by simpa using n_lt_two_sob n)
  obtain ⟨C2, hC2, h2⟩ := CSq_le_ENormSq_seriesFun (ι := Fin n) k
  refine ⟨C0 * (2 * Real.pi) ^ m * Real.sqrt C2, by positivity, ?_⟩
  intro N c hc l i j x
  have hmom : ∀ M : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ M * ‖c k i j‖) :=
    fun M => summable_moment_box c hc i j M
  have hfun : (fun y : Fin n → ℝ => seriesFunM c y i j)
      = seriesFun (fun k : Fin n → ℤ => c k i j) := by
    funext y; rw [seriesFunM_apply]
  have hpd : pdVec m l (fun y => seriesFunM c y i j) x
      = seriesFun (dmulV (List.ofFn l) (fun k => c k i j)) x := by
    rw [hfun]
    exact pdList_seriesFun (List.ofFn l) (fun k => c k i j) hmom x
  rw [hpd]
  have hstep := h0 (dmulV (List.ofFn l) (fun k => c k i j))
    (summable_wt_pow_mul_norm_sq _ (fun M => summable_dmulV _ _ hmom M) (sob n)) x
  have hCSq : CSq (sob n) (dmulV (List.ofFn l) (fun k => c k i j))
      ≤ ((2 * Real.pi) ^ 2) ^ m * CSq (sob n + m) (fun k => c k i j) := by
    have h := CSq_dmulV_le (sob n) (List.ofFn l) (fun k => c k i j) hmom
    simpa [List.length_ofFn] using h
  have hlev : sob n + m ≤ k := by omega
  have hmono : CSq (sob n + m) (fun k : Fin n → ℤ => c k i j)
      ≤ CSq k (fun k => c k i j) := by
    rw [CSq, CSq]
    refine Summable.tsum_le_tsum (fun k => ?_)
      (summable_wt_pow_mul_norm_sq _ hmom (sob n + m))
      (summable_wt_pow_mul_norm_sq _ hmom k)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (wt_one_le k) hlev) (sq_nonneg _)
  have h4 : CSq k (fun k : Fin n → ℤ => c k i j) ≤ C2 * ENormSqFull k (seriesFunM c) := by
    have h := h2 (fun k => c k i j) hmom
    have hEs : ENormSq k (seriesFun (fun k : Fin n → ℤ => c k i j))
        ≤ ENormSqM k (seriesFunM c) := by
      have hh := ENormSq_le_ENormSqM (j := k) (seriesFunM c) i j
      rwa [hfun] at hh
    have hE0 : ENormSq 0 (seriesFun (fun k : Fin n → ℤ => c k i j))
        ≤ ENormSqM 0 (seriesFunM c) := by
      have hh := ENormSq_le_ENormSqM (j := 0) (seriesFunM c) i j
      rwa [hfun] at hh
    refine h.trans ?_
    rw [ENormSqFull]
    exact mul_le_mul_of_nonneg_left (add_le_add hEs hE0) hC2
  calc ‖seriesFun (dmulV (List.ofFn l) (fun k => c k i j)) x‖
      ≤ C0 * Real.sqrt (CSq (sob n) (dmulV (List.ofFn l) (fun k => c k i j))) := hstep
    _ ≤ C0 * Real.sqrt (((2 * Real.pi) ^ 2) ^ m * CSq (sob n + m) (fun k => c k i j)) := by
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hCSq) hC0
    _ = C0 * ((2 * Real.pi) ^ m * Real.sqrt (CSq (sob n + m) (fun k => c k i j))) := by
        have hsq : ((2 * Real.pi) ^ 2) ^ m = ((2 * Real.pi) ^ m) ^ 2 := by
          rw [← pow_mul]; ring_nf
        rw [hsq, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ ≤ C0 * ((2 * Real.pi) ^ m * Real.sqrt (C2 * ENormSqFull k (seriesFunM c))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
        exact hmono.trans h4
    _ = C0 * ((2 * Real.pi) ^ m * (Real.sqrt C2 * Real.sqrt (ENormSqFull k (seriesFunM c)))) := by
        rw [Real.sqrt_mul hC2]
    _ ≤ C0 * ((2 * Real.pi) ^ m * (Real.sqrt C2
          * (1 + Real.sqrt (ENormSqFull k (seriesFunM c))))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg C2)
    _ = C0 * (2 * Real.pi) ^ m * Real.sqrt C2
          * (1 + Real.sqrt (ENormSqFull k (seriesFunM c))) := by ring

/-- `pdM` in terms of `pdVec`. -/
lemma pdM_eq_pdVec_one {n : ℕ} (d : Fin n) (u : Torus n) (x : Fin n → ℝ) (i j : Fin n) :
    pdM d u x i j = pdVec 1 (fun _ : Fin 1 => d) (fun y => u y i j) x := by
  simp [pdM, pdVec, pdList]

/-- The second derivative of the jet in terms of `pdVec`. -/
lemma pdM_pdM_eq_pdVec_two {n : ℕ} (d e : Fin n) (u : Torus n) (x : Fin n → ℝ)
    (i j : Fin n) :
    pdM d (pdM e u) x i j = pdVec 2 (Fin.cases d (fun _ : Fin 1 => e))
      (fun y => u y i j) x := by
  simp [pdM, pdVec, pdList]

/-- The value of the jet in terms of `pdVec`. -/
lemma zero_eq_pdVec_zero {n : ℕ} (u : Torus n) (x : Fin n → ℝ) (i j : Fin n) :
    u x i j = pdVec 0 (fun _ : Fin 0 => i) (fun y => u y i j) x := by
  simp [pdVec, pdList]

/-- **The jet sup bounds.**  From the level-`k` box energy bound, the entries of the value, the
first jet and the second jet of `seriesFunM c` are bounded by a constant `KA` depending only on
`n`, `k` and `B`. -/
theorem jet_sup_bound {n k : ℕ} (hk : Fintype.card (Fin n) + 4 < 2 * k) (B : ℝ) (hB : 0 ≤ B) :
    ∃ KA : ℝ, 0 ≤ KA ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k', k' ∉ box n N → c k' = 0) →
      ENormSqFull k (seriesFunM c) ≤ B ^ 2 →
      (∀ x (i j : Fin n), ‖seriesFunM c x i j‖ ≤ KA) ∧
      (∀ x (d : Fin n) (i j : Fin n), ‖pdM d (seriesFunM c) x i j‖ ≤ KA) ∧
      (∀ x (d e : Fin n) (i j : Fin n), ‖pdM d (pdM e (seriesFunM c)) x i j‖ ≤ KA) := by
  have hsobk : sob n + 2 ≤ k := sob_add_two_le hk
  have hs0 : 0 + sob n ≤ k := by omega
  have hs1 : 1 + sob n ≤ k := by omega
  have hs2 : 2 + sob n ≤ k := by omega
  obtain ⟨C0, hC0nn, h0⟩ := jet_sup_le_uniform (n := n) (k := k) (m := 0) hs0
  obtain ⟨C1, hC1nn, h1⟩ := jet_sup_le_uniform (n := n) (k := k) (m := 1) hs1
  obtain ⟨C2, hC2nn, h2⟩ := jet_sup_le_uniform (n := n) (k := k) (m := 2) hs2
  refine ⟨max (max C0 C1) C2 * (1 + B), by positivity, ?_⟩
  intro N c hc hE
  have hsqrt : Real.sqrt (ENormSqFull k (seriesFunM c)) ≤ B := by
    rw [← Real.sqrt_sq hB]
    exact Real.sqrt_le_sqrt hE
  have hstep : ∀ (C : ℝ) (hC : C ≤ max (max C0 C1) C2) (S : ℝ),
      S ≤ C * (1 + Real.sqrt (ENormSqFull k (seriesFunM c))) →
      S ≤ max (max C0 C1) C2 * (1 + B) := by
    intro C hC S hS
    refine le_trans hS (mul_le_mul hC ?_ (by positivity) ?_)
    · linarith
    · have h0' : (0 : ℝ) ≤ max (max C0 C1) C2 :=
        le_trans hC0nn (le_trans (le_max_left C0 C1) (le_max_left (max C0 C1) C2))
      linarith
  refine ⟨?_, ?_, ?_⟩
  · intro x i j
    have h := h0 N c hc (fun _ : Fin 0 => i) i j x
    rw [zero_eq_pdVec_zero (seriesFunM c)]
    exact hstep C0 (le_trans (le_max_left C0 C1) (le_max_left (max C0 C1) C2)) _ h
  · intro x d i j
    have h := h1 N c hc (fun _ : Fin 1 => d) i j x
    rw [pdM_eq_pdVec_one d (seriesFunM c)]
    exact hstep C1 (le_trans (le_max_right C0 C1) (le_max_left (max C0 C1) C2)) _ h
  · intro x d e i j
    have h := h2 N c hc (Fin.cases d (fun _ : Fin 1 => e)) i j x
    rw [pdM_pdM_eq_pdVec_two d e (seriesFunM c)]
    exact hstep C2 (le_max_right (max C0 C1) C2) _ h

/-! ## Quadratic forms: crude lower bound and Lipschitz comparison -/

/-- The crude lower bound for the quadratic form of a matrix with bounded entries. -/
lemma quadForm_ge_neg {n : ℕ} (A : MatC n) {KA : ℝ} (hKA : 0 ≤ KA)
    (hA : ∀ i j, ‖A i j‖ ≤ KA) (v : Fin n → ℝ) :
    -((n : ℝ) * KA) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMat A i j * v i * v j := by
  have habs : |∑ i, ∑ j, reMat A i j * v i * v j| ≤ (n : ℝ) * KA * ∑ i, (v i) ^ 2 := by
    have h1 : |∑ i : Fin n, ∑ j : Fin n, reMat A i j * v i * v j|
        ≤ ∑ i : Fin n, ∑ j : Fin n, KA * (|v i| * |v j|) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
      have hre : |reMat A i j| ≤ KA := by
        calc |reMat A i j| = |(A i j).re| := rfl
          _ ≤ ‖A i j‖ := Complex.abs_re_le_norm _
          _ ≤ KA := hA i j
      calc |reMat A i j * v i * v j| = |reMat A i j| * |v i| * |v j| := by
            rw [abs_mul, abs_mul]
        _ = |reMat A i j| * (|v i| * |v j|) := by ring
        _ ≤ KA * (|v i| * |v j|) := mul_le_mul_of_nonneg_right hre (by positivity)
    have h2 : ∑ i : Fin n, ∑ j : Fin n, KA * (|v i| * |v j|)
        = KA * ((∑ i, |v i|) ^ 2) := by
      rw [sq, Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
    have h3 : ((∑ i, |v i|) ^ 2) ≤ (n : ℝ) * ∑ i, (v i) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => |v i|)
      simpa [Finset.card_univ, Fintype.card_fin, sq_abs] using h
    calc |∑ i : Fin n, ∑ j : Fin n, reMat A i j * v i * v j|
        ≤ ∑ i : Fin n, ∑ j : Fin n, KA * (|v i| * |v j|) := h1
      _ = KA * ((∑ i, |v i|) ^ 2) := h2
      _ ≤ KA * ((n : ℝ) * ∑ i, (v i) ^ 2) := mul_le_mul_of_nonneg_left h3 hKA
      _ = (n : ℝ) * KA * ∑ i, (v i) ^ 2 := by ring
  linarith [neg_abs_le (∑ i, ∑ j, reMat A i j * v i * v j)]

/-- **Lipschitz comparison of quadratic forms.**  If the entries of `A - A'` are bounded by `M`,
then the two quadratic forms differ by at most `n · M · ∑ vᵢ²`. -/
lemma quadForm_sub_le {n : ℕ} (A A' : MatC n) (v : Fin n → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hd : ∀ i j, ‖A i j - A' i j‖ ≤ M) :
    ∑ i, ∑ j, reMat A i j * v i * v j - ∑ i, ∑ j, reMat A' i j * v i * v j
      ≤ (n : ℝ) * M * ∑ i, (v i) ^ 2 := by
  have hdiff : ∑ i, ∑ j, reMat A i j * v i * v j - ∑ i, ∑ j, reMat A' i j * v i * v j
      = ∑ i, ∑ j, reMat (A - A') i j * v i * v j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [reMat_apply, Pi.sub_apply, Complex.sub_re]
    ring
  rw [hdiff]
  have h1 : ∑ i : Fin n, ∑ j : Fin n, reMat (A - A') i j * v i * v j
      ≤ ∑ i : Fin n, ∑ j : Fin n, M * (|v i| * |v j|) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hre : |reMat (A - A') i j| ≤ M := by
      calc |reMat (A - A') i j| = |((A - A') i j).re| := rfl
        _ ≤ ‖(A - A') i j‖ := Complex.abs_re_le_norm _
        _ ≤ M := hd i j
    calc reMat (A - A') i j * v i * v j
        ≤ |reMat (A - A') i j * v i * v j| := le_abs_self _
      _ = |reMat (A - A') i j| * (|v i| * |v j|) := by
            rw [abs_mul, abs_mul]; ring
      _ ≤ M * (|v i| * |v j|) := mul_le_mul_of_nonneg_right hre (by positivity)
  have h2 : ∑ i : Fin n, ∑ j : Fin n, M * (|v i| * |v j|)
      = M * ((∑ i, |v i|) ^ 2) := by
    rw [sq, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
  have h3 : ((∑ i, |v i|) ^ 2) ≤ (n : ℝ) * ∑ i, (v i) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => |v i|)
    simpa [Finset.card_univ, Fintype.card_fin, sq_abs] using h
  calc ∑ i : Fin n, ∑ j : Fin n, reMat (A - A') i j * v i * v j
      ≤ ∑ i : Fin n, ∑ j : Fin n, M * (|v i| * |v j|) := h1
    _ = M * ((∑ i, |v i|) ^ 2) := h2
    _ ≤ M * ((n : ℝ) * ∑ i, (v i) ^ 2) := mul_le_mul_of_nonneg_left h3 hM
    _ = (n : ℝ) * M * ∑ i, (v i) ^ 2 := by ring

/-! ## STEP 2 (a): the time derivative of the Galerkin solution -/

/-- The time derivative of the `(i,j)`-entry of `seriesFunM (c t) x`, computed from the Galerkin
ODE, as a finite sum over the box. -/
lemma hasDerivAt_seriesFunM {n N : ℕ} {Tc : ℝ} (c : ℝ → (Fin n → ℤ) → MatC n)
    (g : ℝ → (Fin n → ℤ) → MatC n) (hc : ∀ t k', k' ∉ box n N → c t k' = 0)
    (hd : ∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ box n N, ∀ i j,
      HasDerivAt (fun σ => c σ k' i j) (g t k' i j) t)
    (x : Fin n → ℝ) (i j : Fin n) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) Tc) :
    HasDerivAt (fun σ => seriesFunM (c σ) x i j)
      (∑ m : box n N, g t m.1 i j * fourierExp m.1 x) t := by
  classical
  have hcongr : (fun σ => seriesFunM (c σ) x i j)
      = fun σ => ∑ m : box n N, c σ m.1 i j * fourierExp m.1 x := by
    funext σ
    exact seriesFunM_eq_sum (c σ) (hc σ) x i j
  rw [hcongr]
  exact HasDerivAt.fun_sum fun m _ => (hd t ht m.1 m.2 i j).mul_const (fourierExp m.1 x)

/-- **The Lipschitz bound in time.**  If the box Fourier coefficients of the nonlinearity are
summable with `ℓ¹`-norm at most `Λ` on `[0,τ]`, then the entries of `seriesFunM` are
`Λ`-Lipschitz in time on `[0,τ]`. -/
lemma lipschitz_of_l1_bound {n N : ℕ} {Tc : ℝ} (c : ℝ → (Fin n → ℤ) → MatC n)
    (g : ℝ → (Fin n → ℤ) → MatC n) (hc : ∀ t k', k' ∉ box n N → c t k' = 0)
    (hd : ∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ box n N, ∀ i j,
      HasDerivAt (fun σ => c σ k' i j) (g t k' i j) t)
    {Λ τ : ℝ} (hτ : τ < Tc) (hΛ : 0 ≤ Λ)
    (hbdd : ∀ t ∈ Set.Icc (0 : ℝ) τ, ∀ i j,
      Summable (fun m : Fin n → ℤ => ‖g t m i j‖) ∧
      (∑' m : Fin n → ℤ, ‖g t m i j‖) ≤ Λ)
    (x : Fin n → ℝ) (i j : Fin n) :
    ∀ t ∈ Set.Icc (0 : ℝ) τ,
      ‖seriesFunM (c t) x i j - seriesFunM (c 0) x i j‖ ≤ Λ * t := by
  intro t ht
  have hdiff : ∀ σ ∈ Set.Icc (0 : ℝ) τ,
      DifferentiableAt ℝ (fun s => seriesFunM (c s) x i j) σ := by
    intro σ hσ
    exact (hasDerivAt_seriesFunM c g hc hd x i j
      ⟨hσ.1, lt_of_le_of_lt hσ.2 hτ⟩).differentiableAt
  have hderiv : ∀ σ ∈ Set.Icc (0 : ℝ) τ,
      ‖deriv (fun s => seriesFunM (c s) x i j) σ‖ ≤ Λ := by
    intro σ hσ
    rw [(hasDerivAt_seriesFunM c g hc hd x i j ⟨hσ.1, lt_of_le_of_lt hσ.2 hτ⟩).deriv]
    calc ‖∑ m : box n N, g σ m.1 i j * fourierExp m.1 x‖
        ≤ ∑ m : box n N, ‖g σ m.1 i j * fourierExp m.1 x‖ := norm_sum_le _ _
      _ = ∑ m : box n N, ‖g σ m.1 i j‖ := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one]
      _ = ∑ m ∈ box n N, ‖g σ m i j‖ := Finset.sum_attach (box n N) (fun m => ‖g σ m i j‖)
      _ ≤ ∑' m : Fin n → ℤ, ‖g σ m i j‖ :=
          Summable.sum_le_tsum (box n N) (fun m _ => norm_nonneg _) (hbdd σ hσ i j).1
      _ ≤ Λ := (hbdd σ hσ i j).2
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv (convex_Icc 0 τ)
    (Set.left_mem_Icc.mpr (by linarith [ht.1, ht.2] : (0 : ℝ) ≤ τ)) ht
  simpa [Real.norm_eq_abs, abs_of_nonneg ht.1] using h

/-- **Comparison of the quadratic forms at time `t` and at time `0`.** -/
lemma quadForm_time_sub {n N : ℕ} {Tc Λ τ : ℝ} (hΛ : 0 ≤ Λ) (hτ0 : 0 ≤ τ) (hτ : τ < Tc)
    (c : ℝ → (Fin n → ℤ) → MatC n) (g : ℝ → (Fin n → ℤ) → MatC n)
    (hc : ∀ t k', k' ∉ box n N → c t k' = 0)
    (hd : ∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ box n N, ∀ i j,
      HasDerivAt (fun σ => c σ k' i j) (g t k' i j) t)
    (hbdd : ∀ t ∈ Set.Icc (0 : ℝ) τ, ∀ i j,
      Summable (fun m : Fin n → ℤ => ‖g t m i j‖) ∧
      (∑' m : Fin n → ℤ, ‖g t m i j‖) ≤ Λ)
    (x : Fin n → ℝ) (v : Fin n → ℝ) :
    ∑ i, ∑ j, reMat (seriesFunM (c 0) x) i j * v i * v j
        - ∑ i, ∑ j, reMat (seriesFunM (c τ) x) i j * v i * v j
      ≤ (n : ℝ) * (Λ * τ) * ∑ i, (v i) ^ 2 := by
  refine quadForm_sub_le _ _ v (mul_nonneg hΛ hτ0) ?_
  intro i j
  have h := lipschitz_of_l1_bound c g hc hd hτ hΛ hbdd x i j τ ⟨hτ0, le_rfl⟩
  simpa [norm_sub_rev] using h

/-! ## STEP 3: the final assembly -/

/-- **The ellipticity persistence, from the uniform short-time bound on the nonlinearity.**
The hypothesis `hshort` is the content of `Work.Diff.STE.flat.nonlin_bound_short`: on a short
interval `[0, τ]` the Fourier coefficients of the nonlinearity have `ℓ¹`-norm bounded by `Λ`,
uniformly in the Galerkin order `N` and in the data. -/
theorem persist_of_short {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Jet n → MatC n) (hshape : IsDeTurckNonlin Φ)
    (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B)
    (C₀ : ℝ) (hC₀nn : 0 ≤ C₀)
    (hC₀ : ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n), (∀ k', k' ∉ box n N → c k' = 0) →
      ∀ j ≤ k, CSqM j c ≤ C₀ * ENormSqFull k (seriesFunM c))
    (Λ τ : ℝ) (hΛ : 0 ≤ Λ) (hτ : 0 < τ)
    (hshort : ∀ (Tc : ℝ) (hc : 0 < Tc) (N : ℕ) (c : ℝ → (Fin n → ℤ) → MatC n),
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ box n N, ∀ (i j : Fin n),
          HasDerivAt (fun σ => c σ k' i j)
            (fourierCoeff (fun x =>
              Φ (x, jetM (seriesFunM (c t)) x) i j) k') t) →
        (∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ box n N → c t k' = 0) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ j ≤ k, CSqM j (c t) ≤ C₀ * B ^ 2) →
        (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            reMat (seriesFunM (c 0) x) i j * v i * v j) →
        ∀ t ∈ Set.Ico (0 : ℝ) (min τ Tc), ∀ i j : Fin n,
          Summable (fun m : Fin n → ℤ => ‖fourierCoeff
            (fun x => Φ (x, jetM (seriesFunM (c t)) x) i j) m‖) ∧
          (∑' m : Fin n → ℤ, ‖fourierCoeff
            (fun x => Φ (x, jetM (seriesFunM (c t)) x) i j) m‖) ≤ Λ) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (Tc : ℝ) (hc : 0 < Tc) (N : ℕ) (c : ℝ → (Fin n → ℤ) → MatC n),
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ box n N, ∀ (i j : Fin n),
          HasDerivAt (fun σ => c σ k' i j)
            (fourierCoeff (fun x =>
              Φ (x, jetM (seriesFunM (c t)) x) i j) k') t) →
        (∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ box n N → c t k' = 0) →
        (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            reMat (seriesFunM (c 0) x) i j * v i * v j) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc,
          ENormSqFull k (seriesFunM (c t)) ≤ B ^ 2) →
        ∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          (lam - M * t) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            reMat (seriesFunM (c t) x) i j * v i * v j := by
  -- the jet sup bound (uniform in the time and in the data)
  obtain ⟨KA, hKA0, hKAb⟩ := jet_sup_bound (n := n) (k := k) hk B hB
  set Neg : ℝ := (n : ℝ) * KA with hNegdef
  have hNeg0 : 0 ≤ Neg := mul_nonneg (Nat.cast_nonneg n) hKA0
  refine ⟨max ((n : ℝ) * Λ) ((lam + Neg) / τ), ?_, ?_⟩
  · exact le_trans (mul_nonneg (Nat.cast_nonneg n) hΛ) (le_max_left _ _)
  intro Tc hc N c hderiv hsupp hpos0 henergy t ht x v
  -- the ℓ¹ bound on the short interval
  have hbdd : ∀ s ∈ Set.Ico (0 : ℝ) (min τ Tc), ∀ i j : Fin n,
      Summable (fun m : Fin n → ℤ => ‖fourierCoeff
        (fun x => Φ (x, jetM (seriesFunM (c s)) x) i j) m‖) ∧
      (∑' m : Fin n → ℤ, ‖fourierCoeff
        (fun x => Φ (x, jetM (seriesFunM (c s)) x) i j) m‖) ≤ Λ :=
    hshort Tc hc N c hderiv hsupp
      (fun s hs j hj => by
        refine le_trans (hC₀ N (c s) (fun k' hk' => hsupp s k' hk') j hj) ?_
        exact mul_le_mul_of_nonneg_left (henergy s hs) hC₀nn)
      hpos0
  by_cases hcase : t < min τ Tc
  · -- inside the short interval: use the Lipschitz bound and the initial positivity
    have hstep : ∀ (i j : Fin n) (s : ℝ), s ∈ Set.Icc (0 : ℝ) t →
        ‖seriesFunM (c s) x i j - seriesFunM (c 0) x i j‖ ≤ Λ * s := by
      intro i j s hs
      refine lipschitz_of_l1_bound c
        (fun σ m i j => fourierCoeff (fun y => Φ (y, jetM (seriesFunM (c σ)) y) i j) m)
        hsupp hderiv (lt_of_le_of_lt hs.2 ht.2) hΛ ?_ x i j s ⟨hs.1, le_rfl⟩
      · exact fun σ hσ i' j' =>
          hbdd σ ⟨hσ.1, lt_of_le_of_lt (le_trans hσ.2 hs.2) hcase⟩ i' j'
    have hquad := quadForm_sub_le (seriesFunM (c 0) x) (seriesFunM (c t) x) v
      (mul_nonneg hΛ ht.1) (fun i' j' => by
        have h := hstep i' j' t ⟨ht.1, le_rfl⟩
        simpa [norm_sub_rev] using h)
    have hinit := hpos0 x v
    have hS : (0 : ℝ) ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hmid : (lam - (n : ℝ) * Λ * t) * ∑ i, (v i) ^ 2 ≤
        ∑ i, ∑ j, reMat (seriesFunM (c t) x) i j * v i * v j := by
      nlinarith [hquad, hinit, hS]
    have hle : (lam - max ((n : ℝ) * Λ) ((lam + Neg) / τ) * t) * ∑ i, (v i) ^ 2 ≤
        (lam - (n : ℝ) * Λ * t) * ∑ i, (v i) ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ hS
      have h1 : (n : ℝ) * Λ * t ≤ max ((n : ℝ) * Λ) ((lam + Neg) / τ) * t :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) ht.1
      linarith
    linarith [hmid, hle]
  · -- beyond the short interval: the crude lower bound
    have hjet := hKAb N (c t) (fun k' hk' => hsupp t k' hk') (henergy t ht)
    have hcrude := quadForm_ge_neg (seriesFunM (c t) x) hKA0
      (fun i' j' => hjet.1 x i' j') v
    have htτ : τ ≤ t := by
      have h1 : ¬ t < min τ Tc := hcase
      have h2 : t < Tc := ht.2
      by_contra hcon
      exact h1 (lt_min (not_le.mp hcon) h2)
    have hMτ : lam + Neg ≤ max ((n : ℝ) * Λ) ((lam + Neg) / τ) * τ := by
      have h2 : (lam + Neg) / τ * τ = lam + Neg := div_mul_cancel₀ _ (ne_of_gt hτ)
      calc lam + Neg = (lam + Neg) / τ * τ := h2.symm
        _ ≤ max ((n : ℝ) * Λ) ((lam + Neg) / τ) * τ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hτ)
    have hlast : lam - max ((n : ℝ) * Λ) ((lam + Neg) / τ) * t ≤ -Neg := by
      have : max ((n : ℝ) * Λ) ((lam + Neg) / τ) * τ ≤ max ((n : ℝ) * Λ) ((lam + Neg) / τ) * t :=
        mul_le_mul_of_nonneg_left htτ (le_trans (mul_nonneg (Nat.cast_nonneg n) hΛ)
          (le_max_left _ _))
      linarith
    have hsq : (0 : ℝ) ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (v i)
    calc (lam - max ((n : ℝ) * Λ) ((lam + Neg) / τ) * t) * ∑ i, (v i) ^ 2
        ≤ -Neg * ∑ i, (v i) ^ 2 := mul_le_mul_of_nonneg_right hlast hsq
      _ ≤ _ := hcrude

theorem ellipticity_persist {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (Tc : ℝ) (hc : 0 < Tc) (N : ℕ)
        (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ Work.Diff.STE.Flat.box n N, ∀ (i j : Fin n),
          HasDerivAt (fun σ => c σ k' i j)
            (Work.Diff.STE.fourierCoeff (fun x =>
              Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x) i j) k') t) →
        (∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n N → c t k' = 0) →
        (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c 0) x) i j * v i * v j) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc,
          Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM (c t)) ≤ B ^ 2) →
        ∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          (lam - M * t) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c t) x) i j * v i * v j := by
  obtain ⟨C₀, hC₀nn, hC₀⟩ := csqM_le_of_energy (n := n) (k := k)
  obtain ⟨Λ, τ, hΛ, hτ, hshort⟩ :=
    Work.Diff.STE.flat.nonlin_bound_short hn Φ hshape k hk lam hlam (C₀ * B ^ 2)
      (mul_nonneg hC₀nn (sq_nonneg B))
  exact persist_of_short hn Φ hshape k hk lam hlam B hB C₀ hC₀nn hC₀ Λ τ hΛ hτ hshort

end

end Work.Diff.STE.flat
