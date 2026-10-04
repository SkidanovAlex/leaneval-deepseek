import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.exists_subseq_uniform
import Submission.Work.Diff.STE.flat.hasDerivWithinAt_of_tendstoUniformlyOn
import Submission.Work.Diff.STE.flat.galerkin_uniform_bound
import Submission.Work.Diff.STE.flat.continuousOn_phi_jet
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.tail_tsum_box_tendsto_zero
import Submission.Work.Diff.STE.flat.norm_fourierCoeff_sub_le
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.CSq_le_ENormSq_seriesFun
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.norm_seriesFun_le
import Submission.Work.Diff.STE.pd_seriesFun
import Submission.Work.Diff.STE.summable_wt_zpow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

set_option maxHeartbeats 8000000

open Filter Set MeasureTheory
open Work.Diff.STE.Flat
open scoped BigOperators

noncomputable section

/-! ## Elementary estimates -/

theorem sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  have h1 : Real.sqrt x ≤ Real.sqrt ((1 + x) ^ 2) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith
  rwa [Real.sqrt_sq (by linarith)] at h1

/-- The zeroth iterated derivative is the function itself. -/
theorem pdVec_zero_eq {n : ℕ} (l : Fin 0 → Fin n) (f : (Fin n → ℝ) → ℂ) :
    pdVec 0 l f = f := by
  simp [pdVec, pdList]

/-- The norm of a matrix is at most the sum of the norms of its entries. -/
theorem norm_matC_le_sum {n : ℕ} (A : MatC n) :
    ‖A‖ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ := by
  have h1 : ∀ i : Fin n, ‖A i‖ ≤ ∑ j : Fin n, ‖A i j‖ := by
    intro i
    refine (pi_norm_le_iff_of_nonneg
      (Finset.sum_nonneg fun (j : Fin n) _ => norm_nonneg (A i j))).mpr fun (j : Fin n) => ?_
    exact Finset.single_le_sum (fun (b : Fin n) _ => norm_nonneg (A i b)) (Finset.mem_univ j)
  have h2 : ‖A‖ ≤ ∑ i : Fin n, ‖A i‖ :=
    (pi_norm_le_iff_of_nonneg
      (Finset.sum_nonneg fun (i : Fin n) _ => norm_nonneg (A i))).mpr fun (i : Fin n) => by
      exact Finset.single_le_sum (fun (a : Fin n) _ => norm_nonneg (A a)) (Finset.mem_univ i)
  exact h2.trans (Finset.sum_le_sum fun (i : Fin n) _ => h1 i)

/-- Along a sequence of box levels tending to infinity, every frequency eventually lies in the
box. -/
theorem eventually_mem_box_comp {n : ℕ} {Nb φ : ℕ → ℕ} (hNb : Tendsto Nb atTop atTop)
    (hφ : Tendsto φ atTop atTop) (k : Fin n → ℤ) :
    ∃ M₀ : ℕ, ∀ m ≥ M₀, k ∈ box n (Nb (φ m)) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((hNb.comp hφ).eventually_ge_atTop (∑ i, (k i).natAbs))
  exact ⟨N₀, fun m hm => mem_box_of_bd_le (hN₀ m hm)⟩

/-! ## The energy-versus-coefficients constant -/

/-- The constant in the inequality `CSq s c ≤ C · (ENormSq s + ENormSq 0)` of
`Work.Diff.STE.CSq_le_ENormSq_seriesFun`. -/
def csqC (n s : ℕ) : ℝ :=
  Classical.choose (Work.Diff.STE.CSq_le_ENormSq_seriesFun (ι := Fin n) s)

theorem csqC_nonneg (n s : ℕ) : 0 ≤ csqC n s :=
  (Classical.choose_spec (Work.Diff.STE.CSq_le_ENormSq_seriesFun (ι := Fin n) s)).1

theorem csqC_le {n s : ℕ} (c : (Fin n → ℤ) → ℂ)
    (h : ∀ N : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖c k‖)) :
    Work.Diff.STE.CSq s c ≤ csqC n s * (Work.Diff.STE.ENormSq s (Work.Diff.STE.seriesFun c)
      + Work.Diff.STE.ENormSq 0 (Work.Diff.STE.seriesFun c)) :=
  (Classical.choose_spec (Work.Diff.STE.CSq_le_ENormSq_seriesFun (ι := Fin n) s)).2 c h

/-- An entrywise `CSq` bound in terms of the energy of the series. -/
theorem CSq_entry_le_energy {n N s : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) (i j : Fin n) :
    Work.Diff.STE.CSq s (fun k => c k i j)
      ≤ 2 * csqC n s * ENormSqFull s (seriesFunM c) := by
  have hmom : ∀ t : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ t * ‖c k i j‖) :=
    fun t => summable_moment_box c hc i j t
  have h := csqC_le (n := n) (s := s) (fun k => c k i j) hmom
  have hfun : (fun x : Fin n → ℝ => seriesFunM c x i j) = Work.Diff.STE.seriesFun
      (fun k => c k i j) := by
    funext x; rw [seriesFunM_apply]
  have h1 : Work.Diff.STE.ENormSq s (Work.Diff.STE.seriesFun (fun k => c k i j))
      ≤ ENormSqFull s (seriesFunM c) := by
    rw [← hfun]; exact ENormSq_le_ENormSqFull (seriesFunM c) i j
  have h2 : Work.Diff.STE.ENormSq 0 (Work.Diff.STE.seriesFun (fun k => c k i j))
      ≤ ENormSqFull s (seriesFunM c) := by
    rw [← hfun]; exact ENormSq_zero_le_ENormSqFull (seriesFunM c) i j
  calc Work.Diff.STE.CSq s (fun k => c k i j)
      ≤ csqC n s * (Work.Diff.STE.ENormSq s (Work.Diff.STE.seriesFun (fun k => c k i j))
        + Work.Diff.STE.ENormSq 0 (Work.Diff.STE.seriesFun (fun k => c k i j))) := h
    _ ≤ csqC n s * (ENormSqFull s (seriesFunM c) + ENormSqFull s (seriesFunM c)) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (csqC_nonneg n s)
    _ = 2 * csqC n s * ENormSqFull s (seriesFunM c) := by ring

/-- Pointwise decay of the coefficients of a box-supported family satisfying uniform energy
bounds. -/
theorem coeff_decay_of_energy {n N : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) {Blim : ℕ → ℝ}
    (hBlim : ∀ j : ℕ, 0 ≤ Blim j)
    (hE : ∀ j : ℕ, ENormSqFull j (seriesFunM c) ≤ Blim j)
    (M : ℕ) (k : Fin n → ℤ) (i j : Fin n) :
    ‖c k i j‖ * (wt k) ^ M ≤ (1 + 2 * csqC n (2 * M)) * (1 + Blim (2 * M)) := by
  have hmom : ∀ t : ℕ, Summable (fun l : Fin n → ℤ => (wt l) ^ t * ‖c l i j‖) :=
    fun t => summable_moment_box c hc i j t
  have hsq : Summable (fun l : Fin n → ℤ => (wt l) ^ (2 * M) * ‖c l i j‖ ^ 2) :=
    Work.Diff.STE.summable_wt_pow_mul_norm_sq (fun l => c l i j) hmom (2 * M)
  have hle : (wt k) ^ (2 * M) * ‖c k i j‖ ^ 2 ≤ Work.Diff.STE.CSq (2 * M) (fun l => c l i j) :=
    hsq.le_tsum k (fun l _ => mul_nonneg (pow_nonneg (wt_pos l).le _) (sq_nonneg _))
  have hCE := CSq_entry_le_energy (N := N) c hc i j (s := 2 * M)
  have hkey : (‖c k i j‖ * (wt k) ^ M) ^ 2 ≤ 2 * csqC n (2 * M) * Blim (2 * M) := by
    have h3 : (‖c k i j‖ * (wt k) ^ M) ^ 2 = (wt k) ^ (2 * M) * ‖c k i j‖ ^ 2 := by
      have h4 : (wt k) ^ (M * 2) = (wt k) ^ (2 * M) := by rw [mul_comm]
      rw [mul_pow, ← pow_mul, h4, mul_comm]
    rw [h3]
    exact hle.trans (hCE.trans (mul_le_mul_of_nonneg_left (hE (2 * M))
      (mul_nonneg (by norm_num) (csqC_nonneg n (2 * M)))))
  have hnn : 0 ≤ 2 * csqC n (2 * M) * Blim (2 * M) :=
    mul_nonneg (mul_nonneg (by norm_num) (csqC_nonneg n (2 * M))) (hBlim (2 * M))
  have hroot : ‖c k i j‖ * (wt k) ^ M ≤ 1 + 2 * csqC n (2 * M) * Blim (2 * M) := by
    have h1 := Real.sqrt_le_sqrt hkey
    rw [Real.sqrt_sq (mul_nonneg (norm_nonneg _) (pow_nonneg (wt_pos k).le _))] at h1
    exact h1.trans (sqrt_le_one_add hnn)
  have hA : (0 : ℝ) ≤ 1 + 2 * csqC n (2 * M) := by linarith [csqC_nonneg n (2 * M)]
  have hB : (0 : ℝ) ≤ 1 + Blim (2 * M) := by linarith [hBlim (2 * M)]
  have hc0 : (0 : ℝ) ≤ csqC n (2 * M) := csqC_nonneg n (2 * M)
  have hB0 : (0 : ℝ) ≤ Blim (2 * M) := hBlim (2 * M)
  calc ‖c k i j‖ * (wt k) ^ M ≤ 1 + 2 * csqC n (2 * M) * Blim (2 * M) := hroot
    _ ≤ (1 + 2 * csqC n (2 * M)) * (1 + Blim (2 * M)) := by nlinarith

/-- Summability of the dual weight. -/
theorem summable_wt_inv (n s : ℕ) (hs : Fintype.card (Fin n) < 2 * s) :
    Summable (fun k : Fin n → ℤ => ((wt k) ^ s)⁻¹) :=
  (Work.Diff.STE.summable_wt_zpow (ι := Fin n) s hs).congr fun k => by simp [zpow_neg]

/-- Power-decay of a coefficient family implies summability of every weighted `ℓ²` sum. -/
theorem summable_weighted_of_decay {n : ℕ} (s : ℕ) {Mdec : ℕ} (hM : s + n + 1 ≤ Mdec)
    {Cdec : ℝ} {γ : (Fin n → ℤ) → ℂ}
    (h : ∀ k : Fin n → ℤ, ‖γ k‖ * (wt k) ^ Mdec ≤ Cdec) :
    Summable (fun k : Fin n → ℤ => (wt k) ^ s * ‖γ k‖ ^ 2) := by
  have hsM : s ≤ Mdec := by omega
  have hcard : Fintype.card (Fin n) < 2 * Mdec := by
    rw [Fintype.card_fin]; omega
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (wt_pos k).le s) (sq_nonneg _)) (fun k => ?_)
    ((summable_wt_inv n Mdec hcard).mul_left (Cdec ^ 2))
  have hx : (0 : ℝ) < (wt k) ^ Mdec := pow_pos (wt_pos k) Mdec
  have hle : ‖γ k‖ ≤ Cdec * ((wt k) ^ Mdec)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hx]
    exact h k
  have hxs : (wt k) ^ s ≤ (wt k) ^ Mdec := pow_le_pow_right₀ (wt_one_le k) hsM
  have hkey : (wt k) ^ s * (((wt k) ^ Mdec)⁻¹) ^ 2 ≤ ((wt k) ^ Mdec)⁻¹ := by
    have h2 : (wt k) ^ Mdec * (((wt k) ^ Mdec)⁻¹) ^ 2 = ((wt k) ^ Mdec)⁻¹ := by
      rw [pow_two, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hx), one_mul]
    calc (wt k) ^ s * (((wt k) ^ Mdec)⁻¹) ^ 2
        = (wt k) ^ s * (((wt k) ^ Mdec) ^ 2)⁻¹ := by rw [inv_pow]
      _ ≤ (wt k) ^ Mdec * (((wt k) ^ Mdec) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hxs (inv_nonneg.mpr (by positivity))
      _ = (wt k) ^ Mdec * (((wt k) ^ Mdec)⁻¹) ^ 2 := by rw [inv_pow]
      _ = ((wt k) ^ Mdec)⁻¹ := h2
  calc (wt k) ^ s * ‖γ k‖ ^ 2
      ≤ (wt k) ^ s * (Cdec * ((wt k) ^ Mdec)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hle 2)
          (pow_nonneg (wt_pos k).le s)
    _ = Cdec ^ 2 * ((wt k) ^ s * (((wt k) ^ Mdec)⁻¹) ^ 2) := by ring
    _ ≤ Cdec ^ 2 * ((wt k) ^ Mdec)⁻¹ := mul_le_mul_of_nonneg_left hkey (sq_nonneg _)

/-- Power-decay of a coefficient family implies summability of every weighted `ℓ¹` sum. -/
theorem summable_l1_of_decay {n : ℕ} (N : ℕ) {Mdec : ℕ} (hM : N + n + 1 ≤ Mdec)
    {Cdec : ℝ} {γ : (Fin n → ℤ) → ℂ}
    (h : ∀ k : Fin n → ℤ, ‖γ k‖ * (wt k) ^ Mdec ≤ Cdec) :
    Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖γ k‖) := by
  have hNM : N ≤ Mdec := by omega
  have hcard : Fintype.card (Fin n) < 2 * (Mdec - N) := by
    rw [Fintype.card_fin]; omega
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (wt_pos k).le N) (norm_nonneg _)) (fun k => ?_)
    (by
      have := (summable_wt_inv n (Mdec - N) hcard).mul_left Cdec
      simpa using this)
  have hw : 0 < (wt k) ^ Mdec := pow_pos (wt_pos k) Mdec
  have hle : ‖γ k‖ ≤ Cdec * ((wt k) ^ Mdec)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hw]
    exact h k
  have hsplit : (wt k) ^ Mdec = (wt k) ^ (Mdec - N) * (wt k) ^ N := by
    rw [← pow_add, Nat.sub_add_cancel hNM]
  have hxn : (wt k) ^ N ≠ 0 := pow_ne_zero _ (ne_of_gt (wt_pos k))
  calc (wt k) ^ N * ‖γ k‖ ≤ (wt k) ^ N * (Cdec * ((wt k) ^ Mdec)⁻¹) :=
        mul_le_mul_of_nonneg_left hle (pow_nonneg (wt_pos k).le N)
    _ = Cdec * ((wt k) ^ N * ((wt k) ^ Mdec)⁻¹) := by ring
    _ = Cdec * ((wt k) ^ (Mdec - N))⁻¹ := by
        rw [hsplit, mul_inv_rev]
        congr 1
        rw [← mul_assoc, mul_inv_cancel₀ hxn, one_mul]

/-! ## Uniform limits of coefficient families -/

/-- If a sequence of coefficient families has uniformly bounded weighted `ℓ²` masses and
converges coefficientwise, then the same bound holds for the limit. -/
theorem weighted_limit_le {n s : ℕ} {A : ℝ}
    {γ : ℕ → (Fin n → ℤ) → ℂ} {γlim : (Fin n → ℤ) → ℂ}
    (hbd : ∀ m, Summable (fun k : Fin n → ℤ => (wt k) ^ s * ‖γ m k‖ ^ 2) ∧
      (∑' k : Fin n → ℤ, (wt k) ^ s * ‖γ m k‖ ^ 2) ≤ A)
    (hconv : ∀ k : Fin n → ℤ, Tendsto (fun m => γ m k) atTop (nhds (γlim k)))
    (hsum : Summable (fun k : Fin n → ℤ => (wt k) ^ s * ‖γlim k‖ ^ 2)) :
    (∑' k : Fin n → ℤ, (wt k) ^ s * ‖γlim k‖ ^ 2) ≤ A := by
  refine Summable.tsum_le_of_sum_le hsum (fun F => ?_)
  have hfin : Tendsto (fun m => ∑ k ∈ F, (wt k) ^ s * ‖γ m k‖ ^ 2) atTop
      (nhds (∑ k ∈ F, (wt k) ^ s * ‖γlim k‖ ^ 2)) := by
    refine tendsto_finsetSum F (fun k _ => ?_)
    have h1 : Tendsto (fun m => ‖γ m k‖ ^ 2) atTop (nhds (‖γlim k‖ ^ 2)) :=
      ((hconv k).norm).pow 2
    exact h1.const_mul ((wt k) ^ s)
  have hb : ∀ m, ∑ k ∈ F, (wt k) ^ s * ‖γ m k‖ ^ 2 ≤ A := fun m =>
    ((hbd m).1.sum_le_tsum F
      (fun k _ => mul_nonneg (pow_nonneg (wt_pos k).le s) (sq_nonneg _))).trans (hbd m).2
  exact le_trans (le_of_tendsto hfin (Eventually.of_forall hb)) le_rfl

/-- The multiplier `dmulV` preserves the weighted `ℓ²` summability class. -/
theorem summable_weighted_dmulV {n : ℕ} (l : List (Fin n)) (s : ℕ) {γ : (Fin n → ℤ) → ℂ}
    (h : Summable (fun k : Fin n → ℤ => (wt k) ^ (s + l.length) * ‖γ k‖ ^ 2)) :
    Summable (fun k : Fin n → ℤ => (wt k) ^ s * ‖dmulV l γ k‖ ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (wt_pos k).le s) (sq_nonneg _)) (fun k => ?_)
    (h.mul_left (((2 * Real.pi) ^ 2) ^ l.length))
  have hstep : (wt k) ^ s * (((2 * Real.pi) ^ 2 * wt k) ^ l.length * ‖γ k‖ ^ 2)
      = ((2 * Real.pi) ^ 2) ^ l.length * ((wt k) ^ (s + l.length) * ‖γ k‖ ^ 2) := by
    rw [mul_pow, pow_add]
    ring
  exact (mul_le_mul_of_nonneg_left (Work.Diff.STE.norm_sq_dmulV_le l γ k)
    (pow_nonneg (wt_pos k).le s)).trans (le_of_eq hstep)

/-- A finite sum of sequences tending uniformly to `0` tends uniformly to `0`. -/
theorem uniform_sum_zero {ι T : Type*} [Fintype ι] {f : ℕ → ι → T → ℝ}
    (h : ∀ p : ι, ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ m ≥ M₀, ∀ t : T, ‖f m p t‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ m ≥ M₀, ∀ t : T, ‖∑ p, f m p t‖ ≤ ε := by
  intro ε hε
  have hN : (0 : ℝ) < Fintype.card ι + 1 := by positivity
  choose M hM using fun p : ι => h p (ε / (Fintype.card ι + 1))
    (div_pos hε (by positivity))
  refine ⟨Finset.univ.sup M, fun m hm t => ?_⟩
  have hterm : ∀ p : ι, ‖f m p t‖ ≤ ε / (Fintype.card ι + 1) := fun p =>
    hM p m (le_trans (Finset.le_sup (Finset.mem_univ p)) hm) t
  calc ‖∑ p, f m p t‖ ≤ ∑ p, ‖f m p t‖ := norm_sum_le _ _
    _ ≤ ∑ _p : ι, ε / (Fintype.card ι + 1) := Finset.sum_le_sum fun p _ => hterm p
    _ = (Fintype.card ι : ℝ) * (ε / (Fintype.card ι + 1)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ε := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ hN]
        nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι), hε.le]


/-! ## Local copies of the jet bounds

The following lemmas are proved in `flat/ellipticity_persist.lean`; they are reproduced here
(with primed names) so that this module does not depend on that (rapidly moving) file. -/

/-- The Sobolev level `sob n + 2` is below any `k` with `card (Fin n) + 4 < 2 k`. -/
private lemma sob_add_two_le' {n k : ℕ} (hk : Fintype.card (Fin n) + 4 < 2 * k) :
    sob n + 2 ≤ k := by
  have hc : Fintype.card (Fin n) = n := Fintype.card_fin n
  rw [hc] at hk
  unfold sob
  omega

/-- `pdM` in terms of `pdVec`. -/
private lemma pdM_eq_pdVec_one' {n : ℕ} (d : Fin n) (u : Torus n) (x : Fin n → ℝ)
    (i j : Fin n) :
    pdM d u x i j = pdVec 1 (fun _ : Fin 1 => d) (fun y => u y i j) x := by
  simp [pdM, pdVec, pdList]

/-- The second derivative of the jet in terms of `pdVec`. -/
private lemma pdM_pdM_eq_pdVec_two' {n : ℕ} (d e : Fin n) (u : Torus n) (x : Fin n → ℝ)
    (i j : Fin n) :
    pdM d (pdM e u) x i j = pdVec 2 (Fin.cases d (fun _ : Fin 1 => e))
      (fun y => u y i j) x := by
  simp [pdM, pdVec, pdList]

/-- The value of the jet in terms of `pdVec`. -/
private lemma zero_eq_pdVec_zero' {n : ℕ} (u : Torus n) (x : Fin n → ℝ) (i j : Fin n) :
    u x i j = pdVec 0 (fun _ : Fin 0 => i) (fun y => u y i j) x := by
  simp [pdVec, pdList]

/-- Uniform sup bounds for the derivatives of `seriesFunM c`. -/
private theorem jet_sup_le_uniform' {n k m : ℕ} (hm : m + sob n ≤ k) :
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

/-- The jet sup bounds from the level-`k` energy bound. -/
private theorem jet_sup_bound' {n k : ℕ} (hk : Fintype.card (Fin n) + 4 < 2 * k) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ KA : ℝ, 0 ≤ KA ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k', k' ∉ box n N → c k' = 0) →
      ENormSqFull k (seriesFunM c) ≤ B ^ 2 →
      (∀ x (i j : Fin n), ‖seriesFunM c x i j‖ ≤ KA) ∧
      (∀ x (d : Fin n) (i j : Fin n), ‖pdM d (seriesFunM c) x i j‖ ≤ KA) ∧
      (∀ x (d e : Fin n) (i j : Fin n), ‖pdM d (pdM e (seriesFunM c)) x i j‖ ≤ KA) := by
  have hsobk : sob n + 2 ≤ k := sob_add_two_le' hk
  have hs0 : 0 + sob n ≤ k := by omega
  have hs1 : 1 + sob n ≤ k := by omega
  have hs2 : 2 + sob n ≤ k := by omega
  obtain ⟨C0, hC0nn, h0⟩ := jet_sup_le_uniform' (n := n) (k := k) (m := 0) hs0
  obtain ⟨C1, hC1nn, h1⟩ := jet_sup_le_uniform' (n := n) (k := k) (m := 1) hs1
  obtain ⟨C2, hC2nn, h2⟩ := jet_sup_le_uniform' (n := n) (k := k) (m := 2) hs2
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
    rw [zero_eq_pdVec_zero' (seriesFunM c)]
    exact hstep C0 (le_trans (le_max_left C0 C1) (le_max_left (max C0 C1) C2)) _ h
  · intro x d i j
    have h := h1 N c hc (fun _ : Fin 1 => d) i j x
    rw [pdM_eq_pdVec_one' d (seriesFunM c)]
    exact hstep C1 (le_trans (le_max_right C0 C1) (le_max_left (max C0 C1) C2)) _ h
  · intro x d e i j
    have h := h2 N c hc (Fin.cases d (fun _ : Fin 1 => e)) i j x
    rw [pdM_pdM_eq_pdVec_two' d e (seriesFunM c)]
    exact hstep C2 (le_max_right (max C0 C1) C2) _ h


/-- The multiplier `dmulV` shifts the power-decay level by its length. -/
theorem dmulV_decay {n : ℕ} {M : ℕ} {C : ℝ} {γ : (Fin n → ℤ) → ℂ} (l : List (Fin n))
    (hl : l.length ≤ 2) (h : ∀ k : Fin n → ℤ, ‖γ k‖ * (wt k) ^ (M + 2) ≤ C) (k : Fin n → ℤ) :
    ‖dmulV l γ k‖ * (wt k) ^ M ≤ (2 * Real.pi) ^ 2 * C := by
  have hw1 : (1 : ℝ) ≤ 2 * Real.pi * wt k := by
    have := wt_one_le k
    nlinarith [Real.pi_gt_three]
  have h2 : (2 * Real.pi * wt k) ^ l.length ≤ (2 * Real.pi * wt k) ^ 2 :=
    pow_le_pow_right₀ hw1 hl
  have h3 : (2 * Real.pi * wt k) ^ 2 = (2 * Real.pi) ^ 2 * (wt k) ^ 2 := by rw [mul_pow]
  calc ‖dmulV l γ k‖ * (wt k) ^ M
      ≤ ((2 * Real.pi * wt k) ^ l.length * ‖γ k‖) * (wt k) ^ M :=
        mul_le_mul_of_nonneg_right (Work.Diff.STE.norm_dmulV_le l γ k)
          (pow_nonneg (wt_pos k).le M)
    _ ≤ ((2 * Real.pi * wt k) ^ 2 * ‖γ k‖) * (wt k) ^ M := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (wt_pos k).le M)
        exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = (2 * Real.pi) ^ 2 * (‖γ k‖ * (wt k) ^ (M + 2)) := by
        rw [h3, pow_add]
        ring
    _ ≤ (2 * Real.pi) ^ 2 * C :=
        mul_le_mul_of_nonneg_left (h k) (by positivity)

/-- **Uniform convergence of a Fourier series from coefficientwise convergence and a uniform
power decay bound.** -/
private theorem series_uniform_of_coeff_uniform {n : ℕ} {T : Type*}
    {γ : ℕ → T → (Fin n → ℤ) → ℂ} {γlim : T → (Fin n → ℤ) → ℂ}
    {M : ℕ} (hM : n < 2 * M) {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ (m : ℕ) (t : T) (k : Fin n → ℤ), ‖γ m t k‖ * (wt k) ^ M ≤ C)
    (hdeclim : ∀ (t : T) (k : Fin n → ℤ), ‖γlim t k‖ * (wt k) ^ M ≤ C)
    (hclim : ∀ k : Fin n → ℤ, ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ m ≥ M₀, ∀ t : T,
      ‖γ m t k - γlim t k‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ m ≥ M₀, ∀ t : T, ∀ x : Fin n → ℝ,
      ‖seriesFun (γ m t) x - seriesFun (γlim t) x‖ ≤ ε := by
  have hw : Summable (fun k : Fin n → ℤ => ((wt k) ^ M)⁻¹) :=
    (Work.Diff.STE.summable_wt_zpow (ι := Fin n) M (by rwa [Fintype.card_fin])).congr
      fun k => by simp [zpow_neg]
  have hsumm : ∀ (f : (Fin n → ℤ) → ℂ), (∀ k, ‖f k‖ * (wt k) ^ M ≤ C) →
      Summable (fun k : Fin n → ℤ => ‖f k‖) := by
    intro f hf
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hw.mul_left C)
    have hw1 : 0 < (wt k) ^ M := pow_pos (wt_pos k) M
    rw [← div_eq_mul_inv, le_div_iff₀ hw1]
    exact hf k
  -- the box-complement tail of the dual weight tends to `0`
  have htail : Tendsto (fun N : ℕ =>
      ∑' k : Fin n → ℤ, (if k ∈ box n N then (0 : ℝ) else ((wt k) ^ M)⁻¹))
      atTop (nhds 0) := by
    have hbox : Tendsto (fun N : ℕ => ∑ k ∈ box n N, ((wt k) ^ M)⁻¹) atTop
        (nhds (∑' k : Fin n → ℤ, ((wt k) ^ M)⁻¹)) :=
      hw.hasSum.comp (tendsto_box_atTop (n := n))
    have hlim : Tendsto (fun N : ℕ => (∑' k : Fin n → ℤ, ((wt k) ^ M)⁻¹)
        - ∑ k ∈ box n N, ((wt k) ^ M)⁻¹) atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := ∑' k : Fin n → ℤ, ((wt k) ^ M)⁻¹)).sub hbox
      simpa using this
    refine hlim.congr' ?_
    filter_upwards with N
    rw [eq_comm]
    have h1 : Summable (fun k : Fin n → ℤ =>
        if k ∈ box n N then (0 : ℝ) else ((wt k) ^ M)⁻¹) := by
      refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hw
      · by_cases hk : k ∈ box n N
        · simp only [hk, if_true]; exact le_refl 0
        · simp only [hk, if_false]
          exact inv_nonneg.mpr (pow_nonneg (wt_pos k).le M)
      · by_cases hk : k ∈ box n N
        · simp only [hk, if_true]; exact inv_nonneg.mpr (pow_nonneg (wt_pos k).le M)
        · simp only [hk, if_false]; exact le_refl _
    have h2 : Summable (fun k : Fin n → ℤ =>
        if k ∈ box n N then ((wt k) ^ M)⁻¹ else 0) := by
      refine summable_of_ne_finset_zero (s := box n N) ?_
      intro k hk
      simp [hk]
    have hcongr : (∑' k : Fin n → ℤ, ((wt k) ^ M)⁻¹)
        = (∑' k : Fin n → ℤ, (if k ∈ box n N then (0 : ℝ) else ((wt k) ^ M)⁻¹))
          + (∑' k : Fin n → ℤ, (if k ∈ box n N then ((wt k) ^ M)⁻¹ else 0)) := by
      rw [← Summable.tsum_add h1 h2]
      exact tsum_congr fun k => by by_cases hk : k ∈ box n N <;> simp [hk]
    have h3 : (∑' k : Fin n → ℤ, (if k ∈ box n N then ((wt k) ^ M)⁻¹ else 0))
        = ∑ k ∈ box n N, ((wt k) ^ M)⁻¹ := by
      rw [tsum_eq_sum (s := box n N) (f := fun k : Fin n → ℤ =>
        if k ∈ box n N then ((wt k) ^ M)⁻¹ else 0) (fun k hk => by simp [hk])]
      exact Finset.sum_congr rfl fun k hk => by simp [hk]
    rw [hcongr, h3]
    ring
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ,
      2 * C * (∑' k : Fin n → ℤ, (if k ∈ box n N then (0 : ℝ) else ((wt k) ^ M)⁻¹)) ≤ ε / 2 := by
    have h1 : ∀ᶠ N in atTop, (∑' k : Fin n → ℤ, (if k ∈ box n N then (0 : ℝ) else ((wt k) ^ M)⁻¹))
        ≤ (ε / 2) / (2 * C + 1) :=
      htail.eventually (eventually_le_nhds (by positivity))
    obtain ⟨N, hN⟩ := h1.exists
    refine ⟨N, ?_⟩
    refine (mul_le_mul_of_nonneg_left hN (by positivity)).trans ?_
    rw [mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < 2 * C + 1)]
    nlinarith
  have hhead : ∃ M₀ : ℕ, ∀ m ≥ M₀, ∀ t : T,
      ∑ k ∈ box n N, ‖γ m t k - γlim t k‖ ≤ ε / 2 := by
    have hε' : (0 : ℝ) < ε / 2 / ((box n N).card + 1) := by positivity
    choose Mb hMb using fun k : Fin n → ℤ =>
      hclim k (ε / 2 / ((box n N).card + 1)) hε'
    refine ⟨(box n N).sup Mb, fun m hm t => ?_⟩
    refine (Finset.sum_le_sum fun k hk =>
      hMb k m (le_trans (Finset.le_sup hk) hm) t).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [mul_div_assoc', div_le_iff₀ (by positivity : (0 : ℝ) < ((box n N).card : ℝ) + 1)]
    nlinarith [Nat.cast_nonneg (α := ℝ) ((box n N).card), hε.le]
  obtain ⟨M₀, hM₀⟩ := hhead
  refine ⟨M₀, fun m hm t x => ?_⟩
  have hsm : Summable (fun k : Fin n → ℤ => ‖γ m t k‖) := hsumm _ (fun k => hdec m t k)
  have hsl : Summable (fun k : Fin n → ℤ => ‖γlim t k‖) := hsumm _ (fun k => hdeclim t k)
  have hmh : Summable (fun k : Fin n → ℤ => ‖γ m t k - γlim t k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => norm_sub_le _ _) (hsm.add hsl)
  have hmain : ‖seriesFun (γ m t) x - seriesFun (γlim t) x‖
      ≤ ∑' k : Fin n → ℤ, ‖γ m t k - γlim t k‖ := by
    have hsub : (∑' k : Fin n → ℤ, γ m t k * fourierExp k x)
          - (∑' k : Fin n → ℤ, γlim t k * fourierExp k x)
        = ∑' k : Fin n → ℤ, (γ m t k - γlim t k) * fourierExp k x := by
      rw [← Summable.tsum_sub]
      · exact tsum_congr fun k => by ring
      · exact Summable.of_norm (by simpa only [norm_mul, norm_fourierExp, mul_one] using hsm)
      · exact Summable.of_norm (by simpa only [norm_mul, norm_fourierExp, mul_one] using hsl)
    rw [seriesFun, seriesFun, hsub]
    have hs : Summable (fun k : Fin n → ℤ => ‖(γ m t k - γlim t k) * fourierExp k x‖) := by
      simpa only [norm_mul, norm_fourierExp, mul_one] using hmh
    refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq ?_)
    exact tsum_congr fun k => by rw [norm_mul, norm_fourierExp, mul_one]
  have hsplit : ∑' k : Fin n → ℤ, ‖γ m t k - γlim t k‖
      ≤ (∑ k ∈ box n N, ‖γ m t k - γlim t k‖)
        + 2 * C * (∑' k : Fin n → ℤ, (if k ∈ box n N then (0 : ℝ) else ((wt k) ^ M)⁻¹)) := by
    have h1 : Summable (fun k : Fin n → ℤ =>
        if k ∈ box n N then ‖γ m t k - γlim t k‖ else 0) := by
      refine summable_of_ne_finset_zero (s := box n N) ?_
      intro k hk
      simp [hk]
    have h2 : Summable (fun k : Fin n → ℤ =>
        if k ∈ box n N then (0 : ℝ) else ‖γ m t k - γlim t k‖) := by
      refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (hsm.add hsl)
      · by_cases hk : k ∈ box n N
        · simp only [hk, if_true]; exact le_refl 0
        · simp only [hk, if_false]; exact norm_nonneg _
      · by_cases hk : k ∈ box n N
        · simp only [hk, if_true]; exact add_nonneg (norm_nonneg _) (norm_nonneg _)
        · simp only [hk, if_false]; exact norm_sub_le _ _
    have hdecomp : (∑' k : Fin n → ℤ, ‖γ m t k - γlim t k‖)
        = (∑' k : Fin n → ℤ, (if k ∈ box n N then ‖γ m t k - γlim t k‖ else 0))
          + (∑' k : Fin n → ℤ, (if k ∈ box n N then (0 : ℝ) else ‖γ m t k - γlim t k‖)) := by
      rw [← Summable.tsum_add h1 h2]
      exact tsum_congr fun k => by by_cases hk : k ∈ box n N <;> simp [hk]
    have hfst : (∑' k : Fin n → ℤ, (if k ∈ box n N then ‖γ m t k - γlim t k‖ else 0))
        = ∑ k ∈ box n N, ‖γ m t k - γlim t k‖ := by
      rw [tsum_eq_sum (s := box n N) (f := fun k : Fin n → ℤ =>
        if k ∈ box n N then ‖γ m t k - γlim t k‖ else 0) (fun k hk => by simp [hk])]
      exact Finset.sum_congr rfl fun k hk => by simp [hk]
    have hsnd : (∑' k : Fin n → ℤ, (if k ∈ box n N then (0 : ℝ) else ‖γ m t k - γlim t k‖))
        ≤ 2 * C * (∑' k : Fin n → ℤ, (if k ∈ box n N then (0 : ℝ) else ((wt k) ^ M)⁻¹)) := by
      rw [← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun k => ?_) h2 ?_
      · by_cases hk : k ∈ box n N
        · simp [hk]
        · simp only [hk, if_false]
          have h1' : ‖γ m t k‖ ≤ C * ((wt k) ^ M)⁻¹ := by
            have hw1 : 0 < (wt k) ^ M := pow_pos (wt_pos k) M
            rw [← div_eq_mul_inv, le_div_iff₀ hw1]
            exact hdec m t k
          have h2' : ‖γlim t k‖ ≤ C * ((wt k) ^ M)⁻¹ := by
            have hw1 : 0 < (wt k) ^ M := pow_pos (wt_pos k) M
            rw [← div_eq_mul_inv, le_div_iff₀ hw1]
            exact hdeclim t k
          calc ‖γ m t k - γlim t k‖ ≤ ‖γ m t k‖ + ‖γlim t k‖ := norm_sub_le _ _
            _ ≤ C * ((wt k) ^ M)⁻¹ + C * ((wt k) ^ M)⁻¹ := add_le_add h1' h2'
            _ = 2 * C * ((wt k) ^ M)⁻¹ := by ring
      · refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (hw.mul_left (2 * C))
        · by_cases hk : k ∈ box n N
          · simp only [hk, if_true]; exact mul_nonneg (by linarith) le_rfl
          · simp only [hk, if_false]
            exact mul_nonneg (by linarith) (inv_nonneg.mpr (pow_nonneg (wt_pos k).le M))
        · by_cases hk : k ∈ box n N
          · simp only [hk, if_true]
            exact mul_le_mul_of_nonneg_left (inv_nonneg.mpr (pow_nonneg (wt_pos k).le M))
              (by linarith)
          · simp only [hk, if_false]; exact le_refl _
    rw [hdecomp, hfst]
    exact add_le_add le_rfl hsnd
  calc ‖seriesFun (γ m t) x - seriesFun (γlim t) x‖
      ≤ ∑' k : Fin n → ℤ, ‖γ m t k - γlim t k‖ := hmain
    _ ≤ (∑ k ∈ box n N, ‖γ m t k - γlim t k‖)
        + 2 * C * (∑' k : Fin n → ℤ, (if k ∈ box n N then (0 : ℝ) else ((wt k) ^ M)⁻¹)) := hsplit
    _ ≤ ε / 2 + ε / 2 := add_le_add (hM₀ m hm t) hN
    _ = ε := by ring

/-! ## Lipschitz continuity of the nonlinearity on the admissible set

A local copy (primed) of `Work.Diff.STE.flat.phi_lipschitz_admissible`, so that this module does
not depend on the (in-flux) file proving it there. -/

/-- Entrywise linearity of `reMat` along an affine combination of matrices. -/
private lemma reMat_add_smul_apply' {n : ℕ} (A B : MatC n) (a b : ℝ) (i j : Fin n) :
    reMat (a • A + b • B) i j = a * reMat A i j + b * reMat B i j := by
  simp only [reMat_apply, Pi.add_apply, Pi.smul_apply, Complex.add_re, Complex.smul_re]
  ring

/-- The norm of a finite family is at most the sum of the norms of its members. -/
private lemma norm_pi_le_sum_norm' {ι : Type*} {G : ι → Type*} [Fintype ι]
    [∀ i, SeminormedAddGroup (G i)] (f : ∀ i, G i) : ‖f‖ ≤ ∑ i, ‖f i‖ := by
  rw [Pi.norm_def]
  simp only [← coe_nnnorm]
  rw [← NNReal.coe_sum, NNReal.coe_le_coe]
  exact Finset.sup_le (fun b _ =>
    Finset.single_le_sum (f := fun i => ‖f i‖₊) (fun i _ => zero_le) (Finset.mem_univ b))

private lemma norm_sub_pi_le_sum' {ι : Type*} {E : ι → Type*} [Fintype ι]
    [∀ i, SeminormedAddGroup (E i)] (f g : ∀ i, E i) :
    ‖f - g‖ ≤ ∑ i, ‖f i - g i‖ := by
  simpa only [Pi.sub_apply] using norm_pi_le_sum_norm' (f - g)

private lemma norm_sub_matC_le' {n : ℕ} (A B : MatC n) :
    ‖A - B‖ ≤ ∑ i, ∑ j, ‖A i j - B i j‖ := by
  refine le_trans (norm_sub_pi_le_sum' A B) ?_
  exact Finset.sum_le_sum (fun i _ => norm_sub_pi_le_sum' (A i) (B i))

private lemma norm_sub_B_le' {n : ℕ} (B B' : Fin n → Fin n → MatC n) :
    ‖B' - B‖ ≤ ∑ i, ∑ j, ‖B' i j - B i j‖ := by
  refine le_trans (norm_sub_pi_le_sum' B' B) ?_
  exact Finset.sum_le_sum (fun i _ => norm_sub_pi_le_sum' (B' i) (B i))

/-- Bilinearity of the quadratic form `∑ᵢ ∑ⱼ Mᵢⱼ vᵢ vⱼ` in the matrix. -/
private lemma sum_sum_add_mul' {n : ℕ} (P Q : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (a b : ℝ) :
    (∑ i, ∑ j, (a * P i j + b * Q i j) * v i * v j)
      = a * (∑ i, ∑ j, P i j * v i * v j) + b * (∑ i, ∑ j, Q i j * v i * v j) := by
  have h1 : ∀ i, (∑ j, (a * P i j + b * Q i j) * v i * v j)
      = a * (∑ j, P i j * v i * v j) + b * (∑ j, Q i j * v i * v j) := by
    intro i
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  calc (∑ i, ∑ j, (a * P i j + b * Q i j) * v i * v j)
      = ∑ i, (a * (∑ j, P i j * v i * v j) + b * (∑ j, Q i j * v i * v j)) :=
        Finset.sum_congr rfl (fun i _ => h1 i)
    _ = (∑ i, a * (∑ j, P i j * v i * v j)) + (∑ i, b * (∑ j, Q i j * v i * v j)) :=
        Finset.sum_add_distrib
    _ = a * (∑ i, ∑ j, P i j * v i * v j) + b * (∑ i, ∑ j, Q i j * v i * v j) := by
        rw [Finset.mul_sum, Finset.mul_sum]

set_option maxHeartbeats 1000000 in
private theorem phi_lipschitz_admissible' {n : ℕ}
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (lam : ℝ) (hlam : 0 < lam) (KA : ℝ) (hKA : 0 ≤ KA) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (x : Fin n → ℝ)
      (hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1))
      (A A' : Work.Diff.STE.Flat.MatC n) (M M' : Fin n → Work.Diff.STE.Flat.MatC n)
      (B B' : Fin n → Fin n → Work.Diff.STE.Flat.MatC n),
      (∀ i j : Fin n, Work.Diff.STE.Flat.reMat A i j = Work.Diff.STE.Flat.reMat A j i) →
      (∀ v : Fin n → ℝ, lam * Finset.sum Finset.univ (fun i : Fin n => (v i)^2) ≤
        Finset.sum Finset.univ (fun i : Fin n => Finset.sum Finset.univ (fun j : Fin n =>
          Work.Diff.STE.Flat.reMat A i j * v i * v j))) →
      (∀ i j : Fin n, ‖A i j‖ ≤ KA) → (∀ i a b : Fin n, ‖M i a b‖ ≤ KA) →
      (∀ i j a b : Fin n, ‖B i j a b‖ ≤ KA) →
      (∀ i j : Fin n, Work.Diff.STE.Flat.reMat A' i j = Work.Diff.STE.Flat.reMat A' j i) →
      (∀ v : Fin n → ℝ, lam * Finset.sum Finset.univ (fun i : Fin n => (v i)^2) ≤
        Finset.sum Finset.univ (fun i : Fin n => Finset.sum Finset.univ (fun j : Fin n =>
          Work.Diff.STE.Flat.reMat A' i j * v i * v j))) →
      (∀ i j : Fin n, ‖A' i j‖ ≤ KA) → (∀ i a b : Fin n, ‖M' i a b‖ ≤ KA) →
      (∀ i j a b : Fin n, ‖B' i j a b‖ ≤ KA) →
      ‖Φ (x, (A',M',B')) - Φ (x, (A,M,B))‖ ≤
        L * (Finset.sum Finset.univ (fun i : Fin n => Finset.sum Finset.univ (fun j : Fin n =>
              ‖A' i j - A i j‖)) +
             Finset.sum Finset.univ (fun i : Fin n => ‖M' i - M i‖) +
             Finset.sum Finset.univ (fun i : Fin n => Finset.sum Finset.univ (fun j : Fin n =>
              ‖B' i j - B i j‖))) := by
  classical
  obtain ⟨hΦ, -⟩ := hshape
  set cube : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1) with hcube
  set SA : Set (MatC n) :=
    Set.univ.pi (fun _ : Fin n =>
      Set.univ.pi (fun _ : Fin n => Metric.closedBall (0 : ℂ) (max KA 0))) with hSA
  set KB : ℝ := ((Fintype.card (Fin n) : ℝ) * (Fintype.card (Fin n) : ℝ) + 1) * max KA 0
    with hKBdef
  have hKB0 : 0 ≤ KB := by
    rw [hKBdef]
    exact mul_nonneg (by positivity) (le_max_right _ _)
  set SM : Set (Fin n → MatC n) :=
    Set.univ.pi (fun _ : Fin n => Metric.closedBall (0 : MatC n) KB) with hSM
  set SB : Set (Fin n → Fin n → MatC n) :=
    Set.univ.pi (fun _ : Fin n =>
      Set.univ.pi (fun _ : Fin n => Metric.closedBall (0 : MatC n) KB)) with hSB
  -- entrywise bounds give the matrix-norm bounds used in the definition of `SM` and `SB`
  have hBmat : ∀ (D : MatC n), (∀ a b : Fin n, ‖D a b‖ ≤ KA) → ‖D‖ ≤ KB := by
    intro D hD
    refine (norm_matC_le_sum D).trans ?_
    have h1 : ∑ a : Fin n, ∑ b : Fin n, ‖D a b‖ ≤ ∑ a : Fin n, ∑ b : Fin n, max KA 0 :=
      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
        (hD a b).trans (le_max_left KA 0)
    have h2 : ∑ _a : Fin n, ∑ _b : Fin n, max KA 0
        = ((Fintype.card (Fin n) : ℝ)) * ((Fintype.card (Fin n) : ℝ)) * max KA 0 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hKBdef]
    nlinarith [h1, h2, le_max_right KA 0]
  set T : Set ((Fin n → ℝ) × Jet n) := cube ×ˢ (SA ×ˢ (SM ×ˢ SB)) with hT
  set Csym : Set ((Fin n → ℝ) × Jet n) :=
    ⋂ (i : Fin n), ⋂ (j : Fin n), {p | reMat (p.2.1) i j = reMat (p.2.1) j i} with hCsym
  set Cpos : Set ((Fin n → ℝ) × Jet n) :=
    ⋂ (v : Fin n → ℝ), {p | lam * ∑ i, (v i)^2
      ≤ ∑ i, ∑ j, reMat (p.2.1) i j * v i * v j} with hCpos
  set S : Set ((Fin n → ℝ) × Jet n) := T ∩ Csym ∩ Cpos with hS
  have hTcomp : IsCompact T := by
    rw [hT, hcube, hSA, hSM, hSB]
    refine IsCompact.prod (isCompact_univ_pi fun _ => isCompact_Icc) ?_
    refine IsCompact.prod (isCompact_univ_pi fun _ =>
      isCompact_univ_pi fun _ => isCompact_closedBall _ _) ?_
    refine IsCompact.prod (isCompact_univ_pi fun _ => isCompact_closedBall _ _) ?_
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hsymC : IsClosed Csym := by
    rw [hCsym]
    refine isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq ?_ ?_ <;> fun_prop
  have hposC : IsClosed Cpos := by
    rw [hCpos]
    refine isClosed_iInter fun _ => isClosed_le continuous_const ?_
    fun_prop
  have hScomp : IsCompact S := by
    rw [hS]
    exact (hTcomp.inter_right hsymC).inter_right hposC
  have hTconv : Convex ℝ T := by
    rw [hT]
    refine Convex.prod ?_ (Convex.prod ?_ (Convex.prod ?_ ?_))
    · rw [hcube]; exact convex_pi (fun _ _ => convex_Icc (0:ℝ) 1)
    · rw [hSA]
      exact convex_pi (fun _ _ => convex_pi (fun _ _ => convex_closedBall (0:ℂ) (max KA 0)))
    · rw [hSM]; exact convex_pi (fun _ _ => convex_closedBall (0 : MatC n) KB)
    · rw [hSB]
      exact convex_pi (fun _ _ => convex_pi (fun _ _ => convex_closedBall (0 : MatC n) KB))
  have hCsymv : Convex ℝ Csym := by
    rw [hCsym]
    refine convex_iInter (fun i => convex_iInter (fun j => ?_))
    intro p hp q hq a b ha hb hab
    simp only [Set.mem_ofPred_eq]
    rw [show (a • p + b • q).2.1 = a • p.2.1 + b • q.2.1 from rfl,
      reMat_add_smul_apply', reMat_add_smul_apply', hp, hq]
  have hCposv : Convex ℝ Cpos := by
    rw [hCpos]
    refine convex_iInter (fun v => ?_)
    intro p hp q hq a b ha hb hab
    simp only [Set.mem_ofPred_eq]
    rw [show (a • p + b • q).2.1 = a • p.2.1 + b • q.2.1 from rfl]
    have hkey : (∑ i, ∑ j, reMat (a • p.2.1 + b • q.2.1) i j * v i * v j)
        = a * (∑ i, ∑ j, reMat p.2.1 i j * v i * v j)
          + b * (∑ i, ∑ j, reMat q.2.1 i j * v i * v j) := by
      have h1 : ∀ i j : Fin n, reMat (a • p.2.1 + b • q.2.1) i j
          = a * reMat p.2.1 i j + b * reMat q.2.1 i j :=
        fun i j => reMat_add_smul_apply' p.2.1 q.2.1 a b i j
      rw [show (∑ i, ∑ j, reMat (a • p.2.1 + b • q.2.1) i j * v i * v j)
            = (∑ i, ∑ j, (a * reMat p.2.1 i j + b * reMat q.2.1 i j) * v i * v j) from
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [h1]))]
      exact sum_sum_add_mul' _ _ v a b
    rw [hkey]
    have hp' := mul_le_mul_of_nonneg_left hp ha
    have hq' := mul_le_mul_of_nonneg_left hq hb
    have hstep : a * (lam * ∑ i, (v i)^2) + b * (lam * ∑ i, (v i)^2) = lam * ∑ i, (v i)^2 := by
      have h : a * (lam * ∑ i, (v i)^2) + b * (lam * ∑ i, (v i)^2)
          = (a + b) * (lam * ∑ i, (v i)^2) := by ring
      rw [h, hab, one_mul]
    linarith [hp', hq', hstep]
  have hSconv : Convex ℝ S := by
    rw [hS]
    exact (hTconv.inter hCsymv).inter hCposv
  have hSsub : S ⊆ Set.univ ×ˢ
      {w : Jet n | (reMat w.1).det ≠ 0} := by
    intro p hp
    rw [hS] at hp
    obtain ⟨⟨_, hsymp⟩, hposp⟩ := hp
    rw [hCsym] at hsymp
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hsymp
    rw [hCpos] at hposp
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hposp
    exact ⟨trivial, reMat_det_ne_zero_of_elliptic p.2.1 hlam hsymp hposp⟩
  obtain ⟨K, hK⟩ := (hΦ.mono hSsub).exists_lipschitzOnWith (by simp) hSconv hScomp
  refine ⟨(K : ℝ), ?_, ?_⟩
  · exact_mod_cast K.2
  intro x hx A A' M M' B B' hsymA hellA hA hM hB hsymA' hellA' hA' hM' hB'
  -- the middle jet blocks are bounded by the entry bounds
  have hMnorm : ∀ i, ‖M i‖ ≤ KB := fun i => hBmat (M i) (fun a b => hM i a b)
  have hMnorm' : ∀ i, ‖M' i‖ ≤ KB := fun i => hBmat (M' i) (fun a b => hM' i a b)
  have hBnorm : ∀ i j, ‖B i j‖ ≤ KB := fun i j => hBmat (B i j) (fun a b => hB i j a b)
  have hBnorm' : ∀ i j, ‖B' i j‖ ≤ KB := fun i j => hBmat (B' i j) (fun a b => hB' i j a b)
  have hmemA : (x, (A, M, B)) ∈ S := by
    rw [hS]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hT]
      refine ⟨hx, ?_, ?_, ?_⟩
      · rw [hSA]
        intro i _ j _
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        exact le_trans (hA i j) (le_max_left _ _)
      · rw [hSM]
        intro i _
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hBmat (M i) (fun a b => hM i a b)
      · rw [hSB]
        intro i _ j _
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hBmat (B i j) (fun a b => hB i j a b)
    · rw [hCsym]
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      exact hsymA
    · rw [hCpos]
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      exact hellA
  have hmemA' : (x, (A', M', B')) ∈ S := by
    rw [hS]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hT]
      refine ⟨hx, ?_, ?_, ?_⟩
      · rw [hSA]
        intro i _ j _
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        exact le_trans (hA' i j) (le_max_left _ _)
      · rw [hSM]
        intro i _
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hBmat (M' i) (fun a b => hM' i a b)
      · rw [hSB]
        intro i _ j _
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hBmat (B' i j) (fun a b => hB' i j a b)
    · rw [hCsym]
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      exact hsymA'
    · rw [hCpos]
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      exact hellA'
  have hle := hK.dist_le_mul _ hmemA' _ hmemA
  set SUM : ℝ := (∑ i, ∑ j, ‖A' i j - A i j‖) + (∑ i, ‖M' i - M i‖)
      + (∑ i, ∑ j, ‖B' i j - B i j‖) with hSUMdef
  have hA0 : (0 : ℝ) ≤ ∑ i, ∑ j, ‖A' i j - A i j‖ :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg (A' i j - A i j)))
  have hM0 : (0 : ℝ) ≤ ∑ i, ‖M' i - M i‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg (M' i - M i))
  have hB0 : (0 : ℝ) ≤ ∑ i, ∑ j, ‖B' i j - B i j‖ :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg (B' i j - B i j)))
  have hSUM : (0 : ℝ) ≤ SUM := by
    rw [hSUMdef]; linarith
  have hA1 : ‖A' - A‖ ≤ ∑ i, ∑ j, ‖A' i j - A i j‖ := norm_sub_matC_le' A' A
  have hM1 : ‖M' - M‖ ≤ ∑ i, ‖M' i - M i‖ := norm_sub_pi_le_sum' M' M
  have hB1 : ‖B' - B‖ ≤ ∑ i, ∑ j, ‖B' i j - B i j‖ := norm_sub_B_le' B B'
  have hd2 : dist (A', (M', B')) (A, (M, B)) ≤ SUM := by
    rw [Prod.dist_eq, Prod.dist_eq, dist_eq_norm, dist_eq_norm, dist_eq_norm, hSUMdef]
    refine max_le ?_ (max_le ?_ ?_) <;> linarith [hA1, hM1, hB1]
  have hd : dist (x, (A', M', B')) (x, (A, M, B)) ≤ SUM := by
    rw [Prod.dist_eq, dist_self]
    exact max_le (by linarith) hd2
  calc ‖Φ (x, (A', M', B')) - Φ (x, (A, M, B))‖
      = dist (Φ (x, (A', M', B'))) (Φ (x, (A, M, B))) := by rw [dist_eq_norm]
    _ ≤ (K : ℝ) * dist (x, (A', M', B')) (x, (A, M, B)) := hle
    _ ≤ (K : ℝ) * SUM := mul_le_mul_of_nonneg_left hd K.coe_nonneg

theorem exists_limit_coeff {n : ℕ}
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (τ : ℝ) (hτ : 0 < τ) (lam : ℝ) (hlam : 0 < lam)
    (Blim : ℕ → ℝ) (hBlim : ∀ j : ℕ, 0 ≤ Blim j)
    (u₀ : Work.Diff.STE.Flat.Torus n)
    (Nb : ℕ → ℕ) (hNb : Filter.Tendsto Nb Filter.atTop Filter.atTop)
    (c : ℕ → ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hsol : ∀ m, ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k' ∈ Work.Diff.STE.Flat.box n (Nb m),
      ∀ (i j : Fin n),
      HasDerivAt (fun s => c m s k' i j)
        (Work.Diff.STE.fourierCoeff (fun x =>
          Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c m t)) x) i j) k') t)
    (hell : ∀ m, ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
      lam * Finset.sum Finset.univ (fun i : Fin n => (v i) ^ 2) ≤
        Finset.sum Finset.univ (fun i : Fin n => Finset.sum Finset.univ (fun j : Fin n =>
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c m t) x) i j * v i * v j)))
    (hsym : ∀ m, ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ (x : Fin n → ℝ) (i j : Fin n),
      Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c m t) x) i j
        = Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c m t) x) j i)
    (hsupp : ∀ (m : ℕ) (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n (Nb m) →
      c m t k' = 0)
    (hbdd : ∀ m, ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ j : ℕ,
      Work.Diff.STE.Flat.ENormSqFull j (Work.Diff.STE.Flat.seriesFunM (c m t)) ≤ Blim j)
    (hinit : ∀ x : Fin n → ℝ,
      Filter.Tendsto (fun m => Work.Diff.STE.Flat.seriesFunM (c m 0) x) Filter.atTop
        (nhds (u₀ x))) :
    ∃ cinf : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n,
      (∀ x : Fin n → ℝ, Work.Diff.STE.Flat.seriesFunM (cinf 0) x = u₀ x) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) τ, Work.Diff.STE.Periodic1 (Work.Diff.STE.Flat.seriesFunM (cinf t))) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ x : Fin n → ℝ,
        Work.Diff.STE.Flat.PosDefM (Work.Diff.STE.Flat.seriesFunM (cinf t) x)) ∧
      (∀ (M : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ (k : Fin n → ℤ) (i j : Fin n),
        ‖cinf t k i j‖ * (Work.Diff.STE.wt k) ^ M ≤ C * (1 + Blim (2 * M))) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ (k : Fin n → ℤ) (i j : Fin n),
        HasDerivWithinAt (fun s : ℝ => cinf s k i j)
          (Work.Diff.STE.fourierCoeff (fun x : Fin n → ℝ =>
            Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (cinf t)) x) i j) k)
          (Set.Ico (0 : ℝ) τ) t) := by
  classical
  -- (0) uniform bounds for the approximations
  obtain ⟨K, hK0, hK⟩ := galerkin_uniform_bound Φ hshape τ hτ lam hlam Blim hBlim Nb c
    hsol hell hsym hsupp hbdd
  -- (1) the extracted subsequence and the limit coefficients
  obtain ⟨φ, hφmono, g, hg⟩ := exists_subseq_uniform (ι := (Fin n → ℤ) × Fin n × Fin n) hτ
    (fun _ => K) (fun _ => hK0) (fun m p t => c m t p.1 p.2.1 p.2.2)
    (fun p m t ht => ((hK m t ht t ht) p.1 p.2.1 p.2.2).1)
    (fun p m t ht t' ht' => ((hK m t ht t' ht') p.1 p.2.1 p.2.2).2.1)
  let cinf : ℝ → (Fin n → ℤ) → MatC n := fun t k i j => g (k, i, j) t
  have hconvv : ∀ (k : Fin n → ℤ) (i j : Fin n),
      ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ m ≥ M₀, ∀ t ∈ Set.Ico (0 : ℝ) τ,
        ‖c (φ m) t k i j - cinf t k i j‖ ≤ ε := by
    intro k i j ε hε
    have h := (Metric.tendstoUniformlyOn_iff.mp (hg (k, i, j))) ε hε
    rw [Filter.eventually_atTop] at h
    obtain ⟨M₀, hM₀⟩ := h
    refine ⟨M₀, fun m hm t ht => ?_⟩
    have h1 := hM₀ m hm t ht
    rw [dist_eq_norm, norm_sub_rev] at h1
    simpa only [cinf] using le_of_lt h1
  have hconvT : ∀ (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ → ∀ (k : Fin n → ℤ) (i j : Fin n),
      Tendsto (fun m => c (φ m) t k i j) atTop (nhds (cinf t k i j)) := by
    intro t ht k i j
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M₀, hM₀⟩ := hconvv k i j (ε / 2) (by linarith)
    exact ⟨M₀, fun m hm => by
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (hM₀ m hm t ht) (by linarith)⟩
  -- (2) the decay bound for the limit family
  have hdec : ∀ (M : ℕ) (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ → ∀ (k : Fin n → ℤ) (i j : Fin n),
      ‖cinf t k i j‖ * (wt k) ^ M ≤ (1 + 2 * csqC n (2 * M)) * (1 + Blim (2 * M)) := by
    intro M t ht k i j
    refine le_of_tendsto ((hconvT t ht k i j).norm.mul_const ((wt k) ^ M))
      (Eventually.of_forall (fun m => ?_))
    exact coeff_decay_of_energy (c (φ m) t) (hsupp (φ m) t) hBlim
      (fun j => hbdd (φ m) t ht j) M k i j
  -- (3) moment summability of the limit family
  have hmom_lim : ∀ (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ → ∀ (i j : Fin n) (N : ℕ),
      Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖cinf t k i j‖) := by
    intro t ht i j N
    refine summable_l1_of_decay N (Mdec := N + n + 1) (by omega)
      (Cdec := (1 + 2 * csqC n (2 * (N + n + 1))) * (1 + Blim (2 * (N + n + 1))))
      (fun k => hdec (N + n + 1) t ht k i j)
  -- (4) weighted `ℓ²` summability and bounds for the approximations
  have hsumseq : ∀ (m : ℕ) (t : ℝ) (s : ℕ) (i j : Fin n),
      Summable (fun k : Fin n → ℤ => (wt k) ^ s * ‖c (φ m) t k i j‖ ^ 2) := fun m t s i j =>
    Work.Diff.STE.summable_wt_pow_mul_norm_sq (fun k => c (φ m) t k i j)
      (fun N => summable_moment_box (c (φ m) t) (hsupp (φ m) t) i j N) s
  have hbdseq : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ → ∀ (s : ℕ) (i j : Fin n),
      (∑' k : Fin n → ℤ, (wt k) ^ s * ‖c (φ m) t k i j‖ ^ 2)
        ≤ 2 * csqC n s * Blim s := by
    intro m t ht s i j
    exact (CSq_entry_le_energy (N := Nb (φ m)) (c (φ m) t) (hsupp (φ m) t) i j (s := s)).trans
      (mul_le_mul_of_nonneg_left (hbdd (φ m) t ht s)
        (mul_nonneg (by norm_num) (csqC_nonneg n s)))
  have hsumlim : ∀ (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ → ∀ (s : ℕ) (i j : Fin n),
      Summable (fun k : Fin n → ℤ => (wt k) ^ s * ‖cinf t k i j‖ ^ 2) := by
    intro t ht s i j
    refine summable_weighted_of_decay s (Mdec := s + n + 1) (by omega)
      (Cdec := (1 + 2 * csqC n (2 * (s + n + 1))) * (1 + Blim (2 * (s + n + 1))))
      (fun k => hdec (s + n + 1) t ht k i j)
  have hbdlim : ∀ (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ → ∀ (s : ℕ) (i j : Fin n),
      (∑' k : Fin n → ℤ, (wt k) ^ s * ‖cinf t k i j‖ ^ 2) ≤ 2 * csqC n s * Blim s := by
    intro t ht s i j
    exact weighted_limit_le (A := 2 * csqC n s * Blim s)
      (fun m => ⟨hsumseq m t s i j, hbdseq m t ht s i j⟩)
      (fun k => hconvT t ht k i j) (hsumlim t ht s i j)
  -- (5) uniform convergence of the spatial jets along the subsequence
  have hjet : ∀ (j : ℕ) (hj : j ≤ 2) (l : Fin j → Fin n) (a b : Fin n),
      ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ m ≥ M₀, ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ x : Fin n → ℝ,
        ‖pdVec j l (fun y => seriesFunM (c (φ m) t) y a b) x
          - pdVec j l (fun y => seriesFunM (cinf t) y a b) x‖ ≤ ε := by
    intro j hj l a b ε hε
    set Cdec : ℝ := (1 + 2 * csqC n (2 * (n + 3))) * (1 + Blim (2 * (n + 3))) with hCdecdef
    have hCdec0 : 0 ≤ Cdec := by
      rw [hCdecdef]
      exact mul_nonneg (by linarith [csqC_nonneg n (2 * (n + 3))])
        (by linarith [hBlim (2 * (n + 3))])
    have hdec1 : ∀ (m : ℕ) (t : {t : ℝ // t ∈ Set.Ico (0 : ℝ) τ}) (k : Fin n → ℤ),
        ‖dmulV (List.ofFn l) (fun k' => c (φ m) t.1 k' a b) k‖ * (wt k) ^ (n + 1)
          ≤ (2 * Real.pi) ^ 2 * Cdec := by
      intro m t k
      refine dmulV_decay (List.ofFn l) (by rw [List.length_ofFn]; omega) ?_ k
      intro k'
      rw [hCdecdef]
      exact coeff_decay_of_energy (c (φ m) t.1) (hsupp (φ m) t.1) hBlim
        (fun j' => hbdd (φ m) t.1 t.2 j') (n + 3) k' a b
    have hdec2 : ∀ (t : {t : ℝ // t ∈ Set.Ico (0 : ℝ) τ}) (k : Fin n → ℤ),
        ‖dmulV (List.ofFn l) (fun k' => cinf t.1 k' a b) k‖ * (wt k) ^ (n + 1)
          ≤ (2 * Real.pi) ^ 2 * Cdec := by
      intro t k
      refine dmulV_decay (List.ofFn l) (by rw [List.length_ofFn]; omega) ?_ k
      intro k'
      rw [hCdecdef]
      exact hdec (n + 3) t.1 t.2 k' a b
    have hclim' : ∀ k : Fin n → ℤ, ∀ ε' : ℝ, 0 < ε' → ∃ M₁ : ℕ,
        ∀ m ≥ M₁, ∀ t : {t : ℝ // t ∈ Set.Ico (0 : ℝ) τ},
        ‖dmulV (List.ofFn l) (fun k' => c (φ m) t.1 k' a b) k
          - dmulV (List.ofFn l) (fun k' => cinf t.1 k' a b) k‖ ≤ ε' := by
      intro k ε' hε'
      set c₀ : ℂ := ((List.ofFn l).map (fun i => 2 * Real.pi * Complex.I * ((k i : ℂ)))).prod
        with hc₀def
      have hk : (0 : ℝ) < ‖c₀‖ + 1 := by positivity
      obtain ⟨M₁, hM₁⟩ := hconvv k a b (ε' / (‖c₀‖ + 1)) (by positivity)
      refine ⟨M₁, fun m hm t => ?_⟩
      have h1 := hM₁ m hm t.1 t.2
      have h2 : dmulV (List.ofFn l) (fun k' => c (φ m) t.1 k' a b) k
          - dmulV (List.ofFn l) (fun k' => cinf t.1 k' a b) k
          = c₀ * (c (φ m) t.1 k a b - cinf t.1 k a b) := by
        rw [Work.Diff.STE.dmulV, Work.Diff.STE.dmulV, hc₀def]
        ring
      rw [h2, norm_mul]
      calc ‖c₀‖ * ‖c (φ m) t.1 k a b - cinf t.1 k a b‖ ≤ ‖c₀‖ * (ε' / (‖c₀‖ + 1)) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ ≤ ε' := by
            rw [mul_div_assoc', div_le_iff₀ hk]
            nlinarith [norm_nonneg c₀, hε'.le]
    obtain ⟨M₀, hM₀⟩ := series_uniform_of_coeff_uniform
      (T := {t : ℝ // t ∈ Set.Ico (0 : ℝ) τ})
      (γ := fun m (t : {t : ℝ // t ∈ Set.Ico (0 : ℝ) τ}) k =>
        dmulV (List.ofFn l) (fun k' => c (φ m) t.1 k' a b) k)
      (γlim := fun (t : {t : ℝ // t ∈ Set.Ico (0 : ℝ) τ}) k =>
        dmulV (List.ofFn l) (fun k' => cinf t.1 k' a b) k)
      (M := n + 1) (by omega)
      (C := (2 * Real.pi) ^ 2 * Cdec) (mul_nonneg (by positivity) hCdec0) hdec1 hdec2 hclim' ε hε
    refine ⟨M₀, fun m hm t ht x => ?_⟩
    have h1 := hM₀ m hm ⟨t, ht⟩ x
    have hb1 : pdVec j l (fun y => seriesFunM (c (φ m) t) y a b) x
        = seriesFun (fun k => dmulV (List.ofFn l) (fun k' => c (φ m) t k' a b) k) x := by
      have h := pdList_seriesFun (List.ofFn l) (fun k => c (φ m) t k a b)
        (fun N => summable_moment_box (c (φ m) t) (hsupp (φ m) t) a b N) x
      simp only [Work.Diff.STE.pdVec, seriesFunM_apply]
      exact h
    have hb2 : pdVec j l (fun y => seriesFunM (cinf t) y a b) x
        = seriesFun (fun k => dmulV (List.ofFn l) (fun k' => cinf t k' a b) k) x := by
      have h := pdList_seriesFun (List.ofFn l) (fun k => cinf t k a b)
        (fun N => hmom_lim t ht a b N) x
      simp only [Work.Diff.STE.pdVec, seriesFunM_apply]
      exact h
    rw [hb1, hb2]
    exact h1
  -- (6) entrywise convergence of the series
  have hseries : ∀ (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ → ∀ (x : Fin n → ℝ) (a b : Fin n),
      Tendsto (fun m => seriesFunM (c (φ m) t) x a b) atTop (nhds (seriesFunM (cinf t) x a b)) := by
    intro t ht x a b
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M₀, hM₀⟩ := hjet 0 (by omega) (fun i : Fin 0 => Fin.elim0 i) a b (ε / 2) (by linarith)
    exact ⟨M₀, fun m hm => by
      rw [dist_eq_norm]
      have h1 := hM₀ m hm t ht x
      simp only [pdVec, List.ofFn_eq_map, List.length_nil, List.ofFn_zero, List.foldr_nil,
        List.map_nil] at h1
      exact lt_of_le_of_lt h1 (by linarith)⟩
  have hseries' : ∀ (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ → ∀ (x : Fin n → ℝ),
      Tendsto (fun m => seriesFunM (c (φ m) t) x) atTop (nhds (seriesFunM (cinf t) x)) := by
    intro t ht x
    rw [tendsto_pi_nhds]
    exact fun a => tendsto_pi_nhds.mpr (fun b => hseries t ht x a b)
  -- (6b) ellipticity and symmetry of the limit matrix
  have hell_lim : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
      lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMat (seriesFunM (cinf t) x) i j * v i * v j := by
    intro t ht x v
    have hT : Tendsto (fun m => ∑ i, ∑ jj, reMat (seriesFunM (c (φ m) t) x) i jj * v i * v jj)
        atTop (nhds (∑ i, ∑ jj, reMat (seriesFunM (cinf t) x) i jj * v i * v jj)) := by
      refine tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun jj _ => ?_))
      have h1 : Tendsto (fun m => (seriesFunM (c (φ m) t) x i jj).re) atTop
          (nhds ((seriesFunM (cinf t) x i jj).re)) := by
        simpa only [Function.comp_def] using
          ((Complex.continuous_re.tendsto (seriesFunM (cinf t) x i jj)).comp
            (hseries t ht x i jj))
      have h2 : Tendsto (fun m => reMat (seriesFunM (c (φ m) t) x) i jj) atTop
          (nhds (reMat (seriesFunM (cinf t) x) i jj)) := by
        simpa only [reMat_apply] using h1
      exact (h2.mul_const (v i)).mul_const (v jj)
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hT
      (fun m => hell (φ m) t ht x v)
  have hsym_lim : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ (x : Fin n → ℝ) (i j : Fin n),
      reMat (seriesFunM (cinf t) x) i j = reMat (seriesFunM (cinf t) x) j i := by
    intro t ht x i j
    have h1 : Tendsto (fun m => reMat (seriesFunM (c (φ m) t) x) i j) atTop
        (nhds (reMat (seriesFunM (cinf t) x) i j)) := by
      simpa only [reMat_apply, Function.comp_def] using
        ((Complex.continuous_re.tendsto _).comp (hseries t ht x i j))
    have h2 : Tendsto (fun m => reMat (seriesFunM (c (φ m) t) x) j i) atTop
        (nhds (reMat (seriesFunM (cinf t) x) j i)) := by
      simpa only [reMat_apply, Function.comp_def] using
        ((Complex.continuous_re.tendsto _).comp (hseries t ht x j i))
    exact tendsto_nhds_unique h1
      (h2.congr' (Eventually.of_forall fun m => (hsym (φ m) t ht x i j).symm))
  -- (6c) pointwise (hence uniform) convergence of the spatial jets
  have hpd_conv : ∀ (j : ℕ) (hj : j ≤ 2) (l : Fin j → Fin n) (a b : Fin n) (t : ℝ),
      t ∈ Set.Ico (0 : ℝ) τ → ∀ x : Fin n → ℝ,
      Tendsto (fun m => pdVec j l (fun y => seriesFunM (c (φ m) t) y a b) x) atTop
        (nhds (pdVec j l (fun y => seriesFunM (cinf t) y a b) x)) := by
    intro j hj l a b t ht x
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M₀, hM₀⟩ := hjet j hj l a b (ε / 2) (by linarith)
    exact ⟨M₀, fun m hm => by
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (hM₀ m hm t ht x) (by linarith)⟩
  -- (7) the jet sup bounds and the Lipschitz constant of the nonlinearity
  obtain ⟨KA, hKA0, hKA⟩ := jet_sup_bound' (n := n) (k := n + 3)
    (by rw [Fintype.card_fin]; omega) (Real.sqrt (Blim (n + 3))) (Real.sqrt_nonneg _)
  have hKAseq : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ → ∀ x : Fin n → ℝ,
      (∀ i j, ‖seriesFunM (c (φ m) t) x i j‖ ≤ KA) ∧
      (∀ d i j, ‖pdM d (seriesFunM (c (φ m) t)) x i j‖ ≤ KA) ∧
      (∀ d e i j, ‖pdM d (pdM e (seriesFunM (c (φ m) t))) x i j‖ ≤ KA) := by
    intro m t ht x
    have h := hKA (Nb (φ m)) (c (φ m) t) (hsupp (φ m) t)
      (by rw [Real.sq_sqrt (hBlim (n + 3))]; exact hbdd (φ m) t ht (n + 3))
    exact ⟨fun i j => h.1 x i j, fun d i j => h.2.1 x d i j, fun d e i j => h.2.2 x d e i j⟩
  have hKA_lim : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ x : Fin n → ℝ,
      (∀ i j, ‖seriesFunM (cinf t) x i j‖ ≤ KA) ∧
      (∀ d i j, ‖pdM d (seriesFunM (cinf t)) x i j‖ ≤ KA) ∧
      (∀ d e i j, ‖pdM d (pdM e (seriesFunM (cinf t))) x i j‖ ≤ KA) := by
    intro t ht x
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      exact le_of_tendsto ((hseries t ht x i j).norm)
        (Eventually.of_forall fun m => (hKAseq m t ht x).1 i j)
    · intro d i j
      refine le_of_tendsto ((hpd_conv 1 (by omega) (fun _ : Fin 1 => d) i j t ht x).norm)
        (Eventually.of_forall fun m => ?_)
      simpa only [pdM_eq_pdVec_one'] using (hKAseq m t ht x).2.1 d i j
    · intro d e i j
      refine le_of_tendsto
        ((hpd_conv 2 (by omega) (Fin.cases d (fun _ : Fin 1 => e)) i j t ht x).norm)
        (Eventually.of_forall fun m => ?_)
      simpa only [pdM_pdM_eq_pdVec_two'] using (hKAseq m t ht x).2.2 d e i j
  obtain ⟨L, hL0, hL⟩ := phi_lipschitz_admissible' (n := n) Φ hshape lam hlam KA hKA0
  -- (8) uniform smallness of the jet difference sums along the subsequence
  have hS1 : ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ m ≥ M₀,
      ∀ q : {t : ℝ // t ∈ Set.Ico (0 : ℝ) τ} × (Fin n → ℝ),
      ∑ p : Fin n × Fin n, ‖seriesFunM (c (φ m) q.1.1) q.2 p.1 p.2
        - seriesFunM (cinf q.1.1) q.2 p.1 p.2‖ ≤ ε := by
    intro ε hε
    have h := uniform_sum_zero (ι := Fin n × Fin n)
      (T := {t : ℝ // t ∈ Set.Ico (0 : ℝ) τ} × (Fin n → ℝ))
      (f := fun m p q => ‖seriesFunM (c (φ m) q.1.1) q.2 p.1 p.2
        - seriesFunM (cinf q.1.1) q.2 p.1 p.2‖)
      (fun p ε' hε' => by
        obtain ⟨M₀, hM₀⟩ := hjet 0 (by omega) (fun i : Fin 0 => Fin.elim0 i) p.1 p.2 ε' hε'
        exact ⟨M₀, fun m hm q => by
          have h1 := hM₀ m hm q.1.1 q.1.2 q.2
          simpa only [pdVec_zero_eq, Real.norm_of_nonneg (norm_nonneg _)] using h1⟩)
    obtain ⟨M₀, hM₀⟩ := h ε hε
    exact ⟨M₀, fun m hm q => by
      have := hM₀ m hm q
      rwa [Real.norm_of_nonneg (Finset.sum_nonneg fun p _ => norm_nonneg _)] at this⟩
  have hS2 : ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ m ≥ M₀,
      ∀ q : {t : ℝ // t ∈ Set.Ico (0 : ℝ) τ} × (Fin n → ℝ),
      ∑ p : Fin n × (Fin n × Fin n), ‖pdM p.1 (seriesFunM (c (φ m) q.1.1)) q.2 p.2.1 p.2.2
        - pdM p.1 (seriesFunM (cinf q.1.1)) q.2 p.2.1 p.2.2‖ ≤ ε := by
    intro ε hε
    have h := uniform_sum_zero (ι := Fin n × (Fin n × Fin n))
      (T := {t : ℝ // t ∈ Set.Ico (0 : ℝ) τ} × (Fin n → ℝ))
      (f := fun m p q => ‖pdM p.1 (seriesFunM (c (φ m) q.1.1)) q.2 p.2.1 p.2.2
        - pdM p.1 (seriesFunM (cinf q.1.1)) q.2 p.2.1 p.2.2‖)
      (fun p ε' hε' => by
        obtain ⟨M₀, hM₀⟩ := hjet 1 (by omega) (fun _ : Fin 1 => p.1) p.2.1 p.2.2 ε' hε'
        exact ⟨M₀, fun m hm q => by
          have h1 := hM₀ m hm q.1.1 q.1.2 q.2
          rw [pdM_eq_pdVec_one', pdM_eq_pdVec_one']
          simpa only [Real.norm_of_nonneg (norm_nonneg _)] using h1⟩)
    obtain ⟨M₀, hM₀⟩ := h ε hε
    exact ⟨M₀, fun m hm q => by
      have := hM₀ m hm q
      rwa [Real.norm_of_nonneg (Finset.sum_nonneg fun p _ => norm_nonneg _)] at this⟩
  have hS3 : ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ m ≥ M₀,
      ∀ q : {t : ℝ // t ∈ Set.Ico (0 : ℝ) τ} × (Fin n → ℝ),
      ∑ p : (Fin n × Fin n) × (Fin n × Fin n),
        ‖pdM p.1.1 (pdM p.1.2 (seriesFunM (c (φ m) q.1.1))) q.2 p.2.1 p.2.2
          - pdM p.1.1 (pdM p.1.2 (seriesFunM (cinf q.1.1))) q.2 p.2.1 p.2.2‖ ≤ ε := by
    intro ε hε
    have h := uniform_sum_zero (ι := (Fin n × Fin n) × (Fin n × Fin n))
      (T := {t : ℝ // t ∈ Set.Ico (0 : ℝ) τ} × (Fin n → ℝ))
      (f := fun m p q => ‖pdM p.1.1 (pdM p.1.2 (seriesFunM (c (φ m) q.1.1))) q.2 p.2.1 p.2.2
        - pdM p.1.1 (pdM p.1.2 (seriesFunM (cinf q.1.1))) q.2 p.2.1 p.2.2‖)
      (fun p ε' hε' => by
        obtain ⟨M₀, hM₀⟩ := hjet 2 (by omega)
          (Fin.cases p.1.1 (fun _ : Fin 1 => p.1.2)) p.2.1 p.2.2 ε' hε'
        exact ⟨M₀, fun m hm q => by
          have h1 := hM₀ m hm q.1.1 q.1.2 q.2
          rw [pdM_pdM_eq_pdVec_two', pdM_pdM_eq_pdVec_two']
          simpa only [Real.norm_of_nonneg (norm_nonneg _)] using h1⟩)
    obtain ⟨M₀, hM₀⟩ := h ε hε
    exact ⟨M₀, fun m hm q => by
      have := hM₀ m hm q
      rwa [Real.norm_of_nonneg (Finset.sum_nonneg fun p _ => norm_nonneg _)] at this⟩
  -- (9) uniform convergence of the right-hand sides
  have hDconv : ∀ (k : Fin n → ℤ) (i j : Fin n),
      TendstoUniformlyOn
        (fun m => fun t : ℝ => fourierCoeff (fun x : Fin n → ℝ =>
          Φ (x, jetM (seriesFunM (c (φ m) t)) x) i j) k)
        (fun t : ℝ => fourierCoeff (fun x : Fin n → ℝ =>
          Φ (x, jetM (seriesFunM (cinf t)) x) i j) k)
        atTop (Set.Ico (0 : ℝ) τ) := by
    intro k i j
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hL1 : (0 : ℝ) < L + 1 := by linarith
    obtain ⟨M₀, hM₀⟩ := hS1 (ε / (3 * (L + 1))) (by positivity)
    obtain ⟨M₁, hM₁⟩ := hS2 (ε / (3 * (L + 1))) (by positivity)
    obtain ⟨M₂, hM₂⟩ := hS3 (ε / (3 * (L + 1))) (by positivity)
    refine Filter.eventually_atTop.mpr ⟨max (max M₀ M₁) M₂, fun m hm t ht => ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    have hSm : ∀ x : Fin n → ℝ,
        (∑ p : Fin n × Fin n, ‖seriesFunM (c (φ m) t) x p.1 p.2
          - seriesFunM (cinf t) x p.1 p.2‖)
        + (∑ p : Fin n × (Fin n × Fin n), ‖pdM p.1 (seriesFunM (c (φ m) t)) x p.2.1 p.2.2
          - pdM p.1 (seriesFunM (cinf t)) x p.2.1 p.2.2‖)
        + (∑ p : (Fin n × Fin n) × (Fin n × Fin n),
            ‖pdM p.1.1 (pdM p.1.2 (seriesFunM (c (φ m) t))) x p.2.1 p.2.2
              - pdM p.1.1 (pdM p.1.2 (seriesFunM (cinf t))) x p.2.1 p.2.2‖)
        ≤ 3 * (ε / (3 * (L + 1))) := by
      intro x
      have h1 := hM₀ m (le_trans (le_max_left M₀ M₁) (le_max_left (max M₀ M₁) M₂) |>.trans hm)
        (⟨t, ht⟩, x)
      have h2 := hM₁ m (le_trans (le_max_right M₀ M₁) (le_max_left (max M₀ M₁) M₂) |>.trans hm)
        (⟨t, ht⟩, x)
      have h3 := hM₂ m (le_trans (le_max_right (max M₀ M₁) M₂) hm) (⟨t, ht⟩, x)
      linarith
    have hbound : ‖fourierCoeff (fun x : Fin n → ℝ =>
          Φ (x, jetM (seriesFunM (c (φ m) t)) x) i j) k
        - fourierCoeff (fun x : Fin n → ℝ =>
          Φ (x, jetM (seriesFunM (cinf t)) x) i j) k‖ ≤ L * (3 * (ε / (3 * (L + 1)))) := by
      refine norm_fourierCoeff_sub_le ?hf ?hg (by positivity) ?hpt k
      · exact continuousOn_phi_jet Φ hshape lam hlam (c (φ m) t)
          (fun i' j' N => summable_moment_box (c (φ m) t) (hsupp (φ m) t) i' j' N)
          (fun x i' j' => hsym (φ m) t ht x i' j') (fun x v => hell (φ m) t ht x v) i j
      · exact continuousOn_phi_jet Φ hshape lam hlam (cinf t)
          (fun i' j' N => hmom_lim t ht i' j' N)
          (fun x i' j' => hsym_lim t ht x i' j') (fun x v => hell_lim t ht x v) i j
      · intro x hx
        have hcube : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) :=
          fun i' _ => ⟨le_of_lt (hx i' trivial).1, (hx i' trivial).2⟩
        have hJm := hKAseq m t ht x
        have hJl := hKA_lim t ht x
        have hΦ := hL x hcube
          (seriesFunM (c (φ m) t) x) (seriesFunM (cinf t) x)
          (fun d => pdM d (seriesFunM (c (φ m) t)) x)
          (fun d => pdM d (seriesFunM (cinf t)) x)
          (fun d e => pdM d (pdM e (seriesFunM (c (φ m) t))) x)
          (fun d e => pdM d (pdM e (seriesFunM (cinf t))) x)
          (fun i' j' => hsym (φ m) t ht x i' j') (fun v => hell (φ m) t ht x v)
          hJm.1 hJm.2.1 hJm.2.2
          (fun i' j' => hsym_lim t ht x i' j') (fun v => hell_lim t ht x v)
          hJl.1 hJl.2.1 hJl.2.2
        have hsplit : ‖Φ (x, jetM (seriesFunM (c (φ m) t)) x) i j
              - Φ (x, jetM (seriesFunM (cinf t)) x) i j‖
            ≤ ‖Φ (x, jetM (seriesFunM (c (φ m) t)) x)
              - Φ (x, jetM (seriesFunM (cinf t)) x)‖ := by
          simpa only [Pi.sub_apply] using
            (norm_le_pi_norm ((Φ (x, jetM (seriesFunM (c (φ m) t)) x)
              - Φ (x, jetM (seriesFunM (cinf t)) x)) i) j).trans
              (norm_le_pi_norm (Φ (x, jetM (seriesFunM (c (φ m) t)) x)
                - Φ (x, jetM (seriesFunM (cinf t)) x)) i)
        have hmid : (∑ i' : Fin n, ‖pdM i' (seriesFunM (cinf t)) x
              - pdM i' (seriesFunM (c (φ m) t)) x‖)
            ≤ ∑ p : Fin n × (Fin n × Fin n),
                ‖pdM p.1 (seriesFunM (c (φ m) t)) x p.2.1 p.2.2
                  - pdM p.1 (seriesFunM (cinf t)) x p.2.1 p.2.2‖ := by
          simp only [Fintype.sum_prod_type]
          refine Finset.sum_le_sum fun i' _ => ?_
          refine (norm_matC_le_sum _).trans ?_
          exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
            le_of_eq (by simp only [Pi.sub_apply, norm_sub_rev])
        have hlast : (∑ i' : Fin n, ∑ j' : Fin n,
              ‖pdM i' (pdM j' (seriesFunM (cinf t))) x - pdM i' (pdM j' (seriesFunM (c (φ m) t))) x‖)
            ≤ ∑ p : (Fin n × Fin n) × (Fin n × Fin n),
                ‖pdM p.1.1 (pdM p.1.2 (seriesFunM (c (φ m) t))) x p.2.1 p.2.2
                  - pdM p.1.1 (pdM p.1.2 (seriesFunM (cinf t))) x p.2.1 p.2.2‖ := by
          simp only [Fintype.sum_prod_type]
          refine Finset.sum_le_sum fun i' _ => Finset.sum_le_sum fun j' _ => ?_
          refine (norm_matC_le_sum _).trans ?_
          exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
            le_of_eq (by simp only [Pi.sub_apply, norm_sub_rev])
        have hfirst : (∑ i' : Fin n, ∑ j' : Fin n,
              ‖seriesFunM (cinf t) x i' j' - seriesFunM (c (φ m) t) x i' j'‖)
            = ∑ p : Fin n × Fin n, ‖seriesFunM (c (φ m) t) x p.1 p.2
                - seriesFunM (cinf t) x p.1 p.2‖ := by
          rw [Fintype.sum_prod_type]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
            rw [norm_sub_rev]
        have hSsum : (∑ i' : Fin n, ∑ j' : Fin n,
              ‖seriesFunM (cinf t) x i' j' - seriesFunM (c (φ m) t) x i' j'‖)
            + (∑ i' : Fin n, ‖pdM i' (seriesFunM (cinf t)) x
              - pdM i' (seriesFunM (c (φ m) t)) x‖)
            + (∑ i' : Fin n, ∑ j' : Fin n,
              ‖pdM i' (pdM j' (seriesFunM (cinf t))) x
                - pdM i' (pdM j' (seriesFunM (c (φ m) t))) x‖)
            ≤ 3 * (ε / (3 * (L + 1))) := by
          rw [hfirst]
          linarith [hmid, hlast, hSm x]
        have hsum3 : ‖Φ (x, jetM (seriesFunM (c (φ m) t)) x)
              - Φ (x, jetM (seriesFunM (cinf t)) x)‖
            ≤ L * (3 * (ε / (3 * (L + 1)))) := by
          simp only [jetM] at hΦ ⊢
          rw [norm_sub_rev]
          exact hΦ.trans (mul_le_mul_of_nonneg_left hSsum hL0)
        exact hsplit.trans hsum3
    calc ‖fourierCoeff (fun x : Fin n → ℝ =>
            Φ (x, jetM (seriesFunM (c (φ m) t)) x) i j) k
          - fourierCoeff (fun x : Fin n → ℝ =>
            Φ (x, jetM (seriesFunM (cinf t)) x) i j) k‖
        ≤ L * (3 * (ε / (3 * (L + 1)))) := hbound
      _ = L * ε / (L + 1) := by field_simp
      _ < ε := by
          rw [div_lt_iff₀ hL1]
          nlinarith
  refine ⟨cinf, ?_, ?_, ?_, ?_, ?_⟩
  · -- (i) initial datum
    intro x
    funext a b
    have h1 : Tendsto (fun m => seriesFunM (c (φ m) 0) x a b) atTop
        (nhds (u₀ x a b)) := by
      have hcont : Continuous (fun M : MatC n => M a b) := by fun_prop
      exact (hcont.tendsto (u₀ x)).comp ((hinit x).comp hφmono.tendsto_atTop)
    exact tendsto_nhds_unique (hseries 0 ⟨le_rfl, hτ⟩ x a b) h1
  · -- (ii) periodicity
    intro t ht i x
    have h1 : Tendsto (fun m => seriesFunM (c (φ m) t) (x + Pi.single i 1)) atTop
        (nhds (seriesFunM (cinf t) (x + Pi.single i 1))) := hseries' t ht _
    have h2 : Tendsto (fun m => seriesFunM (c (φ m) t) x) atTop (nhds (seriesFunM (cinf t) x)) :=
      hseries' t ht x
    have h3 : Tendsto (fun m => seriesFunM (c (φ m) t) (x + Pi.single i 1)) atTop
        (nhds (seriesFunM (cinf t) x)) :=
      h2.congr' (Eventually.of_forall fun m => by
        funext a b
        exact (periodic1_seriesFun (fun k : Fin n → ℤ => c (φ m) t k a b) i x).symm)
    exact tendsto_nhds_unique h1 h3
  · -- (iii) positive definiteness
    intro t ht x
    rw [PosDefM]
    have hHerm : (reMat (seriesFunM (cinf t) x)).IsHermitian := by
      rw [Matrix.isHermitian_iff_isSymm]
      exact Matrix.IsSymm.ext (fun i j => hsym_lim t ht x j i)
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨hHerm, fun v hv => ?_⟩
    have hsum : 0 < ∑ i : Fin n, (v i) ^ 2 := by
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv
      exact Finset.sum_pos' (fun j _ => sq_nonneg _)
        ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
    have hquad : star v ⬝ᵥ (reMat (seriesFunM (cinf t) x)).mulVec v
        = ∑ i, ∑ j, reMat (seriesFunM (cinf t) x) i j * v i * v j := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, star_trivial]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hquad]
    exact lt_of_lt_of_le (mul_pos hlam hsum) (hell_lim t ht x v)
  · -- (iv) coefficient decay
    intro M
    refine ⟨1 + 2 * csqC n (2 * M), by linarith [csqC_nonneg n (2 * M)], ?_⟩
    intro t ht k i j
    exact hdec M t ht k i j
  · -- (v) the limit solves the equation
    intro t ht k i j
    obtain ⟨M₀, hM₀⟩ := eventually_mem_box_comp hNb hφmono.tendsto_atTop k
    have hf : TendstoUniformlyOn (fun m => fun s : ℝ => c (φ m) s k i j)
        (fun s : ℝ => cinf s k i j) atTop (Set.Ico (0 : ℝ) τ) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨M₁, hM₁⟩ := hconvv k i j (ε / 2) (by linarith)
      refine Filter.eventually_atTop.mpr ⟨M₁, fun m hm s hs => ?_⟩
      rw [dist_eq_norm, norm_sub_rev]
      exact lt_of_le_of_lt (hM₁ m hm s hs) (by linarith)
    exact hasDerivWithinAt_of_tendstoUniformlyOn
      ⟨M₀, fun m hm s hs => hsol (φ m) s hs k (hM₀ m hm) i j⟩ hf (hDconv k i j) t ht

end

end Work.Diff.STE.flat
