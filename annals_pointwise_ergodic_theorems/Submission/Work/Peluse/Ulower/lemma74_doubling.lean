import Mathlib
import Submission.Work.Peluse.Ulower.iterDefs
import Submission.Work.Peluse.Ulower.Defs
import Submission.Work.Peluse.BoxNorm.genHolder
import Submission.Work.Peluse.Ulower.dualFn_tsum_le

set_option maxHeartbeats 3200000
open scoped BigOperators
open Polynomial

namespace Work.Peluse.Ulower

noncomputable section

/-- A finite sum of summable functions is summable. -/
private lemma Summable.finset_sum' {ι β : Type*} [AddCommMonoid β] [TopologicalSpace β] [ContinuousAdd β]
    {s : Finset ι} {f : ι → ℤ → β} (h : ∀ i ∈ s, Summable (f i)) :
    Summable (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (summable_zero : Summable (fun _ : ℤ => (0 : β)))
  | insert a s ha ih =>
      have h1 : Summable (f a) := h a (Finset.mem_insert_self a s)
      have h2 : Summable (fun x => ∑ i ∈ s, f i x) := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      simpa only [Finset.sum_insert ha] using h1.add h2

/-- Translation does not change summability. -/
private lemma summable_comp_add_right {g : ℤ → ℝ} (hg : Summable g) (c : ℤ) :
    Summable (fun x : ℤ => g (x + c)) := by
  have := (Equiv.summable_iff (Equiv.addRight c) (f := g)).mpr hg
  simpa only [Function.comp_def, Equiv.coe_addRight] using this

/-- `dualFn N P f₀ f₁` is bounded by `1` when `f₀` and `f₁` are. -/
private lemma dualFn_norm_le_one' {N : ℕ} (hN : 1 ≤ N) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ)
    (h0 : ∀ x : ℤ, ‖f₀ x‖ ≤ 1) (h1 : ∀ x : ℤ, ‖f₁ x‖ ≤ 1) (u : ℤ) :
    ‖Work.Peluse.dualFn N P f₀ f₁ u‖ ≤ 1 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hcard : ((Finset.Icc 1 N).card : ℝ) = (N : ℝ) := by
    rw [Nat.card_Icc]; simp
  set Z : ℂ := ∑ y ∈ Finset.Icc 1 N,
      f₀ (u - P.eval ((y : ℕ) : ℤ)) * f₁ (u + ((y : ℕ) : ℤ) - P.eval ((y : ℕ) : ℤ)) with hZ
  have hZbound : ‖Z‖ ≤ (N : ℝ) := by
    calc ‖Z‖ ≤ ∑ y ∈ Finset.Icc 1 N,
          ‖f₀ (u - P.eval ((y : ℕ) : ℤ)) * f₁ (u + ((y : ℕ) : ℤ) - P.eval ((y : ℕ) : ℤ))‖ := by
          rw [hZ]; exact norm_sum_le _ _
      _ ≤ ∑ y ∈ Finset.Icc 1 N, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro y hy
          rw [norm_mul]
          have hm := mul_le_mul (h0 (u - P.eval ((y : ℕ) : ℤ)))
            (h1 (u + ((y : ℕ) : ℤ) - P.eval ((y : ℕ) : ℤ))) (norm_nonneg _)
            (by norm_num : (0 : ℝ) ≤ 1)
          simpa using hm
      _ = ((Finset.Icc 1 N).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = (N : ℝ) := hcard
  rw [Work.Peluse.dualFn, norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖Z‖ ≤ (N : ℝ)⁻¹ * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hZbound (by positivity)
    _ = 1 := by rw [inv_mul_cancel₀ (ne_of_gt hNpos)]

/-- Jensen for the uniform average over `[1, M]`. -/
private lemma ave_pow_le {N : ℕ} (hN : 1 ≤ N) (g : ℕ → ℝ) (hg : ∀ y, 0 ≤ g y) (q : ℕ) :
    (((N : ℝ))⁻¹ * ∑ y ∈ Finset.Icc 1 N, g y) ^ q ≤
      ((N : ℝ))⁻¹ * ∑ y ∈ Finset.Icc 1 N, (g y) ^ q := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hcard : ((Finset.Icc 1 N).card : ℝ) = (N : ℝ) := by rw [Nat.card_Icc]; simp
  have hw : ∑ y ∈ Finset.Icc 1 N, ((N : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard, mul_inv_cancel₀ (ne_of_gt hNpos)]
  have h := Real.pow_arith_mean_le_arith_mean_pow (Finset.Icc 1 N) (fun _ => ((N : ℝ))⁻¹) g
    (by intro i _; positivity) hw (by intro i _; exact hg i) q
  simpa only [Finset.mul_sum, ← Finset.sum_mul] using h

/-- The pointwise Jensen bound: the squared modulus of the dual function is at most the average
of the squared moduli of the products. -/
private lemma dualFn_normSq_le_ave {N : ℕ} (hN : 1 ≤ N) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ) (u : ℤ) :
    ‖Work.Peluse.dualFn N P f₀ f₁ u‖ ^ 2 ≤
      ((N : ℝ))⁻¹ * ∑ y ∈ Finset.Icc 1 N,
        ‖f₀ (u - P.eval ((y : ℕ) : ℤ))‖ ^ 2 *
          ‖f₁ (u + ((y : ℕ) : ℤ) - P.eval ((y : ℕ) : ℤ))‖ ^ 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hcard : ((Finset.Icc 1 N).card : ℝ) = (N : ℝ) := by rw [Nat.card_Icc]; simp
  set a : ℕ → ℝ := fun y => ‖f₀ (u - P.eval ((y : ℕ) : ℤ)) *
      f₁ (u + ((y : ℕ) : ℤ) - P.eval ((y : ℕ) : ℤ))‖ with ha
  set Z : ℂ := ∑ y ∈ Finset.Icc 1 N,
      f₀ (u - P.eval ((y : ℕ) : ℤ)) * f₁ (u + ((y : ℕ) : ℤ) - P.eval ((y : ℕ) : ℤ)) with hZ
  have ha0 : ∀ y, 0 ≤ a y := by intro y; rw [ha]; exact norm_nonneg _
  -- Cauchy-Schwarz on the `y`-sum
  have hCS : (∑ y ∈ Finset.Icc 1 N, a y) ^ 2
      ≤ (N : ℝ) * ∑ y ∈ Finset.Icc 1 N, (a y) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N) a (fun _ => (1 : ℝ))
    have h' : (∑ y ∈ Finset.Icc 1 N, a y) ^ 2
        ≤ (∑ y ∈ Finset.Icc 1 N, (a y) ^ 2) * ((Finset.Icc 1 N).card : ℝ) := by
      simpa [Finset.sum_const, nsmul_eq_mul] using h
    rw [hcard] at h'
    linarith [h']
  have hZnorm : ‖Z‖ ≤ ∑ y ∈ Finset.Icc 1 N, a y := by
    rw [hZ, ha]; exact norm_sum_le _ _
  have hZsq : ‖Z‖ ^ 2 ≤ (N : ℝ) * ∑ y ∈ Finset.Icc 1 N, (a y) ^ 2 :=
    le_trans (pow_le_pow_left₀ (norm_nonneg _) hZnorm 2) hCS
  have hdual : ‖Work.Peluse.dualFn N P f₀ f₁ u‖ = (N : ℝ)⁻¹ * ‖Z‖ := by
    rw [Work.Peluse.dualFn, ← hZ, norm_mul, norm_inv, Complex.norm_natCast]
  rw [hdual]
  have hsq : ((N : ℝ)⁻¹ * ‖Z‖) ^ 2 = (N : ℝ)⁻¹ ^ 2 * ‖Z‖ ^ 2 := by ring
  rw [hsq]
  have hkey : ∑ y ∈ Finset.Icc 1 N, (a y) ^ 2 =
      ∑ y ∈ Finset.Icc 1 N,
        ‖f₀ (u - P.eval ((y : ℕ) : ℤ))‖ ^ 2 * ‖f₁ (u + ((y : ℕ) : ℤ) - P.eval ((y : ℕ) : ℤ))‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro y hy
    show (‖f₀ (u - P.eval ((y : ℕ) : ℤ)) *
      f₁ (u + ((y : ℕ) : ℤ) - P.eval ((y : ℕ) : ℤ))‖) ^ 2 = _
    rw [norm_mul, mul_pow]
  calc (N : ℝ)⁻¹ ^ 2 * ‖Z‖ ^ 2
      ≤ (N : ℝ)⁻¹ ^ 2 * ((N : ℝ) * ∑ y ∈ Finset.Icc 1 N, (a y) ^ 2) :=
        mul_le_mul_of_nonneg_left hZsq (by positivity)
    _ = (N : ℝ)⁻¹ * ∑ y ∈ Finset.Icc 1 N,
        ‖f₀ (u - P.eval ((y : ℕ) : ℤ))‖ ^ 2 * ‖f₁ (u + ((y : ℕ) : ℤ) - P.eval ((y : ℕ) : ℤ))‖ ^ 2 := by
        rw [hkey]
        field_simp

/-- Membership in `symIcc`. -/
private lemma mem_symIcc_iff (N : ℕ) (x : ℤ) : x ∈ Work.Peluse.symIcc N ↔ x.natAbs ≤ N := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · intro h
    have h1 : |x| ≤ (N : ℤ) := abs_le.mpr h
    rw [← Int.natCast_natAbs] at h1
    exact_mod_cast h1
  · intro h
    have h1 : ((x.natAbs : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast h
    rw [Int.natCast_natAbs] at h1
    exact abs_le.mp h1

/-- The cardinality of `symIcc`. -/
private lemma symIcc_card (N : ℕ) : (Work.Peluse.symIcc N).card = 2 * N + 1 := by
  rw [Work.Peluse.symIcc, Int.card_Icc]
  have h1 : ((N : ℤ) + 1 - -((N : ℤ))) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h1]
  exact Int.toNat_natCast _

/-- The `tsum` of a finite sum of summability functions. -/
private lemma tsum_finset_sum' {ι : Type*} {s : Finset ι} {f : ι → ℤ → ℝ}
    (h : ∀ i ∈ s, Summable (f i)) :
    (∑' x : ℤ, ∑ i ∈ s, f i x) = ∑ i ∈ s, ∑' x : ℤ, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have h1 : Summable (f a) := h a (Finset.mem_insert_self a s)
      have h2 : Summable (fun x => ∑ i ∈ s, f i x) :=
        Summable.finset_sum' (fun i hi => h i (Finset.mem_insert_of_mem hi))
      rw [Finset.sum_insert ha]
      rw [show (∑' x : ℤ, ∑ i ∈ insert a s, f i x) = ∑' x : ℤ, (f a x + ∑ i ∈ s, f i x) from
        tsum_congr (fun x => by rw [Finset.sum_insert ha])]
      rw [h1.tsum_add h2, ih (fun i hi => h i (Finset.mem_insert_of_mem hi))]

/-- Translation invariance of a `tsum` over `ℤ`. -/
private lemma tsum_shift (g : ℤ → ℝ) (c : ℤ) : (∑' x : ℤ, g (x + c)) = ∑' x : ℤ, g x := by
  have := Equiv.tsum_eq (Equiv.addRight c) g
  simpa only [Equiv.coe_addRight] using this

/-- `star` of a real cast is the cast itself; hence `star ↑r * ↑r = ↑(r * r)`. -/
private lemma conj_pow_mul_self (r : ℝ) (k : ℕ) :
    star (((r ^ k : ℝ)) : ℂ) * (((r ^ k : ℝ)) : ℂ) = (((r ^ (2 * k) : ℝ)) : ℂ) := by
  have h : star (((r ^ k : ℝ)) : ℂ) = (((r ^ k : ℝ)) : ℂ) := by simp
  rw [h, ← Complex.ofReal_mul, Complex.ofReal_inj, ← pow_add]
  congr 1
  ring

/-- With *diagonal* shift pairs `(u i, u i)` the iterated `Δ'`-difference collapses to the
`2 ^ (n+1)`-th power of the modulus: the two recursive branches coincide. -/
private theorem iterDelta_diag_succ' (n : ℕ) : ∀ (u : Fin (n + 1) → ℤ) (f : ℤ → ℂ) (x : ℤ),
    Work.Peluse.Ulower.iterDelta' (n + 1) (fun i => (u i, u i)) f x
      = ((‖f (x + ∑ i, u i)‖ ^ (2 ^ (n + 1)) : ℝ) : ℂ) := by
  induction n with
  | zero =>
    intro u f x
    simp only [iterDelta']
    rw [Fin.sum_univ_one]
    norm_num
    rw [RCLike.conj_mul]
    norm_num
  | succ n ih =>
    intro u f x
    show star (Work.Peluse.Ulower.iterDelta' (n + 1) (fun i => (u i.succ, u i.succ)) f (x + u 0)) *
        Work.Peluse.Ulower.iterDelta' (n + 1) (fun i => (u i.succ, u i.succ)) f (x + u 0) = _
    rw [ih (fun i => u i.succ) f (x + u 0)]
    conv_rhs => rw [Fin.sum_univ_succ]
    rw [show (x + u 0) + ∑ i : Fin (n + 1), u i.succ
        = x + (u 0 + ∑ i : Fin (n + 1), u i.succ) from by ring]
    rw [show (2 : ℕ) ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) from by rw [pow_succ]; ring]
    exact conj_pow_mul_self ‖f (x + (u 0 + ∑ i : Fin (n + 1), u i.succ))‖ (2 ^ (n + 1))

/-- Diagonal shift pairs: `iterDelta' t (fun i => (u i, u i)) f x = ↑(‖f (x + ∑ u)‖ ^ 2 ^ t)`. -/
private lemma iterDelta_diag_priv {t : ℕ} (ht : 1 ≤ t) (u : Fin t → ℤ) (f : ℤ → ℂ) (x : ℤ) :
    Work.Peluse.Ulower.iterDelta' t (fun i => (u i, u i)) f x
      = ((‖f (x + ∑ i, u i)‖ ^ (2 ^ t) : ℝ) : ℂ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  exact iterDelta_diag_succ' n u f x

end

end Work.Peluse.Ulower
