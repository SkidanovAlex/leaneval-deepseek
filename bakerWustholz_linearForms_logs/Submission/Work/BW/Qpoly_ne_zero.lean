import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 400000

/-!
# `Work.BW.Qpoly_ne_zero`

BW §12 last paragraph / §13: `P = Q(·;0) ≠ 0` when `p ≠ 0`, by the linear independence of
`(Δ(z+j;k))^l`, `0 ≤ j ≤ k−1`, `l ≥ 1` (Baker, *Transcendental Number Theory*, Ch. 3, L2)
together with independence of the monomials `Y^λ`.

The file is organised as

* `coeff_prod_X_add_C` — the multinomial expansion of a product of linear factors;
* `vandermonde_general` — the generalized Vandermonde fact;
* `prod_shift_pow_indep` — Baker's independence in shifted-product form;
* `aeval_deltaPoly`, `deltaPoly_aeval_indep` — transport to `deltaPoly`/`aeval` form;
* `Qpoly_ne_zero` — the extraction of the `Y^λ`-coefficients.
-/

namespace Work.BW

open Polynomial

/-! ## Coefficient of a product of linear factors -/

/-- Multinomial expansion: the coefficient of `X ^ (#s - m)` in `∏_{i ∈ s} (X + C (b i))` is the
elementary symmetric function `∑_{t ⊆ s, #t = m} ∏_{i ∈ t} b i`. -/
theorem coeff_prod_X_add_C {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → ℂ) {m : ℕ}
    (hm : m ≤ s.card) :
    (∏ i ∈ s, (Polynomial.X + Polynomial.C (b i))).coeff (s.card - m)
      = ∑ t ∈ s.powersetCard m, ∏ i ∈ t, b i := by
  classical
  have hsplit : (∏ i ∈ s, (Polynomial.X + Polynomial.C (b i)))
      = ∑ t ∈ s.powerset, Polynomial.C (∏ i ∈ t, b i) * Polynomial.X ^ (s.card - t.card) := by
    have h1 : (∏ i ∈ s, (Polynomial.X + Polynomial.C (b i)))
        = ∏ i ∈ s, (Polynomial.C (b i) + Polynomial.X) :=
      Finset.prod_congr rfl (fun i _ => by ring)
    rw [h1, Finset.prod_add]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [← map_prod, Finset.prod_const, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp ht)]
  rw [hsplit, Polynomial.finsetSum_coeff]
  have key : ∀ t ∈ s.powerset,
      (Polynomial.C (∏ i ∈ t, b i) * Polynomial.X ^ (s.card - t.card)).coeff (s.card - m)
        = if t.card = m then ∏ i ∈ t, b i else 0 := by
    intro t ht
    have hts : t ⊆ s := Finset.mem_powerset.mp ht
    have htc : t.card ≤ s.card := Finset.card_le_card hts
    rw [Polynomial.coeff_C_mul_X_pow]
    by_cases h : t.card = m
    · subst h; rw [ite_eq_left rfl, ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right h]
  rw [Finset.sum_congr rfl key]
  rw [← Finset.sum_filter, ← Finset.powersetCard_eq_filter]

/-! ## Generalized Vandermonde -/

/-- Generalized Vandermonde: if `P m` has degree `≤ m` and nonzero `m`-th coefficient, then the
moments `∑_j c j * (P m).eval j` determine `c`; the nodes are `0, 1, …, h-1`. -/
theorem vandermonde_general {h : ℕ} (P : Fin h → Polynomial ℂ)
    (hdeg : ∀ m, (P m).natDegree ≤ m) (hlc : ∀ m, (P m).coeff m ≠ 0)
    (c : Fin h → ℂ) (hvan : ∀ m : Fin h, ∑ j : Fin h, c j * (P m).eval (j : ℂ) = 0) :
    c = 0 := by
  classical
  rcases Nat.eq_zero_or_pos h with h0 | hpos
  · subst h0; funext j; exact Fin.elim0 j
  have hinj : Set.InjOn (fun j : Fin h => (j : ℂ)) (Finset.univ : Finset (Fin h)) :=
    fun a _ b _ hab => Fin.ext (Nat.cast_injective hab)
  set Φ : Polynomial ℂ → ℂ := fun Q => ∑ j : Fin h, c j * Q.eval (j : ℂ) with hΦ
  have hΦ_add : ∀ Q Q' : Polynomial ℂ, Φ (Q + Q') = Φ Q + Φ Q' := by
    intro Q Q'
    simp only [hΦ, Polynomial.eval_add, mul_add, Finset.sum_add_distrib]
  have hΦ_C : ∀ (a : ℂ) (Q : Polynomial ℂ), Φ (Polynomial.C a * Q) = a * Φ Q := by
    intro a Q
    simp only [hΦ, Polynomial.eval_mul, Polynomial.eval_C]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hvan' : ∀ m : Fin h, Φ (P m) = 0 := fun m => by rw [hΦ]; exact hvan m
  have decomp : ∀ (m : ℕ) (Q : Polynomial ℂ), Q.natDegree ≤ m →
      ∃ R : Polynomial ℂ, R.natDegree ≤ m - 1 ∧
        Q = Polynomial.C (Q.coeff m) * Polynomial.X ^ m + R := by
    intro m Q hQ
    refine ⟨Q - Polynomial.C (Q.coeff m) * Polynomial.X ^ m, ?_, by ring⟩
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow]
    rcases eq_or_lt_of_le (by omega : m ≤ n) with hnm | hlt
    · subst hnm; rw [ite_eq_left rfl]; ring
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < n),
        ite_eq_right (by omega : n ≠ m), sub_zero]
  have gen : ∀ m, m < h → ∀ Q : Polynomial ℂ, Q.natDegree ≤ m → Φ Q = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm Q hQ
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        have hP0 : P ⟨0, hm⟩ = Polynomial.C ((P ⟨0, hm⟩).coeff 0) :=
          Polynomial.eq_C_of_natDegree_le_zero (by simpa using hdeg ⟨0, hm⟩)
        have h1 : Φ (1 : Polynomial ℂ) = 0 := by
          have h := hvan' ⟨0, hm⟩
          rw [hP0] at h
          have h2 : Φ (Polynomial.C ((P ⟨0, hm⟩).coeff 0))
              = (P ⟨0, hm⟩).coeff 0 * Φ (1 : Polynomial ℂ) := by
            simpa using hΦ_C ((P ⟨0, hm⟩).coeff 0) (1 : Polynomial ℂ)
          rw [h2] at h
          exact (mul_eq_zero.mp h).resolve_left (hlc ⟨0, hm⟩)
        rw [Polynomial.eq_C_of_natDegree_le_zero hQ]
        have h3 : Φ (Polynomial.C (Q.coeff 0)) = (Q.coeff 0) * Φ (1 : Polynomial ℂ) := by
          simpa using hΦ_C (Q.coeff 0) (1 : Polynomial ℂ)
        rw [h3, h1, mul_zero]
      · obtain ⟨R, hRdeg, hR⟩ := decomp m Q hQ
        have hR0 : Φ R = 0 := ih (m - 1) (by omega) (by omega) R hRdeg
        obtain ⟨R', hR'deg, hR'⟩ := decomp m (P ⟨m, hm⟩) (hdeg ⟨m, hm⟩)
        have hR'0 : Φ R' = 0 := ih (m - 1) (by omega) (by omega) R' hR'deg
        have hXm : Φ (Polynomial.X ^ m) = 0 := by
          have h := hvan' ⟨m, hm⟩
          rw [hR'] at h
          have h2 : Φ (Polynomial.C ((P ⟨m, hm⟩).coeff m) * Polynomial.X ^ m + R')
              = (P ⟨m, hm⟩).coeff m * Φ (Polynomial.X ^ m) + Φ R' := by
            rw [hΦ_add, hΦ_C]
          rw [h2, hR'0, add_zero] at h
          exact (mul_eq_zero.mp h).resolve_left (hlc ⟨m, hm⟩)
        rw [hR, hΦ_add, hΦ_C, hXm, hR0, mul_zero, zero_add]
  funext j₀
  set L := Lagrange.basis (Finset.univ : Finset (Fin h)) (fun j : Fin h => (j : ℂ)) j₀ with hL
  have hLdeg : L.natDegree = h - 1 := by
    rw [hL, Lagrange.natDegree_basis hinj (Finset.mem_univ j₀), Finset.card_univ, Fintype.card_fin]
  have hkey : Φ L = c j₀ := by
    rw [hΦ]
    change (∑ j : Fin h, c j * L.eval (j : ℂ)) = c j₀
    rw [Finset.sum_eq_single j₀]
    · rw [hL, Lagrange.eval_basis_self hinj (Finset.mem_univ j₀), mul_one]
    · intro j _ hj
      rw [hL, Lagrange.eval_basis_of_ne (s := Finset.univ) (v := fun i : Fin h => (i : ℂ))
        hj.symm (Finset.mem_univ j), mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j₀) hj
  have hgen := gen (h - 1) (by omega) L (by rw [hLdeg])
  rw [hkey] at hgen
  exact hgen

/-! ## Baker's independence lemma, product form -/

/-- **Baker's linear independence** (Baker, *Transcendental Number Theory*, Ch. 3, L2), in the
shifted-product form of BW §12: the polynomials `(∏_{i < h} (X + (j + i + 1)))^(l+1)`,
`j < h`, `l ≤ D`, are `ℂ`-linearly independent. -/
lemma rat_smul_C (q : ℚ) (P : Polynomial ℂ) : q • P = Polynomial.C ((q : ℂ)) * P := by
  rw [Algebra.smul_def, Polynomial.algebraMap_apply]
  congr 2

lemma aeval_X_add_C (c : ℂ) (q : ℚ) :
    Polynomial.aeval (Polynomial.X + Polynomial.C c) (Polynomial.X + Polynomial.C q)
      = Polynomial.X + Polynomial.C (c + (q : ℂ)) := by
  have hq : (algebraMap ℚ ℂ) q = (q : ℂ) := by exact_mod_cast rfl
  rw [map_add, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.algebraMap_apply, hq,
    Polynomial.C_add]
  ring

/-- **Baker's linear independence** (Baker, *Transcendental Number Theory*, Ch. 3, L2), in the
shifted-product form of BW §12: the polynomials `(∏_{i < h} (X + (j + i + 1)))^(l+1)`,
`j < h`, `l ≤ D`, are `ℂ`-linearly independent. -/
theorem prod_shift_pow_indep {h D : ℕ} (c : Fin h → Fin (D + 1) → ℂ)
    (hc : (∑ j : Fin h, ∑ l : Fin (D + 1), c j l •
        (∏ i ∈ Finset.range h,
          (Polynomial.X + Polynomial.C (((j : ℕ) + i + 1 : ℕ) : ℂ))) ^ ((l : ℕ) + 1)) = 0) :
    c = 0 := by
  classical
  rcases Nat.eq_zero_or_pos h with h0 | hpos
  · subst h0; funext j; exact Fin.elim0 j
  set G : Fin h → Polynomial ℂ := fun j =>
    ∏ i ∈ Finset.range h, (Polynomial.X + Polynomial.C (((j : ℕ) + i + 1 : ℕ) : ℂ)) with hG
  set H : Fin (D + 1) → Polynomial ℂ := fun l =>
    ∑ j : Fin h, Polynomial.C (c j l) * (G j) ^ ((l : ℕ) + 1) with hH
  have hGdeg : ∀ j : Fin h, (G j).natDegree ≤ h := by
    intro j
    have hGj : (G j).natDegree ≤ ∑ i ∈ Finset.range h, (1 : ℕ) := by
      rw [hG]
      refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
      exact Finset.sum_le_sum fun i _ => le_of_eq (Polynomial.natDegree_X_add_C _)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hGj
    exact hGj
  have hdeg : ∀ l : Fin (D + 1), (H l).natDegree ≤ h * ((l : ℕ) + 1) := by
    intro l
    rw [hH]
    refine Polynomial.natDegree_sum_le_of_forall_le (Finset.univ)
      (fun j => Polynomial.C (c j l) * (G j) ^ ((l : ℕ) + 1)) ?_
    intro j _
    calc (Polynomial.C (c j l) * (G j) ^ ((l : ℕ) + 1)).natDegree
        ≤ ((G j) ^ ((l : ℕ) + 1)).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ ≤ ((l : ℕ) + 1) * (G j).natDegree := Polynomial.natDegree_pow_le
      _ ≤ ((l : ℕ) + 1) * h := Nat.mul_le_mul_left _ (hGdeg j)
      _ = h * ((l : ℕ) + 1) := Nat.mul_comm _ _
  have hsum : ∑ l : Fin (D + 1), H l = 0 := by
    rw [hH]
    have hc' := hc
    simp only [Polynomial.smul_eq_C_mul] at hc'
    rw [Finset.sum_comm]
    simp only [hG]
    exact hc'
  have key : ∀ l : Fin (D + 1), (∀ l' : Fin (D + 1), l < l' → H l' = 0) →
      (∀ j : Fin h, c j l = 0) := by
    intro l hgt
    set s : Finset (ℕ × ℕ) := Finset.range h ×ˢ Finset.range ((l : ℕ) + 1) with hs
    set Pm : Fin h → Polynomial ℂ := fun m => ∑ t ∈ s.powersetCard m.val,
      ∏ p ∈ t, (Polynomial.X + Polynomial.C (((p.1 : ℕ) + 1 : ℕ) : ℂ)) with hPm
    have hs_card : s.card = h * ((l : ℕ) + 1) := by
      rw [hs, Finset.card_product, Finset.card_range, Finset.card_range]
    have hGpow : ∀ (j : Fin h) (m : Fin h),
        ((G j) ^ ((l : ℕ) + 1)).coeff (h * ((l : ℕ) + 1) - m.val) = (Pm m).eval (j : ℂ) := by
      intro j m
      have hp : (∏ p ∈ s, (Polynomial.X + Polynomial.C (((j : ℕ) + p.1 + 1 : ℕ) : ℂ)))
          = (G j) ^ ((l : ℕ) + 1) := by
        rw [hG]
        change (∏ p ∈ s, (Polynomial.X + Polynomial.C (((j : ℕ) + p.1 + 1 : ℕ) : ℂ)))
          = (∏ i ∈ Finset.range h,
              (Polynomial.X + Polynomial.C (((j : ℕ) + i + 1 : ℕ) : ℂ))) ^ ((l : ℕ) + 1)
        rw [hs, Finset.prod_product, ← Finset.prod_pow]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [show (∏ y ∈ Finset.range ((l : ℕ) + 1),
              (Polynomial.X + Polynomial.C (((j : ℕ) + i + 1 : ℕ) : ℂ)))
            = (Polynomial.X + Polynomial.C (((j : ℕ) + i + 1 : ℕ) : ℂ)) ^ ((l : ℕ) + 1)
            from by rw [Finset.prod_const, Finset.card_range]]
      have hmle : m.val ≤ s.card := by
        rw [hs_card]
        have h1 : m.val < h := m.isLt
        have h2 : 0 < h := hpos
        nlinarith
      rw [← hp, ← hs_card,
        coeff_prod_X_add_C s (fun p => (((j : ℕ) + p.1 + 1 : ℕ) : ℂ)) hmle,
        hPm, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Polynomial.eval_prod]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      push_cast
      ring
    have natDegree_Pm_le : ∀ m : Fin h, (Pm m).natDegree ≤ m.val := by
      intro m
      rw [hPm]
      refine Polynomial.natDegree_sum_le_of_forall_le (s.powersetCard m.val)
        (fun t => ∏ p ∈ t, (Polynomial.X + Polynomial.C (((p.1 : ℕ) + 1 : ℕ) : ℂ))) ?_
      intro t ht
      have htc : t.card = m.val := (Finset.mem_powersetCard.mp ht).2
      calc (∏ p ∈ t, (Polynomial.X + Polynomial.C (((p.1 : ℕ) + 1 : ℕ) : ℂ))).natDegree
          ≤ ∑ p ∈ t, (Polynomial.X + Polynomial.C (((p.1 : ℕ) + 1 : ℕ) : ℂ)).natDegree :=
            Polynomial.natDegree_prod_le _ _
        _ = ∑ p ∈ t, (1 : ℕ) := Finset.sum_congr rfl fun p _ => Polynomial.natDegree_X_add_C _
        _ = t.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]
        _ = m.val := htc
    have coeff_Pm_ne_zero : ∀ m : Fin h, (Pm m).coeff m.val ≠ 0 := by
      intro m
      rw [hPm, Polynomial.finsetSum_coeff]
      have htc : ∀ t ∈ s.powersetCard m.val,
          (∏ p ∈ t, (Polynomial.X + Polynomial.C (((p.1 : ℕ) + 1 : ℕ) : ℂ))).coeff m.val
            = 1 := by
        intro t ht
        have h2 : t.card = m.val := (Finset.mem_powersetCard.mp ht).2
        have h := coeff_prod_X_add_C t (fun p => (((p.1 : ℕ) + 1 : ℕ) : ℂ)) (Nat.zero_le t.card)
        rw [Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty, Nat.sub_zero] at h
        rw [← h2]; exact h
      rw [Finset.sum_congr rfl htc, Finset.sum_const, Finset.card_powersetCard, hs_card,
        nsmul_eq_mul, mul_one, Nat.cast_ne_zero]
      refine Nat.ne_of_gt (Nat.choose_pos ?_)
      nlinarith [m.isLt, hpos]
    have hmain : ∀ m : Fin h, ∑ j : Fin h, c j l * (Pm m).eval (j : ℂ) = 0 := by
      intro m
      have h1 : (∑ l' : Fin (D + 1), (H l').coeff (h * ((l : ℕ) + 1) - m.val))
          = (H l).coeff (h * ((l : ℕ) + 1) - m.val) := by
        refine Finset.sum_eq_single l ?_ ?_
        · intro l' _ hl'
          rcases lt_or_gt_of_ne hl' with hlt' | hgt'
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
            refine lt_of_le_of_lt (hdeg l') ?_
            have hle : (l' : ℕ) + 1 ≤ (l : ℕ) := by
              have h : (l' : ℕ) < (l : ℕ) := hlt'
              omega
            have hA : h * ((l' : ℕ) + 1) ≤ h * (l : ℕ) := Nat.mul_le_mul_left h hle
            have hC : h * ((l : ℕ) + 1) = h * (l : ℕ) + h := by ring
            have hB : m.val < h := m.isLt
            have hm : m.val ≤ h * ((l : ℕ) + 1) := by omega
            omega
          · rw [hgt l' hgt', Polynomial.coeff_zero]
        · intro hmem; exact absurd (Finset.mem_univ l) hmem
      have h2 : (H l).coeff (h * ((l : ℕ) + 1) - m.val) = 0 := by
        have hc0 : (∑ l' : Fin (D + 1), (H l').coeff (h * ((l : ℕ) + 1) - m.val)) = 0 := by
          have h := congrArg (fun Q : Polynomial ℂ => Q.coeff (h * ((l : ℕ) + 1) - m.val)) hsum
          rwa [Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at h
        rw [← h1]; exact hc0
      rw [← h2, hH, Polynomial.finsetSum_coeff]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Polynomial.coeff_C_mul, hGpow j m]
    have hv := vandermonde_general Pm natDegree_Pm_le coeff_Pm_ne_zero (fun j => c j l) hmain
    intro j
    simpa using congrFun hv j
  have keyl : ∀ k : ℕ, ∀ l : Fin (D + 1), D - k ≤ l.val → (∀ j : Fin h, c j l = 0) := by
    intro k
    induction k with
    | zero =>
      intro l hl j
      have hl' : l = Fin.last D := by
        refine Fin.ext ?_
        rw [Fin.val_last]
        have := l.isLt
        omega
      subst hl'
      refine key (Fin.last D) (fun l'' hlt => ?_) j
      exfalso
      rw [Fin.lt_def, Fin.val_last] at hlt
      omega
    | succ k ih =>
      intro l hl j
      by_cases hcase : D - k ≤ l.val
      · exact ih l hcase j
      · refine key l (fun l'' hlt => ?_) j
        rw [hH]
        refine Finset.sum_eq_zero fun j' _ => ?_
        rw [ih l'' ?_ j', Polynomial.C_0, zero_mul]
        rw [Fin.lt_def] at hlt
        omega
  funext j l
  exact keyl (D - l.val) l (by omega) j

/-! ## Transport to the `deltaPoly`/`aeval` form -/

lemma aeval_deltaPoly (h j : ℕ) :
    Polynomial.aeval (Polynomial.X + Polynomial.C ((j : ℕ) : ℂ)) (deltaPoly h)
      = Polynomial.C (((h.factorial : ℂ))⁻¹) *
          ∏ i ∈ Finset.range h, (Polynomial.X + Polynomial.C (((j : ℕ) + i + 1 : ℕ) : ℂ)) := by
  rw [deltaPoly, map_smul, map_prod, rat_smul_C]
  congr 1
  · congr 1
    push_cast
    rfl
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [aeval_X_add_C]
    congr 1
    push_cast
    ring_nf

lemma aeval_deltaPoly_pow (h l j : ℕ) :
    Polynomial.aeval (Polynomial.X + Polynomial.C ((j : ℕ) : ℂ)) (deltaPoly h ^ (l + 1))
      = (((h.factorial : ℂ))⁻¹ ^ (l + 1)) •
          (∏ i ∈ Finset.range h,
            (Polynomial.X + Polynomial.C (((j : ℕ) + i + 1 : ℕ) : ℂ))) ^ (l + 1) := by
  rw [map_pow, aeval_deltaPoly, mul_pow, ← map_pow, ← Polynomial.smul_eq_C_mul]

/-- Baker's independence in the form needed for `Qpoly`: the polynomials
`aeval (X + j) (deltaPoly h ^ (l+1))` are `ℂ`-linearly independent. -/
theorem deltaPoly_aeval_indep {h D : ℕ} (c : Fin h → Fin (D + 1) → ℂ)
    (hc : (∑ j : Fin h, ∑ l : Fin (D + 1), c j l •
        Polynomial.aeval (Polynomial.X + Polynomial.C ((j : ℕ) : ℂ))
          (deltaPoly h ^ ((l : ℕ) + 1))) = 0) :
    c = 0 := by
  have hc' : (∑ j : Fin h, ∑ l : Fin (D + 1),
      (c j l * ((h.factorial : ℂ))⁻¹ ^ ((l : ℕ) + 1)) •
        (∏ i ∈ Finset.range h,
          (Polynomial.X + Polynomial.C (((j : ℕ) + i + 1 : ℕ) : ℂ))) ^ ((l : ℕ) + 1)) = 0 := by
    rw [← hc]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [aeval_deltaPoly_pow, smul_smul]
  have h2 := prod_shift_pow_indep (fun j l => c j l * ((h.factorial : ℂ))⁻¹ ^ ((l : ℕ) + 1)) hc'
  funext j l
  have h3 := congrFun (congrFun h2 j) l
  simp only [Pi.zero_apply] at h3
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact h4
  · exact absurd h4 (pow_ne_zero _ (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero h))))

/-! ## Extraction of the `Y^λ`-coefficients -/

/-- `Δ z 0 = 1`. -/
lemma Delta_zero (z : ℂ) : Delta z 0 = 1 := by
  simp [Delta, deltaPoly]

/-- The evaluation homomorphism `Y₀ ↦ X`, `Y_{i+1} ↦ C (t i)`. -/
noncomputable def evHom {r : ℕ} (t : Fin r → ℂ) :
    MvPolynomial (Fin (r + 1)) ℂ →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C (Fin.cons Polynomial.X (fun i => Polynomial.C (t i)))

lemma evHom_C {r : ℕ} (t : Fin r → ℂ) (c : ℂ) :
    evHom t (MvPolynomial.C c) = Polynomial.C c := by
  simp [evHom]

lemma evHom_X_zero {r : ℕ} (t : Fin r → ℂ) : evHom t (MvPolynomial.X 0) = Polynomial.X := by
  simp [evHom]

lemma evHom_X_succ {r : ℕ} (t : Fin r → ℂ) (i : Fin r) :
    evHom t (MvPolynomial.X i.succ) = Polynomial.C (t i) := by
  simp [evHom]

lemma evHom_aeval {r : ℕ} (t : Fin r → ℂ) (f : MvPolynomial (Fin (r + 1)) ℂ)
    (q : Polynomial ℚ) : evHom t (Polynomial.aeval f q) = Polynomial.aeval (evHom t f) q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial m a =>
    simp only [Polynomial.aeval_monomial, map_mul, map_pow, evHom_C,
      MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply]

/-- The evaluation of a single term of `Qpoly` at `t`. -/
lemma evHom_term {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ) (k : Fin n)
    (L : Fin r → Fin n → ℤ) (h D0 : ℕ) (Dj : Fin r → ℕ) (p : AuxIdx r h D0 Dj → K)
    (t : Fin r → ℂ) (j : Fin h) (l : Fin (D0 + 1)) (lam : ∀ i : Fin r, Fin (Dj i + 1)) :
    evHom t (MvPolynomial.C (φ (p (j, l, lam))) *
      Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C ((j : ℕ) : ℂ))
        (deltaPoly h ^ ((l : ℕ) + 1)) *
      (∏ i : Fin r, MvPolynomial.X i.succ ^ ((lam i : ℕ))))
    = (φ (p (j, l, lam)) * ∏ i : Fin r, t i ^ ((lam i : ℕ))) •
        Polynomial.aeval (Polynomial.X + Polynomial.C ((j : ℕ) : ℂ))
          (deltaPoly h ^ ((l : ℕ) + 1)) := by
  have hA : evHom t (Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C ((j : ℕ) : ℂ))
        (deltaPoly h ^ ((l : ℕ) + 1)))
      = Polynomial.aeval (Polynomial.X + Polynomial.C ((j : ℕ) : ℂ))
          (deltaPoly h ^ ((l : ℕ) + 1)) := by
    rw [evHom_aeval, map_add, evHom_X_zero, evHom_C]
  have hY : evHom t (∏ i : Fin r, MvPolynomial.X i.succ ^ ((lam i : ℕ)))
      = Polynomial.C (∏ i : Fin r, t i ^ ((lam i : ℕ))) := by
    rw [map_prod, map_prod (Polynomial.C)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, evHom_X_succ, ← Polynomial.C_pow]
  rw [map_mul, map_mul, evHom_C, hA, hY]
  rw [show (Polynomial.C (φ (p (j, l, lam))) *
        Polynomial.aeval (Polynomial.X + Polynomial.C ((j : ℕ) : ℂ))
          (deltaPoly h ^ ((l : ℕ) + 1))) *
        Polynomial.C (∏ i : Fin r, t i ^ ((lam i : ℕ)))
      = (Polynomial.C (φ (p (j, l, lam))) *
          Polynomial.C (∏ i : Fin r, t i ^ ((lam i : ℕ)))) *
          Polynomial.aeval (Polynomial.X + Polynomial.C ((j : ℕ) : ℂ))
            (deltaPoly h ^ ((l : ℕ) + 1)) from by ring,
    ← map_mul, Polynomial.C_mul']

/-- The monomial index of `∏ i, X i ^ (lam i)`. -/
noncomputable def liftm {r : ℕ} (lam : Fin r → ℕ) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm lam

lemma liftm_apply {r : ℕ} (lam : Fin r → ℕ) (i : Fin r) : liftm lam i = lam i := by
  rw [liftm, Finsupp.coe_equivFunOnFinite_symm]

lemma liftm_injective {r : ℕ} : Function.Injective (liftm (r := r)) := by
  intro a b hab
  funext i
  rw [← liftm_apply a i, ← liftm_apply b i, hab]

lemma C_mul_prod_X_eq_monomial {r : ℕ} (a : ℂ) (lam : Fin r → ℕ) :
    (MvPolynomial.C a * ∏ i : Fin r, MvPolynomial.X i ^ (lam i))
      = MvPolynomial.monomial (liftm lam) a := by
  have hs : (Finsupp.indicator Finset.univ (fun i (_ : i ∈ Finset.univ) => lam i)) = liftm lam := by
    ext i
    rw [Finsupp.indicator_apply, liftm_apply]
    simp
  rw [MvPolynomial.prod_X_pow, hs, MvPolynomial.C_mul_monomial, mul_one]

lemma coeff_C_mul_prod_X {r : ℕ} (a : ℂ) (lam lam' : Fin r → ℕ) :
    (MvPolynomial.C a * ∏ i : Fin r, MvPolynomial.X i ^ (lam i)).coeff (liftm lam') =
      if lam = lam' then a else 0 := by
  rw [C_mul_prod_X_eq_monomial, MvPolynomial.coeff_monomial]
  by_cases h : lam = lam'
  · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h (liftm_injective hc))]

/-- BW §12 last paragraph / §13: `P = Q(·;0) ≠ 0` when `p ≠ 0`, by the linear independence of `(Δ(z+j;k))^l`, `0 ≤ j ≤ k−1`, `l ≥ 1` (Baker, *Transcendental Number Theory*, Ch. 3, L2) together with independence of the monomials `Y^λ`. -/
theorem Qpoly_ne_zero {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (α' : Fin r → K)
    (h D0 : ℕ) (Dj : Fin r → ℕ) (p : AuxIdx r h D0 Dj → K) (hp : p ≠ 0) :
    Qpoly φ b k L ι α' h D0 Dj p 0 0 ≠ 0 := by
  intro hQ
  rw [show Qpoly φ b k L ι α' h D0 Dj p 0 0 =
      (∑ lm : AuxIdx r h D0 Dj,
        MvPolynomial.C (φ (p lm)) *
          Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C ((lm.1 : ℕ) : ℂ))
            (deltaPoly h ^ ((lm.2.1 : ℕ) + 1)) *
          (∏ j : Fin r, MvPolynomial.X j.succ ^ ((lm.2.2 j : ℕ)))) from by
    simp only [Qpoly, Polynomial.hasseDeriv_zero, LinearMap.id_apply, pow_zero, mul_one,
      Pi.zero_apply, Finset.prod_const_one, Delta_zero]] at hQ
  have hiter : (∑ j : Fin h, ∑ l : Fin (D0 + 1), ∑ lam : (∀ i : Fin r, Fin (Dj i + 1)),
      MvPolynomial.C (φ (p (j, l, lam))) *
        Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C ((j : ℕ) : ℂ))
          (deltaPoly h ^ ((l : ℕ) + 1)) *
        (∏ i : Fin r, MvPolynomial.X i.succ ^ ((lam i : ℕ)))) = 0 := by
    rw [← hQ, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_prod_type]
  have hkey : ∀ t : Fin r → ℂ,
      (∑ j : Fin h, ∑ l : Fin (D0 + 1),
        (∑ lam : (∀ i : Fin r, Fin (Dj i + 1)), φ (p (j, l, lam)) * ∏ i, t i ^ ((lam i : ℕ))) •
          Polynomial.aeval (Polynomial.X + Polynomial.C ((j : ℕ) : ℂ))
            (deltaPoly h ^ ((l : ℕ) + 1))) = 0 := by
    intro t
    have h0 : evHom t (∑ j : Fin h, ∑ l : Fin (D0 + 1), ∑ lam : (∀ i : Fin r, Fin (Dj i + 1)),
        MvPolynomial.C (φ (p (j, l, lam))) *
          Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C ((j : ℕ) : ℂ))
            (deltaPoly h ^ ((l : ℕ) + 1)) *
          (∏ i : Fin r, MvPolynomial.X i.succ ^ ((lam i : ℕ)))) = 0 := by
      rw [hiter, map_zero]
    have h1 : evHom t (∑ j : Fin h, ∑ l : Fin (D0 + 1), ∑ lam : (∀ i : Fin r, Fin (Dj i + 1)),
        MvPolynomial.C (φ (p (j, l, lam))) *
          Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C ((j : ℕ) : ℂ))
            (deltaPoly h ^ ((l : ℕ) + 1)) *
          (∏ i : Fin r, MvPolynomial.X i.succ ^ ((lam i : ℕ))))
        = ∑ j : Fin h, ∑ l : Fin (D0 + 1), ∑ lam : (∀ i : Fin r, Fin (Dj i + 1)),
            (φ (p (j, l, lam)) * ∏ i, t i ^ ((lam i : ℕ))) •
              Polynomial.aeval (Polynomial.X + Polynomial.C ((j : ℕ) : ℂ))
                (deltaPoly h ^ ((l : ℕ) + 1)) := by
      simp only [map_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun lam _ => ?_
      exact evHom_term φ b k L h D0 Dj p t j l lam
    rw [show (∑ j : Fin h, ∑ l : Fin (D0 + 1),
          (∑ lam : (∀ i : Fin r, Fin (Dj i + 1)), φ (p (j, l, lam)) * ∏ i, t i ^ ((lam i : ℕ))) •
            Polynomial.aeval (Polynomial.X + Polynomial.C ((j : ℕ) : ℂ))
              (deltaPoly h ^ ((l : ℕ) + 1)))
        = (∑ j : Fin h, ∑ l : Fin (D0 + 1), ∑ lam : (∀ i : Fin r, Fin (Dj i + 1)),
            (φ (p (j, l, lam)) * ∏ i, t i ^ ((lam i : ℕ))) •
              Polynomial.aeval (Polynomial.X + Polynomial.C ((j : ℕ) : ℂ))
                (deltaPoly h ^ ((l : ℕ) + 1))) from by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_smul]]
    rw [← h1]
    exact h0
  have hg : ∀ (j : Fin h) (l : Fin (D0 + 1)),
      (∑ lam : (∀ i : Fin r, Fin (Dj i + 1)),
        MvPolynomial.C (φ (p (j, l, lam))) *
          (∏ i : Fin r, MvPolynomial.X i ^ ((lam i : ℕ)))) = 0 := by
    intro j l
    refine MvPolynomial.funext fun t => ?_
    have hc := deltaPoly_aeval_indep
      (fun j l => ∑ lam : (∀ i : Fin r, Fin (Dj i + 1)),
        φ (p (j, l, lam)) * ∏ i, t i ^ ((lam i : ℕ))) (hkey t)
    have hjl : (∑ lam : (∀ i : Fin r, Fin (Dj i + 1)),
        φ (p (j, l, lam)) * ∏ i, t i ^ ((lam i : ℕ))) = 0 := by
      simpa using congrFun (congrFun hc j) l
    rw [show MvPolynomial.eval t (∑ lam : (∀ i : Fin r, Fin (Dj i + 1)),
          MvPolynomial.C (φ (p (j, l, lam))) *
            (∏ i : Fin r, MvPolynomial.X i ^ ((lam i : ℕ))))
        = ∑ lam : (∀ i : Fin r, Fin (Dj i + 1)),
            φ (p (j, l, lam)) * ∏ i, t i ^ ((lam i : ℕ)) from by
      simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_prod, MvPolynomial.eval_pow, MvPolynomial.eval_X]]
    exact hjl
  have hcoeff : ∀ (j : Fin h) (l : Fin (D0 + 1)) (lam : ∀ i : Fin r, Fin (Dj i + 1)),
      φ (p (j, l, lam)) = 0 := by
    intro j l lam
    have hterm : (MvPolynomial.C (φ (p (j, l, lam))) *
        (∏ i : Fin r, MvPolynomial.X i ^ ((lam i : ℕ)))).coeff
          (liftm (fun i => (lam i : ℕ))) = φ (p (j, l, lam)) := by
      rw [coeff_C_mul_prod_X, ite_eq_left rfl]
    have hother : ∀ lam' ∈ (Finset.univ : Finset (∀ i : Fin r, Fin (Dj i + 1))),
        lam' ≠ lam → (MvPolynomial.C (φ (p (j, l, lam'))) *
          (∏ i : Fin r, MvPolynomial.X i ^ ((lam' i : ℕ)))).coeff
            (liftm (fun i => (lam i : ℕ))) = 0 := by
      intro lam' _ hne
      rw [coeff_C_mul_prod_X, ite_eq_right]
      exact fun hc => hne (funext fun i => Fin.ext (congrFun hc i))
    have h := congrArg (fun P : MvPolynomial (Fin r) ℂ =>
      P.coeff (liftm (fun i => (lam i : ℕ)))) (hg j l)
    rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_sum,
      Finset.sum_eq_single lam hother (fun hmem => absurd (Finset.mem_univ lam) hmem)] at h
    rwa [hterm] at h
  refine absurd ?_ hp
  funext lm
  obtain ⟨j, l, lam⟩ := lm
  exact RingHom.injective φ (by rw [Pi.zero_apply, map_zero]; exact hcoeff j l lam)

end Work.BW
