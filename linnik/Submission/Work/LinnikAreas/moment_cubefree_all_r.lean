import Mathlib
import Submission.Work.LinnikAreas.CorrAllR.Defs
import Submission.Work.LinnikAreas.charCorrelation_allR_cubefree
import Submission.Work.LinnikAreas.nosingleton_value_count
import Submission.Work.LinnikAreas.CorrAllR.sum_Ww_eq_pow
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_moment_cubefree_r3
import Submission.Commons.NumberTheory.Divisors.sum_gcd_le_of_pos
import Submission.Work.LinnikAreas.CorrAllR.final_arith
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_moment_squarefree_r2

/-!
# The `2r`-th moment of Dirichlet character sums over intervals, cube-free moduli

This file assembles the proof of `Work.LinnikAreas.moment_cubefree_all_r` (Heath-Brown,
Burgess's Bounds for Character Sums, arXiv:1203.5219, Lemma 2 (ii) under condition (i)):

for `r ≥ 1`, `ε > 0` there is `C > 0` such that for every cube-free `q`, every primitive
non-trivial Dirichlet character `χ` mod `q`, and every `H ≤ q`,

`∑_{m < q} ‖∑_{h ∈ (m, m+H]} χ h‖ ^ (2r) ≤ C q^ε (q H^r + H^(2r) √q)`.

The expansion of the `2r`-th power (`sum_norm_eq_norm_sum`, `Z_eq'`) writes the left side as the
norm of a double sum of correlation sums.  Each correlation (indexed by a pair `(f, g)` of tuples
of summation indices) is either bounded by the global cube-free correlation bound
`charCorrelation_allR_cubefree` (when the corresponding combined shift tuple has a unique entry),
with `gcd`-weights summed by `CorrAllR.sum_Ww_eq_pow` and `gcd_shift_sum_le_local`, or bounded
trivially by `q` (and the pairs of the latter kind are counted by `nosingleton_value_count`).
The final arithmetic is `CorrAllR.final_arith`.
-/

open Finset
open scoped BigOperators

namespace Work.LinnikAreas

open Commons.NumberTheory.DirichletCharacter

noncomputable section

/-- `Tgq H r χ f g` in the `corrSumV` normal form. -/
lemma Tgq_eq_corrSumV {q : ℕ} [NeZero q] (H r : ℕ) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (f g : Fin r → Fin H) :
    Tgq H r χ f g
      = corrSumV q χ r (combShift (fun l => (f l : ℕ) + 1) (fun l => (g l : ℕ) + 1)) := by
  have hm2 : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  simp only [Tgq, corrSumV, combShift_castAdd, combShift_natAdd]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_pow, map_mul, map_pow]
  congr 1
  · simp only [Pf, Polynomial.eval_prod, map_prod, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
  · rw [chi_conj_eq_pow_pred χ hm2 (∏ l : Fin r, (x + (((g l : ℕ) + 1 : ℕ) : ZMod q)))]
    simp only [Pf, Polynomial.eval_prod, map_prod, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]

/-- `Tgq` for the pair reindexed as a single tuple `w`, in the `corrSumV` normal form. -/
lemma Tgq_eq_corrSumV_pairVecH {q : ℕ} [NeZero q] (H r : ℕ) (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (w : Fin (r + r) → Fin H) :
    Tgq H r χ ((pairEquivR H r).symm w).1 ((pairEquivR H r).symm w).2
      = corrSumV q χ r (pairVecH w) := by
  rw [Tgq_eq_corrSumV H r χ hχ]
  congr 1
  funext i
  refine Fin.addCases (motive := fun i =>
    combShift (fun l : Fin r => (((pairEquivR H r).symm w).1 l : ℕ) + 1)
      (fun l : Fin r => (((pairEquivR H r).symm w).2 l : ℕ) + 1) i = pairVecH w i)
    (fun l => ?_) (fun l => ?_) i
  · rw [combShift_castAdd, pairEquivR_symm_fst]; rfl
  · rw [combShift_natAdd, pairEquivR_symm_snd]; rfl

/-- The `gcd`-weight of a tuple, written with the differences of the *indices* (the form used by
`singleton_gcd_weight_sum`). -/
noncomputable def WwU (q : ℕ) {H r : ℕ} (w : Fin (r + r) → Fin H) (i : Fin (r + r)) : ℝ :=
  ∏ j ∈ Finset.univ.erase i,
    (if w j = w i then 0 else (Nat.gcd q (Int.natAbs ((w j : ℤ) - (w i : ℤ))) : ℝ))

lemma WwU_eq_Ww (q : ℕ) {H r : ℕ} (w : Fin (r + r) → Fin H) (i : Fin (r + r)) :
    WwU q w i = Ww q w i := by
  refine Finset.prod_congr rfl (fun j _ => ?_)
  by_cases h : w j = w i
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    have e : ((pairVecH w j : ℤ) - (pairVecH w i : ℤ)) = ((w j : ℤ) - (w i : ℤ)) := by
      simp only [pairVecH]; push_cast; ring
    rw [e]

lemma gcdWeightV_pairVecH_eq_WwU (q : ℕ) {H r : ℕ} (w : Fin (r + r) → Fin H) (i : Fin (r + r))
    (huniq : ∀ j : Fin (r + r), j ≠ i → w j ≠ w i) :
    gcdWeightV q (pairVecH w) i = WwU q w i := by
  refine Finset.prod_congr rfl (fun j hj => ?_)
  have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
  have hne : w j ≠ w i := huniq j hjne
  rw [if_neg hne]
  have e : Int.natAbs ((pairVecH w i : ℤ) - (pairVecH w j : ℤ))
      = Int.natAbs ((w j : ℤ) - (w i : ℤ)) := by
    have e2 : ((pairVecH w i : ℤ) - (pairVecH w j : ℤ)) = -((w j : ℤ) - (w i : ℤ)) := by
      simp only [pairVecH]; push_cast; ring
    rw [e2, Int.natAbs_neg]
  rw [e]

/-- The `¬ WHasUniqIdx` filter, in the syntactically identical form used by
`nosingleton_value_count`. -/
lemma uniq_filter_eq (H r : ℕ) :
    (Finset.univ.filter (fun w : Fin (r + r) → Fin H => ¬ WHasUniqIdx w))
      = (Finset.univ.filter (fun w : Fin (r + r) → Fin H =>
          ¬ ∃ i : Fin (r + r), ∀ j : Fin (r + r), j ≠ i → w j ≠ w i)) := by
  apply Finset.filter_congr
  intro w _
  simp only [WHasUniqIdx]

/-- The single-coordinate `gcd`-weight sum: `∑_v (v = u ? 0 : gcd (q, |u - v|)) ≤ 2 H d(q)`. -/
lemma gcd_shift_sum_le_local (q H : ℕ) (hq : q ≠ 0) (u : Fin H) :
    (∑ v : Fin H, (if v = u then 0 else (Nat.gcd q (((u : ℤ) - (v : ℤ)).natAbs) : ℝ)))
      ≤ 2 * (H : ℝ) * ((q.divisors.card : ℕ) : ℝ) := by
  refine (Commons.NumberTheory.DirichletCharacter.r3_gcd_shift_sum_le (q := q) u).trans ?_
  have h := Commons.NumberTheory.Divisors.sum_gcd_le_of_pos H q (Nat.pos_of_ne_zero hq)
  have h2 : (∑ c ∈ Finset.Icc 1 H, (Nat.gcd q c : ℝ))
      ≤ (H : ℝ) * ((q.divisors.card : ℕ) : ℝ) := by
    have hswap : (∑ c ∈ Finset.Icc 1 H, Nat.gcd q c)
        = ∑ c ∈ Finset.Icc 1 H, Nat.gcd c q := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Nat.gcd_comm]
    rw [← hswap] at h
    exact_mod_cast h
  linarith

/-- The `gcd`-weight sum bound for a fixed index `i`. -/
lemma sum_Ww_le_local (q : ℕ) (hq : q ≠ 0) {H r : ℕ} (hr : 0 < r) (i : Fin (r + r)) :
    (∑ w : Fin (r + r) → Fin H, Ww q w i)
      ≤ 2 ^ (2 * r - 1) * (H : ℝ) ^ (2 * r)
          * ((q.divisors.card : ℕ) : ℝ) ^ (2 * r - 1) := by
  rw [CorrAllR.sum_Ww_eq_pow q hr i]
  have hterm : ∀ u : Fin H,
      (∑ v : Fin H, (if u = v then 0 else (Nat.gcd q (((u : ℤ) - (v : ℤ)).natAbs) : ℝ)))
        ≤ 2 * (H : ℝ) * ((q.divisors.card : ℕ) : ℝ) := by
    intro u
    have heq : (∑ v : Fin H, (if u = v then 0
          else (Nat.gcd q (((u : ℤ) - (v : ℤ)).natAbs) : ℝ)))
        = ∑ v : Fin H, (if v = u then 0
          else (Nat.gcd q (((u : ℤ) - (v : ℤ)).natAbs) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : u = v
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
    rw [heq]
    exact gcd_shift_sum_le_local q H hq u
  calc (∑ u : Fin H,
        (∑ v : Fin H, (if u = v then 0 else (Nat.gcd q (((u : ℤ) - (v : ℤ)).natAbs) : ℝ)))
          ^ (2 * r - 1))
      ≤ ∑ u : Fin H, (2 * (H : ℝ) * ((q.divisors.card : ℕ) : ℝ)) ^ (2 * r - 1) := by
        apply Finset.sum_le_sum
        intro u _
        apply pow_le_pow_left₀ _ (hterm u)
        exact Finset.sum_nonneg (fun v _ => by
          by_cases h : u = v
          · rw [if_pos h]
          · rw [if_neg h]; positivity)
    _ = (H : ℝ) * (2 * (H : ℝ) * ((q.divisors.card : ℕ) : ℝ)) ^ (2 * r - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = 2 ^ (2 * r - 1) * (H : ℝ) ^ (2 * r)
          * ((q.divisors.card : ℕ) : ℝ) ^ (2 * r - 1) := by
        set D : ℝ := ((q.divisors.card : ℕ) : ℝ) with hD
        have hk : 2 * r - 1 + 1 = 2 * r := by omega
        calc (H : ℝ) * (2 * (H : ℝ) * D) ^ (2 * r - 1)
            = (H : ℝ) * (2 ^ (2 * r - 1) * (H : ℝ) ^ (2 * r - 1) * D ^ (2 * r - 1)) := by
              rw [mul_pow, mul_pow]
          _ = ((H : ℝ) ^ (2 * r - 1) * (H : ℝ)) * (2 ^ (2 * r - 1) * D ^ (2 * r - 1)) := by
              ring
          _ = (H : ℝ) ^ (2 * r) * (2 ^ (2 * r - 1) * D ^ (2 * r - 1)) := by
              rw [← pow_succ, hk]
          _ = 2 ^ (2 * r - 1) * (H : ℝ) ^ (2 * r) * D ^ (2 * r - 1) := by
              ring

/-- The combined `gcd`-weight sum over all tuples, summed over the `2r` possible unique indices. -/
lemma sum_Ww_le_two_r (r : ℕ) (hr : 1 ≤ r) {q H : ℕ} (hq : q ≠ 0) :
    (∑ i : Fin (r + r), ∑ w : Fin (r + r) → Fin H, Ww q w i)
      ≤ (2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1) * (H : ℝ) ^ (2 * r)
          * ((q.divisors.card : ℕ) : ℝ) ^ (2 * r - 1) := by
  have hterm : ∀ i : Fin (r + r),
      (∑ w : Fin (r + r) → Fin H, Ww q w i)
        ≤ (2 : ℝ) ^ (2 * r - 1) * (H : ℝ) ^ (2 * r)
            * ((q.divisors.card : ℕ) : ℝ) ^ (2 * r - 1) := by
    intro i
    exact sum_Ww_le_local q hq hr i
  calc (∑ i : Fin (r + r), ∑ w : Fin (r + r) → Fin H, Ww q w i)
      ≤ ∑ _i : Fin (r + r), (2 : ℝ) ^ (2 * r - 1) * (H : ℝ) ^ (2 * r)
            * ((q.divisors.card : ℕ) : ℝ) ^ (2 * r - 1) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = (2 * r : ℝ) * ((2 : ℝ) ^ (2 * r - 1) * (H : ℝ) ^ (2 * r)
            * ((q.divisors.card : ℕ) : ℝ) ^ (2 * r - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ = (2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1) * (H : ℝ) ^ (2 * r)
          * ((q.divisors.card : ℕ) : ℝ) ^ (2 * r - 1) := by ring

/-- **The `2r`-th moment bound for cube-free moduli** (Heath-Brown, Lemma 2 (ii), condition (i)). -/
theorem moment_cubefree_all_r (r : ℕ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ q) →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ H : ℕ, H ≤ q →
        ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)‖ ^ (2 * r)
          ≤ C * (q : ℝ) ^ ε *
              ((q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ)) := by
  have hr1 : 1 ≤ r := hr
  obtain ⟨C₀, hC₀pos, harith⟩ := CorrAllR.final_arith r hr ε hε
  refine ⟨C₀, hC₀pos, ?_⟩
  intro q _inst hcube χ hprim hne H _hH
  have hq0 : q ≠ 0 := NeZero.ne q
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  set B : ℝ := (2 * r : ℝ) ^ q.primeFactors.card * Real.sqrt (q : ℝ) with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hexp : (∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)‖ ^ (2 * r))
      = ‖∑ f : Fin r → Fin H, ∑ g : Fin r → Fin H, Tgq H r χ f g‖ := by
    rw [sum_norm_eq_norm_sum (p := q)
      (S := fun m => ∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)) r, Z_eq' H r χ hne]
  rw [hexp]
  have hpair : ∀ w : Fin (r + r) → Fin H,
      ‖Tgq H r χ ((pairEquivR H r).symm w).1 ((pairEquivR H r).symm w).2‖
        ≤ (if WHasUniqIdx w then B * (∑ i : Fin (r + r),
            (if ∀ j : Fin (r + r), j ≠ i → w j ≠ w i then Ww q w i else 0))
          else (q : ℝ)) := by
    intro w
    rw [Tgq_eq_corrSumV_pairVecH H r χ hne w]
    by_cases hun : WHasUniqIdx w
    · rw [if_pos hun]
      obtain ⟨i0, hi0⟩ := hun
      have huniqV : ∀ j : Fin (r + r), j ≠ i0 → pairVecH w j ≠ pairVecH w i0 :=
        fun j hj hcon => hi0 j hj ((pairVecH_eq_iff w j i0).mp hcon)
      have h1 : ‖corrSumV q χ r (pairVecH w)‖ ≤ B * Ww q w i0 := by
        have h := corrSumV_bound r hr1 q hcube χ hprim hne (pairVecH w) i0 huniqV
        rw [gcdWeightV_pairVecH_eq_WwU q w i0 hi0, WwU_eq_Ww q w i0] at h
        exact h
      have h2 : Ww q w i0
          ≤ ∑ i : Fin (r + r),
              (if ∀ j : Fin (r + r), j ≠ i → w j ≠ w i then Ww q w i else 0) := by
        have hnn : ∀ i : Fin (r + r),
            0 ≤ (if ∀ j : Fin (r + r), j ≠ i → w j ≠ w i then Ww q w i else 0) := by
          intro i
          by_cases h : ∀ j : Fin (r + r), j ≠ i → w j ≠ w i
          · rw [if_pos h]; exact Ww_nonneg q w i
          · rw [if_neg h]
        calc Ww q w i0
            = (if ∀ j : Fin (r + r), j ≠ i0 → w j ≠ w i0 then Ww q w i0 else 0) := by
              rw [if_pos hi0]
          _ ≤ _ := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ i0)
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hBnn)
    · rw [if_neg hun]
      exact corrSumV_norm_le_card q χ r (pairVecH w)
  have htri : ‖∑ f : Fin r → Fin H, ∑ g : Fin r → Fin H, Tgq H r χ f g‖
      ≤ ∑ w : Fin (r + r) → Fin H,
          ‖Tgq H r χ ((pairEquivR H r).symm w).1 ((pairEquivR H r).symm w).2‖ := by
    calc ‖∑ f : Fin r → Fin H, ∑ g : Fin r → Fin H, Tgq H r χ f g‖
        ≤ ∑ f : Fin r → Fin H, ‖∑ g : Fin r → Fin H, Tgq H r χ f g‖ := norm_sum_le _ _
      _ ≤ ∑ f : Fin r → Fin H, ∑ g : Fin r → Fin H, ‖Tgq H r χ f g‖ :=
          Finset.sum_le_sum (fun f _ => norm_sum_le _ _)
      _ = ∑ p : (Fin r → Fin H) × (Fin r → Fin H), ‖Tgq H r χ p.1 p.2‖ :=
          (Fintype.sum_prod_type (f := fun p : (Fin r → Fin H) × (Fin r → Fin H) =>
            ‖Tgq H r χ p.1 p.2‖)).symm
      _ = ∑ w : Fin (r + r) → Fin H,
            ‖Tgq H r χ ((pairEquivR H r).symm w).1 ((pairEquivR H r).symm w).2‖ :=
          Fintype.sum_equiv (pairEquivR H r)
            (fun p : (Fin r → Fin H) × (Fin r → Fin H) => ‖Tgq H r χ p.1 p.2‖)
            (fun w : Fin (r + r) → Fin H =>
              ‖Tgq H r χ ((pairEquivR H r).symm w).1 ((pairEquivR H r).symm w).2‖)
            (fun p => by simp only [Equiv.symm_apply_apply])
  refine htri.trans ((Finset.sum_le_sum (fun w _ => hpair w)).trans ?_)
  -- decompose the `if` into two sums
  have hsum_eq : (∑ w : Fin (r + r) → Fin H,
        (if WHasUniqIdx w then B * (∑ i : Fin (r + r),
            (if ∀ j : Fin (r + r), j ≠ i → w j ≠ w i then Ww q w i else 0))
          else (q : ℝ)))
      = (∑ w : Fin (r + r) → Fin H,
          (if WHasUniqIdx w then B * (∑ i : Fin (r + r),
            (if ∀ j : Fin (r + r), j ≠ i → w j ≠ w i then Ww q w i else 0)) else 0))
        + (∑ w : Fin (r + r) → Fin H, (if WHasUniqIdx w then 0 else (q : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    by_cases h : WHasUniqIdx w <;> simp [h]
  rw [hsum_eq]
  -- the part carried by the tuples with a unique entry
  have hU : (∑ w : Fin (r + r) → Fin H,
        (if WHasUniqIdx w then B * (∑ i : Fin (r + r),
            (if ∀ j : Fin (r + r), j ≠ i → w j ≠ w i then Ww q w i else 0)) else 0))
      ≤ B * ((2 * r : ℝ) * (2 : ℝ) ^ (2 * r - 1) * (H : ℝ) ^ (2 * r)
          * ((q.divisors.card : ℕ) : ℝ) ^ (2 * r - 1)) := by
    have hstep1 : (∑ w : Fin (r + r) → Fin H,
          (if WHasUniqIdx w then B * (∑ i : Fin (r + r),
            (if ∀ j : Fin (r + r), j ≠ i → w j ≠ w i then Ww q w i else 0)) else 0))
        ≤ ∑ w : Fin (r + r) → Fin H, B * (∑ i : Fin (r + r),
            (if ∀ j : Fin (r + r), j ≠ i → w j ≠ w i then Ww q w i else 0)) := by
      apply Finset.sum_le_sum
      intro w _
      by_cases h : WHasUniqIdx w
      · rw [if_pos h]
      · rw [if_neg h]
        exact mul_nonneg hBnn (Finset.sum_nonneg (fun i _ => by
          by_cases h2 : ∀ j : Fin (r + r), j ≠ i → w j ≠ w i
          · rw [if_pos h2]; exact Ww_nonneg q w i
          · rw [if_neg h2]))
    refine hstep1.trans ?_
    have hstep2 : (∑ w : Fin (r + r) → Fin H, B * (∑ i : Fin (r + r),
          (if ∀ j : Fin (r + r), j ≠ i → w j ≠ w i then Ww q w i else 0)))
        ≤ B * ∑ i : Fin (r + r), ∑ w : Fin (r + r) → Fin H, Ww q w i := by
      have h2a : (∑ w : Fin (r + r) → Fin H, B * (∑ i : Fin (r + r),
            (if ∀ j : Fin (r + r), j ≠ i → w j ≠ w i then Ww q w i else 0)))
          ≤ ∑ w : Fin (r + r) → Fin H, B * (∑ i : Fin (r + r), Ww q w i) := by
        apply Finset.sum_le_sum
        intro w _
        apply mul_le_mul_of_nonneg_left _ hBnn
        apply Finset.sum_le_sum
        intro i _
        by_cases h : ∀ j : Fin (r + r), j ≠ i → w j ≠ w i
        · rw [if_pos h]
        · rw [if_neg h]; exact Ww_nonneg q w i
      have h2b : (∑ w : Fin (r + r) → Fin H, B * (∑ i : Fin (r + r), Ww q w i))
          = B * ∑ w : Fin (r + r) → Fin H, ∑ i : Fin (r + r), Ww q w i := by
        rw [Finset.mul_sum]
      refine h2a.trans ?_
      rw [h2b, Finset.sum_comm]
    refine hstep2.trans ?_
    exact mul_le_mul_of_nonneg_left (sum_Ww_le_two_r r hr1 hq0) hBnn
  -- the part carried by the tuples with no unique entry
  have hV : (∑ w : Fin (r + r) → Fin H, (if WHasUniqIdx w then 0 else (q : ℝ)))
      ≤ (q : ℝ) * ((2 * r : ℝ) ^ (2 * r) * (H : ℝ) ^ r) := by
    have hfilter : (∑ w : Fin (r + r) → Fin H, (if WHasUniqIdx w then 0 else (q : ℝ)))
        = (q : ℝ) * (((Finset.univ.filter (fun w : Fin (r + r) → Fin H =>
            ¬ WHasUniqIdx w)).card : ℕ) : ℝ) := by
      have hcongr : (∑ w : Fin (r + r) → Fin H, (if WHasUniqIdx w then 0 else (q : ℝ)))
          = ∑ w : Fin (r + r) → Fin H, (if ¬ WHasUniqIdx w then (q : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases h : WHasUniqIdx w <;> simp [h]
      rw [hcongr, ← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hfilter]
    have hcount := nosingleton_value_count r hr1 H
    rw [← uniq_filter_eq] at hcount
    have hcast : (((Finset.univ.filter (fun w : Fin (r + r) → Fin H =>
        ¬ WHasUniqIdx w)).card : ℕ) : ℝ) ≤ ((2 * r) ^ (2 * r) * H ^ r : ℕ) := by
      exact_mod_cast hcount
    have hcast' : ((((2 * r) ^ (2 * r) * H ^ r : ℕ)) : ℝ)
        = (2 * r : ℝ) ^ (2 * r) * (H : ℝ) ^ r := by push_cast; ring
    rw [hcast'] at hcast
    exact mul_le_mul_of_nonneg_left hcast (Nat.cast_nonneg q)
  refine (add_le_add hU hV).trans ?_
  rw [hBdef]
  refine le_trans (le_of_eq ?_) (harith q H (Nat.one_le_iff_ne_zero.mpr hq0))
  ring

end

end Work.LinnikAreas
