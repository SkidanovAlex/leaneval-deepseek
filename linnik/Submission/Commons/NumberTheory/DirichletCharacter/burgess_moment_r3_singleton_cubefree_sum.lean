import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_moment_squarefree_r2
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_cubefree_global
import Submission.Commons.NumberTheory.Divisors.sum_gcd_le_of_pos
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Commons.NumberTheory.DirichletSeries.omega_euler_product
import Submission.Commons.Combinatorics.Counting.sum_fun_prod_erase_eq

open Finset
open scoped BigOperators
namespace Commons.NumberTheory.DirichletCharacter

/-! ## Auxiliary gcd-weight bounds

These are the elementary estimates controlling `∑_{d ≤ H} gcd(q,d) ≤ H · τ(q)` and its
consequences for the weighted sum over the six shift coordinates. -/

lemma bmr3sc_gcd_sum_lt_le {q H : ℕ} (u : Fin H) :
    (∑ v ∈ (Finset.univ.filter (fun v : Fin H => v < u)),
        (Nat.gcd q (((u:ℤ)-(v:ℤ)).natAbs) : ℝ))
      ≤ ∑ c ∈ Finset.Icc 1 H, (Nat.gcd q c : ℝ) := by
  set s := Finset.univ.filter (fun v : Fin H => v < u) with hs
  have hstep : (∑ v ∈ s, (Nat.gcd q (((u:ℤ)-(v:ℤ)).natAbs) : ℝ))
      = ∑ v ∈ s, (Nat.gcd q (u.val - v.val) : ℝ) := by
    apply Finset.sum_congr rfl
    intro v hv
    have hv' : v.val < u.val := by
      have : v < u := by simpa [hs] using hv
      exact this
    have hcast : ((u:ℤ) - (v:ℤ)) = ((u.val - v.val : ℕ) : ℤ) := by
      have : (v.val : ℤ) ≤ (u.val : ℤ) := by exact_mod_cast le_of_lt hv'
      push_cast
      omega
    rw [hcast, Int.natAbs_natCast]
  rw [hstep]
  calc ∑ v ∈ s, (Nat.gcd q (u.val - v.val) : ℝ)
      = ∑ c ∈ Finset.Icc 1 u.val, (Nat.gcd q c : ℝ) := by
        refine Finset.sum_bij (fun v _ => u.val - v.val) ?_ ?_ ?_ ?_
        · intro v hv
          have hv' : v.val < u.val := by
            have : v < u := by simpa [hs] using hv
            exact this
          rw [Finset.mem_Icc]
          omega
        · intro v1 hv1 v2 hv2 heq
          have h1 : v1.val < u.val := by
            have : v1 < u := by simpa [hs] using hv1
            exact this
          have h2 : v2.val < u.val := by
            have : v2 < u := by simpa [hs] using hv2
            exact this
          have e1 : v1.val = u.val - (u.val - v1.val) := (Nat.sub_sub_self (le_of_lt h1)).symm
          have e2 : v2.val = u.val - (u.val - v2.val) := (Nat.sub_sub_self (le_of_lt h2)).symm
          have : v1.val = v2.val := by rw [e1, e2, heq]
          exact Fin.ext this
        · intro b hb
          rw [Finset.mem_Icc] at hb
          refine ⟨⟨u.val - b, by omega⟩, ?_, ?_⟩
          · simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
            omega
          · simp only [Fin.val_mk]
            omega
        · intro v hv
          rfl
    _ ≤ ∑ c ∈ Finset.Icc 1 H, (Nat.gcd q c : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc_right (le_of_lt u.isLt))
          (fun c _ _ => by positivity)

lemma bmr3sc_gcd_sum_gt_le {q H : ℕ} (u : Fin H) :
    (∑ v ∈ (Finset.univ.filter (fun v : Fin H => u < v)),
        (Nat.gcd q (((u:ℤ)-(v:ℤ)).natAbs) : ℝ))
      ≤ ∑ c ∈ Finset.Icc 1 H, (Nat.gcd q c : ℝ) := by
  set s := Finset.univ.filter (fun v : Fin H => u < v) with hs
  have hstep : (∑ v ∈ s, (Nat.gcd q (((u:ℤ)-(v:ℤ)).natAbs) : ℝ))
      = ∑ v ∈ s, (Nat.gcd q (v.val - u.val) : ℝ) := by
    apply Finset.sum_congr rfl
    intro v hv
    have hv' : u.val < v.val := by
      have : u < v := by simpa [hs] using hv
      exact this
    have hcast : ((u:ℤ) - (v:ℤ)) = (- ((v.val - u.val : ℕ) : ℤ)) := by
      have : (u.val : ℤ) ≤ (v.val : ℤ) := by exact_mod_cast le_of_lt hv'
      push_cast
      omega
    rw [hcast, Int.natAbs_neg, Int.natAbs_natCast]
  rw [hstep]
  calc ∑ v ∈ s, (Nat.gcd q (v.val - u.val) : ℝ)
      = ∑ c ∈ Finset.Icc 1 (H - 1 - u.val), (Nat.gcd q c : ℝ) := by
        refine Finset.sum_bij (fun v _ => v.val - u.val) ?_ ?_ ?_ ?_
        · intro v hv
          have hv' : u.val < v.val := by
            have : u < v := by simpa [hs] using hv
            exact this
          rw [Finset.mem_Icc]
          have := v.isLt
          omega
        · intro v1 hv1 v2 hv2 heq
          have h1 : u.val < v1.val := by
            have : u < v1 := by simpa [hs] using hv1
            exact this
          have h2 : u.val < v2.val := by
            have : u < v2 := by simpa [hs] using hv2
            exact this
          have : v1.val = v2.val := by omega
          exact Fin.ext this
        · intro b hb
          rw [Finset.mem_Icc] at hb
          refine ⟨⟨b + u.val, by omega⟩, ?_, ?_⟩
          · simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
            omega
          · simp only [Fin.val_mk]
            omega
        · intro v hv
          rfl
    _ ≤ ∑ c ∈ Finset.Icc 1 H, (Nat.gcd q c : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc_right (by omega))
          (fun c _ _ => by positivity)

lemma bmr3sc_gcd_shift_sum_le {q H : ℕ} (u : Fin H) :
    (∑ v : Fin H, (if v = u then 0 else (Nat.gcd q (((u:ℤ)-(v:ℤ)).natAbs) : ℝ)))
      ≤ 2 * ∑ c ∈ Finset.Icc 1 H, (Nat.gcd q c : ℝ) := by
  have h1 : (∑ v : Fin H, (if v = u then 0 else (Nat.gcd q (((u:ℤ)-(v:ℤ)).natAbs) : ℝ)))
      = ∑ v ∈ Finset.univ.filter (fun v : Fin H => v ≠ u),
          (Nat.gcd q (((u:ℤ)-(v:ℤ)).natAbs) : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v = u
    · subst hv; simp
    · simp [hv]
  have hsplit : Finset.univ.filter (fun v : Fin H => v ≠ u)
      = Finset.univ.filter (fun v : Fin H => v < u)
        ∪ Finset.univ.filter (fun v : Fin H => u < v) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hv; exact lt_or_gt_of_ne hv
    · rintro (h | h)
      · exact ne_of_lt h
      · exact ne_of_gt h
  have hdisj : Disjoint (Finset.univ.filter (fun v : Fin H => v < u))
      (Finset.univ.filter (fun v : Fin H => u < v)) := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
    omega
  rw [h1, hsplit, Finset.sum_union hdisj]
  have a := bmr3sc_gcd_sum_lt_le (q := q) u
  have b := bmr3sc_gcd_sum_gt_le (q := q) u
  linarith

theorem bmr3sc_sum_prod_gcd_diff_le {q H : ℕ} (hq : q ≠ 0) (i : Fin 6) :
    (∑ w : Fin 6 → Fin H, ∏ j ∈ Finset.univ.erase i,
        (if w j = w i then 0 else (Nat.gcd q (((w j : ℤ) - (w i : ℤ)).natAbs) : ℝ)))
      ≤ 32 * (H : ℝ) ^ 6 * ((q.divisors.card : ℕ) : ℝ) ^ 5 := by
  set hk : Fin H → Fin H → ℝ :=
    fun u v => if u = v then 0 else (Nat.gcd q (((u:ℤ)-(v:ℤ)).natAbs) : ℝ) with hkdef
  have hknn : ∀ u v : Fin H, 0 ≤ hk u v := by
    intro u v
    by_cases h : u = v
    · simp [hkdef, h]
    · simp only [hkdef, if_neg h]; positivity
  have hcongr : (∑ w : Fin 6 → Fin H, ∏ j ∈ Finset.univ.erase i,
        (if w j = w i then 0 else (Nat.gcd q (((w j : ℤ) - (w i : ℤ)).natAbs) : ℝ)))
      = ∑ w : Fin 6 → Fin H, ∏ j ∈ Finset.univ.erase i, hk (w i) (w j) := by
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.prod_congr rfl
    intro j _
    simp only [hkdef]
    by_cases h : w j = w i
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
      rw [show ((w i : ℤ) - (w j : ℤ)) = -(((w j : ℤ) - (w i : ℤ))) by ring, Int.natAbs_neg]
  rw [hcongr]
  have hfac := Commons.Combinatorics.Counting.sum_fun_prod_erase_eq (ι := Fin 6) (α := Fin H) i hk
  rw [hfac]
  have hcard : Fintype.card (Fin 6) - 1 = 5 := by simp
  rw [hcard]
  have hstep : ∀ u : Fin H, (∑ v : Fin H, hk u v) ≤ 2 * (H:ℝ) * ((q.divisors.card : ℕ) : ℝ) := by
    intro u
    have h1 := bmr3sc_gcd_shift_sum_le (q := q) u
    have h1' : (∑ v : Fin H, hk u v)
        ≤ 2 * ∑ c ∈ Finset.Icc 1 H, (Nat.gcd q c : ℝ) := by
      simp only [hkdef]
      calc (∑ v : Fin H, (if u = v then 0 else (Nat.gcd q (((u:ℤ)-(v:ℤ)).natAbs) : ℝ)))
          = ∑ v : Fin H, (if v = u then 0 else (Nat.gcd q (((u:ℤ)-(v:ℤ)).natAbs) : ℝ)) := by
            apply Finset.sum_congr rfl; intro v _
            by_cases h : u = v
            · rw [if_pos h, if_pos h.symm]
            · rw [if_neg h, if_neg (Ne.symm h)]
        _ ≤ _ := h1
    have h2 : (∑ c ∈ Finset.Icc 1 H, (Nat.gcd q c : ℝ))
        ≤ (H:ℝ) * ((q.divisors.card : ℕ) : ℝ) := by
      have hthis := Commons.NumberTheory.Divisors.sum_gcd_le_of_pos H q (Nat.pos_of_ne_zero hq)
      have hswap : (∑ c ∈ Finset.Icc 1 H, Nat.gcd q c) = ∑ c ∈ Finset.Icc 1 H, Nat.gcd c q := by
        apply Finset.sum_congr rfl; intro c _; rw [Nat.gcd_comm]
      rw [← hswap] at hthis
      have hcast : ((∑ c ∈ Finset.Icc 1 H, Nat.gcd q c : ℕ) : ℝ)
          = ∑ c ∈ Finset.Icc 1 H, (Nat.gcd q c : ℝ) := Nat.cast_sum _ _
      rw [← hcast]
      exact_mod_cast hthis
    calc (∑ v : Fin H, hk u v)
        ≤ 2 * ∑ c ∈ Finset.Icc 1 H, (Nat.gcd q c : ℝ) := h1'
      _ ≤ 2 * ((H:ℝ) * ((q.divisors.card : ℕ) : ℝ)) := by
            apply mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 2 * (H:ℝ) * ((q.divisors.card : ℕ) : ℝ) := by ring
  calc (∑ u : Fin H, (∑ v : Fin H, hk u v) ^ 5)
      ≤ ∑ u : Fin H, (2 * (H:ℝ) * ((q.divisors.card : ℕ) : ℝ)) ^ 5 :=
        Finset.sum_le_sum (fun u _ => pow_le_pow_left₀ (Finset.sum_nonneg (fun v _ => hknn u v)) (hstep u) 5)
    _ = (H:ℝ) * (2 * (H:ℝ) * ((q.divisors.card : ℕ) : ℝ)) ^ 5 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = 32 * (H:ℝ) ^ 6 * ((q.divisors.card : ℕ) : ℝ) ^ 5 := by ring

/-! ## The six-shift vector and the reindexing equivalence -/

noncomputable def bmr3sc_v6 {H : ℕ} (f g : Fin 3 → Fin H) : Fin 6 → ℕ :=
  ![((f 0 : ℕ) + 1), ((f 1 : ℕ) + 1), ((f 2 : ℕ) + 1),
    ((g 0 : ℕ) + 1), ((g 1 : ℕ) + 1), ((g 2 : ℕ) + 1)]

noncomputable def bmr3sc_pairEquiv (H : ℕ) :
    ((Fin 3 → Fin H) × (Fin 3 → Fin H)) ≃ (Fin 6 → Fin H) where
  toFun p := ![p.1 0, p.1 1, p.1 2, p.2 0, p.2 1, p.2 2]
  invFun w := (fun l : Fin 3 => w ⟨l.val, by omega⟩, fun l : Fin 3 => w ⟨l.val + 3, by omega⟩)
  left_inv p := by
    obtain ⟨f, g⟩ := p
    refine Prod.ext ?_ ?_ <;> funext l <;> fin_cases l <;> rfl
  right_inv w := by
    funext k
    fin_cases k <;> rfl

lemma bmr3sc_v6_eq_pairEquiv {H : ℕ} (f g : Fin 3 → Fin H) (i : Fin 6) :
    bmr3sc_v6 f g i = ((bmr3sc_pairEquiv H (f, g)) i : ℕ) + 1 := by
  fin_cases i <;> rfl

/-! ## `Tgq` as a cubic character correlation -/

lemma bmr3sc_Pf_eval_prod {q H : ℕ} [NeZero q] (f : Fin 3 → Fin H) (x : ZMod q) :
    (Pf q H 3 f).eval x = ∏ l : Fin 3, (x + (((f l : ℕ) + 1 : ℕ) : ZMod q)) := by
  rw [Pf, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro l _
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

lemma bmr3sc_Tgq_three_eq_corr {q : ℕ} [NeZero q] (H : ℕ) (χ : DirichletCharacter ℂ q)
    (hm : 2 ≤ orderOf χ) (f g : Fin 3 → Fin H) :
    Tgq H 3 χ f g
      = ∑ x : ZMod q,
          χ (∏ l : Fin 3, (x + (((f l : ℕ) + 1 : ℕ) : ZMod q)))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (((g l : ℕ) + 1 : ℕ) : ZMod q)))) := by
  unfold Tgq
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hmul : χ ((Pf q H 3 f * (Pf q H 3 g) ^ (orderOf χ - 1)).eval x)
      = χ ((Pf q H 3 f).eval x) * (χ ((Pf q H 3 g).eval x)) ^ (orderOf χ - 1) := by
    rw [Polynomial.eval_mul, Polynomial.eval_pow, map_mul, map_pow]
  rw [hmul, bmr3sc_Pf_eval_prod f x, bmr3sc_Pf_eval_prod g x, ← chi_conj_eq_pow_pred χ hm]

lemma bmr3sc_orderOf_two_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    2 ≤ orderOf χ := by
  have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
  have h2 : 1 ≤ orderOf χ := orderOf_pos χ
  omega

/-- Per-pair bound for a pair `(f,g)` of triples whose `i`-th shift is unique:
`‖Tgq‖ ≤ 6^{ω(q)} √q ∏_{j ≠ i} gcd(q, |v_i - v_j|)`. -/
lemma bmr3sc_norm_Tgq_three_singleton_le {q : ℕ} [NeZero q]
    (hcube : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1)
    (H : ℕ) (f g : Fin 3 → Fin H) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → bmr3sc_v6 f g i ≠ bmr3sc_v6 f g j) :
    ‖Tgq H 3 χ f g‖ ≤ (6 : ℝ) ^ (q.primeFactors.card) * Real.sqrt (q : ℝ) *
        ∏ j ∈ Finset.univ.erase i,
          (((Nat.gcd q (((bmr3sc_v6 f g i : ℤ) - (bmr3sc_v6 f g j : ℤ)).natAbs)) : ℕ) : ℝ) := by
  have hm := bmr3sc_orderOf_two_le h1
  rw [bmr3sc_Tgq_three_eq_corr H χ hm f g]
  have key := charCorrelation6_cubefree_global (q := q) hcube χ hχ h1
      (fun l : Fin 3 => (f l : ℕ) + 1) (fun l : Fin 3 => (g l : ℕ) + 1) i
      (by
        intro j hj
        have := hi j hj
        simpa [bmr3sc_v6] using this)
  simpa [bmr3sc_v6] using key

/-! ## Singleton index, weights, and transport to the `Fin 6 → Fin H` representation -/

noncomputable def bmr3sc_UniqIdx {H : ℕ} (f g : Fin 3 → Fin H) (i : Fin 6) : Prop :=
  ∀ j : Fin 6, j ≠ i → bmr3sc_v6 f g i ≠ bmr3sc_v6 f g j

def bmr3sc_UniqW {H : ℕ} (w : Fin 6 → Fin H) (i : Fin 6) : Prop :=
  ∀ j ∈ Finset.univ.erase i, w j ≠ w i

noncomputable def bmr3sc_Wgt (q : ℕ) {H : ℕ} (f g : Fin 3 → Fin H) (i : Fin 6) : ℝ :=
  ∏ j ∈ Finset.univ.erase i,
    (((Nat.gcd q (((bmr3sc_v6 f g i : ℤ) - (bmr3sc_v6 f g j : ℤ)).natAbs)) : ℕ) : ℝ)

noncomputable def bmr3sc_Ww (q : ℕ) {H : ℕ} (w : Fin 6 → Fin H) (i : Fin 6) : ℝ :=
  ∏ j ∈ Finset.univ.erase i,
    (if w j = w i then 0 else (Nat.gcd q (((w i : ℤ) - (w j : ℤ)).natAbs) : ℝ))

lemma bmr3sc_Ww_nonneg (q : ℕ) {H : ℕ} (w : Fin 6 → Fin H) (i : Fin 6) : 0 ≤ bmr3sc_Ww q w i := by
  unfold bmr3sc_Ww
  apply Finset.prod_nonneg
  intro j _
  by_cases h : w j = w i
  · simp [h]
  · simp only [if_neg h]; positivity

lemma bmr3sc_Wgt_nonneg (q : ℕ) {H : ℕ} (f g : Fin 3 → Fin H) (i : Fin 6) :
    0 ≤ bmr3sc_Wgt q f g i := by
  unfold bmr3sc_Wgt
  apply Finset.prod_nonneg
  intro j _
  positivity

lemma bmr3sc_UniqIdx_iff {H : ℕ} (f g : Fin 3 → Fin H) (i : Fin 6) :
    bmr3sc_UniqIdx f g i ↔ bmr3sc_UniqW (bmr3sc_pairEquiv H (f, g)) i := by
  unfold bmr3sc_UniqIdx bmr3sc_UniqW
  constructor
  · intro h j hj
    have hji : j ≠ i := by
      simp only [Finset.mem_erase] at hj; exact hj.1
    intro hc
    apply h j hji
    rw [bmr3sc_v6_eq_pairEquiv f g i, bmr3sc_v6_eq_pairEquiv f g j, hc]
  · intro h j hji
    intro hc
    apply h j (by simp [Finset.mem_erase, hji])
    have h2 : ((bmr3sc_pairEquiv H (f, g)) i : ℕ) = ((bmr3sc_pairEquiv H (f, g)) j : ℕ) := by
      have h3 : ((bmr3sc_pairEquiv H (f, g)) i : ℕ) + 1
          = ((bmr3sc_pairEquiv H (f, g)) j : ℕ) + 1 := by
        rw [← bmr3sc_v6_eq_pairEquiv f g i, ← bmr3sc_v6_eq_pairEquiv f g j, hc]
      omega
    exact Fin.ext h2.symm

lemma bmr3sc_Wgt_eq_Ww_of (q : ℕ) {H : ℕ} (f g : Fin 3 → Fin H) (i : Fin 6)
    (h : bmr3sc_UniqIdx f g i) :
    bmr3sc_Wgt q f g i = bmr3sc_Ww q (bmr3sc_pairEquiv H (f, g)) i := by
  unfold bmr3sc_Wgt bmr3sc_Ww
  apply Finset.prod_congr rfl
  intro j hj
  have hne : (bmr3sc_pairEquiv H (f, g)) j ≠ (bmr3sc_pairEquiv H (f, g)) i :=
    (bmr3sc_UniqIdx_iff f g i).mp h j hj
  rw [if_neg hne]
  apply congrArg (fun z : ℕ => (Nat.gcd q z : ℝ))
  rw [show ((bmr3sc_v6 f g i : ℤ) - (bmr3sc_v6 f g j : ℤ))
        = (((bmr3sc_pairEquiv H (f, g)) i : ℤ) - ((bmr3sc_pairEquiv H (f, g)) j : ℤ)) by
      rw [bmr3sc_v6_eq_pairEquiv f g i, bmr3sc_v6_eq_pairEquiv f g j]; push_cast; ring]

lemma bmr3sc_Ww_eq_zero_of_not (q : ℕ) {H : ℕ} (f g : Fin 3 → Fin H) (i : Fin 6)
    (h : ¬ bmr3sc_UniqIdx f g i) : bmr3sc_Ww q (bmr3sc_pairEquiv H (f, g)) i = 0 := by
  unfold bmr3sc_Ww
  have h' : ¬ bmr3sc_UniqW (bmr3sc_pairEquiv H (f, g)) i :=
    fun hh => h ((bmr3sc_UniqIdx_iff f g i).mpr hh)
  unfold bmr3sc_UniqW at h'
  push_neg at h'
  obtain ⟨j0, hj0, hj0eq⟩ := h'
  exact Finset.prod_eq_zero hj0 (by rw [if_pos hj0eq])

lemma bmr3sc_Ww_eq_swap (q : ℕ) {H : ℕ} (w : Fin 6 → Fin H) (i : Fin 6) :
    bmr3sc_Ww q w i = ∏ j ∈ Finset.univ.erase i,
      (if w j = w i then 0 else (Nat.gcd q (((w j : ℤ) - (w i : ℤ)).natAbs) : ℝ)) := by
  unfold bmr3sc_Ww
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : w j = w i
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    apply congrArg (fun z : ℕ => (Nat.gcd q z : ℝ))
    rw [show ((w i : ℤ) - (w j : ℤ)) = -(((w j : ℤ) - (w i : ℤ))) by ring, Int.natAbs_neg]

/-! ## The cube-free `r = 3` singleton bound (sum of norms) -/

/-- Cube-free `r = 3` singleton bound (sum-of-norms). For every `ε > 0` there is `C` with, for every cube-free `q`, every primitive non-trivial `χ` mod `q` and every `H` with `H^6 ≤ q`:
`∑_{f,g : Fin 3 → Fin H, a value occurs exactly once among the six shifts} ‖Tgq H 3 χ f g‖ ≤ C q^ε (q H^3 + H^6 √q)`.
Use `charCorrelation6_cubefree_global` per singleton pair plus the gcd-weight summation. -/
theorem burgess_moment_r3_singleton_cubefree_sum {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ q) →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ H : ℕ, H ^ 6 ≤ q →
        ∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
          (if ∃ i : Fin 6, ∀ j : Fin 6, j ≠ i →
            ![((f 0 : ℕ) + 1), ((f 1 : ℕ) + 1), ((f 2 : ℕ) + 1),
              ((g 0 : ℕ) + 1), ((g 1 : ℕ) + 1), ((g 2 : ℕ) + 1)] i
            ≠ ![((f 0 : ℕ) + 1), ((f 1 : ℕ) + 1), ((f 2 : ℕ) + 1),
              ((g 0 : ℕ) + 1), ((g 1 : ℕ) + 1), ((g 2 : ℕ) + 1)] j
          then ‖Tgq H 3 χ f g‖ else 0)
        ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ)) := by
  classical
  obtain ⟨C6, hC6pos, hC6⟩ :=
    Commons.NumberTheory.DirichletSeries.pow_card_primeFactors_le_const_mul_rpow 6 (ε/2)
      (by norm_num) (by linarith)
  obtain ⟨Cd, hCdpos, hCd⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (ε/10) (by linarith)
  refine ⟨192 * C6 * Cd ^ 5 + 1, by positivity, ?_⟩
  intro q _inst hcube χ hprim hne H hH6
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hqRpos : (0:ℝ) < (q:ℝ) := by linarith
  set B : ℝ := (6:ℝ)^(q.primeFactors.card) * Real.sqrt (q:ℝ) with hBdef
  set τ : ℝ := ((q.divisors.card : ℕ) : ℝ) with hτdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hτnn : 0 ≤ τ := by rw [hτdef]; positivity
  -- rewrite the singleton indicator in terms of `bmr3sc_UniqIdx`
  have hconv : (∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
        (if ∃ i : Fin 6, ∀ j : Fin 6, j ≠ i →
          ![((f 0 : ℕ) + 1), ((f 1 : ℕ) + 1), ((f 2 : ℕ) + 1),
            ((g 0 : ℕ) + 1), ((g 1 : ℕ) + 1), ((g 2 : ℕ) + 1)] i
          ≠ ![((f 0 : ℕ) + 1), ((f 1 : ℕ) + 1), ((f 2 : ℕ) + 1),
            ((g 0 : ℕ) + 1), ((g 1 : ℕ) + 1), ((g 2 : ℕ) + 1)] j
        then ‖Tgq H 3 χ f g‖ else 0))
      = ∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
        (if ∃ i : Fin 6, bmr3sc_UniqIdx f g i then ‖Tgq H 3 χ f g‖ else 0) := by
    apply Finset.sum_congr rfl; intro f _
    apply Finset.sum_congr rfl; intro g _
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by simpa only [bmr3sc_UniqIdx, bmr3sc_v6] using hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, by simpa only [bmr3sc_UniqIdx, bmr3sc_v6] using hi⟩
  rw [hconv]
  have hprod : (∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
        (if ∃ i : Fin 6, bmr3sc_UniqIdx f g i then ‖Tgq H 3 χ f g‖ else 0))
      = ∑ p : (Fin 3 → Fin H) × (Fin 3 → Fin H),
          (if ∃ i : Fin 6, bmr3sc_UniqIdx p.1 p.2 i then ‖Tgq H 3 χ p.1 p.2‖ else 0) :=
    (Fintype.sum_prod_type (f := fun p : (Fin 3 → Fin H) × (Fin 3 → Fin H) =>
      (if ∃ i : Fin 6, bmr3sc_UniqIdx p.1 p.2 i then ‖Tgq H 3 χ p.1 p.2‖ else 0))).symm
  rw [hprod]
  -- pointwise bound
  have hpoint : ∀ p : (Fin 3 → Fin H) × (Fin 3 → Fin H),
      (if ∃ i : Fin 6, bmr3sc_UniqIdx p.1 p.2 i then ‖Tgq H 3 χ p.1 p.2‖ else 0) ≤
        B * ∑ i : Fin 6,
          (if bmr3sc_UniqIdx p.1 p.2 i then bmr3sc_Wgt q p.1 p.2 i else 0) := by
    intro p
    by_cases hU : ∃ i : Fin 6, bmr3sc_UniqIdx p.1 p.2 i
    · rw [if_pos hU]
      obtain ⟨i0, hi0⟩ := hU
      have hb : ‖Tgq H 3 χ p.1 p.2‖ ≤ B * bmr3sc_Wgt q p.1 p.2 i0 := by
        have h0 := bmr3sc_norm_Tgq_three_singleton_le hcube χ hprim hne H p.1 p.2 i0 hi0
        rw [hBdef]
        simpa only [bmr3sc_Wgt] using h0
      have hnn : ∀ i : Fin 6,
          0 ≤ (if bmr3sc_UniqIdx p.1 p.2 i then bmr3sc_Wgt q p.1 p.2 i else 0) := by
        intro i; by_cases h : bmr3sc_UniqIdx p.1 p.2 i
        · rw [if_pos h]; exact bmr3sc_Wgt_nonneg q p.1 p.2 i
        · rw [if_neg h]
      have hw : bmr3sc_Wgt q p.1 p.2 i0 ≤ ∑ i : Fin 6,
          (if bmr3sc_UniqIdx p.1 p.2 i then bmr3sc_Wgt q p.1 p.2 i else 0) := by
        calc bmr3sc_Wgt q p.1 p.2 i0
            = (if bmr3sc_UniqIdx p.1 p.2 i0 then bmr3sc_Wgt q p.1 p.2 i0 else 0) := by
              rw [if_pos hi0]
          _ ≤ _ := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ i0)
      exact hb.trans (mul_le_mul_of_nonneg_left hw hBnn)
    · rw [if_neg hU]
      apply mul_nonneg hBnn
      apply Finset.sum_nonneg
      intro i _
      by_cases h : bmr3sc_UniqIdx p.1 p.2 i
      · rw [if_pos h]; exact bmr3sc_Wgt_nonneg q p.1 p.2 i
      · rw [if_neg h]
  have hY : (∑ p : (Fin 3 → Fin H) × (Fin 3 → Fin H),
        B * ∑ i : Fin 6,
          (if bmr3sc_UniqIdx p.1 p.2 i then bmr3sc_Wgt q p.1 p.2 i else 0))
      = B * ∑ i : Fin 6, ∑ p : (Fin 3 → Fin H) × (Fin 3 → Fin H),
          (if bmr3sc_UniqIdx p.1 p.2 i then bmr3sc_Wgt q p.1 p.2 i else 0) := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hZ : (∑ i : Fin 6, ∑ p : (Fin 3 → Fin H) × (Fin 3 → Fin H),
          (if bmr3sc_UniqIdx p.1 p.2 i then bmr3sc_Wgt q p.1 p.2 i else 0))
      = ∑ i : Fin 6, ∑ w : Fin 6 → Fin H, bmr3sc_Ww q w i := by
    apply Finset.sum_congr rfl
    intro i _
    refine Fintype.sum_equiv (bmr3sc_pairEquiv H) _ _ ?_
    intro p
    by_cases h : bmr3sc_UniqIdx p.1 p.2 i
    · rw [if_pos h]; exact bmr3sc_Wgt_eq_Ww_of q p.1 p.2 i h
    · rw [if_neg h]; exact (bmr3sc_Ww_eq_zero_of_not q p.1 p.2 i h).symm
  have hYb : (∑ i : Fin 6, ∑ w : Fin 6 → Fin H, bmr3sc_Ww q w i)
      ≤ 192 * (H:ℝ) ^ 6 * τ ^ 5 := by
    have hterm : ∀ i : Fin 6, (∑ w : Fin 6 → Fin H, bmr3sc_Ww q w i)
        ≤ 32 * (H:ℝ) ^ 6 * τ ^ 5 := by
      intro i
      simp only [bmr3sc_Ww_eq_swap]
      have h := bmr3sc_sum_prod_gcd_diff_le (q := q) (H := H) hq0 i
      simpa only [hτdef] using h
    calc (∑ i : Fin 6, ∑ w : Fin 6 → Fin H, bmr3sc_Ww q w i)
        ≤ ∑ i : Fin 6, (32 * (H:ℝ) ^ 6 * τ ^ 5) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = 6 * (32 * (H:ℝ) ^ 6 * τ ^ 5) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ = 192 * (H:ℝ) ^ 6 * τ ^ 5 := by ring
  have hBs : B * (192 * (H:ℝ) ^ 6 * τ ^ 5)
      ≤ 192 * C6 * Cd ^ 5 * (q:ℝ) ^ ε * (H:ℝ) ^ 6 * Real.sqrt (q:ℝ) := by
    have h6 : (6:ℝ)^(q.primeFactors.card) ≤ C6 * (q:ℝ)^(ε/2) := hC6 q hq1
    have hd : τ ≤ Cd * (q:ℝ)^(ε/10) := by rw [hτdef]; exact hCd q
    have hd5 : τ^5 ≤ (Cd * (q:ℝ)^(ε/10))^5 := pow_le_pow_left₀ hτnn hd 5
    have hτ5nn : 0 ≤ τ^5 := by positivity
    have hcomb : (6:ℝ)^(q.primeFactors.card) * τ^5 ≤ C6 * Cd^5 * (q:ℝ)^ε := by
      have h1 : (6:ℝ)^(q.primeFactors.card) * τ^5
          ≤ (C6 * (q:ℝ)^(ε/2)) * (Cd * (q:ℝ)^(ε/10))^5 :=
        mul_le_mul h6 hd5 hτ5nn (by positivity)
      have h2 : (Cd * (q:ℝ)^(ε/10))^5 = Cd^5 * (q:ℝ)^(ε/2) := by
        rw [mul_pow]
        congr 1
        rw [show ((q:ℝ)^(ε/10))^5 = ((q:ℝ)^(ε/10))^(5:ℝ) by norm_num [Real.rpow_natCast]]
        rw [← Real.rpow_mul hqRpos.le (ε/10) (5:ℝ)]
        rw [show (ε/10) * (5:ℝ) = ε/2 by ring]
      have h3 : (q:ℝ)^(ε/2) * (q:ℝ)^(ε/2) = (q:ℝ)^ε := by
        rw [← Real.rpow_add hqRpos]; ring_nf
      calc (6:ℝ)^(q.primeFactors.card) * τ^5
          ≤ (C6 * (q:ℝ)^(ε/2)) * (Cd * (q:ℝ)^(ε/10))^5 := h1
        _ = (C6 * (q:ℝ)^(ε/2)) * (Cd^5 * (q:ℝ)^(ε/2)) := by rw [h2]
        _ = C6 * Cd^5 * ((q:ℝ)^(ε/2) * (q:ℝ)^(ε/2)) := by ring
        _ = C6 * Cd^5 * (q:ℝ)^ε := by rw [h3]
    calc B * (192 * (H:ℝ)^6 * τ^5)
        = 192 * (H:ℝ)^6 * Real.sqrt (q:ℝ) * ((6:ℝ)^(q.primeFactors.card) * τ^5) := by
          rw [hBdef]; ring
      _ ≤ 192 * (H:ℝ)^6 * Real.sqrt (q:ℝ) * (C6 * Cd^5 * (q:ℝ)^ε) := by
          apply mul_le_mul_of_nonneg_left hcomb
          positivity
      _ = 192 * C6 * Cd^5 * (q:ℝ)^ε * (H:ℝ)^6 * Real.sqrt (q:ℝ) := by ring
  refine (Finset.sum_le_sum (fun p _ => hpoint p)).trans ?_
  rw [hY, hZ]
  refine (mul_le_mul_of_nonneg_left hYb hBnn).trans ?_
  refine hBs.trans ?_
  have hA0 : (0:ℝ) ≤ 192 * C6 * Cd ^ 5 := by positivity
  have hpe : (0:ℝ) ≤ (q:ℝ) ^ ε := Real.rpow_nonneg hqRpos.le ε
  have hsq0 : (0:ℝ) ≤ Real.sqrt (q:ℝ) := Real.sqrt_nonneg _
  have hY0 : (0:ℝ) ≤ (H:ℝ) ^ 6 * Real.sqrt (q:ℝ) := by positivity
  have hZ0 : (0:ℝ) ≤ (q:ℝ) * (H:ℝ) ^ 3 := by positivity
  nlinarith [hA0, hpe, hsq0, hY0, hZ0,
    mul_nonneg hpe hY0, mul_nonneg hpe hZ0, mul_nonneg (mul_nonneg hA0 hpe) hZ0]

end Commons.NumberTheory.DirichletCharacter
