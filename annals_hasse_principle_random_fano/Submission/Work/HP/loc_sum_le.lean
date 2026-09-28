import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.DiagDefs
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.veronese_enorm_lower
import Submission.Work.HP.bigW_le_pow

/-!
# The diagonal localised sum `Σ_a Δ_V^loc(B) ≪ A^{N-1} B`

Browning--Le Boudec--Sawin, *The Hasse principle for random Fano hypersurfaces* (Annals 197 (3),
2023): the diagonal contribution `Δ_V^loc(B)` to the second moment of the localised counting
function satisfies

`Σ_{a ∈ V_{d,n}(A)} Δ_V^loc(a,B) ≪ A^{N-1} B`,   `N = N_{d,n} = #Mon d n`,

which is the third summand of the diagonal bound `K(A,B) ≪ A^N · B/A` used in the proof of the
variance proposition.

The proof here is elementary: dropping the arithmetic conditions `W ∣ f_a(x)` and the cone
condition, `Δ_V^loc` is bounded by a product of two single sums,

`Δ_V^loc(a,B) ≤ ½ (log B · W / ‖a‖)² · Σ_{x ∈ Ξ(B)} ‖ν(x)‖^{-2}`,

so the double sum factorises as `(Σ_a ‖a‖^{-2}) · (Σ_x ‖ν(x)‖^{-2})`; the first factor is
`≪ A^{N-2}` (dyadic ball counting in `ℤ^N`), the second is `≪ B` (dyadic ball counting in
`ℤ^{n+1}` together with `‖ν(x)‖ ≳ ‖x‖^d`), and `W = B^{o(1)}` (`bigW_le_pow`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Filter Finset

namespace Work.HP

/-! ## Elementary facts about `eNorm` -/

section NormFacts
variable {ι : Type*} [Fintype ι]

/-- A nonzero integer vector has Euclidean norm at least `1`. -/
lemma lsq_one_le_eNorm {v : ι → ℤ} (hv : v ≠ 0) : (1:ℝ) ≤ eNorm v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hiz : v i ≠ 0 := by simpa using hi
  have hge : (1 : ℤ) ≤ |v i| := by have := abs_pos.mpr hiz; omega
  have hge' : (1 : ℝ) ≤ |((v i : ℤ) : ℝ)| := by exact_mod_cast hge
  have hsq : (1 : ℝ) ≤ ((v i : ℝ)) ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_nonneg ((v i : ℤ) : ℝ)]
  have h2 : ((v i : ℝ)) ^ 2 ≤ ∑ j, ((v j : ℝ)) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j : ℝ)) (Finset.mem_univ i)
  simpa [eNorm] using Real.one_le_sqrt.mpr (le_trans hsq h2)

/-- The set of integer vectors of Euclidean norm at most `C` is finite. -/
lemma lsq_finite_eNorm_le (C : ℝ) : ({v : ι → ℤ | eNorm v ≤ C} : Set (ι → ℤ)).Finite := by
  refine (Set.Finite.pi fun _ : ι => Set.finite_Icc (-⌈C⌉) ⌈C⌉).subset ?_
  intro v hv
  rw [Set.mem_univ_pi]
  intro i
  rw [Set.mem_Icc]
  have h1 : |((v i : ℤ) : ℝ)| ≤ eNorm v := abs_coord_le_eNorm v i
  have hab : |((v i : ℤ) : ℝ)| ≤ C := le_trans h1 hv
  obtain ⟨hl, hu⟩ := abs_le.mp hab
  constructor
  · have h3 : ((-⌈C⌉ : ℤ) : ℝ) ≤ ((v i : ℤ) : ℝ) := by
      have h4 : -(⌈C⌉ : ℝ) ≤ -C := by have := Int.le_ceil C; linarith
      push_cast; linarith
    exact_mod_cast h3
  · have h3 : ((v i : ℤ) : ℝ) ≤ ((⌈C⌉ : ℤ) : ℝ) := by
      have h4 := Int.le_ceil C; linarith
    exact_mod_cast h3

/-- Box count: the number of integer vectors of Euclidean norm at most `t` is `≤ (2t+3)^{card}`. -/
lemma lsq_ncard_ball_le [DecidableEq ι] (t : ℝ) (ht : 0 ≤ t) :
    (({v : ι → ℤ | eNorm v ≤ t} : Set (ι → ℤ)).ncard : ℝ) ≤ (2 * t + 3) ^ (Fintype.card ι) := by
  set box : Finset (ι → ℤ) := Fintype.piFinset (fun _ : ι => Finset.Icc (-⌈t⌉) ⌈t⌉) with hboxdef
  have hsub : ({v : ι → ℤ | eNorm v ≤ t} : Set (ι → ℤ)) ⊆ (↑box : Set (ι → ℤ)) := by
    intro v hv
    rw [Finset.mem_coe, hboxdef, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h1 : |((v i : ℤ) : ℝ)| ≤ eNorm v := abs_coord_le_eNorm v i
    have hab : |((v i : ℤ) : ℝ)| ≤ t := le_trans h1 hv
    obtain ⟨hl, hu⟩ := abs_le.mp hab
    constructor
    · have h3 : ((-⌈t⌉ : ℤ) : ℝ) ≤ ((v i : ℤ) : ℝ) := by
        have h4 : -(⌈t⌉ : ℝ) ≤ -t := by have := Int.le_ceil t; linarith
        push_cast; linarith
      exact_mod_cast h3
    · have h3 : ((v i : ℤ) : ℝ) ≤ ((⌈t⌉ : ℤ) : ℝ) := by
        have h4 := Int.le_ceil t; linarith
      exact_mod_cast h3
  have hcard : ((↑box : Set (ι → ℤ)).ncard : ℝ) = (box.card : ℝ) := by
    have h : (box.finite_toSet).toFinset = box := by
      ext x; rw [Set.Finite.mem_toFinset, Finset.mem_coe]
    rw [Set.ncard_eq_toFinset_card (↑box : Set (ι → ℤ)) box.finite_toSet, h]
  have hle : (({v : ι → ℤ | eNorm v ≤ t} : Set (ι → ℤ)).ncard : ℝ)
      ≤ ((↑box : Set (ι → ℤ)).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub box.finite_toSet
  rw [hcard] at hle
  refine le_trans hle ?_
  have hb : box.card = (2 * ⌈t⌉ + 1 : ℤ).toNat ^ (Fintype.card ι) := by
    rw [hboxdef, Fintype.card_piFinset]
    rw [Finset.prod_const]
    congr 2
    rw [Int.card_Icc]
    have hM : (0:ℤ) ≤ ⌈t⌉ := Int.ceil_nonneg ht
    omega
  rw [hb, Nat.cast_pow]
  have hnn : (0:ℤ) ≤ 2 * ⌈t⌉ + 1 := by have := Int.ceil_nonneg ht; omega
  have h2 : (((2 * ⌈t⌉ + 1 : ℤ)).toNat : ℝ) = (((2 * ⌈t⌉ + 1 : ℤ)) : ℝ) := by
    have h3 := Int.toNat_of_nonneg hnn
    exact_mod_cast h3
  rw [h2]
  push_cast
  refine pow_le_pow_left₀ (by positivity) ?_ (Fintype.card ι)
  have h4 := Int.ceil_lt_add_one t
  linarith

end NormFacts

/-! ## The dyadic ball sum `Σ_{0 < ‖x‖ ≤ R} ‖x‖^{-2k}` -/

section Dyadic
variable {ι : Type*} [Fintype ι]

/-- `2^{ja}/2^{jb} ≤ 2^{j(a-b)}`, with truncated subtraction on the right. -/
lemma lsq_pow_div_two_le (a b j : ℕ) :
    (2:ℝ)^(j*a) / (2:ℝ)^(j*b) ≤ (2:ℝ)^(j*(a - b)) := by
  rcases le_total b a with hba | hab
  · have hexp : j*(a-b) = j*a - j*b := Nat.mul_sub_left_distrib j a b
    rw [hexp, pow_sub₀ _ (by norm_num : (2:ℝ) ≠ 0) (Nat.mul_le_mul_left j hba), div_eq_mul_inv]
  · have hjab : j * a ≤ j * b := Nat.mul_le_mul_left j hab
    have h1 : (2:ℝ)^(j*a) ≤ (2:ℝ)^(j*b) := pow_le_pow_right₀ (by norm_num) hjab
    have h2 : j * (a - b) = 0 := by
      rw [Nat.mul_eq_zero]; right; omega
    rw [h2, pow_zero]
    exact div_le_one_of_le₀ h1 (by positivity)

/-- `Nat.log 2 M ≤ log M / log 2` for `1 ≤ M`. -/
lemma lsq_nat_log_two_le (M : ℕ) (hM : 1 ≤ M) :
    ((Nat.log 2 M : ℕ) : ℝ) ≤ Real.log M / Real.log 2 := by
  have hpow : (2:ℕ)^(Nat.log 2 M) ≤ M := Nat.pow_log_le_self 2 (by omega)
  have hlog : Real.log ((2:ℝ)^(Nat.log 2 M)) ≤ Real.log M := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hpow
  rw [Real.log_pow] at hlog
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  exact (le_div_iff₀ hlog2).mpr hlog

variable [DecidableEq ι]

/-- For `a ≥ 1`, `a^m / a^n ≤ a^(m-n)` (truncated subtraction). -/
lemma lsq_pow_div_pow_le (a : ℝ) (ha : 1 ≤ a) (m n : ℕ) : a^m / a^n ≤ a^(m - n) := by
  rcases le_total n m with h | h
  · rw [pow_sub₀ _ (by positivity) h, div_eq_mul_inv]
  · have h1 : a^m ≤ a^n := pow_le_pow_right₀ ha h
    have h2 : m - n = 0 := by omega
    rw [h2, pow_zero]
    exact div_le_one_of_le₀ h1 (by positivity)

/-- **Pointwise dyadic bound.**  If `R ≤ 2^J` and `0 < ‖x‖ ≤ R` then `‖x‖^{-2k}` is at most the
sum of the shell weights `2^{2k(1-j)}` over the levels `j ≤ J` with `‖x‖ ≤ 2^j`. -/
lemma lsq_dyadic_pointwise (k : ℕ) (hk : 1 ≤ k) (J : ℕ) (R : ℝ) (hRJ : R ≤ (2:ℝ)^J)
    {x : ι → ℤ} (hx0 : 0 < eNorm x) (hxR : eNorm x ≤ R) :
    1 / eNorm x ^ (2*k) ≤
      ∑ j ∈ Finset.range (J+1), (2:ℝ)^(2*k) / (2:ℝ)^(2*k*j) *
        (if eNorm x ≤ (2:ℝ)^j then (1:ℝ) else 0) := by
  have hxne : x ≠ 0 := by intro h; rw [h] at hx0; simp [eNorm] at hx0
  have hex : ∃ j, eNorm x ≤ (2:ℝ)^j := ⟨J, le_trans hxR hRJ⟩
  set L := Nat.find hex with hLdef
  have hLspec : eNorm x ≤ (2:ℝ)^L := Nat.find_spec hex
  have hLJ : L ≤ J := Nat.find_le (le_trans hxR hRJ)
  have hmem : L ∈ Finset.range (J+1) := Finset.mem_range.mpr (by omega)
  have hsingle : (2:ℝ)^(2*k) / (2:ℝ)^(2*k*L) ≤
      ∑ j ∈ Finset.range (J+1), (2:ℝ)^(2*k) / (2:ℝ)^(2*k*j) *
        (if eNorm x ≤ (2:ℝ)^j then (1:ℝ) else 0) := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun j => (2:ℝ)^(2*k) / (2:ℝ)^(2*k*j) *
        (if eNorm x ≤ (2:ℝ)^j then (1:ℝ) else 0)) (fun j _ => ?_) hmem)
    · rw [if_pos hLspec, mul_one]
    · by_cases h : eNorm x ≤ (2:ℝ)^j <;> simp only [h, if_true, if_false] <;> positivity
  refine le_trans ?_ hsingle
  rcases Nat.eq_zero_or_pos L with h0 | hpos
  · rw [h0] at hLspec ⊢
    have hx1 : eNorm x ≤ 1 := by simpa using hLspec
    have hx2 : (1:ℝ) ≤ eNorm x := lsq_one_le_eNorm hxne
    have hxe : eNorm x = 1 := le_antisymm hx1 hx2
    rw [hxe, one_pow, div_one, mul_zero]
    have h4 : (4:ℝ) ≤ (2:ℝ)^(2*k) := by
      have := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show 2 ≤ 2*k by omega)
      norm_num at this; exact this
    linarith
  · have hL1 : 1 ≤ L := hpos
    have hmin : (2:ℝ)^(L-1) < eNorm x := by
      have h := Nat.find_min hex (show L - 1 < L by omega)
      exact not_le.mp h
    have hpow : (2:ℝ)^((L-1)*(2*k)) < eNorm x^(2*k) := by
      have h2 := pow_lt_pow_left₀ hmin (by positivity : (0:ℝ) ≤ (2:ℝ)^(L-1))
        (show 2*k ≠ 0 by omega)
      rwa [← pow_mul] at h2
    have hLsub : L - 1 + 1 = L := Nat.sub_add_cancel hL1
    have hexp : (L-1)*(2*k) + 2*k = L*(2*k) := by
      conv_rhs => rw [← hLsub, Nat.add_mul, one_mul]
    have hmul : (2:ℝ)^(L*(2*k)) = (2:ℝ)^((L-1)*(2*k)) * (2:ℝ)^(2*k) := by
      rw [← pow_add, hexp]
    have hlt : (2:ℝ)^(L*(2*k)) < eNorm x^(2*k) * (2:ℝ)^(2*k) := by
      rw [hmul]
      exact mul_lt_mul_of_pos_right hpow (by positivity)
    rw [Nat.mul_comm (2*k) L]
    have hlt2 : (2:ℝ)^(L*(2*k)) / (2:ℝ)^(2*k) < eNorm x^(2*k) := by
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^(2*k))]
      exact hlt
    have hpos2 : 0 < (2:ℝ)^(L*(2*k)) / (2:ℝ)^(2*k) := by positivity
    have hfin := one_div_lt_one_div_of_lt hpos2 hlt2
    calc 1 / eNorm x ^ (2*k) ≤ 1 / ((2:ℝ)^(L*(2*k))/(2:ℝ)^(2*k)) := le_of_lt hfin
      _ = (2:ℝ)^(2*k)/(2:ℝ)^(L*(2*k)) := by rw [one_div_div]

/-- **The dyadic ball sum.**  For `k ≥ 1` and `R ≥ 1`,
`Σ_{0 < ‖x‖ ≤ R} ‖x‖^{-2k} ≪ (1 + R^{N-2k}) (1 + log R)` where `N = card ι` (the exponent
`N - 2k` being truncated subtraction). -/
theorem dyadic_ball_sum (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      (∑ᶠ x ∈ ({x : ι → ℤ | 0 < eNorm x ∧ eNorm x ≤ R} : Set (ι → ℤ)),
          1 / eNorm x ^ (2 * k))
        ≤ C * (1 + R ^ (Fintype.card ι - 2 * k)) * (1 + Real.log R) := by
  classical
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hconstpos : 0 < 3 + 1 / Real.log 2 := by positivity
  refine ⟨2 ^ (2*k) * 5 ^ (Fintype.card ι) * 4 ^ (Fintype.card ι) * (3 + 1 / Real.log 2),
    by positivity, ?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hlogR0' : 0 ≤ Real.log R := Real.log_nonneg hR
  set N : ℕ := Fintype.card ι with hNdef
  set J : ℕ := Nat.log 2 ⌈R⌉₊ + 1 with hJdef
  have hceil1 : 1 ≤ ⌈R⌉₊ := by
    have h := Nat.le_ceil R
    exact_mod_cast (le_trans hR h)
  have hpJ : (2:ℝ)^J ≤ 4 * R := by
    have h1 : (2:ℝ)^(Nat.log 2 ⌈R⌉₊) ≤ ((⌈R⌉₊ : ℕ) : ℝ) := by
      have := Nat.pow_log_le_self 2 (x := ⌈R⌉₊) (by omega)
      exact_mod_cast this
    have h2 : ((⌈R⌉₊ : ℕ) : ℝ) ≤ R + 1 := le_of_lt (Nat.ceil_lt_add_one hRpos.le)
    rw [hJdef, pow_succ]
    linarith
  have hRJ : R ≤ (2:ℝ)^J := by
    have h1 : ⌈R⌉₊ < 2^J := by
      have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) ⌈R⌉₊
      rw [hJdef]
      simpa [Nat.succ_eq_add_one] using h2
    exact le_trans (Nat.le_ceil R) (by exact_mod_cast h1.le)
  -- the J-bound
  have hJbd : ((J : ℕ) : ℝ) + 1 ≤ (3 + 1 / Real.log 2) * (1 + Real.log R) := by
    have hlogR0 : 0 ≤ Real.log R := Real.log_nonneg hR
    have h1 := lsq_nat_log_two_le (⌈R⌉₊) hceil1
    have h2 : Real.log ((⌈R⌉₊ : ℕ) : ℝ) ≤ Real.log 2 + Real.log R := by
      have h4 : ((⌈R⌉₊ : ℕ) : ℝ) ≤ 2*R := by
        have h5 : (⌈R⌉₊ : ℝ) ≤ R + 1 := le_of_lt (Nat.ceil_lt_add_one hRpos.le)
        linarith
      calc Real.log ((⌈R⌉₊ : ℕ) : ℝ) ≤ Real.log (2*R) := Real.log_le_log (by positivity) h4
        _ = Real.log 2 + Real.log R := Real.log_mul (by norm_num) hRpos.ne'
    have h3 : ((Nat.log 2 ⌈R⌉₊ : ℕ) : ℝ) ≤ 1 + Real.log R / Real.log 2 := by
      refine le_trans h1 ?_
      rw [div_le_iff₀ hlog2pos]
      rw [add_mul, one_mul, div_mul_cancel₀ _ hlog2pos.ne']
      exact h2
    have h6 : Real.log R / Real.log 2 = Real.log R * (1/Real.log 2) := by
      rw [div_eq_mul_one_div]
    have h7 : (3 + 1/Real.log 2) * (1 + Real.log R)
        = 3 + 3*Real.log R + (1+Real.log R)*(1/Real.log 2) := by ring
    rw [h7, hJdef]
    have h8 : (0:ℝ) ≤ 3 * Real.log R + 1/Real.log 2 := by positivity
    have hcast : (((Nat.log 2 ⌈R⌉₊ + 1 : ℕ)) : ℝ) + 1 = ((Nat.log 2 ⌈R⌉₊ : ℕ) : ℝ) + 2 := by
      push_cast; ring
    rw [hcast]
    nlinarith [h3, h6, h8, hlogR0, hlog2pos]
  -- the sum bound
  have hSfin : ({x : ι → ℤ | 0 < eNorm x ∧ eNorm x ≤ R} : Set (ι → ℤ)).Finite :=
    (lsq_finite_eNorm_le R).subset (fun v hv => hv.2)
  set T : Finset (ι → ℤ) := hSfin.toFinset with hTdef
  have hmemT : ∀ x, x ∈ T ↔ 0 < eNorm x ∧ eNorm x ≤ R := by
    intro x; rw [hTdef]; exact hSfin.mem_toFinset
  rw [finsum_mem_of_finite _ hSfin, ← hTdef]
  have hcardj : ∀ j : ℕ, ((T.filter (fun x => eNorm x ≤ (2:ℝ)^j)).card : ℝ)
      ≤ (5 * (2:ℝ)^j) ^ N := by
    intro j
    set M : ℤ := ⌈(2:ℝ)^j⌉ with hMdef
    have hM0 : (0:ℤ) ≤ M := by rw [hMdef]; exact Int.ceil_nonneg (by positivity)
    set box : Finset (ι → ℤ) := Fintype.piFinset (fun _ : ι => Finset.Icc (-M) M) with hboxdef
    have hsub : T.filter (fun x => eNorm x ≤ (2:ℝ)^j) ⊆ box := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [hboxdef, Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      have h1 : |((x i : ℤ) : ℝ)| ≤ eNorm x := abs_coord_le_eNorm x i
      have h2 : eNorm x ≤ (2:ℝ)^j := hx.2
      have hceil := Int.le_ceil ((2:ℝ)^j)
      constructor
      · rw [hMdef]
        have h8 : -((x i : ℤ) : ℝ) ≤ |((x i : ℤ) : ℝ)| := neg_le_abs _
        have h9 : -(((⌈(2:ℝ)^j⌉ : ℤ)) : ℝ) ≤ ((x i : ℤ) : ℝ) := by linarith
        push_cast
        exact_mod_cast h9
      · rw [hMdef]
        have h7 : ((x i : ℤ) : ℝ) ≤ |((x i : ℤ) : ℝ)| := le_abs_self _
        have h9 : ((x i : ℤ) : ℝ) ≤ (((⌈(2:ℝ)^j⌉ : ℤ)) : ℝ) := by linarith
        exact_mod_cast h9
    have hcard := Finset.card_le_card hsub
    have hboxcard : box.card = (2 * M + 1 : ℤ).toNat ^ (Fintype.card ι) := by
      rw [hboxdef, Fintype.card_piFinset]
      rw [Finset.prod_const]
      congr 2
      rw [Int.card_Icc]
      omega
    have h2' : ((2 * M + 1 : ℤ).toNat : ℝ) ≤ 2 * (2:ℝ)^j + 3 := by
      have hcast : (((2 * M + 1 : ℤ)).toNat : ℝ) = (((2 * M + 1 : ℤ)) : ℝ) := by
        have h3 := Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ 2 * M + 1)
        exact_mod_cast h3
      rw [hcast, hMdef]
      push_cast
      have := Int.ceil_lt_add_one ((2:ℝ)^j)
      linarith
    have hfinal : ((2 * M + 1 : ℤ).toNat : ℝ) ^ (Fintype.card ι)
        ≤ (5 * (2:ℝ)^j) ^ (Fintype.card ι) := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have h6 : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
      linarith
    rw [hNdef] at *
    calc ((T.filter (fun x => eNorm x ≤ (2:ℝ)^j)).card : ℝ)
        ≤ (box.card : ℝ) := by exact_mod_cast hcard
      _ = ((2 * M + 1 : ℤ).toNat : ℝ) ^ (Fintype.card ι) := by rw [hboxcard, Nat.cast_pow]
      _ ≤ (5 * (2:ℝ)^j) ^ (Fintype.card ι) := hfinal
  have hstep1 : ∑ x ∈ T, 1 / eNorm x ^ (2*k) ≤
      ∑ j ∈ Finset.range (J+1), ∑ x ∈ T, (2:ℝ)^(2*k) / (2:ℝ)^(2*k*j) *
        (if eNorm x ≤ (2:ℝ)^j then (1:ℝ) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun x hx => ?_)
    obtain ⟨h0, hR'⟩ := (hmemT x).mp hx
    exact lsq_dyadic_pointwise k hk J R hRJ h0 hR'
  have hstep2 : ∀ j ∈ Finset.range (J+1),
      ∑ x ∈ T, (2:ℝ)^(2*k) / (2:ℝ)^(2*k*j) * (if eNorm x ≤ (2:ℝ)^j then (1:ℝ) else 0)
      ≤ (2:ℝ)^(2*k) * 5^N * (2:ℝ)^(j*(N - 2*k)) := by
    intro j hj
    rw [← Finset.mul_sum, Finset.sum_boole]
    have hcj : 0 ≤ (2:ℝ)^(2*k) / (2:ℝ)^(2*k*j) := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left (hcardj j) hcj) ?_
    rw [hNdef] at *
    have hkey : ((2:ℝ)^j)^Fintype.card ι / (2:ℝ)^(2*k*j)
        ≤ (2:ℝ)^(j*(Fintype.card ι - 2 * k)) := by
      rw [← pow_mul, show 2*k*j = j*(2*k) from Nat.mul_comm _ _]
      exact lsq_pow_div_two_le (Fintype.card ι) (2*k) j
    rw [mul_pow]
    calc (2:ℝ)^(2*k) / (2:ℝ)^(2*k*j) * (5^Fintype.card ι * ((2:ℝ)^j)^Fintype.card ι)
        = 5^Fintype.card ι * 2^(2*k) * (((2:ℝ)^j)^Fintype.card ι / (2:ℝ)^(2*k*j)) := by ring
      _ ≤ 5^Fintype.card ι * 2^(2*k) * (2:ℝ)^(j*(Fintype.card ι - 2*k)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 2^(2*k) * 5^Fintype.card ι * (2:ℝ)^(j*(Fintype.card ι - 2*k)) := by ring
  refine le_trans (le_trans hstep1 (Finset.sum_le_sum hstep2)) ?_
  rw [← Finset.mul_sum]
  have hsum2 : ∑ j ∈ Finset.range (J+1), (2:ℝ)^(j*(N - 2*k))
      ≤ (((J : ℕ) : ℝ) + 1) * (2:ℝ)^(J*(N - 2*k)) := by
    have h1 : ∀ j ∈ Finset.range (J+1), (2:ℝ)^(j*(N - 2*k)) ≤ (2:ℝ)^(J*(N - 2*k)) := by
      intro j hj
      refine pow_le_pow_right₀ (by norm_num) ?_
      exact Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    calc ∑ j ∈ Finset.range (J+1), (2:ℝ)^(j*(N - 2*k))
        ≤ ∑ j ∈ Finset.range (J+1), (2:ℝ)^(J*(N - 2*k)) := Finset.sum_le_sum h1
      _ = (((J : ℕ) : ℝ) + 1) * (2:ℝ)^(J*(N - 2*k)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hJpow : (2:ℝ)^(J*(N - 2*k)) ≤ (4*R)^(N - 2*k) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hpJ _
  have h4R : (4*R)^(N - 2*k) = 4^(N - 2*k) * R^(N - 2*k) := mul_pow _ _ _
  have h4N : (4:ℝ)^(N - 2*k) ≤ (4:ℝ)^N := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) (Nat.sub_le _ _)
  have hRnonneg : (0:ℝ) ≤ R^(N - 2*k) := by positivity
  have hJ' : (((J:ℕ):ℝ) + 1) ≤ (3 + 1/Real.log 2) * (1 + Real.log R) := hJbd
  calc 2 ^ (2*k) * 5^N * (∑ i ∈ Finset.range (J+1), (2:ℝ)^(i*(N - 2*k)))
      ≤ 2 ^ (2*k) * 5^N * ((((J:ℕ):ℝ) + 1) * (4*R)^(N - 2*k)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact le_trans hsum2 (mul_le_mul_of_nonneg_left hJpow (by positivity))
    _ ≤ 2 ^ (2*k) * 5^N * (((3 + 1/Real.log 2) * (1 + Real.log R)) * (4^N * R^(N - 2*k))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [h4R]
        exact mul_le_mul hJ' (mul_le_mul_of_nonneg_right h4N hRnonneg) (by positivity) (by positivity)
    _ = 2 ^ (2*k) * 5^N * 4^N * (3 + 1/Real.log 2) * (1 + Real.log R) * R^(N - 2*k) := by ring
    _ ≤ 2 ^ (2*k) * 5^N * 4^N * (3 + 1/Real.log 2) * (1 + Real.log R) * (1 + R^(N - 2*k)) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 2 ^ (2*k) * 5^N * 4^N * (3 + 1/Real.log 2) * (1 + R^(N - 2*k)) * (1 + Real.log R) := by ring

end Dyadic

/-! ## Finsum plumbing -/

section Plumbing
variable {α : Type*}

lemma lsq_finsum_mem_le_of_subset_of_nonneg {s t : Set α} (hst : s ⊆ t) (ht : t.Finite)
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) : (∑ᶠ x ∈ s, f x) ≤ ∑ᶠ x ∈ t, f x := by
  have hs : s.Finite := ht.subset hst
  rw [finsum_mem_of_finite s hs, finsum_mem_of_finite t ht]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro x hx; exact ht.mem_toFinset.mpr (hst (hs.mem_toFinset.mp hx))
  · intro x _ _; exact hf x

lemma lsq_finsum_mem_le_of_le {s : Set α} (hs : s.Finite) {f g : α → ℝ}
    (h : ∀ x ∈ s, f x ≤ g x) : (∑ᶠ x ∈ s, f x) ≤ ∑ᶠ x ∈ s, g x := by
  rw [finsum_mem_of_finite s hs, finsum_mem_of_finite s hs]
  exact Finset.sum_le_sum fun x hx => h x (hs.mem_toFinset.mp hx)

lemma lsq_finsum_mem_congr {s : Set α} (hs : s.Finite) {f g : α → ℝ}
    (h : ∀ x ∈ s, f x = g x) : (∑ᶠ x ∈ s, f x) = ∑ᶠ x ∈ s, g x := by
  rw [finsum_mem_of_finite s hs, finsum_mem_of_finite s hs]
  exact Finset.sum_congr rfl fun x hx => h x (hs.mem_toFinset.mp hx)

lemma lsq_finsum_mem_mul_left (s : Set α) (hs : s.Finite) (c : ℝ) (f : α → ℝ) :
    (∑ᶠ x ∈ s, c * f x) = c * ∑ᶠ x ∈ s, f x := by
  rw [finsum_mem_of_finite s hs, finsum_mem_of_finite s hs, Finset.mul_sum]

lemma lsq_finsum_mem_mul_right (s : Set α) (hs : s.Finite) (c : ℝ) (f : α → ℝ) :
    (∑ᶠ x ∈ s, f x * c) = (∑ᶠ x ∈ s, f x) * c := by
  rw [finsum_mem_of_finite s hs, finsum_mem_of_finite s hs, Finset.sum_mul]

end Plumbing

/-- `(C/y)^2 = C^2 * (1/y^2)`, valid also at `y = 0`. -/
lemma lsq_sq_div_eq (C y : ℝ) : (C/y)^2 = C^2 * (1/y^2) := by
  rcases eq_or_ne y 0 with h | h
  · rw [h]; norm_num
  · field_simp

/-- A primitive integer vector is nonzero. -/
lemma lsq_isPrim_ne_zero {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : IsPrim v) : v ≠ 0 := by
  intro h
  rw [IsPrim] at hv
  have h0 : (Finset.univ.gcd (0 : ι → ℤ)) = 0 := by
    rw [Finset.gcd_eq_zero_iff]; intro i _; rfl
  rw [← h] at h0
  rw [h0] at hv
  exact one_ne_zero hv.symm

/-- `1 ≤ B / log B` for `B > 1`. -/
lemma lsq_one_le_div_log {B : ℝ} (hB : 1 < B) : 1 ≤ B / Real.log B := by
  have h0 : 0 < Real.log B := Real.log_pos hB
  rw [one_le_div h0]
  linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < B)]

/-- `Σ_{a ∈ primSet d n A} ‖a‖^{-2} ≪ (1+A^{N-2})(1+log A)`. -/
lemma lsq_primSet_weighted (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 1 ≤ A →
      (∑ᶠ a ∈ primSet d n A (fun _ => True), 1 / eNorm a ^ 2)
        ≤ K * (1 + A ^ (NN d n - 2)) * (1 + Real.log A) := by
  obtain ⟨C, hC, hsum⟩ := dyadic_ball_sum (Mon d n) 1 (by norm_num)
  refine ⟨C, hC, fun A hA => ?_⟩
  have hsub : primSet d n A (fun _ => True) ⊆
      ({a : Mon d n → ℤ | 0 < eNorm a ∧ eNorm a ≤ A} : Set (Mon d n → ℤ)) := by
    intro a ha
    obtain ⟨hprim, hnorm, -⟩ := ha
    exact ⟨lt_of_lt_of_le zero_lt_one (lsq_one_le_eNorm (lsq_isPrim_ne_zero hprim)), hnorm⟩
  refine le_trans (lsq_finsum_mem_le_of_subset_of_nonneg hsub
    ((lsq_finite_eNorm_le A).subset (fun v hv => hv.2)) (fun x => by positivity)) ?_
  simpa [NN, mul_one] using hsum A hA

/-- Product bound: `(1+R^m)(1+log R) ≤ 4B` for `R = B^{1/E}`, `B ≥ 1`, `E ≥ 1`, `m+1 ≤ E`. -/
lemma lsq_rpow_factor_bound (B : ℝ) (hB : 1 ≤ B) (E : ℝ) (hE : 1 ≤ E) (m : ℕ)
    (hm : (m:ℝ) + 1 ≤ E) :
    (1 + (B ^ (1/E))^m) * (1 + Real.log (B ^ (1/E))) ≤ 4 * B := by
  have hB0 : (0:ℝ) < B := lt_of_lt_of_le zero_lt_one hB
  set R : ℝ := B ^ (1/E) with hRdef
  have hR1 : 1 ≤ R := by
    rw [hRdef]; exact Real.one_le_rpow hB (by positivity)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hRB : R ≤ B := by
    rw [hRdef]
    calc B ^ (1/E) ≤ B ^ (1:ℝ) := by
          refine Real.rpow_le_rpow_of_exponent_le hB ?_
          rw [div_le_one (by linarith)]; linarith
      _ = B := Real.rpow_one B
  have hRpow : R^m = B ^ ((m:ℝ)/E) := by
    rw [hRdef, ← Real.rpow_natCast (B ^ (1/E)) m,
      ← Real.rpow_mul (le_of_lt hB0), one_div_mul_eq_div]
  have hmE : ((m:ℝ)/E) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hm1E : (((m:ℝ)+1)/E) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have key : ∀ j : ℕ, ((j:ℝ)) ≤ E → R^j ≤ B := by
    intro j hj
    have h0 : R^j = B ^ ((j:ℝ)/E) := by
      rw [hRdef, ← Real.rpow_natCast (B ^ (1/E)) j,
        ← Real.rpow_mul (le_of_lt hB0), one_div_mul_eq_div]
    rw [h0]
    calc B ^ ((j:ℝ)/E) ≤ B ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hB (by rw [div_le_one (by linarith)]; linarith)
      _ = B := Real.rpow_one B
  have h1 : R^m ≤ B := key m (by linarith)
  have h1' : R^(m+1) ≤ B := key (m+1) (by push_cast; linarith)
  have h2 : Real.log R ≤ B := by
    have h3 : Real.log R ≤ R - 1 := Real.log_le_sub_one_of_pos hRpos
    linarith
  have h3 : R^m * Real.log R ≤ B := by
    have hlogR : Real.log R ≤ R := by
      have := Real.log_le_sub_one_of_pos hRpos; linarith
    calc R^m * Real.log R ≤ R^m * R := mul_le_mul_of_nonneg_left hlogR (by positivity)
      _ = R^(m+1) := by rw [pow_succ]
      _ ≤ B := h1'
  have hexp : (1 + R^m) * (1 + Real.log R) = 1 + R^m + Real.log R + R^m * Real.log R := by ring
  rw [hexp]
  nlinarith [h1, h2, h3, hB]

/-- `Σ_{x ∈ Ξ_{d,n}(B)} ‖ν_{d,n}(x)‖^{-2} ≪ B`. -/
theorem Xi_veronese_sq (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ C B₀ : ℝ, 0 < C ∧ 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B →
      (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2) ≤ C * B := by
  obtain ⟨c, hcpos, hclow⟩ := veronese_enorm_lower d n hd
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₁, hC₁pos, hC₁⟩ := dyadic_ball_sum (Fin (n+1)) d hd1
  have hE1 : (1:ℝ) ≤ (n:ℝ) + 1 - d := by
    have hdn' : (d:ℝ) ≤ n := by exact_mod_cast hdn
    linarith
  have hmE : (((Fintype.card (Fin (n+1)) - 2*d : ℕ)) : ℝ) + 1 ≤ (n:ℝ) + 1 - d := by
    rw [Fintype.card_fin]
    rcases lt_or_ge (n+1) (2*d) with hlt | hle
    · rw [Nat.sub_eq_zero_of_le (le_of_lt hlt), Nat.cast_zero]
      have hdn' : (d:ℝ) ≤ n := by exact_mod_cast hdn
      linarith
    · have hc : ((n + 1 - 2*d : ℕ) : ℝ) = (n:ℝ) + 1 - 2*d := by
        rw [Nat.cast_sub hle]; push_cast; ring
      rw [hc]
      have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
      linarith
  refine ⟨4 * (1/c^2) * C₁, 2, by positivity, by norm_num, fun B hB => ?_⟩
  have hB1 : (1:ℝ) ≤ B := le_trans (by norm_num) hB
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  set R : ℝ := B ^ (1 / ((n:ℝ) + 1 - d)) with hRdef
  have hR1 : 1 ≤ R := by
    rw [hRdef]; exact Real.one_le_rpow hB1 (by positivity)
  have hsub : Xi d n B ⊆ ({x : Fin (n+1) → ℤ | 0 < eNorm x ∧ eNorm x ≤ R} :
      Set (Fin (n+1) → ℤ)) := by
    intro x hx
    obtain ⟨hprim, hnorm⟩ := hx
    exact ⟨lt_of_lt_of_le zero_lt_one (lsq_one_le_eNorm (lsq_isPrim_ne_zero hprim)),
      by rw [hRdef]; exact hnorm⟩
  have hper : ∀ x ∈ Xi d n B,
      1 / eNorm (veronese d n x) ^ 2 ≤ (1/c^2) * (1 / eNorm x ^ (2*d)) := by
    intro x hx
    obtain ⟨hprim, -⟩ := hx
    have hxne : x ≠ 0 := lsq_isPrim_ne_zero hprim
    have hxpos : 0 < eNorm x := lt_of_lt_of_le zero_lt_one (lsq_one_le_eNorm hxne)
    have h1 : c * eNorm x ^ d ≤ eNorm (veronese d n x) := hclow x
    have h2 : 0 < c * eNorm x ^ d := by positivity
    have h3 : (c * eNorm x ^ d)^2 ≤ eNorm (veronese d n x)^2 :=
      pow_le_pow_left₀ h2.le h1 2
    have h5 : 1 / eNorm (veronese d n x)^2 ≤ 1 / (c * eNorm x ^ d)^2 :=
      one_div_le_one_div_of_le (by positivity) h3
    refine le_trans h5 (le_of_eq ?_)
    rw [mul_pow, ← pow_mul, show d * 2 = 2 * d from Nat.mul_comm d 2]
    field_simp
  have hstep1 : (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2)
      ≤ (1/c^2) * (∑ᶠ x ∈ Xi d n B, 1 / eNorm x ^ (2*d)) := by
    refine le_trans (lsq_finsum_mem_le_of_le (Xi_finite d n B) hper) (le_of_eq ?_)
    exact lsq_finsum_mem_mul_left _ (Xi_finite d n B) _ _
  have hstep2 : (∑ᶠ x ∈ Xi d n B, 1 / eNorm x ^ (2*d))
      ≤ (∑ᶠ x ∈ ({x : Fin (n+1) → ℤ | 0 < eNorm x ∧ eNorm x ≤ R} : Set (Fin (n+1) → ℤ)),
          1 / eNorm x ^ (2*d)) :=
    lsq_finsum_mem_le_of_subset_of_nonneg hsub
      ((lsq_finite_eNorm_le R).subset (fun v hv => hv.2))
      (fun x => by
        have hx : (0:ℝ) ≤ eNorm x := by rw [eNorm]; exact Real.sqrt_nonneg _
        exact div_nonneg zero_le_one (pow_nonneg hx (2*d)))
  have hstep3 := hC₁ R hR1
  have hfac := lsq_rpow_factor_bound B hB1 ((n:ℝ) + 1 - d) hE1 (Fintype.card (Fin (n+1)) - 2*d) hmE
  have hconst : (0:ℝ) ≤ 1/c^2 := by positivity
  calc (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2)
      ≤ (1/c^2) * (∑ᶠ x ∈ Xi d n B, 1 / eNorm x ^ (2*d)) := hstep1
    _ ≤ (1/c^2) * (∑ᶠ x ∈ ({x : Fin (n+1) → ℤ | 0 < eNorm x ∧ eNorm x ≤ R} :
          Set (Fin (n+1) → ℤ)), 1 / eNorm x ^ (2*d)) :=
        mul_le_mul_of_nonneg_left hstep2 hconst
    _ ≤ (1/c^2) * (C₁ * (1 + R ^ (Fintype.card (Fin (n+1)) - 2*d)) * (1 + Real.log R)) :=
        mul_le_mul_of_nonneg_left hstep3 hconst
    _ ≤ (1/c^2) * (C₁ * (4 * B)) := by
        refine mul_le_mul_of_nonneg_left ?_ hconst
        have hfac' : (1 + R ^ (Fintype.card (Fin (n+1)) - 2*d)) * (1 + Real.log R) ≤ 4 * B := by
          simpa only [hRdef] using hfac
        calc C₁ * (1 + R ^ (Fintype.card (Fin (n+1)) - 2*d)) * (1 + Real.log R)
            = C₁ * ((1 + R ^ (Fintype.card (Fin (n+1)) - 2*d)) * (1 + Real.log R)) := by ring
          _ ≤ C₁ * (4 * B) := mul_le_mul_of_nonneg_left hfac' hC₁pos.le
    _ = 4 * (1/c^2) * C₁ * B := by ring

/-- `(log B)^m ≤ B^{3/4}` eventually, for every `m`. -/
lemma lsq_log_pow_le_rpow (m : ℕ) :
    ∀ᶠ B : ℝ in atTop, Real.log B ^ m ≤ B ^ ((3:ℝ)/4) := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    filter_upwards [eventually_ge_atTop (1:ℝ)] with B hB
    rw [pow_zero]
    exact Real.one_le_rpow hB (by norm_num)
  · have hr : (0:ℝ) < 1/(4*(m:ℝ)) := by positivity
    have hlit := (isLittleO_log_rpow_atTop hr).pow hpos
    have hcongr : (fun x : ℝ => (x ^ ((1:ℝ)/(4*(m:ℝ))))^m) =ᶠ[atTop] fun x : ℝ => x ^ ((1:ℝ)/4) := by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      have hkey : (1/(4*(m:ℝ))) * (m:ℝ) = (1:ℝ)/4 := by field_simp
      rw [← Real.rpow_natCast (x ^ ((1:ℝ)/(4*(m:ℝ)))) m,
        ← Real.rpow_mul (le_of_lt hx), hkey]
    have hlit' : (fun x : ℝ => Real.log x ^ m) =o[atTop] fun x : ℝ => x ^ ((1:ℝ)/4) :=
      hlit.congr' Filter.EventuallyEq.rfl hcongr
    filter_upwards [hlit'.eventuallyLE, eventually_ge_atTop (1:ℝ)] with B hB1 hB2
    have hlog0 : 0 ≤ Real.log B := Real.log_nonneg hB2
    have h1 : Real.log B ^ m ≤ B ^ ((1:ℝ)/4) := by
      have := hB1
      rwa [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg hlog0 m),
        abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at this
    calc Real.log B ^ m ≤ B ^ ((1:ℝ)/4) := h1
      _ ≤ B ^ ((3:ℝ)/4) := Real.rpow_le_rpow_of_exponent_le hB2 (by norm_num)

/-- **The diagonal localised sum.**  `Σ_{a ∈ V_{d,n}(A)} Δ_V^loc(B) ≪ A^{N-1} B`. -/
theorem loc_sum_le (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ K B₀ : ℝ, 0 < K ∧ 0 < B₀ ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      (∑ᶠ a ∈ primSet d n A (fun _ => True), DeltaLoc d n a B)
        ≤ K * A ^ (NN d n - 1) * B := by
  classical
  obtain ⟨K1, hK1pos, h1⟩ := lsq_primSet_weighted d n hd hdn
  obtain ⟨C2, B02, hC2pos, hB02pos, h2⟩ := Xi_veronese_sq d n hd hdn
  obtain ⟨B03, h3⟩ := bigW_le_pow (1/8) (by norm_num)
  obtain ⟨B04, h4⟩ := eventually_atTop.mp (lsq_log_pow_le_rpow 4)
  refine ⟨max 1 (8*K1*C2), max (max (max B02 B03) B04) 4,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 4) (le_max_right _ _), ?_⟩
  intro A B hB hA hAB
  have hB02' : B02 ≤ B :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hB
  have hB03' : B03 ≤ B :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hB
  have hB04' : B04 ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB
  have hB4 : (4:ℝ) ≤ B := le_trans (le_max_right _ _) hB
  have hB1 : (1:ℝ) ≤ B := by linarith
  have hBpos : 0 < B := by linarith
  have hA1 : (1:ℝ) ≤ A := le_trans (lsq_one_le_div_log (by linarith : (1:ℝ) < B)) hA
  have hApos : 0 < A := by linarith
  set L : ℝ := Real.log B with hLdef
  have hLnn : 0 ≤ L := by rw [hLdef]; exact Real.log_nonneg hB1
  have hLpos : 0 < L := by
    rw [hLdef]
    have h5 : Real.log 4 ≤ Real.log B := Real.log_le_log (by norm_num) hB4
    have h6 : (1:ℝ) ≤ Real.log 4 := by
      have h7 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
      rw [h7]
      linarith [Real.log_two_gt_d9]
    linarith
  have hWnn : (0:ℝ) ≤ (bigW (wOf B) : ℝ) := by positivity
  have hWa : (bigW (wOf B) : ℝ) ≤ B ^ ((1:ℝ)/8) := h3 B hB03'
  have hPfin : (primSet d n A (fun _ => True)).Finite := primSet_finite d n A _
  have hXfin : (Xi d n B).Finite := Xi_finite d n B
  have hSx : (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2) ≤ C2 * B := h2 B hB02'
  have hSa : (∑ᶠ a ∈ primSet d n A (fun _ => True), 1 / eNorm a ^ 2)
      ≤ K1 * (1 + A ^ (NN d n - 2)) * (1 + Real.log A) := h1 A hA1
  have hSann : 0 ≤ ∑ᶠ a ∈ primSet d n A (fun _ => True), 1 / eNorm a ^ 2 := by
    rw [finsum_mem_of_finite _ hPfin]
    exact Finset.sum_nonneg (fun a _ => div_nonneg zero_le_one (pow_nonneg (Real.sqrt_nonneg _) _))
  have hSxnn : 0 ≤ ∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2 := by
    rw [finsum_mem_of_finite _ hXfin]
    exact Finset.sum_nonneg (fun x _ => div_nonneg zero_le_one (pow_nonneg (Real.sqrt_nonneg _) _))
  have hper : ∀ a ∈ primSet d n A (fun _ => True), DeltaLoc d n a B ≤ (1/2) * (L * (bigW (wOf B) : ℝ) / eNorm a)^2 * (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2) := by
    intro a ha
    have hsub : ({x ∈ Xi d n B | ((bigW (wOf B) : ℕ) : ℤ) ∣ formEval d n a x ∧ toR a ∈ Cgam (toR (veronese d n x)) (Real.log B)} : Set (Fin (n + 1) → ℤ)) ⊆ Xi d n B := fun x hx => hx.1
    have hbound := lsq_finsum_mem_le_of_subset_of_nonneg hsub hXfin (fun x => by
      have hx : (0:ℝ) ≤ eNorm (veronese d n x) := Real.sqrt_nonneg _
      exact div_nonneg zero_le_one (pow_nonneg hx 2))
    rw [DeltaLoc, ← hLdef]
    exact mul_le_mul_of_nonneg_left hbound (mul_nonneg (by norm_num) (sq_nonneg _))
  have hstepA : (∑ᶠ a ∈ primSet d n A (fun _ => True), DeltaLoc d n a B) ≤ (∑ᶠ a ∈ primSet d n A (fun _ => True), (1/2) * (L * (bigW (wOf B) : ℝ) / eNorm a)^2 * (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2)) :=
    lsq_finsum_mem_le_of_le hPfin hper
  have hstepB : (∑ᶠ a ∈ primSet d n A (fun _ => True), (1/2) * (L * (bigW (wOf B) : ℝ) / eNorm a)^2 * (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2)) = (∑ᶠ a ∈ primSet d n A (fun _ => True), (1/2) * (L * (bigW (wOf B) : ℝ))^2 * ((1 / eNorm a ^ 2) * (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2))) := by
    refine lsq_finsum_mem_congr hPfin (fun a ha => ?_)
    rw [lsq_sq_div_eq]
    ring
  have hstepC : (∑ᶠ a ∈ primSet d n A (fun _ => True), (1/2) * (L * (bigW (wOf B) : ℝ))^2 * ((1 / eNorm a ^ 2) * (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2))) = (1/2) * (L * (bigW (wOf B) : ℝ))^2 * ((∑ᶠ a ∈ primSet d n A (fun _ => True), 1 / eNorm a ^ 2) * (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2)) := by
    rw [lsq_finsum_mem_mul_left _ hPfin]
    congr 1
    rw [lsq_finsum_mem_mul_right _ hPfin]
  have hstep : (∑ᶠ a ∈ primSet d n A (fun _ => True), DeltaLoc d n a B) ≤ (1/2) * (L * (bigW (wOf B) : ℝ))^2 * ((∑ᶠ a ∈ primSet d n A (fun _ => True), 1 / eNorm a ^ 2) * (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2)) :=
    le_trans hstepA (le_of_eq (hstepB.trans hstepC))
  have hAN1 : (1:ℝ) ≤ A ^ (NN d n - 2) := one_le_pow₀ hA1
  have hlogA : 1 + Real.log A ≤ 1 + 2*L := by
    have h5 : Real.log A ≤ Real.log (B^2) := Real.log_le_log hApos hAB
    rw [Real.log_pow] at h5
    rw [hLdef]
    push_cast at h5
    linarith
  have hSa' : (∑ᶠ a ∈ primSet d n A (fun _ => True), 1 / eNorm a ^ 2) ≤ K1 * (2 * A ^ (NN d n - 2)) * (1 + 2*L) := by
    refine le_trans hSa ?_
    have h1' : (1 + A ^ (NN d n - 2)) ≤ 2 * A ^ (NN d n - 2) := by linarith
    have h3' : 0 ≤ 1 + Real.log A := by
      have : 0 ≤ Real.log A := Real.log_nonneg hA1
      linarith
    have h4' : 0 ≤ K1 * (2 * A ^ (NN d n - 2)) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1' hK1pos.le) hlogA h3' h4'
  have hW2 : (L * (bigW (wOf B) : ℝ))^2 ≤ L^2 * B ^ ((1:ℝ)/4) := by
    have h1 : (bigW (wOf B) : ℝ)^2 ≤ B ^ ((1:ℝ)/4) := by
      have h3 : (bigW (wOf B) : ℝ)^2 ≤ (B ^ ((1:ℝ)/8))^2 := pow_le_pow_left₀ hWnn hWa 2
      have h4' : (B ^ ((1:ℝ)/8))^2 = B ^ ((1:ℝ)/4) := by
        rw [← Real.rpow_natCast (B ^ ((1:ℝ)/8)) 2, ← Real.rpow_mul (le_of_lt hBpos)]
        norm_num
      exact h3.trans_eq h4'
    have h5 : (L * (bigW (wOf B) : ℝ))^2 = L^2 * (bigW (wOf B) : ℝ)^2 := by ring
    exact h5.trans_le (mul_le_mul_of_nonneg_left h1 (sq_nonneg L))
  have hcomb1 : (∑ᶠ a ∈ primSet d n A (fun _ => True), 1 / eNorm a ^ 2) * (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2) ≤ (K1 * (2 * A ^ (NN d n - 2)) * (1 + 2*L)) * (C2 * B) :=
    mul_le_mul hSa' hSx hSxnn (by positivity)
  have hcomb2 : (L * (bigW (wOf B) : ℝ))^2 * ((∑ᶠ a ∈ primSet d n A (fun _ => True), 1 / eNorm a ^ 2) * (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2)) ≤ (L^2 * B ^ ((1:ℝ)/4)) * ((K1 * (2 * A ^ (NN d n - 2)) * (1 + 2*L)) * (C2 * B)) :=
    mul_le_mul hW2 hcomb1 (mul_nonneg hSann hSxnn) (by positivity)
  have hcomb3 : (1/2) * (L * (bigW (wOf B) : ℝ))^2 * ((∑ᶠ a ∈ primSet d n A (fun _ => True), 1 / eNorm a ^ 2) * (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2)) = (1/2) * ((L * (bigW (wOf B) : ℝ))^2 * ((∑ᶠ a ∈ primSet d n A (fun _ => True), 1 / eNorm a ^ 2) * (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2))) := by ring
  have hcomb : (1/2) * (L * (bigW (wOf B) : ℝ))^2 * ((∑ᶠ a ∈ primSet d n A (fun _ => True), 1 / eNorm a ^ 2) * (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2)) ≤ K1 * C2 * (L^2 * (1 + 2*L)) * B ^ ((1:ℝ)/4) * A ^ (NN d n - 2) * B := by
    have h4'' : (1/2) * ((L * (bigW (wOf B) : ℝ))^2 * ((∑ᶠ a ∈ primSet d n A (fun _ => True), 1 / eNorm a ^ 2) * (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x) ^ 2))) ≤ (1/2) * ((L^2 * B ^ ((1:ℝ)/4)) * ((K1 * (2 * A ^ (NN d n - 2)) * (1 + 2*L)) * (C2 * B))) :=
      mul_le_mul_of_nonneg_left hcomb2 (by norm_num)
    have h5'' : (1/2) * ((L^2 * B ^ ((1:ℝ)/4)) * ((K1 * (2 * A ^ (NN d n - 2)) * (1 + 2*L)) * (C2 * B))) = K1 * C2 * (L^2 * (1 + 2*L)) * B ^ ((1:ℝ)/4) * A ^ (NN d n - 2) * B := by ring
    exact hcomb3.trans_le (h4''.trans_eq h5'')
  have hL3 : L^3 ≤ 1 + L^4 := by
    rcases lt_or_ge L 1 with h | h
    · have h1 : L^3 ≤ 1 := by nlinarith [hLnn, h]
      linarith [pow_nonneg hLnn 4]
    · have h1 : L^3 * L ≥ L^3 * 1 := mul_le_mul_of_nonneg_left h (pow_nonneg hLnn 3)
      have h2 : L^3 * L = L^4 := by rw [pow_succ]; ring
      rw [h2] at h1
      linarith
  have hL4B : L^4 * B ^ ((1:ℝ)/4) ≤ B := by
    have h1 : L^4 * B ^ ((1:ℝ)/4) ≤ B ^ ((3:ℝ)/4) * B ^ ((1:ℝ)/4) := mul_le_mul_of_nonneg_right (h4 B hB04') (Real.rpow_nonneg (by linarith) _)
    have h2 : B ^ ((3:ℝ)/4) * B ^ ((1:ℝ)/4) = B ^ ((3:ℝ)/4 + (1:ℝ)/4) := (Real.rpow_add hBpos _ _).symm
    have h3 : B ^ ((3:ℝ)/4 + (1:ℝ)/4) = B ^ (1:ℝ) := by norm_num
    have h4'' : B ^ (1:ℝ) = B := Real.rpow_one B
    exact h1.trans (le_of_eq (h2.trans (h3.trans h4'')))
  have hB14 : B ^ ((1:ℝ)/4) ≤ B := by
    have h1 : B ^ ((1:ℝ)/4) ≤ B ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num)
    exact h1.trans_eq (Real.rpow_one B)
  have hbig : L^2 * (1 + 2*L) * B ^ ((1:ℝ)/4) * L ≤ 8 * B := by
    have h1 : L^2 * (1 + 2*L) * B ^ ((1:ℝ)/4) * L = (L^3 + 2 * L^4) * B ^ ((1:ℝ)/4) := by ring
    have h2 : (L^3 + 2*L^4) * B ^ ((1:ℝ)/4) = (L^3 * B ^ ((1:ℝ)/4)) + 2 * (L^4 * B ^ ((1:ℝ)/4)) := by ring
    rw [h1, h2]
    have h4' : L^3 * B ^ ((1:ℝ)/4) ≤ (1 + L^4) * B ^ ((1:ℝ)/4) := mul_le_mul_of_nonneg_right hL3 (Real.rpow_nonneg (by linarith) _)
    have h5' : (1 + L^4) * B ^ ((1:ℝ)/4) = B ^ ((1:ℝ)/4) + L^4 * B ^ ((1:ℝ)/4) := by ring
    linarith [h4', h5', hL4B, hB14, Real.rpow_nonneg (by linarith : (0:ℝ) ≤ B) ((1:ℝ)/4)]
  have hKL : K1 * C2 * (L^2 * (1 + 2*L)) * B ^ ((1:ℝ)/4) * L ≤ max 1 (8*K1*C2) * B := by
    have h1 : K1 * C2 * (L^2 * (1 + 2*L)) * B ^ ((1:ℝ)/4) * L = K1 * C2 * (L^2 * (1 + 2*L) * B ^ ((1:ℝ)/4) * L) := by ring
    have h2 : K1 * C2 * (L^2 * (1 + 2*L) * B ^ ((1:ℝ)/4) * L) ≤ K1 * C2 * (8 * B) := mul_le_mul_of_nonneg_left hbig (by positivity)
    have h3 : K1 * C2 * (8 * B) = 8 * K1 * C2 * B := by ring
    have h4' : 8 * K1 * C2 * B ≤ max 1 (8*K1*C2) * B := by
      refine mul_le_mul_of_nonneg_right ?_ hBpos.le
      linarith [le_max_right (1:ℝ) (8*K1*C2)]
    exact h1.trans_le (h2.trans (h3.trans_le h4'))
  have hbase : (0:ℝ) ≤ max 1 (8*K1*C2) := le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_left 1 (8*K1*C2))
  have hkey : K1 * C2 * (L^2 * (1 + 2*L)) * B ^ ((1:ℝ)/4) ≤ max 1 (8*K1*C2) * A := by
    have h3 : K1 * C2 * (L^2 * (1 + 2*L)) * B ^ ((1:ℝ)/4) ≤ max 1 (8*K1*C2) * (B / L) := by
      rw [← mul_div_assoc, le_div_iff₀ hLpos]
      exact hKL
    exact le_trans h3 (mul_le_mul_of_nonneg_left hA hbase)
  have h7 : K1 * C2 * (L^2 * (1 + 2*L)) * B ^ ((1:ℝ)/4) * A ^ (NN d n - 2) * B ≤ max 1 (8*K1*C2) * A * A ^ (NN d n - 2) * B := by
    refine mul_le_mul_of_nonneg_right ?_ hBpos.le
    exact mul_le_mul_of_nonneg_right hkey (pow_nonneg hApos.le _)
  have h8 : max 1 (8*K1*C2) * A * A ^ (NN d n - 2) * B = max 1 (8*K1*C2) * A ^ (NN d n - 1) * B := by
    have hN2 : 2 ≤ NN d n := by have := six_le_NN d n hd hdn; omega
    have h9 : A ^ (NN d n - 1) = A * A ^ (NN d n - 2) := by
      rw [mul_comm, ← pow_succ, show NN d n - 2 + 1 = NN d n - 1 by omega]
    rw [h9]
    ring
  exact le_trans (le_trans hstep hcomb) (le_trans h7 (le_of_eq h8))

end Work.HP
