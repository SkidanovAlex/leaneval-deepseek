import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.FM3.box_count_le
import Submission.Work.HP.ceil_logb_bounds
import Submission.Work.HP.MDBasic.finite_sets

set_option autoImplicit false

noncomputable section

namespace Work.HP.DegSq

open Finset
open scoped BigOperators

/-- A nonzero integer vector has Euclidean norm at least `1`. -/
lemma one_le_eNorm {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : v ≠ 0) : 1 ≤ eNorm v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  have h1 : (1 : ℝ) ≤ |(v i : ℝ)| := by
    have : (1 : ℤ) ≤ |v i| := Int.one_le_abs hi
    exact_mod_cast this
  have h2 : |(v i : ℝ)| ≤ eNorm v := MDBasic.abs_apply_le_eNorm v i
  linarith

/-- Per-point dyadic shell majorant. -/
lemma inv_pow_shell_le (k J : ℕ) (hk : 1 ≤ k) {t : ℝ} (ht1 : 1 ≤ t) (htJ : t ≤ (2:ℝ)^J) :
    1 / t^k ≤ (2:ℝ)^k * ∑ j ∈ Finset.range (J+1),
      (if t ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*k)) else 0) := by
  have ht0 : 0 < t := by linarith
  set j0 : ℕ := ⌈Real.logb 2 t⌉₊ with hj0def
  have hlog : Real.logb 2 t ≤ Real.logb 2 ((2:ℝ)^J) :=
    Real.logb_le_logb_of_le (by norm_num) ht0 htJ
  have hlog2 : Real.logb 2 ((2:ℝ)^J) = (J:ℝ) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; ring
  have hj0le : j0 ≤ J := by
    have h : Real.logb 2 t ≤ (J:ℝ) := by rw [hlog2] at hlog; exact hlog
    have := Nat.ceil_mono h
    simpa [j0, Nat.ceil_natCast] using this
  have hle : t ≤ (2:ℝ)^j0 := ceil_logb_bounds ht1 |>.1
  have hle2 : (2:ℝ)^j0 ≤ 2*t := ceil_logb_bounds ht1 |>.2
  have hmem : j0 ∈ Finset.range (J+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj0le)
  have hnn : ∀ j ∈ Finset.range (J+1),
      (0:ℝ) ≤ (if t ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*k)) else 0) := by
    intro j _
    split_ifs with h
    · positivity
    · rfl
  have hsumbound : ((1/2:ℝ)^(j0*k)) ≤ ∑ j ∈ Finset.range (J+1),
      (if t ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*k)) else 0) := by
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum hnn hmem)
    rw [if_pos hle]
  have h2 : (2:ℝ)^j0 / t ≤ 2 := by
    rw [div_le_iff₀ ht0]; linarith
  have hpow : ((2:ℝ)^j0 / t)^k ≤ (2:ℝ)^k := pow_le_pow_left₀ (by positivity) h2 k
  rw [div_pow, ← pow_mul] at hpow
  have h3 := mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ) ≤ (1/2:ℝ)^(j0*k))
  calc 1 / t^k = ((1/2:ℝ)^(j0*k)) * ((2:ℝ)^(j0*k) / t^k) := by
        rw [← mul_div_assoc, ← mul_pow]; norm_num
    _ ≤ ((1/2:ℝ)^(j0*k)) * (2:ℝ)^k := h3
    _ = (2:ℝ)^k * ((1/2:ℝ)^(j0*k)) := by ring
    _ ≤ (2:ℝ)^k * ∑ j ∈ Finset.range (J+1),
          (if t ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*k)) else 0) :=
        mul_le_mul_of_nonneg_left hsumbound (by positivity)

/-- `⌈logb₂ R⌉ + 1 ≪ 1 + log R`. -/
lemma logb_ceil_bound {R : ℝ} (hR : 1 ≤ R) :
    ((⌈Real.logb 2 R⌉₊ : ℝ) + 1) ≤ (2 / Real.log 2) * (1 + Real.log R) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hlog2le1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hceil : (⌈Real.logb 2 R⌉₊ : ℝ) < Real.logb 2 R + 1 :=
    Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) hR)
  rw [Real.logb] at hceil ⊢
  have hkey : Real.log R / Real.log 2 + 2 ≤ (2 / Real.log 2) * (1 + Real.log R) := by
    have h1 : (Real.log R / Real.log 2 + 2) * Real.log 2 = Real.log R + 2 * Real.log 2 := by
      field_simp
    have h2 : ((2 / Real.log 2) * (1 + Real.log R)) * Real.log 2 = 2 * (1 + Real.log R) := by
      field_simp
    have h3 : Real.log R + 2 * Real.log 2 ≤ 2 * (1 + Real.log R) := by nlinarith
    have h4 : (Real.log R / Real.log 2 + 2) * Real.log 2
        ≤ ((2 / Real.log 2) * (1 + Real.log R)) * Real.log 2 := by rw [h1, h2]; exact h3
    exact le_of_mul_le_mul_right h4 hlog2pos
  linarith

/-- Dyadic geometric sum bound. -/
lemma geom_sum_two_pow_le {d J : ℕ} (hd : 1 ≤ d) :
    (∑ j ∈ Finset.range (J+1), (2:ℝ)^(j*d)) ≤ (2:ℝ)^(d*(J+1)) := by
  have hr2 : (2:ℝ) ≤ (2:ℝ)^d := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hd
  have hr1 : (1:ℝ) ≤ (2:ℝ)^d - 1 := by linarith
  have hrew : (∑ j ∈ Finset.range (J+1), (2:ℝ)^(j*d))
      = ∑ j ∈ Finset.range (J+1), ((2:ℝ)^d)^j := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← pow_mul, Nat.mul_comm]
  have hSnn : (0:ℝ) ≤ ∑ j ∈ Finset.range (J+1), ((2:ℝ)^d)^j :=
    Finset.sum_nonneg (fun j _ => pow_nonneg (by norm_num) _)
  have hg := geom_sum_mul ((2:ℝ)^d) (J+1)
  have hle : (∑ j ∈ Finset.range (J+1), ((2:ℝ)^d)^j) * ((2:ℝ)^d - 1) ≤ ((2:ℝ)^d)^(J+1) := by
    rw [hg]; linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (d*(J+1))]
  have hSle : (∑ j ∈ Finset.range (J+1), ((2:ℝ)^d)^j) ≤ ((2:ℝ)^d)^(J+1) := by
    have h2 := mul_le_mul_of_nonneg_left hr1 hSnn
    linarith [hle, h2]
  rw [hrew]
  calc ∑ j ∈ Finset.range (J+1), ((2:ℝ)^d)^j ≤ ((2:ℝ)^d)^(J+1) := hSle
    _ = (2:ℝ)^(d*(J+1)) := by rw [pow_mul]

/-- `(1/2)^{jk} · 2^{jn} = 2^{j(n-k)}` for `k ≤ n`. -/
lemma half_pow_mul_two_pow {k n j : ℕ} (h : k ≤ n) :
    ((1/2:ℝ)^(j*k)) * (2:ℝ)^(j*n) = (2:ℝ)^(j*(n-k)) := by
  have hjk : j*k ≤ j*n := Nat.mul_le_mul_left j h
  rw [one_div, inv_pow, inv_mul_eq_div, div_eq_mul_inv, ← pow_sub₀ (2:ℝ) (by norm_num) hjk]
  congr 1
  exact (Nat.mul_sub_left_distrib j n k).symm

/-- Counting: a finset of integer vectors whose norm is at most `2^j` has at most `5^n 2^{jn}`
elements. -/
lemma card_le_ball_pow (n j : ℕ) (S : Finset (Fin n → ℤ)) :
    ((S.filter (fun x => eNorm x ≤ (2:ℝ)^j)).card : ℝ) ≤ 5^n * (2:ℝ)^(j*n) := by
  have h0 : (0:ℝ) ≤ (2:ℝ)^j := by positivity
  have h := FM3.box_count_le n S ((2:ℝ)^j) h0
  have h2 : (2 * (2:ℝ)^j + 3) ≤ 5 * (2:ℝ)^j := by
    have h1 : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    linarith
  calc ((S.filter (fun x => eNorm x ≤ (2:ℝ)^j)).card : ℝ)
      ≤ (2 * (2:ℝ)^j + 3)^n := h
    _ ≤ (5 * (2:ℝ)^j)^n := pow_le_pow_left₀ (by positivity) h2 n
    _ = 5^n * (2:ℝ)^(j*n) := by rw [mul_pow, ← pow_mul]

/-- The finset-level dyadic shell bound. -/
lemma finset_sum_inv_pow_shell (n k J : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) {R : ℝ}
    (hRJ : R ≤ (2:ℝ)^J) (S : Finset (Fin n → ℤ)) (hS : ∀ x ∈ S, x ≠ 0 ∧ eNorm x ≤ R) :
    (∑ x ∈ S, 1 / eNorm x^k)
      ≤ (2:ℝ)^k * 5^n * ∑ j ∈ Finset.range (J+1), (2:ℝ)^(j*(n-k)) := by
  have step1 : (∑ x ∈ S, 1 / eNorm x^k)
      ≤ ∑ x ∈ S, (2:ℝ)^k * ∑ j ∈ Finset.range (J+1),
        (if eNorm x ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*k)) else 0) :=
    Finset.sum_le_sum (fun x hx => inv_pow_shell_le k J hk (one_le_eNorm (hS x hx).1)
      (le_trans (hS x hx).2 hRJ))
  have step4 : ∀ j ∈ Finset.range (J+1),
      (∑ x ∈ S, (if eNorm x ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*k)) else 0))
        = ((1/2:ℝ)^(j*k)) * ((S.filter (fun x => eNorm x ≤ (2:ℝ)^j)).card : ℝ) := by
    intro j _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hper : ∀ j, ((1/2:ℝ)^(j*k)) * (5^n * (2:ℝ)^(j*n)) = 5^n * (2:ℝ)^(j*(n-k)) := by
    intro j
    calc ((1/2:ℝ)^(j*k)) * (5^n * (2:ℝ)^(j*n))
        = 5^n * (((1/2:ℝ)^(j*k)) * (2:ℝ)^(j*n)) := by ring
      _ = 5^n * (2:ℝ)^(j*(n-k)) := by rw [half_pow_mul_two_pow hkn]
  calc (∑ x ∈ S, 1 / eNorm x^k)
      ≤ ∑ x ∈ S, (2:ℝ)^k * ∑ j ∈ Finset.range (J+1),
        (if eNorm x ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*k)) else 0) := step1
    _ = (2:ℝ)^k * ∑ x ∈ S, ∑ j ∈ Finset.range (J+1),
        (if eNorm x ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*k)) else 0) :=
        (Finset.mul_sum _ _ _).symm
    _ = (2:ℝ)^k * ∑ j ∈ Finset.range (J+1), ∑ x ∈ S,
        (if eNorm x ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*k)) else 0) := by rw [Finset.sum_comm]
    _ = (2:ℝ)^k * ∑ j ∈ Finset.range (J+1),
        ((1/2:ℝ)^(j*k)) * ((S.filter (fun x => eNorm x ≤ (2:ℝ)^j)).card : ℝ) := by
        congr 1
        exact Finset.sum_congr rfl step4
    _ ≤ (2:ℝ)^k * ∑ j ∈ Finset.range (J+1),
        ((1/2:ℝ)^(j*k)) * (5^n * (2:ℝ)^(j*n)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (by positivity)
        intro j _
        exact mul_le_mul_of_nonneg_left (card_le_ball_pow n j S) (by positivity)
    _ = (2:ℝ)^k * (5^n * ∑ j ∈ Finset.range (J+1), (2:ℝ)^(j*(n-k))) := by
        congr 1
        rw [Finset.sum_congr rfl (fun j _ => hper j), ← Finset.mul_sum]
    _ = (2:ℝ)^k * 5^n * ∑ j ∈ Finset.range (J+1), (2:ℝ)^(j*(n-k)) := by ring

/-- Finsum form of the shell bound. -/
lemma ball_finsum_le_shell (n k J : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) {R : ℝ} (hR : 1 ≤ R)
    (hRJ : R ≤ (2:ℝ)^J) :
    (∑ᶠ x ∈ ({v : Fin n → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (Fin n → ℤ)), 1 / eNorm x^k)
      ≤ (2:ℝ)^k * 5^n * ∑ j ∈ Finset.range (J+1), (2:ℝ)^(j*(n-k)) := by
  let S : Set (Fin n → ℤ) := {v | v ≠ 0 ∧ eNorm v ≤ R}
  have hsub : S ⊆ ((Fintype.piFinset
      (fun _ : Fin n => Finset.Icc (-(Nat.ceil R : ℤ)) (Nat.ceil R : ℤ))) : Set (Fin n → ℤ)) := by
    intro v hv
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h1 : |(v i : ℝ)| ≤ eNorm v := MDBasic.abs_apply_le_eNorm v i
    have h2 : |(v i : ℝ)| ≤ R := le_trans h1 hv.2
    have h3 : |(v i : ℝ)| ≤ (Nat.ceil R : ℝ) := le_trans h2 (Nat.le_ceil R)
    exact ⟨by exact_mod_cast (abs_le.mp h3).1, by exact_mod_cast (abs_le.mp h3).2⟩
  have hsupp : Function.support (Set.indicator S (fun x : Fin n → ℤ => 1 / eNorm x^k))
      ⊆ ((Fintype.piFinset
      (fun _ : Fin n => Finset.Icc (-(Nat.ceil R : ℤ)) (Nat.ceil R : ℤ))) : Set (Fin n → ℤ)) := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxT
    exact hx (Set.indicator_of_notMem (fun hxS => hxT (hsub hxS)) _)
  show (∑ᶠ x ∈ S, 1 / eNorm x^k) ≤ _
  rw [finsum_mem_def S (fun x : Fin n → ℤ => 1 / eNorm x^k),
      finsum_eq_finsetSum_of_support_subset _ hsupp]
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter]
  exact finset_sum_inv_pow_shell n k J hk hkn hRJ _
    (fun x hx => (Finset.mem_filter.mp hx).2)

theorem ball_sum_inv_pow (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (k : ℕ), 1 ≤ k → ∀ R : ℝ, 1 ≤ R →
      (∑ᶠ x ∈ ({v : Fin m → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (Fin m → ℤ)),
        1 / eNorm x ^ k)
        ≤ K * (1 + Real.log R) * (1 + R ^ (m - k)) := by
  rcases m with _ | N
  · refine ⟨1, one_pos, ?_⟩
    intro k hk R hR
    have hempty : ({v : Fin 0 → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (Fin 0 → ℤ)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro v hv
      exact hv.1 (Subsingleton.elim v 0)
    rw [hempty, finsum_mem_empty]
    have h1 : (0:ℝ) ≤ Real.log R := Real.log_nonneg hR
    have h2 : (0:ℝ) ≤ R ^ (0 - k) := by positivity
    nlinarith [h1, h2]
  · refine ⟨(2:ℝ)^(N+1) * 5^(N+1) * (4^(N+1) + 1/Real.log 2), ?_, ?_⟩
    · have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    · intro k hk R hR
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
      have hRJ : R ≤ (2:ℝ)^⌈Real.logb 2 R⌉₊ := (ceil_logb_bounds hR).1
      have h2R : (2:ℝ)^⌈Real.logb 2 R⌉₊ ≤ 2 * R := (ceil_logb_bounds hR).2
      by_cases hkn : k ≤ N + 1
      · rcases lt_or_eq_of_le hkn with hlt | heq
        · -- k < N+1
          have hd : 1 ≤ (N+1) - k := by omega
          have hmain := ball_finsum_le_shell (N+1) k ⌈Real.logb 2 R⌉₊ hk (le_of_lt hlt) hR hRJ
          have hgeom : (∑ j ∈ Finset.range (⌈Real.logb 2 R⌉₊ + 1), (2:ℝ)^(j*((N+1)-k)))
              ≤ (2:ℝ)^(((N+1)-k)*(⌈Real.logb 2 R⌉₊+1)) := geom_sum_two_pow_le hd
          have hpow : (2:ℝ)^(((N+1)-k)*(⌈Real.logb 2 R⌉₊+1)) ≤ 4^(N+1) * R^((N+1)-k) := by
            have hdJ : (2:ℝ)^(((N+1)-k)*(⌈Real.logb 2 R⌉₊+1))
                = ((2:ℝ)^(⌈Real.logb 2 R⌉₊+1)) ^ ((N+1)-k) := by
              rw [← pow_mul]; congr 1; ring
            rw [hdJ]
            have h2J1 : (2:ℝ)^(⌈Real.logb 2 R⌉₊+1) ≤ 4*R := by
              rw [pow_succ]
              nlinarith [h2R, hlogR, hR]
            calc ((2:ℝ)^(⌈Real.logb 2 R⌉₊+1)) ^ ((N+1)-k) ≤ (4*R)^((N+1)-k) :=
                  pow_le_pow_left₀ (by positivity) h2J1 _
              _ = 4^((N+1)-k) * R^((N+1)-k) := by rw [mul_pow]
              _ ≤ 4^(N+1) * R^((N+1)-k) := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  exact pow_le_pow_right₀ (by norm_num) (by omega : (N+1)-k ≤ N+1)
          have h4n : (0:ℝ) ≤ 4^(N+1) := by positivity
          have hRd : (0:ℝ) ≤ R^((N+1)-k) := by positivity
          have hCn : (0:ℝ) ≤ 5^(N+1) := by positivity
          have hlogR1 : (1:ℝ) ≤ 1 + Real.log R := by linarith
          have hX : R^((N+1)-k) ≤ (1 + Real.log R) * (1 + R^((N+1)-k)) := by
            have h2 : R^((N+1)-k) ≤ 1 + R^((N+1)-k) := by linarith
            calc R^((N+1)-k) = 1 * R^((N+1)-k) := (one_mul _).symm
              _ ≤ (1 + Real.log R) * (1 + R^((N+1)-k)) :=
                  mul_le_mul hlogR1 h2 hRd (by linarith)
          have hkey2 : (4:ℝ)^(N+1) ≤ 4^(N+1) + 1/Real.log 2 := by
            have := one_div_pos.mpr hlog2pos; linarith
          calc (∑ᶠ x ∈ ({v : Fin (N+1) → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (Fin (N+1) → ℤ)),
                1 / eNorm x^k)
              ≤ (2:ℝ)^k * 5^(N+1) * ∑ j ∈ Finset.range (⌈Real.logb 2 R⌉₊ + 1),
                  (2:ℝ)^(j*((N+1)-k)) := hmain
            _ ≤ (2:ℝ)^k * 5^(N+1) * (2:ℝ)^(((N+1)-k)*(⌈Real.logb 2 R⌉₊+1)) := by
                refine mul_le_mul_of_nonneg_left hgeom (by positivity)
            _ ≤ (2:ℝ)^k * 5^(N+1) * (4^(N+1) * R^((N+1)-k)) := by
                refine mul_le_mul_of_nonneg_left hpow (by positivity)
            _ ≤ (2:ℝ)^(N+1) * 5^(N+1) * (4^(N+1) * R^((N+1)-k)) := by
                refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hCn)
                  (by positivity)
                exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hkn
            _ ≤ ((2:ℝ)^(N+1) * 5^(N+1) * (4^(N+1) + 1/Real.log 2))
                  * (1 + Real.log R) * (1 + R^((N+1)-k)) := by
                have hKnn : (0:ℝ) ≤ 4^(N+1) + 1/Real.log 2 := by
                  have := one_div_pos.mpr hlog2pos; linarith
                have hs2 : (2:ℝ)^(N+1) * 5^(N+1) * (4^(N+1) * R^((N+1)-k))
                    ≤ (2:ℝ)^(N+1) * 5^(N+1)
                        * ((4^(N+1) + 1/Real.log 2) * R^((N+1)-k)) := by
                  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                  exact mul_le_mul_of_nonneg_right (by linarith) hRd
                have hs3 : (2:ℝ)^(N+1) * 5^(N+1)
                        * ((4^(N+1) + 1/Real.log 2) * R^((N+1)-k))
                    ≤ (2:ℝ)^(N+1) * 5^(N+1) * ((4^(N+1) + 1/Real.log 2)
                        * ((1 + Real.log R) * (1 + R^((N+1)-k)))) := by
                  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                  exact mul_le_mul_of_nonneg_left hX hKnn
                have hs4 : (2:ℝ)^(N+1) * 5^(N+1) * ((4^(N+1) + 1/Real.log 2)
                        * ((1 + Real.log R) * (1 + R^((N+1)-k))))
                    = ((2:ℝ)^(N+1) * 5^(N+1) * (4^(N+1) + 1/Real.log 2))
                      * (1 + Real.log R) * (1 + R^((N+1)-k)) := by ring
                exact le_trans hs2 (le_trans hs3 (le_of_eq hs4))
        · -- k = N+1
          subst heq
          have hmain := ball_finsum_le_shell (N+1) (N+1) ⌈Real.logb 2 R⌉₊ (by omega) le_rfl hR hRJ
          have hsum : (∑ j ∈ Finset.range (⌈Real.logb 2 R⌉₊ + 1), (2:ℝ)^(j*((N+1)-(N+1))))
              = ((⌈Real.logb 2 R⌉₊ : ℝ) + 1) := by
            simp only [Nat.sub_self, Nat.mul_zero, pow_zero, Finset.sum_const, Finset.card_range,
              nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
          rw [hsum] at hmain
          have hlog := logb_ceil_bound hR
          have hKL : (0:ℝ) ≤ 1 + Real.log R := by linarith
          have hAn : (0:ℝ) ≤ (2:ℝ)^(N+1) * 5^(N+1) := by positivity
          have hkey2 : (2:ℝ)/Real.log 2 ≤ 2 * (4^(N+1) + 1/Real.log 2) := by
            rw [div_eq_mul_inv, one_div]
            nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4) (n := N+1)]
          calc (∑ᶠ x ∈ ({v : Fin (N+1) → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (Fin (N+1) → ℤ)),
                1 / eNorm x^(N+1))
              ≤ (2:ℝ)^(N+1) * 5^(N+1) * ((⌈Real.logb 2 R⌉₊ : ℝ) + 1) := hmain
            _ ≤ (2:ℝ)^(N+1) * 5^(N+1) * ((2/Real.log 2) * (1 + Real.log R)) := by
                refine mul_le_mul_of_nonneg_left hlog (by positivity)
            _ ≤ ((2:ℝ)^(N+1) * 5^(N+1) * (4^(N+1) + 1/Real.log 2))
                  * (1 + Real.log R) * (1 + R^((N+1)-(N+1))) := by
                rw [show N + 1 - (N + 1) = 0 from Nat.sub_self _, pow_zero]
                calc (2:ℝ)^(N+1) * 5^(N+1) * ((2/Real.log 2) * (1 + Real.log R))
                    = (2^(N+1) * 5^(N+1)) * (2/Real.log 2) * (1 + Real.log R) := by ring
                  _ ≤ (2^(N+1) * 5^(N+1)) * (2 * (4^(N+1) + 1/Real.log 2))
                        * (1 + Real.log R) := by
                      refine mul_le_mul_of_nonneg_right ?_ hKL
                      exact mul_le_mul_of_nonneg_left hkey2 hAn
                  _ = ((2:ℝ)^(N+1) * 5^(N+1) * (4^(N+1) + 1/Real.log 2))
                        * (1 + Real.log R) * (1 + 1) := by ring
      · -- k > N+1
        push_neg at hkn
        have hSfin : ({v : Fin (N+1) → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (Fin (N+1) → ℤ)).Finite :=
          (MDBasic.finite_eNorm_le R).subset (fun v hv => hv.2)
        have hsub : (∑ᶠ x ∈ ({v : Fin (N+1) → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (Fin (N+1) → ℤ)),
              1 / eNorm x^k)
            ≤ (∑ᶠ x ∈ ({v : Fin (N+1) → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (Fin (N+1) → ℤ)),
              1 / eNorm x^(N+1)) := by
          rw [finsum_mem_def, finsum_mem_def]
          refine finsum_le_finsum ?_ ?_ ?_
          · exact hSfin.subset (fun x hx => by
              rw [Function.mem_support] at hx
              by_contra hxS
              exact hx (Set.indicator_of_notMem hxS _))
          · exact hSfin.subset (fun x hx => by
              rw [Function.mem_support] at hx
              by_contra hxS
              exact hx (Set.indicator_of_notMem hxS _))
          · intro x
            by_cases hxS : x ∈ ({v : Fin (N+1) → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (Fin (N+1) → ℤ))
            · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem hxS]
              have hxe : 1 ≤ eNorm x := one_le_eNorm hxS.1
              have hpow : eNorm x^(N+1) ≤ eNorm x^k :=
                pow_le_pow_right₀ hxe (by omega)
              exact one_div_le_one_div_of_le (by positivity) hpow
            · rw [Set.indicator_of_notMem hxS, Set.indicator_of_notMem hxS]
        have hmain := ball_finsum_le_shell (N+1) (N+1) ⌈Real.logb 2 R⌉₊ (by omega) le_rfl hR hRJ
        have hsum : (∑ j ∈ Finset.range (⌈Real.logb 2 R⌉₊ + 1), (2:ℝ)^(j*((N+1)-(N+1))))
            = ((⌈Real.logb 2 R⌉₊ : ℝ) + 1) := by
          simp only [Nat.sub_self, Nat.mul_zero, pow_zero, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
        rw [hsum] at hmain
        have hlog := logb_ceil_bound hR
        have hKL : (0:ℝ) ≤ 1 + Real.log R := by linarith
        have hAn : (0:ℝ) ≤ (2:ℝ)^(N+1) * 5^(N+1) := by positivity
        have hkey2 : (2:ℝ)/Real.log 2 ≤ 2 * (4^(N+1) + 1/Real.log 2) := by
          rw [div_eq_mul_inv, one_div]
          nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4) (n := N+1)]
        have hmid : (∑ᶠ x ∈ ({v : Fin (N+1) → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (Fin (N+1) → ℤ)),
              1 / eNorm x^(N+1))
            ≤ ((2:ℝ)^(N+1) * 5^(N+1) * (4^(N+1) + 1/Real.log 2))
                * (1 + Real.log R) * (1 + R^((N+1)-(N+1))) := by
          calc (∑ᶠ x ∈ ({v : Fin (N+1) → ℤ | v ≠ 0 ∧ eNorm v ≤ R} : Set (Fin (N+1) → ℤ)),
                1 / eNorm x^(N+1))
              ≤ (2:ℝ)^(N+1) * 5^(N+1) * ((⌈Real.logb 2 R⌉₊ : ℝ) + 1) := hmain
            _ ≤ (2:ℝ)^(N+1) * 5^(N+1) * ((2/Real.log 2) * (1 + Real.log R)) := by
                refine mul_le_mul_of_nonneg_left hlog (by positivity)
            _ ≤ ((2:ℝ)^(N+1) * 5^(N+1) * (4^(N+1) + 1/Real.log 2))
                  * (1 + Real.log R) * (1 + R^((N+1)-(N+1))) := by
                rw [show N + 1 - (N + 1) = 0 from Nat.sub_self _, pow_zero]
                calc (2:ℝ)^(N+1) * 5^(N+1) * ((2/Real.log 2) * (1 + Real.log R))
                    = (2^(N+1) * 5^(N+1)) * (2/Real.log 2) * (1 + Real.log R) := by ring
                  _ ≤ (2^(N+1) * 5^(N+1)) * (2 * (4^(N+1) + 1/Real.log 2))
                        * (1 + Real.log R) := by
                      refine mul_le_mul_of_nonneg_right ?_ hKL
                      exact mul_le_mul_of_nonneg_left hkey2 hAn
                  _ = ((2:ℝ)^(N+1) * 5^(N+1) * (4^(N+1) + 1/Real.log 2))
                        * (1 + Real.log R) * (1 + 1) := by ring
        refine le_trans hsub (le_trans hmid ?_)
        have hd1 : N + 1 - (N + 1) = 0 := Nat.sub_self _
        have hd2 : N + 1 - k = 0 := Nat.sub_eq_zero_of_le (le_of_lt hkn)
        rw [hd1, hd2, pow_zero]

end Work.HP.DegSq
