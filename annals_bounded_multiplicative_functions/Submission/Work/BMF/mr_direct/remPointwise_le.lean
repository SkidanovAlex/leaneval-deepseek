import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.remPointwise_defs
import Submission.Work.BMF.mr_direct.nat_cpow_I_norm_le
import Submission.Work.BMF.liouville.dist_algebra
import Submission.Work.BMF.mr_direct.halasz_window_twist

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open BoundedMultiplicativeFunctions
open MeasureTheory intervalIntegral
open scoped BigOperators ComplexConjugate

noncomputable section

/-- `ω(p;P,Q)` for a prime `p` is `1` exactly when `P ≤ p ≤ Q`. -/
private lemma omegaCount_prime (P Q : ℝ) {p : ℕ} (hp : p.Prime) :
    Work.BMF.mrDirect.omegaCount P Q p
      = (if P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q then 1 else 0) := by
  unfold Work.BMF.mrDirect.omegaCount
  have hset : (Finset.Icc 1 p).filter
        (fun q : ℕ => q.Prime ∧ P ≤ (q : ℝ) ∧ (q : ℝ) ≤ Q ∧ q ∣ p)
      = (if P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q then {p} else ∅) := by
    by_cases hc : P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q
    · rw [if_pos hc]
      ext q
      rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1q, hqp⟩, hqprime, hPq, hqQ, hqdp⟩
        exact (Nat.prime_dvd_prime_iff_eq hqprime hp).mp hqdp
      · rintro rfl
        exact ⟨⟨hp.one_le, le_rfl⟩, hp, hc.1, hc.2, dvd_rfl⟩
    · rw [if_neg hc]
      ext q
      constructor
      · intro hq
        rw [Finset.mem_filter, Finset.mem_Icc] at hq
        obtain ⟨⟨h1q, hqp⟩, hqprime, hPq, hqQ, hqdp⟩ := hq
        have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hp).mp hqdp
        exact absurd ⟨hqeq ▸ hPq, hqeq ▸ hqQ⟩ hc
      · intro hq
        exact ((Finset.notMem_empty q) hq).elim
  rw [hset]
  split_ifs with hc
  · simp
  · simp

/-- `ω(·;P,Q)` is additive on coprime arguments. -/
private lemma omegaCount_coprime_add (P Q : ℝ) {m n : ℕ} (h : m.Coprime n) :
    Work.BMF.mrDirect.omegaCount P Q (m * n)
      = Work.BMF.mrDirect.omegaCount P Q m + Work.BMF.mrDirect.omegaCount P Q n := by
  unfold Work.BMF.mrDirect.omegaCount
  set B : Finset ℕ := (Finset.Icc 1 m).filter
    (fun p : ℕ => p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ p ∣ m) with hB
  set C : Finset ℕ := (Finset.Icc 1 n).filter
    (fun p : ℕ => p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ p ∣ n) with hC
  have hsplit : (Finset.Icc 1 (m * n)).filter
        (fun p : ℕ => p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ p ∣ m * n)
      = B ∪ C := by
    ext p
    simp only [hB, hC, Finset.mem_filter, Finset.mem_Icc, Finset.mem_union]
    constructor
    · rintro ⟨⟨h1p, hpmn⟩, hpp, hPp, hpQ, hpdvd⟩
      have hp2 : 2 ≤ p := hpp.two_le
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with hm | hm
        · rw [hm, Nat.zero_mul] at hpmn; omega
        · exact hm
      have hnpos : 0 < n := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · rw [hn, Nat.mul_zero] at hpmn; omega
        · exact hn
      rcases hpp.dvd_mul.mp hpdvd with hpm | hpn
      · exact Or.inl ⟨⟨h1p, Nat.le_of_dvd hmpos hpm⟩, hpp, hPp, hpQ, hpm⟩
      · exact Or.inr ⟨⟨h1p, Nat.le_of_dvd hnpos hpn⟩, hpp, hPp, hpQ, hpn⟩
    · rintro (⟨⟨h1p, hpm⟩, hpp, hPp, hpQ, hpm'⟩ | ⟨⟨h1p, hpn⟩, hpp, hPp, hpQ, hpn'⟩)
      · have hn1 : 1 ≤ n := by
          rcases Nat.eq_zero_or_pos n with hn | hn
          · subst hn
            have hm1 : m = 1 := (Nat.coprime_zero_right m).mp h
            have hp2 : 2 ≤ p := hpp.two_le
            omega
          · exact hn
        exact ⟨⟨h1p, le_trans hpm (Nat.le_mul_of_pos_right m hn1)⟩,
          hpp, hPp, hpQ, dvd_mul_of_dvd_left hpm' n⟩
      · have hm1 : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with hm | hm
          · subst hm
            have hn1 : n = 1 := (Nat.coprime_zero_left n).mp h
            have hp2 : 2 ≤ p := hpp.two_le
            omega
          · exact hm
        exact ⟨⟨h1p, le_trans hpn (Nat.le_mul_of_pos_left n hm1)⟩,
          hpp, hPp, hpQ, dvd_mul_of_dvd_right hpn' m⟩
  have hdisj : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro p hpB hpC
    rw [hB, Finset.mem_filter] at hpB
    rw [hC, Finset.mem_filter] at hpC
    obtain ⟨_, hpp, _, _, hpm⟩ := hpB
    obtain ⟨_, _, _, _, hpn⟩ := hpC
    have hdiv1 : p ∣ 1 := h ▸ Nat.dvd_gcd hpm hpn
    have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) hdiv1
    have hp2 : 2 ≤ p := hpp.two_le
    omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj]

/-- `ω(1;P,Q) = 0`. -/
private lemma omegaCount_one (P Q : ℝ) : Work.BMF.mrDirect.omegaCount P Q 1 = 0 := by
  have h := omegaCount_coprime_add P Q (m := 1) (n := 1) (Nat.coprime_one_left 1)
  rw [Nat.mul_one] at h
  omega

/-- Membership in `primesIn P Q` for a prime. -/
private lemma mem_primesIn_iffP (P Q : ℝ) {p : ℕ} (hp : p.Prime) :
    p ∈ Work.BMF.primesIn P Q ↔ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q := by
  simp only [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, _⟩
    have hQ0 : 0 ≤ Q := by
      by_contra h
      push_neg at h
      have hfz : ⌊Q⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      rw [hfz] at h2
      have hp2 : 2 ≤ p := hp.two_le
      omega
    exact ⟨le_trans (Nat.le_ceil P) (by exact_mod_cast h1),
      le_trans (by exact_mod_cast h2) (Nat.floor_le hQ0)⟩
  · rintro ⟨hP, hQ⟩
    exact ⟨⟨(Nat.ceil_le).mpr hP, Nat.le_floor hQ⟩, hp⟩

/-- Pointwise value of the `ω`-weight at a prime. -/
private lemma omegaWeighted_apply_prime (g : ℕ → ℂ) (P Q : ℝ) (x : ℂ) {p : ℕ} (hp : p.Prime) :
    omegaWeighted g P Q x p = (if P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q then x else 1) * g p := by
  unfold omegaWeighted omegaPow
  rw [omegaCount_prime P Q hp]
  split_ifs with hc
  · rw [pow_one]
  · rw [pow_zero]

/-- `omegaWeighted g P Q x` is multiplicative for multiplicative `g`. -/
lemma omegaWeighted_mul (g : ℕ → ℂ) (P Q : ℝ) (x : ℂ)
    (hg : ∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) :
    ∀ m n : ℕ, m.Coprime n →
      omegaWeighted g P Q x (m * n) = omegaWeighted g P Q x m * omegaWeighted g P Q x n := by
  intro m n hmn
  unfold omegaWeighted omegaPow
  rw [omegaCount_coprime_add P Q hmn, hg m n hmn, pow_add]
  ring

/-- `omegaWeighted g P Q x 1 = 1` when `g 1 = 1`. -/
lemma omegaWeighted_one (g : ℕ → ℂ) (P Q : ℝ) (x : ℂ) (hg1 : g 1 = 1) :
    omegaWeighted g P Q x 1 = 1 := by
  unfold omegaWeighted omegaPow
  rw [omegaCount_one, pow_zero, one_mul, hg1]

/-- `m ↦ r^{ω(m;P,Q)} g m` is `1`-bounded for `0 ≤ r ≤ 1` and `‖g‖ ≤ 1`. -/
lemma omegaWeighted_oneBounded (g : ℕ → ℂ) (P Q : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hg : ∀ n, ‖g n‖ ≤ 1) : ∀ n, ‖omegaWeighted g P Q (r : ℂ) n‖ ≤ 1 := by
  intro n
  unfold omegaWeighted omegaPow
  rw [norm_mul]
  have hx : ‖((r : ℝ) : ℂ) ^ Work.BMF.mrDirect.omegaCount P Q n‖ ≤ 1 := by
    rw [norm_pow, Complex.norm_of_nonneg hr0]
    exact pow_le_one₀ hr0 hr1
  calc ‖((r : ℝ) : ℂ) ^ Work.BMF.mrDirect.omegaCount P Q n‖ * ‖g n‖
      ≤ 1 * 1 := mul_le_mul hx (hg n) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1


/-- The `ω`-weighting costs at most `Σ_{p ∈ [P,Q]} 1/p` in the pretentious distance. -/
lemma omegaWeighted_dist_lower (g : ℕ → ℂ) (P Q B r y w : ℝ)
    (hg : ∀ n, ‖g n‖ ≤ 1) (hB : 0 ≤ B) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hL : ∑ p ∈ Work.BMF.primesIn P Q, (1 : ℝ) / (p : ℝ) ≤ B ^ 2 / 8)
    (hdist : B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * w)) y) :
    7 * B ^ 2 / 8 ≤
      BoundedMultiplicativeFunctions.𝔻 (omegaWeighted g P Q (r : ℂ))
        (fun n ↦ (n : ℂ) ^ (Complex.I * w)) y ^ 2 := by
  set χ : ℕ → ℂ := fun n ↦ (n : ℂ) ^ (Complex.I * w) with hχ
  have hgb : IsOneBounded g := hg
  have hχb : IsOneBounded χ := fun n => by rw [hχ]; exact nat_cpow_I_norm_le n w
  have hfb : IsOneBounded (omegaWeighted g P Q (r : ℂ)) :=
    omegaWeighted_oneBounded g P Q hr0 hr1 hg
  have hg2 := Work.BMF.liouville.dist_algebra.1 g χ y hgb hχb
  have hf2 := Work.BMF.liouville.dist_algebra.1 (omegaWeighted g P Q (r : ℂ)) χ y hfb hχb
  have hstep : ∀ p ∈ ⌊y⌋₊.primesLE,
      (1 - (g p * conj (χ p)).re) / (p : ℝ) ≤
        (1 - (omegaWeighted g P Q (r : ℂ) p * conj (χ p)).re) / (p : ℝ) +
          (if p ∈ Work.BMF.primesIn P Q then (1 : ℝ) / (p : ℝ) else 0) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
    have hppos : (0 : ℝ) < (p : ℝ) := by
      have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
      linarith
    have hnorm : ‖g p * conj (χ p)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_conj]
      calc ‖g p‖ * ‖χ p‖ ≤ 1 * 1 := mul_le_mul (hg p) (hχb p) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hzlow : -1 ≤ (g p * conj (χ p)).re := by
      have h := Complex.re_le_norm (-(g p * conj (χ p)))
      rw [Complex.neg_re, norm_neg] at h
      linarith
    by_cases hc : P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q
    · have hval : omegaWeighted g P Q (r : ℂ) p = (r : ℂ) * g p := by
        rw [omegaWeighted_apply_prime g P Q (r:ℂ) hpp, if_pos hc]
      have hre : (omegaWeighted g P Q (r : ℂ) p * conj (χ p)).re
          = r * (g p * conj (χ p)).re := by
        rw [hval]
        have hrr : (r:ℂ) * g p * conj (χ p) = (r:ℂ) * (g p * conj (χ p)) := by ring
        rw [hrr, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring
      have hmem : p ∈ Work.BMF.primesIn P Q := (mem_primesIn_iffP P Q hpp).mpr hc
      rw [hre, if_pos hmem, ← add_div]
      apply div_le_div_of_nonneg_right _ hppos.le
      have hkey : (r - 1) * (g p * conj (χ p)).re ≤ 1 := by
        have h1 : (r - 1) * (g p * conj (χ p)).re ≤ (r - 1) * (-1) :=
          mul_le_mul_of_nonpos_left hzlow (by linarith)
        linarith
      nlinarith [hkey]
    · have hval : omegaWeighted g P Q (r : ℂ) p = g p := by
        rw [omegaWeighted_apply_prime g P Q (r:ℂ) hpp, if_neg hc, one_mul]
      have hnotmem : p ∉ Work.BMF.primesIn P Q := fun hh => hc ((mem_primesIn_iffP P Q hpp).mp hh)
      rw [hval, if_neg hnotmem, add_zero]
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib] at hsum
  have hitesum : (∑ p ∈ ⌊y⌋₊.primesLE,
        (if p ∈ Work.BMF.primesIn P Q then (1 : ℝ) / (p : ℝ) else 0))
      ≤ ∑ p ∈ Work.BMF.primesIn P Q, (1 : ℝ) / (p : ℝ) := by
    rw [← Finset.sum_filter]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.mp hp).2)
      (fun i _ _ => by positivity)
  rw [hf2]
  have hB2 : B ^ 2 ≤ BoundedMultiplicativeFunctions.𝔻 g χ y ^ 2 := pow_le_pow_left₀ hB hdist 2
  rw [hg2] at hB2
  linarith [hsum, hitesum, hL, hB2]

/-- `∫_0^1 x^k dx = (k+1)^{-1}` for the complex power. -/
lemma integral_cpow_nat (k : ℕ) : ∫ x in (0 : ℝ)..1, (x : ℂ) ^ k = (((k : ℂ)) + 1)⁻¹ := by
  have h1 : ∀ x : ℝ, (x : ℂ) ^ k = ((x ^ k : ℝ) : ℂ) := fun x => (Complex.ofReal_pow x k).symm
  simp_rw [h1]
  rw [intervalIntegral.integral_ofReal, integral_pow]
  have h0 : (0:ℝ) ^ (k+1) = 0 := zero_pow (by omega)
  rw [h0, one_pow, sub_zero, one_div, Complex.ofReal_inv]
  congr 1
  push_cast
  ring

/-- The weighted window sum is the integral over `x ∈ [0,1]` of the `x^{ω}`-weighted window
sum. -/
lemma omegaWeighted_sum_eq_integral (g : ℕ → ℂ) (P Q X t : ℝ) :
    (∑ m ∈ Work.BMF.natIcc X (2 * X),
        g m * ((((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ))⁻¹ *
          (m : ℂ) ^ (-(1 + Complex.I * t)))
      = ∫ x in (0 : ℝ)..1, omegaWindowSum g P Q X t (x : ℂ) := by
  unfold omegaWindowSum
  have hint : ∀ m ∈ Work.BMF.natIcc X (2 * X), IntervalIntegrable
      (fun x : ℝ => omegaWeighted g P Q (x : ℂ) m * (m : ℂ) ^ (-(1 + Complex.I * t)))
      volume (0 : ℝ) 1 := by
    intro m hm
    apply Continuous.intervalIntegrable
    unfold omegaWeighted omegaPow
    continuity
  rw [intervalIntegral.integral_finset_sum hint]
  apply Finset.sum_congr rfl
  intro m hm
  have hrw : ∀ x : ℝ, omegaWeighted g P Q (x : ℂ) m * (m : ℂ) ^ (-(1 + Complex.I * t))
      = (x : ℂ) ^ (Work.BMF.mrDirect.omegaCount P Q m) *
          (g m * (m : ℂ) ^ (-(1 + Complex.I * t))) := by
    intro x; unfold omegaWeighted omegaPow; ring
  simp_rw [hrw]
  rw [intervalIntegral.integral_mul_const (g m * (m : ℂ) ^ (-(1 + Complex.I * t))),
    integral_cpow_nat]
  have hc : ((Work.BMF.mrDirect.omegaCount P Q m : ℂ) + 1)
      = ((((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ) := by push_cast; ring
  rw [hc]
  ring

/-- **The pointwise remainder bound.** -/
theorem remPointwise_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 1 ≤ B →
      ∀ (g : ℕ → ℂ) (P Q X T₀ t : ℝ),
        g 1 = 1 → (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) →
        (∀ n, ‖g n‖ ≤ 1) → 2 ≤ P → P ≤ Q → 16 ≤ X → 1 ≤ T₀ →
        (∀ (x : ℝ), X ^ (1/4:ℝ) / 16 ≤ x → x ≤ 16 * X → ∀ u : ℝ, |u| ≤ 4 * T₀ →
          B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) x) →
        (∑ p ∈ Work.BMF.primesIn P Q, 1 / (p : ℝ)) ≤ B ^ 2 / 8 →
        |t| ≤ 2 * T₀ →
        ‖∑ m ∈ Work.BMF.natIcc X (2 * X),
            g m * (((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
              (m : ℂ) ^ (-(1 + Complex.I * t))‖
          ≤ C * (Real.log Q / Real.log P) *
              ((1 + B ^ 2) * Real.exp (-(B ^ 2 / 4)) + 1 / Real.sqrt T₀) := by
  obtain ⟨Cw, hCw, hw⟩ := halasz_window_twist
  refine ⟨Cw, hCw, ?_⟩
  intro B hB1 g P Q X T₀ t hg1 hgmul hgb hP hPQ hX hT0 hdist hL ht
  set M₀ : ℝ := 7 * B ^ 2 / 8 with hM₀
  have hM0pos : 0 < M₀ := by rw [hM₀]; nlinarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith : 1 < P)
  have hlog1 : 1 ≤ Real.log Q / Real.log P := by
    rw [one_le_div hlogP]
    exact Real.log_le_log (by linarith : 0 < P) hPQ
  have hXr : X ^ (1/4:ℝ) ≤ 4 * X := by
    have h1 := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ X by linarith)
      (show (1/4:ℝ) ≤ 1 by norm_num)
    rw [Real.rpow_one] at h1
    linarith
  have hF : ∀ x ∈ Set.Icc (0:ℝ) 1,
      ‖omegaWindowSum g P Q X t (x:ℂ)‖ ≤ Cw * ((1 + M₀) * Real.exp (-M₀) + 1/Real.sqrt T₀) := by
    intro x hx
    have hr0 : 0 ≤ x := hx.1
    have hr1 : x ≤ 1 := hx.2
    have hdistx : ∀ y : ℝ, X/4 ≤ y → y ≤ 4*X → ∀ w : ℝ, |w| ≤ 4*T₀ →
        M₀ ≤ BoundedMultiplicativeFunctions.𝔻 (omegaWeighted g P Q (x:ℂ))
          (fun n ↦ (n:ℂ)^(Complex.I*w)) y ^ 2 := by
      intro y hy1 hy2 w hw'
      have hy1' : X ^ (1/4:ℝ)/16 ≤ y := by linarith [hXr]
      have hy2' : y ≤ 16*X := by linarith
      rw [hM₀]
      exact omegaWeighted_dist_lower g P Q B x y w hgb (by linarith) hr0 hr1 hL
        (hdist y hy1' hy2' w hw')
    have hres := hw (omegaWeighted g P Q (x:ℂ)) X M₀ T₀ t
        (omegaWeighted_one g P Q (x:ℂ) hg1)
        (omegaWeighted_mul g P Q (x:ℂ) hgmul)
        (omegaWeighted_oneBounded g P Q hr0 hr1 hgb)
        hX hM0pos hT0 ht hdistx
    unfold omegaWindowSum
    exact hres
  have hInt : ‖∫ x in (0:ℝ)..1, omegaWindowSum g P Q X t (x:ℂ)‖ ≤
      Cw * ((1 + M₀) * Real.exp (-M₀) + 1/Real.sqrt T₀) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => omegaWindowSum g P Q X t (x:ℂ)) (a := (0:ℝ)) (b := 1)
      (C := Cw * ((1 + M₀) * Real.exp (-M₀) + 1/Real.sqrt T₀))
      (fun x hx => by
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
        exact hF x ⟨le_of_lt hx.1, hx.2⟩)
    rwa [sub_zero, abs_one, mul_one] at h
  rw [omegaWeighted_sum_eq_integral g P Q X t]
  refine le_trans hInt ?_
  have hexp : Real.exp (-M₀) ≤ Real.exp (-(B^2/4)) := by
    apply Real.exp_le_exp.mpr
    rw [hM₀]; nlinarith
  have h1M : 1 + M₀ ≤ 1 + B^2 := by rw [hM₀]; nlinarith
  have hbase : (1 + M₀) * Real.exp (-M₀) ≤ (1 + B^2) * Real.exp (-(B^2/4)) :=
    mul_le_mul h1M hexp (Real.exp_pos _).le (by nlinarith [sq_nonneg B])
  have hbase_nn : 0 ≤ (1 + B^2) * Real.exp (-(B^2/4)) := by positivity
  have hA : (1 + M₀) * Real.exp (-M₀) ≤
      (Real.log Q / Real.log P) * ((1 + B^2) * Real.exp (-(B^2/4))) := by
    have hh : (1 + B^2) * Real.exp (-(B^2/4)) ≤
        (Real.log Q / Real.log P) * ((1 + B^2) * Real.exp (-(B^2/4))) := by
      have h := mul_le_mul_of_nonneg_right hlog1 hbase_nn
      rwa [one_mul] at h
    exact le_trans hbase hh
  have hsT_nn : 0 ≤ 1/Real.sqrt T₀ := by positivity
  have hB' : 1 / Real.sqrt T₀ ≤ (Real.log Q / Real.log P) * (1 / Real.sqrt T₀) := by
    have hh := mul_le_mul_of_nonneg_right hlog1 hsT_nn
    rwa [one_mul] at hh
  have htot : (1 + M₀) * Real.exp (-M₀) + 1/Real.sqrt T₀ ≤
      (Real.log Q / Real.log P) * ((1 + B^2) * Real.exp (-(B^2/4)) + 1/Real.sqrt T₀) := by
    rw [mul_add]
    exact add_le_add hA hB'
  calc Cw * ((1 + M₀) * Real.exp (-M₀) + 1/Real.sqrt T₀)
      ≤ Cw * ((Real.log Q / Real.log P) * ((1 + B^2) * Real.exp (-(B^2/4)) + 1/Real.sqrt T₀)) :=
        mul_le_mul_of_nonneg_left htot hCw.le
    _ = Cw * (Real.log Q / Real.log P) * ((1 + B^2) * Real.exp (-(B^2/4)) + 1/Real.sqrt T₀) := by ring


end

end Work.BMF.mr_direct
