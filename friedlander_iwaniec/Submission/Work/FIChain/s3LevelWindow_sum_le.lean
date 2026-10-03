import Mathlib
import Submission.Work.FIChain.s3MainLevelDefs
import Submission.Work.FIChain.mu_gtil_interval_le
import Submission.Work.FIChain.S3plusC_aux2

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary multiplicativity / vanishing lemmas for `μ` and `g̃ = FIgtil` -/

/-- The Möbius function is multiplicative on coprime arguments (at the level of `ℝ`). -/
lemma fi_moebius_mul_of_coprime {m n : ℕ} (h : m.Coprime n) :
    (ArithmeticFunction.moebius (m * n) : ℝ)
      = (ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius n : ℝ) := by
  have h' := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h.gcd_eq_one
  rw [h']
  push_cast
  ring

/-- `|μ n| = 1` for squarefree `n`. -/
lemma fi_abs_moebius_of_squarefree {n : ℕ} (h : Squarefree n) :
    |(ArithmeticFunction.moebius n : ℝ)| = 1 := by
  have h2 : (ArithmeticFunction.moebius n : ℝ) ^ 2 = 1 := by
    rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree h]
    norm_num
  rcases sq_eq_one_iff.mp h2 with h' | h'
  · rw [h']; norm_num
  · rw [h']; norm_num

/-- The weight `μ·g̃` is multiplicative on squarefree products. -/
lemma fi_mu_gtil_mul_of_squarefree {m n : ℕ} (h : Squarefree (m * n)) :
    (ArithmeticFunction.moebius (m * n) : ℝ) * Submission.ASP.FIgtil (m * n)
      = ((ArithmeticFunction.moebius m : ℝ) * Submission.ASP.FIgtil m)
        * ((ArithmeticFunction.moebius n : ℝ) * Submission.ASP.FIgtil n) := by
  obtain ⟨hcop, -, -⟩ := Nat.squarefree_mul_iff.mp h
  rw [fi_moebius_mul_of_coprime hcop, Submission.ASP.FIgtil_mul hcop]
  ring

/-- `g̃` vanishes on a product of non-coprime factors. -/
lemma fi_FIgtil_eq_zero_of_not_coprime {m n : ℕ} (h : ¬ m.Coprime n) :
    Submission.ASP.FIgtil (m * n) = 0 := by
  obtain ⟨p, hp, hpm, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  refine Submission.ASP.FIgtil_eq_zero (fun hsq => ?_)
  have hdiv : p * p ∣ m * n := mul_dvd_mul hpm hpn
  exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) hdiv

/-- The factorisation `g̃(e·b·d) = g̃(e)·g̃(d)·g̃(b)` for `(e,d) = 1`, `(b, e·d) = 1`. -/
lemma fi_FIgtil_ebd_eq {e b d : ℕ} (hed : e.Coprime d) (hb : b.Coprime (e * d)) :
    Submission.ASP.FIgtil (e * b * d)
      = Submission.ASP.FIgtil e * Submission.ASP.FIgtil d * Submission.ASP.FIgtil b := by
  rw [show e * b * d = (e * d) * b by ring, Submission.ASP.FIgtil_mul hb.symm,
    Submission.ASP.FIgtil_mul hed]

/-- `g̃(e·b·d) = 0` when `b` is not coprime to `e·d`. -/
lemma fi_FIgtil_ebd_eq_zero {e b d : ℕ} (h : ¬ b.Coprime (e * d)) :
    Submission.ASP.FIgtil (e * b * d) = 0 := by
  rw [show e * b * d = b * (e * d) by ring]
  exact fi_FIgtil_eq_zero_of_not_coprime h

/-- `g̃(e·b·d) = 0` when `e` is not coprime to `d` (then `e·b·d` is never squarefree). -/
lemma fi_FIgtil_ebd_eq_zero_of_ed {e b d : ℕ} (h : ¬ e.Coprime d) :
    Submission.ASP.FIgtil (e * b * d) = 0 := by
  refine Submission.ASP.FIgtil_eq_zero (fun hsq => ?_)
  obtain ⟨p, hp, hpe, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hdiv : p * p ∣ e * b * d := by
    rcases hpe with ⟨e', rfl⟩
    rcases hpd with ⟨d', rfl⟩
    exact ⟨b * e' * d', by ring⟩
  exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) hdiv

/-- Reindexing a sum over the multiples of `ν` in an interval: `b = ν·b'`. -/
lemma sum_dvd_Icc_eq (ν a c : ℕ) (hν : 1 ≤ ν) (f : ℕ → ℝ) :
    ∑ b ∈ (Finset.Icc a c).filter (fun b => ν ∣ b), f b
      = ∑ b' ∈ Finset.Icc ((a + ν - 1) / ν) (c / ν), f (ν * b') := by
  have hν0 : 0 < ν := by omega
  have hy1 : ∀ b' : ℕ, (a + ν - 1) / ν ≤ b' ↔ a ≤ ν * b' := by
    intro b'; rw [Nat.div_le_iff_le_mul_add_pred hν0]; omega
  have hy2 : ∀ b' : ℕ, b' ≤ c / ν ↔ ν * b' ≤ c := by
    intro b'; rw [Nat.le_div_iff_mul_le hν0, mul_comm]
  refine Finset.sum_bij (fun b _ => b / ν) ?_ ?_ ?_ ?_
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    have hbν : ν * (b / ν) = b := Nat.mul_div_cancel' h3
    rw [Finset.mem_Icc]
    exact ⟨(hy1 (b / ν)).mpr (h1.trans (le_of_eq hbν.symm)),
      (hy2 (b / ν)).mpr ((le_of_eq hbν).trans h2)⟩
  · intro b1 h1 b2 h2 heq
    rw [Finset.mem_filter] at h1 h2
    rw [← Nat.mul_div_cancel' h1.2, ← Nat.mul_div_cancel' h2.2, heq]
  · intro b' hb'
    rw [Finset.mem_Icc] at hb'
    refine ⟨ν * b', ?_, Nat.mul_div_right b' hν0⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨(hy1 b').mp hb'.1, (hy2 b').mp hb'.2⟩, dvd_mul_right ν b'⟩
  · intro b hb
    rw [Finset.mem_filter] at hb
    rw [Nat.mul_div_cancel' hb.2]

/-! ## Elementary real-analysis / arithmetic helpers -/

/-- `t ↦ (log (max t 2))^{-6}` is non-increasing. -/
lemma log_max_rpow_neg6_anti {a b : ℝ} (h : a ≤ b) :
    (Real.log (max b 2)) ^ (-(6 : ℝ)) ≤ (Real.log (max a 2)) ^ (-(6 : ℝ)) := by
  have h2 : (0 : ℝ) < Real.log (max a 2) :=
    Real.log_pos (lt_of_lt_of_le one_lt_two (le_max_right a 2))
  have hle : Real.log (max a 2) ≤ Real.log (max b 2) :=
    Real.log_le_log (by positivity) (max_le_max h le_rfl)
  exact Real.rpow_le_rpow_of_nonpos h2 hle (by norm_num)

lemma sigmaTilde_nonneg (ℓ : ℕ) : 0 ≤ Work.FIChain.sigmaTilde ℓ := by
  rw [Work.FIChain.sigmaTilde]
  exact Finset.prod_nonneg (fun p _ => by positivity)

lemma log_rpow_neg6_nonneg (y : ℕ) :
    0 ≤ (Real.log (((max y 2 : ℕ)) : ℝ)) ^ (-(6 : ℝ)) := by
  refine Real.rpow_nonneg (Real.log_nonneg ?_) _
  exact_mod_cast (show 1 ≤ max y 2 by omega)

/-- The lower endpoint of the `b'`-interval dominates `sy/Δ`: `⌈lo/ν⌉ ≥ sy/Δ` whenever
`lo > sy` and `ν ≤ Δ`. -/
lemma div_ceil_ge (lo ν Δ : ℕ) {sy : ℝ} (hlo : 1 ≤ lo) (hν : 1 ≤ ν) (hνΔ : ν ≤ Δ)
    (h : sy < (lo : ℝ)) :
    sy / (Δ : ℝ) ≤ (((lo + ν - 1) / ν : ℕ) : ℝ) := by
  have hν0 : (0 : ℝ) < (ν : ℝ) := by exact_mod_cast (by omega : 0 < ν)
  have hΔ0 : (0 : ℝ) < (Δ : ℝ) := by
    have : 0 < Δ := by omega
    exact_mod_cast this
  have hΔν : (ν : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hνΔ
  have hmul : lo ≤ ν * ((lo + ν - 1) / ν) := by
    have h2 : lo + ν - 1 ≤ ν * ((lo + ν - 1) / ν) + (ν - 1) :=
      (Nat.div_le_iff_le_mul_add_pred (b := ν) (a := lo + ν - 1)
        (c := (lo + ν - 1) / ν) (by omega)).mp le_rfl
    omega
  have hmulR : (lo : ℝ) ≤ (ν : ℝ) * (((lo + ν - 1) / ν : ℕ) : ℝ) := by exact_mod_cast hmul
  have hdivlo : (lo : ℝ) / (ν : ℝ) ≤ (((lo + ν - 1) / ν : ℕ) : ℝ) := by
    rw [div_le_iff₀ hν0]
    linarith [hmulR]
  by_cases hsy : 0 ≤ sy
  · exact le_of_lt (calc sy / (Δ : ℝ) ≤ sy / (ν : ℝ) := div_le_div_of_nonneg_left hsy hν0 hΔν
      _ < (lo : ℝ) / (ν : ℝ) := div_lt_div_of_pos_right h hν0
      _ ≤ _ := hdivlo)
  · have h1 : sy / (Δ : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hsy) hΔ0.le
    linarith

lemma div_ceil_ge_one (lo ν : ℕ) (hlo : 1 ≤ lo) (hν : 1 ≤ ν) :
    1 ≤ (lo + ν - 1) / ν := by
  rw [Nat.le_div_iff_mul_le (by omega : 0 < ν)]
  omega

/-! ## The two auxiliary sums of the `(2.4)`-application -/

/-- The `b`-sum restricted to the multiples of `ν` (with the squarefreeness and coprimality
conditions of the level sum): the object that `(2.4)` bounds. -/
def s3WindowDvdSum (lo hi e d ν : ℕ) : ℝ :=
  ∑ b ∈ (Finset.Icc lo hi).filter
      (fun b => Squarefree b ∧ Nat.Coprime b (e * d) ∧ ν ∣ b),
    (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil b

/-- The interval sum with the coprimality parameter `ℓ` that `(2.4)`
(`Work.FIChain.mu_gtil_interval_le`) bounds. -/
def s3SieveWin (y₁ y₂ ℓ : ℕ) : ℝ :=
  ∑ b' ∈ (Finset.Icc y₁ y₂).filter (fun b' => Squarefree b' ∧ Nat.Coprime b' ℓ),
    (ArithmeticFunction.moebius b' : ℝ) * Submission.ASP.FIgtil b'

/-- The degenerate case of the reindexing: if `ν` is not squarefree or not coprime to `e·d`,
then no admissible `b` is a multiple of `ν`. -/
lemma s3WindowDvdSum_eq_zero (lo hi ν e d : ℕ)
    (h : ¬ (Squarefree ν ∧ Nat.Coprime ν (e * d))) : s3WindowDvdSum lo hi e d ν = 0 := by
  rw [s3WindowDvdSum]
  refine Finset.sum_eq_zero fun b hb => ?_
  rw [Finset.mem_filter] at hb
  obtain ⟨hsq, hbc, hνb⟩ := hb.2
  exact absurd ⟨Squarefree.squarefree_of_dvd hνb hsq,
    Nat.Coprime.coprime_dvd_left hνb hbc⟩ h

/-- The `b`-window of the level sum is an interval: each of the five conditions is a half-line in
`b`, so the window is `Icc` of its least and greatest element. -/
lemma s3LevelWindow_eq_Icc (x : ℕ) (z sz : ℝ) (Cm : ℕ) (sy : ℝ) (n : ℕ) (u : ℝ) (e : ℕ)
    (hne : (Work.FIChain.s3LevelWindow x z sz Cm sy n u e).Nonempty) :
    Work.FIChain.s3LevelWindow x z sz Cm sy n u e
      = Finset.Icc ((Work.FIChain.s3LevelWindow x z sz Cm sy n u e).min' hne)
                  ((Work.FIChain.s3LevelWindow x z sz Cm sy n u e).max' hne) := by
  set W := Work.FIChain.s3LevelWindow x z sz Cm sy n u e with hWdef
  set lo := W.min' hne with hlodef
  set hi := W.max' hne with hhidef
  have hloW : lo ∈ W := Finset.min'_mem W hne
  have hhiW : hi ∈ W := Finset.max'_mem W hne
  obtain ⟨hl1, hlx, hlsy, hlA, hlB, hlC, hlD⟩ := Work.FIChain.mem_s3LevelWindow.mp hloW
  obtain ⟨hh1, hhx, hhsy, hhA, hhB, hhC, hhD⟩ := Work.FIChain.mem_s3LevelWindow.mp hhiW
  have hgoal : W = Finset.Icc lo hi := by
    refine Finset.Subset.antisymm (fun b hb => ?_) (fun b hb => ?_)
    · rw [Finset.mem_Icc]
      exact ⟨Finset.min'_le W b hb, Finset.le_max' W b hb⟩
    · rw [Finset.mem_Icc] at hb
      obtain ⟨hb1, hb2⟩ := hb
      rw [Work.FIChain.mem_s3LevelWindow]
      have hb1' : (lo : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
      have hb2' : (b : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hb2
      refine ⟨le_trans hl1 hb1, le_trans hb2 hhx, lt_of_lt_of_le hlsy hb1', ?_, ?_, ?_, ?_⟩
      · by_cases hz : 0 ≤ (e : ℝ) * z
        · nlinarith [mul_le_mul_of_nonneg_left hb2' hz, hhA]
        · nlinarith [mul_le_mul_of_nonpos_right hb1' (lt_of_not_ge hz).le, hlA]
      · by_cases hz : 0 ≤ (e : ℝ) * sz
        · nlinarith [mul_le_mul_of_nonneg_left hb1' hz, hlB]
        · nlinarith [mul_le_mul_of_nonpos_right hb2' (lt_of_not_ge hz).le, hhB]
      · by_cases hz : 0 ≤ (e : ℝ) * z
        · nlinarith [mul_le_mul_of_nonneg_left hb2' hz, hhC]
        · nlinarith [mul_le_mul_of_nonpos_right hb1' (lt_of_not_ge hz).le, hlC]
      · by_cases hz : 0 ≤ (e : ℝ) * ((Cm : ℝ) * u)
        · nlinarith [mul_le_mul_of_nonneg_left hb2' hz, hhD]
        · nlinarith [mul_le_mul_of_nonpos_right hb1' (lt_of_not_ge hz).le, hlD]
  exact hgoal

/-- The reindexing `b = ν·b'` of the `ν`-fibre of the level sum. -/
lemma s3WindowDvdSum_eq (lo hi ν e d : ℕ) (hν : 1 ≤ ν) (hsq : Squarefree ν)
    (hcop : Nat.Coprime ν (e * d)) :
    Work.FIChain.s3WindowDvdSum lo hi e d ν
      = ((ArithmeticFunction.moebius ν : ℝ) * Submission.ASP.FIgtil ν)
        * Work.FIChain.s3SieveWin ((lo + ν - 1) / ν) (hi / ν) (e * d * ν) := by
  have hfilter : (Finset.Icc ((lo + ν - 1) / ν) (hi / ν)).filter
        (fun b' => Squarefree (ν * b') ∧ Nat.Coprime (ν * b') (e * d))
      = (Finset.Icc ((lo + ν - 1) / ν) (hi / ν)).filter
        (fun b' => Squarefree b' ∧ Nat.Coprime b' (e * d * ν)) := by
    ext b'
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hmem, h1, h2⟩
      refine ⟨hmem, (Nat.squarefree_mul_iff.mp h1).2.2, ?_⟩
      rw [Nat.coprime_mul_iff_right]
      exact ⟨(Nat.coprime_mul_iff_left.mp h2).2, ((Nat.squarefree_mul_iff.mp h1).1).symm⟩
    · rintro ⟨hmem, h1, h2⟩
      refine ⟨hmem, ?_, ?_⟩
      · rw [Nat.squarefree_mul_iff]
        exact ⟨((Nat.coprime_mul_iff_right.mp h2).2).symm, hsq, h1⟩
      · rw [Nat.coprime_mul_iff_left]
        exact ⟨hcop, (Nat.coprime_mul_iff_right.mp h2).1⟩
  rw [s3WindowDvdSum, s3SieveWin]
  calc ∑ b ∈ (Finset.Icc lo hi).filter
          (fun b => Squarefree b ∧ Nat.Coprime b (e * d) ∧ ν ∣ b),
        (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil b
      = ∑ b ∈ ((Finset.Icc lo hi).filter (fun b => ν ∣ b)).filter
          (fun b => Squarefree b ∧ Nat.Coprime b (e * d)),
        (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil b := by
        refine Finset.sum_congr ?_ (fun b _ => rfl)
        ext b
        simp only [Finset.mem_filter]
        tauto
    _ = ∑ b ∈ (Finset.Icc lo hi).filter (fun b => ν ∣ b),
        (if Squarefree b ∧ Nat.Coprime b (e * d) then
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil b else 0) := by
        rw [Finset.sum_filter]
    _ = ∑ b' ∈ Finset.Icc ((lo + ν - 1) / ν) (hi / ν),
        (if Squarefree (ν * b') ∧ Nat.Coprime (ν * b') (e * d) then
          (ArithmeticFunction.moebius (ν * b') : ℝ) * Submission.ASP.FIgtil (ν * b') else 0) := by
        rw [sum_dvd_Icc_eq ν lo hi hν]
    _ = ∑ b' ∈ (Finset.Icc ((lo + ν - 1) / ν) (hi / ν)).filter
          (fun b' => Squarefree (ν * b') ∧ Nat.Coprime (ν * b') (e * d)),
        (ArithmeticFunction.moebius (ν * b') : ℝ) * Submission.ASP.FIgtil (ν * b') := by
        rw [Finset.sum_filter]
    _ = ((ArithmeticFunction.moebius ν : ℝ) * Submission.ASP.FIgtil ν) *
        ∑ b' ∈ (Finset.Icc ((lo + ν - 1) / ν) (hi / ν)).filter
          (fun b' => Squarefree (ν * b') ∧ Nat.Coprime (ν * b') (e * d)),
        (ArithmeticFunction.moebius b' : ℝ) * Submission.ASP.FIgtil b' := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b' hb' => ?_
        rw [Finset.mem_filter] at hb'
        rw [fi_mu_gtil_mul_of_squarefree hb'.2.1]
    _ = ((ArithmeticFunction.moebius ν : ℝ) * Submission.ASP.FIgtil ν) *
        ∑ b' ∈ (Finset.Icc ((lo + ν - 1) / ν) (hi / ν)).filter
          (fun b' => Squarefree b' ∧ Nat.Coprime b' (e * d * ν)),
        (ArithmeticFunction.moebius b' : ℝ) * Submission.ASP.FIgtil b' := by
        rw [hfilter]

/-- Expansion of `ρ(e·b) = Σ_{νe | e} Σ_{νb | b} λ(νe·νb)` and the reindexing of the `b`-sum into
the `νb`-fibres, truncated at `Δ` (where `λ` vanishes). -/
lemma s3LevelSum_reindex (lo hi e d Δ : ℕ) (lam : ℕ → ℝ) (he : 1 ≤ e)
    (hsupp : ∀ ν : ℕ, Δ < ν → lam ν = 0) :
    (∑ b ∈ (Finset.Icc lo hi).filter (fun b => Squarefree b ∧ Nat.Coprime b (e * d)),
        (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
          * Submission.ASP.FIgtil b)
      = ∑ νe ∈ e.divisors, ∑ νb ∈ Finset.Icc 1 Δ,
          lam (νe * νb) * Work.FIChain.s3WindowDvdSum lo hi e d νb := by
  have he0 : e ≠ 0 := by omega
  have htrunc : ∀ (b νe : ℕ), 1 ≤ b → 1 ≤ νe →
      (∑ νb ∈ b.divisors, lam (νe * νb))
        = ∑ νb ∈ Finset.Icc 1 Δ, (if νb ∣ b then lam (νe * νb) else 0) := by
    intro b νe hb1 hνe1
    have hdrop : (∑ νb ∈ b.divisors, lam (νe * νb))
        = ∑ νb ∈ (b.divisors).filter (fun νb => νb ≤ Δ), lam (νe * νb) :=
      (Finset.sum_filter_of_ne (s := b.divisors) (f := fun νb => lam (νe * νb))
        (p := fun νb => νb ≤ Δ) (fun νb _ h0 => by
          by_contra hle
          refine h0 (hsupp (νe * νb) ?_)
          have h2 : νb ≤ νe * νb := Nat.le_mul_of_pos_left νb (by omega)
          omega)).symm
    rw [hdrop, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun νb _ => rfl)
    ext νb
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hdvd, hne⟩, hle⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega), hle⟩, hdvd⟩
    · rintro ⟨⟨h1, hle⟩, hdvd⟩
      exact ⟨⟨hdvd, by omega⟩, hle⟩
  have hInner : ∀ νb : ℕ,
      (∑ b ∈ (Finset.Icc lo hi).filter (fun b => Squarefree b ∧ Nat.Coprime b (e * d)),
        (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil b
          * (if νb ∣ b then 1 else 0))
        = Work.FIChain.s3WindowDvdSum lo hi e d νb := by
    intro νb
    rw [s3WindowDvdSum]
    have hset : ((Finset.Icc lo hi).filter
          (fun b => Squarefree b ∧ Nat.Coprime b (e * d))).filter (fun b => νb ∣ b)
        = (Finset.Icc lo hi).filter
          (fun b => Squarefree b ∧ Nat.Coprime b (e * d) ∧ νb ∣ b) := by
      ext b
      simp only [Finset.mem_filter]
      tauto
    conv_rhs => rw [← hset, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hc : νb ∣ b <;> simp [hc]
  calc (∑ b ∈ (Finset.Icc lo hi).filter (fun b => Squarefree b ∧ Nat.Coprime b (e * d)),
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
            * Submission.ASP.FIgtil b)
      = ∑ b ∈ (Finset.Icc lo hi).filter (fun b => Squarefree b ∧ Nat.Coprime b (e * d)),
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil b
            * (∑ νe ∈ e.divisors, ∑ νb ∈ b.divisors, lam (νe * νb)) := by
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [Finset.mem_filter] at hb
        have hcb : Nat.Coprime e b :=
          ((hb.2.2).coprime_dvd_right (dvd_mul_right e d)).symm
        rw [Work.FIChain.rhoOf_mul_coprime lam hcb]
        ring
    _ = ∑ νe ∈ e.divisors,
          ∑ b ∈ (Finset.Icc lo hi).filter (fun b => Squarefree b ∧ Nat.Coprime b (e * d)),
            (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil b
              * (∑ νb ∈ b.divisors, lam (νe * νb)) := by
        have h1 : ∀ b : ℕ, (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil b
              * (∑ νe ∈ e.divisors, ∑ νb ∈ b.divisors, lam (νe * νb))
            = ∑ νe ∈ e.divisors, (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil b
                * (∑ νb ∈ b.divisors, lam (νe * νb)) := fun b => by rw [Finset.mul_sum]
        simp only [h1]
        exact Finset.sum_comm
    _ = ∑ νe ∈ e.divisors,
          ∑ b ∈ (Finset.Icc lo hi).filter (fun b => Squarefree b ∧ Nat.Coprime b (e * d)),
            (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil b
              * (∑ νb ∈ Finset.Icc 1 Δ, (if νb ∣ b then lam (νe * νb) else 0)) := by
        refine Finset.sum_congr rfl fun νe hνe => Finset.sum_congr rfl fun b hb => ?_
        rw [Finset.mem_filter] at hb
        have hνe1 : 1 ≤ νe := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hνe).1 (by omega)
        have hb1 : 1 ≤ b := Nat.pos_of_ne_zero hb.2.1.ne_zero
        rw [htrunc b νe hb1 hνe1]
    _ = ∑ νe ∈ e.divisors, ∑ νb ∈ Finset.Icc 1 Δ, lam (νe * νb) *
          (∑ b ∈ (Finset.Icc lo hi).filter (fun b => Squarefree b ∧ Nat.Coprime b (e * d)),
            (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.FIgtil b
              * (if νb ∣ b then 1 else 0)) := by
        refine Finset.sum_congr rfl fun νe _ => ?_
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun νb _ => Finset.sum_congr rfl fun b _ => ?_
        by_cases hc : νb ∣ b
        · rw [if_pos hc, if_pos hc]; ring
        · rw [if_neg hc, if_neg hc]; ring
    _ = ∑ νe ∈ e.divisors, ∑ νb ∈ Finset.Icc 1 Δ,
          lam (νe * νb) * Work.FIChain.s3WindowDvdSum lo hi e d νb := by
        refine Finset.sum_congr rfl fun νe _ => Finset.sum_congr rfl fun νb _ => ?_
        rw [hInner νb]

/-- **The sieve estimate `(2.4)` on the `b`-window of the level sum.**  For fixed
`(n,u,e,d)` the `b`-window of `s3LevelWindow` is an *interval*, and on the support the weight in
`b` is `μ(b)·g̃(b)·(constant in b)`: `g̃(e·b·d) = g̃(e)·g̃(b)·g̃(d)` whenever `(b, e·d) = 1`, and
when `(b,e)>1` or `(b,d)>1` the term vanishes because `e·b·d` is then not squarefree (so on the
support the coprimality is free and the restricted sum is the same sum).

Route: (i) convert the filter `s3LevelWindow` into the explicit interval
`Icc (max (⌊sy⌋₊+1) ⌈n/(e·sz)⌉₊) (min (⌊x/(e·z)⌋₊) (⌈n/(e·z)⌉₊-1) (⌈n/(e·Cm·u)⌉₊-1))`;
(ii) restrict to `(b, e·d) = 1` (equality of the sums, the dropped terms being `0`), factor
`g̃(e·b·d) = g̃(e)·g̃(b)·g̃(d)` via `Submission.ASP.FIgtil_mul`, and expand
`ρ(e·b) = Σ_{νe | e} Σ_{νb | b} λ(νe·νb)` via `Work.FIChain.rhoOf_mul_coprime` (valid since
`(e,b) = 1`); (iii) substitute `b = νb·b'` (the pair `(b, νb)` with `νb | b` becomes the pair
`(νb, b')`: this is an identity), which turns the `b`-sum into
`Σ_{νb} μ(νb)·g̃(νb)·Σ_{b' ∈ Icc ⌊lo/νb⌋+1 ⌊hi/νb⌋} μ(b')·g̃(b')·[(b', e·d·νb) = 1]·(constant)`,
a genuine interval sum whose lower end satisfies `⌊lo/νb⌋ + 1 ≥ sy/Δ` (use `⌊sy⌋₊ + 1 > sy`);
(iv) apply `Work.FIChain.mu_gtil_interval_le` with the coprimality parameter `e·d·νb`: the inner
`b'`-sum is `≤ C·σ̃_{edνb}·(log (max y₁ 2))^{-6}` with `y₁ ≥ sy/Δ`, whence the stated
`(log (max (sy/Δ) 2))^{-6}` since `sy/νb ≥ sy/Δ`;
(v) bound `|λ(νb·νe)| ≤ 1` and sum over `(νb, νe) ∈ Icc 1 Δ × e.divisors` (the `νb > Δ`
contribute `0` since `λ` vanishes there, and the `νb` not coprime to `e·d` are absent from the
identity — adding them only enlarges the right-hand side, a sum of nonnegative terms). -/
theorem s3LevelWindow_sum_le : ∃ C : ℝ, 0 < C ∧
    ∀ (x : ℕ) (z sz : ℝ) (Cm : ℕ) (sy : ℝ) (n : ℕ) (u : ℝ) (e d : ℕ) (lam : ℕ → ℝ) (Δ : ℕ),
      (∀ ν : ℕ, Δ < ν → lam ν = 0) → (∀ ν : ℕ, |lam ν| ≤ 1) →
      1 ≤ e → 1 ≤ d → 0 < u → 0 < z → 0 < sz → 1 < sy / (Δ : ℝ) →
      |∑ b ∈ Work.FIChain.s3LevelWindow x z sz Cm sy n u e,
          (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
            * Submission.ASP.FIgtil (e * b * d)|
        ≤ C * Submission.ASP.FIgtil e * Submission.ASP.FIgtil d
            * (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ ν₂ ∈ e.divisors,
                Submission.ASP.FIgtil ν₁ * |lam (ν₁ * ν₂)|
                  * Work.FIChain.sigmaTilde (e * d * ν₁))
            * (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FIChain.mu_gtil_interval_le
  refine ⟨C₀, hC₀pos, ?_⟩
  intro x z sz Cm sy n u e d lam Δ hsupp hlam1 he hd hu hz hsz hsy
  have hge : (0 : ℝ) ≤ Submission.ASP.FIgtil e := Submission.ASP.FIgtil_nonneg e
  have hgd : (0 : ℝ) ≤ Submission.ASP.FIgtil d := Submission.ASP.FIgtil_nonneg d
  have hL₀nn : (0 : ℝ) ≤ (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ)) :=
    Real.rpow_nonneg
      (Real.log_nonneg (le_of_lt (lt_of_lt_of_le one_lt_two (le_max_right _ _)))) _
  have hsum_nn : (0 : ℝ) ≤ ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ ν₂ ∈ e.divisors,
      Submission.ASP.FIgtil ν₁ * |lam (ν₁ * ν₂)| * Work.FIChain.sigmaTilde (e * d * ν₁) :=
    Finset.sum_nonneg fun ν₁ _ => Finset.sum_nonneg fun ν₂ _ =>
      mul_nonneg (mul_nonneg (Submission.ASP.FIgtil_nonneg _) (abs_nonneg _))
        (Work.FIChain.sigmaTilde_nonneg _)
  have hRHSnn : (0 : ℝ) ≤ C₀ * Submission.ASP.FIgtil e * Submission.ASP.FIgtil d *
      (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ ν₂ ∈ e.divisors,
        Submission.ASP.FIgtil ν₁ * |lam (ν₁ * ν₂)| * Work.FIChain.sigmaTilde (e * d * ν₁)) *
      (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC₀pos.le hge) hgd) hsum_nn) hL₀nn
  by_cases hed : Nat.Coprime e d
  · by_cases hW : (Work.FIChain.s3LevelWindow x z sz Cm sy n u e).Nonempty
    · set W := Work.FIChain.s3LevelWindow x z sz Cm sy n u e with hWdef
      have hne : W.Nonempty := hW
      set lo := W.min' hne with hlodef
      set hi := W.max' hne with hhidef
      have hloW : lo ∈ W := by rw [hlodef]; exact Finset.min'_mem W hne
      have hhiW : hi ∈ W := by rw [hhidef]; exact Finset.max'_mem W hne
      have hWIcc : W = Finset.Icc lo hi := by
        rw [hlodef, hhidef]
        exact s3LevelWindow_eq_Icc x z sz Cm sy n u e hne
      have hlo1 : 1 ≤ lo := (Work.FIChain.mem_s3LevelWindow.mp hloW).1
      have hsy_lo : sy < (lo : ℝ) := (Work.FIChain.mem_s3LevelWindow.mp hloW).2.2.1
      set T := (Finset.Icc lo hi).filter (fun b => Squarefree b ∧ Nat.Coprime b (e * d))
        with hTdef
      set S : ℝ := ∑ b ∈ T, (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
          * Submission.ASP.FIgtil b with hSdef
      -- ### Step 1: reduce the level sum to the `b`-weight
      have hA : ∑ b ∈ W, (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
              * Submission.ASP.FIgtil (e * b * d)
            = ∑ b ∈ (Finset.Icc lo hi).filter (fun b => Nat.Coprime b (e * d)),
                (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
                  * Submission.ASP.FIgtil (e * b * d) := by
        rw [hWIcc, Finset.sum_filter]
        refine Finset.sum_congr rfl fun b hb => ?_
        by_cases hc : Nat.Coprime b (e * d)
        · rw [if_pos hc]
        · rw [if_neg hc, fi_FIgtil_ebd_eq_zero hc, mul_zero]
      have hB : ∑ b ∈ (Finset.Icc lo hi).filter (fun b => Nat.Coprime b (e * d)),
              (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
                * Submission.ASP.FIgtil (e * b * d)
            = Submission.ASP.FIgtil e * Submission.ASP.FIgtil d
              * ∑ b ∈ (Finset.Icc lo hi).filter (fun b => Nat.Coprime b (e * d)),
                (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
                  * Submission.ASP.FIgtil b := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [Finset.mem_filter] at hb
        rw [fi_FIgtil_ebd_eq hed hb.2]
        ring
      have hC : ∑ b ∈ (Finset.Icc lo hi).filter (fun b => Nat.Coprime b (e * d)),
              (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
                * Submission.ASP.FIgtil b
            = ∑ b ∈ T, (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
                * Submission.ASP.FIgtil b := by
        have hset : ((Finset.Icc lo hi).filter (fun b => Nat.Coprime b (e * d))).filter
              (fun b => Squarefree b) = T := by
          rw [hTdef]
          ext b
          simp only [Finset.mem_filter]
          tauto
        rw [← hset]
        exact (Finset.sum_filter_of_ne (s := (Finset.Icc lo hi).filter
          (fun b => Nat.Coprime b (e * d)))
          (f := fun b => (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
            * Submission.ASP.FIgtil b) (p := fun b => Squarefree b)
          (fun b _ hb0 => by
            by_contra hsq
            rw [Submission.ASP.FIgtil_eq_zero hsq, mul_zero] at hb0
            exact hb0 rfl)).symm
      have hLHSfac : |∑ b ∈ W, (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
              * Submission.ASP.FIgtil (e * b * d)|
            = Submission.ASP.FIgtil e * Submission.ASP.FIgtil d * |S| := by
        have h0 : ∑ b ∈ W, (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
              * Submission.ASP.FIgtil (e * b * d)
            = Submission.ASP.FIgtil e * Submission.ASP.FIgtil d * S := by
          rw [hA, hB, hC, hSdef]
        rw [h0, abs_mul, abs_of_nonneg (mul_nonneg hge hgd)]
      -- ### Step 2: `(2.4)` on each `ν`-fibre
      have hDbound : ∀ νb ∈ Finset.Icc 1 Δ,
          |s3WindowDvdSum lo hi e d νb|
            ≤ Submission.ASP.FIgtil νb
              * (C₀ * Work.FIChain.sigmaTilde (e * d * νb)
                  * (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ))) := by
        intro νb hνb
        rw [Finset.mem_Icc] at hνb
        obtain ⟨hνb1, hνbΔ⟩ := hνb
        by_cases hgood : Squarefree νb ∧ Nat.Coprime νb (e * d)
        · obtain ⟨hsq, hcop⟩ := hgood
          have hre : s3WindowDvdSum lo hi e d νb
              = ((ArithmeticFunction.moebius νb : ℝ) * Submission.ASP.FIgtil νb)
                * s3SieveWin ((lo + νb - 1) / νb) (hi / νb) (e * d * νb) :=
            s3WindowDvdSum_eq lo hi νb e d hνb1 hsq hcop
          have hsieve : |s3SieveWin ((lo + νb - 1) / νb) (hi / νb) (e * d * νb)|
              ≤ C₀ * Work.FIChain.sigmaTilde (e * d * νb)
                * (Real.log (((max ((lo + νb - 1) / νb) 2 : ℕ)) : ℝ)) ^ (-(6 : ℝ)) := by
            by_cases hy : (lo + νb - 1) / νb ≤ hi / νb
            · have h := hC₀ (e * d * νb) ((lo + νb - 1) / νb) (hi / νb)
                (by refine Nat.one_le_iff_ne_zero.mpr ?_
                    exact Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega))
                (div_ceil_ge_one lo νb hlo1 hνb1) hy
              simpa only [s3SieveWin] using h
            · have hempty : Finset.Icc ((lo + νb - 1) / νb) (hi / νb) = ∅ :=
                Finset.Icc_eq_empty (by omega)
              rw [s3SieveWin, hempty]
              simp only [Finset.filter_empty, Finset.sum_empty, abs_zero]
              exact mul_nonneg (mul_nonneg hC₀pos.le (sigmaTilde_nonneg _))
                (log_rpow_neg6_nonneg _)
          have hlogcomp : (Real.log (((max ((lo + νb - 1) / νb) 2 : ℕ)) : ℝ)) ^ (-(6 : ℝ))
              ≤ (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ)) := by
            have hle : sy / (Δ : ℝ) ≤ (((lo + νb - 1) / νb : ℕ) : ℝ) :=
              div_ceil_ge lo νb Δ hlo1 hνb1 hνbΔ hsy_lo
            have h := log_max_rpow_neg6_anti hle
            simpa only [Nat.cast_max, Nat.cast_ofNat] using h
          calc |s3WindowDvdSum lo hi e d νb|
              = Submission.ASP.FIgtil νb
                * |s3SieveWin ((lo + νb - 1) / νb) (hi / νb) (e * d * νb)| := by
                rw [hre, abs_mul, abs_mul, fi_abs_moebius_of_squarefree hsq, one_mul,
                  abs_of_nonneg (Submission.ASP.FIgtil_nonneg νb)]
            _ ≤ Submission.ASP.FIgtil νb * (C₀ * Work.FIChain.sigmaTilde (e * d * νb)
                  * (Real.log (((max ((lo + νb - 1) / νb) 2 : ℕ)) : ℝ)) ^ (-(6 : ℝ))) :=
                mul_le_mul_of_nonneg_left hsieve (Submission.ASP.FIgtil_nonneg νb)
            _ ≤ Submission.ASP.FIgtil νb * (C₀ * Work.FIChain.sigmaTilde (e * d * νb)
                  * (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ))) := by
                refine mul_le_mul_of_nonneg_left ?_ (Submission.ASP.FIgtil_nonneg νb)
                exact mul_le_mul_of_nonneg_left hlogcomp
                  (mul_nonneg hC₀pos.le (sigmaTilde_nonneg _))
        · rw [s3WindowDvdSum_eq_zero lo hi νb e d hgood, abs_zero]
          exact mul_nonneg (Submission.ASP.FIgtil_nonneg νb)
            (mul_nonneg (mul_nonneg hC₀pos.le (sigmaTilde_nonneg _)) hL₀nn)
      -- ### Step 3: expand `ρ(e·b)` and reindex
      have hSbound : |S| ≤ C₀ * (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ ν₂ ∈ e.divisors,
            Submission.ASP.FIgtil ν₁ * |lam (ν₁ * ν₂)| * Work.FIChain.sigmaTilde (e * d * ν₁))
          * (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ)) := by
        have hS1 : S = ∑ νe ∈ e.divisors, ∑ νb ∈ Finset.Icc 1 Δ,
            lam (νe * νb) * s3WindowDvdSum lo hi e d νb :=
          s3LevelSum_reindex lo hi e d Δ lam he hsupp
        rw [hS1]
        calc |∑ νe ∈ e.divisors, ∑ νb ∈ Finset.Icc 1 Δ,
                lam (νe * νb) * s3WindowDvdSum lo hi e d νb|
            ≤ ∑ νe ∈ e.divisors, |∑ νb ∈ Finset.Icc 1 Δ,
                lam (νe * νb) * s3WindowDvdSum lo hi e d νb| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ νe ∈ e.divisors, ∑ νb ∈ Finset.Icc 1 Δ,
                |lam (νe * νb)| * |s3WindowDvdSum lo hi e d νb| := by
              refine Finset.sum_le_sum fun νe _ => ?_
              calc |∑ νb ∈ Finset.Icc 1 Δ, lam (νe * νb) * s3WindowDvdSum lo hi e d νb|
                  ≤ ∑ νb ∈ Finset.Icc 1 Δ,
                      |lam (νe * νb) * s3WindowDvdSum lo hi e d νb| :=
                    Finset.abs_sum_le_sum_abs _ _
                _ = ∑ νb ∈ Finset.Icc 1 Δ,
                      |lam (νe * νb)| * |s3WindowDvdSum lo hi e d νb| :=
                    Finset.sum_congr rfl fun νb _ => abs_mul _ _
          _ ≤ ∑ νe ∈ e.divisors, ∑ νb ∈ Finset.Icc 1 Δ, |lam (νe * νb)| *
                (Submission.ASP.FIgtil νb * (C₀ * Work.FIChain.sigmaTilde (e * d * νb)
                  * (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ)))) := by
              refine Finset.sum_le_sum fun νe _ => Finset.sum_le_sum fun νb hνb => ?_
              exact mul_le_mul_of_nonneg_left (hDbound νb hνb) (abs_nonneg _)
          _ = (C₀ * (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ)))
                * (∑ νe ∈ e.divisors, ∑ νb ∈ Finset.Icc 1 Δ,
                    Submission.ASP.FIgtil νb * |lam (νe * νb)|
                      * Work.FIChain.sigmaTilde (e * d * νb)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun νe _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun νb _ => ?_
              ring
          _ = (C₀ * (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ ν₂ ∈ e.divisors,
                  Submission.ASP.FIgtil ν₁ * |lam (ν₁ * ν₂)| * Work.FIChain.sigmaTilde (e * d * ν₁)))
                * (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ)) := by
              have hWV : (∑ νe ∈ e.divisors, ∑ νb ∈ Finset.Icc 1 Δ,
                    Submission.ASP.FIgtil νb * |lam (νe * νb)|
                      * Work.FIChain.sigmaTilde (e * d * νb))
                  = ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ ν₂ ∈ e.divisors,
                      Submission.ASP.FIgtil ν₁ * |lam (ν₁ * ν₂)|
                        * Work.FIChain.sigmaTilde (e * d * ν₁) := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun ν₁ _ => Finset.sum_congr rfl fun ν₂ _ => ?_
                rw [mul_comm ν₂ ν₁]
              rw [hWV]
              ring
      calc |∑ b ∈ W, (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
              * Submission.ASP.FIgtil (e * b * d)|
          = Submission.ASP.FIgtil e * Submission.ASP.FIgtil d * |S| := hLHSfac
        _ ≤ Submission.ASP.FIgtil e * Submission.ASP.FIgtil d
              * (C₀ * (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ ν₂ ∈ e.divisors,
                  Submission.ASP.FIgtil ν₁ * |lam (ν₁ * ν₂)| * Work.FIChain.sigmaTilde (e * d * ν₁))
                * (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ))) :=
            mul_le_mul_of_nonneg_left hSbound (mul_nonneg hge hgd)
        _ = C₀ * Submission.ASP.FIgtil e * Submission.ASP.FIgtil d
              * (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ ν₂ ∈ e.divisors,
                  Submission.ASP.FIgtil ν₁ * |lam (ν₁ * ν₂)| * Work.FIChain.sigmaTilde (e * d * ν₁))
              * (Real.log (max (sy / (Δ : ℝ)) 2)) ^ (-(6 : ℝ)) := by ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hW, Finset.sum_empty, abs_zero]
      exact hRHSnn
  · have hzero : ∑ b ∈ Work.FIChain.s3LevelWindow x z sz Cm sy n u e,
        (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b)
          * Submission.ASP.FIgtil (e * b * d) = 0 :=
      Finset.sum_eq_zero fun b _ => by rw [fi_FIgtil_ebd_eq_zero_of_ed hed, mul_zero]
    rw [hzero, abs_zero]
    exact hRHSnn

end

end Work.FIChain
