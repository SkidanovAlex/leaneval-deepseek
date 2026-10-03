/-
# `Submission.Work.FITop4.Red5.BformPiTauSmall_le`

**The `\tau`-truncated, `\Pi`-restricted small-`m` region of the `\S\S4-5.2` reduction.**

`BformPiTau x N Pz C \tau` is the paper's (4.9) sieve form: `Bform` with the support conditions
`(n, \Pi) = 1` (5.8) and `\tau(n) \le \tau` (5.9) imposed on the inner variable.  This file shows
that the small-`m` region `m \le Y`, `Y N \le \vartheta x` of the *`\tau`-truncated,
`\Pi`-restricted* form is absorbed elementarily by `(\vartheta x)^{3/4}(\log x)^{65536`, just as for
the untruncated `BformAtilSmall` (`Red5/BformAtilSmall_le`): adding the two extra support
conditions `PiCond Pz n` and `TauCond \tau n` can only *shrink* each inner sum, so the whole
expression is dominated by the `\tau`-weighted double sum
`\sum_{m \le Y} \sum_{n \le 2N} \tau(n) \tilde a_{mn}`, which is bounded by the divisor-sum
estimate `Aseq_tau_sq_le_univ` together with `\tilde A(y) \ll y^{3/4}`.

The proof of the double-sum bound is the tail of the argument of `Red5/BformAtilSmall_le`
(its `hstep2`-`hstep6`), reproduced here so that the two files are independent.
-/
import Mathlib
import Submission.Work.FITop4.Red5.Vocab
import Submission.Work.FITop4.Defs4
import Submission.Work.FITop4.Red5.Aseq_tau_sq_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.Aseq_eq_intpairs_ncard
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_intpairs_asymptotic

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `|μ(n)| ≤ 1`, cast to `ℝ`. -/
private lemma abs_moebius_cast_le_one (n : ℕ) :
    |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
  have h : |ArithmeticFunction.moebius n| ≤ (1 : ℤ) := ArithmeticFunction.abs_moebius_le_one
  have h2 : (((|ArithmeticFunction.moebius n| : ℤ)) : ℝ) ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast h
  rw [Int.cast_abs] at h2
  simpa using h2

/-- **The hyperbola reindexing**: for nonnegative `F`, `Σ_{m ≤ Y, n ≤ M} F (mn) ≤ Σ_{k ≤ YM} F k · τ(k)`. -/
private lemma sum_mul_le_sum_divisors {Y M : ℕ} {F : ℕ → ℝ} (hF : ∀ k, 0 ≤ F k) :
    (∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc 1 M, F (m * n))
      ≤ ∑ k ∈ Finset.Icc 1 (Y * M), F k * ((k.divisors.card : ℝ)) := by
  classical
  set s : Finset (ℕ × ℕ) := (Finset.Icc 1 Y) ×ˢ (Finset.Icc 1 M) with hs
  set g : ℕ × ℕ → ℕ := fun p => p.1 * p.2 with hg
  have hmaps : ∀ p ∈ s, g p ∈ s.image g := fun p hp => Finset.mem_image_of_mem g hp
  have hprod : (∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc 1 M, F (m * n))
      = ∑ p ∈ s, F (g p) := by
    rw [hs, Finset.sum_product]
  have hfib := Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image g)
    (g := g) (f := fun p => F (g p)) hmaps
  rw [hprod, ← hfib]
  -- the image is contained in `Icc 1 (Y*M)`
  have himage : s.image g ⊆ Finset.Icc 1 (Y * M) := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hp1
    obtain ⟨h3, h4⟩ := Finset.mem_Icc.mp hp2
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
      Nat.mul_le_mul h2 h4⟩
  -- each fibre has at most `τ(k)` elements
  have hcard : ∀ k, (s.filter (fun p => g p = k)).card ≤ k.divisors.card := by
    intro k
    by_cases hk : k = 0
    · subst hk
      have hempty : s.filter (fun p => g p = 0) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro p hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
        obtain ⟨h1, _⟩ := Finset.mem_Icc.mp hp1
        obtain ⟨h3, _⟩ := Finset.mem_Icc.mp hp2
        simp only [hg]
        exact Nat.mul_ne_zero (by omega) (by omega)
      rw [hempty]; simp
    · have hsub : (s.filter (fun p => g p = k)).image Prod.fst ⊆ k.divisors := by
        intro m hm
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
        obtain ⟨hps, hpg⟩ := Finset.mem_filter.mp hp
        have hkm : k = p.1 * p.2 := hpg.symm
        rw [Nat.mem_divisors]
        exact ⟨⟨p.2, by rw [hkm, mul_comm]⟩, hk⟩
      have hinj : Set.InjOn Prod.fst (↑(s.filter (fun p => g p = k)) : Set (ℕ × ℕ)) := by
        intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
        have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp ha.1).1).1
        have hb1 : 1 ≤ b.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hb.1).1).1
        have hmul : a.1 * a.2 = b.1 * b.2 := by
          have h1 : g a = k := ha.2
          have h2 : g b = k := hb.2
          have h3 : g a = g b := by rw [h1, h2]
          simpa [hg] using h3
        have h2 : a.2 = b.2 := by
          rw [← hab] at hmul
          exact Nat.mul_left_cancel (by omega : 0 < a.1) hmul
        exact Prod.ext hab h2
      calc (s.filter (fun p => g p = k)).card
          = ((s.filter (fun p => g p = k)).image Prod.fst).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ k.divisors.card := Finset.card_le_card hsub
  -- termwise bound on the fibrewise sum
  have hinner : ∀ k ∈ s.image g,
      (∑ p ∈ s.filter (fun p => g p = k), F (g p))
        ≤ F k * ((k.divisors.card : ℝ)) := by
    intro k _
    have hconst : (∑ p ∈ s.filter (fun p => g p = k), F (g p))
        = ((s.filter (fun p => g p = k)).card : ℝ) * F k := by
      rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2]),
        Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    have h1 : (((s.filter (fun p => g p = k)).card : ℕ) : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast hcard k
    nlinarith [hF k]
  calc (∑ k ∈ s.image g, ∑ p ∈ s.filter (fun p => g p = k), F (g p))
      ≤ ∑ k ∈ s.image g, F k * ((k.divisors.card : ℝ)) := Finset.sum_le_sum hinner
    _ ≤ ∑ k ∈ Finset.Icc 1 (Y * M), F k * ((k.divisors.card : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg himage
          (fun k _ _ => mul_nonneg (hF k) (Nat.cast_nonneg _))

/-- The `n`-cardinality defining `anFI` is `Submission.an`. -/
private lemma anFI_eq_an (n : ℕ) : Work.FIPlan.anFI n = Submission.an n := rfl

/-- `Ã(y) ≤ Σ_{n ≤ y} a_n`. -/
private lemma AcountAtil_le_ansum (y : ℕ) :
    Work.FITop.AcountAtil y ≤ ∑ n ∈ Finset.range (y + 1), (Work.FIPlan.anFI n : ℝ) := by
  rw [Work.FITop.AcountAtil, Submission.ASP.Acount, Nat.floor_natCast]
  have h1 : ∀ n ∈ Finset.Icc 1 y, Work.FITop.atilFIa n ≤ (Work.FIPlan.anFI n : ℝ) := by
    intro n _
    rw [Work.FITop.atilFIa_eq_indicator n, anFI_eq_an n]
    split_ifs with h
    · exact le_rfl
    · positivity
  calc (∑ n ∈ Finset.Icc 1 y, Work.FITop.atilFIa n)
      ≤ ∑ n ∈ Finset.Icc 1 y, (Work.FIPlan.anFI n : ℝ) := Finset.sum_le_sum h1
    _ ≤ ∑ n ∈ Finset.range (y + 1), (Work.FIPlan.anFI n : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn => by
            simp only [Finset.mem_Icc] at hn
            simp only [Finset.mem_range]
            omega)
          (fun n _ _ => by positivity)

/-- `Σ_{n ≤ y} a_n ≪ y^{3/4}` (the paper's (3.18)). -/
private lemma ansum_le_const_mul_rpow :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 1 ≤ y →
      (∑ n ∈ Finset.range (y + 1), (Work.FIPlan.anFI n : ℝ)) ≤ C * (y : ℝ) ^ ((3 : ℝ) / 4) := by
  obtain ⟨C, hC, h⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_intpairs_asymptotic
  set κ : ℝ := ∫ u in (0)..1, Real.sqrt (1 - u ^ 4) with hκ
  have hκ0 : 0 ≤ κ := by
    rw [hκ]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => Real.sqrt_nonneg _)
  refine ⟨4 * κ + C, by positivity, fun y hy => ?_⟩
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hsum : (∑ n ∈ Finset.range (y + 1), (Work.FIPlan.anFI n : ℝ))
      = (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (y : ℤ)}).ncard : ℝ) := by
    rw [← Commons.NumberTheory.FriedlanderIwaniec.Aseq_eq_intpairs_ncard y]
    push_cast
    rfl
  rw [hsum]
  have hkey : |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (y : ℤ)}).ncard : ℝ)
      - 4 * κ * (y : ℝ) ^ ((3 : ℝ) / 4)| ≤ C * Real.sqrt y := h y hy
  have h1 : (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (y : ℤ)}).ncard : ℝ)
      - 4 * κ * (y : ℝ) ^ ((3 : ℝ) / 4) ≤ C * Real.sqrt y := (abs_le.mp hkey).2
  have h2 : Real.sqrt (y : ℝ) ≤ (y : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
  have h3 : C * Real.sqrt (y : ℝ) ≤ C * (y : ℝ) ^ ((3 : ℝ) / 4) :=
    mul_le_mul_of_nonneg_left h2 hC.le
  have h4 : 4 * κ * (y : ℝ) ^ ((3 : ℝ) / 4) ≤ (4 * κ + C) * (y : ℝ) ^ ((3 : ℝ) / 4) := by
    have h5 : (0 : ℝ) ≤ (y : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
    nlinarith
  linarith

/-- `τ(n) ≤ τ(mn)` for `m, n ≥ 1`. -/
private lemma card_divisors_le_card_mul (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (n.divisors.card : ℝ) ≤ ((m * n).divisors.card : ℝ) := by
  have hdiv : n.divisors ⊆ (m * n).divisors := by
    intro d hd
    rw [Nat.mem_divisors] at hd ⊢
    obtain ⟨hdvd, _⟩ := hd
    exact ⟨dvd_mul_of_dvd_right hdvd m, Nat.mul_ne_zero (by omega) (by omega)⟩
  exact_mod_cast Finset.card_le_card hdiv

/-- **The `\tau`-weighted double sum** that dominates the small-`m` region of the `\tau`-truncated
`\Pi`-restricted sieve form.  This is the estimate that the proof of `BformAtilSmall_le`
establishes internally (`hstep2`-`hstep6`); it is stated separately so that the truncation step of
`BformPiTauSmall_le` reduces to it. -/
private theorem tauSqDoubleSum_local :
    ∃ C x₀ : ℕ, 0 < C ∧ ∀ (x N Y : ℕ) (ϑ : ℝ), x₀ ≤ x → 1 ≤ N →
      0 < ϑ → 2 * ϑ ≤ 1 → 1 ≤ ϑ * (x : ℝ) → (Y : ℝ) * (N : ℝ) ≤ ϑ * (x : ℝ) →
      (∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc 1 (2 * N),
          (n.divisors.card : ℝ) * Work.FITop.atilFIa (m * n))
        ≤ C * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4) * (Real.log (x : ℝ)) ^ (65536 : ℕ) := by
  obtain ⟨C1, hC1, h1⟩ := Aseq_tau_sq_le_univ
  obtain ⟨C2, hC2, h2⟩ := ansum_le_const_mul_rpow
  set Cbig : ℝ := C1 * (C2 * (3 : ℝ) ^ ((3 : ℝ) / 4) + 1) * (2 : ℝ) ^ (65536 : ℕ) with hCbig
  have hCbig0 : 0 < Cbig := by
    rw [hCbig]
    have h1' : 0 < C2 * (3 : ℝ) ^ ((3 : ℝ) / 4) + 1 := by
      have := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 3) ((3:ℝ)/4)
      nlinarith
    positivity
  refine ⟨⌈Cbig⌉₊ + 1, 3, by omega, ?_⟩
  intro x N Y ϑ hx hN hϑ0 hϑ1 hϑx hYN
  have hx3 : 3 ≤ x := hx
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    calc Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      _ ≤ (x : ℝ) := by exact_mod_cast hx3
  have hlogx0 : 0 ≤ Real.log (x : ℝ) := le_trans zero_le_one hlog1
  have hã : ∀ k, 0 ≤ Work.FITop.atilFIa k := Work.FITop.atilFIa_nonneg
  have hÃx0 : 0 ≤ Work.FITop.AcountAtil x := by
    unfold Work.FITop.AcountAtil Submission.ASP.Acount
    exact Finset.sum_nonneg fun k _ => hã k
  -- step 2: replace `τ(n)` by `τ(mn)`
  have hstep2 : (∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc 1 (2 * N),
          (n.divisors.card : ℝ) * Work.FITop.atilFIa (m * n))
      ≤ ∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc 1 (2 * N),
          ((m * n).divisors.card : ℝ) * Work.FITop.atilFIa (m * n) := by
    apply Finset.sum_le_sum
    intro m hm
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_right
      (card_divisors_le_card_mul m n (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1)
      (hã (m * n))
  -- step 3: the hyperbola reindexing
  have hstep3 : (∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc 1 (2 * N),
          ((m * n).divisors.card : ℝ) * Work.FITop.atilFIa (m * n))
      ≤ ∑ k ∈ Finset.Icc 1 (Y * (2 * N)),
          Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 2) := by
    have h := sum_mul_le_sum_divisors (Y := Y) (M := 2 * N)
      (F := fun k => ((k.divisors.card : ℝ)) * Work.FITop.atilFIa k)
      (fun k => mul_nonneg (Nat.cast_nonneg _) (hã k))
    calc (∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc 1 (2 * N),
            ((m * n).divisors.card : ℝ) * Work.FITop.atilFIa (m * n))
        = ∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc 1 (2 * N),
            (fun k => ((k.divisors.card : ℝ)) * Work.FITop.atilFIa k) (m * n) := rfl
      _ ≤ ∑ k ∈ Finset.Icc 1 (Y * (2 * N)),
            ((k.divisors.card : ℝ)) * Work.FITop.atilFIa k * ((k.divisors.card : ℝ)) := h
      _ = ∑ k ∈ Finset.Icc 1 (Y * (2 * N)),
            Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro k _
          ring
  -- step 4: the divisor-sum bound at `K := Y*(2N)`
  have hKle : ((Y * (2 * N) : ℕ) : ℝ) ≤ (x : ℝ) := by
    push_cast
    nlinarith [hYN, hϑx, hϑ1]
  have h4 : (∑ k ∈ Finset.Icc 1 (Y * (2 * N)),
          Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 2))
      ≤ C1 * (Work.FITop.AcountAtil (Y * (2 * N)) + 1)
          * (Real.log (((Y * (2 * N) : ℕ) : ℝ) + 2)) ^ (65536 : ℕ) := h1 _
  -- step 5: `Ã K + 1 ≤ (C2 3^{3/4} + 1)(ϑx)^{3/4}`
  have hK1 : 1 ≤ Y * (2 * N) + 1 := by omega
  have hÃK : Work.FITop.AcountAtil (Y * (2 * N))
      ≤ C2 * (((Y * (2 * N) + 1 : ℕ)) : ℝ) ^ ((3 : ℝ) / 4) := by
    refine le_trans (AcountAtil_le_ansum (Y * (2 * N))) ?_
    have hle := h2 (Y * (2 * N) + 1) hK1
    refine le_trans ?_ hle
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_range] at hn ⊢
      omega
    · intro n _ _; positivity
  have hK1le : (((Y * (2 * N) + 1 : ℕ)) : ℝ) ≤ 3 * (ϑ * (x : ℝ)) := by
    push_cast
    have hK : ((Y * (2 * N) : ℕ) : ℝ) ≤ 2 * (ϑ * (x : ℝ)) := by
      push_cast; nlinarith [hYN]
    linarith
  have hbase1 : (1 : ℝ) ≤ (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((3 : ℝ) / 4) := by rw [Real.one_rpow]
      _ ≤ (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4) :=
          Real.rpow_le_rpow (by norm_num) hϑx (by norm_num)
  have hbase0 : (0 : ℝ) ≤ (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg (by positivity) _
  have h5 : C1 * (Work.FITop.AcountAtil (Y * (2 * N)) + 1)
      ≤ C1 * (C2 * (3 : ℝ) ^ ((3 : ℝ) / 4) + 1) * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4) := by
    have hrp : (((Y * (2 * N) + 1 : ℕ)) : ℝ) ^ ((3 : ℝ) / 4)
        ≤ (3 * (ϑ * (x : ℝ))) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) hK1le (by norm_num)
    have hsplit : (3 * (ϑ * (x : ℝ))) ^ ((3 : ℝ) / 4)
        = (3 : ℝ) ^ ((3 : ℝ) / 4) * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4) :=
      Real.mul_rpow (by norm_num) (by positivity)
    have hKp : (((Y * (2 * N) + 1 : ℕ)) : ℝ) ^ ((3 : ℝ) / 4)
        ≤ (3 : ℝ) ^ ((3 : ℝ) / 4) * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4) :=
      le_trans hrp (le_of_eq hsplit)
    have hstepA : Work.FITop.AcountAtil (Y * (2 * N)) + 1
        ≤ C2 * ((3 : ℝ) ^ ((3 : ℝ) / 4) * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4)) + 1 := by
      have hC2r : C2 * (((Y * (2 * N) + 1 : ℕ)) : ℝ) ^ ((3 : ℝ) / 4)
          ≤ C2 * ((3 : ℝ) ^ ((3 : ℝ) / 4) * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left hKp hC2.le
      linarith
    have hstepB : C2 * ((3 : ℝ) ^ ((3 : ℝ) / 4) * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4)) + 1
        ≤ (C2 * (3 : ℝ) ^ ((3 : ℝ) / 4) + 1) * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4) := by
      have h1' : (1 : ℝ) ≤ (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4) := hbase1
      nlinarith [hbase0, hC2.le, Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 3) ((3:ℝ)/4)]
    calc C1 * (Work.FITop.AcountAtil (Y * (2 * N)) + 1)
        ≤ C1 * (C2 * ((3 : ℝ) ^ ((3 : ℝ) / 4) * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4)) + 1) :=
          mul_le_mul_of_nonneg_left hstepA hC1.le
      _ ≤ C1 * ((C2 * (3 : ℝ) ^ ((3 : ℝ) / 4) + 1) * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left hstepB hC1.le
      _ = C1 * (C2 * (3 : ℝ) ^ ((3 : ℝ) / 4) + 1) * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4) := by ring
  -- step 6: the logarithm
  have h6 : (Real.log (((Y * (2 * N) : ℕ) : ℝ) + 2)) ^ (65536 : ℕ)
      ≤ (2 : ℝ) ^ (65536 : ℕ) * (Real.log (x : ℝ)) ^ (65536 : ℕ) := by
    have h1' : ((Y * (2 * N) : ℕ) : ℝ) + 2 ≤ 2 * (x : ℝ) := by
      push_cast
      nlinarith [hYN, hϑx, hϑ1, hx1]
    have hlog : Real.log (((Y * (2 * N) : ℕ) : ℝ) + 2) ≤ Real.log (2 * (x : ℝ)) :=
      Real.log_le_log (by positivity) h1'
    have hlog2x : Real.log (2 * (x : ℝ)) = Real.log 2 + Real.log (x : ℝ) :=
      Real.log_mul (by norm_num) (by linarith)
    have hlog2le : Real.log 2 ≤ Real.log (x : ℝ) := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast (by omega : 2 ≤ x)
    have hlogle : Real.log (((Y * (2 * N) : ℕ) : ℝ) + 2) ≤ 2 * Real.log (x : ℝ) := by
      rw [hlog2x] at hlog; linarith
    have hlogK0 : 0 ≤ Real.log (((Y * (2 * N) : ℕ) : ℝ) + 2) := by
      apply Real.log_nonneg
      push_cast
      have : (0 : ℝ) ≤ (Y : ℝ) := Nat.cast_nonneg Y
      have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      nlinarith
    have h2log0 : 0 ≤ 2 * Real.log (x : ℝ) := by linarith
    calc (Real.log (((Y * (2 * N) : ℕ) : ℝ) + 2)) ^ (65536 : ℕ)
        ≤ (2 * Real.log (x : ℝ)) ^ (65536 : ℕ) := pow_le_pow_left₀ hlogK0 hlogle 65536
      _ = (2 : ℝ) ^ (65536 : ℕ) * (Real.log (x : ℝ)) ^ (65536 : ℕ) := by
          rw [mul_pow]
  -- assembly
  have hCc_le : Cbig ≤ ((⌈Cbig⌉₊ + 1 : ℕ) : ℝ) := by
    have h1'' : Cbig ≤ ((⌈Cbig⌉₊ : ℕ) : ℝ) := Nat.le_ceil Cbig
    have h2'' : ((⌈Cbig⌉₊ : ℕ) : ℝ) ≤ ((⌈Cbig⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    linarith
  have hlogxpow0 : (0 : ℝ) ≤ (Real.log (x : ℝ)) ^ (65536 : ℕ) := pow_nonneg hlogx0 65536
  have hbasepow0 : (0 : ℝ) ≤ (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4) := hbase0
  calc (∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc 1 (2 * N),
          (n.divisors.card : ℝ) * Work.FITop.atilFIa (m * n))
    _ ≤ ∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ Finset.Icc 1 (2 * N),
          ((m * n).divisors.card : ℝ) * Work.FITop.atilFIa (m * n) := hstep2
    _ ≤ ∑ k ∈ Finset.Icc 1 (Y * (2 * N)),
          Work.FITop.atilFIa k * ((k.divisors.card : ℝ) ^ 2) := hstep3
    _ ≤ C1 * (Work.FITop.AcountAtil (Y * (2 * N)) + 1)
          * (Real.log (((Y * (2 * N) : ℕ) : ℝ) + 2)) ^ (65536 : ℕ) := h4
    _ ≤ C1 * (C2 * (3 : ℝ) ^ ((3 : ℝ) / 4) + 1) * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4)
          * (Real.log (((Y * (2 * N) : ℕ) : ℝ) + 2)) ^ (65536 : ℕ) :=
        mul_le_mul_of_nonneg_right h5
          (pow_nonneg (Real.log_nonneg (by
            have hnn : (0 : ℝ) ≤ ((Y * (2 * N) : ℕ) : ℝ) := Nat.cast_nonneg _
            linarith)) _)
    _ ≤ C1 * (C2 * (3 : ℝ) ^ ((3 : ℝ) / 4) + 1) * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4)
          * ((2 : ℝ) ^ (65536 : ℕ) * (Real.log (x : ℝ)) ^ (65536 : ℕ)) := by
        apply mul_le_mul_of_nonneg_left h6
        have h3p : (0 : ℝ) < (3 : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
        have hC23 : (0 : ℝ) ≤ C2 * (3 : ℝ) ^ ((3 : ℝ) / 4) + 1 :=
          add_nonneg (mul_nonneg hC2.le (le_of_lt h3p)) (by norm_num)
        exact mul_nonneg (mul_nonneg hC1.le hC23) hbasepow0
    _ = Cbig * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4) * (Real.log (x : ℝ)) ^ (65536 : ℕ) := by
        rw [hCbig]; ring
    _ ≤ ((⌈Cbig⌉₊ + 1 : ℕ) : ℝ) * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4)
          * (Real.log (x : ℝ)) ^ (65536 : ℕ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCc_le hbasepow0) hlogxpow0

/-- **The `\tau`-truncated, `\Pi`-restricted small-`m` region of the reduction.** -/
theorem BformPiTauSmall_le :
    ∃ C x₀ : ℕ, 0 < C ∧ ∀ (x N Y Pz : ℕ) (Ccoe τ ϑ : ℝ), x₀ ≤ x → 1 ≤ N →
      0 < ϑ → 2 * ϑ ≤ 1 → 1 ≤ ϑ * (x : ℝ) → (Y : ℝ) * (N : ℝ) ≤ ϑ * (x : ℝ) →
      (∑ m ∈ Finset.Icc 1 Y, |∑ n ∈ Finset.Icc 1 (2 * N),
          (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
            then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc Ccoe n
              * Work.FITop.atilFIa (m * n) else 0)|)
        ≤ C * (ϑ * (x : ℝ)) ^ ((3 : ℝ) / 4) * (Real.log (x : ℝ)) ^ (65536 : ℕ) := by
  obtain ⟨C, x₀, hC, hbound⟩ := tauSqDoubleSum_local
  refine ⟨C, x₀, hC, ?_⟩
  intro x N Y Pz Ccoe τ ϑ hx hN hϑ0 hϑ1 hϑx hYN
  refine le_trans ?_ (hbound x N Y ϑ hx hN hϑ0 hϑ1 hϑx hYN)
  -- the two extra support conditions `PiCond`, `TauCond` only shrink each inner sum
  apply Finset.sum_le_sum
  intro m _
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun n _ => ?_))
  by_cases hcond : N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
  · rw [if_pos hcond]
    have hmu : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := abs_moebius_cast_le_one n
    have hgam : |Work.FIPlan.gammaTrunc Ccoe n| ≤ (n.divisors.card : ℝ) :=
      Work.FITop4.abs_gammaTrunc_le Ccoe n
    have hã0 : 0 ≤ Work.FITop.atilFIa (m * n) := Work.FITop.atilFIa_nonneg _
    rw [abs_mul, abs_mul, abs_of_nonneg hã0]
    calc |((ArithmeticFunction.moebius n : ℤ) : ℝ)| * |Work.FIPlan.gammaTrunc Ccoe n|
          * Work.FITop.atilFIa (m * n)
        ≤ 1 * (n.divisors.card : ℝ) * Work.FITop.atilFIa (m * n) := by gcongr
      _ = (n.divisors.card : ℝ) * Work.FITop.atilFIa (m * n) := by ring
  · rw [if_neg hcond]
    simp only [abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Work.FITop.atilFIa_nonneg _)

end

end Work.FITop4.Red5

