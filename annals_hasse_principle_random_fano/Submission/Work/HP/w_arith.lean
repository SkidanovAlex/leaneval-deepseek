import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.w_arith_growth

/-!
# Arithmetic input on `W = ∏_{p ≤ w} p^{r_p(w)}` and `wOf B = log B / log log B`

This file proves `Work.HP.w_arith`, the arithmetic input consumed by the `w_bound` /
`bigW_le_pow` circle of estimates:

* every positive integer `m ≤ w` divides `W / rad(W)` (equivalently, `W/rad W` is divisible by
  `lcm(1,2,…,⌊w⌋)` up to the `⌈w⌉` boundary), and
* `wOf B^{n-2}` eventually dominates `(log B)^{1/2}` for `n ≥ 3` (proved separately in
  `Submission.Work.HP.w_arith_growth` and imported here).

The first part is the formal content behind the paper's observation
`v_p(W/rad W) = ⌈log w / log p⌉ ≥ log w / log p` (Browning–Le Boudec–Sawin, §4, around
Definition of the radical): the powers of every prime `p ≤ w` occurring in `m` are absorbed,
and no prime `> w` can occur in `m ≤ w`.
-/

set_option autoImplicit false

open Filter

namespace Work.HP

/-- `W = rad(W) · ∏_{p ≤ w} p^{r_p(w) - 1}`: peeling off one copy of each prime `≤ w`. -/
private lemma bigW_eq_radW_mul (w : ℝ) :
    bigW w = radW w * ∏ p ∈ (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime,
      p ^ (rOf p w - 1) := by
  rw [bigW, radW, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  have h1 : 1 ≤ rOf p w := by rw [rOf]; exact Nat.le_add_left 1 _
  calc p ^ rOf p w = p ^ (rOf p w - 1 + 1) := by rw [Nat.sub_add_cancel h1]
    _ = p * p ^ (rOf p w - 1) := by rw [pow_succ']

/-- `W / rad(W) = ∏_{p ≤ w} p^{r_p(w) - 1}`. -/
private lemma bigW_div_radW (w : ℝ) :
    bigW w / radW w = ∏ p ∈ (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime,
      p ^ (rOf p w - 1) := by
  have hpos : 0 < radW w := by
    rw [radW]
    exact Finset.prod_pos fun p hp => Nat.Prime.pos (Finset.mem_filter.mp hp).2
  rw [bigW_eq_radW_mul w, Nat.mul_div_cancel_left _ hpos]

/-- Every `m ≥ 1` with `m ≤ w` divides `W / rad(W)`. -/
private lemma dvd_bigW_div_radW (w : ℝ) (m : ℕ) (hm : 1 ≤ m) (hmw : (m : ℝ) ≤ w) :
    m ∣ bigW w / radW w := by
  rw [bigW_div_radW w]
  set P := ∏ p ∈ (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime, p ^ (rOf p w - 1) with hP
  have hm0 : m ≠ 0 := by omega
  have hP0 : P ≠ 0 := by
    rw [hP]
    refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
    exact pow_ne_zero _ (Nat.Prime.ne_zero (Finset.mem_filter.mp hp).2)
  -- it suffices to compare `p`-adic valuations for primes `p`
  rw [← Nat.factorization_prime_le_iff_dvd hm0 hP0]
  intro q hq
  by_cases hqF : q ∈ (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime
  · -- `q ≤ w`: the valuation of `q` in `P` is `r_p(w) - 1 = clog q ⌈w⌉`
    have hdvd : q ^ (rOf q w - 1) ∣ P := by
      rw [hP]
      exact Finset.dvd_prod_of_mem _ hqF
    have hPfac : rOf q w - 1 ≤ P.factorization q :=
      (Nat.Prime.pow_dvd_iff_le_factorization hq hP0).mp hdvd
    have hcle : rOf q w - 1 = Nat.clog q ⌈w⌉₊ := by simp [rOf]
    have hmfac : m.factorization q ≤ rOf q w - 1 := by
      rw [hcle]
      by_cases hdiv : q ∣ m
      · -- `q ^ v_q(m) ≤ m ≤ ⌈w⌉ ≤ q ^ clog q ⌈w⌉`
        have h1 : q ^ m.factorization q ∣ m := Nat.ordProj_dvd m q
        have h2 : q ^ m.factorization q ≤ m := Nat.le_of_dvd (by omega) h1
        have hmceil : m ≤ ⌈w⌉₊ := by
          have h3 : (m : ℝ) ≤ (⌈w⌉₊ : ℝ) := le_trans hmw (Nat.le_ceil w)
          exact_mod_cast h3
        have h4 : m ≤ q ^ Nat.clog q ⌈w⌉₊ := le_trans hmceil (Nat.le_pow_clog hq.one_lt _)
        exact (Nat.pow_le_pow_iff_right hq.one_lt).mp (le_trans h2 h4)
      · rw [Nat.factorization_eq_zero_of_not_dvd hdiv]
        exact Nat.zero_le _
    exact le_trans hmfac hPfac
  · -- no prime `q ∤ m` with `q > w` can divide `m`
    have hnotdvd : ¬ q ∣ m := by
      intro hdvd
      have hqm : q ≤ m := Nat.le_of_dvd (by omega) hdvd
      have hqw : (q : ℝ) ≤ w := le_trans (by exact_mod_cast hqm) hmw
      have hqfloor : q ≤ ⌊w⌋₊ := Nat.le_floor hqw
      exact hqF (by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hqfloor), hq⟩)
    rw [Nat.factorization_eq_zero_of_not_dvd hnotdvd]
    exact Nat.zero_le _

theorem w_arith (n : ℕ) (hn : 3 ≤ n) :
    (∀ (w : ℝ), 0 ≤ w → ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ w → m ∣ bigW w / radW w) ∧
    (∀ᶠ B in atTop, Real.log B ^ ((1 : ℝ) / 2) ≤ wOf B ^ (n - 2)) :=
  ⟨fun w _ m hm hmw => dvd_bigW_div_radW w m hm hmw, w_arith_growth n hn⟩

end Work.HP
