import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeZeta_pole
import Submission.Commons.NumberTheory.Diophantine.mertens_three_mod_four_prod_bound
import Submission.Commons.NumberTheory.FriedlanderIwaniec.chi4_prime_recip_converges
import Submission.Commons.Analysis.DirichletSeries.abel_tendsto_tsum_mul_rpow_conditional

open scoped BigOperators Topology
open Filter

set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.Diophantine

noncomputable section

/-! ## The `3`-mod-`4`-free Dirichlet series -/

/-- The set of naturals with no prime factor congruent to `3` mod `4`. -/
private def Sfree : Set ℕ := {n : ℕ | ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ n}

/-- Its indicator, as a real function. -/
private def aa (n : ℕ) : ℝ := Set.indicator Sfree (fun _ => (1 : ℝ)) n

private lemma aa_of_mem {n : ℕ} (h : n ∈ Sfree) : aa n = 1 := by
  rw [aa, Set.indicator_of_mem h]

private lemma aa_of_notMem {n : ℕ} (h : n ∉ Sfree) : aa n = 0 := by
  rw [aa, Set.indicator_of_notMem h]

private lemma mem_Sfree_mul (m n : ℕ) : m * n ∈ Sfree ↔ m ∈ Sfree ∧ n ∈ Sfree := by
  constructor
  · intro h
    exact ⟨fun p hp hp4 hdvd => h p hp hp4 (dvd_mul_of_dvd_left hdvd n),
           fun p hp hp4 hdvd => h p hp hp4 (dvd_mul_of_dvd_right hdvd m)⟩
  · rintro ⟨hm, hn⟩ p hp hp4 hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact hm p hp hp4 h
    · exact hn p hp hp4 h

private lemma aa_mul (m n : ℕ) : aa (m * n) = aa m * aa n := by
  by_cases hm : m ∈ Sfree
  · by_cases hn : n ∈ Sfree
    · have hmn : m * n ∈ Sfree := (mem_Sfree_mul m n).mpr ⟨hm, hn⟩
      rw [aa_of_mem hmn, aa_of_mem hm, aa_of_mem hn, mul_one]
    · have hmn : m * n ∉ Sfree := fun h => hn ((mem_Sfree_mul m n).mp h).2
      rw [aa_of_notMem hmn, aa_of_mem hm, aa_of_notMem hn, mul_zero]
  · have hmn : m * n ∉ Sfree := fun h => hm ((mem_Sfree_mul m n).mp h).1
    rw [aa_of_notMem hmn, aa_of_notMem hm, zero_mul]

private lemma aa_zero : aa 0 = 0 := by
  refine aa_of_notMem (fun h => ?_)
  exact h 3 (by norm_num) (by norm_num) (dvd_zero 3)

private lemma aa_one : aa 1 = 1 := by
  refine aa_of_mem (fun p hp _ hdvd => ?_)
  exact hp.not_dvd_one hdvd

private lemma aa_eq_one_or_zero (n : ℕ) : aa n = 1 ∨ aa n = 0 := by
  by_cases h : n ∈ Sfree
  · exact Or.inl (aa_of_mem h)
  · exact Or.inr (aa_of_notMem h)

private lemma aa_nonneg (n : ℕ) : 0 ≤ aa n := by
  rcases aa_eq_one_or_zero n with h | h <;> simp [h]

private lemma aa_le_one (n : ℕ) : aa n ≤ 1 := by
  rcases aa_eq_one_or_zero n with h | h <;> simp [h]

/-- The completely multiplicative function `n ↦ a n * n^(-s)`. -/
private def fser (s : ℝ) : ℕ →*₀ ℝ where
  toFun n := aa n * (n : ℝ) ^ (-s)
  map_zero' := by rw [aa_zero, zero_mul]
  map_one' := by simp [aa_one]
  map_mul' m n := by
    show aa (m * n) * ((m * n : ℕ) : ℝ) ^ (-s)
      = (aa m * (m : ℝ) ^ (-s)) * (aa n * (n : ℝ) ^ (-s))
    rw [aa_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring

private lemma summable_fser_norm (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => ‖fser s n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (Real.summable_nat_rpow.mpr (show -s < -1 by linarith))
  show ‖aa n * (n : ℝ) ^ (-s)‖ ≤ (n : ℝ) ^ (-s)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (aa_nonneg n),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) (aa_le_one n)

/-! ## The logarithm of the Euler product -/

private def gfun (s : ℝ) (p : ℕ) : ℝ :=
  if p.Prime then -Real.log (1 - (p : ℝ) ^ (-s)) else 0

private def Gterm (s : ℝ) (p : ℕ) : ℝ := aa p * gfun s p

private def G (s : ℝ) : ℝ := ∑' p : ℕ, Gterm s p

private lemma abs_log_one_sub_le_two {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    |Real.log (1 - x)| ≤ 2 * x := by
  have hle0 : Real.log (1 - x) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hneg : 0 ≤ -Real.log (1 - x) - x :=
    Commons.NumberTheory.Mertens.g_nonneg (by linarith)
  have hle : -Real.log (1 - x) - x ≤ 2 * x ^ 2 :=
    Commons.NumberTheory.Mertens.g_le_two_sq hx0 hx
  have h2 : 2 * x ^ 2 ≤ x := by
    have : x * (2 * x - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx0 (by linarith)
    nlinarith [this]
  rw [abs_of_nonpos hle0]
  linarith

private lemma rpow_neg_le_half {p : ℕ} (hp : 2 ≤ p) {s : ℝ} (hs : 1 ≤ s) :
    (p : ℝ) ^ (-s) ≤ 1 / 2 := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  rw [Real.rpow_neg_one] at h1
  calc (p : ℝ) ^ (-s) ≤ (p : ℝ)⁻¹ := h1
    _ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
    _ = 1 / 2 := by norm_num

private lemma abs_gfun_le {s : ℝ} (hs : 1 ≤ s) (p : ℕ) :
    |gfun s p| ≤ 2 * (p : ℝ) ^ (-s) := by
  rw [gfun]
  split_ifs with hp
  · have hx0 : 0 ≤ (p : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    simpa only [abs_neg] using abs_log_one_sub_le_two hx0 (rpow_neg_le_half hp.two_le hs)
  · rw [abs_zero]; positivity

private lemma summable_Gterm (s : ℝ) (hs : 1 < s) :
    Summable (fun p : ℕ => Gterm s p) := by
  refine Summable.of_norm_bounded (g := fun p : ℕ => 2 * (p : ℝ) ^ (-s))
    ((Real.summable_nat_rpow.mpr (show -s < -1 by linarith)).mul_left 2)
    (fun p => ?_)
  show ‖Gterm s p‖ ≤ 2 * (p : ℝ) ^ (-s)
  rw [Gterm, Real.norm_eq_abs, abs_mul, abs_of_nonneg (aa_nonneg p)]
  calc aa p * |gfun s p| ≤ 1 * (2 * (p : ℝ) ^ (-s)) :=
        mul_le_mul (aa_le_one p) (abs_gfun_le (le_of_lt hs) p) (abs_nonneg _) (by norm_num)
    _ = 2 * (p : ℝ) ^ (-s) := one_mul _

private lemma Gterm_eq_neg_log {s : ℝ} {p : ℕ} (hp : p.Prime) :
    Gterm s p = -Real.log (1 - fser s p) := by
  have h : fser s p = aa p * (p : ℝ) ^ (-s) := rfl
  by_cases hmem : p ∈ Sfree
  · rw [Gterm, gfun, if_pos hp, h, aa_of_mem hmem]; ring
  · rw [Gterm, gfun, if_pos hp, h, aa_of_notMem hmem]; simp

private lemma one_sub_fser_prime_pos {s : ℝ} (hs : 1 < s) {p : ℕ} (hp : p.Prime) :
    0 < 1 - fser s p := by
  have hle : fser s p ≤ 1 / 2 := by
    show aa p * (p : ℝ) ^ (-s) ≤ 1 / 2
    calc aa p * (p : ℝ) ^ (-s) ≤ 1 * (1 / 2) :=
          mul_le_mul (aa_le_one p) (rpow_neg_le_half hp.two_le (le_of_lt hs))
            (Real.rpow_nonneg (Nat.cast_nonneg p) _) (by norm_num)
      _ = 1 / 2 := one_mul _
  linarith

private lemma exp_Gterm {s : ℝ} (hs : 1 < s) {p : ℕ} (hp : p.Prime) :
    Real.exp (Gterm s p) = (1 - fser s p)⁻¹ := by
  rw [Gterm_eq_neg_log hp, Real.exp_neg, Real.exp_log (one_sub_fser_prime_pos hs hp)]

private lemma sum_primesBelow_Gterm (s : ℝ) (N : ℕ) :
    (∑ p ∈ Nat.primesBelow N, Gterm s p) = ∑ p ∈ Finset.range N, Gterm s p := by
  rw [Nat.primesBelow_eq_filter_range, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p.Prime
  · rw [if_pos hp]
  · rw [if_neg hp, Gterm, gfun, if_neg hp, mul_zero]

private lemma exp_partial_Gterm (s : ℝ) (hs : 1 < s) (N : ℕ) :
    (∏ p ∈ Nat.primesBelow N, (1 - fser s p)⁻¹)
      = Real.exp (∑ p ∈ Nat.primesBelow N, Gterm s p) := by
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun p hp => ?_
  exact (exp_Gterm hs (Nat.mem_primesBelow.mp hp).2).symm

private lemma tendsto_partial_Gterm (s : ℝ) (hs : 1 < s) :
    Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesBelow N, Gterm s p) atTop (nhds (G s)) := by
  have h := (summable_Gterm s hs).hasSum.tendsto_sum_nat
  refine h.congr fun N => ?_
  exact (sum_primesBelow_Gterm s N).symm

private lemma series_eq_exp_G (s : ℝ) (hs : 1 < s) :
    (∑' n : ℕ, fser s n) = Real.exp (G s) := by
  have hsumm := summable_fser_norm s hs
  have hprod : Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, (1 - fser s p)⁻¹) atTop
      (nhds (∑' n : ℕ, fser s n)) :=
    EulerProduct.eulerProduct_completely_multiplicative hsumm
  have hexp : Tendsto (fun N : ℕ => Real.exp (∑ p ∈ Nat.primesBelow N, Gterm s p)) atTop
      (nhds (Real.exp (G s))) :=
    Real.continuous_exp.tendsto (G s) |>.comp (tendsto_partial_Gterm s hs)
  have heq : (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, (1 - fser s p)⁻¹)
      = fun N : ℕ => Real.exp (∑ p ∈ Nat.primesBelow N, Gterm s p) :=
    funext fun N => exp_partial_Gterm s hs N
  rw [heq] at hprod
  exact tendsto_nhds_unique hprod hexp

/-! ## Facts about `χ₄` and the pointwise identity `2a_p - 1 = χ₄(p) + [p = 2]` -/

private def c4 (n : ℕ) : ℝ := ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ)

private lemma c4_eq (n : ℕ) :
    c4 n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 := by
  rw [c4, ZMod.χ₄_nat_eq_if_mod_four]
  push_cast
  ring

private lemma c4_one_mod {n : ℕ} (h : n % 4 = 1) : c4 n = 1 := by
  rw [c4, ZMod.χ₄_nat_one_mod_four h]; norm_num

private lemma c4_three_mod {n : ℕ} (h : n % 4 = 3) : c4 n = -1 := by
  rw [c4, ZMod.χ₄_nat_three_mod_four h]; norm_num

private lemma c4_two : c4 2 = 0 := by
  rw [c4, ZMod.χ₄_nat_eq_if_mod_four]; norm_num

private lemma c4_abs_le_one (n : ℕ) : |c4 n| ≤ 1 := by
  rw [c4, ZMod.χ₄_nat_eq_if_mod_four]
  push_cast
  split_ifs <;> norm_num

private lemma mem_Sfree_prime {p : ℕ} (hp : p.Prime) : p ∈ Sfree ↔ p % 4 ≠ 3 := by
  constructor
  · intro h h3
    exact h p hp h3 (dvd_refl p)
  · intro h q hq hq4 hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact hq.ne_one h1
    · rw [h1] at hq4; exact h hq4

private lemma two_aa_sub_one (p : ℕ) (hp : p.Prime) :
    2 * aa p - 1 = c4 p + (if p = 2 then 1 else 0) := by
  rcases Commons.NumberTheory.Diophantine.prime_mod_four p hp with h1 | h2 | h3
  · have hpne : p ≠ 2 := by rintro rfl; norm_num at h1
    rw [aa_of_mem ((mem_Sfree_prime hp).mpr (by omega)), c4_one_mod h1, if_neg hpne]
    norm_num
  · have hp2 : p = 2 := by
      rcases hp.eq_two_or_odd with h | h
      · exact h
      · omega
    subst hp2
    rw [aa_of_mem ((mem_Sfree_prime (by norm_num)).mpr (by norm_num)), c4_two, if_pos rfl]
    norm_num
  · have hpne : p ≠ 2 := by rintro rfl; norm_num at h3
    rw [aa_of_notMem (fun hm => (mem_Sfree_prime hp).mp hm h3), c4_three_mod h3, if_neg hpne]
    norm_num

/-! ## The prime zeta comparison -/

private def W (s : ℝ) : ℝ := ∑' p : ℕ, gfun s p

private lemma W_eq_logSum (s : ℝ) :
    W s = Commons.NumberTheory.Mertens.primeZetaLogSum s := by
  simp only [W, Commons.NumberTheory.Mertens.primeZetaLogSum, Nat.Primes]
  have h1 : (∑' x : ℕ, gfun s x)
      = ∑' x : ℕ, Set.indicator {p : ℕ | p.Prime}
          (fun p : ℕ => -Real.log (1 - (p : ℝ) ^ (-s))) x :=
    tsum_congr fun x => by
      rw [gfun, Set.indicator_apply]
      by_cases hx : x.Prime <;> simp [hx]
  rw [h1]
  exact (tsum_subtype {p : ℕ | p.Prime}
    (fun p : ℕ => -Real.log (1 - (p : ℝ) ^ (-s)))).symm

private lemma tendsto_W :
    Tendsto (fun s : ℝ => W s + Real.log (s - 1)) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have h := Commons.NumberTheory.Mertens.tendsto_primeZetaLogSum_add_log_sub
  refine h.congr' (Eventually.of_forall fun s => ?_)
  simp only [W_eq_logSum]

/-! ## Summability of the auxiliary series -/

private lemma summable_gfun (s : ℝ) (hs : 1 < s) : Summable (fun p : ℕ => gfun s p) := by
  refine Summable.of_norm_bounded (g := fun p : ℕ => 2 * (p : ℝ) ^ (-s))
    ((Real.summable_nat_rpow.mpr (show -s < -1 by linarith)).mul_left 2) (fun p => ?_)
  rw [Real.norm_eq_abs]
  exact abs_gfun_le (le_of_lt hs) p

private lemma summable_chiG (s : ℝ) (hs : 1 < s) :
    Summable (fun p : ℕ => c4 p * gfun s p) := by
  refine Summable.of_norm_bounded (g := fun p : ℕ => 2 * (p : ℝ) ^ (-s))
    ((Real.summable_nat_rpow.mpr (show -s < -1 by linarith)).mul_left 2) (fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |c4 p| * |gfun s p| ≤ 1 * (2 * (p : ℝ) ^ (-s)) :=
        mul_le_mul (c4_abs_le_one p) (abs_gfun_le (le_of_lt hs) p) (abs_nonneg _) (by norm_num)
    _ = 2 * (p : ℝ) ^ (-s) := one_mul _

/-! ## The `pTerm` / `ccTerm` decomposition of the `χ₄`-twisted series -/

private def bAb (n : ℕ) : ℝ := if n.Prime then c4 n / (n : ℝ) else 0

private def pTerm (s : ℝ) (p : ℕ) : ℝ := if p.Prime then c4 p * (p : ℝ) ^ (-s) else 0

private def ccTerm (s : ℝ) (p : ℕ) : ℝ :=
  c4 p * (gfun s p - (if p.Prime then (p : ℝ) ^ (-s) else 0))

private def chiG (s : ℝ) : ℝ := ∑' p : ℕ, c4 p * gfun s p

private lemma pTerm_eq (s : ℝ) (p : ℕ) :
    pTerm s p = bAb p * (p : ℝ) ^ (-(s - 1)) := by
  rw [pTerm, bAb]
  by_cases hp : p.Prime
  · rw [if_pos hp, if_pos hp]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have h1 : (p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ (-(s - 1)) = (p : ℝ) ^ (-s) := by
      rw [← Real.rpow_add hp0]; ring_nf
    rw [div_eq_mul_inv, ← Real.rpow_neg_one (p : ℝ), mul_assoc, h1]
  · rw [if_neg hp, if_neg hp, zero_mul]

private lemma summable_bAb_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => bAb n * (n : ℝ) ^ (-(s - 1))) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) ^ (-s))
    (Real.summable_nat_rpow.mpr (show -s < -1 by linarith)) (fun n => ?_)
  rw [Real.norm_eq_abs, bAb]
  by_cases hn : n.Prime
  · rw [if_pos hn]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.pos
    rw [abs_mul, abs_div, abs_of_nonneg (le_of_lt hn0),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    calc |c4 n| / (n : ℝ) * (n : ℝ) ^ (-(s - 1))
        ≤ 1 / (n : ℝ) * (n : ℝ) ^ (-(s - 1)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          exact div_le_div_of_nonneg_right (c4_abs_le_one n) (le_of_lt hn0)
      _ = (n : ℝ) ^ (-s) := by
          rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hn0]; ring_nf
  · rw [if_neg hn, zero_mul, abs_zero]; positivity

private lemma summable_pTerm (s : ℝ) (hs : 1 < s) :
    Summable (fun p : ℕ => pTerm s p) := by
  refine Summable.of_norm_bounded (g := fun p : ℕ => (p : ℝ) ^ (-s))
    (Real.summable_nat_rpow.mpr (show -s < -1 by linarith)) (fun p => ?_)
  rw [pTerm, Real.norm_eq_abs]
  by_cases hp : p.Prime
  · rw [if_pos hp, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    calc |c4 p| * (p : ℝ) ^ (-s) ≤ 1 * (p : ℝ) ^ (-s) :=
          mul_le_mul_of_nonneg_right (c4_abs_le_one p) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
      _ = (p : ℝ) ^ (-s) := one_mul _
  · rw [if_neg hp, abs_zero]; positivity

private lemma partial_bAb_tendsto :
    ∃ L : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, bAb n) atTop (nhds L) := by
  obtain ⟨cc, hcc⟩ := Commons.NumberTheory.FriedlanderIwaniec.chi4_prime_recip_converges
  refine ⟨cc.re, ?_⟩
  have hre : Tendsto (fun y : ℝ => ∑ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime,
      ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ) / (p : ℝ)) atTop (nhds cc.re) := by
    have h := (Complex.continuous_re.tendsto cc).comp hcc
    refine h.congr fun y => ?_
    rw [Function.comp_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Complex.ofReal_intCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
      Complex.ofReal_re]
  have hN : Tendsto (fun N : ℕ => ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
      ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ) / (p : ℝ)) atTop (nhds cc.re) := by
    have hFn := hre.comp tendsto_natCast_atTop_atTop
    simp only [Function.comp_def] at hFn
    simpa only [Nat.floor_natCast] using hFn
  have hM : Tendsto (fun M : ℕ => ∑ p ∈ (Finset.range M).filter Nat.Prime,
      ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ) / (p : ℝ)) atTop (nhds cc.re) :=
    (Filter.tendsto_add_atTop_iff_nat (f := fun M : ℕ =>
      ∑ p ∈ (Finset.range M).filter Nat.Prime,
        ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ) / (p : ℝ)) 1).mp hN
  refine hM.congr fun M => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [bAb, c4]

private lemma abel_pTerm :
    ∃ L : ℝ, Tendsto (fun s : ℝ => ∑' p : ℕ, pTerm s p)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds L) := by
  obtain ⟨L, hL⟩ := partial_bAb_tendsto
  refine ⟨L, ?_⟩
  have ha0 : bAb 0 = 0 := by simp [bAb]
  have habel :=
    Commons.Analysis.DirichletSeries.abel_tendsto_tsum_mul_rpow_conditional ha0 hL
  have hshift : Tendsto (fun s : ℝ => s - 1) (nhdsWithin 1 (Set.Ioi 1))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h : Tendsto (fun s : ℝ => s - 1) (nhds (1 : ℝ)) (nhds (1 - 1)) :=
        tendsto_id.sub tendsto_const_nhds
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_Ioi] at hs ⊢; linarith
  have hcomp := habel.comp hshift
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Function.comp_apply]
  rw [tsum_eq_of_summable_unconditional (summable_bAb_rpow s hs)]
  exact tsum_congr fun p => (pTerm_eq s p).symm

private lemma abs_ccTerm_bound {s : ℝ} (hs : 1 ≤ s) (p : ℕ) :
    |ccTerm s p| ≤ 2 * (p : ℝ) ^ (-2 : ℝ) := by
  rw [ccTerm]
  by_cases hp : p.Prime
  · rw [if_pos hp, abs_mul, gfun, if_pos hp]
    have hx0 : 0 ≤ (p : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    have hx : (p : ℝ) ^ (-s) ≤ 1 / 2 := rpow_neg_le_half hp.two_le hs
    have hcore : |(-Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s))|
        ≤ 2 * ((p : ℝ) ^ (-s)) ^ (2 : ℝ) := by
      have ha : 0 ≤ -Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s) :=
        Commons.NumberTheory.Mertens.g_nonneg (by linarith)
      rw [abs_of_nonneg ha]
      simpa only [Real.rpow_two, pow_two] using
        Commons.NumberTheory.Mertens.g_le_two_sq hx0 hx
    have hsq : ((p : ℝ) ^ (-s)) ^ (2 : ℝ) ≤ (p : ℝ) ^ (-2 : ℝ) := by
      rw [← Real.rpow_mul (Nat.cast_nonneg p) (-s) 2]
      refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) ?_
      push_cast; nlinarith [hs]
    calc |c4 p| * |(-Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s))|
        ≤ 1 * (2 * ((p : ℝ) ^ (-s)) ^ (2 : ℝ)) :=
          mul_le_mul (c4_abs_le_one p) hcore (abs_nonneg _) (by norm_num)
      _ = 2 * ((p : ℝ) ^ (-s)) ^ (2 : ℝ) := one_mul _
      _ ≤ 2 * (p : ℝ) ^ (-2 : ℝ) := by nlinarith [hsq]
  · rw [if_neg hp]
    simp only [gfun, if_neg hp, sub_zero, mul_zero, abs_zero]
    positivity

private lemma summable_ccTerm (s : ℝ) (hs : 1 < s) :
    Summable (fun p : ℕ => ccTerm s p) := by
  refine Summable.of_norm_bounded (g := fun p : ℕ => 2 * (p : ℝ) ^ (-2 : ℝ))
    ((Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_left 2) (fun p => ?_)
  rw [Real.norm_eq_abs]
  exact abs_ccTerm_bound (le_of_lt hs) p

private lemma continuousAt_ccTerm (p : ℕ) :
    ContinuousAt (fun s : ℝ => ccTerm s p) 1 := by
  by_cases hp : p.Prime
  · have hne : (p : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hp.pos)
    have hq : ContinuousAt (fun s : ℝ => (p : ℝ) ^ (-s)) 1 :=
      (Real.continuousAt_const_rpow hne).comp (continuous_neg.continuousAt)
    have h1 : ContinuousAt (fun s : ℝ => 1 - (p : ℝ) ^ (-s)) 1 :=
      continuousAt_const.sub hq
    have hne1 : 1 - (p : ℝ) ^ (-1 : ℝ) ≠ 0 := by
      have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
      have hlt : (p : ℝ) ^ (-1 : ℝ) < 1 := by
        rw [Real.rpow_neg_one]; exact inv_lt_one_of_one_lt₀ hp1
      exact ne_of_gt (by linarith)
    have hlog : ContinuousAt (fun s : ℝ => Real.log (1 - (p : ℝ) ^ (-s))) 1 :=
      h1.log hne1
    have hcc : ContinuousAt
        (fun s : ℝ => -Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s)) 1 :=
      hlog.neg.sub hq
    have hfun : (fun s : ℝ => ccTerm s p)
        = fun s => c4 p * (-Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s)) := by
      funext s; rw [ccTerm, if_pos hp, gfun, if_pos hp]
    rw [hfun]
    exact continuousAt_const.mul hcc
  · have hfun : (fun s : ℝ => ccTerm s p) = fun _ => 0 := by
      funext s; rw [ccTerm, if_neg hp, gfun, if_neg hp]; ring
    rw [hfun]; exact continuousAt_const

private lemma tendsto_ccTerm :
    Tendsto (fun s : ℝ => ∑' p : ℕ, ccTerm s p) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (∑' p : ℕ, ccTerm 1 p)) := by
  refine tendsto_tsum_of_dominated_convergence (f := fun s p => ccTerm s p)
    (g := fun p => ccTerm 1 p) (bound := fun p : ℕ => 2 * (p : ℝ) ^ (-2 : ℝ)) ?_ ?_ ?_
  · exact (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_left 2
  · intro p
    exact (continuousAt_ccTerm p).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs p
    simpa only [Real.norm_eq_abs] using abs_ccTerm_bound (le_of_lt hs) p

private lemma pTerm_add_ccTerm (s : ℝ) (p : ℕ) :
    pTerm s p + ccTerm s p = c4 p * gfun s p := by
  by_cases hp : p.Prime
  · simp only [pTerm, ccTerm, if_pos hp]; ring
  · simp only [pTerm, ccTerm, if_neg hp]; ring

private lemma chiG_eq (s : ℝ) (hs : 1 < s) :
    chiG s = (∑' p : ℕ, pTerm s p) + ∑' p : ℕ, ccTerm s p := by
  rw [chiG]
  rw [← (summable_pTerm s hs).tsum_add (summable_ccTerm s hs)]
  exact tsum_congr fun p => (pTerm_add_ccTerm s p).symm

private lemma two_G_sub_W (s : ℝ) (hs : 1 < s) :
    2 * G s - W s = chiG s + gfun s 2 := by
  have hG := summable_Gterm s hs
  have hW := summable_gfun s hs
  have hchi := summable_chiG s hs
  have h2 : Summable (fun p : ℕ => (if p = 2 then 1 else 0) * gfun s p) :=
    summable_of_ne_finset_zero (s := {2}) (fun b hb => by
      rw [Finset.mem_singleton] at hb
      rw [if_neg hb, zero_mul])
  have hptw : (fun p : ℕ => (2 * aa p - 1) * gfun s p)
      = fun p : ℕ => (c4 p + (if p = 2 then 1 else 0)) * gfun s p := by
    funext p
    by_cases hp : p.Prime
    · rw [two_aa_sub_one p hp]
    · rw [gfun, if_neg hp, mul_zero, mul_zero]
  have hfac : (fun p : ℕ => (c4 p + (if p = 2 then 1 else 0)) * gfun s p)
      = fun p : ℕ => c4 p * gfun s p + (if p = 2 then 1 else 0) * gfun s p := by
    funext p; rw [add_mul]
  have hsum : (∑' p : ℕ, (2 * aa p - 1) * gfun s p)
      = (∑' p : ℕ, c4 p * gfun s p)
        + ∑' p : ℕ, (if p = 2 then 1 else 0) * gfun s p := by
    rw [hptw, hfac, hchi.tsum_add h2]
  have hsingle : (∑' p : ℕ, (if p = 2 then 1 else 0) * gfun s p) = gfun s 2 := by
    rw [tsum_eq_single 2]
    · simp
    · intro b hb; rw [if_neg hb, zero_mul]
  have hK : (∑' p : ℕ, (2 * aa p - 1) * gfun s p) = chiG s + gfun s 2 := by
    rw [hsum, hsingle, chiG]
  have hL : 2 * G s - W s = ∑' p : ℕ, (2 * aa p - 1) * gfun s p := by
    rw [G, W]
    have e1 : (2 : ℝ) * (∑' p : ℕ, Gterm s p) = ∑' p : ℕ, (2 : ℝ) * Gterm s p :=
      (tsum_mul_left (f := fun p : ℕ => Gterm s p) (a := (2 : ℝ))).symm
    rw [e1, ← (hG.mul_left 2).tsum_sub hW]
    refine tsum_congr fun p => ?_
    rw [Gterm]; ring
  rw [hL, hK]

private lemma tendsto_gfun_two :
    Tendsto (fun s : ℝ => gfun s 2) (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log 2)) := by
  have hq : Tendsto (fun s : ℝ => (2 : ℝ) ^ (-s)) (nhdsWithin 1 (Set.Ioi 1))
      (nhds ((2 : ℝ) ^ (-1 : ℝ))) := by
    have hneg : Tendsto (fun s : ℝ => -s) (nhdsWithin 1 (Set.Ioi 1)) (nhds (-1 : ℝ)) :=
      (continuous_neg.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    exact (Real.continuousAt_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp hneg
  have h1 : Tendsto (fun s : ℝ => 1 - (2 : ℝ) ^ (-s)) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (1 - (2 : ℝ) ^ (-1 : ℝ))) := tendsto_const_nhds.sub hq
  have hne : 1 - (2 : ℝ) ^ (-1 : ℝ) ≠ 0 := by rw [Real.rpow_neg_one]; norm_num
  have hlog : Tendsto (fun s : ℝ => Real.log (1 - (2 : ℝ) ^ (-s))) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (Real.log (1 - (2 : ℝ) ^ (-1 : ℝ)))) :=
    (Real.continuousAt_log hne).tendsto.comp h1
  have hres : Tendsto (fun s : ℝ => -Real.log (1 - (2 : ℝ) ^ (-s))) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (-Real.log (1 - (2 : ℝ) ^ (-1 : ℝ)))) := hlog.neg
  have hval : -Real.log (1 - (2 : ℝ) ^ (-1 : ℝ)) = Real.log 2 := by
    rw [Real.rpow_neg_one, show (1 : ℝ) - 2⁻¹ = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]; ring
  rw [hval] at hres
  refine hres.congr fun s => ?_
  rw [gfun, if_pos (by norm_num : Nat.Prime 2), Nat.cast_ofNat]

/-! ## Final assembly -/

private lemma main_term (s : ℝ) (hs : 1 < s) :
    Real.sqrt (s - 1) *
      (∑' n : ℕ, (Set.indicator {n : ℕ | ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ n}
        (fun _ => (1 : ℝ)) n) * (n : ℝ) ^ (-s))
      = Real.exp (G s + (1 / 2) * Real.log (s - 1)) := by
  have hsame : (fun n : ℕ => (Set.indicator {n : ℕ | ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ n}
        (fun _ => (1 : ℝ)) n) * (n : ℝ) ^ (-s)) = fun n => fser s n := by
    funext n; rfl
  rw [hsame, series_eq_exp_G s hs, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos (by linarith : (0 : ℝ) < s - 1), ← Real.exp_add]
  congr 1; ring

theorem three_mod_four_lseries_half :
    ∃ c : ℝ, 0 < c ∧ Filter.Tendsto
      (fun s : ℝ => Real.sqrt (s - 1) *
        tsum (fun n : ℕ => (Set.indicator {n : ℕ | ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ n} (fun _ => (1 : ℝ)) n) * (n : ℝ) ^ (-s)))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds c) := by
  obtain ⟨Lp, hLp⟩ := abel_pTerm
  set Lcc : ℝ := ∑' p : ℕ, ccTerm 1 p with hLcc
  set V : ℝ := (Lp + Lcc + Real.log 2) / 2 with hV
  refine ⟨Real.exp V, Real.exp_pos V, ?_⟩
  have hchi : Tendsto (fun s : ℝ => chiG s) (nhdsWithin 1 (Set.Ioi 1)) (nhds (Lp + Lcc)) := by
    have hsum := hLp.add tendsto_ccTerm
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (chiG_eq s hs).symm
  have hcomb : Tendsto
      (fun s : ℝ => (1 / 2) * (W s + Real.log (s - 1)) + (1 / 2) * chiG s + (1 / 2) * gfun s 2)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds V) := by
    have h := ((tendsto_W.const_mul (1 / 2 : ℝ)).add (hchi.const_mul (1 / 2 : ℝ))).add
      (tendsto_gfun_two.const_mul (1 / 2 : ℝ))
    have hV' : (1 / 2 : ℝ) * 0 + (1 / 2) * (Lp + Lcc) + (1 / 2) * Real.log 2 = V := by
      rw [hV]; ring
    rwa [hV'] at h
  have hΦ : Tendsto (fun s : ℝ => G s + (1 / 2) * Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds V) := by
    refine hcomb.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have h2 := two_G_sub_W s hs
    have hh : G s + (1 / 2) * Real.log (s - 1)
        = (1 / 2) * (W s + Real.log (s - 1)) + (1 / 2) * chiG s + (1 / 2) * gfun s 2 := by
      linarith [h2]
    exact hh.symm
  have hexp : Tendsto (fun s : ℝ => Real.exp (G s + (1 / 2) * Real.log (s - 1)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.exp V)) :=
    Real.continuous_exp.tendsto V |>.comp hΦ
  refine hexp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (main_term s hs).symm

end

end Commons.NumberTheory.Diophantine
