import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular

open scoped BigOperators Topology
open Filter

namespace Commons.NumberTheory.Mertens

lemma rpowDiff_nonneg {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ (k : ℝ) ^ (-ε) - (((k + 1 : ℕ) : ℝ) ^ (-ε)) := by
  have ha0 : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hb0 : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hab : (k : ℝ) ≤ (((k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.le_succ k)
  have hle : (k : ℝ) ^ ε ≤ (((k + 1 : ℕ) : ℝ)) ^ ε :=
    Real.rpow_le_rpow (le_of_lt ha0) hab (le_of_lt hε)
  have hpa : 0 < (k : ℝ) ^ ε := Real.rpow_pos_of_pos ha0 ε
  have hpb : 0 < (((k + 1 : ℕ) : ℝ)) ^ ε := Real.rpow_pos_of_pos hb0 ε
  have hrec : ((((k + 1 : ℕ) : ℝ)) ^ ε)⁻¹ ≤ ((k : ℝ) ^ ε)⁻¹ := (inv_le_inv₀ hpb hpa).2 hle
  have hneg1 : (k : ℝ) ^ (-ε) = ((k : ℝ) ^ ε)⁻¹ := Real.rpow_neg (le_of_lt ha0) ε
  have hneg2 : (((k + 1 : ℕ) : ℝ)) ^ (-ε) = ((((k + 1 : ℕ) : ℝ)) ^ ε)⁻¹ :=
    Real.rpow_neg (le_of_lt hb0) ε
  rw [hneg1, hneg2]
  exact sub_nonneg.mpr hrec

lemma hasSum_of_differences {a : ℕ → ℝ} (ha0 : ∀ k, 0 ≤ a k)
    {n : ℕ} (hdec : ∀ k, n ≤ k → a (k + 1) ≤ a k)
    (ht : Tendsto a atTop (nhds 0)) :
    HasSum (fun k : ℕ => if n ≤ k then a k - a (k + 1) else 0) (a n) := by
  let e : ℕ → ℝ := fun k => if n ≤ k then a k - a (k + 1) else 0
  have e_nonneg (k : ℕ) : 0 ≤ e k := by
    dsimp [e]
    by_cases hk : n ≤ k
    · have hh : a (k + 1) ≤ a k := hdec k hk
      simp [hk, sub_nonneg.mpr hh]
    · simp [hk]
  let P : ℕ → ℝ := fun m => ∑ i ∈ Finset.range m, e i
  have P_eq (m : ℕ) (hmn : n ≤ m) : P m = a n - a m := by
    dsimp [P]
    calc
      ∑ i ∈ Finset.range m, e i
          = ∑ i ∈ Finset.range m, (if n ≤ i then a i - a (i + 1) else 0) := by rfl
      _ = ∑ i ∈ Finset.range m with n ≤ i, (a i - a (i + 1)) := by
              rw [← Finset.sum_filter]
      _ = ∑ i ∈ Finset.Ico n m, (a i - a (i + 1)) := by
              congr 1
              ext i
              simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
              tauto
      _ = a n - a m := by
              calc
                (∑ i ∈ Finset.Ico n m, (a i - a (i + 1)))
                    = ∑ i ∈ Finset.Ico n m, (-(a (i + 1)) - (-(a i))) := by
                        apply Finset.sum_congr rfl; intro i hi; ring
                _ = -(a m) - (-(a n)) := Finset.sum_Ico_sub (f := fun j : ℕ => - a j) hmn
                _ = a n - a m := by ring
  have P_le (m : ℕ) : P m ≤ a n := by
    by_cases hmn : m ≤ n
    · dsimp [P]
      have hz : ∀ i ∈ Finset.range m, e i = 0 := by
        intro i hi
        have hi_lt : i < m := Finset.mem_range.mp hi
        have hin : ¬ n ≤ i := by omega
        dsimp [e]; simp [hin]
      rw [Finset.sum_eq_zero hz]
      exact ha0 n
    · have hnm : n ≤ m := le_of_not_ge hmn
      rw [P_eq m hnm]
      exact sub_le_self (a n) (ha0 m)
  have hsummable : Summable e :=
    summable_of_sum_range_le (f := e) (c := a n) (fun k => e_nonneg k) (fun m => P_le m)
  have hP_tsum : Tendsto P atTop (nhds (∑' k, e k)) := by
    simpa [P] using hsummable.tendsto_sum_tsum_nat
  have hP_lim : Tendsto P atTop (nhds (a n)) := by
    have h1 : Tendsto (fun m : ℕ => a n - a m) atTop (nhds (a n)) := by
      simpa using (tendsto_const_nhds.sub ht : Tendsto (fun m : ℕ => a n - a m) atTop (nhds (a n - 0)))
    have hcong' : P =ᶠ[atTop] (fun m : ℕ => a n - a m) := by
      filter_upwards [eventually_ge_atTop n] with m hm
      rw [P_eq m hm]
    exact Filter.Tendsto.congr' hcong'.symm h1
  have hEq : (∑' k, e k) = a n := tendsto_nhds_unique hP_tsum hP_lim
  simpa [e, hEq] using hsummable.hasSum

lemma rpow_inv_mul_neg {x : ℝ} (hx : 0 < x) (ε : ℝ) :
    x ^ (-(1 + ε)) = (1 / x) * x ^ (-ε) := by
  calc
    x ^ (-(1 + ε)) = x ^ ((-1 : ℝ) + (-ε)) := by congr 1; ring
    _ = x ^ (-1) * x ^ (-ε) := Real.rpow_add hx (-1) (-ε)
    _ = x⁻¹ * x ^ (-ε) := by rw [Real.rpow_neg_one]
    _ = (1 / x) * x ^ (-ε) := by simp

lemma hasSum_primes_rpow_tail {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 2 ≤ n) :
    HasSum (fun k : ℕ => if n ≤ k then (1 : ℝ) / (n : ℝ) *
        (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0)
      ((n : ℝ) ^ (-(1 + ε))) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hc0 : 0 ≤ (1 : ℝ) / (n : ℝ) := by positivity
  let a : ℕ → ℝ := fun k => (1 : ℝ) / (n : ℝ) * (k : ℝ) ^ (-ε)
  have ha0 (k : ℕ) : 0 ≤ a k := by
    dsimp [a]
    exact mul_nonneg hc0 (Real.rpow_nonneg (by positivity : 0 ≤ (k : ℝ)) (-ε))
  have hdec (k : ℕ) (hk : n ≤ k) : a (k + 1) ≤ a k := by
    have hk1 : 1 ≤ k := by omega
    have hd := rpowDiff_nonneg hε hk1
    have hsub : (((k + 1 : ℕ) : ℝ)) ^ (-ε) ≤ (k : ℝ) ^ (-ε) := sub_nonneg.mp hd
    dsimp [a]
    exact mul_le_mul_of_nonneg_left hsub hc0
  have hs : Tendsto (fun k : ℕ => (k : ℝ) ^ (-ε)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop
  have ht : Tendsto a atTop (nhds 0) := by
    simpa [a] using (hs.const_mul ((1 : ℝ) / (n : ℝ)))
  have hh := hasSum_of_differences (a := a) (ha0 := ha0) (n := n) (hdec := hdec) (ht := ht)
  have hmain : HasSum (fun k : ℕ => if n ≤ k then (1 : ℝ) / (n : ℝ) *
        (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0)
      ((1 : ℝ) / (n : ℝ) * (n : ℝ) ^ (-ε)) := by
    refine hh.congr_fun ?_
    intro k
    by_cases hk : n ≤ k
    · rw [if_pos hk, if_pos hk]
      dsimp [a]
      ring
    · simp [hk]
  rw [rpow_inv_mul_neg hnpos ε]
  exact hmain

lemma tsum_primes_rpow_tail {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 2 ≤ n) :
    (∑' k : ℕ, (if n ≤ k then (1 : ℝ) / (n : ℝ) *
        (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0)) =
      (n : ℝ) ^ (-(1 + ε)) :=
  (hasSum_primes_rpow_tail hε n hn).tsum_eq

lemma summable_primes_rpow {ε : ℝ} (hε : 0 < ε) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(1 + ε))) := by
  have h : Summable (fun m : ℕ => (m : ℝ) ^ (-(1 + ε))) := by
    rw [Real.summable_nat_rpow]
    linarith
  exact h.comp_injective (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective

lemma rpowDiff_tail_nonneg {ε : ℝ} (hε : 0 < ε) (p : Nat.Primes) (k : ℕ) :
    0 ≤ (if (p : ℕ) ≤ k then (1 : ℝ) / ((p : ℕ) : ℝ) *
        (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0) := by
  by_cases hpk : (p : ℕ) ≤ k
  · rw [if_pos hpk]
    have hk1 : 1 ≤ k := by
      have hp2 : 2 ≤ (p : ℕ) := Nat.Prime.two_le p.property
      omega
    have hd := rpowDiff_nonneg hε hk1
    have hp0 : 0 ≤ (1 : ℝ) / ((p : ℕ) : ℝ) := by positivity
    exact mul_nonneg hp0 hd
  · simp [hpk]

lemma tsum_primes_term {ε : ℝ} (k : ℕ) :
    (∑' p : Nat.Primes,
        (if (p : ℕ) ≤ k then
          (1 : ℝ) / ((p : ℕ) : ℝ) * (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε)))
         else 0)) =
    if 2 ≤ k then
      (∑ p ∈ k.primesLE, (1 : ℝ) / (p : ℝ)) *
        (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε)))
    else 0 := by
  let e : ℝ := ((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))
  by_cases hk : 2 ≤ k
  · rw [if_pos hk]
    let u : ℕ → ℝ := fun m => if m ∈ k.primesLE then (1 : ℝ) / (m : ℝ) * e else 0
    have hsub := tsum_subtype (s := {m : ℕ | Nat.Prime m}) u
    have hind : (fun m : ℕ => ({m : ℕ | Nat.Prime m}).indicator u m) = u := by
      funext m
      by_cases hm : Nat.Prime m
      · have hmem : m ∈ ({m : ℕ | Nat.Prime m} : Set ℕ) := hm
        simp [Set.indicator, hmem]
      · have hmem' : m ∉ ({m : ℕ | Nat.Prime m} : Set ℕ) := by simpa using hm
        simp [Set.indicator, hmem']
        dsimp [u]
        have hnp : ¬ m ∈ k.primesLE := by
          intro hmem2
          exact hm (Nat.mem_primesLE.mp hmem2).2
        simp [hnp]
    calc
      (∑' p : Nat.Primes,
          (if (p : ℕ) ≤ k then
            (1 : ℝ) / ((p : ℕ) : ℝ) * (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε)))
           else 0))
          = (∑' p : Nat.Primes, (if (p : ℕ) ≤ k then (1 : ℝ) / ((p : ℕ) : ℝ) * e else 0)) := by
              apply tsum_congr; intro p; rfl
      _ = ∑' x : {m : ℕ // Nat.Prime m}, u x.1 := by
              apply tsum_congr
              intro p
              dsimp [u]
              by_cases hp : (p : ℕ) ≤ k
              · rw [if_pos hp]
                have hmemb : (p : ℕ) ∈ k.primesLE := (Nat.mem_primesLE).2 ⟨hp, p.property⟩
                rw [if_pos hmemb]
              · rw [if_neg hp]
                have hmemb' : ¬ (p : ℕ) ∈ k.primesLE := by
                  intro hmemb
                  exact hp (Nat.mem_primesLE.mp hmemb).1
                rw [if_neg hmemb']
      _ = ∑' m : ℕ, u m := by
              exact hsub.trans (by simp [hind])
      _ = ∑ p ∈ k.primesLE, (1 : ℝ) / (p : ℝ) * e := by
              refine (tsum_eq_sum (f := u) (s := k.primesLE) ?_).trans ?_
              · intro m hm
                dsimp [u]
                simp [hm]
              · apply Finset.sum_congr rfl
                intro p hp
                dsimp [u]
                simp [hp]
      _ = (∑ p ∈ k.primesLE, (1 : ℝ) / (p : ℝ)) * e := by
              rw [Finset.sum_mul]
      _ = (∑ p ∈ k.primesLE, (1 : ℝ) / (p : ℝ)) *
          (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) := by
              simp [e]
  · rw [if_neg hk]
    have hnot : ∀ p : Nat.Primes, ¬ (p : ℕ) ≤ k := by
      intro p
      have h2p : 2 ≤ (p : ℕ) := Nat.Prime.two_le p.property
      omega
    calc
      (∑' p : Nat.Primes,
          (if (p : ℕ) ≤ k then
            (1 : ℝ) / ((p : ℕ) : ℝ) * (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε)))
           else 0))
          = (∑' p : Nat.Primes, (if (p : ℕ) ≤ k then (1 : ℝ) / ((p : ℕ) : ℝ) * e else 0)) := by
              apply tsum_congr; intro p; rfl
      _ = 0 := by
              have hz : (fun p : Nat.Primes => (if (p : ℕ) ≤ k then (1 : ℝ) / ((p : ℕ) : ℝ) * e else 0)) = fun _ => 0 := by
                funext p
                have hnp := hnot p
                simp [hnp]
              rw [hz]
              exact tsum_zero

theorem tsum_primes_eq_sum_rpowDiff {ε : ℝ} (hε : 0 < ε) :
    (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + ε))) =
    ∑' k : ℕ, if 2 ≤ k then
      (∑ p ∈ k.primesLE, (1 : ℝ) / (p : ℝ)) *
        (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε)))
    else 0 := by
  let g : Nat.Primes → ℕ → ℝ := fun p k => if (p : ℕ) ≤ k then
      (1 : ℝ) / ((p : ℕ) : ℝ) *
        (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0
  have hper (p : Nat.Primes) : (∑' k : ℕ, g p k) = ((p : ℕ) : ℝ) ^ (-(1 + ε)) := by
    simpa [g] using tsum_primes_rpow_tail hε (p : ℕ) (Nat.Prime.two_le p.property)
  have hg_summ : Summable (fun z : Nat.Primes × ℕ => g z.1 z.2) := by
    refine (summable_prod_of_nonneg (f := fun z : Nat.Primes × ℕ => g z.1 z.2) ?_).2 ?_
    · intro z
      exact rpowDiff_tail_nonneg hε z.1 z.2
    · constructor
      · intro p
        have hH : HasSum (fun k : ℕ => g p k) (((p : ℕ) : ℝ) ^ (-(1 + ε))) := by
          simpa [g] using hasSum_primes_rpow_tail hε (p : ℕ) (Nat.Prime.two_le p.property)
        exact hH.summable
      · have hcong' : (fun p : Nat.Primes => ∑' k : ℕ, g p k) =
            (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(1 + ε))) := by
            funext p
            exact hper p
        simpa [hcong'] using summable_primes_rpow hε
  calc
    (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + ε)))
        = (∑' p : Nat.Primes, ∑' k : ℕ, g p k) := by
            apply tsum_congr; intro p; exact (hper p).symm
    _ = (∑' k : ℕ, ∑' p : Nat.Primes, g p k) := by
            have hswap := Summable.tsum_comm (f := g) hg_summ
            exact hswap.symm
    _ = (∑' k : ℕ, if 2 ≤ k then
          (∑ p ∈ k.primesLE, (1 : ℝ) / (p : ℝ)) *
            (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε)))
        else 0) := by
            apply tsum_congr; intro k
            dsimp [g]
            exact tsum_primes_term (ε := ε) (k := k)

end Commons.NumberTheory.Mertens