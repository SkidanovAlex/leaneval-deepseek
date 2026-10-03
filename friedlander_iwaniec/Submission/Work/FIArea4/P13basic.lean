import Mathlib
import Submission.Work.FIArea4.P13Defs
import Submission.Work.FIArea4.P13_prime_window_sum

/-!
# Elementary pieces of FI §13

* `P13_sum_L2p`: the `L²`-masses `L2p R S p α` summed over a set of primes is at most the number of
  primes dividing a fixed `r ≤ 2R` (at most `K`) times the full `L²`-norm.
* `P13_fiber_sum`: a general "at most `M`-to-one" summation bound.
* `P13_prime_count`: the number of primes in a dyadic window is `≫ n / log n`.
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Summing the `p ∣ r` masses over a set `W` of primes is controlled by the largest number of
elements of `W` dividing a fixed `r ≤ 2R`. -/
theorem P13_sum_L2p (R S : ℕ) (α : ℕ → ℕ → ℂ) (W : Finset ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hK2 : ∀ r : ℕ, 1 ≤ r → r ≤ 2 * R → ((W.filter (fun p => p ∣ r)).card : ℝ) ≤ K) :
    ∑ p ∈ W, L2p R S p α ≤ K * p14L2 R S α := by
  have hswap : ∑ p ∈ W, L2p R S p α
      = ∑ r ∈ Finset.Icc 1 (2 * R),
          ∑ p ∈ W.filter (fun p => p ∣ r),
            ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s) := by
    simp only [L2p, Finset.sum_filter]
    rw [Finset.sum_comm]
  have hstep : ∀ r ∈ Finset.Icc 1 (2 * R),
      ∑ p ∈ W.filter (fun p => p ∣ r), ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s)
        ≤ K * ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hc := hK2 r hr.1 hr.2
    have hinner : (0:ℝ) ≤ ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s) :=
      Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _)
    calc ∑ _p ∈ W.filter (fun p => p ∣ r), ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s)
        = (((W.filter (fun p => p ∣ r)).card : ℕ) : ℝ) *
            ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ K * ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s) :=
          mul_le_mul_of_nonneg_right hc hinner
  calc ∑ p ∈ W, L2p R S p α
      = ∑ r ∈ Finset.Icc 1 (2 * R),
          ∑ p ∈ W.filter (fun p => p ∣ r),
            ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s) := hswap
    _ ≤ ∑ r ∈ Finset.Icc 1 (2 * R), K * ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s) :=
        Finset.sum_le_sum hstep
    _ = K * p14L2 R S α := by
        rw [p14L2, Finset.mul_sum]

/-- A general "at most `M`-to-one" summation bound: if every value of `g` is hit at most `M` times
on `s` and `f ≥ 0` on `t ⊇ g '' s`, then `Σ_{i∈s} f (g i) ≤ M Σ_{j∈t} f j`. -/
theorem P13_fiber_sum {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ) (g : ι → κ)
    (f : κ → ℝ) (hmap : ∀ i ∈ s, g i ∈ t) (M : ℝ)
    (hcard : ∀ j ∈ t, ((s.filter (fun i => g i = j)).card : ℝ) ≤ M)
    (hf : ∀ j ∈ t, 0 ≤ f j) :
    ∑ i ∈ s, f (g i) ≤ M * ∑ j ∈ t, f j := by
  have hfib := Finset.sum_fiberwise_of_maps_to hmap (fun i => f (g i))
  rw [← hfib]
  have h1 : ∀ j ∈ t, ∑ i ∈ s.filter (fun i => g i = j), f (g i)
      = ((s.filter (fun i => g i = j)).card : ℕ) • f j := by
    intro j hj
    rw [Finset.sum_congr rfl (g := fun _ => f j) (fun i hi => ?_), Finset.sum_const]
    simp only [Finset.mem_filter] at hi
    rw [hi.2]
  calc ∑ j ∈ t, ∑ i ∈ s.filter (fun i => g i = j), f (g i)
      = ∑ j ∈ t, ((s.filter (fun i => g i = j)).card : ℕ) • f j := Finset.sum_congr rfl h1
    _ = ∑ j ∈ t, (((s.filter (fun i => g i = j)).card : ℕ) : ℝ) * f j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [nsmul_eq_mul]
    _ ≤ ∑ j ∈ t, M * f j := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        exact mul_le_mul_of_nonneg_right (hcard j hj) (hf j hj)
    _ = M * ∑ j ∈ t, f j := by rw [Finset.mul_sum]

/-- There are `≫ n / log n` primes in the dyadic window `(n, 2n]`.  (Immediate from the Mertens-type
lower bound `Σ_{n<p≤2n} (log p)/p ≫ 1` and `log p / p ≤ log(2n)/n` for `p ≤ 2n`.) -/
theorem P13_prime_count : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
    c * (n : ℝ) / Real.log (2 * (n : ℝ)) ≤ (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ) := by
  obtain ⟨c, hc0, hc⟩ := P13_prime_window_sum
  refine ⟨c, hc0, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hLpos : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos (by linarith)
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hterm : ∀ p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime,
      Real.log (p : ℝ) / (p : ℝ) ≤ Real.log (2 * (n : ℝ)) / (n : ℝ) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hnp, hp2n⟩, hpprime⟩ := hp
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.pos
    have hnple : (n : ℝ) < (p : ℝ) := by exact_mod_cast hnp
    have hple : (p : ℝ) ≤ 2 * (n : ℝ) := by
      have : p ≤ 2 * n := by omega
      exact_mod_cast this
    have hlogp : Real.log (p : ℝ) ≤ Real.log (2 * (n : ℝ)) := Real.log_le_log hppos hple
    have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.one_le
      linarith)
    rw [div_le_div_iff₀ hppos hnpos]
    nlinarith [hlogp, hnple, hlog0]
  have hcard := hc n hn1
  have hle : ∑ p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)
      ≤ (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ)
          * (Real.log (2 * (n : ℝ)) / (n : ℝ)) := by
    calc ∑ p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)
        ≤ ∑ _p ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime,
            Real.log (2 * (n : ℝ)) / (n : ℝ) := Finset.sum_le_sum hterm
      _ = (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ)
            * (Real.log (2 * (n : ℝ)) / (n : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : c ≤ (((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℝ)
      * (Real.log (2 * (n : ℝ)) / (n : ℝ)) := le_trans hcard hle
  rw [div_le_iff₀ hLpos]
  have h := mul_le_mul_of_nonneg_right h2 hnpos.le
  have hsimp : ((((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℕ) : ℝ)
      * (Real.log (2 * (n : ℝ)) / (n : ℝ)) * (n : ℝ)
      = ((((Finset.Ioc n (2 * n)).filter Nat.Prime).card : ℕ) : ℝ)
        * Real.log (2 * (n : ℝ)) := by
    field_simp
  linarith [h, hsimp]

/-- The number of primes `p ∈ W` with `p² ∣ e` is at most `log e / log 4` (each such prime
contributes at least `2` to the exponent sum, so `4 ^ # ≤ ∏ p² ≤ e`). -/
lemma p13_prime_sq_card_le (W : Finset ℕ) (e : ℕ) (he : 1 ≤ e)
    (hprime : ∀ p ∈ W, Nat.Prime p) :
    (((W.filter (fun p => p ^ 2 ∣ e)).card : ℕ) : ℝ) ≤ Real.log e / Real.log 4 := by
  set S := W.filter (fun p => p ^ 2 ∣ e) with hS
  have hdvd : (∏ p ∈ S, p ^ 2) ∣ e := by
    have hmain : ∀ t, t ⊆ S → (∏ p ∈ t, p ^ 2) ∣ e := by
      intro t
      induction t using Finset.induction_on with
      | empty => intro _; simp
      | insert p t hpt ih =>
          intro ht
          rw [Finset.prod_insert hpt]
          have hpS : p ∈ S := ht (Finset.mem_insert_self p t)
          have htS : t ⊆ S := fun q hq => ht (Finset.mem_insert_of_mem hq)
          have hp' : Nat.Prime p := hprime p (Finset.mem_filter.mp hpS).1
          have hcop : Nat.Coprime (p ^ 2) (∏ q ∈ t, q ^ 2) := by
            apply Nat.Coprime.prod_right
            intro q hq
            have hqS : q ∈ S := htS hq
            have hpq : p ≠ q := fun h => hpt (h ▸ hq)
            have hq' : Nat.Prime q := hprime q (Finset.mem_filter.mp hqS).1
            exact ((Nat.coprime_primes hp' hq').mpr hpq).pow 2 2
          exact hcop.mul_dvd_of_dvd_of_dvd (Finset.mem_filter.mp hpS).2 (ih htS)
    exact hmain S (fun _ h => h)
  have h4 : (4 : ℕ) ^ S.card ≤ ∏ p ∈ S, p ^ 2 := by
    refine Finset.pow_card_le_prod S (fun p => p ^ 2) 4 ?_
    intro p hp
    have hp' : Nat.Prime p := hprime p (Finset.mem_filter.mp hp).1
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp'.two_le 2
  have hprod : (∏ p ∈ S, p ^ 2) ≤ e := Nat.le_of_dvd (by omega) hdvd
  have hlog : ((S.card : ℕ) : ℝ) * Real.log 4 ≤ Real.log (e : ℝ) := by
    have h1 : (((4 : ℕ) ^ S.card : ℕ) : ℝ) ≤ (e : ℝ) := by exact_mod_cast le_trans h4 hprod
    have h2 : Real.log ((((4 : ℕ) ^ S.card : ℕ)) : ℝ) ≤ Real.log (e : ℝ) :=
      Real.log_le_log (by positivity) h1
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h2
    simpa using h2
  rw [le_div_iff₀ (Real.log_pos (by norm_num))]
  linarith

/-- The multiplicity of a modulus `e = d p²` (`p` prime, `d ∈ D`) is at most `log e / log 4 + 1`:
the fibre of `(p,d) ↦ d p²` over `e` injects into the set of primes `p` with `p² ∣ e`. -/
lemma p13_fiber_card_le (D W : Finset ℕ) (e : ℕ) (he : 1 ≤ e)
    (hprime : ∀ p ∈ W, Nat.Prime p) :
    (((W ×ˢ D).filter (fun x : ℕ × ℕ => x.1 ^ 2 * x.2 = e)).card : ℝ)
      ≤ Real.log e / Real.log 4 + 1 := by
  set s := (W ×ˢ D).filter (fun x : ℕ × ℕ => x.1 ^ 2 * x.2 = e) with hs
  have himg : s.image Prod.fst ⊆ W.filter (fun p => p ^ 2 ∣ e) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨x, hx, rfl⟩
    rw [hs] at hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
    exact Finset.mem_filter.mpr ⟨hx1, ⟨x.2, (Finset.mem_filter.mp hx).2.symm⟩⟩
  have hinj : ∀ x ∈ s, ∀ y ∈ s, Prod.fst x = Prod.fst y → x = y := by
    intro x hx y hy hxy
    rw [hs] at hx hy
    have hx2 : x.1 ^ 2 * x.2 = e := (Finset.mem_filter.mp hx).2
    have hy2 : y.1 ^ 2 * y.2 = e := (Finset.mem_filter.mp hy).2
    have hxW : x.1 ∈ W := (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
    have h2 : x.2 = y.2 := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < x.1 ^ 2 by
        have := (hprime x.1 hxW).pos
        positivity)
      rw [hx2, hxy, ← hy2]
    exact Prod.ext hxy h2
  have hcard : s.card ≤ (W.filter (fun p => p ^ 2 ∣ e)).card := by
    calc s.card = (s.image Prod.fst).card :=
          (Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)).symm
      _ ≤ _ := Finset.card_le_card himg
  have h2 := p13_prime_sq_card_le W e he hprime
  have h3 : (((W.filter (fun p => p ^ 2 ∣ e)).card : ℕ) : ℝ) ≤ Real.log e / Real.log 4 := h2
  calc (((W ×ˢ D).filter (fun x : ℕ × ℕ => x.1 ^ 2 * x.2 = e)).card : ℝ)
      = (s.card : ℝ) := by rw [hs]
    _ ≤ (((W.filter (fun p => p ^ 2 ∣ e)).card : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ Real.log e / Real.log 4 := h3
    _ ≤ Real.log e / Real.log 4 + 1 := by linarith

/-- **The summation bound for the enlarged moduli** `d p²` (FI §13, (13.4)): since the moduli
`d p²` (`p` prime in `W`, `d ∈ (D,2D]`) lie in the window `(e₁, e₂]` and each value is hit at most
`log e₂/log 4 + 2` times (a prime `p` with `p² ∣ e` contributes `2` to the exponent of `e`), the
sum over the enlarged moduli is dominated by the corresponding window of `Evar`. -/
theorem p13_enlarged_sum_le (D R S : ℕ) (W : Finset ℕ) (α : ℕ → ℕ → ℂ) (e₁ e₂ : ℕ)
    (he₁ : 1 ≤ e₁)
    (hprime : ∀ p ∈ W, Nat.Prime p)
    (hlo : ∀ p ∈ W, ∀ d ∈ Finset.Ioc D (2 * D), e₁ < d * p ^ 2)
    (hhi : ∀ p ∈ W, ∀ d ∈ Finset.Ioc D (2 * D), d * p ^ 2 ≤ e₂) :
    ∑ p ∈ W, ∑ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S (d * p ^ 2) α
      ≤ (Real.log (e₂ : ℝ) / Real.log 4 + 2)
          * ∑ e ∈ Finset.Ioc e₁ e₂, Work.FIPlan.Evar R S e α := by
  have h1 : ∑ p ∈ W, ∑ d ∈ Finset.Ioc D (2 * D), Work.FIPlan.Evar R S (d * p ^ 2) α
      = ∑ x ∈ W ×ˢ (Finset.Ioc D (2 * D)), Work.FIPlan.Evar R S (x.1 ^ 2 * x.2) α := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun d _ => ?_))
    rw [Nat.mul_comm]
  rw [h1]
  refine le_trans (P13_fiber_sum (W ×ˢ (Finset.Ioc D (2 * D))) (Finset.Ioc e₁ e₂)
    (fun x : ℕ × ℕ => x.1 ^ 2 * x.2) (fun e => Work.FIPlan.Evar R S e α) ?_
    (Real.log (e₂ : ℝ) / Real.log 4 + 2) ?_ ?_) ?_
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
    rw [Finset.mem_Ioc]
    refine ⟨?_, ?_⟩
    · rw [Nat.mul_comm]; exact hlo x.1 hx1 x.2 hx2
    · rw [Nat.mul_comm]; exact hhi x.1 hx1 x.2 hx2
  · intro j hj
    rw [Finset.mem_Ioc] at hj
    obtain ⟨hj1, hj2⟩ := hj
    have he : 1 ≤ j := by omega
    have h := p13_fiber_card_le (Finset.Ioc D (2 * D)) W j he hprime
    have hlog : Real.log (j : ℝ) ≤ Real.log (e₂ : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast (by omega : 0 < j)
      · exact_mod_cast hj2
    have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have : Real.log (j : ℝ) / Real.log 4 + 1
        ≤ Real.log (e₂ : ℝ) / Real.log 4 + 2 := by
      have := div_le_div_of_nonneg_right hlog (le_of_lt hlog4)
      linarith
    linarith [h, this]
  · intro e _
    rw [Work.FIPlan.Evar]
    exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)
  · have hsum : (0:ℝ) ≤ ∑ e ∈ Finset.Ioc e₁ e₂, Work.FIPlan.Evar R S e α :=
      Finset.sum_nonneg (fun e _ => by
        rw [Work.FIPlan.Evar]
        exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _))
    exact le_of_eq rfl

end

end Work.FIArea4
