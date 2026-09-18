import Mathlib
import Submission.DS.WindowSharp
import Submission.Commons.NumberTheory.Mertens.prod_one_sub_inv_range_lower_sharp
import Submission.Commons.NumberTheory.Mertens.primeProduct_oneSubInv_ge_invLog

open scoped BigOperators
open Finset

namespace SigmaSelfWin

noncomputable section

/-! # The σ-window sieve estimate

Target: for `N QR : ℕ`, `QR ≠ 0`, `S` a finite set of primes none of which divides `QR`,

  ∑_{c ≤ N, (c,QR)=1} ∏_{p ∈ S} (if p ∣ c then 1 else (p-2)/(p-1))
     ≤ K · N · ∏_{p | QR, p ≤ N} (1-1/p) · ∏_{p ∈ S}(1-1/p)

for an absolute constant `K`.  We prove it with `K = 4000`, which is more than enough for the
Duffin–Schaeffer application (any absolute constant works there).

Proof strategy (classical, "sieve + weighted average"):

* expand the σ-product over subsets `T ⊆ S`: `∏_{p∈S}σ_p(c) = ∑_T c_T·1_{D_T | c}`
  with `D_T = ∏_{p∈T}p` and `c_T = ∏_{p∈T}1/(p-1)·∏_{p∈S\T}(p-2)/(p-1)`;
* reindex `∑_{c ≤ N, (c,QR)=1, D_T | c}` as `#{m ≤ ⌊N/D_T⌋ : (m,QR)=1}` (as `D_T ⊥ QR`);
* bound each such count by the Selberg window bound `# ≤ 17·Y·∏_{p|QR,p≤Y}(1-1/p)`
  (`Submission.DS.window_density_le_17`);
* the weights `c_T/D_T` telescope: their total mass is `A := ∏_{p∈S}(1-1/p)` and the
  `p`-marginal mass is `A/(p-1)^2`, so the weighted average of the "window loss factor"
  `∏_{⌊N/D_T⌋<p≤N, p|QR}(1-1/p)^{-1}` is bounded by a constant using Mertens' theorem,
  the trivial bound `1/∏_{p≤N}(1-1/p) ≪ log N` and a Markov step on the logarithmic moment
  `∑_T (c_T/D_T)·log D_T = A·∑_{p∈S} log p/(p-1)^2 ≪ A`.
-/

/-! ## 1. σ-weights -/

/-- The `σ`-weight of the prime `p` at `c`. -/
def sig (p c : ℕ) : ℝ := if p ∣ c then 1 else ((p : ℝ) - 2) / ((p : ℝ) - 1)

lemma sig_nonneg {p c : ℕ} (hp : p.Prime) : 0 ≤ sig p c := by
  unfold sig
  split_ifs with h
  · norm_num
  · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    exact div_nonneg (by linarith) (by linarith)

lemma sig_le_one {p c : ℕ} (hp : p.Prime) : sig p c ≤ 1 := by
  unfold sig
  split_ifs with h
  · norm_num
  · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    rw [div_le_one (by linarith)]
    linarith

/-- Splitting the σ-weight into a constant part plus an indicator part. -/
lemma sig_eq_add {p c : ℕ} (hp : 2 ≤ p) :
    sig p c = ((p : ℝ) - 2) / ((p : ℝ) - 1) + (if p ∣ c then 1 / ((p : ℝ) - 1) else 0) := by
  unfold sig
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : ((p : ℝ) - 1) ≠ 0 := by linarith
  split_ifs with h
  · field_simp
    ring
  · ring

/-! ## 2. The subset expansion of the σ-product -/

/-- A product of pairwise coprime divisors of `c` divides `c`. -/
lemma prod_pairwise_coprime_dvd {T : Finset ℕ} {c : ℕ}
    (hcop : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → Nat.Coprime p q) (hdiv : ∀ p ∈ T, p ∣ c) :
    (∏ p ∈ T, p) ∣ c := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hdiv a (Finset.mem_insert_self a s)) ?_
      · rw [Nat.coprime_prod_right_iff]
        intro q hq
        exact hcop a (Finset.mem_insert_self a s) q (Finset.mem_insert_of_mem hq)
          (fun h => ha (h ▸ hq))
      · exact ih (fun p hp q hq hpq => hcop p (Finset.mem_insert_of_mem hp) q
            (Finset.mem_insert_of_mem hq) hpq)
          (fun p hp => hdiv p (Finset.mem_insert_of_mem hp))

/-- For a finset `T` of distinct primes and any `c`, the product of the indicator factors
`p ↦ if p ∣ c then 1/(p-1) else 0` equals `∏_{p∈T}(1/(p-1))` when `D_T ∣ c` and `0` otherwise. -/
lemma prod_indicator_dvd (T : Finset ℕ) (hT : ∀ p ∈ T, Nat.Prime p) (c : ℕ) :
    (∏ p ∈ T, (if p ∣ c then (1 : ℝ) / ((p : ℝ) - 1) else 0)) =
      (∏ p ∈ T, (1 : ℝ) / ((p : ℝ) - 1)) * (if (∏ p ∈ T, p) ∣ c then 1 else 0) := by
  classical
  have hcop : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → Nat.Coprime p q := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hT p hp) (hT q hq)).mpr hpq
  by_cases hall : ∀ p ∈ T, p ∣ c
  · have hD : (∏ p ∈ T, p) ∣ c := prod_pairwise_coprime_dvd hcop hall
    rw [if_pos hD, mul_one]
    refine Finset.prod_congr rfl ?_
    intro p hp
    rw [if_pos (hall p hp)]
  · push Not at hall
    obtain ⟨p, hp, hpnd⟩ := hall
    rw [if_neg (fun hD => hpnd (dvd_trans (Finset.dvd_prod_of_mem _ hp) hD))]
    rw [Finset.prod_eq_zero hp (if_neg hpnd)]
    ring


/-- **Subset expansion of the σ-product.**  For a finset `S` of primes and any `c`,
`∏_{p∈S} σ_p(c) = ∑_{T ⊆ S} (∏_{p∈T} 1/(p-1)) (∏_{p∈S\T} (p-2)/(p-1)) · 1_{D_T ∣ c}`. -/
lemma prod_sig_eq (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (c : ℕ) :
    (∏ p ∈ S, sig p c) =
      ∑ T ∈ S.powerset,
        (∏ p ∈ T, (1 : ℝ) / ((p : ℝ) - 1)) * (∏ p ∈ S \ T, ((p : ℝ) - 2) / ((p : ℝ) - 1)) *
          (if (∏ p ∈ T, p) ∣ c then 1 else 0) := by
  classical
  have hstep : ∀ T ∈ S.powerset,
      (∏ p ∈ T, (if p ∣ c then (1 : ℝ) / ((p : ℝ) - 1) else 0)) *
          (∏ p ∈ S \ T, ((p : ℝ) - 2) / ((p : ℝ) - 1)) =
        (∏ p ∈ T, (1 : ℝ) / ((p : ℝ) - 1)) * (∏ p ∈ S \ T, ((p : ℝ) - 2) / ((p : ℝ) - 1)) *
          (if (∏ p ∈ T, p) ∣ c then 1 else 0) := by
    intro T hT
    have hTp : ∀ p ∈ T, Nat.Prime p := fun p hp => hS p ((Finset.mem_powerset.mp hT) hp)
    rw [prod_indicator_dvd T hTp c]
    ring
  calc (∏ p ∈ S, sig p c)
      = ∏ p ∈ S, ((if p ∣ c then (1 : ℝ) / ((p : ℝ) - 1) else 0) + ((p : ℝ) - 2) / ((p : ℝ) - 1)) := by
        refine Finset.prod_congr rfl ?_
        intro p hp
        rw [sig_eq_add (hS p hp).two_le]
        ring_nf
    _ = ∑ T ∈ S.powerset,
          (∏ p ∈ T, (if p ∣ c then (1 : ℝ) / ((p : ℝ) - 1) else 0)) *
            (∏ p ∈ S \ T, ((p : ℝ) - 2) / ((p : ℝ) - 1)) :=
        Finset.prod_add _ _ S
    _ = ∑ T ∈ S.powerset,
          (∏ p ∈ T, (1 : ℝ) / ((p : ℝ) - 1)) * (∏ p ∈ S \ T, ((p : ℝ) - 2) / ((p : ℝ) - 1)) *
            (if (∏ p ∈ T, p) ∣ c then 1 else 0) :=
        Finset.sum_congr rfl hstep

/-! ## 3. Reindexing the divisibility condition -/

/-- For `D` coprime to `QR` and `D > 0`, the integers `c ≤ N` coprime to `QR` and divisible
by `D` are in bijection (via `c = D * m`) with the integers `m ≤ N / D` coprime to `QR`. -/
lemma card_filter_dvd_coprime (N D QR : ℕ) (hDgt : 0 < D) (hD : Nat.Coprime D QR) :
    (((Finset.Icc 1 N).filter (fun c : ℕ => c.gcd QR = 1 ∧ D ∣ c)).card)
      = (((Finset.Icc 1 (N / D)).filter (fun m : ℕ => m.gcd QR = 1)).card) := by
  classical
  refine Finset.card_bij (fun c _ => c / D) ?_ ?_ ?_
  · intro c hc
    rw [Finset.mem_filter, Finset.mem_Icc] at hc ⊢
    obtain ⟨⟨hc1, hcN⟩, hg, hdc⟩ := hc
    have hDle : D ≤ c := Nat.le_of_dvd (by omega) hdc
    refine ⟨⟨?_, Nat.div_le_div_right hcN⟩, ?_⟩
    · exact Nat.div_pos hDle hDgt
    · have hcD : D * (c / D) = c := Nat.mul_div_cancel' hdc
      have hcop : (D * (c / D)).Coprime QR := by rw [hcD]; exact Nat.coprime_iff_gcd_eq_one.mpr hg
      exact (Nat.coprime_mul_iff_left.mp hcop).2
  · intro c₁ h₁ c₂ h₂ heq
    rw [Finset.mem_filter] at h₁ h₂
    calc c₁ = D * (c₁ / D) := (Nat.mul_div_cancel' h₁.2.2).symm
      _ = D * (c₂ / D) := by rw [heq]
      _ = c₂ := Nat.mul_div_cancel' h₂.2.2
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hmN⟩, hmg⟩ := hm
    refine ⟨D * m, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.succ_le_of_lt (Nat.mul_pos hDgt (by omega)), ?_⟩, ?_, dvd_mul_right D m⟩
      · calc D * m ≤ D * (N / D) := Nat.mul_le_mul_left D hmN
          _ ≤ N := Nat.mul_div_le N D
      · rw [← Nat.coprime_iff_gcd_eq_one, Nat.coprime_mul_iff_left]
        exact ⟨hD, Nat.coprime_iff_gcd_eq_one.mpr hmg⟩
    · show D * m / D = m
      rw [Nat.mul_comm]
      exact Nat.mul_div_left m hDgt


/-! ## 4. The truncated Euler product and the Selberg window bound -/

/-- `∏_{p ∣ QR, p ≤ x} (1 - 1/p)`, as a function of the real truncation point `x`. -/
def eprod (QR : ℕ) (x : ℝ) : ℝ :=
  ∏ p ∈ (Nat.primeFactors QR).filter (fun p : ℕ => (p : ℝ) ≤ x), (1 - 1 / (p : ℝ))

lemma eprod_nonneg (QR : ℕ) (x : ℝ) : 0 ≤ eprod QR x := by
  rw [eprod]
  refine Finset.prod_nonneg (fun p hp => ?_)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
  have : (1 : ℝ) / (p : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  linarith

lemma eprod_pos (QR : ℕ) (x : ℝ) : 0 < eprod QR x := by
  rw [eprod]
  refine Finset.prod_pos (fun p hp => ?_)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
  have : (1 : ℝ) / (p : ℝ) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  linarith

/-- Each Euler factor `1 - 1/p` lies in `[0,1]`. -/
lemma one_sub_inv_mem (p : ℕ) (hp : p.Prime) : 0 ≤ 1 - 1 / (p : ℝ) ∧ 1 - 1 / (p : ℝ) ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hle : (1 : ℝ) / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  constructor <;> linarith [one_div_pos.mpr (by linarith : (0:ℝ) < (p:ℝ))]

lemma eprod_le_one (QR : ℕ) (x : ℝ) : eprod QR x ≤ 1 := by
  rw [eprod]
  refine Finset.prod_le_one₀ (fun p hp => (one_sub_inv_mem p
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).1)
    (fun p hp => (one_sub_inv_mem p
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).2)

lemma eprod_mono (QR : ℕ) {x y : ℝ} (h : x ≤ y) : eprod QR y ≤ eprod QR x := by
  rw [eprod, eprod]
  set s : Finset ℕ := (Nat.primeFactors QR).filter (fun p : ℕ => (p : ℝ) ≤ x) with hs
  set t : Finset ℕ := (Nat.primeFactors QR).filter (fun p : ℕ => (p : ℝ) ≤ y) with ht
  have hsub : s ⊆ t := by
    intro p hp
    rw [hs, Finset.mem_filter] at hp
    rw [ht, Finset.mem_filter]
    exact ⟨hp.1, le_trans hp.2 h⟩
  have h1 : (∏ p ∈ t \ s, (1 - 1 / (p : ℝ))) ≤ 1 := by
    refine Finset.prod_le_one₀ (fun p hp => ?_) (fun p hp => ?_)
    · exact (one_sub_inv_mem p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp
        ((Finset.mem_sdiff.mp hp).1)).1)).1
    · exact (one_sub_inv_mem p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp
        ((Finset.mem_sdiff.mp hp).1)).1)).2
  have h2 : (0 : ℝ) ≤ ∏ p ∈ s, (1 - 1 / (p : ℝ)) :=
    Finset.prod_nonneg (fun p hp => (one_sub_inv_mem p (Nat.prime_of_mem_primeFactors
      (Finset.mem_filter.mp (by rw [hs] at hp; exact hp)).1)).1)
  calc (∏ p ∈ t, (1 - 1 / (p : ℝ)))
      = (∏ p ∈ t \ s, (1 - 1 / (p : ℝ))) * (∏ p ∈ s, (1 - 1 / (p : ℝ))) :=
        (Finset.prod_sdiff hsub).symm
    _ ≤ 1 * (∏ p ∈ s, (1 - 1 / (p : ℝ))) := mul_le_mul_of_nonneg_right h1 h2
    _ = (∏ p ∈ s, (1 - 1 / (p : ℝ))) := one_mul _

lemma eprod_nat (QR Y : ℕ) :
    eprod QR (Y : ℝ) =
      ∏ p ∈ (Nat.primeFactors QR).filter (fun p : ℕ => p ≤ Y), (1 - 1 / (p : ℝ)) := by
  rw [eprod]
  refine Finset.prod_congr ?_ (fun p _ => rfl)
  refine Finset.filter_congr ?_
  intro p _
  exact Nat.cast_le

/-- A product of primes is squarefree. -/
lemma squarefree_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      have haP : Nat.Prime a := hs a (Finset.mem_insert_self a t)
      have htP : ∀ p ∈ t, Nat.Prime p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have hcop : Nat.Coprime a (∏ p ∈ t, p) := by
        refine Nat.Coprime.prod_right (fun p hp => ?_)
        exact (Nat.coprime_primes haP (htP p hp)).mpr (fun h => ha (h ▸ hp))
      rw [Finset.prod_insert ha, Nat.squarefree_mul hcop]
      refine ⟨?_, ih htP⟩
      rw [Nat.squarefree_iff_prime_squarefree]
      intro x hx hdvd
      have hxa : x = a := by
        rcases haP.eq_one_or_self_of_dvd x ((dvd_mul_right x x).trans hdvd) with h | h
        · exact absurd h hx.ne_one
        · exact h
      subst hxa
      have hle := Nat.le_of_dvd haP.pos hdvd
      nlinarith [haP.two_le]

/-- **Selberg window bound**, in the form needed here: for `QR ≠ 0`, the number of `m ≤ Y`
coprime to `QR` is at most `17 · Y · ∏_{p ∣ QR, p ≤ Y} (1 - 1/p)`. -/
lemma card_coprime_window_le (QR Y : ℕ) (hQR : QR ≠ 0) :
    ((((Finset.Icc 1 Y).filter (fun m : ℕ => m.gcd QR = 1)).card : ℕ) : ℝ) ≤
      17 * (Y : ℝ) * eprod QR (Y : ℝ) := by
  classical
  set s : Finset ℕ := (Nat.primeFactors QR).filter (fun p : ℕ => p ≤ Y) with hs
  set P : ℕ := ∏ p ∈ s, p with hP
  have hsP : ∀ p ∈ s, Nat.Prime p := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hsq : Squarefree P := by rw [hP]; exact squarefree_prod_primes s hsP
  have hpf : P.primeFactors = s := by rw [hP]; exact Nat.primeFactors_prod hsP
  have hle : ∀ p ∈ P.primeFactors, p ≤ Y := by
    rw [hpf]; intro p hp; exact (Finset.mem_filter.mp hp).2
  have hw := Submission.DS.window_density_le_17 P Y hsq hle
  have hset : (Finset.Icc 1 Y).filter (fun c : ℕ => c.Coprime P) =
      (Finset.Icc 1 Y).filter (fun c : ℕ => c.gcd QR = 1) := by
    refine Finset.filter_congr ?_
    intro c hc
    rw [Finset.mem_Icc] at hc
    obtain ⟨hc1, hcY⟩ := hc
    constructor
    · intro hcop
      have hcop' : c.gcd P = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
      by_contra hne
      obtain ⟨q, hqP, hqdvd⟩ := Nat.exists_prime_and_dvd hne
      have hqQRdvd : q ∣ QR := dvd_trans hqdvd (Nat.gcd_dvd_right c QR)
      have hqc : q ∣ c := dvd_trans hqdvd (Nat.gcd_dvd_left c QR)
      have hqQR : q ∈ Nat.primeFactors QR :=
        Nat.mem_primeFactors.mpr ⟨hqP, hqQRdvd, hQR⟩
      have hqY : q ≤ Y := le_trans (Nat.le_of_dvd (by omega) hqc) hcY
      have hqs : q ∈ s := by rw [hs]; exact Finset.mem_filter.mpr ⟨hqQR, hqY⟩
      have hqdvdP : q ∣ P := by rw [hP]; exact Finset.dvd_prod_of_mem _ hqs
      have : q ∣ c.gcd P := Nat.dvd_gcd hqc hqdvdP
      rw [hcop'] at this
      exact hqP.not_dvd_one this
    · intro hg
      rw [Nat.coprime_iff_gcd_eq_one]
      refine Nat.Coprime.prod_right (fun p hp => ?_)
      rw [Nat.coprime_comm]
      refine (Nat.Prime.coprime_iff_not_dvd (hsP p hp)).mpr ?_
      intro hpdvd
      have hpdvdQR : p ∣ QR := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).2.1
      have : p ∣ c.gcd QR := Nat.dvd_gcd hpdvd hpdvdQR
      rw [hg] at this
      exact (hsP p hp).not_dvd_one this
  rw [hset, hpf] at hw
  rw [eprod_nat]
  exact hw


/-! ## 5. The coefficient bookkeeping: the weights `wgt` telescope -/

/-- `D_T = ∏_{p∈T} p`. -/
def DT (T : Finset ℕ) : ℕ := ∏ p ∈ T, p

/-- The coefficient attached to `T ⊆ S` in the expansion of `∏_{p∈S} σ_p(c)`. -/
def coeffD (S T : Finset ℕ) : ℝ :=
  (∏ p ∈ T, (1 : ℝ) / ((p : ℝ) - 1)) * (∏ p ∈ S \ T, ((p : ℝ) - 2) / ((p : ℝ) - 1))

/-- The same coefficient divided by `D_T`.  These are the weights that telescope. -/
def wgt (S T : Finset ℕ) : ℝ :=
  (∏ p ∈ T, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) *
    (∏ p ∈ S \ T, ((p : ℝ) - 2) / ((p : ℝ) - 1))

lemma DT_pos (T : Finset ℕ) (hT : ∀ p ∈ T, 0 < p) : 0 < DT T := by
  rw [DT]
  exact Finset.prod_pos (fun p hp => hT p hp)

lemma DT_ne_zero (T : Finset ℕ) (hT : ∀ p ∈ T, 0 < p) : (DT T : ℝ) ≠ 0 := by
  exact_mod_cast (DT_pos T hT).ne'

/-- `∏_{p∈T} 1/(p(p-1)) · D_T = ∏_{p∈T} 1/(p-1)`. -/
lemma prod_inv_mul_DT (T : Finset ℕ) (hT : ∀ p ∈ T, 1 < p) :
    (∏ p ∈ T, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) * (DT T : ℝ) =
      ∏ p ∈ T, (1 : ℝ) / ((p : ℝ) - 1) := by
  rw [DT, Nat.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (hT p hp)
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) ≠ 0 := by linarith
  field_simp

/-- The coefficient `coeffD S T` is `wgt S T * D_T`. -/
lemma coeffD_eq_wgt_mul_DT (S T : Finset ℕ) (hT : ∀ p ∈ T, Nat.Prime p) :
    coeffD S T = wgt S T * (DT T : ℝ) := by
  rw [coeffD, wgt, ← prod_inv_mul_DT T (fun p hp => (hT p hp).one_lt)]
  ring

/-- **The telescoping identity.**  For a finset `S` of primes, `∑_{T ⊆ S} wgt S T = ∏_{p∈S}(1-1/p)`. -/
lemma sum_wgt_eq (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    ∑ T ∈ S.powerset, wgt S T = ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  have hkey : ∀ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) + ((p : ℝ) - 2) / ((p : ℝ) - 1)
      = 1 - 1 / (p : ℝ) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).two_le
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (p : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  calc ∑ T ∈ S.powerset, wgt S T
      = ∑ T ∈ S.powerset,
          (∏ p ∈ T, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) *
            (∏ p ∈ S \ T, ((p : ℝ) - 2) / ((p : ℝ) - 1)) := rfl
    _ = ∏ p ∈ S,
          ((1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) + ((p : ℝ) - 2) / ((p : ℝ) - 1)) :=
        (Finset.prod_add _ _ S).symm
    _ = ∏ p ∈ S, (1 - 1 / (p : ℝ)) := Finset.prod_congr rfl hkey

/-- The `q`-marginal mass of the telescoping weights, in the form where `q` is inserted. -/
lemma sum_wgt_of_mem_insert {q : ℕ} (S : Finset ℕ) (hS : ∀ p ∈ insert q S, Nat.Prime p) (hq : q ∉ S) :
    ∑ T ∈ (insert q S).powerset, (if q ∈ T then wgt (insert q S) T else 0)
      = (∏ p ∈ insert q S, (1 - 1 / (p : ℝ))) / ((q : ℝ) - 1) ^ 2 := by
  classical
  have hfirst : ∑ T ∈ S.powerset, (if q ∈ T then wgt (insert q S) T else 0) = 0 := by
    refine Finset.sum_eq_zero (fun T hT => ?_)
    rw [if_neg]
    intro hmem
    exact hq (Finset.mem_powerset.mp hT hmem)
  have hqT : ∀ T ∈ S.powerset, q ∉ T := fun T hT hmem =>
    hq (Finset.mem_powerset.mp hT hmem)
  have hdiff : ∀ T ∈ S.powerset, (insert q S) \ (insert q T) = S \ T := by
    intro T hT
    have hqT' : q ∉ T := hqT T hT
    ext x
    rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_insert]
    by_cases hxq : x = q
    · subst hxq
      simp [hq, hqT']
    · simp [hxq]
  have hsecond : ∀ T ∈ S.powerset,
      (if q ∈ insert q T then wgt (insert q S) (insert q T) else 0)
        = (1 / ((q : ℝ) * ((q : ℝ) - 1))) * wgt S T := by
    intro T hT
    rw [if_pos (Finset.mem_insert_self q T), wgt, wgt, hdiff T hT,
      Finset.prod_insert (hqT T hT)]
    ring
  rw [Finset.sum_powerset_insert hq, hfirst, zero_add, Finset.sum_congr rfl hsecond]
  rw [← Finset.mul_sum, sum_wgt_eq S (fun p hp => hS p (Finset.mem_insert_of_mem hp))]
  rw [Finset.prod_insert hq]
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (hS q (Finset.mem_insert_self q S)).two_le
  have hqne : ((q : ℝ) - 1) ≠ 0 := by linarith
  field_simp

/-- The `q`-marginal mass of the telescoping weights: `∑_{T ∋ q} wgt S T = A_S/(q-1)^2`. -/
lemma sum_wgt_of_mem (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) {q : ℕ} (hq : q ∈ S) :
    ∑ T ∈ S.powerset, (if q ∈ T then wgt S T else 0)
      = (∏ p ∈ S, (1 - 1 / (p : ℝ))) / ((q : ℝ) - 1) ^ 2 := by
  classical
  have h := sum_wgt_of_mem_insert (S.erase q)
    (fun p hp => hS p (by
      rw [Finset.mem_insert] at hp
      rcases hp with h | h
      · rw [h]; exact hq
      · exact Finset.mem_of_mem_erase h))
    (Finset.notMem_erase q S)
  rwa [Finset.insert_erase hq] at h

/-! ## 6. The logarithmic moment of the telescoping weights -/

/-- `log D_T = ∑_{p∈T} log p` for a set of primes. -/
lemma log_DT (S T : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (hT : T ∈ S.powerset) :
    Real.log ((DT T : ℕ) : ℝ) = ∑ p ∈ T, Real.log (p : ℝ) := by
  rw [DT, Nat.cast_prod, Real.log_prod]
  intro p hp
  exact_mod_cast (hS p (Finset.mem_powerset.mp hT hp)).ne_zero

/-- **Logarithmic moment.**  `∑_{T ⊆ S} wgt S T · log D_T = A_S · ∑_{p ∈ S} log p/(p-1)^2`. -/
lemma sum_wgt_mul_log_DT (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    ∑ T ∈ S.powerset, wgt S T * Real.log ((DT T : ℕ) : ℝ)
      = (∏ p ∈ S, (1 - 1 / (p : ℝ))) *
        ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  classical
  have hind : ∀ T ∈ S.powerset, (∑ p ∈ T, wgt S T * Real.log (p : ℝ))
      = ∑ p ∈ S, (if p ∈ T then wgt S T * Real.log (p : ℝ) else 0) := by
    intro T hT
    have hsub : T ⊆ S := Finset.mem_powerset.mp hT
    have hfil : S.filter (fun p => p ∈ T) = T := by
      ext x
      rw [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
    have h := Finset.sum_filter (s := S) (p := fun p => p ∈ T)
      (f := fun p => wgt S T * Real.log (p : ℝ))
    rw [hfil] at h
    exact h
  calc ∑ T ∈ S.powerset, wgt S T * Real.log ((DT T : ℕ) : ℝ)
      = ∑ T ∈ S.powerset, wgt S T * ∑ p ∈ T, Real.log (p : ℝ) :=
        Finset.sum_congr rfl (fun T hT => by rw [log_DT S T hS hT])
    _ = ∑ T ∈ S.powerset, ∑ p ∈ T, wgt S T * Real.log (p : ℝ) :=
        Finset.sum_congr rfl (fun T _ =>
          Finset.mul_sum T (fun p => Real.log (p : ℝ)) (wgt S T))
    _ = ∑ T ∈ S.powerset,
          ∑ p ∈ S, (if p ∈ T then wgt S T * Real.log (p : ℝ) else 0) :=
        Finset.sum_congr rfl hind
    _ = ∑ p ∈ S,
          ∑ T ∈ S.powerset, (if p ∈ T then wgt S T * Real.log (p : ℝ) else 0) :=
        Finset.sum_comm
    _ = ∑ p ∈ S, Real.log (p : ℝ) *
          ∑ T ∈ S.powerset, (if p ∈ T then wgt S T else 0) := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun T _ => ?_)
        by_cases h : p ∈ T <;> simp [h]; ring
    _ = ∑ p ∈ S, Real.log (p : ℝ) *
          ((∏ p ∈ S, (1 - 1 / (p : ℝ))) / ((p : ℝ) - 1) ^ 2) :=
        Finset.sum_congr rfl (fun p hp => by rw [sum_wgt_of_mem S hS hp])
    _ = (∏ p ∈ S, (1 - 1 / (p : ℝ))) *
          ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => by ring)


/-! ## 6½. Basic positivity and bounds for the coefficients -/

lemma coeffD_nonneg (S T : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (hT : T ⊆ S) :
    0 ≤ coeffD S T := by
  rw [coeffD]
  refine mul_nonneg (Finset.prod_nonneg ?_) (Finset.prod_nonneg ?_)
  · intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p (hT hp)).two_le
    exact div_nonneg (by norm_num) (by linarith)
  · intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (hS p (Finset.mem_sdiff.mp hp).1).two_le
    exact div_nonneg (by linarith) (by linarith)

lemma wgt_nonneg (S T : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (hT : T ⊆ S) :
    0 ≤ wgt S T := by
  rw [wgt]
  refine mul_nonneg (Finset.prod_nonneg ?_) (Finset.prod_nonneg ?_)
  · intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p (hT hp)).two_le
    exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
  · intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (hS p (Finset.mem_sdiff.mp hp).1).two_le
    exact div_nonneg (by linarith) (by linarith)

lemma A_nonneg (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) :=
  Finset.prod_nonneg (fun p hp => (one_sub_inv_mem p (hS p hp)).1)

lemma A_le_one (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    ∏ p ∈ S, (1 - 1 / (p : ℝ)) ≤ 1 :=
  Finset.prod_le_one₀ (fun p hp => (one_sub_inv_mem p (hS p hp)).1)
    (fun p hp => (one_sub_inv_mem p (hS p hp)).2)

/-! ## 7. Auxiliary monotonicity and numeric facts -/

lemma prod_le_prod_of_subset_of_le_one' {s t : Finset ℕ} (hsub : s ⊆ t) {f : ℕ → ℝ}
    (h0 : ∀ i ∈ t, 0 ≤ f i) (h1 : ∀ i ∈ t, f i ≤ 1) : ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i :=
  Finset.prod_le_prod_of_subset_of_le_one₀ hsub h0 (fun i hi _ => h1 i hi)

/-- Strict positivity of the Euler factor at a prime. -/
lemma one_sub_inv_pos_of_prime {p : ℕ} (hp : Nat.Prime p) : 0 < 1 - 1 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  linarith

lemma log_four_le_of_large {N : ℕ} (hN : 10000 ≤ N) : 4 ≤ Real.log (N : ℝ) := by
  rw [Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < (N : ℝ))]
  have h4 : Real.exp (4 : ℝ) = (Real.exp 1) ^ 4 := by
    rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  rw [h4]
  have hlt := Real.exp_one_lt_d9
  have hpos := Real.exp_pos 1
  have h1 : (Real.exp 1) ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (le_of_lt hpos) (le_of_lt hlt) 4
  have h2 : (2.7182818286 : ℝ) ^ 4 ≤ 10000 := by norm_num
  have hN' : (10000 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  linarith

lemma log_le_ten_of_small {N : ℕ} (hN : N ≤ 10000) : Real.log (N : ℝ) ≤ 10 := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hpos
    rw [Real.log_le_iff_le_exp hNpos]
    have h10 : Real.exp (10 : ℝ) = (Real.exp 1) ^ 10 := by
      rw [show (10 : ℝ) = (10 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h10]
    have hlt := Real.exp_one_gt_d9
    have h1 : (2.7182818283 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 :=
      pow_le_pow_left₀ (by norm_num) (le_of_lt hlt) 10
    have h2 : (10000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 10 := by norm_num
    have hN' : (N : ℝ) ≤ 10000 := by exact_mod_cast hN
    linarith

/-- The Euler product over `p ≤ 16`. -/
lemma primesLE_sixteen : Nat.primesLE 16 = {2, 3, 5, 7, 11, 13} := by decide

lemma primesLE_sixteen_prod :
    (∏ p ∈ Nat.primesLE 16, (1 - 1 / (p : ℝ))) = 192 / 1001 := by
  rw [primesLE_sixteen]
  norm_num

/-! ## 8. The Euler product comparisons -/

/-- `eprod QR N` dominates the full Euler product over `p ≤ N`. -/
lemma eprod_ge_primesLE (QR N : ℕ) :
    (∏ p ∈ Nat.primesLE N, (1 - 1 / (p : ℝ))) ≤ eprod QR (N : ℝ) := by
  rw [eprod_nat]
  refine prod_le_prod_of_subset_of_le_one'
    (s := (Nat.primeFactors QR).filter (fun p : ℕ => p ≤ N)) (t := Nat.primesLE N) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp
    rw [Nat.mem_primesLE]
    exact ⟨hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
  · intro p hp
    rw [Nat.mem_primesLE] at hp
    exact (one_sub_inv_mem p hp.2).1
  · intro p hp
    rw [Nat.mem_primesLE] at hp
    exact (one_sub_inv_mem p hp.2).2

lemma log_100_le_five : Real.log (100 : ℝ) ≤ 5 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h10 : Real.exp (5 : ℝ) = (Real.exp 1) ^ 5 := by
    rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  rw [h10]
  have hlt := Real.exp_one_gt_d9
  have h1 : (2.7182818283 : ℝ) ^ 5 ≤ (Real.exp 1) ^ 5 :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt hlt) 5
  have h2 : (100 : ℝ) ≤ (2.7182818283 : ℝ) ^ 5 := by norm_num
  linarith

/-- `eprod QR N ≥ 1/25` for `N ≤ 10000`. -/
lemma eprod_ge_inv_twenty (QR N : ℕ) (hN : N ≤ 10000) : (1 / 25 : ℝ) ≤ eprod QR (N : ℝ) := by
  have h1 : (∏ p ∈ Nat.primesLE N, (1 - 1 / (p : ℝ))) ≤ eprod QR (N : ℝ) := eprod_ge_primesLE QR N
  by_cases hN100 : N ≤ 100
  · have hsub : Nat.primesLE N ⊆ Nat.primesLE 100 := by
      intro p hp
      rw [Nat.mem_primesLE] at hp ⊢
      exact ⟨le_trans hp.1 hN100, hp.2⟩
    have h2 : (∏ p ∈ Nat.primesLE 100, (1 - 1 / (p : ℝ))) ≤
        ∏ p ∈ Nat.primesLE N, (1 - 1 / (p : ℝ)) :=
      prod_le_prod_of_subset_of_le_one' hsub
        (fun p hp => (one_sub_inv_mem p (Nat.mem_primesLE.mp hp).2).1)
        (fun p hp => (one_sub_inv_mem p (Nat.mem_primesLE.mp hp).2).2)
    have h3 := Commons.NumberTheory.Mertens.primeProduct_oneSubInv_ge_invLog 100 (by norm_num)
    have h3' : (9 : ℝ) / 20 / Real.log (100 : ℝ) ≤
        ∏ p ∈ Nat.primesLE 100, (1 - 1 / (p : ℝ)) := by
      simpa [one_div] using h3
    have h4 : Real.log (100 : ℝ) ≤ 5 := log_100_le_five
    have hlogpos : 0 < Real.log (100 : ℝ) := Real.log_pos (by norm_num)
    have h5 : (1 / 25 : ℝ) ≤ (9 : ℝ) / 20 / Real.log (100 : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num) hlogpos]
      linarith
    linarith
  · have h100 : 100 ≤ N := by omega
    have h3 := Commons.NumberTheory.Mertens.primeProduct_oneSubInv_ge_invLog N h100
    have h3' : (9 : ℝ) / 20 / Real.log (N : ℝ) ≤
        ∏ p ∈ Nat.primesLE N, (1 - 1 / (p : ℝ)) := by
      simpa [one_div] using h3
    have h4 : Real.log (N : ℝ) ≤ 10 := log_le_ten_of_small hN
    have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have h5 : (1 / 25 : ℝ) ≤ (9 : ℝ) / 20 / Real.log (N : ℝ) := by
      rw [div_le_div_iff₀ (by norm_num) hlogpos]
      linarith
    linarith

/-- **Mertens range comparison.**  For `100 ≤ s ≤ N`, the ratio `eprod QR N / eprod QR s` is at
least `(4/5)·log s / log N`. -/
lemma eprod_ratio_ge (QR N s : ℕ) (hQR : QR ≠ 0) (hs : 100 ≤ s) (hsN : s ≤ N) :
    (4 / 5) * (Real.log (s : ℝ) / Real.log (N : ℝ)) ≤
      eprod QR (N : ℝ) / eprod QR (s : ℝ) := by
  classical
  set W : Finset ℕ := (Nat.primeFactors QR).filter (fun p : ℕ => p ≤ N) \ (Nat.primeFactors QR).filter (fun p : ℕ => p ≤ s) with hW
  have hsub : (Nat.primeFactors QR).filter (fun p : ℕ => p ≤ s) ⊆
      (Nat.primeFactors QR).filter (fun p : ℕ => p ≤ N) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, le_trans hp.2 hsN⟩
  have hEs : eprod QR (s : ℝ) ≠ 0 := ne_of_gt (eprod_pos QR _)
  have hE : eprod QR (N : ℝ) = eprod QR (s : ℝ) * ∏ p ∈ W, (1 - 1 / (p : ℝ)) := by
    rw [eprod_nat, eprod_nat, hW, mul_comm]
    exact (Finset.prod_sdiff hsub).symm
  rw [hE, mul_div_cancel_left₀ _ hEs]
  have hmer : (4 / 5) * (Real.log (s : ℝ) / Real.log (N : ℝ)) ≤
      ∏ p ∈ (Nat.primesLE N).filter (fun p : ℕ => (s : ℝ) ≤ (p : ℝ)), (1 - 1 / (p : ℝ)) := by
    have h := Commons.NumberTheory.Mertens.prod_one_sub_inv_range_lower_sharp (s : ℝ) (N : ℝ)
      (by exact_mod_cast hs) (by exact_mod_cast hsN)
    rw [Nat.floor_natCast] at h
    exact h
  have hstep : (∏ p ∈ (Nat.primesLE N).filter (fun p : ℕ => (s : ℝ) ≤ (p : ℝ)), (1 - 1 / (p : ℝ))) ≤
      ∏ p ∈ W, (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_le_prod_of_subset_of_le_one₀
      (s := W) (t := (Nat.primesLE N).filter (fun p : ℕ => (s : ℝ) ≤ (p : ℝ))) ?_ ?_ ?_
    · intro p hp
      rw [hW, Finset.mem_sdiff] at hp
      obtain ⟨hpA, hpB⟩ := hp
      rw [Finset.mem_filter] at hpA hpB
      rw [Finset.mem_filter, Nat.mem_primesLE]
      refine ⟨⟨hpA.2, Nat.prime_of_mem_primeFactors hpA.1⟩, ?_⟩
      by_contra hlt
      push Not at hlt
      exact hpB ⟨hpA.1, by exact_mod_cast (le_of_lt hlt)⟩
    · intro p hp
      rw [Finset.mem_filter, Nat.mem_primesLE] at hp
      exact (one_sub_inv_mem p hp.1.2).1
    · intro p hp _
      rw [Finset.mem_filter, Nat.mem_primesLE] at hp
      exact (one_sub_inv_mem p hp.1.2).2
  linarith

/-- If `D² ≤ N` and `N ≥ 10^4` then `5 log N ≤ 16 log (N/D)`. -/
lemma log_ratio_le {N D : ℕ} (hN : 10000 ≤ N) (hD : 0 < D) (hsq : D * D ≤ N) :
    5 * Real.log (N : ℝ) ≤ 16 * Real.log ((N / D : ℕ) : ℝ) := by
  have hDposR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hNDposR : (0 : ℝ) < ((N / D : ℕ) : ℝ) := by
    have hDleN : D ≤ N :=
      le_trans (by simpa using (Nat.mul_le_mul_left D hD : D * 1 ≤ D * D)) hsq
    have : 0 < N / D := Nat.div_pos hDleN hD
    exact_mod_cast this
  have h1 : D ≤ N / D := (Nat.le_div_iff_mul_le hD).mpr hsq
  have h2 : Real.log (D : ℝ) ≤ Real.log ((N / D : ℕ) : ℝ) :=
    Real.log_le_log hDposR (by exact_mod_cast h1)
  have h4 : N < (N / D) * D + D := by
    have h5 : N = (N / D) * D + N % D := by
      rw [mul_comm]
      exact (Nat.div_add_mod N D).symm
    have h6 : N % D < D := Nat.mod_lt N hD
    omega
  have h7 : (N : ℝ) < 2 * (D : ℝ) * ((N / D : ℕ) : ℝ) := by
    have h8 : N < 2 * D * (N / D) := by nlinarith [h4, h1]
    exact_mod_cast h8
  have h8 : Real.log (N : ℝ) < Real.log 2 + Real.log (D : ℝ) + Real.log ((N / D : ℕ) : ℝ) := by
    have h9 := Real.log_lt_log (by positivity : (0 : ℝ) < (N : ℝ)) h7
    have h10 : Real.log (2 * (D : ℝ) * ((N / D : ℕ) : ℝ)) =
        Real.log 2 + Real.log (D : ℝ) + Real.log ((N / D : ℕ) : ℝ) := by
      have h11 : (2 * (D : ℝ) * ((N / D : ℕ) : ℝ)) = (2 * (D : ℝ)) * ((N / D : ℕ) : ℝ) := by
        ring
      rw [h11, Real.log_mul (mul_ne_zero (by norm_num) (ne_of_gt hDposR)) (ne_of_gt hNDposR),
        Real.log_mul (by norm_num) (ne_of_gt hDposR)]
    rw [h10] at h9
    exact h9
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have h9 : (3 / 2 : ℝ) ≤ Real.log ((N / D : ℕ) : ℝ) := by
    have h4' : 4 ≤ Real.log (N : ℝ) := log_four_le_of_large hN
    linarith
  linarith

/-- In the "100 or more" regime, the Mertens range bound gives `R ≤ 4`. -/
lemma ratio_le_four (QR N s : ℕ) (hQR : QR ≠ 0) (h100 : 100 ≤ s) (hsN : s ≤ N)
    (hlog : 5 * Real.log (N : ℝ) ≤ 16 * Real.log (s : ℝ)) :
    eprod QR (s : ℝ) / eprod QR (N : ℝ) ≤ 4 := by
  have hNpos : (0 : ℝ) < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hEn : 0 < eprod QR (N : ℝ) := eprod_pos QR _
  have hEs : 0 < eprod QR (s : ℝ) := eprod_pos QR _
  have h := eprod_ratio_ge QR N s hQR h100 hsN
  have hquarter : (1 / 4 : ℝ) ≤ eprod QR (N : ℝ) / eprod QR (s : ℝ) := by
    refine le_trans ?_ h
    have h2 : (4 / 5 : ℝ) * ((5 : ℝ) / 16) ≤
        (4 / 5 : ℝ) * (Real.log (s : ℝ) / Real.log (N : ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      rw [le_div_iff₀ hNpos]
      linarith
    linarith
  rw [div_le_iff₀ hEn]
  have h3 : (1 / 4 : ℝ) * eprod QR (s : ℝ) ≤ eprod QR (N : ℝ) := (le_div_iff₀ hEs).mp hquarter
  linarith

/-- The universal (logarithmic) regime bound. -/
lemma ratio_le_log (QR N s : ℕ) (hN : 100 ≤ N) :
    eprod QR (s : ℝ) / eprod QR (N : ℝ) ≤ 3 * Real.log (N : ℝ) := by
  have hEn : 0 < eprod QR (N : ℝ) := eprod_pos QR _
  rw [div_le_iff₀ hEn]
  have h1 : eprod QR (s : ℝ) ≤ 1 := eprod_le_one QR _
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hpl := Commons.NumberTheory.Mertens.primeProduct_oneSubInv_ge_invLog N hN
  have hpl' : (9 : ℝ) / 20 / Real.log (N : ℝ) ≤
      ∏ p ∈ Nat.primesLE N, (1 - 1 / (p : ℝ)) := by
    simpa [one_div] using hpl
  have hge := eprod_ge_primesLE QR N
  have h3 : (9 : ℝ) / 20 / Real.log (N : ℝ) ≤ eprod QR (N : ℝ) := le_trans hpl' hge
  have h2 : (1 : ℝ) ≤ eprod QR (N : ℝ) * (3 * Real.log (N : ℝ)) := by
    rw [div_le_iff₀ hlogN] at h3
    nlinarith [h3, hlogN]
  linarith

/-- For `N ≥ 10^4` and `D² ≤ N`, `N / D ≥ 100`. -/
lemma div_ge_hundred {N D : ℕ} (hD : 0 < D) (hsq : D * D ≤ N) (hN : 10000 ≤ N) :
    100 ≤ N / D := by
  by_contra hc
  push Not at hc
  have h1 : N / D ≤ 99 := by omega
  have h2 : N < (N / D + 1) * D := by
    have h3 : (N / D + 1) * D = (N / D) * D + D := by rw [Nat.add_mul, one_mul]
    have h4 : N = (N / D) * D + N % D := by
      rw [mul_comm]
      exact (Nat.div_add_mod N D).symm
    have h5 : N % D < D := Nat.mod_lt N hD
    omega
  have h5 : N < 100 * D := by nlinarith
  have h6 : D < 100 := by nlinarith
  omega

/-- **The σ-window sieve estimate**, with the explicit absolute constant `4000`. -/
theorem sigma_window_bound (N QR : ℕ) (S : Finset ℕ) (hQR : QR ≠ 0)
    (hS : ∀ p ∈ S, Nat.Prime p) (hSQR : ∀ p ∈ S, ¬ p ∣ QR)
    (hL0 : ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 30) :
    (∑ c ∈ (Finset.Icc 1 N).filter (fun c : ℕ => c.gcd QR = 1), ∏ p ∈ S, sig p c)
      ≤ 4000 * (N : ℝ) * eprod QR (N : ℝ) * ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  classical
  rcases Nat.eq_zero_or_pos N with h0 | hNpos
  · subst h0
    simp
  set F : Finset ℕ := (Finset.Icc 1 N).filter (fun c : ℕ => c.gcd QR = 1) with hF
  set A : ℝ := ∏ p ∈ S, (1 - 1 / (p : ℝ)) with hA
  have hA0 : 0 ≤ A := by rw [hA]; exact A_nonneg S hS
  have hEpos : 0 < eprod QR (N : ℝ) := eprod_pos QR N
  -- (1) the exact expansion
  have hexp : (∑ c ∈ F, ∏ p ∈ S, sig p c)
      = ∑ T ∈ S.powerset, coeffD S T * ((F.filter (fun c : ℕ => DT T ∣ c)).card : ℝ) := by
    rw [Finset.sum_congr rfl (fun c _ => prod_sig_eq S hS c)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    show (∑ c ∈ F, coeffD S T * (if DT T ∣ c then (1 : ℝ) else 0))
        = coeffD S T * ((F.filter (fun c : ℕ => DT T ∣ c)).card : ℝ)
    have h1 : (∑ c ∈ F, coeffD S T * (if DT T ∣ c then (1 : ℝ) else 0))
        = ∑ c ∈ F, (if DT T ∣ c then coeffD S T else 0) := by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      by_cases h : DT T ∣ c <;> simp [h]
    rw [h1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  -- (2) reindexing each fibre
  have hre : ∀ T ∈ S.powerset, ((F.filter (fun c : ℕ => DT T ∣ c)).card : ℝ)
      = (((Finset.Icc 1 (N / DT T)).filter (fun m : ℕ => m.gcd QR = 1)).card : ℝ) := by
    intro T hT
    have hsub : T ⊆ S := Finset.mem_powerset.mp hT
    have hDpos : 0 < DT T := DT_pos T (fun p hp => (hS p (hsub hp)).pos)
    have hcop : Nat.Coprime (DT T) QR := by
      rw [DT]
      exact Nat.Coprime.prod_left (fun p hp =>
        (Nat.Prime.coprime_iff_not_dvd (hS p (hsub hp))).mpr (hSQR p (hsub hp)))
    have h1 : F.filter (fun c : ℕ => DT T ∣ c)
        = (Finset.Icc 1 N).filter (fun c : ℕ => c.gcd QR = 1 ∧ DT T ∣ c) := by
      rw [hF, Finset.filter_filter]
    rw [h1, card_filter_dvd_coprime N (DT T) QR hDpos hcop]
  by_cases hN : N ≤ 10000
  · -- small case: the trivial count bound
    have hle : ∀ T ∈ S.powerset, ((F.filter (fun c : ℕ => DT T ∣ c)).card : ℝ)
        ≤ (N : ℝ) / (DT T : ℝ) := by
      intro T hT
      rw [hre T hT]
      have hcard : (((Finset.Icc 1 (N / DT T)).filter (fun m : ℕ => m.gcd QR = 1)).card : ℝ)
          ≤ ((N / DT T : ℕ) : ℝ) := by
        calc (((Finset.Icc 1 (N / DT T)).filter (fun m : ℕ => m.gcd QR = 1)).card : ℝ)
            ≤ ((Finset.Icc 1 (N / DT T)).card : ℝ) := by
              exact_mod_cast Finset.card_filter_le (Finset.Icc 1 (N / DT T))
                (fun m : ℕ => m.gcd QR = 1)
          _ = ((N / DT T : ℕ) : ℝ) := by
              rw [Nat.card_Icc]
              push_cast
              ring
      exact le_trans hcard Nat.cast_div_le
    calc (∑ c ∈ F, ∏ p ∈ S, sig p c)
        = ∑ T ∈ S.powerset, coeffD S T * ((F.filter (fun c : ℕ => DT T ∣ c)).card : ℝ) := hexp
      _ ≤ ∑ T ∈ S.powerset, coeffD S T * ((N : ℝ) / (DT T : ℝ)) := by
          refine Finset.sum_le_sum (fun T hT => ?_)
          exact mul_le_mul_of_nonneg_left (hle T hT)
            (coeffD_nonneg S T hS (Finset.mem_powerset.mp hT))
      _ = (N : ℝ) * A := by
          have h2 : ∀ T ∈ S.powerset, coeffD S T * ((N : ℝ) / (DT T : ℝ))
              = (N : ℝ) * wgt S T := by
            intro T hT
            rw [coeffD_eq_wgt_mul_DT S T (fun p hp => hS p (Finset.mem_powerset.mp hT hp))]
            have hDne : (DT T : ℝ) ≠ 0 :=
              DT_ne_zero T (fun p hp => (hS p (Finset.mem_powerset.mp hT hp)).pos)
            field_simp
          rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, sum_wgt_eq S hS, hA]
      _ ≤ 4000 * (N : ℝ) * eprod QR (N : ℝ) * A := by
          have h20 : (1 / 25 : ℝ) ≤ eprod QR (N : ℝ) := eprod_ge_inv_twenty QR N hN
          have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
          have h1 : (N : ℝ) ≤ 4000 * (N : ℝ) * eprod QR (N : ℝ) := by nlinarith [h20, hN0]
          calc (N : ℝ) * A ≤ (4000 * (N : ℝ) * eprod QR (N : ℝ)) * A :=
                mul_le_mul_of_nonneg_right h1 hA0
            _ = 4000 * (N : ℝ) * eprod QR (N : ℝ) * A := by ring
  · -- large case
    have hN' : 10000 ≤ N := by omega
    have h17 : 17 ≤ N := by omega
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    set R : Finset ℕ → ℝ := fun T => eprod QR ((N / DT T : ℕ) : ℝ) / eprod QR (N : ℝ) with hR
    have hstep1 : (∑ c ∈ F, ∏ p ∈ S, sig p c)
        ≤ ∑ T ∈ S.powerset, coeffD S T *
            (17 * ((N : ℝ) / (DT T : ℝ)) * eprod QR ((N / DT T : ℕ) : ℝ)) := by
      rw [hexp]
      refine Finset.sum_le_sum (fun T hT => ?_)
      have hsub : T ⊆ S := Finset.mem_powerset.mp hT
      have h1 : ((F.filter (fun c : ℕ => DT T ∣ c)).card : ℝ)
          ≤ 17 * (((N / DT T : ℕ)) : ℝ) * eprod QR ((N / DT T : ℕ) : ℝ) := by
        rw [hre T hT]
        exact card_coprime_window_le QR (N / DT T) hQR
      have h2 : (17 : ℝ) * (((N / DT T : ℕ)) : ℝ) * eprod QR ((N / DT T : ℕ) : ℝ)
          ≤ 17 * ((N : ℝ) / (DT T : ℝ)) * eprod QR ((N / DT T : ℕ) : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (eprod_nonneg _ _)
        exact mul_le_mul_of_nonneg_left Nat.cast_div_le (by norm_num)
      exact mul_le_mul_of_nonneg_left (le_trans h1 h2) (coeffD_nonneg S T hS hsub)
    have hstep2 : (∑ T ∈ S.powerset, coeffD S T *
            (17 * ((N : ℝ) / (DT T : ℝ)) * eprod QR ((N / DT T : ℕ) : ℝ)))
        = 17 * (N : ℝ) * eprod QR (N : ℝ) * ∑ T ∈ S.powerset, wgt S T * R T := by
      have h2 : ∀ T ∈ S.powerset, coeffD S T *
            (17 * ((N : ℝ) / (DT T : ℝ)) * eprod QR ((N / DT T : ℕ) : ℝ))
          = 17 * (N : ℝ) * eprod QR (N : ℝ) * (wgt S T * R T) := by
        intro T hT
        have hsub : T ⊆ S := Finset.mem_powerset.mp hT
        have hDne : (DT T : ℝ) ≠ 0 := DT_ne_zero T (fun p hp => (hS p (hsub hp)).pos)
        rw [coeffD_eq_wgt_mul_DT S T (fun p hp => hS p (hsub hp)), hR]
        field_simp
      rw [Finset.sum_congr rfl h2, Finset.mul_sum]
    have hstep3 : (∑ T ∈ S.powerset, wgt S T * R T) ≤ 184 * A := by
      have hsplit : (∑ T ∈ S.powerset, wgt S T * R T)
          = (∑ T ∈ S.powerset.filter (fun T => DT T * DT T ≤ N), wgt S T * R T)
          + (∑ T ∈ S.powerset.filter (fun T => ¬ (DT T * DT T ≤ N)), wgt S T * R T) :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      have hsum1 : (∑ T ∈ S.powerset.filter (fun T => DT T * DT T ≤ N), wgt S T * R T) ≤ 4 * A := by
        have hb : ∀ T ∈ S.powerset.filter (fun T => DT T * DT T ≤ N), R T ≤ 4 := by
          intro T hT
          have hT' : T ∈ S.powerset := (Finset.mem_filter.mp hT).1
          have hsub : T ⊆ S := Finset.mem_powerset.mp hT'
          have hDpos : 0 < DT T := DT_pos T (fun p hp => (hS p (hsub hp)).pos)
          have hss : DT T * DT T ≤ N := (Finset.mem_filter.mp hT).2
          have h100 : 100 ≤ N / DT T := div_ge_hundred hDpos hss hN'
          have hlog : 5 * Real.log (N : ℝ) ≤ 16 * Real.log (((N / DT T : ℕ)) : ℝ) :=
            log_ratio_le (by omega) hDpos hss
          have h := ratio_le_four QR N (N / DT T) hQR h100 (Nat.div_le_self N _) hlog
          rwa [hR]
        calc (∑ T ∈ S.powerset.filter (fun T => DT T * DT T ≤ N), wgt S T * R T)
            ≤ ∑ T ∈ S.powerset.filter (fun T => DT T * DT T ≤ N), wgt S T * 4 := by
              refine Finset.sum_le_sum (fun T hT => ?_)
              exact mul_le_mul_of_nonneg_left (hb T hT)
                (wgt_nonneg S T hS (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1))
          _ = 4 * (∑ T ∈ S.powerset.filter (fun T => DT T * DT T ≤ N), wgt S T) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun T _ => by ring)
          _ ≤ 4 * A := by
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              calc (∑ T ∈ S.powerset.filter (fun T => DT T * DT T ≤ N), wgt S T)
                  ≤ ∑ T ∈ S.powerset, wgt S T :=
                    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                      (fun T hT _ => wgt_nonneg S T hS (Finset.mem_powerset.mp hT))
                _ = A := by rw [sum_wgt_eq S hS, hA]
      have hsum2 : (∑ T ∈ S.powerset.filter (fun T => ¬ (DT T * DT T ≤ N)), wgt S T * R T)
          ≤ 180 * A := by
        have hb : ∀ T ∈ S.powerset.filter (fun T => ¬ (DT T * DT T ≤ N)),
            R T ≤ 3 * Real.log (N : ℝ) := by
          intro T hT
          have h := ratio_le_log QR N (N / DT T) (by omega : 100 ≤ N)
          rwa [hR]
        have hpt : ∀ T ∈ S.powerset.filter (fun T => ¬ (DT T * DT T ≤ N)),
            wgt S T ≤ wgt S T * (2 * Real.log (((DT T : ℕ)) : ℝ) / Real.log (N : ℝ)) := by
          intro T hT
          have hT' : T ∈ S.powerset := (Finset.mem_filter.mp hT).1
          have hsub : T ⊆ S := Finset.mem_powerset.mp hT'
          have hDpos : 0 < DT T := DT_pos T (fun p hp => (hS p (hsub hp)).pos)
          have hgt : N < DT T * DT T := by
            exact not_le.mp (Finset.mem_filter.mp hT).2
          have hDTlarge : 101 ≤ DT T := by
            by_contra hc
            push Not at hc
            have hc' : DT T ≤ 100 := by omega
            have h2 : DT T * DT T ≤ 100 * 100 := Nat.mul_le_mul hc' hc'
            omega
          have hlogDT : 0 < Real.log (((DT T : ℕ)) : ℝ) :=
            Real.log_pos (by exact_mod_cast (by omega : 1 < DT T))
          have h2 : Real.log (N : ℝ) ≤ 2 * Real.log (((DT T : ℕ)) : ℝ) := by
            have h3 : Real.log (N : ℝ) ≤ Real.log ((((DT T : ℕ) : ℝ) * ((DT T : ℕ) : ℝ))) :=
              Real.log_le_log (by positivity) (by exact_mod_cast (by nlinarith [hgt] : N ≤ DT T * DT T))
            rw [Real.log_mul (by positivity) (by positivity)] at h3
            linarith
          have h3 : (1 : ℝ) ≤ 2 * Real.log (((DT T : ℕ)) : ℝ) / Real.log (N : ℝ) := by
            rw [le_div_iff₀ hlogN]
            linarith
          have hw := wgt_nonneg S T hS hsub
          nlinarith [hw, h3]
        calc (∑ T ∈ S.powerset.filter (fun T => ¬ (DT T * DT T ≤ N)), wgt S T * R T)
            ≤ ∑ T ∈ S.powerset.filter (fun T => ¬ (DT T * DT T ≤ N)),
                wgt S T * (3 * Real.log (N : ℝ)) := by
              refine Finset.sum_le_sum (fun T hT => ?_)
              exact mul_le_mul_of_nonneg_left (hb T hT)
                (wgt_nonneg S T hS (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1))
          _ = (3 * Real.log (N : ℝ)) *
                (∑ T ∈ S.powerset.filter (fun T => ¬ (DT T * DT T ≤ N)), wgt S T) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun T _ => by ring)
          _ ≤ (3 * Real.log (N : ℝ)) *
                ((2 / Real.log (N : ℝ)) * (∑ T ∈ S.powerset, wgt S T * Real.log (((DT T : ℕ)) : ℝ))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by linarith [hlogN])
              have h1 : (∑ T ∈ S.powerset.filter (fun T => ¬ (DT T * DT T ≤ N)), wgt S T)
                  ≤ ∑ T ∈ S.powerset.filter (fun T => ¬ (DT T * DT T ≤ N)),
                      wgt S T * (2 * Real.log (((DT T : ℕ)) : ℝ) / Real.log (N : ℝ)) :=
                Finset.sum_le_sum hpt
              have h2 : (∑ T ∈ S.powerset.filter (fun T => ¬ (DT T * DT T ≤ N)),
                      wgt S T * (2 * Real.log (((DT T : ℕ)) : ℝ) / Real.log (N : ℝ)))
                  ≤ ∑ T ∈ S.powerset,
                      wgt S T * (2 * Real.log (((DT T : ℕ)) : ℝ) / Real.log (N : ℝ)) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  (fun T hT _ => by
                    have := wgt_nonneg S T hS (Finset.mem_powerset.mp hT)
                    positivity)
              refine le_trans h1 (le_trans h2 ?_)
              rw [Finset.mul_sum]
              refine Finset.sum_le_sum (fun T _ => le_of_eq (by ring))
          _ = (3 * Real.log (N : ℝ)) *
                ((2 / Real.log (N : ℝ)) * (A * (∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) ^ 2))) := by
              rw [sum_wgt_mul_log_DT S hS, hA]
          _ ≤ (3 * Real.log (N : ℝ)) *
                ((2 / Real.log (N : ℝ)) * (A * 30)) := by
              have hAl : 0 ≤ A := hA0
              have h2 : (0:ℝ) ≤ 2 / Real.log (N : ℝ) := by positivity
              have h3 : A * (∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) ^ 2) ≤ A * 30 :=
                mul_le_mul_of_nonneg_left hL0 hAl
              have h4 : (3 * Real.log (N : ℝ)) * ((2 / Real.log (N : ℝ)) * (A * 30)) ≥
                  (3 * Real.log (N : ℝ)) * ((2 / Real.log (N : ℝ)) * (A * (∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) ^ 2))) := by
                exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 h2) (by linarith)
              linarith
          _ = 180 * A := by
              field_simp
              ring
      rw [hsplit]
      linarith
    calc (∑ c ∈ F, ∏ p ∈ S, sig p c)
        ≤ ∑ T ∈ S.powerset, coeffD S T *
            (17 * ((N : ℝ) / (DT T : ℝ)) * eprod QR ((N / DT T : ℕ) : ℝ)) := hstep1
      _ = 17 * (N : ℝ) * eprod QR (N : ℝ) * ∑ T ∈ S.powerset, wgt S T * R T := hstep2
      _ ≤ 17 * (N : ℝ) * eprod QR (N : ℝ) * (184 * A) := by
          refine mul_le_mul_of_nonneg_left hstep3 ?_
          positivity
      _ ≤ 4000 * (N : ℝ) * eprod QR (N : ℝ) * A := by
          have hN0 : (0:ℝ) ≤ (N:ℝ) := by positivity
          have hE0 : (0:ℝ) ≤ eprod QR (N:ℝ) := hEpos.le
          have hX : (0:ℝ) ≤ (N:ℝ) * eprod QR (N:ℝ) * A :=
            mul_nonneg (mul_nonneg hN0 hE0) hA0
          nlinarith [hX]

end

end SigmaSelfWin
